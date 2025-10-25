#!/usr/bin/env python3

import simpy
import random
import uuid
import threading
import queue
import time
import csv
import json
from datetime import datetime
from collections import defaultdict, deque, OrderedDict
from enum import Enum
import tkinter as tk
from tkinter import ttk, filedialog, messagebox
from tkinter.scrolledtext import ScrolledText
import matplotlib
matplotlib.use('TkAgg')
from matplotlib.backends.backend_tkagg import FigureCanvasTkAgg
import matplotlib.pyplot as plt
import matplotlib.patches as patches
from matplotlib.animation import FuncAnimation

# Configuration - Based on Mesh Topology
N_HOSTS = 16 # Total IPs: 14 GPUs + 1 CPU + 1 Global Memory
N_GPUS = 14 # GPU nodes 0-13
MESH_SIZE = 4 # 4x4 mesh for 16 nodes
CPU_NODE_ID = 14 # CPU (inactive)
GLOBAL_MEMORY_ID = 15 # Global Memory (HOME NODE)

# MEMORY CONFIGURATION
GLOBAL_MEMORY_SIZE = 32 # Global memory: 0-31 addresses
GPU_CACHE_SIZE = 4 # GPU cache ONLY 4 slots (LRU policy)

# NETWORK INFRASTRUCTURE PARAMETERS - UPDATED FOR REALISTIC ON-CHIP NoC
ACCESS_LINK_BW = 200e9 # 200 Gbps Node to Router (on-chip realistic)
MESH_LINK_BW = 400e9 # 400 Gbps Router to Router (on-chip realistic)
SWITCH_PROCESSING_DELAY = 3e-9 # 3ns per switch hop (on-chip realistic)
BUFFER_SIZE = 16 # Router buffer size (packets)
PACKET_SIZE = 64 # Packet size (bytes)

# CACHE TIMING - Realistic values
CACHE_HIT_DELAY = 2e-9 # 2ns for cache hit
CACHE_MISS_PENALTY = 30e-9 # 30ns miss penalty
MEMORY_ACCESS_DELAY = 100e-9 # 100ns memory access
LRU_ACCESS_OVERHEAD = 0.5e-9 # 0.5ns LRU overhead

# SIMULATION PARAMETERS
ANIM_SPEED = 0.3
SIM_TIMEOUT = 30.0
RANDOM_TRAFFIC_PERIOD = 1.5
random.seed(42)

# ENUMS
class MessageType(Enum):
    ReadShared = 0
    WriteUnique = 1
    CompData = 2
    CompAck = 3
    SnpUnique = 4
    SnpResp = 5
    SnpSharedFwd = 6
    SnpRespData = 7
    WriteBackFull = 8 # NEW: Explicit writeback message

class CacheState(Enum):
    Invalid = 0 # I
    Shared = 1 # S
    Modified = 2 # M (Dirty)
    Exclusive = 3 # E (Clean)

class NodeType(Enum):
    GPU = 0
    CPU = 1
    GLOBAL_MEMORY = 2

class TrafficPattern(Enum):
    UNIFORM_RANDOM = 0

# LRU Cache Entry with proper timing
class LRUCacheEntry:
    def __init__(self, state, data, timestamp):
        self.state = state
        self.data = data
        self.creation_time = timestamp
        self.last_access_time = timestamp
        self.access_count = 1

    def update_access(self, timestamp):
        self.last_access_time = timestamp
        self.access_count += 1

    def get_state_char(self):
        state_map = {
            CacheState.Invalid: 'I',
            CacheState.Shared: 'S',
            CacheState.Modified: 'M',
            CacheState.Exclusive: 'E'
        }
        return state_map.get(self.state, 'I')

# MESH Router with XY routing logic
class MeshRouter:
    def __init__(self, env, router_id, row, col, mesh_size):
        self.env = env
        self.router_id = router_id
        self.row = row
        self.col = col
        self.mesh_size = mesh_size
        
        # Enhanced queuing system - per-port stores and service processes
        self.input_queues = {} # port -> simpy.Store
        self.port_service_procs = {} # port -> process
        
        # Connected nodes/routers
        self.connected_nodes = {} # port -> node_id
        self.connected_routers = {} # port -> router
        
        # Statistics
        self.packets_processed = 0
        self.packets_dropped = 0
        self.total_queue_delay = 0.0 # Track total queuing delay
        self.queue_delay_samples = 0 # Count of delay samples
        
        # Mesh-specific ports: North=0, East=1, South=2, West=3, Local=4
        self.PORT_NORTH = 0
        self.PORT_EAST = 1
        self.PORT_SOUTH = 2
        self.PORT_WEST = 3
        self.PORT_LOCAL = 4

    def _ensure_port_exists(self, port):
        """Ensure simpy.Store and service process exist for a port."""
        if port not in self.input_queues:
            self.input_queues[port] = simpy.Store(self.env)
            # start the service process for this input port
            proc = self.env.process(self._port_service_loop(port))
            self.port_service_procs[port] = proc

    def enqueue_packet_to_port(self, port, packet):
        """Public method to push packet into a router input port."""
        self._ensure_port_exists(port)
        queue_store = self.input_queues[port]
        
        # simulate finite buffer size
        if len(queue_store.items) >= BUFFER_SIZE:
            self.packets_dropped += 1
            LOGGER.log(f"Router {self.router_id} DROP on port {port} (buffer full)")
            return False
        else:
            # record arrival time for queue delay measurement
            packet.arrival_to_port = self.env.now
            queue_store.put(packet)
            return True

    def _port_service_loop(self, port):
        """Service loop for single port - takes next packet and forwards after service time."""
        store = self.input_queues[port]
        while True:
            try:
                packet = yield store.get() # wait for next packet
                
                # queue delay = time spent waiting in queue
                queue_delay = self.env.now - getattr(packet, 'arrival_to_port', self.env.now)
                packet.switch_delays.append(('queue_delay', self.router_id, port, queue_delay))
                
                # Track queue delay statistics
                self.total_queue_delay += queue_delay
                self.queue_delay_samples += 1
                
                # compute serialization/service time for this hop
                output_port = self.route_packet(packet)
                
                # pick link bandwidth based on destination
                if output_port == self.PORT_LOCAL:
                    link_ser = (packet.size_bytes * 8) / ACCESS_LINK_BW
                else:
                    link_ser = (packet.size_bytes * 8) / MESH_LINK_BW
                
                # total service = router processing + serialization
                service_time = SWITCH_PROCESSING_DELAY + link_ser
                
                # simulate service
                yield self.env.timeout(service_time)
                
                # record service delay
                packet.switch_delays.append(('service', self.router_id, service_time))
                
                # forward packet
                if output_port == self.PORT_LOCAL:
                    # Deliver to local node
                    node_id = self.connected_nodes.get(output_port)
                    if node_id is not None:
                        yield self.env.process(self._deliver_to_node(packet, node_id))
                else:
                    # Forward to neighboring router
                    next_router = self.connected_routers.get(output_port)
                    if next_router:
                        # Determine input port for next router based on direction
                        next_input_port = self._get_opposite_port(output_port)
                        success = next_router.enqueue_packet_to_port(next_input_port, packet)
                        if not success:
                            LOGGER.log(f"Router {self.router_id} -> {next_router.router_id}: packet dropped")
                
                self.packets_processed += 1
                
            except Exception as e:
                LOGGER.log(f"Router {self.router_id} port {port} service error: {e}")
                yield self.env.timeout(0.01)

    def _get_opposite_port(self, output_port):
        """Get the opposite port direction for neighboring router."""
        opposite = {
            self.PORT_NORTH: self.PORT_SOUTH,
            self.PORT_EAST: self.PORT_WEST,
            self.PORT_SOUTH: self.PORT_NORTH,
            self.PORT_WEST: self.PORT_EAST
        }
        return opposite.get(output_port, 0)

    def connect_node(self, node_id):
        """Connect a node to this router's local port."""
        self.connected_nodes[self.PORT_LOCAL] = node_id

    def connect_router(self, port, router):
        """Connect another router to this port."""
        self.connected_routers[port] = router

    def route_packet(self, packet):
        """Route packet using XY routing algorithm."""
        dest_id = packet.dest_id
        
        # Convert destination node ID to mesh coordinates
        dest_row = dest_id // self.mesh_size
        dest_col = dest_id % self.mesh_size
        
        # XY Routing: First move in X direction (horizontal), then Y direction (vertical)
        if self.col < dest_col:
            # Need to go East
            return self.PORT_EAST
        elif self.col > dest_col:
            # Need to go West
            return self.PORT_WEST
        elif self.row < dest_row:
            # Same column, need to go South
            return self.PORT_SOUTH
        elif self.row > dest_row:
            # Same column, need to go North
            return self.PORT_NORTH
        else:
            # Same router - deliver locally
            return self.PORT_LOCAL

    def _deliver_to_node(self, packet, node_id):
        """Deliver packet to final destination node."""
        # Add final delivery delay
        yield self.env.timeout(3e-9) # 3ns delivery delay

    def get_queue_stats(self):
        """Get queuing statistics."""
        avg_queue_delay = 0.0
        if self.queue_delay_samples > 0:
            avg_queue_delay = self.total_queue_delay / self.queue_delay_samples
        
        total_queued = sum(len(store.items) for store in self.input_queues.values())
        
        return {
            'avg_queue_delay': avg_queue_delay,
            'total_queue_delay': self.total_queue_delay,
            'queue_delay_samples': self.queue_delay_samples,
            'current_queued_packets': total_queued,
            'packets_processed': self.packets_processed,
            'packets_dropped': self.packets_dropped
        }

class CHIPacket:
    def __init__(self, msg_type, address, source_id, dest_id, data=None, fwd_id=None, tx_id=None, operation_id=None):
        self.msg_type = msg_type
        self.address = address
        self.source_id = source_id
        self.dest_id = dest_id
        self.data = data
        self.fwd_id = fwd_id
        self.tx_id = tx_id or str(uuid.uuid4())[:8]
        self.operation_id = operation_id
        self.creation_time = 0
        self.size_bytes = PACKET_SIZE
        self.hop_count = 0
        self.path = []
        self.switch_delays = []
        self.total_network_delay = 0.0 # NEW: Track total network delay

    def add_hop(self, hop_id):
        self.hop_count += 1
        self.path.append(hop_id)

    def __repr__(self):
        return f"{self.msg_type.name}(A{self.address}, {self.source_id}→{self.dest_id}, hops:{self.hop_count})"

print("Updated timing parameters for realistic on-chip NoC:")
print(f" - Router processing: {SWITCH_PROCESSING_DELAY*1e9:.1f}ns")
print(f" - Access links: {ACCESS_LINK_BW/1e9:.0f} Gbps")
print(f" - Mesh links: {MESH_LINK_BW/1e9:.0f} Gbps")
print(f" - Delivery delay: 3ns")

# CHI Protocol Node with MINIMAL INSTRUMENTATION ADDITIONS
class CHINode:
    def __init__(self, env, node_id, node_type, is_home_node, home_node_id):
        self.env = env
        self.id = node_id
        self.node_type = node_type
        self.is_home_node = is_home_node
        self.home_node_id = home_node_id
        self.is_active = True

        # Set role based on corrected architecture
        if node_type == NodeType.GLOBAL_MEMORY:
            self.role = "HN" # Global Memory is HOME NODE
        elif node_type == NodeType.CPU:
            self.role = "CPU"
            self.is_active = False # CPU inactive for now
        else:
            self.role = "RN" # All GPUs are REQUEST NODES

        # Initialize memory/cache structures
        self._initialize_memory_cache()

        # LRU Cache for GPUs (ONLY 4 slots!)
        if self.node_type == NodeType.GPU:
            self.lru_cache = OrderedDict() # Maintains insertion order for LRU
            self.lru_evictions = 0
            self.temporal_locality_hits = 0

        # Statistics
        self.cache_hits = 0
        self.cache_misses = 0
        self.snoop_count = 0
        self.read_operations = 0
        self.write_operations = 0
        self.total_cache_access_time = 0.0
        self.total_miss_penalty_time = 0.0
        self.total_memory_access_time = 0.0
        self.writeback_count = 0 # NEW: Track writebacks

        # Protocol handling
        self.pending_transactions = {}
        self.pending_writes = {}

        # Network interface
        self.incoming_packets = simpy.Store(env)
        self.packet_router = None

        if self.is_active:
            self.env.process(self._message_processor())

    def _initialize_memory_cache(self):
        """Initialize memory and cache based on node type"""
        self.cache = {}
        self.memory = {}

        if self.node_type == NodeType.GLOBAL_MEMORY:
            # Global memory (Home Node) - 32 addresses
            self.memory = {addr: random.randint(10, 255) for addr in range(GLOBAL_MEMORY_SIZE)}
            # Directory for coherency management
            self.directory = defaultdict(list)
        elif self.node_type == NodeType.GPU:
            # GPU nodes have NO persistent cache dict - only LRU!
            pass
        elif self.node_type == NodeType.CPU:
            # CPU inactive for now
            pass

    def lru_cache_access(self, address):
        """PROPER LRU cache access with timing"""
        if address in self.lru_cache:
            # Cache hit - move to end (most recent)
            entry = self.lru_cache.pop(address)
            self.lru_cache[address] = entry
            entry.update_access(self.env.now)
            return entry
        return None

    def lru_cache_insert(self, address, state, data):
        """PROPER LRU cache insert with eviction"""
        # Remove if already exists
        if address in self.lru_cache:
            del self.lru_cache[address]

        # Evict if cache is full (4 slots only!)
        if len(self.lru_cache) >= GPU_CACHE_SIZE:
            self._lru_evict_oldest()

        # Insert new entry (automatically goes to end - most recent)
        new_entry = LRUCacheEntry(state, data, self.env.now)
        self.lru_cache[address] = new_entry
        LOGGER.log(f"{self.role}{self.id} LRU inserted A{address} ({state.name}) - cache size: {len(self.lru_cache)}")

    def _lru_evict_oldest(self):
        """CORRECTED: Evict least recently used entry with proper writeback"""
        if self.lru_cache:
            # OrderedDict: first item is least recently used
            lru_address, lru_entry = next(iter(self.lru_cache.items()))

            # CRITICAL FIX: If evicting Modified (dirty) data, perform writeback!
            if lru_entry.state == CacheState.Modified:
                LOGGER.log(f"WRITEBACK: {self.role}{self.id} evicting DIRTY A{lru_address}={lru_entry.data} - sending writeback to memory")
                self._perform_writeback(lru_address, lru_entry.data)
                self.writeback_count += 1

            # Remove from cache
            del self.lru_cache[lru_address]
            self.lru_evictions += 1
            LOGGER.log(f"{self.role}{self.id} LRU evicted A{lru_address} (accessed {lru_entry.access_count} times)")

    def _check_other_gpu_has_modified_data(self, address):
        """
        Check if any other GPU (not this one) has modified data for the given address.
        This is used to avoid unnecessary writebacks when multiple GPUs are competing for write access.
        """
        if hasattr(self, 'network') and self.network:
            for node in self.network.nodes:
                # Skip self and non-GPU nodes
                if node.id == self.id or node.node_type != NodeType.GPU:
                    continue
                # Check if this other GPU has the address in Modified state
                if (hasattr(node, 'lru_cache') and address in node.lru_cache and
                    node.lru_cache[address].state == CacheState.Modified):
                    return True
        return False

    def _perform_writeback(self, address, data):
        """CRITICAL FIX: Perform actual writeback to global memory"""
        if self.packet_router:
            # Create writeback packet to home node
            writeback_packet = CHIPacket(
                MessageType.WriteBackFull, address, self.id, self.home_node_id,
                data=data, tx_id=str(uuid.uuid4())[:8]
            )
            self.send_packet(writeback_packet)
            LOGGER.log(f"WRITEBACK: {self.role}{self.id} sent writeback A{address}={data} to GlobalMem")

    def lru_cache_update_state(self, address, new_state):
        """Update cache entry state and refresh LRU order"""
        if address in self.lru_cache:
            entry = self.lru_cache.pop(address)
            entry.state = new_state
            entry.update_access(self.env.now)
            self.lru_cache[address] = entry

    def send_packet(self, packet):
        """Send packet through network"""
        if self.packet_router:
            self.packet_router(packet)
        else:
            LOGGER.log(f"No packet router configured for {self.role}{self.id}")

    def receive_packet(self, packet):
        """Receive packet from network"""
        if self.is_active:
            self.incoming_packets.put(packet)

    def _message_processor(self):
        """Main message processing loop"""
        while True:
            try:
                packet = yield self.incoming_packets.get()
                LOGGER.log(f"{self.role}{self.id} processing {packet}")

                if self.is_home_node:
                    yield self.env.process(self._handle_home_node_message(packet))
                else:
                    yield self.env.process(self._handle_request_node_message(packet))

            except Exception as e:
                LOGGER.log(f"Error in {self.role}{self.id} message processor: {e}")
                yield self.env.timeout(0.01)

    def _handle_home_node_message(self, packet):
        """Handle messages at Global Memory Home Node with INSTRUMENTATION"""
        try:
            # Add memory access delay for home node operations
            yield self.env.timeout(MEMORY_ACCESS_DELAY)
            self.total_memory_access_time += MEMORY_ACCESS_DELAY

            # MINIMAL INSTRUMENTATION: Log HN memory access
            if PERF_TRACKER:
                PERF_TRACKER.log_hn_memory_access()

            if packet.msg_type == MessageType.ReadShared:
                yield self.env.process(self._handle_home_read_shared(packet))
            elif packet.msg_type == MessageType.WriteUnique:
                yield self.env.process(self._handle_home_write_unique(packet))
            elif packet.msg_type == MessageType.SnpResp:
                self._handle_snoop_response(packet)
            elif packet.msg_type == MessageType.WriteBackFull: # NEW: Handle writeback
                yield self.env.process(self._handle_writeback(packet))
            else:
                LOGGER.log(f"HN received unexpected message: {packet.msg_type}")

        except Exception as e:
            LOGGER.log(f"HN message handling error: {e}")

    def _handle_writeback(self, packet):
        """CRITICAL FIX: Handle writeback from GPU - update global memory"""
        address = packet.address
        data = packet.data
        source_gpu = packet.source_id

        # Update global memory with the writeback data
        old_value = self.memory.get(address, 0)
        self.memory[address] = data

        # MINIMAL INSTRUMENTATION: Log additional HN memory access for writeback
        if PERF_TRACKER:
            PERF_TRACKER.log_hn_memory_access()

        LOGGER.log(f"WRITEBACK: GlobalMem received writeback A{address}: {old_value} -> {data} from GPU{source_gpu}")
        LOGGER.log(f"MEMORY UPDATED: GlobalMem A{address} now has CURRENT data={data}")

    def _handle_home_read_shared(self, packet):
        """Handle ReadShared at Home Node with proper coherency"""
        address = packet.address
        requester = packet.source_id

        # Check directory for current sharers
        current_sharers = self.directory.get(address, [])

        # CRITICAL FIX: Validate that sharers actually have valid data
        valid_sharers = []
        for sharer_id in current_sharers:
            if sharer_id < len(self.network.nodes):
                node = self.network.nodes[sharer_id]
                # Check if this node actually has valid data for this address
                if (hasattr(node, 'lru_cache') and address in node.lru_cache and
                    node.lru_cache[address].state != CacheState.Invalid):
                    valid_sharers.append(sharer_id)

        if not valid_sharers:
            # No one has valid data - serve from memory as EXCLUSIVE (single reader)
            data = self.memory.get(address, 0)
            response = CHIPacket(
                MessageType.CompData, address, self.id, requester,
                data=data, tx_id=packet.tx_id, operation_id=packet.operation_id
            )
            # Mark this as exclusive grant for single reader
            response.is_exclusive_grant = True
            self.send_packet(response)

            # Update directory with only the requester
            self.directory[address] = [requester]
            LOGGER.log(f"HN served ReadShared A{address}={data} from MEMORY to RN{requester} [EXCLUSIVE - single reader]")

        else:
            # Someone has valid data - forward from their cache
            owner = valid_sharers[0]
            forward = CHIPacket(
                MessageType.SnpSharedFwd, address, self.id, owner,
                fwd_id=requester, tx_id=packet.tx_id, operation_id=packet.operation_id
            )
            self.send_packet(forward)

            # Add requester to valid sharers if not already there
            if requester not in valid_sharers:
                self.directory[address] = valid_sharers + [requester]

            LOGGER.log(f"HN forwarding ReadShared A{address} from RN{owner} to RN{requester}")

    def _handle_home_write_unique(self, packet):
        """Handle WriteUnique at Home Node - CORRECTED CHI BEHAVIOR"""
        address = packet.address
        requester = packet.source_id
        data = packet.data

        # Get current sharers (excluding requester)
        old_sharers = [s for s in self.directory.get(address, []) if s != requester]

        if not old_sharers:
            # CORRECTED: NO immediate memory update - data stays dirty in requester's cache
            # According to CHI protocol, WriteUnique does NOT immediately write to memory
            # Memory is only updated on explicit writeback (WriteBackFull) transactions
            self.directory[address] = [requester]

            response = CHIPacket(
                MessageType.CompAck, address, self.id, requester,
                tx_id=packet.tx_id, operation_id=packet.operation_id
            )
            self.send_packet(response)
            LOGGER.log(f"HN WriteUnique A{address}={data} - DATA STAYS DIRTY IN RN{requester}, MEMORY UNCHANGED")

        else:
            # Need to invalidate other sharers first
            self.pending_writes[packet.tx_id] = {
                'requester': requester,
                'acks_needed': len(old_sharers),
                'address': address,
                'data': data,
                'operation_id': packet.operation_id,
                'received_acks': 0
            }

            # Send invalidations to all other sharers
            for sharer in old_sharers:
                snoop = CHIPacket(
                    MessageType.SnpUnique, address, self.id, sharer,
                    tx_id=packet.tx_id, operation_id=packet.operation_id
                )
                self.send_packet(snoop)

            LOGGER.log(f"HN WriteUnique A{address}={data} - invalidating {old_sharers}, MEMORY WILL REMAIN UNCHANGED")

    def _handle_snoop_response(self, packet):
        """Handle snoop response (invalidation acknowledgment)"""
        # FIXED: Clean up directory entry for the responding node
        address = packet.address
        source_id = packet.source_id

        # Remove the invalidated node from directory
        if address in self.directory:
            if source_id in self.directory[address]:
                self.directory[address].remove(source_id)

        write_info = self.pending_writes.get(packet.tx_id)
        if write_info:
            write_info['received_acks'] += 1

            if write_info['received_acks'] >= write_info['acks_needed']:
                # All invalidations received - complete the write
                requester = write_info['requester']
                address = write_info['address']
                data = write_info['data']

                # CORRECTED: Update directory but DO NOT UPDATE MEMORY
                # According to CHI protocol, data stays dirty in requester's cache
                self.directory[address] = [requester]

                # Send completion acknowledgment
                response = CHIPacket(
                    MessageType.CompAck, address, self.id, requester,
                    tx_id=packet.tx_id, operation_id=write_info['operation_id']
                )
                self.send_packet(response)
                LOGGER.log(f"HN completed WriteUnique A{address}={data} - DATA STAYS DIRTY IN RN{requester}, MEMORY UNCHANGED")

                del self.pending_writes[packet.tx_id]

    def _handle_request_node_message(self, packet):
        """Handle messages at request nodes (GPUs)"""
        try:
            if packet.msg_type == MessageType.CompData:
                yield self.env.process(self._handle_completion_data(packet))
            elif packet.msg_type == MessageType.CompAck:
                self._handle_completion_ack(packet)
            elif packet.msg_type == MessageType.SnpSharedFwd:
                yield self.env.process(self._handle_snoop_shared_forward(packet))
            elif packet.msg_type == MessageType.SnpUnique:
                yield self.env.process(self._handle_snoop_unique(packet))
            elif packet.msg_type == MessageType.SnpRespData:
                yield self.env.process(self._handle_snoop_response_data(packet))
            else:
                LOGGER.log(f"RN received unexpected message: {packet.msg_type}")

        except Exception as e:
            LOGGER.log(f"RN message handling error: {e}")

    def _handle_completion_data(self, packet):
        """CORRECTED: Handle data completion with proper Exclusive vs Shared state"""
        # Add cache hit delay for LRU access
        yield self.env.timeout(CACHE_HIT_DELAY + LRU_ACCESS_OVERHEAD)
        self.total_cache_access_time += CACHE_HIT_DELAY + LRU_ACCESS_OVERHEAD

        # CORRECTED: Check if this is exclusive grant (single reader from memory)
        if hasattr(packet, 'is_exclusive_grant') and packet.is_exclusive_grant:
            # Single reader from memory gets EXCLUSIVE state (green)
            self.lru_cache_insert(packet.address, CacheState.Exclusive, packet.data)
            LOGGER.log(f"{self.role}{self.id} received data A{packet.address}={packet.data} [EXCLUSIVE CLEAN - single reader]")
        else:
            # Multiple readers or forwarded data gets SHARED state (blue)
            self.lru_cache_insert(packet.address, CacheState.Shared, packet.data)
            LOGGER.log(f"{self.role}{self.id} received data A{packet.address}={packet.data} [SHARED - multiple readers]")

        # Complete transaction
        event = self.pending_transactions.pop(packet.tx_id, None)
        if event and not event.triggered:
            event.succeed()

    def _handle_completion_ack(self, packet):
        """Handle write completion"""
        event = self.pending_transactions.pop(packet.tx_id, None)
        if event and not event.triggered:
            event.succeed()
        LOGGER.log(f"{self.role}{self.id} write A{packet.address} complete")

    def _handle_snoop_shared_forward(self, packet):
        """CORRECTED: Handle snoop forward request with proper writeback"""
        # Check LRU cache
        cache_entry = self.lru_cache_access(packet.address)

        if cache_entry and cache_entry.state in [CacheState.Modified, CacheState.Exclusive, CacheState.Shared]:
            # Add cache access delay
            yield self.env.timeout(CACHE_HIT_DELAY + LRU_ACCESS_OVERHEAD)
            self.total_cache_access_time += CACHE_HIT_DELAY + LRU_ACCESS_OVERHEAD

            # CRITICAL FIX: If Modified, perform implicit writeback to memory!
            if cache_entry.state == CacheState.Modified:
                LOGGER.log(f"WRITEBACK: {self.role}{self.id} forwarding DIRTY data A{packet.address}={cache_entry.data} - implicit writeback to memory")
                self._perform_writeback(packet.address, cache_entry.data)
                self.writeback_count += 1

            # CORRECTED: Exclusive->Shared transition when sharing occurs
            if cache_entry.state == CacheState.Exclusive:
                LOGGER.log(f"STATE TRANSITION: {self.role}{self.id} A{packet.address} Exclusive -> Shared (sharing with RN{packet.fwd_id})")

            # Transition to Shared when forwarding (from any state)
            self.lru_cache_update_state(packet.address, CacheState.Shared)

            # Send data to requester
            response = CHIPacket(
                MessageType.SnpRespData, packet.address, self.id, packet.fwd_id,
                data=cache_entry.data, tx_id=packet.tx_id, operation_id=packet.operation_id
            )
            self.send_packet(response)
            LOGGER.log(f"{self.role}{self.id} forwarded A{packet.address}={cache_entry.data} to RN{packet.fwd_id}")

        else:
            # No valid data to forward
            response = CHIPacket(
                MessageType.SnpRespData, packet.address, self.id, packet.fwd_id,
                data=0, tx_id=packet.tx_id, operation_id=packet.operation_id
            )
            self.send_packet(response)

    def _handle_snoop_unique(self, packet):
        """CORRECTED: Handle invalidation request with proper writeback"""
        old_state = CacheState.Invalid
        writeback_data = None

        if packet.address in self.lru_cache:
            old_state = self.lru_cache[packet.address].state
            writeback_data = self.lru_cache[packet.address].data

            # CRITICAL FIX: If evicting Modified data, perform implicit writeback!
            # MODIFIED: Do NOT writeback if another GPU already has modified data for this address
            if old_state == CacheState.Modified:
                # Check if any other GPU already has modified data for this address
                other_gpu_has_modified = self._check_other_gpu_has_modified_data(packet.address)

                if not other_gpu_has_modified:
                    LOGGER.log(f"WRITEBACK: {self.role}{self.id} invalidating DIRTY A{packet.address}={writeback_data} - implicit writeback to memory")
                    self._perform_writeback(packet.address, writeback_data)
                    self.writeback_count += 1
                else:
                    LOGGER.log(f"NO WRITEBACK: {self.role}{self.id} invalidating DIRTY A{packet.address}={writeback_data} - skipping writeback (another GPU already has modified data)")

            # Remove from LRU cache
            del self.lru_cache[packet.address]

        self.snoop_count += 1

        # Send invalidation acknowledgment
        response = CHIPacket(
            MessageType.SnpResp, packet.address, self.id, packet.source_id,
            tx_id=packet.tx_id, operation_id=packet.operation_id
        )
        self.send_packet(response)
        LOGGER.log(f"{self.role}{self.id} invalidated A{packet.address} ({old_state.name})")

    def _handle_snoop_response_data(self, packet):
        """Handle forwarded data from another GPU"""
        # Add cache access delay
        yield self.env.timeout(CACHE_HIT_DELAY + LRU_ACCESS_OVERHEAD)
        self.total_cache_access_time += CACHE_HIT_DELAY + LRU_ACCESS_OVERHEAD

        # Insert into LRU cache as Shared
        self.lru_cache_insert(packet.address, CacheState.Shared, packet.data)

        # Complete transaction
        event = self.pending_transactions.pop(packet.tx_id, None)
        if event and not event.triggered:
            event.succeed()

        LOGGER.log(f"{self.role}{self.id} received forwarded data A{packet.address}={packet.data} [LRU cached]")

    def issue_read_operation(self, address, operation_id=None):
        """Issue read operation with PROPER LRU cache behavior"""
        if not self.is_active or self.node_type != NodeType.GPU:
            return self.env.event().succeed()

        if not (0 <= address < GLOBAL_MEMORY_SIZE):
            LOGGER.log(f"RN{self.id} invalid address {address}")
            return self.env.event().succeed()

        def read_process():
            # Check LRU cache first
            cache_entry = self.lru_cache_access(address)

            if cache_entry and cache_entry.state != CacheState.Invalid:
                # CACHE HIT - add realistic cache hit delay
                yield self.env.timeout(CACHE_HIT_DELAY + LRU_ACCESS_OVERHEAD)
                self.cache_hits += 1
                self.total_cache_access_time += CACHE_HIT_DELAY + LRU_ACCESS_OVERHEAD
                LOGGER.log(f"{self.role}{self.id} LRU cache HIT A{address} ({cache_entry.state.name}) - delay {(CACHE_HIT_DELAY + LRU_ACCESS_OVERHEAD)*1e9:.1f}ns")
                return

            # CACHE MISS - apply miss penalty first
            yield self.env.timeout(CACHE_MISS_PENALTY)
            self.cache_misses += 1
            self.read_operations += 1
            self.total_miss_penalty_time += CACHE_MISS_PENALTY
            LOGGER.log(f"{self.role}{self.id} LRU cache MISS A{address} - miss penalty {CACHE_MISS_PENALTY*1e9:.1f}ns")

            # Send request to home node
            tx_id = str(uuid.uuid4())[:8]
            completion_event = self.env.event()
            self.pending_transactions[tx_id] = completion_event

            request = CHIPacket(
                MessageType.ReadShared, address, self.id, self.home_node_id,
                tx_id=tx_id, operation_id=operation_id
            )
            self.send_packet(request)
            LOGGER.log(f"{self.role}{self.id} -> ReadShared A{address} (MISS, TX:{tx_id})")

            # Wait for network response
            yield completion_event

        return self.env.process(read_process())

    def issue_write_operation(self, address, data, operation_id=None):
        """Issue write operation - CORRECTED CHI BEHAVIOR"""
        if not self.is_active or self.node_type != NodeType.GPU:
            return self.env.event().succeed()

        if not (0 <= address < GLOBAL_MEMORY_SIZE):
            LOGGER.log(f"RN{self.id} invalid address {address}")
            return self.env.event().succeed()

        def write_process():
            # Add cache access delay for write
            yield self.env.timeout(CACHE_HIT_DELAY + LRU_ACCESS_OVERHEAD)
            self.write_operations += 1
            self.total_cache_access_time += CACHE_HIT_DELAY + LRU_ACCESS_OVERHEAD

            # CORRECTED: Update local LRU cache to Modified (dirty) state FIRST
            # According to CHI protocol, data stays dirty in cache until explicit writeback
            self.lru_cache_insert(address, CacheState.Modified, data)

            # Send WriteUnique to home node (for coherency, NOT memory update)
            tx_id = str(uuid.uuid4())[:8]
            completion_event = self.env.event()
            self.pending_transactions[tx_id] = completion_event

            request = CHIPacket(
                MessageType.WriteUnique, address, self.id, self.home_node_id,
                data=data, tx_id=tx_id, operation_id=operation_id
            )
            self.send_packet(request)
            LOGGER.log(f"{self.role}{self.id} -> WriteUnique A{address}={data} [LRU updated to Modified/DIRTY]")

            # Wait for network response
            yield completion_event

        return self.env.process(write_process())

    def get_cache_display_data(self):
        """Get cache data for visualization with LRU info"""
        cache_data = {}

        if self.node_type == NodeType.GPU:
            # Show all possible addresses
            for addr in range(GLOBAL_MEMORY_SIZE):
                if addr in self.lru_cache:
                    entry = self.lru_cache[addr]
                    cache_data[addr] = {
                        'state': entry.get_state_char(),
                        'data': entry.data,
                        'lru_position': list(self.lru_cache.keys()).index(addr)
                    }
                else:
                    cache_data[addr] = {'state': 'I', 'data': None, 'lru_position': -1}

        return cache_data

    def get_memory_display_data(self):
        """Get memory data for visualization"""
        if self.node_type == NodeType.GLOBAL_MEMORY:
            return dict(self.memory)
        return {}

    def get_lru_cache_stats(self):
        """Get LRU cache specific statistics"""
        total_accesses = self.cache_hits + self.cache_misses
        hit_rate = (self.cache_hits / max(total_accesses, 1)) * 100

        return {
            'cache_hits': self.cache_hits,
            'cache_misses': self.cache_misses,
            'hit_rate_percent': hit_rate,
            'lru_evictions': self.lru_evictions,
            'writeback_count': self.writeback_count, # NEW
            'current_cache_size': len(self.lru_cache) if hasattr(self, 'lru_cache') else 0,
            'max_cache_size': GPU_CACHE_SIZE
        }

print("CHI Node created with MINIMAL instrumentation additions")
print("Only added HN memory access tracking - no other changes")

# PROPER 2D Mesh Network with XY Routing
class MeshNetwork:
    def __init__(self, env, visualizer=None):
        self.env = env
        self.visualizer = visualizer
        
        # Network components
        self.nodes = []
        self.routers = [] # Mesh routers
        
        # Build the mesh topology
        self._build_mesh_topology()
        
        # Global packet delivery system
        self.packet_delivery_queue = simpy.Store(env)
        self.env.process(self._packet_delivery_processor())
        
        LOGGER.log("PROPER 2D Mesh Network initialized")
        LOGGER.log(f" {N_HOSTS} IPs: {N_GPUS} GPUs + 1 CPU + 1 Memory")
        LOGGER.log(f" Home Node: Global Memory (ID {GLOBAL_MEMORY_ID})")
        LOGGER.log(f" {MESH_SIZE}x{MESH_SIZE} mesh with {MESH_SIZE*MESH_SIZE} routers")

    def _build_mesh_topology(self):
        """Build the complete Mesh topology with proper connections."""
        # 1. Create mesh routers in a 4x4 grid
        for row in range(MESH_SIZE):
            router_row = []
            for col in range(MESH_SIZE):
                router_id = f"router_{row}_{col}"
                router = MeshRouter(self.env, router_id, row, col, MESH_SIZE)
                router_row.append(router)
                self.routers.append(router)
        
        # Organize routers in a 2D array for easier access
        self.router_grid = []
        for row in range(MESH_SIZE):
            router_row = []
            for col in range(MESH_SIZE):
                idx = row * MESH_SIZE + col
                router_row.append(self.routers[idx])
            self.router_grid.append(router_row)
        
        # 2. Connect routers to each other (mesh connections)
        for row in range(MESH_SIZE):
            for col in range(MESH_SIZE):
                router = self.router_grid[row][col]
                
                # Connect to North neighbor
                if row > 0:
                    north_router = self.router_grid[row-1][col]
                    router.connect_router(router.PORT_NORTH, north_router)
                
                # Connect to East neighbor
                if col < MESH_SIZE - 1:
                    east_router = self.router_grid[row][col+1]
                    router.connect_router(router.PORT_EAST, east_router)
                
                # Connect to South neighbor
                if row < MESH_SIZE - 1:
                    south_router = self.router_grid[row+1][col]
                    router.connect_router(router.PORT_SOUTH, south_router)
                
                # Connect to West neighbor
                if col > 0:
                    west_router = self.router_grid[row][col-1]
                    router.connect_router(router.PORT_WEST, west_router)
        
        # 3. Create and connect nodes to routers
        for i in range(N_HOSTS):
            # Determine node type
            if i < N_GPUS:
                node = CHINode(self.env, i, NodeType.GPU, False, GLOBAL_MEMORY_ID)
            elif i == CPU_NODE_ID:
                node = CHINode(self.env, i, NodeType.CPU, False, GLOBAL_MEMORY_ID)
                node.is_active = False
            else:
                node = CHINode(self.env, i, NodeType.GLOBAL_MEMORY, True, GLOBAL_MEMORY_ID)
            
            # Connect node to network routing
            node.packet_router = self._route_packet
            node.network = self # Back reference
            self.nodes.append(node)
            
            # Connect node to appropriate router (one node per router position)
            router_row = i // MESH_SIZE
            router_col = i % MESH_SIZE
            router = self.router_grid[router_row][router_col]
            router.connect_node(i)
            
            LOGGER.log(f"Connected {node.role}{i} to router_({router_row},{router_col})")
        
        LOGGER.log("Mesh topology built with XY routing")

    def _route_packet(self, packet):
        """Route packet through Mesh network with realistic delays."""
        packet.creation_time = self.env.now
        self.env.process(self._route_packet_through_routers(packet))

    def _route_packet_through_routers(self, packet):
        """Route packet through actual routers with proper delays."""
        source_id = packet.source_id
        dest_id = packet.dest_id
        
        # Add initial hop (source node)
        packet.add_hop(f"Node_{source_id}")
        
        # Determine source and destination router coordinates
        src_row = source_id // MESH_SIZE
        src_col = source_id % MESH_SIZE
        dst_row = dest_id // MESH_SIZE
        dst_col = dest_id % MESH_SIZE
        
        total_delay = 0.0
        
        # Stage 1: Source node to source router
        yield self.env.timeout(self._get_access_link_delay())
        packet.add_hop(f"router_{src_row}_{src_col}")
        total_delay += self._get_access_link_delay()
        
        # Stage 2: Route through mesh using XY routing
        current_row, current_col = src_row, src_col
        
        # First move in X direction (columns)
        while current_col != dst_col:
            if current_col < dst_col:
                # Move East
                current_col += 1
            else:
                # Move West
                current_col -= 1
            
            # Add router processing and link delay
            yield self.env.timeout(SWITCH_PROCESSING_DELAY)
            yield self.env.timeout(self._get_mesh_link_delay())
            total_delay += SWITCH_PROCESSING_DELAY + self._get_mesh_link_delay()
            
            packet.add_hop(f"router_{current_row}_{current_col}")
        
        # Then move in Y direction (rows)
        while current_row != dst_row:
            if current_row < dst_row:
                # Move South
                current_row += 1
            else:
                # Move North
                current_row -= 1
            
            # Add router processing and link delay
            yield self.env.timeout(SWITCH_PROCESSING_DELAY)
            yield self.env.timeout(self._get_mesh_link_delay())
            total_delay += SWITCH_PROCESSING_DELAY + self._get_mesh_link_delay()
            
            packet.add_hop(f"router_{current_row}_{current_col}")
        
        # Stage 3: Destination router to destination node
        yield self.env.timeout(self._get_access_link_delay())
        total_delay += self._get_access_link_delay()
        packet.add_hop(f"Node_{dest_id}")
        
        # Record packet metrics
        packet.hop_count = len(packet.path) - 1 if len(packet.path) > 0 else 0
        packet.total_network_delay = total_delay
        
        # Log metrics to performance tracker
        if PERF_TRACKER:
            PERF_TRACKER.log_message(packet.msg_type, packet.source_id, packet.dest_id,
                                   size_bytes=packet.size_bytes, hop_count=packet.hop_count)
        
        # Queue packet for delivery
        self.packet_delivery_queue.put((packet, dest_id))
        
        # Update visualizer if available
        if self.visualizer:
            self.visualizer.add_packet_animation(packet, f"path_{packet.tx_id}")
        
        LOGGER.log(f"Routed {packet} via {len(packet.path)}-hop path ({total_delay*1000:.2f}ms)")

    def _get_access_link_delay(self):
        """Calculate access link delay (Node to router)."""
        return (PACKET_SIZE * 8) / ACCESS_LINK_BW

    def _get_mesh_link_delay(self):
        """Calculate mesh link delay (router to router)."""
        return (PACKET_SIZE * 8) / MESH_LINK_BW

    def _packet_delivery_processor(self):
        """Process packet deliveries to final destinations."""
        while True:
            try:
                packet, dest_id = yield self.packet_delivery_queue.get()
                
                # Deliver to destination node
                if 0 <= dest_id < len(self.nodes):
                    self.nodes[dest_id].receive_packet(packet)
                    LOGGER.log(f"Delivered {packet} to {self.nodes[dest_id].role}{dest_id}")
                else:
                    LOGGER.log(f"Invalid destination: {dest_id}")
                    
            except Exception as e:
                LOGGER.log(f"Packet delivery error: {e}")
                yield self.env.timeout(0.01)

# Traffic Generator (unchanged - topology independent)
class RealisticTrafficGenerator:
    def __init__(self, network):
        self.network = network

    def generate_operation(self):
        """Generate random operation for GPU nodes only."""
        # Only GPU nodes can initiate operations (not CPU or Global Memory)
        gpu_nodes = list(range(N_GPUS))
        node_id = random.choice(gpu_nodes)
        address = random.randint(0, GLOBAL_MEMORY_SIZE - 1)
        
        if random.random() < 0.6:
            return ('read', node_id, address, None)
        else:
            value = random.randint(1, 255)
            return ('write', node_id, address, value)

# Logging System
class SimulatorLogger:
    def __init__(self):
        self.message_queue = queue.Queue()

    def log(self, message, level="INFO"):
        timestamp = time.strftime("%H:%M:%S")
        formatted_msg = f"[{timestamp}] {level}: {message}"
        self.message_queue.put(formatted_msg)

    def get_messages(self):
        messages = []
        try:
            while True:
                messages.append(self.message_queue.get_nowait())
        except queue.Empty:
            pass
        return messages

LOGGER = SimulatorLogger()

# ENHANCED Performance Tracker with comprehensive metrics
class PerformanceTracker:
    def __init__(self, env):
        self.env = env
        self.operation_logs = []
        self.total_operations = 0
        self.completed_operations = 0
        self.failed_operations = 0
        self.total_messages = 0
        self.total_bytes = 0 # total payload bytes sent
        self.total_hop_count = 0 # sum of hops across packets
        self.packet_count = 0 # number of packets routed
        self.hn_message_count = 0 # messages seen by Home Node (HN)
        self.hn_memory_accesses = 0 # explicit memory accesses (writebacks / HN reads)
        self.total_queue_delay = 0.0 # NEW: Track total queuing delays
        self.queue_delay_samples = 0 # NEW: Count of queue delay samples
        self.lock = threading.Lock()

    def log_operation_start(self, operation_id, node_id, operation_type, address, value=None):
        with self.lock:
            log_entry = {
                'operation_id': operation_id,
                'node_id': node_id,
                'operation_type': operation_type,
                'address': address,
                'value': value,
                'start_time': self.env.now,
                'status': 'STARTED'
            }
            self.operation_logs.append(log_entry)
            self.total_operations += 1

    def log_operation_complete(self, operation_id, status='COMPLETED'):
        with self.lock:
            for log_entry in reversed(self.operation_logs):
                if log_entry['operation_id'] == operation_id:
                    log_entry['end_time'] = self.env.now
                    log_entry['latency'] = log_entry['end_time'] - log_entry['start_time']
                    log_entry['status'] = status
                    if status == 'COMPLETED':
                        self.completed_operations += 1
                    else:
                        self.failed_operations += 1
                    break

    def log_message(self, message_type, source_id, dest_id, size_bytes=64, hop_count=0):
        """Call whenever a packet is injected/finished routing to accumulate stats."""
        with self.lock:
            self.total_messages += 1
            self.total_bytes += size_bytes
            self.total_hop_count += hop_count
            self.packet_count += 1
            
            # Count HN involvement
            if dest_id == GLOBAL_MEMORY_ID or source_id == GLOBAL_MEMORY_ID:
                self.hn_message_count += 1

    def log_hn_memory_access(self):
        with self.lock:
            self.hn_memory_accesses += 1

    def log_queue_delay(self, queue_delay):
        """Log queue delay from switch processing"""
        with self.lock:
            self.total_queue_delay += queue_delay
            self.queue_delay_samples += 1

    def compute_summary(self, sim_time_seconds):
        """Return a dict with aggregated metrics."""
        avg_latency = 0.0
        latencies = [l.get('latency', 0) for l in self.operation_logs if 'latency' in l]
        if latencies:
            avg_latency = sum(latencies) / len(latencies)

        avg_hop = (self.total_hop_count / max(self.packet_count, 1))
        throughput_bytes_per_sec = (self.total_bytes / max(sim_time_seconds, 1e-12))

        # link capacity summary (simple): fraction of time link would be saturated by total bytes
        access_link_capacity_bps = ACCESS_LINK_BW / 8 # Convert to bytes per second
        mesh_capacity_bps = MESH_LINK_BW / 8

        # Basic utilization estimate across network (very approximate)
        access_utilization = throughput_bytes_per_sec / access_link_capacity_bps
        mesh_utilization = throughput_bytes_per_sec / mesh_capacity_bps

        # Queue delay statistics
        avg_queue_delay = 0.0
        if self.queue_delay_samples > 0:
            avg_queue_delay = self.total_queue_delay / self.queue_delay_samples

        return {
            'total_operations': self.total_operations,
            'completed_operations': self.completed_operations,
            'failed_operations': self.failed_operations,
            'total_messages': self.total_messages,
            'total_bytes': int(self.total_bytes),
            'avg_latency_s': avg_latency,
            'avg_hop_count': avg_hop,
            'throughput_Bps': throughput_bytes_per_sec,
            'access_link_utilization': access_utilization,
            'backbone_link_utilization': mesh_utilization,
            'hn_message_count': self.hn_message_count,
            'hn_memory_accesses': self.hn_memory_accesses,
            'avg_queue_delay_s': avg_queue_delay,
            'total_queue_delay_s': self.total_queue_delay,
            'queue_delay_samples': self.queue_delay_samples
        }

    def print_summary(self, sim_time_seconds):
        s = self.compute_summary(sim_time_seconds)
        LOGGER.log("=== SIMULATION SUMMARY ===")
        LOGGER.log(f"Sim time: {sim_time_seconds:.6f} s")
        LOGGER.log(f"Operations: {s['total_operations']} completed: {s['completed_operations']} failed: {s['failed_operations']}")
        LOGGER.log(f"Messages: {s['total_messages']} total bytes: {s['total_bytes']} B")
        LOGGER.log(f"Avg op latency: {s['avg_latency_s']*1e6:.3f} us")
        LOGGER.log(f"Avg hop count per packet: {s['avg_hop_count']:.3f}")
        LOGGER.log(f"Throughput: {s['throughput_Bps']/1e6:.6f} MB/s")
        LOGGER.log(f"Access-link util. (approx): {s['access_link_utilization']*100:.4f}%")
        LOGGER.log(f"Mesh-link util. (approx): {s['backbone_link_utilization']*100:.4f}%")
        LOGGER.log(f"HN messages: {s['hn_message_count']} HN memory-access events: {s['hn_memory_accesses']}")
        LOGGER.log(f"QUEUING DELAYS:")
        LOGGER.log(f" Avg queue delay: {s['avg_queue_delay_s']*1e6:.3f} μs")
        LOGGER.log(f" Total queue delay: {s['total_queue_delay_s']*1e3:.6f} ms")
        LOGGER.log(f" Queue delay samples: {s['queue_delay_samples']}")
        return s

    def export_to_excel(self, filename=None):
        """Export detailed transaction logs to Excel file."""
        if not filename:
            timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
            filename = f"chi_transactions_{timestamp}.xlsx"

        try:
            import pandas as pd
            # Create DataFrame from operation logs
            df = pd.DataFrame(self.operation_logs)

            # Add computed fields
            if not df.empty:
                df['latency_us'] = df.get('latency', 0) * 1e6 # Convert to microseconds
                df['latency_ns'] = df.get('latency', 0) * 1e9 # Convert to nanoseconds

            # Export to Excel
            with pd.ExcelWriter(filename, engine='openpyxl') as writer:
                df.to_excel(writer, sheet_name='Transactions', index=False)

                # Add summary sheet
                summary = self.compute_summary(self.env.now if hasattr(self, 'env') else 1.0)
                summary_df = pd.DataFrame(list(summary.items()), columns=['Metric', 'Value'])
                summary_df.to_excel(writer, sheet_name='Summary', index=False)

            LOGGER.log(f"Transaction logs exported to {filename}")
            return filename

        except ImportError:
            # Fallback to CSV if pandas not available
            filename = filename.replace('.xlsx', '.csv')
            return self.export_to_csv(filename)

    def export_to_csv(self, filename=None):
        """Export transaction logs to CSV file."""
        if not filename:
            timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
            filename = f"chi_transactions_{timestamp}.csv"

        try:
            with open(filename, 'w', newline='', encoding='utf-8') as csvfile:
                if self.operation_logs:
                    fieldnames = self.operation_logs[0].keys()
                    writer = csv.DictWriter(csvfile, fieldnames=fieldnames)
                    writer.writeheader()

                    for log_entry in self.operation_logs:
                        # Add computed latency fields
                        enhanced_entry = dict(log_entry)
                        if 'latency' in enhanced_entry:
                            enhanced_entry['latency_us'] = enhanced_entry['latency'] * 1e6
                            enhanced_entry['latency_ns'] = enhanced_entry['latency'] * 1e9
                        writer.writerow(enhanced_entry)

            LOGGER.log(f"Transaction logs exported to {filename}")
            return filename

        except Exception as e:
            LOGGER.log(f"Error exporting to CSV: {e}")
            return None

    def export_parameters(self, filename=None):
        """Export calculated performance parameters to file."""
        if not filename:
            timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
            filename = f"noc_parameters_{timestamp}.txt"

        sim_time = self.env.now if hasattr(self, 'env') else 1.0
        summary = self.compute_summary(sim_time)

        try:
            with open(filename, 'w', encoding='utf-8') as f:
                f.write("CHI Mesh NoC Performance Parameters\n")
                f.write("=" * 45 + "\n\n")
                f.write(f"Simulation Time: {sim_time:.6f} seconds\n\n")

                f.write("OPERATION STATISTICS\n")
                f.write("-" * 20 + "\n")
                f.write(f"Total Operations: {summary['total_operations']}\n")
                f.write(f"Completed Operations: {summary['completed_operations']}\n")
                f.write(f"Failed Operations: {summary['failed_operations']}\n")
                f.write(f"Success Rate: {(summary['completed_operations']/max(summary['total_operations'], 1)*100):.2f}%\n\n")

                f.write("NETWORK STATISTICS\n")
                f.write("-" * 18 + "\n")
                f.write(f"Total Messages: {summary['total_messages']}\n")
                f.write(f"Total Bytes Transferred: {summary['total_bytes']} B ({summary['total_bytes']/1024:.2f} KB)\n")
                f.write(f"Average Hop Count: {summary['avg_hop_count']:.3f} hops/packet\n")
                f.write(f"Throughput: {summary['throughput_Bps']/1e6:.6f} MB/s\n\n")

                f.write("LATENCY ANALYSIS\n")
                f.write("-" * 16 + "\n")
                f.write(f"Average Operation Latency: {summary['avg_latency_s']*1e6:.3f} μs\n")
                f.write(f"Average Operation Latency: {summary['avg_latency_s']*1e9:.1f} ns\n\n")

                f.write("LINK UTILIZATION (Approximate)\n")
                f.write("-" * 30 + "\n")
                f.write(f"Access Link Utilization: {summary['access_link_utilization']*100:.4f}%\n")
                f.write(f"Mesh Link Utilization: {summary['backbone_link_utilization']*100:.4f}%\n\n")

                f.write("HOME NODE INVOLVEMENT\n")
                f.write("-" * 21 + "\n")
                f.write(f"Messages involving Home Node: {summary['hn_message_count']}\n")
                f.write(f"Global Memory Access Events: {summary['hn_memory_accesses']}\n")
                f.write(f"HN Message Ratio: {(summary['hn_message_count']/max(summary['total_messages'], 1)*100):.2f}%\n\n")

                f.write("NETWORK CONFIGURATION\n")
                f.write("-" * 21 + "\n")
                f.write(f"Topology: 2D Mesh with XY Routing\n")
                f.write(f"Total Nodes: {N_HOSTS} ({N_GPUS} GPUs + 1 CPU + 1 Memory)\n")
                f.write(f"Routers: {MESH_SIZE}x{MESH_SIZE} = {MESH_SIZE*MESH_SIZE}\n")
                f.write(f"Access Link Bandwidth: {ACCESS_LINK_BW/1e9:.0f} Gbps\n")
                f.write(f"Mesh Link Bandwidth: {MESH_LINK_BW/1e9:.0f} Gbps\n")
                f.write(f"Router Processing Delay: {SWITCH_PROCESSING_DELAY*1e9:.1f} ns\n")
                f.write(f"Packet Size: {PACKET_SIZE} bytes\n")
                f.write(f"GPU Cache Size: {GPU_CACHE_SIZE} slots (LRU)\n")

            LOGGER.log(f"Performance parameters exported to {filename}")
            return filename

        except Exception as e:
            LOGGER.log(f"Error exporting parameters: {e}")
            return None

# Initialize global performance tracker
PERF_TRACKER = None

print("Added minimal network instrumentation and enhanced PerformanceTracker")
print("Key metrics tracked:")
print(" - Latency, bandwidth, hop count, throughput")
print(" - Home node involvement and memory accesses")
print(" - Excel/CSV export and parameter extraction")

# Proper Mesh Visualizer with realistic packet animation through routers
class MeshVisualizer:
    MESSAGE_COLORS = {
        MessageType.ReadShared: '#FF4444',
        MessageType.WriteUnique: '#44FF44',
        MessageType.CompData: '#4444FF',
        MessageType.CompAck: '#FF44FF',
        MessageType.SnpUnique: '#FFAA44',
        MessageType.SnpResp: '#44FFAA',
        MessageType.SnpSharedFwd: '#AAAA44',
        MessageType.SnpRespData: '#AA44FF',
        MessageType.WriteBackFull: '#FF8800', # NEW: Writeback color
    }

    STATE_COLORS = {
        'I': '#CCCCCC', # Invalid - gray
        'S': '#4444FF', # Shared - blue
        'M': '#FF4444', # Modified (dirty) - red
        'E': '#44FF44', # Exclusive (clean) - green
    }

    def __init__(self):
        self.main_fig, self.main_ax = plt.subplots(1, 1, figsize=(16, 11))
        self.cache_fig = None
        self.cache_ax = None
        self.cache_window = None
        self.animated_packets = []
        self._setup_topology()

    def _setup_topology(self):
        """Setup 2D mesh layout with proper router positions."""
        # Router positions in a 4x4 grid
        self.router_positions = {}
        for row in range(MESH_SIZE):
            for col in range(MESH_SIZE):
                router_id = f"router_{row}_{col}"
                x = col * 3  # Horizontal spacing
                y = (MESH_SIZE - 1 - row) * 3  # Vertical spacing (flip for display)
                self.router_positions[router_id] = (x, y)

        # Node positions (co-located with routers)
        self.node_positions = {}
        for i in range(N_HOSTS):
            row = i // MESH_SIZE
            col = i % MESH_SIZE
            # Offset nodes slightly from routers for visibility
            x = col * 3 + 0.5
            y = (MESH_SIZE - 1 - row) * 3 + 0.5
            self.node_positions[i] = (x, y)

        self._draw_topology()

    def _draw_topology(self):
        """Draw network topology with proper Mesh connections."""
        self.main_ax.clear()
        self.main_ax.set_facecolor('#F8F8FF')
        self.main_ax.set_title("CHI 2D Mesh NoC [BLACKMAGNET]",
                              fontsize=14, fontweight='bold')

        # Draw mesh links (router to router connections)
        for row in range(MESH_SIZE):
            for col in range(MESH_SIZE):
                router_pos = self.router_positions[f"router_{row}_{col}"]
                
                # Draw horizontal links (East connections)
                if col < MESH_SIZE - 1:
                    next_router_pos = self.router_positions[f"router_{row}_{col+1}"]
                    self.main_ax.plot([router_pos[0], next_router_pos[0]], 
                                    [router_pos[1], next_router_pos[1]],
                                    'lightcoral', linewidth=2, alpha=0.7)
                
                # Draw vertical links (South connections)
                if row < MESH_SIZE - 1:
                    next_router_pos = self.router_positions[f"router_{row+1}_{col}"]
                    self.main_ax.plot([router_pos[0], next_router_pos[0]], 
                                    [router_pos[1], next_router_pos[1]],
                                    'lightcoral', linewidth=2, alpha=0.7)

        # Draw access links (node to router connections)
        for i in range(N_HOSTS):
            node_pos = self.node_positions[i]
            row = i // MESH_SIZE
            col = i % MESH_SIZE
            router_pos = self.router_positions[f"router_{row}_{col}"]
            self.main_ax.plot([node_pos[0], router_pos[0]], [node_pos[1], router_pos[1]],
                            'lightblue', linewidth=1.5, alpha=0.7)

        # Draw routers
        for router_id, pos in self.router_positions.items():
            circle = patches.Circle(pos, 0.3, facecolor='orange', edgecolor='darkorange', linewidth=2)
            self.main_ax.add_patch(circle)
            # Extract row and col from router_id for labeling
            parts = router_id.split('_')
            row, col = parts[1], parts[2]
            self.main_ax.text(pos[0], pos[1], f"R\n{row},{col}", ha='center', va='center',
                            fontsize=8, fontweight='bold', color='white')

        # Draw nodes
        for i, pos in self.node_positions.items():
            if i < N_GPUS:
                # GPU nodes
                rect = patches.Rectangle((pos[0]-0.3, pos[1]-0.3), 0.6, 0.6,
                                       facecolor='lightblue', edgecolor='darkblue', linewidth=2)
                label = f"GPU\n{i}"
                color = 'darkblue'
            elif i == CPU_NODE_ID:
                # CPU node
                rect = patches.Rectangle((pos[0]-0.3, pos[1]-0.3), 0.6, 0.6,
                                       facecolor='lightgray', edgecolor='gray', linewidth=2)
                label = f"CPU\n{i}"
                color = 'black'
            else:
                # Global Memory (Home Node)
                rect = patches.Rectangle((pos[0]-0.3, pos[1]-0.3), 0.6, 0.6,
                                       facecolor='gold', edgecolor='darkorange', linewidth=3)
                label = f"HN\nMEM{i}"
                color = 'black'

            self.main_ax.add_patch(rect)
            self.main_ax.text(pos[0], pos[1], label, ha='center', va='center',
                            fontsize=7, fontweight='bold', color=color)

        # Set limits and formatting
        max_x = max(pos[0] for pos in list(self.node_positions.values()) + 
                   list(self.router_positions.values()))
        max_y = max(pos[1] for pos in list(self.node_positions.values()) + 
                   list(self.router_positions.values()))
        
        self.main_ax.set_xlim(-1, max_x + 1)
        self.main_ax.set_ylim(-1, max_y + 1)
        self.main_ax.set_aspect('equal')
        self.main_ax.grid(True, alpha=0.3)

        # Add CHI Protocol Message Legend at the bottom
        self._add_message_legend()

    def _add_message_legend(self):
        """Add CHI protocol message legend at the bottom of the topology."""
        # Create legend entries for CHI protocol messages
        legend_elements = []
        message_descriptions = {
            MessageType.ReadShared: 'ReadShared (Request)',
            MessageType.WriteUnique: 'WriteUnique (Request)',
            MessageType.CompData: 'CompData (Response)',
            MessageType.CompAck: 'CompAck (Response)',
            MessageType.SnpUnique: 'SnpUnique (Snoop)',
            MessageType.SnpResp: 'SnpResp (Snoop Response)',
            MessageType.SnpSharedFwd: 'SnpSharedFwd (Snoop)',
            MessageType.SnpRespData: 'SnpRespData (Snoop Response)',
            MessageType.WriteBackFull: 'WriteBackFull (Writeback)'
        }

        # Create colored patches for the legend
        for msg_type, description in message_descriptions.items():
            color = self.MESSAGE_COLORS.get(msg_type, '#000000')
            patch = patches.Patch(facecolor=color, label=description)
            legend_elements.append(patch)

        # Position legend at the bottom with proper spacing
        legend = self.main_ax.legend(
            handles=legend_elements,
            loc='upper center',
            bbox_to_anchor=(0.5, -0.05), # Position below the plot
            ncol=3, # 3 columns for better layout
            fontsize=9,
            frameon=True,
            fancybox=True,
            shadow=True,
            title="CHI Protocol Messages",
            title_fontsize=10
        )

        # Style the legend
        legend.get_frame().set_facecolor('#F8F8FF')
        legend.get_frame().set_edgecolor('black')
        legend.get_frame().set_alpha(0.9)

    def create_cache_window(self):
        """Create cache/memory visualization window."""
        if self.cache_window is None:
            self.cache_window = tk.Toplevel()
            self.cache_window.title("CORRECTED CHI: Memory doesn't track dirty GPU ownership (Modified state = GPU owns)")
            self.cache_window.geometry("1600x900")
            
            self.cache_fig, self.cache_ax = plt.subplots(figsize=(16, 9))
            canvas = FigureCanvasTkAgg(self.cache_fig, master=self.cache_window)
            canvas.draw()
            canvas.get_tk_widget().pack(fill=tk.BOTH, expand=True)
            
            self._setup_cache_display()

    def _setup_cache_display(self):
        """Setup cache state visualization."""
        if self.cache_ax is None:
            return
            
        self.cache_ax.clear()
        self.cache_ax.set_facecolor('#F0F0F0')
        self.cache_ax.set_title("Memory states visualization",
                               fontsize=16, fontweight='bold', pad=20)

        # Setup grid with proper space utilization
        self.cache_ax.set_xlim(-1.2, N_GPUS + 3.8)
        self.cache_ax.set_ylim(-1.5, GLOBAL_MEMORY_SIZE + 0.5)
        self.cache_ax.set_xlabel("GPU Nodes + Global Memory", fontsize=14, fontweight='bold')
        self.cache_ax.set_ylabel("Memory Addresses", fontsize=14, fontweight='bold')

        # Labels with proper spacing
        x_labels = [f"GPU{i}" for i in range(N_GPUS)] + ["GlobalMem"]
        x_positions = list(range(N_GPUS)) + [N_GPUS + 2] # 2-unit gap before memory
        
        self.cache_ax.set_xticks(x_positions)
        self.cache_ax.set_xticklabels(x_labels, fontsize=12, rotation=45, fontweight='bold')
        self.cache_ax.set_yticks(range(GLOBAL_MEMORY_SIZE))
        self.cache_ax.set_yticklabels([f"A{i}" for i in range(GLOBAL_MEMORY_SIZE)], fontsize=10)
        self.cache_ax.grid(True, alpha=0.5)

        # Enhanced Legend with writeback info
        state_legend = []
        state_names = {
            'I': 'Invalid',
            'S': 'Shared (Multiple readers)',
            'M': 'Modified (DIRTY - will writeback on evict/snoop)',
            'E': 'Exclusive Clean (Single reader from memory - GREEN)'
        }
        
        for state, color in self.STATE_COLORS.items():
            state_legend.append(patches.Patch(facecolor=color, label=state_names[state]))
        
        self.cache_ax.legend(handles=state_legend, loc='upper left',
                           bbox_to_anchor=(1.02, 1), fontsize=9)

    def add_packet_animation(self, packet, link_name):
        """Add packet animation showing route through routers."""
        if len(packet.path) < 2:
            return

        # Create animation path through actual routers and nodes
        animation_path = []
        for i, hop in enumerate(packet.path):
            if hop.startswith('Node_'):
                node_id = int(hop.split('_')[1])
                if node_id in self.node_positions:
                    animation_path.append(self.node_positions[node_id])
            elif hop.startswith('router_'):
                if hop in self.router_positions:
                    animation_path.append(self.router_positions[hop])

        if len(animation_path) >= 2:
            packet_info = {
                'packet': packet,
                'path': animation_path,
                'current_segment': 0,
                'segment_progress': 0.0,
                'patches': []
            }
            self.animated_packets.append(packet_info)

    def update_animation(self, frame):
        """Update packet animations through router path."""
        # Clear old animations
        for packet_info in self.animated_packets:
            for patch in packet_info['patches']:
                try:
                    patch.remove()
                except:
                    pass
            packet_info['patches'] = []

        # Update positions
        active_packets = []
        for packet_info in self.animated_packets:
            path = packet_info['path']
            segment = packet_info['current_segment']
            progress = packet_info['segment_progress']

            if segment < len(path) - 1:
                # Calculate current position
                start_pos = path[segment]
                end_pos = path[segment + 1]
                current_x = start_pos[0] + (end_pos[0] - start_pos[0]) * progress
                current_y = start_pos[1] + (end_pos[1] - start_pos[1]) * progress

                # Draw packet
                color = self.MESSAGE_COLORS.get(packet_info['packet'].msg_type, '#000000')
                packet_dot = patches.Circle((current_x, current_y), 0.15,
                                          facecolor=color, edgecolor='white', linewidth=1)
                self.main_ax.add_patch(packet_dot)
                packet_info['patches'].append(packet_dot)

                # Update progress
                packet_info['segment_progress'] += ANIM_SPEED
                if packet_info['segment_progress'] >= 1.0:
                    packet_info['current_segment'] += 1
                    packet_info['segment_progress'] = 0.0

                active_packets.append(packet_info)

        self.animated_packets = active_packets
        return []

    def update_cache_display(self, network):
        """CHI-Mesh NoC Simulator [BLACKMAGNET]"""
        if self.cache_ax is None:
            return
            
        self.cache_ax.clear()
        self._setup_cache_display()

        # Display GPU caches with LRU ordering
        for gpu_id in range(N_GPUS):
            node = network.nodes[gpu_id]
            cache_data = node.get_cache_display_data()
            
            for addr in range(GLOBAL_MEMORY_SIZE):
                cache_info = cache_data.get(addr, {'state': 'I', 'data': None, 'lru_position': -1})
                state = cache_info['state']
                data = cache_info['data']
                lru_pos = cache_info.get('lru_position', -1)
                
                color = self.STATE_COLORS.get(state, '#CCCCCC')
                
                # Adjust alpha based on LRU position
                alpha = 0.9 if state != 'I' else 0.3
                if lru_pos >= 0:
                    alpha = 0.5 + 0.4 * (lru_pos / max(GPU_CACHE_SIZE - 1, 1))
                
                rect = patches.Rectangle((gpu_id - 0.48, addr - 0.45), 0.96, 0.90,
                                       facecolor=color, edgecolor='black', linewidth=1, alpha=alpha)
                self.cache_ax.add_patch(rect)
                
                if state != 'I' and data is not None:
                    text = f"{state}\n{data}"
                    if lru_pos >= 0:
                        text += f"\nLRU:{lru_pos}"
                else:
                    text = state
                
                self.cache_ax.text(gpu_id, addr, text, ha='center', va='center',
                                 fontsize=8, fontweight='bold',
                                 color='white' if state != 'I' else 'black')

        # Display Global Memory
        global_mem_node = network.nodes[GLOBAL_MEMORY_ID]
        memory_data = global_mem_node.get_memory_display_data()
        x_pos = N_GPUS + 2 # 2-unit gap from last GPU
        
        for addr in range(GLOBAL_MEMORY_SIZE):
            value = memory_data.get(addr, 0)
            
            # Check if any GPU has this address in Modified state
            has_dirty = False
            for gpu_id in range(N_GPUS):
                cache_data = network.nodes[gpu_id].get_cache_display_data()
                if addr in cache_data and cache_data[addr]['state'] == 'M':
                    has_dirty = True
                    break
            
            if has_dirty:
                # Memory has stale data
                rect = patches.Rectangle((x_pos - 0.48, addr - 0.45), 0.96, 0.90,
                                       facecolor='#FFAAAA', edgecolor='red', linewidth=2)
                text = f"STALE\n{value}\n(GPU OWNS)"
            else:
                # Memory has current data
                rect = patches.Rectangle((x_pos - 0.48, addr - 0.45), 0.96, 0.90,
                                       facecolor='lightyellow', edgecolor='black', linewidth=1)
                text = f"CURRENT\n{value}"
            
            self.cache_ax.add_patch(rect)
            self.cache_ax.text(x_pos, addr, text, ha='center', va='center',
                             fontsize=8, fontweight='bold')

        if hasattr(self.cache_fig, 'canvas'):
            self.cache_fig.canvas.draw_idle()

print("Added Mesh visualizer (replacing Fat-Tree visualizer)")

# Simulation Controller (updated to use MeshNetwork)
def run_mesh_noc_simulation(command_queue, network, traffic_generator):
    """Run simulation with proper NoC routing and CORRECTED writeback."""
    env = network.env
    operation_counter = 0
    
    global PERF_TRACKER
    PERF_TRACKER = PerformanceTracker(env)
    
    LOGGER.log("CORRECTED CHI Protocol Mesh NoC Simulation started with ENHANCED PERFORMANCE TRACKING")
    LOGGER.log(f"Home Node: Global Memory (ID {GLOBAL_MEMORY_ID})")
    LOGGER.log(f"GPU nodes: {list(range(N_GPUS))} (all request nodes)")
    LOGGER.log("Packets route through ACTUAL routers with XY routing")
    LOGGER.log("CHI CORRECTED: WriteUnique does NOT immediately update memory")
    LOGGER.log("ENHANCED: Performance tracking with realistic on-chip timing")
    
    while True:
        try:
            command = command_queue.get(timeout=1.0)
            if command == 'exit':
                break
                
            parts = command.split()
            if len(parts) < 3:
                continue
                
            operation_counter += 1
            operation_id = f"op_{operation_counter}"
            
            try:
                operation = parts[0].lower()
                node_id = int(parts[1])
                address = int(parts[2])
                
                # Only GPU nodes can initiate operations
                if node_id not in range(N_GPUS):
                    LOGGER.log(f"Only GPU nodes (0-{N_GPUS-1}) can initiate operations")
                    continue
                    
                if not (0 <= address < GLOBAL_MEMORY_SIZE):
                    LOGGER.log(f"Invalid address {address}. Valid range: 0-{GLOBAL_MEMORY_SIZE-1}")
                    continue
                    
                node = network.nodes[node_id]
                
                if operation == 'read':
                    PERF_TRACKER.log_operation_start(operation_id, node_id, 'READ', address)
                    completion_event = node.issue_read_operation(address, operation_id)
                    result = env.run(until=env.any_of([completion_event, env.timeout(SIM_TIMEOUT)]))
                    
                    if completion_event in result:
                        PERF_TRACKER.log_operation_complete(operation_id)
                        LOGGER.log(f"READ #{operation_counter} completed (GPU{node_id} A{address})")
                    else:
                        PERF_TRACKER.log_operation_complete(operation_id, 'TIMEOUT')
                        LOGGER.log(f"READ #{operation_counter} TIMEOUT")
                        
                elif operation == 'write':
                    if len(parts) < 4:
                        continue
                    value = int(parts[3])
                    
                    PERF_TRACKER.log_operation_start(operation_id, node_id, 'WRITE', address, value)
                    completion_event = node.issue_write_operation(address, value, operation_id)
                    result = env.run(until=env.any_of([completion_event, env.timeout(SIM_TIMEOUT)]))
                    
                    if completion_event in result:
                        PERF_TRACKER.log_operation_complete(operation_id)
                        LOGGER.log(f"WRITE #{operation_counter} completed (GPU{node_id} A{address}={value}) [DIRTY in cache]")
                    else:
                        PERF_TRACKER.log_operation_complete(operation_id, 'TIMEOUT')
                        LOGGER.log(f"WRITE #{operation_counter} TIMEOUT")
                        
            except Exception as e:
                LOGGER.log(f"Operation error: {e}")
                
        except queue.Empty:
            continue
        except Exception as e:
            LOGGER.log(f"Simulation error: {e}")

print("Updated simulation controller for mesh topology")

# Main GUI Application for CORRECTED CHI Protocol Mesh NoC
class CorrectedCHIMeshNoCApp(tk.Tk):
    def __init__(self):
        super().__init__()
        self.title("CORRECTED CHI Protocol Mesh NoC with ENHANCED PERFORMANCE TRACKING")
        self.geometry("1200x850")
        self.configure(bg='#F0F0F0')
        
        # Initialize components
        self.env = simpy.Environment()
        self.visualizer = MeshVisualizer()
        self.network = MeshNetwork(self.env, self.visualizer)  # Changed from ProperFatTreeNetwork
        self.traffic_generator = RealisticTrafficGenerator(self.network)
        self.random_traffic_enabled = False
        
        self._create_gui()
        self._initialize_simulation()
        self._start_update_loops()
        
        LOGGER.log("CHI-Mesh NoC Simulator [BLACKMAGNET]")
        LOGGER.log("=" * 60)
        LOGGER.log("CHI PROTOCOL")
        LOGGER.log(f" Home Node: Global Memory (ID {GLOBAL_MEMORY_ID})")
        LOGGER.log(f" GPU Nodes: {list(range(N_GPUS))} (request nodes)")
        LOGGER.log(f" Global Memory: {GLOBAL_MEMORY_SIZE} addresses")
        LOGGER.log(f" GPU Caches: {GPU_CACHE_SIZE} slots (LRU policy)")
        LOGGER.log(f" {MESH_SIZE}x{MESH_SIZE} mesh topology with XY routing")
        LOGGER.log("ENHANCED: Realistic on-chip timing and performance tracking")
        LOGGER.log("Export capabilities: Transaction logs and performance parameters")
        LOGGER.log("=" * 60)

    def _create_gui(self):
        """Create GUI layout."""
        self.grid_rowconfigure(0, weight=1)
        self.grid_columnconfigure(0, weight=2)
        self.grid_columnconfigure(1, weight=1)

        # Main visualization panel
        viz_panel = ttk.LabelFrame(self, text="CHI-Mesh NoC Simulator [BLACKMAGNET]", padding=5)
        viz_panel.grid(row=0, column=0, sticky="nsew", padx=5, pady=5)
        
        self.canvas = FigureCanvasTkAgg(self.visualizer.main_fig, master=viz_panel)
        self.canvas.draw()
        self.canvas.get_tk_widget().pack(fill=tk.BOTH, expand=True)

        # Control panel
        control_panel = ttk.Frame(self)
        control_panel.grid(row=0, column=1, sticky="nsew", padx=5, pady=5)
        control_panel.grid_rowconfigure(6, weight=1)

        self._create_command_interface(control_panel)
        self._create_quick_actions(control_panel)
        self._create_traffic_controls(control_panel)
        self._create_cache_controls(control_panel)
        self._create_extract_panel(control_panel)
        self._create_log_panel(control_panel)

    def _create_command_interface(self, parent):
        """Create command interface."""
        cmd_frame = ttk.LabelFrame(parent, text="Command Interface", padding=5)
        cmd_frame.grid(row=0, column=0, sticky="ew", pady=(0, 5))
        cmd_frame.grid_columnconfigure(1, weight=1)

        ttk.Label(cmd_frame, text="Command:").grid(row=0, column=0, sticky="w")
        self.command_var = tk.StringVar()
        self.command_entry = ttk.Entry(cmd_frame, textvariable=self.command_var, width=25)
        self.command_entry.grid(row=0, column=1, sticky="ew", padx=(5, 0))
        self.command_entry.bind("<Return>", lambda e: self.execute_command())

        ttk.Button(cmd_frame, text="Execute", command=self.execute_command).grid(row=0, column=2, padx=(5, 0))

    def _create_quick_actions(self, parent):
        """Create quick action buttons."""
        quick_frame = ttk.LabelFrame(parent, text="Quick Actions (Test ENHANCED CHI with Performance Tracking)", padding=5)
        quick_frame.grid(row=1, column=0, sticky="ew", pady=(0, 5))

        actions = [
            ("Read GPU0 A0", "read 0 0"),
            ("Single Read (→E)", "read 3 12"),
            ("Second Read (E→S)", "exclusive_to_shared_test"),
            ("Modified WB Test", "modified_wb_test"),
            ("Coherency Test", "coherency_test"),
            ("Eviction Test", "eviction_test")
        ]

        for i, (text, command) in enumerate(actions):
            if command == "modified_wb_test":
                btn = ttk.Button(quick_frame, text=text, command=self.run_modified_writeback_test)
            elif command == "exclusive_to_shared_test":
                btn = ttk.Button(quick_frame, text=text, command=self.run_exclusive_to_shared_test)
            elif command == "coherency_test":
                btn = ttk.Button(quick_frame, text=text, command=self.run_coherency_test)
            elif command == "eviction_test":
                btn = ttk.Button(quick_frame, text=text, command=self.run_eviction_test)
            else:
                btn = ttk.Button(quick_frame, text=text,
                               command=lambda cmd=command: self.queue_command(cmd))
            
            btn.grid(row=i//2, column=i%2, padx=2, pady=2, sticky="ew")

        quick_frame.grid_columnconfigure(0, weight=1)
        quick_frame.grid_columnconfigure(1, weight=1)

    def _create_traffic_controls(self, parent):
        """Create traffic controls."""
        traffic_frame = ttk.LabelFrame(parent, text="Traffic Generation", padding=5)
        traffic_frame.grid(row=2, column=0, sticky="ew", pady=(0, 5))

        self.random_traffic_var = tk.BooleanVar()
        ttk.Checkbutton(traffic_frame, text="Enable Random Traffic",
                       variable=self.random_traffic_var,
                       command=self.toggle_random_traffic).pack(anchor='w')

    def _create_cache_controls(self, parent):
        """Create cache controls."""
        cache_frame = ttk.LabelFrame(parent, text="CORRECTED CHI Cache View", padding=5)
        cache_frame.grid(row=3, column=0, sticky="ew", pady=(0, 5))

        ttk.Button(cache_frame, text="Open Cache Window",
                  command=self.open_cache_window).pack(fill='x', pady=2)

    def _create_extract_panel(self, parent):
        """Create extract panel."""
        extract_frame = ttk.LabelFrame(parent, text="Extract Data & Performance Metrics", padding=5)
        extract_frame.grid(row=4, column=0, sticky="ew", pady=(0, 5))

        # Extract Logs button
        extract_logs_btn = ttk.Button(extract_frame, text="Extract Logs (Excel/CSV)",
                                    command=self.extract_logs)
        extract_logs_btn.pack(fill='x', pady=2)

        # Extract Parameters button
        extract_params_btn = ttk.Button(extract_frame, text="Extract Parameters (TXT)",
                                      command=self.extract_parameters)
        extract_params_btn.pack(fill='x', pady=2)

        # Performance Summary button
        summary_btn = ttk.Button(extract_frame, text="Performance Summary",
                               command=self.show_performance_summary)
        summary_btn.pack(fill='x', pady=2)

        # Enhanced info text
        info_text = f"""Realistic On-Chip NoC Timing:
• Router delay: {SWITCH_PROCESSING_DELAY*1e9:.0f}ns
• Access links: {ACCESS_LINK_BW/1e9:.0f} Gbps
• Mesh links: {MESH_LINK_BW/1e9:.0f} Gbps

Performance Metrics Tracked:
• Latency, bandwidth, hop count
• Home node involvement
• Memory access patterns
• Link utilization estimates"""

        info_label = ttk.Label(extract_frame, text=info_text, font=('Consolas', 8))
        info_label.pack(anchor='w', pady=(5, 0))

    def _create_log_panel(self, parent):
        """Create log panel."""
        log_frame = ttk.LabelFrame(parent, text="System Log", padding=3)
        log_frame.grid(row=5, column=0, sticky="nsew")
        log_frame.grid_rowconfigure(0, weight=1)
        log_frame.grid_columnconfigure(0, weight=1)

        self.log_display = ScrolledText(log_frame, height=15, width=50, wrap=tk.WORD,
                                      font=('Consolas', 8))
        self.log_display.grid(row=0, column=0, sticky="nsew")

        log_controls = ttk.Frame(log_frame)
        log_controls.grid(row=1, column=0, sticky="ew", pady=(3, 0))

        ttk.Button(log_controls, text="Clear", command=self.clear_log).pack(side='left')
        ttk.Button(log_controls, text="Exit", command=self.close_application).pack(side='right')

    def _initialize_simulation(self):
        """Initialize simulation thread."""
        self.command_queue = queue.Queue()
        self.simulation_thread = threading.Thread(
            target=run_mesh_noc_simulation,  # Changed from run_proper_noc_simulation
            args=(self.command_queue, self.network, self.traffic_generator),
            daemon=True
        )
        self.simulation_thread.start()
        
        self.animation = FuncAnimation(self.visualizer.main_fig, self.visualizer.update_animation,
                                     interval=100, blit=False, cache_frame_data=False)

    def _start_update_loops(self):
        """Start update loops."""
        self.after(100, self.update_log_display)
        self.after(2000, self.update_cache_display)
        self.after(int(RANDOM_TRAFFIC_PERIOD * 1000), self.generate_random_traffic)

    # Extract methods (unchanged from original)
    def extract_logs(self):
        """Extract transaction logs to Excel/CSV file."""
        try:
            if PERF_TRACKER:
                filename = PERF_TRACKER.export_to_excel()
                if filename:
                    messagebox.showinfo("Export Success", f"Transaction logs exported to:\n{filename}")
                    LOGGER.log(f"✅ Transaction logs exported to {filename}")
                else:
                    messagebox.showerror("Export Error", "Failed to export transaction logs")
            else:
                messagebox.showwarning("No Data", "No performance data available to export")
        except Exception as e:
            messagebox.showerror("Export Error", f"Error exporting logs: {str(e)}")
            LOGGER.log(f"❌ Error exporting logs: {e}")

    def extract_parameters(self):
        """Extract performance parameters to text file."""
        try:
            if PERF_TRACKER:
                filename = PERF_TRACKER.export_parameters()
                if filename:
                    messagebox.showinfo("Export Success", f"Performance parameters exported to:\n{filename}")
                    LOGGER.log(f"✅ Performance parameters exported to {filename}")
                else:
                    messagebox.showerror("Export Error", "Failed to export performance parameters")
            else:
                messagebox.showwarning("No Data", "No performance data available to export")
        except Exception as e:
            messagebox.showerror("Export Error", f"Error exporting parameters: {str(e)}")
            LOGGER.log(f"❌ Error exporting parameters: {e}")

    def show_performance_summary(self):
        """Show performance summary in a popup window."""
        try:
            if PERF_TRACKER:
                # Create summary window
                summary_window = tk.Toplevel(self)
                summary_window.title("Enhanced Performance Summary")
                summary_window.geometry("600x500")

                # Create text widget with scrollbar
                frame = ttk.Frame(summary_window)
                frame.pack(fill='both', expand=True, padx=10, pady=10)

                text_widget = ScrolledText(frame, wrap=tk.WORD, font=('Consolas', 10))
                text_widget.pack(fill='both', expand=True)

                # Get summary and display
                sim_time = PERF_TRACKER.env.now if hasattr(PERF_TRACKER, 'env') else 1.0
                summary = PERF_TRACKER.compute_summary(sim_time)

                summary_text = f"""Enhanced CHI Mesh NoC Performance Summary

{"="*55}

SIMULATION PARAMETERS
Simulation Time: {sim_time:.6f} seconds
Topology: 2D Mesh with realistic on-chip timing
Router Processing Delay: {SWITCH_PROCESSING_DELAY*1e9:.1f} ns
Access Link Bandwidth: {ACCESS_LINK_BW/1e9:.0f} Gbps
Mesh Link Bandwidth: {MESH_LINK_BW/1e9:.0f} Gbps

OPERATION STATISTICS
Total Operations: {summary['total_operations']}
Completed Operations: {summary['completed_operations']}
Failed Operations: {summary['failed_operations']}
Success Rate: {(summary['completed_operations']/max(summary['total_operations'], 1)*100):.2f}%

NETWORK PERFORMANCE
Total Messages: {summary['total_messages']}
Total Bytes: {summary['total_bytes']} B ({summary['total_bytes']/1024:.2f} KB)
Average Hop Count: {summary['avg_hop_count']:.3f} hops/packet
Throughput: {summary['throughput_Bps']/1e6:.6f} MB/s

LATENCY ANALYSIS
Average Operation Latency: {summary['avg_latency_s']*1e6:.3f} μs
Average Operation Latency: {summary['avg_latency_s']*1e9:.1f} ns

LINK UTILIZATION
Access Link Utilization: {summary['access_link_utilization']*100:.4f}%
Mesh Link Utilization: {summary['backbone_link_utilization']*100:.4f}%

HOME NODE METRICS
Messages involving Home Node: {summary['hn_message_count']}
Global Memory Access Events: {summary['hn_memory_accesses']}
HN Message Ratio: {(summary['hn_message_count']/max(summary['total_messages'], 1)*100):.2f}%

"""

                text_widget.insert('1.0', summary_text)
                text_widget.config(state='disabled')

                # Add close button
                ttk.Button(summary_window, text="Close",
                          command=summary_window.destroy).pack(pady=5)

            else:
                messagebox.showwarning("No Data", "No performance data available to display")

        except Exception as e:
            messagebox.showerror("Display Error", f"Error displaying summary: {str(e)}")

    def open_cache_window(self):
        """Open cache visualization window."""
        self.visualizer.create_cache_window()
        self.update_cache_display()

    def queue_command(self, command):
        """Queue command for simulation."""
        self.command_queue.put(command)
        LOGGER.log(f"Queued: {command}")

    def execute_command(self):
        """Execute user command."""
        command = self.command_var.get().strip()
        if command:
            self.queue_command(command)
            self.command_var.set("")

    def run_modified_writeback_test(self):
        """Test MODIFIED writeback behavior."""
        LOGGER.log("Testing ENHANCED writeback behavior...")
        LOGGER.log(" Step 1: GPU0 writes A8=150 (gets dirty)")
        self.queue_command("write 0 8 150")
        
        self.after(2000, lambda: [
            LOGGER.log(" Step 2: GPU1 writes A8=250 (should invalidate GPU0 WITHOUT writeback)"),
            LOGGER.log(" Because GPU1 will now have dirty data, GPU0 writeback is skipped"),
            self.queue_command("write 1 8 250")
        ])
        
        self.after(4000, lambda: [
            LOGGER.log(" Step 3: Check memory - should show STALE (GPU OWNS), no specific GPU tracked"),
            LOGGER.log(" GPU1 now has dirty A8=250, GPU0 was invalidated without writeback"),
            LOGGER.log(" Memory shows ownership is with GPU, not which specific GPU")
        ])

    def run_exclusive_to_shared_test(self):
        """Test CORRECTED Exclusive (E) to Shared (S) transition."""
        LOGGER.log("Testing ENHANCED Exclusive (E) to Shared (S) transition...")
        LOGGER.log(" Step 1: GPU0 reads A15 (should get EXCLUSIVE - green color)")
        self.queue_command("read 0 15")
        
        self.after(2000, lambda: [
            LOGGER.log(" Step 2: Check cache window - GPU0 should have A15 in EXCLUSIVE (E) green state"),
            LOGGER.log(" This shows single reader gets exclusive clean access")
        ])
        
        self.after(4000, lambda: [
            LOGGER.log(" Step 3: GPU1 also reads A15 (should trigger E→S transition)"),
            self.queue_command("read 1 15")
        ])
        
        self.after(6000, lambda: [
            LOGGER.log(" Step 4: Check cache window - BOTH GPUs should now have A15 in SHARED (S) blue state"),
            LOGGER.log(" Exclusive→Shared transition completed!")
        ])

    def run_coherency_test(self):
        """Test cache coherency with writeback."""
        LOGGER.log("Testing cache coherency with performance tracking...")
        self.queue_command("read 0 7") # GPU0 reads A7
        self.after(1000, lambda: self.queue_command("read 1 7")) # GPU1 reads A7 (should share)
        self.after(2000, lambda: self.queue_command("write 2 7 200")) # GPU2 writes A7 (invalidates others)
        self.after(3000, lambda: self.queue_command("read 0 7")) # GPU0 reads A7 (should get new value)

    def run_eviction_test(self):
        """Test LRU evictions with writeback."""
        LOGGER.log("Testing LRU evictions with performance tracking...")
        LOGGER.log("Writing to 5 addresses to force evictions...")
        
        # Fill cache completely then add one more to force eviction
        self.queue_command("write 0 0 10")
        self.after(500, lambda: self.queue_command("write 0 1 20"))
        self.after(1000, lambda: self.queue_command("write 0 2 30"))
        self.after(1500, lambda: self.queue_command("write 0 3 40"))
        self.after(2000, lambda: [
            LOGGER.log(" Cache full (4 slots), next write will evict oldest"),
            self.queue_command("write 0 4 50")
        ])

    def toggle_random_traffic(self):
        """Toggle random traffic."""
        self.random_traffic_enabled = self.random_traffic_var.get()
        if self.random_traffic_enabled:
            LOGGER.log("Random traffic ENABLED")
        else:
            LOGGER.log("Random traffic DISABLED")

    def generate_random_traffic(self):
        """Generate random traffic."""
        if self.random_traffic_enabled:
            operation, node_id, address, value = self.traffic_generator.generate_operation()
            if operation == 'read':
                command = f"read {node_id} {address}"
            else:
                command = f"write {node_id} {address} {value}"
            self.queue_command(command)
        
        self.after(int(RANDOM_TRAFFIC_PERIOD * 1000), self.generate_random_traffic)

    def update_cache_display(self):
        """Update cache display."""
        if hasattr(self.visualizer, 'cache_ax') and self.visualizer.cache_ax:
            self.visualizer.update_cache_display(self.network)
        
        self.after(2000, self.update_cache_display)

    def update_log_display(self):
        """Update log display."""
        messages = LOGGER.get_messages()
        for message in messages:
            self.log_display.insert(tk.END, message + "\n")
            
            # Color coding
            line_start = self.log_display.index(tk.END + "-2c linestart")
            line_end = tk.END + "-1c"
            
            if "ERROR" in message or "TIMEOUT" in message:
                self.log_display.tag_add("error", line_start, line_end)
                self.log_display.tag_config("error", foreground="red")
            elif "completed" in message or "WRITEBACK" in message or "✅" in message:
                self.log_display.tag_add("success", line_start, line_end)
                self.log_display.tag_config("success", foreground="green", font=("Consolas", 8, "bold"))
            elif "Testing" in message or "Step" in message or "ENHANCED" in message:
                self.log_display.tag_add("highlight", line_start, line_end)
                self.log_display.tag_config("highlight", foreground="blue", font=("Consolas", 8, "bold"))
            elif "STALE" in message or "DIRTY" in message or "CURRENT" in message:
                self.log_display.tag_add("chi_corrected", line_start, line_end)
                self.log_display.tag_config("chi_corrected", foreground="purple", font=("Consolas", 8, "bold"))
        
        if messages:
            self.log_display.see(tk.END)
        
        self.after(100, self.update_log_display)

    def clear_log(self):
        """Clear log display."""
        self.log_display.delete(1.0, tk.END)

    def close_application(self):
        """Close application."""
        self.random_traffic_enabled = False
        
        try:
            self.command_queue.put('exit')
        except:
            pass
        
        if hasattr(self.visualizer, 'cache_window') and self.visualizer.cache_window:
            self.visualizer.cache_window.destroy()
        
        # Print final performance summary
        if PERF_TRACKER:
            PERF_TRACKER.print_summary(PERF_TRACKER.env.now if hasattr(PERF_TRACKER, 'env') else 1.0)
        
        self.destroy()

# Main Entry Point
def main():
    try:
        app = CorrectedCHIMeshNoCApp()  # Changed from CorrectedCHIFatTreeNoCApp
        app.protocol("WM_DELETE_WINDOW", app.close_application)
        app.mainloop()
    except Exception as e:
        print(f"Startup failed: {e}")
        import traceback
        traceback.print_exc()

if __name__ == "__main__":
    main()