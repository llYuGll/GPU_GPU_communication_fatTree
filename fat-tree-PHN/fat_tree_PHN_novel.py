

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

# Configuration - Enhanced with PHN Architecture
N_HOSTS = 16 # Total IPs: 14 GPUs + 1 CPU + 1 Global Memory
N_GPUS = 14 # GPU nodes 0-13
N_SPINE = 2 # Level 2 switches
N_LEAF = 4 # Level 1 switches
LEAF_HOSTS = 4 # IPs per leaf switch

# PHN CLUSTER CONFIGURATION
PHN_SEGMENTS = {
    'G1': {'gpus': [0, 1, 2, 3], 'addresses': list(range(0, 10))},     # G1m: A0-A9
    'G2': {'gpus': [4, 5, 6, 7], 'addresses': list(range(10, 20))},    # G2m: A10-A19
    'G3': {'gpus': [8, 9, 10, 11], 'addresses': list(range(20, 30))},  # G3m: A20-A29
    'G_prime': {'gpus': [12, 13], 'addresses': list(range(30, 32))}     # Global: A30-A31
}

# MEMORY CONFIGURATION
GLOBAL_MEMORY_SIZE = 32 # Global memory: 0-31 addresses
GPU_CACHE_SIZE = 4 # GPU cache ONLY 4 slots (LRU policy)
PHN_CACHE_SIZE = 6 # PHN cache size
CPU_NODE_ID = 14 # CPU (inactive)
GLOBAL_MEMORY_ID = 15 # Global Memory (HOME NODE)

# PHN NODE IDs
PHN_G1_ID = 16  # Attached to leaf 0
PHN_G2_ID = 17  # Attached to leaf 1
PHN_G3_ID = 18  # Attached to leaf 2

# NETWORK INFRASTRUCTURE PARAMETERS
ACCESS_LINK_BW = 200e9 # 200 Gbps GPU to Leaf
BACKBONE_LINK_BW = 400e9 # 400 Gbps Leaf to Spine
SWITCH_PROCESSING_DELAY = 3e-9 # 3ns per switch hop
BUFFER_SIZE = 16 # Switch buffer size
PACKET_SIZE = 64 # Packet size (bytes)

# CACHE TIMING - Realistic values
CACHE_HIT_DELAY = 2e-9 # 2ns for cache hit
CACHE_MISS_PENALTY = 30e-9 # 30ns miss penalty
MEMORY_ACCESS_DELAY = 100e-9 # 100ns memory access
PHN_ACCESS_DELAY = 60e-9 # 60ns PHN cache access
LRU_ACCESS_OVERHEAD = 0.5e-9 # 0.5ns LRU overhead

# TRAFFIC CONFIGURATION
LOCAL_TRAFFIC_RATIO = 0.85  # 85% local cluster traffic
CROSS_CLUSTER_RATIO = 0.15  # 15% cross-cluster traffic

# SIMULATION PARAMETERS
ANIM_SPEED = 0.2
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
    WriteBackFull = 8
    # PHN-specific messages
    PHNRead = 9
    PHNWrite = 10
    PHNInvalidate = 11

class CacheState(Enum):
    Invalid = 0 # I
    Shared = 1 # S
    Modified = 2 # M (Dirty)
    # Removed Exclusive state as per requirement
    Used = 3 # U (One-time use for cross-cluster reads)
    UpdatedOnce = 4 # UP (One-time use for cross-cluster writes)

class NodeType(Enum):
    GPU = 0
    CPU = 1
    GLOBAL_MEMORY = 2
    PHN = 3  # Partial Home Node

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

# Enhanced LRU Cache Entry with one-time use states
class LRUCacheEntry:
    def __init__(self, state, data, timestamp):
        self.state = state
        self.data = data
        self.creation_time = timestamp
        self.last_access_time = timestamp
        self.access_count = 1
        self.is_one_time_use = (state == CacheState.Used or state == CacheState.UpdatedOnce)
        # new fields for timed display:
        self.is_display_only = False   # when True: shown in GUI but not accessible
        self.visible_until = None      # env.now + seconds (set by node process)

    def update_access(self, timestamp):
        self.last_access_time = timestamp
        self.access_count += 1

    def get_state_char(self):
        state_map = {
            CacheState.Invalid: 'I',
            CacheState.Shared: 'S',
            CacheState.Modified: 'M',
            CacheState.Used: 'U',          # Cross-cluster read, one-time use
            CacheState.UpdatedOnce: 'UP'   # Cross-cluster write, one-time use
        }
        return state_map.get(self.state, 'I')

    def can_hit(self):
        """Check if this entry can provide cache hits"""

        # If the entry is display-only, it should not be accessible
        if getattr(self, 'is_display_only', False):
            return False
        if self.is_one_time_use and self.access_count > 1:
            return False  # One-time use entries can't hit after first use
        return self.state != CacheState.Invalid

# PHN Cache Entry
class PHNCacheEntry:
    def __init__(self, data, timestamp, is_exclusive=False):
        self.data = data
        self.creation_time = timestamp
        self.last_access_time = timestamp
        self.is_exclusive = is_exclusive

    def update_access(self, timestamp):
        self.last_access_time = timestamp

# CHI Packet (enhanced for PHN)
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
        self.total_network_delay = 0.0
        self.is_cross_cluster = False  # Track cross-cluster transactions
        self.is_one_time_use = False   # Track one-time use transactions

    def add_hop(self, hop_id):
        self.hop_count += 1
        self.path.append(hop_id)

    def __repr__(self):
        return f"{self.msg_type.name}(A{self.address}, {self.source_id}→{self.dest_id}, hops:{self.hop_count})"




# Fat-Tree Switch (unchanged from original)
class FatTreeSwitch:
    def __init__(self, env, switch_id, level, switch_type):
        self.env = env
        self.switch_id = switch_id
        self.level = level # 0=leaf, 1=spine
        self.switch_type = switch_type

        # Enhanced queuing system
        self.input_queues = {} # port -> simpy.Store
        self.port_service_procs = {} # port -> process

        # Routing table: destination -> output port
        self.routing_table = {}

        # Connected nodes/switches
        self.connected_nodes = {} # port -> node_id
        self.connected_switches = {} # port -> switch_id

        # Statistics
        self.packets_processed = 0
        self.packets_dropped = 0
        self.total_queue_delay = 0.0
        self.queue_delay_samples = 0

    def _ensure_port_exists(self, port):
        if port not in self.input_queues:
            self.input_queues[port] = simpy.Store(self.env)
            proc = self.env.process(self._port_service_loop(port))
            self.port_service_procs[port] = proc

    def enqueue_packet_to_port(self, port, packet):
        self._ensure_port_exists(port)
        queue_store = self.input_queues[port]

        if len(queue_store.items) >= BUFFER_SIZE:
            self.packets_dropped += 1
            LOGGER.log(f"Switch {self.switch_id} DROP on port {port} (buffer full)")
            return False
        else:
            packet.arrival_to_port = self.env.now
            queue_store.put(packet)
            return True

    def _port_service_loop(self, port):
        store = self.input_queues[port]
        while True:
            try:
                packet = yield store.get()

                queue_delay = self.env.now - getattr(packet, 'arrival_to_port', self.env.now)
                packet.switch_delays.append(('queue_delay', self.switch_id, port, queue_delay))

                self.total_queue_delay += queue_delay
                self.queue_delay_samples += 1

                output_port = self.route_packet(packet)

                if output_port in self.connected_switches:
                    link_ser = (packet.size_bytes * 8) / BACKBONE_LINK_BW
                else:
                    link_ser = (packet.size_bytes * 8) / ACCESS_LINK_BW

                service_time = SWITCH_PROCESSING_DELAY + link_ser
                yield self.env.timeout(service_time)

                packet.switch_delays.append(('service', self.switch_id, service_time))

                if output_port in self.connected_nodes:
                    node_id = self.connected_nodes[output_port]
                    yield self.env.process(self._deliver_to_node(packet, node_id))
                elif output_port in self.connected_switches:
                    next_switch = self.connected_switches[output_port]
                    next_input_port = self._map_to_input_port(output_port, next_switch)
                    success = next_switch.enqueue_packet_to_port(next_input_port, packet)
                    if not success:
                        LOGGER.log(f"Switch {self.switch_id} -> {next_switch.switch_id}: packet dropped")

                self.packets_processed += 1

            except Exception as e:
                LOGGER.log(f"Switch {self.switch_id} port {port} service error: {e}")
                yield self.env.timeout(10e-9)  # 10ns instead of 0.01 seconds

    def _map_to_input_port(self, output_port, next_switch):
        if self.level == 0 and next_switch.level == 1: # leaf to spine
            return self._get_leaf_id()
        elif self.level == 1 and next_switch.level == 0: # spine to leaf
            return 4
        else:
            return 0

    def _get_leaf_id(self):
        try:
            return int(self.switch_id.split('_')[1])
        except:
            return 0

    def connect_node(self, port, node_id):
        self.connected_nodes[port] = node_id

    def connect_switch(self, port, switch):
        self.connected_switches[port] = switch

    def _build_routing_table(self):
        if self.level == 0: # Leaf switch
            for port, node_id in self.connected_nodes.items():
                self.routing_table[node_id] = port

            for node_id in range(N_HOSTS + 10):  # Include PHN nodes
                if node_id not in self.routing_table:
                    spine_port = 4 + (node_id % N_SPINE)
                    self.routing_table[node_id] = spine_port

        elif self.level == 1: # Spine switch
            for node_id in range(N_HOSTS + 10):  # Include PHN nodes
                if node_id < N_HOSTS:
                    leaf_idx = node_id // LEAF_HOSTS
                elif node_id in [PHN_G1_ID, PHN_G2_ID, PHN_G3_ID]:
                    # PHN routing
                    phn_leaf_map = {PHN_G1_ID: 0, PHN_G2_ID: 1, PHN_G3_ID: 2}
                    leaf_idx = phn_leaf_map.get(node_id, 3)
                else:
                    leaf_idx = 3  # Default to leaf 3
                self.routing_table[node_id] = leaf_idx

    def route_packet(self, packet):
        dest_id = packet.dest_id
        if dest_id in self.routing_table:
            return self.routing_table[dest_id]
        else:
            if self.level == 0:
                return 4  # Send to spine
            else:
                return 0  # Send to leaf

    def _deliver_to_node(self, packet, node_id):
        yield self.env.timeout(3e-9)



# PARTIAL HOME NODE (PHN) Implementation
class PartialHomeNode:
    def __init__(self, env, phn_id, cluster_name, address_range, cluster_gpus, network):
        self.env = env
        self.phn_id = phn_id
        self.cluster_name = cluster_name  # G1, G2, G3
        self.address_range = address_range  # Address range this PHN manages
        self.cluster_gpus = cluster_gpus    # GPUs in this cluster
        self.network = network

        # PHN Cache - stores data for its address range
        self.phn_cache = OrderedDict()  # address -> PHNCacheEntry

        # Directory for coherency within cluster
        self.directory = defaultdict(list)  # address -> [gpu_ids]
        self.pending_requests = {}  # tx_id -> original_requester (used for global responses)

        # Message processing
        self.incoming_packets = simpy.Store(env)
        self.packet_router = None

        # Statistics
        self.cache_hits = 0
        self.cache_misses = 0
        self.cross_cluster_requests = 0
        self.writebacks_received = 0

        # Start message processor
        self.env.process(self._message_processor())

        LOGGER.log(f"PHN {cluster_name} created: addresses {address_range[0]}-{address_range[-1]}, GPUs {cluster_gpus}")

    def _get_cluster_for_address(self, address):
        """Get cluster name that owns this address"""
        for cluster, config in PHN_SEGMENTS.items():
            if address in config['addresses']:
                return cluster
        return 'G_prime'  # Default to global

    def _is_local_address(self, address):
        """Check if address belongs to this PHN"""
        return address in self.address_range

    def receive_packet(self, packet):
        self.incoming_packets.put(packet)

    def send_packet(self, packet):
        if self.packet_router:
            self.packet_router(packet)

    def _message_processor(self):
        while True:
            try:
                packet = yield self.incoming_packets.get()
                LOGGER.log(f"PHN {self.cluster_name} processing {packet}")
                yield self.env.process(self._handle_phn_message(packet))
            except Exception as e:
                LOGGER.log(f"PHN {self.cluster_name} message processor error: {e}")
                yield self.env.timeout(10e-9)  # 10ns instead of 0.01 seconds

    def _handle_phn_message(self, packet):
        """Handle messages at PHN"""
        # Add PHN access delay
        yield self.env.timeout(PHN_ACCESS_DELAY)

        if packet.msg_type == MessageType.ReadShared:
            yield self.env.process(self._handle_phn_read(packet))
        elif packet.msg_type == MessageType.WriteUnique:
            yield self.env.process(self._handle_phn_write(packet))
        elif packet.msg_type == MessageType.WriteBackFull:
            yield self.env.process(self._handle_phn_writeback(packet))
        elif packet.msg_type == MessageType.CompData:
            # Handle CompData coming back from global memory (forward to original requester)
            yield self.env.process(self._handle_phn_compdata(packet))
        elif packet.msg_type == MessageType.CompAck:
            # Forward completion ack to original requester if present
            yield self.env.process(self._handle_phn_compack(packet))
        elif packet.msg_type == MessageType.PHNInvalidate:
            yield self.env.process(self._handle_phn_invalidate(packet))
        else:
            LOGGER.log(f"PHN {self.cluster_name} received unexpected message: {packet.msg_type}")

    def _handle_phn_read(self, packet):
        """Handle read request at PHN"""
        address = packet.address
        requester = packet.source_id

        if self._is_local_address(address):
            # LOCAL CLUSTER READ
            if address in self.phn_cache:
                # PHN cache hit
                self.cache_hits += 1
                phn_entry = self.phn_cache[address]
                phn_entry.update_access(self.env.now)

                # Send data back to requester
                response = CHIPacket(
                    MessageType.CompData, address, self.phn_id, requester,
                    data=phn_entry.data, tx_id=packet.tx_id, operation_id=packet.operation_id
                )
                self.send_packet(response)

                # Update directory
                if requester not in self.directory[address]:
                    self.directory[address].append(requester)

                LOGGER.log(f"PHN {self.cluster_name} served local read A{address}={phn_entry.data} from PHN cache")
            else:
                # PHN cache miss - fetch from global memory
                self.cache_misses += 1
                # Forward to global memory
                global_request = CHIPacket(
                    MessageType.ReadShared, address, self.phn_id, GLOBAL_MEMORY_ID,
                    tx_id=packet.tx_id, operation_id=packet.operation_id
                )
                global_request.original_requester = requester  # Track original requester
                self.send_packet(global_request)
            # record mapping so we can forward the global response back:
                self.pending_requests[global_request.tx_id] = requester
                LOGGER.log(f"PHN {self.cluster_name} forwarding read A{address} to global memory (PHN miss)")
        else:
            # CROSS-CLUSTER READ - forward to appropriate PHN
            target_cluster = self._get_cluster_for_address(address)
            target_phn_id = self._get_phn_id_for_cluster(target_cluster)

            if target_phn_id:
                self.cross_cluster_requests += 1
                cross_request = CHIPacket(
                    MessageType.ReadShared, address, requester, target_phn_id,
                    tx_id=packet.tx_id, operation_id=packet.operation_id
                )
                cross_request.is_cross_cluster = True
                cross_request.is_one_time_use = True
                self.send_packet(cross_request)
                LOGGER.log(f"PHN {self.cluster_name} forwarding cross-cluster read A{address} to {target_cluster}")
            else:
                # Forward to global memory for G_prime addresses
                global_request = CHIPacket(
                    MessageType.ReadShared, address, requester, GLOBAL_MEMORY_ID,
                    tx_id=packet.tx_id, operation_id=packet.operation_id
                )
                global_request.is_cross_cluster = True
                global_request.is_one_time_use = True
                self.send_packet(global_request)
                LOGGER.log(f"PHN {self.cluster_name} forwarding read A{address} to global memory (G_prime)")

    def _handle_phn_write(self, packet):
        """Handle write request at PHN"""
        address = packet.address
        requester = packet.source_id
        data = packet.data

        if self._is_local_address(address):
            # LOCAL CLUSTER WRITE
            # Step 1: Update PHN cache
            self._update_phn_cache(address, data)

            # Step 2: Invalidate other GPUs in cluster
            current_sharers = [s for s in self.directory.get(address, []) if s != requester]
            if current_sharers:
                for sharer in current_sharers:
                    invalidate = CHIPacket(
                        MessageType.SnpUnique, address, self.phn_id, sharer,
                        tx_id=packet.tx_id, operation_id=packet.operation_id
                    )
                    self.send_packet(invalidate)
                LOGGER.log(f"PHN {self.cluster_name} invalidating GPUs {current_sharers} for write A{address}={data}")

            # Step 3: Update global memory (dual-write for consistency)
            global_update = CHIPacket(
                MessageType.WriteBackFull, address, self.phn_id, GLOBAL_MEMORY_ID,
                data=data, tx_id=str(uuid.uuid4())[:8]  # New transaction for global update
            )
            self.send_packet(global_update)

            # Step 4: Update directory and send completion
            self.directory[address] = [requester]
            response = CHIPacket(
                MessageType.CompAck, address, self.phn_id, requester,
                tx_id=packet.tx_id, operation_id=packet.operation_id
            )
            self.send_packet(response)

            LOGGER.log(f"PHN {self.cluster_name} completed local write A{address}={data} with dual-write to global")
        else:
            # CROSS-CLUSTER WRITE
            target_cluster = self._get_cluster_for_address(address)
            target_phn_id = self._get_phn_id_for_cluster(target_cluster)

            if target_phn_id:
                self.cross_cluster_requests += 1
                # Forward write to target PHN
                cross_write = CHIPacket(
                    MessageType.WriteUnique, address, requester, target_phn_id,
                    data=data, tx_id=packet.tx_id, operation_id=packet.operation_id
                )
                cross_write.is_cross_cluster = True
                cross_write.is_one_time_use = True
                self.send_packet(cross_write)

                # Also update global memory
                global_update = CHIPacket(
                    MessageType.WriteBackFull, address, self.phn_id, GLOBAL_MEMORY_ID,
                    data=data, tx_id=str(uuid.uuid4())[:8]
                )
                self.send_packet(global_update)

                LOGGER.log(f"PHN {self.cluster_name} forwarding cross-cluster write A{address}={data} to {target_cluster} + global update")
            else:
                # Direct write to global memory for G_prime addresses
                global_write = CHIPacket(
                    MessageType.WriteUnique, address, requester, GLOBAL_MEMORY_ID,
                    data=data, tx_id=packet.tx_id, operation_id=packet.operation_id
                )
                global_write.is_cross_cluster = True
                global_write.is_one_time_use = True
                self.send_packet(global_write)
                LOGGER.log(f"PHN {self.cluster_name} forwarding write A{address}={data} to global memory (G_prime)")

    def _handle_phn_writeback(self, packet):
        """Handle writeback from GPU"""
        address = packet.address
        data = packet.data
        source_gpu = packet.source_id

        if self._is_local_address(address):
            # Before accepting a GPU writeback we must invalidate other sharers
            current_sharers = [s for s in list(self.directory.get(address, [])) if s != source_gpu]
            if current_sharers:
                for sharer in current_sharers:
                    invalidate = CHIPacket(
                        MessageType.SnpUnique, address, self.phn_id, sharer,
                        tx_id=packet.tx_id, operation_id=packet.operation_id
                    )
                    # send snoop/invalidate to protect against data corruption
                    self.send_packet(invalidate)
                LOGGER.log(f"PHN {self.cluster_name} snooped/invalidate GPUs {current_sharers} due to writeback A{address}")

            # Update PHN cache with writeback data
            self._update_phn_cache(address, data)
            self.writebacks_received += 1

            # Update directory: now only source_gpu is the sharer (owner)
            self.directory[address] = [source_gpu]

            # Also send to global memory for consistency (dual-write)
            global_update = CHIPacket(
                MessageType.WriteBackFull, address, self.phn_id, GLOBAL_MEMORY_ID,
                data=data, tx_id=str(uuid.uuid4())[:8]
            )
            # tag as coming from PHN if you like
            self.send_packet(global_update)

            LOGGER.log(f"PHN {self.cluster_name} received writeback A{address}={data} from GPU{source_gpu}, sent snoops and updated PHN+global")

    def _handle_phn_compdata(self, packet):
        """Handle CompData coming from global or other PHN and forward to original requester (if tracked)."""
        address = packet.address
        data = packet.data
        tx = packet.tx_id

        # If this CompData is a reply to a global_request this PHN created earlier,
        # forward to the original requester and also update PHN cache & directory.
        original = self.pending_requests.pop(tx, None)

        # Update PHN cache (local)
        if self._is_local_address(address):
            self._update_phn_cache(address, data)

        # If we know the original requester, forward the data packet to it.
        target = original if original is not None else packet.dest_id
        resp = CHIPacket(MessageType.CompData, address, self.phn_id, target,
                         data=data, tx_id=tx, operation_id=packet.operation_id)

        # ENHANCED: Check if target is GPU 0-3 and address is non-local to them
        is_target_gpu_0_3 = target in [0, 1, 2, 3]
        is_local_address_for_target = (0 <= address <= 9) if is_target_gpu_0_3 else True
        gpu_0_3_cross_access = is_target_gpu_0_3 and not is_local_address_for_target

        # preserve one-time flags if present or set for GPU 0-3 cross-cluster access
        resp.is_cross_cluster = getattr(packet, 'is_cross_cluster', False) or gpu_0_3_cross_access
        resp.is_one_time_use = getattr(packet, 'is_one_time_use', False) or gpu_0_3_cross_access

        self.send_packet(resp)

        # update directory for local addresses
        if self._is_local_address(address) and target not in self.directory[address]:
            self.directory[address].append(target)

        if gpu_0_3_cross_access:
            LOGGER.log(f"PHN {self.cluster_name} forwarded CompData A{address}={data} to GPU{target} [GPU 0-3 CROSS-CLUSTER]")
        else:
            LOGGER.log(f"PHN {self.cluster_name} forwarded CompData A{address}={data} to {target}")
    def _handle_phn_compack(self, packet):
        """Forward completion acks coming from global to original requester (if tracked)."""
        tx = packet.tx_id
        original = self.pending_requests.pop(tx, None)
        target = original if original is not None else packet.dest_id
        resp = CHIPacket(MessageType.CompAck, packet.address, self.phn_id, target,
                         tx_id=tx, operation_id=packet.operation_id)
        self.send_packet(resp)
        LOGGER.log(f"PHN {self.cluster_name} forwarded CompAck A{packet.address} to {target}")

    def _handle_phn_invalidate(self, packet):
        """Handle invalidation request from another PHN"""
        address = packet.address

        # Invalidate all GPUs in this cluster that have this address
        current_sharers = self.directory.get(address, [])
        for sharer in current_sharers:
            invalidate = CHIPacket(
                MessageType.SnpUnique, address, self.phn_id, sharer,
                tx_id=packet.tx_id, operation_id=packet.operation_id
            )
            self.send_packet(invalidate)

        # Clear directory entry
        if address in self.directory:
            del self.directory[address]

        # Remove from PHN cache if present
        if address in self.phn_cache:
            del self.phn_cache[address]

        LOGGER.log(f"PHN {self.cluster_name} invalidated A{address} in GPUs {current_sharers}")

    def _update_phn_cache(self, address, data):
        """Update PHN cache with eviction if needed"""
        if address in self.phn_cache:
            # Update existing entry
            self.phn_cache[address].data = data
            self.phn_cache[address].update_access(self.env.now)
            # Move to end (most recent)
            self.phn_cache.move_to_end(address)
        else:
            # Add new entry with eviction if needed
            if len(self.phn_cache) >= PHN_CACHE_SIZE:
                # Evict least recently used
                lru_address, lru_entry = self.phn_cache.popitem(last=False)
                LOGGER.log(f"PHN {self.cluster_name} evicted A{lru_address} from PHN cache")

            # Add new entry
            new_entry = PHNCacheEntry(data, self.env.now)
            self.phn_cache[address] = new_entry

    def _get_phn_id_for_cluster(self, cluster):
        """Get PHN ID for cluster name"""
        cluster_phn_map = {
            'G1': PHN_G1_ID,
            'G2': PHN_G2_ID, 
            'G3': PHN_G3_ID
        }
        return cluster_phn_map.get(cluster)

    def get_cache_display_data(self):
        """Get PHN cache data for visualization"""
        cache_data = {}
        for addr in self.address_range:
            if addr in self.phn_cache:
                entry = self.phn_cache[addr]
                cache_data[addr] = {
                    'state': 'P',  # PHN cached
                    'data': entry.data,
                    'is_exclusive': entry.is_exclusive
                }
        return cache_data




# Enhanced CHI Node with PHN support and new cache states
class EnhancedCHINode:
    def __init__(self, env, node_id, node_type, is_home_node, home_node_id):
        self.env = env
        self.id = node_id
        self.node_type = node_type
        self.is_home_node = is_home_node
        self.home_node_id = home_node_id
        self.is_active = True

        # Set role and determine cluster
        if node_type == NodeType.GLOBAL_MEMORY:
            self.role = "HN"
            self.cluster = "G_prime"
        elif node_type == NodeType.CPU:
            self.role = "CPU"
            self.cluster = "G_prime"
            self.is_active = False
        else:  # GPU
            self.role = "RN"
            self.cluster = self._determine_cluster()
            self.phn_id = self._get_phn_id()

        # Initialize memory/cache
        self._initialize_memory_cache()

        # LRU Cache for GPUs with enhanced states
        if self.node_type == NodeType.GPU:
            self.lru_cache = OrderedDict()
            self.lru_evictions = 0

        # Statistics
        self.cache_hits = 0
        self.cache_misses = 0
        self.cross_cluster_accesses = 0
        self.local_cluster_accesses = 0
        self.one_time_use_count = 0
        self.writeback_count = 0

        # Protocol handling
        self.pending_transactions = {}

        # Network interface
        self.incoming_packets = simpy.Store(env)
        self.packet_router = None
        self.network = None

        if self.is_active:
            self.env.process(self._message_processor())

    def _is_address_local_to_gpu_0_3(self, gpu_id, address):
        """Check if address is local to GPU 0-3 (addresses 0-9)"""
        if gpu_id in [0, 1, 2, 3]:
            return 0 <= address <= 9
        return True  # For other GPUs, we don't apply this rule

    def _should_use_used_state(self, gpu_id, address):
        """Determine if this GPU should get Used state for this address"""
        # GPU 0-3 accessing non-local addresses (not 0-9) should get Used state
        if gpu_id in [0, 1, 2, 3]:
            return not (0 <= address <= 9)
        return False  # Other GPUs follow normal cross-cluster logic

    def _determine_cluster(self):
        """Determine which cluster this GPU belongs to"""
        for cluster, config in PHN_SEGMENTS.items():
            if self.id in config['gpus']:
                return cluster
        return "G_prime"

    def _get_phn_id(self):
        """Get PHN ID for this GPU's cluster"""
        cluster_phn_map = {
            'G1': PHN_G1_ID,
            'G2': PHN_G2_ID,
            'G3': PHN_G3_ID,
            'G_prime': GLOBAL_MEMORY_ID
        }
        return cluster_phn_map.get(self.cluster, GLOBAL_MEMORY_ID)

    def _is_local_address(self, address):
        """Check if address is local to this GPU's cluster"""
        if self.cluster in PHN_SEGMENTS:
            return address in PHN_SEGMENTS[self.cluster]['addresses']
        return False

    def _initialize_memory_cache(self):
        """Initialize memory and cache based on node type"""
        self.cache = {}
        self.memory = {}

        if self.node_type == NodeType.GLOBAL_MEMORY:
            # Global memory (Home Node) - all 32 addresses
            self.memory = {addr: random.randint(10, 255) for addr in range(GLOBAL_MEMORY_SIZE)}
            self.directory = defaultdict(list)
        elif self.node_type == NodeType.GPU:
            pass  # Uses LRU cache
        elif self.node_type == NodeType.CPU:
            pass  # Inactive

    def lru_cache_access(self, address):
        """Enhanced LRU cache access with one-time use logic"""
        if address in self.lru_cache:
            entry = self.lru_cache[address]

            # Check if entry can provide cache hit
            if entry.can_hit():
                # Move to end (most recent)
                self.lru_cache.move_to_end(address)
                entry.update_access(self.env.now)

                # Mark one-time use entries as used
                if entry.is_one_time_use and entry.access_count == 2:  # First access was creation
                    LOGGER.log(f"{self.role}{self.id} one-time entry A{address} now exhausted")

                return entry
            else:
                # One-time use entry already exhausted - treat as miss
                LOGGER.log(f"{self.role}{self.id} one-time entry A{address} cannot hit (exhausted)")
                return None

        return None

    def lru_cache_insert(self, address, state, data, is_cross_cluster=False):
        """Enhanced LRU cache insert with new states"""
        # Remove if already exists
        if address in self.lru_cache:
            del self.lru_cache[address]

        # Evict if cache is full
        if len(self.lru_cache) >= GPU_CACHE_SIZE:
            self._lru_evict_oldest()

        # Determine if this is one-time use
        is_one_time = (state == CacheState.Used or state == CacheState.UpdatedOnce) or is_cross_cluster

        # Insert new entry
        new_entry = LRUCacheEntry(state, data, self.env.now)
        new_entry.is_one_time_use = is_one_time

        self.lru_cache[address] = new_entry

        # If it is a one-time (Used/UpdatedOnce) entry, set it to display-only for 3.5s and schedule removal
        is_one_time = (state == CacheState.Used or state == CacheState.UpdatedOnce)
        if is_one_time:
            new_entry.is_display_only = True
            duration = 3.5e-9  # seconds; change to 3 or 4 as you want
            new_entry.visible_until = self.env.now + duration
            # schedule a process to clear it after duration
            def _display_timer(addr, timer):
                yield self.env.timeout(timer)
                # If entry still there, remove or invalidate
                if addr in self.lru_cache:
                    try:
                        del self.lru_cache[addr]
                        LOGGER.log(f"{self.role}{self.id} display-only entry A{addr} expired and removed after {duration/1e9:.1f}s")
                    except Exception as e:
                        LOGGER.log(f"{self.role}{self.id} error removing display-only A{addr}: {e}")
            # spawn process
            self.env.process(_display_timer(address, duration))

        if is_one_time:
            self.one_time_use_count += 1
            LOGGER.log(f"{self.role}{self.id} LRU inserted A{address} ({state.name}) [ONE-TIME USE]")
        else:
            LOGGER.log(f"{self.role}{self.id} LRU inserted A{address} ({state.name})")

    def _lru_evict_oldest(self):
        """Evict least recently used entry with proper writeback"""
        if self.lru_cache:
            # Get least recently used (first item)
            lru_address, lru_entry = next(iter(self.lru_cache.items()))

            # If evicting Modified (dirty) data, perform writeback
            if lru_entry.state == CacheState.Modified:
                LOGGER.log(f"WRITEBACK: {self.role}{self.id} evicting DIRTY A{lru_address}={lru_entry.data}")
                self._perform_writeback(lru_address, lru_entry.data)
                self.writeback_count += 1

            # Remove from cache
            del self.lru_cache[lru_address]
            self.lru_evictions += 1

            LOGGER.log(f"{self.role}{self.id} LRU evicted A{lru_address}")

    def _perform_writeback(self, address, data):
        """Perform writeback to PHN or global memory"""
        if self._is_local_address(address):
            # Send writeback to PHN
            target = self.phn_id
        else:
            # Send writeback to global memory
            target = self.home_node_id

        writeback_packet = CHIPacket(
            MessageType.WriteBackFull, address, self.id, target,
            data=data, tx_id=str(uuid.uuid4())[:8]
        )
        self.send_packet(writeback_packet)
        LOGGER.log(f"WRITEBACK: {self.role}{self.id} sent writeback A{address}={data} to {target}")

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
                yield self.env.timeout(10e-9)  # 10ns instead of 0.01 seconds

    def _handle_home_node_message(self, packet):
        """Handle messages at Global Memory Home Node"""
        # Add memory access delay
        yield self.env.timeout(MEMORY_ACCESS_DELAY)

        if packet.msg_type == MessageType.ReadShared:
            yield self.env.process(self._handle_home_read_shared(packet))
        elif packet.msg_type == MessageType.WriteUnique:
            yield self.env.process(self._handle_home_write_unique(packet))
        elif packet.msg_type == MessageType.WriteBackFull:
            yield self.env.process(self._handle_writeback(packet))
        else:
            LOGGER.log(f"HN received unexpected message: {packet.msg_type}")

    def _handle_writeback(self, packet):
        """Handle writeback to global memory"""
        address = packet.address
        data = packet.data
        source = packet.source_id

        # Update global memory
        old_value = self.memory.get(address, 0)
        self.memory[address] = data

        LOGGER.log(f"GLOBAL MEMORY: Updated A{address}: {old_value} -> {data} from {source}")

    def _handle_home_read_shared(self, packet):
        
        address = packet.address
        requester = packet.source_id

        # FIXED: For addresses 30-31, implement proper directory-based CHI protocol
        if address in [30, 31]:
            # Basic CHI protocol - check if any GPU has modified copy
            # For addresses 30-31, only GPUs 12-13 can have modified copies
            modified_owner = None

            # Check GPUs 12-13 for modified state
            for gpu_id in [12, 13]:
                if gpu_id != requester:  # Don't snoop the requester
                    # Add to directory for tracking and send snoop
                    if address not in self.directory:
                        self.directory[address] = []
                    if gpu_id not in self.directory[address]:
                        self.directory[address].append(gpu_id)

                    # Send snoop to check if this GPU has modified copy
                    snoop_packet = CHIPacket(
                        MessageType.SnpSharedFwd, address, self.id, gpu_id,
                        fwd_id=requester, tx_id=packet.tx_id, operation_id=packet.operation_id
                    )
                    self.send_packet(snoop_packet)
                    LOGGER.log(f"BASIC CHI: Global HN sent snoop to GPU{gpu_id} for A{address} (fwd to GPU{requester})")

                    # For basic CHI, assume we'll get response - simplified for simulation
                    # In real implementation, we'd wait for snoop responses

            # If no modified copy found, serve from memory
            data = self.memory.get(address, 0)
            response = CHIPacket(
                MessageType.CompData, address, self.id, requester,
                data=data, tx_id=packet.tx_id, operation_id=packet.operation_id
            )
            self.send_packet(response)

            # Add requester to directory
            if address not in self.directory:
                self.directory[address] = []
            if requester not in self.directory[address]:
                self.directory[address].append(requester)

            LOGGER.log(f"BASIC CHI: Global HN served ReadShared A{address}={data} to GPU{requester}, directory: {self.directory[address]}")

        else:
            # Regular PHN/cross-cluster handling
            data = self.memory.get(address, 0)
            is_cross_cluster = getattr(packet, 'is_cross_cluster', False)
            is_one_time = getattr(packet, 'is_one_time_use', False)

            response = CHIPacket(
                MessageType.CompData, address, self.id, requester,
                data=data, tx_id=packet.tx_id, operation_id=packet.operation_id
            )

            if is_cross_cluster or is_one_time:
                response.is_cross_cluster = True
                response.is_one_time_use = True

            self.send_packet(response)

            marker = "[CROSS-CLUSTER ONE-TIME]" if is_cross_cluster else ""
            LOGGER.log(f"GLOBAL MEMORY: Served ReadShared A{address}={data} to {requester} {marker}")

    def _handle_home_write_unique(self, packet):
        """Enhanced WriteUnique at Global Memory - FIXED for addresses 30-31 basic CHI"""
        address = packet.address
        requester = packet.source_id
        data = packet.data

        # FIXED: For addresses 30-31, implement proper basic CHI invalidation
        if address in [30, 31]:
            # Basic CHI protocol - invalidate all other GPUs in directory
            if address in self.directory:
                current_sharers = [gpu_id for gpu_id in self.directory[address] if gpu_id != requester]

                # Send invalidations to all current sharers
                for gpu_id in current_sharers:
                    invalidate_packet = CHIPacket(
                        MessageType.SnpUnique, address, self.id, gpu_id,
                        tx_id=packet.tx_id, operation_id=packet.operation_id
                    )
                    self.send_packet(invalidate_packet)
                    LOGGER.log(f"BASIC CHI: Global HN sent invalidation for A{address} to GPU{gpu_id}")

                # Update directory - only requester has it now
                self.directory[address] = [requester]
            else:
                # First access - just add to directory
                self.directory[address] = [requester]

            # Update global memory
            old_value = self.memory.get(address, 0)
            self.memory[address] = data

            # Send completion
            response = CHIPacket(
                MessageType.CompAck, address, self.id, requester,
                tx_id=packet.tx_id, operation_id=packet.operation_id
            )
            self.send_packet(response)

            LOGGER.log(f"BASIC CHI: Global HN WriteUnique A{address}: {old_value} -> {data} from GPU{requester}, directory: {self.directory[address]}")

        else:
            # Regular PHN/cross-cluster handling
            old_value = self.memory.get(address, 0)
            self.memory[address] = data

            response = CHIPacket(
                MessageType.CompAck, address, self.id, requester,
                tx_id=packet.tx_id, operation_id=packet.operation_id
            )

            is_cross_cluster = getattr(packet, 'is_cross_cluster', False)
            if is_cross_cluster:
                response.is_cross_cluster = True
                response.is_one_time_use = True

            self.send_packet(response)

            marker = "[CROSS-CLUSTER ONE-TIME]" if is_cross_cluster else ""
            LOGGER.log(f"GLOBAL MEMORY: WriteUnique A{address}: {old_value} -> {data} from {requester} {marker}")

    def _handle_request_node_message(self, packet):
        """Handle messages at request nodes (GPUs)"""
        if packet.msg_type == MessageType.CompData:
            yield self.env.process(self._handle_completion_data(packet))
        elif packet.msg_type == MessageType.CompAck:
            self._handle_completion_ack(packet)
        elif packet.msg_type == MessageType.SnpSharedFwd:
            yield self.env.process(self._handle_snoop_shared_fwd(packet))
        elif packet.msg_type == MessageType.SnpUnique:
            yield self.env.process(self._handle_snoop_unique(packet))
        else:
            LOGGER.log(f"RN received unexpected message: {packet.msg_type}")
    def _handle_snoop_shared_fwd(self, packet):
        """Handle SnpSharedFwd - forward data if we have it, or respond with no data"""
        address = packet.address
        fwd_id = packet.fwd_id  # Who to forward data to

        response_data = None
        has_data = False

        if address in self.lru_cache:
            entry = self.lru_cache[address]
            if entry.state == CacheState.Modified:
                # We have modified (dirty) copy - forward data and downgrade to Shared
                response_data = entry.data
                has_data = True
                entry.state = CacheState.Shared
                LOGGER.log(f"{self.role}{self.id} BASIC CHI: Forwarding modified A{address}={response_data} to GPU{fwd_id}, downgraded to Shared")
            elif entry.state == CacheState.Shared:
                # We have shared copy - can forward data
                response_data = entry.data
                has_data = True
                LOGGER.log(f"{self.role}{self.id} BASIC CHI: Forwarding shared A{address}={response_data} to GPU{fwd_id}")

        if has_data:
            # Send data directly to the forwarding target
            fwd_response = CHIPacket(
                MessageType.CompData, address, self.id, fwd_id,
                data=response_data, tx_id=packet.tx_id, operation_id=packet.operation_id
            )
            self.send_packet(fwd_response)

            # Also send snoop response back to home node
            snoop_response = CHIPacket(
                MessageType.SnpRespData, address, self.id, packet.source_id,
                data=response_data, tx_id=packet.tx_id, operation_id=packet.operation_id
            )
            self.send_packet(snoop_response)
        else:
            # No data to forward - send snoop response without data
            snoop_response = CHIPacket(
                MessageType.SnpResp, address, self.id, packet.source_id,
                tx_id=packet.tx_id, operation_id=packet.operation_id
            )
            self.send_packet(snoop_response)
            LOGGER.log(f"{self.role}{self.id} BASIC CHI: No data for A{address}, sent SnpResp to home node")



    def _handle_completion_data(self, packet):
        """Handle data completion with enhanced states - GPU 0-3 get Used for cross-cluster"""
        yield self.env.timeout(CACHE_HIT_DELAY)

        address = packet.address
        data = packet.data
        is_cross_cluster = getattr(packet, 'is_cross_cluster', False)
        is_one_time = getattr(packet, 'is_one_time_use', False)

        # NEW LOGIC: Check if this is GPU 0-3 accessing non-local addresses
        is_gpu_0_to_3 = self.id in [0, 1, 2, 3]
        is_local_address_for_gpu_0_3 = (0 <= address <= 9) if is_gpu_0_to_3 else True

        # GPU 0-3 accessing addresses outside 0-9 should get Used state
        gpu_0_3_cross_access = is_gpu_0_to_3 and not is_local_address_for_gpu_0_3

        if is_cross_cluster or is_one_time or gpu_0_3_cross_access:
            # Cross-cluster read or GPU 0-3 non-local access gets Used state (one-time use)
            self.lru_cache_insert(address, CacheState.Used, data, is_cross_cluster=True)
            self.cross_cluster_accesses += 1
            if gpu_0_3_cross_access:
                LOGGER.log(f"{self.role}{self.id} received non-local data A{address}={data} [USED STATE - GPU 0-3 CROSS-CLUSTER]")
            else:
                LOGGER.log(f"{self.role}{self.id} received cross-cluster data A{address}={data} [USED STATE - ONE-TIME]")
        else:
            # Local cluster read gets Shared state
            self.lru_cache_insert(address, CacheState.Shared, data, is_cross_cluster=False)
            self.local_cluster_accesses += 1
            LOGGER.log(f"{self.role}{self.id} received local data A{address}={data} [SHARED STATE]")

        # Complete the transaction
        if packet.tx_id in self.pending_transactions:
            completion_event = self.pending_transactions.pop(packet.tx_id)
            completion_event.succeed()
    def _handle_completion_ack(self, packet):
        """Handle write completion"""
        event = self.pending_transactions.pop(packet.tx_id, None)
        if event and not event.triggered:
            event.succeed()

        is_cross_cluster = getattr(packet, 'is_cross_cluster', False)
        marker = "[CROSS-CLUSTER ONE-TIME]" if is_cross_cluster else ""
        LOGGER.log(f"{self.role}{self.id} write A{packet.address} complete {marker}")

    def _handle_snoop_unique(self, packet):
        """Handle invalidation request"""
        address = packet.address
        old_state = CacheState.Invalid
        writeback_data = None

        if address in self.lru_cache:
            entry = self.lru_cache[address]
            old_state = entry.state
            writeback_data = entry.data

            # If evicting Modified data, perform writeback
            if old_state == CacheState.Modified:
                LOGGER.log(f"WRITEBACK: {self.role}{self.id} invalidating DIRTY A{address}={writeback_data}")
                self._perform_writeback(address, writeback_data)
                self.writeback_count += 1

            # Remove from cache
            del self.lru_cache[address]

        # Send invalidation acknowledgment
        response = CHIPacket(
            MessageType.SnpResp, address, self.id, packet.source_id,
            tx_id=packet.tx_id, operation_id=packet.operation_id
        )
        self.send_packet(response)

        LOGGER.log(f"{self.role}{self.id} invalidated A{address} ({old_state.name})")

    def issue_read_operation(self, address, operation_id=None):
        """Issue read operation - FIXED for addresses 30-31 basic CHI protocol"""
        if not self.is_active or self.node_type != NodeType.GPU:
            return self.env.event().succeed()

        if not (0 <= address < GLOBAL_MEMORY_SIZE):
            LOGGER.log(f"RN{self.id} invalid address {address}")
            return self.env.event().succeed()

        def read_process():
            # Check LRU cache first
            cache_entry = self.lru_cache_access(address)
            if cache_entry and cache_entry.state != CacheState.Invalid:
                # CACHE HIT
                yield self.env.timeout(CACHE_HIT_DELAY)
                self.cache_hits += 1
                hit_type = "ONE-TIME" if cache_entry.is_one_time_use else "NORMAL"
                LOGGER.log(f"{self.role}{self.id} LRU cache HIT A{address} ({cache_entry.state.name}) [{hit_type}]")
                return

            # CACHE MISS
            yield self.env.timeout(CACHE_MISS_PENALTY)
            self.cache_misses += 1

            # FIXED: For addresses 30-31, GPUs 12-13 use basic CHI protocol (no PHN)
            if address in [30, 31] and self.id in [12, 13]:
                # Basic CHI protocol - send directly to global home node
                target = self.home_node_id  # Global Memory
                self.local_cluster_accesses += 1
                LOGGER.log(f"{self.role}{self.id} LRU cache MISS A{address} - BASIC CHI to Global Memory (GPU{self.id})")
            elif self._is_local_address(address):
                target = self.phn_id  # Send to PHN
                self.local_cluster_accesses += 1
                LOGGER.log(f"{self.role}{self.id} LRU cache MISS A{address} - sending to PHN {self.cluster}")
            else:
                # Cross-cluster access
                target_cluster = self._get_cluster_for_address(address)
                if target_cluster == 'G_prime':
                    target = self.home_node_id  # Send to global memory for G_prime
                else:
                    target = self._get_phn_id_for_cluster(target_cluster)
                self.cross_cluster_accesses += 1
                LOGGER.log(f"{self.role}{self.id} LRU cache MISS A{address} - CROSS-CLUSTER to {target_cluster}")

            # Send request
            tx_id = str(uuid.uuid4())[:8]
            completion_event = self.env.event()
            self.pending_transactions[tx_id] = completion_event

            request = CHIPacket(
                MessageType.ReadShared, address, self.id, target,
                tx_id=tx_id, operation_id=operation_id
            )

            # Mark cross-cluster requests (except basic CHI addresses 30-31 from GPUs 12-13)
            if not self._is_local_address(address) and not (address in [30, 31] and self.id in [12, 13]):
                request.is_cross_cluster = True
                request.is_one_time_use = True

            self.send_packet(request)

            # Wait for response
            yield completion_event

        return self.env.process(read_process())

    def issue_write_operation(self, address, data, operation_id=None):
        """Issue write operation - FIXED for addresses 30-31 basic CHI protocol"""
        if not self.is_active or self.node_type != NodeType.GPU:
            return self.env.event().succeed()

        if not (0 <= address < GLOBAL_MEMORY_SIZE):
            LOGGER.log(f"RN{self.id} invalid address {address}")
            return self.env.event().succeed()

        def write_process():
            # Add cache access delay
            yield self.env.timeout(CACHE_HIT_DELAY)

            # FIXED: For addresses 30-31, GPUs 12-13 use basic CHI protocol
            if address in [30, 31] and self.id in [12, 13]:
                # Basic CHI - Modified state means we have ownership
                self.lru_cache_insert(address, CacheState.Modified, data)
                target = self.home_node_id  # Global Memory
                self.local_cluster_accesses += 1
                LOGGER.log(f"{self.role}{self.id} BASIC CHI write A{address}={data} [MODIFIED STATE - HAS OWNERSHIP]")
            elif self._is_local_address(address):
                # LOCAL CLUSTER WRITE - Modified state
                self.lru_cache_insert(address, CacheState.Modified, data)

                # Immediate writeback to PHN and global home node for dual consistency
                if self._is_local_address(address):
                    wb_phn = CHIPacket(
                        MessageType.WriteBackFull, address, self.id, self.phn_id,
                        data=data, tx_id=str(uuid.uuid4())[:8]
                    )
                    self.send_packet(wb_phn)
                    LOGGER.log(f"{self.role}{self.id} sent immediate WRITEBACK to PHN{self.phn_id} for A{address}={data}")

                    # Also send to global home node (dual-write)
                    wb_global = CHIPacket(
                        MessageType.WriteBackFull, address, self.id, self.home_node_id,
                        data=data, tx_id=str(uuid.uuid4())[:8]
                    )
                    self.send_packet(wb_global)
                    LOGGER.log(f"{self.role}{self.id} sent immediate WRITEBACK to GlobalHN for A{address}={data}")

                target = self.phn_id
                self.local_cluster_accesses += 1
                LOGGER.log(f"{self.role}{self.id} local write A{address}={data} [MODIFIED STATE]")
            else:
                # CROSS-CLUSTER WRITE - UpdatedOnce state (one-time use)
                self.lru_cache_insert(address, CacheState.UpdatedOnce, data, is_cross_cluster=True)
                target_cluster = self._get_cluster_for_address(address)
                if target_cluster == 'G_prime':
                    target = self.home_node_id
                else:
                    target = self._get_phn_id_for_cluster(target_cluster)
                self.cross_cluster_accesses += 1
                LOGGER.log(f"{self.role}{self.id} cross-cluster write A{address}={data} [UPDATED_ONCE STATE - ONE-TIME]")

            # Send write request
            tx_id = str(uuid.uuid4())[:8]
            completion_event = self.env.event()
            self.pending_transactions[tx_id] = completion_event

            request = CHIPacket(
                MessageType.WriteUnique, address, self.id, target,
                data=data, tx_id=tx_id, operation_id=operation_id
            )

            # Mark cross-cluster requests (except basic CHI addresses 30-31 from GPUs 12-13)
            if not self._is_local_address(address) and not (address in [30, 31] and self.id in [12, 13]):
                request.is_cross_cluster = True
                request.is_one_time_use = True

            self.send_packet(request)

            # Wait for completion
            yield completion_event

        return self.env.process(write_process())

    def _get_cluster_for_address(self, address):
        """Get cluster name that owns this address"""
        for cluster, config in PHN_SEGMENTS.items():
            if address in config['addresses']:
                return cluster
        return 'G_prime'

    def _get_phn_id_for_cluster(self, cluster):
        """Get PHN ID for cluster name"""
        cluster_phn_map = {
            'G1': PHN_G1_ID,
            'G2': PHN_G2_ID,
            'G3': PHN_G3_ID
        }
        return cluster_phn_map.get(cluster)

    def get_cache_display_data(self):
        """Get cache data for visualization with enhanced states"""
        cache_data = {}

        if self.node_type == NodeType.GPU:
            for addr in range(GLOBAL_MEMORY_SIZE):
                if addr in self.lru_cache:
                    entry = self.lru_cache[addr]
                    cache_data[addr] = {
                        'state': entry.get_state_char(),
                        'data': entry.data,
                        'lru_position': list(self.lru_cache.keys()).index(addr),
                        'is_local': self._is_local_address(addr),
                        'is_one_time_use': entry.is_one_time_use,
                        'can_cache_hit': entry.can_hit()
                    }
                else:
                    cache_data[addr] = {
                        'state': 'I', 
                        'data': None, 
                        'lru_position': -1,
                        'is_local': self._is_local_address(addr),
                        'is_one_time_use': False,
                        'can_cache_hit': False
                    }

        return cache_data

    def get_memory_display_data(self):
        """Get memory data for visualization"""
        if self.node_type == NodeType.GLOBAL_MEMORY:
            return dict(self.memory)
        return {}




# Enhanced Fat-Tree Network with PHN support
class EnhancedFatTreeNetwork:
    def __init__(self, env, visualizer=None):
        self.env = env
        self.visualizer = visualizer

        # Network components
        self.nodes = []
        self.phn_nodes = []  # PHN nodes
        self.leaf_switches = []
        self.spine_switches = []

        # Build enhanced topology with PHNs
        self._build_enhanced_fat_tree_topology()

        # Global packet delivery system
        self.packet_delivery_queue = simpy.Store(env)
        self.env.process(self._packet_delivery_processor())

        LOGGER.log("Enhanced Fat-Tree Network with PHN architecture initialized")
        LOGGER.log(f"   {N_HOSTS} IPs: {N_GPUS} GPUs + 1 CPU + 1 Global Memory")
        LOGGER.log(f"   3 PHN nodes for cluster management")
        LOGGER.log(f"   Cluster configuration: G1(0-3), G2(4-7), G3(8-11), G_prime(12-13)")

    def _build_enhanced_fat_tree_topology(self):
        """Build Fat-Tree topology with PHN nodes"""

        # 1. Create spine switches
        for i in range(N_SPINE):
            spine = FatTreeSwitch(self.env, f"spine_{i}", level=1, switch_type="spine")
            self.spine_switches.append(spine)

        # 2. Create leaf switches
        for i in range(N_LEAF):
            leaf = FatTreeSwitch(self.env, f"leaf_{i}", level=0, switch_type="leaf")
            self.leaf_switches.append(leaf)

        # 3. Create regular nodes
        for i in range(N_HOSTS):
            if i < N_GPUS:
                node = EnhancedCHINode(self.env, i, NodeType.GPU, False, GLOBAL_MEMORY_ID)
            elif i == CPU_NODE_ID:
                node = EnhancedCHINode(self.env, i, NodeType.CPU, False, GLOBAL_MEMORY_ID)
                node.is_active = False
            else:  # Global Memory
                node = EnhancedCHINode(self.env, i, NodeType.GLOBAL_MEMORY, True, GLOBAL_MEMORY_ID)

            node.packet_router = self._route_packet
            node.network = self
            self.nodes.append(node)

            # Connect to leaf switches
            leaf_idx = i // LEAF_HOSTS
            port = i % LEAF_HOSTS
            self.leaf_switches[leaf_idx].connect_node(port, i)

            LOGGER.log(f"Connected {node.role}{i} ({node.cluster}) to leaf_{leaf_idx} port {port}")

        # 4. Create PHN nodes
        phn_configs = [
            (PHN_G1_ID, 'G1', PHN_SEGMENTS['G1'], 0),  # PHN1 on leaf 0
            (PHN_G2_ID, 'G2', PHN_SEGMENTS['G2'], 1),  # PHN2 on leaf 1  
            (PHN_G3_ID, 'G3', PHN_SEGMENTS['G3'], 2),  # PHN3 on leaf 2
        ]

        for phn_id, cluster_name, config, leaf_idx in phn_configs:
            phn = PartialHomeNode(
                self.env, phn_id, cluster_name, 
                config['addresses'], config['gpus'], self
            )
            phn.packet_router = self._route_packet
            self.phn_nodes.append(phn)

            # Connect PHN to leaf switch (use port 4, GPUs use 0-3)
            phn_port = 4
            self.leaf_switches[leaf_idx].connect_node(phn_port, phn_id)

            LOGGER.log(f"Connected PHN {cluster_name} (addresses {config['addresses'][0]}-{config['addresses'][-1]}) to leaf_{leaf_idx}")

        # 5. Connect switches
        for leaf_idx, leaf in enumerate(self.leaf_switches):
            for spine_idx, spine in enumerate(self.spine_switches):
                leaf.connect_switch(5 + spine_idx, spine)  # PHN uses port 4, spines use 5,6
                spine.connect_switch(leaf_idx, leaf)

        # 6. Build routing tables
        for leaf in self.leaf_switches:
            leaf._build_routing_table()
        for spine in self.spine_switches:
            spine._build_routing_table()

        LOGGER.log("Enhanced Fat-Tree topology with PHN nodes completed")

    def _route_packet(self, packet):
        """Route packet through network"""
        packet.creation_time = self.env.now
        self.env.process(self._route_packet_through_switches(packet))

    def _route_packet_through_switches(self, packet):
        """Route packet through Fat-Tree with PHN support"""
        source_id = packet.source_id
        dest_id = packet.dest_id
        packet.add_hop(f"IP_{source_id}")

        # Determine routing based on destination type
        if dest_id < N_HOSTS:
            # Regular node
            source_leaf_idx = source_id // LEAF_HOSTS if source_id < N_HOSTS else (source_id - PHN_G1_ID)
            dest_leaf_idx = dest_id // LEAF_HOSTS
        elif dest_id in [PHN_G1_ID, PHN_G2_ID, PHN_G3_ID]:
            # PHN node
            source_leaf_idx = source_id // LEAF_HOSTS if source_id < N_HOSTS else (source_id - PHN_G1_ID)  
            phn_leaf_map = {PHN_G1_ID: 0, PHN_G2_ID: 1, PHN_G3_ID: 2}
            dest_leaf_idx = phn_leaf_map[dest_id]
        else:
            # Unknown destination
            source_leaf_idx = 0
            dest_leaf_idx = 0

        total_delay = 0.0

        # Stage 1: Source to leaf
        yield self.env.timeout(self._get_access_link_delay())
        packet.add_hop(f"leaf_{source_leaf_idx}")
        total_delay += self._get_access_link_delay()

        # Stage 2: Route through switches
        if source_leaf_idx == dest_leaf_idx:
            # Same leaf switch
            yield self.env.timeout(SWITCH_PROCESSING_DELAY)
            total_delay += SWITCH_PROCESSING_DELAY
            packet.add_hop(f"leaf_{dest_leaf_idx}_out")
        else:
            # Different leaves - through spine
            spine_idx = self._select_spine_switch(packet)

            # Leaf to spine
            yield self.env.timeout(SWITCH_PROCESSING_DELAY + self._get_backbone_link_delay())
            total_delay += SWITCH_PROCESSING_DELAY + self._get_backbone_link_delay()
            packet.add_hop(f"spine_{spine_idx}")

            # Spine to destination leaf
            yield self.env.timeout(SWITCH_PROCESSING_DELAY + self._get_backbone_link_delay())
            total_delay += SWITCH_PROCESSING_DELAY + self._get_backbone_link_delay()
            packet.add_hop(f"leaf_{dest_leaf_idx}")

            yield self.env.timeout(SWITCH_PROCESSING_DELAY)
            total_delay += SWITCH_PROCESSING_DELAY
            packet.add_hop(f"leaf_{dest_leaf_idx}_out")

        # Stage 3: Final delivery
        yield self.env.timeout(self._get_access_link_delay())
        total_delay += self._get_access_link_delay()
        packet.add_hop(f"IP_{dest_id}")

        packet.hop_count = len(packet.path) - 1
        packet.total_network_delay = total_delay

        # Queue for delivery
        self.packet_delivery_queue.put((packet, dest_id))

        if self.visualizer:
            self.visualizer.add_packet_animation(packet, f"path_{packet.tx_id}")

        # Enhanced logging with cluster info
        cluster_type = "[CROSS-CLUSTER]" if getattr(packet, 'is_cross_cluster', False) else "[LOCAL]"
        one_time_marker = " [ONE-TIME]" if getattr(packet, 'is_one_time_use', False) else ""

        LOGGER.log(f"Routed {packet} via {packet.hop_count}-hop path ({total_delay*1e9:.2f}ns) {cluster_type}{one_time_marker}")

        # Record message in performance tracker
        global PERF_TRACKER
        if PERF_TRACKER:
            PERF_TRACKER.record_message(packet, total_delay)

    def _select_spine_switch(self, packet):
        return (packet.source_id + packet.dest_id) % N_SPINE

    def _get_access_link_delay(self):
        return (PACKET_SIZE * 8) / ACCESS_LINK_BW

    def _get_backbone_link_delay(self):
        return (PACKET_SIZE * 8) / BACKBONE_LINK_BW

    def _packet_delivery_processor(self):
        """Process packet deliveries with PHN support"""
        while True:
            try:
                packet, dest_id = yield self.packet_delivery_queue.get()

                # Deliver to appropriate node type
                if dest_id < len(self.nodes):
                    # Regular node
                    self.nodes[dest_id].receive_packet(packet)
                    LOGGER.log(f"Delivered {packet} to {self.nodes[dest_id].role}{dest_id}")
                elif dest_id in [PHN_G1_ID, PHN_G2_ID, PHN_G3_ID]:
                    # PHN node
                    for phn in self.phn_nodes:
                        if phn.phn_id == dest_id:
                            phn.receive_packet(packet)
                            LOGGER.log(f"Delivered {packet} to PHN {phn.cluster_name}")
                            break
                else:
                    LOGGER.log(f"Invalid destination: {dest_id}")

            except Exception as e:
                LOGGER.log(f"Packet delivery error: {e}")
                yield self.env.timeout(10e-9)  # 10ns instead of 0.01 seconds

# Enhanced Traffic Generator with 98%/2% locality
class ClusterAwareTrafficGenerator:
    def __init__(self, network):
        self.network = network
        self.total_operations = 0
        self.local_operations = 0
        self.cross_operations = 0

    def generate_cluster_aware_operation(self):
        """Generate operation with 85% local, 15% cross-cluster traffic"""
        # Only GPU nodes can initiate operations
        gpu_nodes = list(range(N_GPUS))
        node_id = random.choice(gpu_nodes)

        # Get cluster for this GPU
        node = self.network.nodes[node_id]
        cluster = node.cluster

        # Determine local vs cross-cluster based on traffic ratio
        is_local = random.random() < LOCAL_TRAFFIC_RATIO

        if is_local and cluster in PHN_SEGMENTS:
            # 85% local traffic - choose address from this GPU's cluster
            local_addresses = PHN_SEGMENTS[cluster]['addresses']
            address = random.choice(local_addresses)
            self.local_operations += 1
        else:
            # 15% cross-cluster traffic - choose address from other clusters
            other_addresses = []
            for other_cluster, config in PHN_SEGMENTS.items():
                if other_cluster != cluster:
                    other_addresses.extend(config['addresses'])

            if other_addresses:
                address = random.choice(other_addresses)
                self.cross_operations += 1
            else:
                # Fallback to any address
                address = random.randint(0, GLOBAL_MEMORY_SIZE - 1)
                self.cross_operations += 1

        # Generate read or write operation
        if random.random() < 0.6:  # 60% reads
            operation = ('read', node_id, address, None)
        else:  # 40% writes
            value = random.randint(1, 255)
            operation = ('write', node_id, address, value)

        self.total_operations += 1
        return operation

    def get_traffic_statistics(self):
        """Get traffic generation statistics"""
        if self.total_operations == 0:
            return None

        actual_local_percentage = (self.local_operations / self.total_operations) * 100
        actual_cross_percentage = (self.cross_operations / self.total_operations) * 100
        target_local_percentage = LOCAL_TRAFFIC_RATIO * 100
        target_cross_percentage = CROSS_CLUSTER_RATIO * 100

        return {
            'total_operations': self.total_operations,
            'local_operations': self.local_operations,
            'cross_operations': self.cross_operations,
            'actual_local_percentage': actual_local_percentage,
            'actual_cross_percentage': actual_cross_percentage,
            'target_local_percentage': target_local_percentage,
            'target_cross_percentage': target_cross_percentage,
            'local_deviation': actual_local_percentage - target_local_percentage,
            'cross_deviation': actual_cross_percentage - target_cross_percentage,
            'is_within_tolerance': abs(actual_local_percentage - target_local_percentage) < 5.0  # 5% tolerance
        }

    def verify_traffic_distribution(self):
        """Verify traffic distribution meets 85%/15% ratio"""
        stats = self.get_traffic_statistics()
        if not stats:
            return False

        is_valid = stats['is_within_tolerance']

        LOGGER.log("=== TRAFFIC DISTRIBUTION VERIFICATION ===")
        LOGGER.log(f"Total operations: {stats['total_operations']}")
        LOGGER.log(f"Local: {stats['local_operations']} ({stats['actual_local_percentage']:.1f}%) [Target: {stats['target_local_percentage']:.0f}%]")
        LOGGER.log(f"Cross: {stats['cross_operations']} ({stats['actual_cross_percentage']:.1f}%) [Target: {stats['target_cross_percentage']:.0f}%]")
        LOGGER.log(f"Deviation: Local {stats['local_deviation']:+.1f}%, Cross {stats['cross_deviation']:+.1f}%")
        LOGGER.log(f"Status: {'✅ PASS' if is_valid else '❌ FAIL'}")

        return is_valid




# Enhanced Performance Tracker with PHN metrics
class EnhancedPerformanceTracker:
    def __init__(self, env):
        self.env = env
        self.operation_logs = []
        self.total_operations = 0
        self.completed_operations = 0
        self.failed_operations = 0

        # Enhanced metrics for PHN architecture
        self.local_cluster_operations = 0
        self.cross_cluster_operations = 0
        self.one_time_use_operations = 0
        self.phn_cache_hits = 0
        self.phn_cache_misses = 0
        self.dual_writes = 0

        # Network metrics
        self.total_messages = 0
        self.total_bytes = 0
        self.total_hop_count = 0
        self.packet_count = 0

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
        with self.lock:
            self.total_messages += 1
            self.total_bytes += size_bytes
            self.total_hop_count += hop_count
            self.packet_count += 1

    def log_local_cluster_message(self):
        with self.lock:
            self.local_cluster_operations += 1

    def log_cross_cluster_message(self):
        with self.lock:
            self.cross_cluster_operations += 1

    def log_one_time_use_operation(self):
        with self.lock:
            self.one_time_use_operations += 1

    def log_phn_hit(self):
        with self.lock:
            self.phn_cache_hits += 1

    def log_phn_miss(self):
        with self.lock:
            self.phn_cache_misses += 1

    def log_dual_write(self):
        with self.lock:
            self.dual_writes += 1

    def record_message(self, packet, total_delay):
        """Record message for performance tracking"""
        with self.lock:
            self.total_messages += 1
            self.total_bytes += getattr(packet, 'size_bytes', PACKET_SIZE)
            self.total_hop_count += getattr(packet, 'hop_count', 0)
            self.packet_count += 1

        # Record enhanced metrics
        if getattr(packet, 'is_cross_cluster', False):
            self.cross_cluster_operations += 1
        else:
            self.local_cluster_operations += 1

        if getattr(packet, 'is_one_time_use', False):
            self.one_time_use_operations += 1

    def compute_summary(self, sim_time_seconds):
        """Enhanced summary with PHN metrics"""
        avg_latency = 0.0
        latencies = [l.get('latency', 0) for l in self.operation_logs if 'latency' in l]
        if latencies:
            avg_latency = sum(latencies) / len(latencies)

        avg_hop = (self.total_hop_count / max(self.packet_count, 1))
        throughput_bytes_per_sec = (self.total_bytes / max(sim_time_seconds, 1e-12))

        # PHN-specific metrics
        total_phn_accesses = self.phn_cache_hits + self.phn_cache_misses
        phn_hit_rate = (self.phn_cache_hits / max(total_phn_accesses, 1)) * 100

        locality_ratio = (self.local_cluster_operations / max(self.total_operations, 1)) * 100
        cross_ratio = (self.cross_cluster_operations / max(self.total_operations, 1)) * 100

        return {
            'total_operations': self.total_operations,
            'completed_operations': self.completed_operations,
            'failed_operations': self.failed_operations,
            'total_messages': self.total_messages,
            'avg_latency_s': avg_latency,
            'avg_hop_count': avg_hop,
            'throughput_Bps': throughput_bytes_per_sec,
            'local_cluster_operations': self.local_cluster_operations,
            'cross_cluster_operations': self.cross_cluster_operations,
            'one_time_use_operations': self.one_time_use_operations,
            'locality_ratio_percent': locality_ratio,
            'cross_cluster_ratio_percent': cross_ratio,
            'phn_cache_hits': self.phn_cache_hits,
            'phn_cache_misses': self.phn_cache_misses,
            'phn_hit_rate_percent': phn_hit_rate,
            'dual_writes': self.dual_writes
        }

    def export_to_excel(self, filename=None):
        """Export logs with PHN metrics"""
        if not filename:
            timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
            filename = f"phn_chi_transactions_{timestamp}.xlsx"

        try:
            import pandas as pd
            df = pd.DataFrame(self.operation_logs)

            if not df.empty:
                df['latency_us'] = df.get('latency', 0) * 1e6
                df['latency_ns'] = df.get('latency', 0) * 1e9

            with pd.ExcelWriter(filename, engine='openpyxl') as writer:
                df.to_excel(writer, sheet_name='Transactions', index=False)

                # Add PHN summary
                summary = self.compute_summary(self.env.now if hasattr(self, 'env') else 1.0)
                summary_df = pd.DataFrame(list(summary.items()), columns=['Metric', 'Value'])
                summary_df.to_excel(writer, sheet_name='PHN_Summary', index=False)

            LOGGER.log(f"PHN transaction logs exported to {filename}")
            return filename

        except ImportError:
            return self.export_to_csv(filename.replace('.xlsx', '.csv'))

    def export_to_csv(self, filename=None):
        """Export to CSV with PHN metrics"""
        if not filename:
            timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
            filename = f"phn_chi_transactions_{timestamp}.csv"

        try:
            with open(filename, 'w', newline='', encoding='utf-8') as csvfile:
                if self.operation_logs:
                    fieldnames = self.operation_logs[0].keys()
                    writer = csv.DictWriter(csvfile, fieldnames=fieldnames)
                    writer.writeheader()

                    for log_entry in self.operation_logs:
                        enhanced_entry = dict(log_entry)
                        if 'latency' in enhanced_entry:
                            enhanced_entry['latency_us'] = enhanced_entry['latency'] * 1e6
                            enhanced_entry['latency_ns'] = enhanced_entry['latency'] * 1e9
                        writer.writerow(enhanced_entry)

            LOGGER.log(f"PHN transaction logs exported to {filename}")
            return filename

        except Exception as e:
            LOGGER.log(f"Error exporting to CSV: {e}")
            return None

# Enhanced Visualizer with PHN support
class EnhancedPHNVisualizer:
    MESSAGE_COLORS = {
        MessageType.ReadShared: '#FF4444',
        MessageType.WriteUnique: '#44FF44', 
        MessageType.CompData: '#4444FF',
        MessageType.CompAck: '#FF44FF',
        MessageType.SnpUnique: '#FFAA44',
        MessageType.SnpResp: '#44FFAA',
        MessageType.SnpSharedFwd: '#AAAA44',
        MessageType.SnpRespData: '#AA44FF',
        MessageType.WriteBackFull: '#FF8800',
        MessageType.PHNRead: '#00FFFF',
        MessageType.PHNWrite: '#FF00FF',
        MessageType.PHNInvalidate: '#FFFF00',
    }

    STATE_COLORS = {
        'I': '#CCCCCC',   # Invalid - gray
        'S': '#4444FF',   # Shared - blue
        'M': '#FF4444',   # Modified - red
        'U': '#AA44AA',   # Used (cross-cluster read, one-time) - purple
        'UP': "#309A24",  # UpdatedOnce (cross-cluster write, one-time) - dark orange
        'P': "#27E6AC",   # PHN cached - orange
    }

    def __init__(self):
        self.main_fig, self.main_ax = plt.subplots(1, 1, figsize=(18, 12))
        self.cache_fig = None
        self.cache_ax = None
        self.cache_window = None
        self.animated_packets = []
        self._setup_enhanced_topology()

    def _setup_enhanced_topology(self):
        """Setup topology with PHN nodes"""
        # Node positions organized by clusters
        self.node_positions = {}
        cluster_spacing = 8

        # Cluster layouts
        for i in range(4):
            x = 0 * cluster_spacing + i * 1.5
            y = 1
            self.node_positions[i] = (x, y)

        for i in range(4, 8):
            x = 1 * cluster_spacing + (i-4) * 1.5
            y = 1
            self.node_positions[i] = (x, y)

        for i in range(8, 12):
            x = 2 * cluster_spacing + (i-8) * 1.5
            y = 1
            self.node_positions[i] = (x, y)

        # Global cluster (GPUs 12-13, CPU 14, Global HN 15)
        for i in range(12, 16):
            x = 3 * cluster_spacing + (i-12) * 1.5
            y = 1
            self.node_positions[i] = (x, y)

        # PHN positions
        self.phn_positions = {
            PHN_G1_ID: (0 * cluster_spacing + 1.5, 2.5),
            PHN_G2_ID: (1 * cluster_spacing + 1.5, 2.5),
            PHN_G3_ID: (2 * cluster_spacing + 1.5, 2.5),
        }

        # Switch positions
        self.leaf_positions = {}
        for i in range(N_LEAF):
            x = i * cluster_spacing + 1.5
            y = 4.5
            self.leaf_positions[i] = (x, y)

        self.spine_positions = {}
        total_width = (N_LEAF - 1) * cluster_spacing
        spine_spacing = total_width / (N_SPINE - 1) if N_SPINE > 1 else 0
        for i in range(N_SPINE):
            x = i * spine_spacing + 1.5
            y = 7
            self.spine_positions[i] = (x, y)

        self._draw_enhanced_topology()

    def _draw_enhanced_topology(self):
        """Draw enhanced topology with PHN nodes"""
        self.main_ax.clear()
        self.main_ax.set_facecolor('#F8F8FF')
        self.main_ax.set_title("Fat-Tree NoC with PHN Architecture [BlackMagnet]",
                              fontsize=16, fontweight='bold', pad=20)

        # Draw connections
        for leaf_idx, leaf_pos in self.leaf_positions.items():
            for spine_idx, spine_pos in self.spine_positions.items():
                self.main_ax.plot([leaf_pos[0], spine_pos[0]], [leaf_pos[1], spine_pos[1]],
                                 'lightcoral', linewidth=2, alpha=0.7)

        # PHN connections
        for phn_id, phn_pos in self.phn_positions.items():
            phn_leaf_map = {PHN_G1_ID: 0, PHN_G2_ID: 1, PHN_G3_ID: 2}
            leaf_idx = phn_leaf_map[phn_id]
            leaf_pos = self.leaf_positions[leaf_idx]
            self.main_ax.plot([phn_pos[0], leaf_pos[0]], [phn_pos[1], leaf_pos[1]],
                             'orange', linewidth=3, alpha=0.8)

        # GPU connections with cluster colors
        cluster_colors = {'G1': 'lightblue', 'G2': 'lightgreen', 'G3': 'lightpink', 'G_prime': 'lightyellow'}

        for gpu_id, gpu_pos in self.node_positions.items():
            if gpu_id < N_GPUS:
                cluster_name = None
                for cluster, config in PHN_SEGMENTS.items():
                    if gpu_id in config['gpus']:
                        cluster_name = cluster
                        break

                leaf_idx = gpu_id // LEAF_HOSTS
                leaf_pos = self.leaf_positions[leaf_idx]
                color = cluster_colors.get(cluster_name, 'lightgray')
                self.main_ax.plot([gpu_pos[0], leaf_pos[0]], [gpu_pos[1], leaf_pos[1]],
                                 color, linewidth=2, alpha=0.7)

        # Draw switches
        for spine_idx, pos in self.spine_positions.items():
            circle = patches.Circle(pos, 0.6, facecolor='red', edgecolor='darkred', linewidth=3)
            self.main_ax.add_patch(circle)
            self.main_ax.text(pos[0], pos[1], f"L2\nSpine{spine_idx}", ha='center', va='center',
                             fontsize=9, fontweight='bold', color='white')

        for leaf_idx, pos in self.leaf_positions.items():
            circle = patches.Circle(pos, 0.5, facecolor='orange', edgecolor='darkorange', linewidth=2)
            self.main_ax.add_patch(circle)
            self.main_ax.text(pos[0], pos[1], f"L1\nLeaf{leaf_idx}", ha='center', va='center',
                             fontsize=8, fontweight='bold', color='white')

        # Draw PHN nodes
        for phn_id, pos in self.phn_positions.items():
            phn_name = {PHN_G1_ID: 'PHN-G1', PHN_G2_ID: 'PHN-G2', PHN_G3_ID: 'PHN-G3'}[phn_id]
            cluster = phn_name.split('-')[1]
            config = PHN_SEGMENTS[cluster]

            hexagon = patches.RegularPolygon(pos, 6, radius=0.7, facecolor='purple',
                                          edgecolor='indigo', linewidth=3)
            self.main_ax.add_patch(hexagon)
            self.main_ax.text(pos[0], pos[1], f"{phn_name}\nA{config['addresses'][0]}-{config['addresses'][-1]}",
                             ha='center', va='center', fontsize=8, fontweight='bold', color='white')

        # Draw nodes with cluster labels
        cluster_labels = {}
        for gpu_id, pos in self.node_positions.items():
            if gpu_id < N_GPUS:
                cluster_name = None
                for cluster, config in PHN_SEGMENTS.items():
                    if gpu_id in config['gpus']:
                        cluster_name = cluster
                        break

                color = cluster_colors.get(cluster_name, 'lightgray')
                rect = patches.Rectangle((pos[0]-0.4, pos[1]-0.4), 0.8, 0.8,
                                        facecolor=color, edgecolor='darkblue', linewidth=2)
                self.main_ax.add_patch(rect)
                self.main_ax.text(pos[0], pos[1], f"GPU\n{gpu_id}", ha='center', va='center',
                                 fontsize=7, fontweight='bold', color='darkblue')

                # Show cluster labels
                if cluster_name and cluster_name not in cluster_labels:
                    cluster_display = cluster_name if cluster_name != 'G_prime' else 'Global'
                    self.main_ax.text(pos[0], pos[1]-0.8, f"Cluster {cluster_display}",
                                     ha='center', va='center', fontsize=6, style='italic')
                    cluster_labels[cluster_name] = True

            elif gpu_id == CPU_NODE_ID:
                rect = patches.Rectangle((pos[0]-0.4, pos[1]-0.4), 0.8, 0.8,
                                        facecolor='lightgray', edgecolor='gray', linewidth=2)
                self.main_ax.add_patch(rect)
                self.main_ax.text(pos[0], pos[1], f"CPU\n{gpu_id}", ha='center', va='center',
                                 fontsize=7, fontweight='bold', color='black')
            else:
                # Global HN
                rect = patches.Rectangle((pos[0]-0.4, pos[1]-0.4), 0.8, 0.8,
                                        facecolor='gold', edgecolor='darkorange', linewidth=3)
                self.main_ax.add_patch(rect)
                self.main_ax.text(pos[0], pos[1], f"Global\nHN{gpu_id}", ha='center', va='center',
                                 fontsize=6, fontweight='bold', color='black')

        # Set limits and grid
        all_positions = list(self.node_positions.values()) + list(self.phn_positions.values()) +                        list(self.leaf_positions.values()) + list(self.spine_positions.values())

        if all_positions:
            max_x = max(pos[0] for pos in all_positions)
            min_x = min(pos[0] for pos in all_positions)
            self.main_ax.set_xlim(min_x - 2, max_x + 2)
            self.main_ax.set_ylim(-1, 9)

        self.main_ax.set_aspect('equal')
        self.main_ax.grid(True, alpha=0.3)

        self._add_enhanced_message_legend()

    def _add_enhanced_message_legend(self):
        """Add enhanced message legend with PHN messages"""
        legend_elements = []
        message_descriptions = {
            MessageType.ReadShared: 'ReadShared (Request)',
            MessageType.WriteUnique: 'WriteUnique (Request)',
            MessageType.CompData: 'CompData (Response)',
            MessageType.CompAck: 'CompAck (Response)',
            MessageType.WriteBackFull: 'WriteBackFull (Writeback)',
            MessageType.PHNRead: 'PHN Read (Local)',
            MessageType.PHNWrite: 'PHN Dual-Write',
        }

        for msg_type, description in message_descriptions.items():
            color = self.MESSAGE_COLORS.get(msg_type, '#000000')
            patch = patches.Patch(facecolor=color, label=description)
            legend_elements.append(patch)

        legend = self.main_ax.legend(
            handles=legend_elements,
            loc='upper center',
            bbox_to_anchor=(0.5, -0.05),
            ncol=4,
            fontsize=9,
            frameon=True,
            fancybox=True,
            shadow=True,
            title="Enhanced CHI + PHN Protocol Messages",
            title_fontsize=11
        )

        legend.get_frame().set_facecolor('#F8F8FF')
        legend.get_frame().set_edgecolor('black')
        legend.get_frame().set_alpha(0.9)

    def create_cache_window(self):
        """Create cache window with PHN support"""
        if self.cache_window is None:
            self.cache_window = tk.Toplevel()
            self.cache_window.title("Enhanced PHN Memory Architecture")
            self.cache_window.geometry("2000x1200")

            self.cache_fig, self.cache_ax = plt.subplots(figsize=(20, 12))
            canvas = FigureCanvasTkAgg(self.cache_fig, master=self.cache_window)
            canvas.draw()
            canvas.get_tk_widget().pack(fill=tk.BOTH, expand=True)

            self._setup_enhanced_cache_display()

    def _setup_enhanced_cache_display(self):
        """Setup cache display with PHN nodes"""
        if self.cache_ax is None:
            return

        self.cache_ax.clear()
        self.cache_ax.set_facecolor('#F0F0F0')
        self.cache_ax.set_title("Enhanced PHN Memory Architecture - Cache States",
                               fontsize=16, fontweight='bold', pad=20)

        # Wider layout for PHNs
        self.cache_ax.set_xlim(-1.5, N_GPUS + 8)
        self.cache_ax.set_ylim(-2, GLOBAL_MEMORY_SIZE + 1)

        # Enhanced labels including PHNs
        x_labels = [f"GPU{i}" for i in range(N_GPUS)] + ["PHN-G1", "PHN-G2", "PHN-G3", "GlobalHN"]
        x_positions = list(range(N_GPUS)) + [N_GPUS + 1, N_GPUS + 3, N_GPUS + 5, N_GPUS + 7]

        self.cache_ax.set_xticks(x_positions)
        self.cache_ax.set_xticklabels(x_labels, fontsize=10, rotation=45, fontweight='bold')
        self.cache_ax.set_yticks(range(GLOBAL_MEMORY_SIZE))
        self.cache_ax.set_yticklabels([f"A{i}" for i in range(GLOBAL_MEMORY_SIZE)], fontsize=9)
        self.cache_ax.grid(True, alpha=0.5)

        # Add PHN memory boundaries
        self._draw_phn_memory_boundaries()

        # Enhanced legend with new states
        state_legend = []
        state_names = {
            'I': 'Invalid',
            'S': 'Shared (Multiple readers)',
            'M': 'Modified (Dirty - needs writeback)',
            'U': 'Used (Cross-cluster read - ONE-TIME only)',
            'UP': 'UpdatedOnce (Cross-cluster write - ONE-TIME only)',
            'P': 'PHN Cached (Local segment data)'
        }

        for state, color in self.STATE_COLORS.items():
            state_legend.append(patches.Patch(facecolor=color, label=state_names[state]))

        legend = self.cache_ax.legend(handles=state_legend, loc='upper left', bbox_to_anchor=(1.02, 1), fontsize=10)
        legend.get_frame().set_facecolor('#F8F8FF')
        legend.get_frame().set_edgecolor('black')

    def _draw_phn_memory_boundaries(self):
        """Draw PHN memory segment boundaries"""
        segment_colors = {'G1': 'lightblue', 'G2': 'lightgreen', 'G3': 'lightpink', 'G_prime': 'lightyellow'}

        for cluster, config in PHN_SEGMENTS.items():
            if config['addresses']:
                start_addr = config['addresses'][0]
                end_addr = config['addresses'][-1]
                color = segment_colors.get(cluster, 'lightgray')

                # Draw boundary rectangle covering all GPU columns
                boundary_rect = patches.Rectangle(
                    (-1, start_addr - 0.5),
                    N_GPUS + 1,
                    end_addr - start_addr + 1,
                    facecolor=color,
                    alpha=0.1,
                    edgecolor='black',
                    linewidth=2,
                    linestyle='--'
                )
                self.cache_ax.add_patch(boundary_rect)

                # Add segment label
                self.cache_ax.text(
                    -0.8, (start_addr + end_addr) / 2,
                    f"{cluster}\nA{start_addr}-{end_addr}",
                    ha='center', va='center',
                    fontsize=8, fontweight='bold',
                    bbox=dict(boxstyle="round,pad=0.3", facecolor=color, alpha=0.7)
                )

    def add_packet_animation(self, packet, link_name):
        """Enhanced packet animation with PHN support"""
        if len(packet.path) < 2:
            return

        animation_path = []
        for hop in packet.path:
            if hop.startswith('IP_'):
                node_id = int(hop.split('_')[1])
                if node_id in self.node_positions:
                    animation_path.append(self.node_positions[node_id])
                elif node_id in self.phn_positions:
                    animation_path.append(self.phn_positions[node_id])
            elif hop.startswith('leaf_'):
                leaf_id = int(hop.split('_')[1])
                if leaf_id in self.leaf_positions:
                    animation_path.append(self.leaf_positions[leaf_id])
            elif hop.startswith('spine_'):
                spine_id = int(hop.split('_')[1])
                if spine_id in self.spine_positions:
                    animation_path.append(self.spine_positions[spine_id])

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
        """Update packet animations"""
        # Clear old animations
        for packet_info in self.animated_packets:
            for patch in packet_info['patches']:
                try:
                    patch.remove()
                except:
                    pass
            packet_info['patches'] = []

        # Update and draw packets
        active_packets = []
        for packet_info in self.animated_packets:
            path = packet_info['path']
            segment = packet_info['current_segment']
            progress = packet_info['segment_progress']

            if segment < len(path) - 1:
                start_pos = path[segment]
                end_pos = path[segment + 1]

                current_x = start_pos[0] + (end_pos[0] - start_pos[0]) * progress
                current_y = start_pos[1] + (end_pos[1] - start_pos[1]) * progress

                color = self.MESSAGE_COLORS.get(packet_info['packet'].msg_type, '#000000')

                # Special rendering for cross-cluster and one-time packets
                if getattr(packet_info['packet'], 'is_cross_cluster', False):
                    packet_dot = patches.Circle((current_x, current_y), 0.2,
                                               facecolor=color, edgecolor='purple', linewidth=3)
                elif getattr(packet_info['packet'], 'is_one_time_use', False):
                    packet_dot = patches.Circle((current_x, current_y), 0.18,
                                               facecolor=color, edgecolor='orange', linewidth=2)
                else:
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
        """Enhanced cache display with PHN support"""
        if self.cache_ax is None:
            return

        self.cache_ax.clear()
        self._setup_enhanced_cache_display()

        # Display GPU caches with enhanced states
        for gpu_id in range(N_GPUS):
            node = network.nodes[gpu_id]
            cache_data = node.get_cache_display_data()

            for addr in range(GLOBAL_MEMORY_SIZE):
                cache_info = cache_data.get(addr, {
                    'state': 'I', 'data': None, 'lru_position': -1, 
                    'is_local': False, 'is_one_time_use': False, 'can_cache_hit': False
                })

                state = cache_info['state']
                data = cache_info['data']
                lru_pos = cache_info.get('lru_position', -1)
                is_local = cache_info.get('is_local', False)
                is_one_time = cache_info.get('is_one_time_use', False)
                can_hit = cache_info.get('can_cache_hit', False)

                color = self.STATE_COLORS.get(state, '#CCCCCC')
                alpha = 0.9 if state != 'I' else 0.3

                # Enhanced highlighting for one-time use states
                if is_one_time and state in ['U', 'UP']:
                    alpha = 1.0  # Full visibility for one-time use states
                    # Add special border for one-time use
                    border_color = 'purple' if state == 'U' else 'darkorange'
                    border_width = 3
                else:
                    border_color = 'black'
                    border_width = 1

                # Enhanced alpha for local addresses
                if is_local and state != 'I':
                    alpha = min(1.0, alpha + 0.1)

                if lru_pos >= 0:
                    alpha = 0.5 + 0.4 * (lru_pos / max(GPU_CACHE_SIZE - 1, 1))

                rect = patches.Rectangle(
                    (gpu_id - 0.48, addr - 0.45), 0.96, 0.90,
                    facecolor=color, edgecolor=border_color, 
                    linewidth=border_width, alpha=alpha
                )
                self.cache_ax.add_patch(rect)

                if state != 'I' and data is not None:
                    text = f"{state}\n{data}"
                    if lru_pos >= 0:
                        text += f"\nLRU:{lru_pos}"
                    if is_local:
                        text += "\n(L)"  # Local marker
                    if is_one_time:
                        text += "\n[1×]"  # One-time use marker
                    if not can_hit and state != 'I':
                        text += "\n[NO HIT]"  # Cannot provide cache hits
                else:
                    text = state

                # Enhanced font colors for visibility
                font_color = 'white' if state not in ['I'] else 'black'
                if is_local:
                    font_color = 'yellow' if state != 'I' else 'orange'
                if is_one_time:
                    font_color = 'white'  # White for one-time use

                self.cache_ax.text(gpu_id, addr, text, ha='center', va='center',
                                  fontsize=7, fontweight='bold', color=font_color)

        # Display PHN caches
        x_positions = [N_GPUS + 1, N_GPUS + 3, N_GPUS + 5]
        for idx, phn in enumerate(network.phn_nodes):
            if idx < len(x_positions):
                x_pos = x_positions[idx]
                cache_data = phn.get_cache_display_data()

                for addr in phn.address_range:
                    if addr in cache_data:
                        cache_info = cache_data[addr]
                        state = cache_info['state']
                        data = cache_info['data']

                        if state == 'P' and data is not None:
                            color = self.STATE_COLORS.get(state, '#CCCCCC')
                            alpha = 0.8

                            rect = patches.Rectangle(
                                (x_pos - 0.48, addr - 0.45), 0.96, 0.90,
                                facecolor=color, edgecolor='purple', linewidth=2, alpha=alpha
                            )
                            self.cache_ax.add_patch(rect)

                            text = f"P\n{data}"
                            is_exclusive = cache_info.get('is_exclusive', False)
                            if is_exclusive:
                                text += "\n(EXC)"

                            self.cache_ax.text(x_pos, addr, text, ha='center', va='center',
                                              fontsize=7, fontweight='bold', color='white')

        # Display Global HN memory
        global_mem_node = network.nodes[GLOBAL_MEMORY_ID]
        memory_data = global_mem_node.get_memory_display_data()
        x_pos = N_GPUS + 7

        for addr in range(GLOBAL_MEMORY_SIZE):
            value = memory_data.get(addr, 0)

            # Check if any cache has dirty copy
            has_dirty = False
            for gpu_id in range(N_GPUS):
                cache_data = network.nodes[gpu_id].get_cache_display_data()
                if addr in cache_data and cache_data[addr].get('state') == 'M':
                    has_dirty = True
                    break

            if not has_dirty:
                for phn in network.phn_nodes:
                    if addr in phn.address_range and addr in phn.phn_cache:
                        has_dirty = True
                        break

            if has_dirty:
                rect = patches.Rectangle(
                    (x_pos - 0.48, addr - 0.45), 0.96, 0.90,
                    facecolor='#FFAAAA', edgecolor='red', linewidth=2
                )
                text = f"STALE\n{value}"
            else:
                rect = patches.Rectangle(
                    (x_pos - 0.48, addr - 0.45), 0.96, 0.90,
                    facecolor='lightyellow', edgecolor='black', linewidth=1
                )
                text = f"CURRENT\n{value}"

            self.cache_ax.add_patch(rect)
            self.cache_ax.text(x_pos, addr, text, ha='center', va='center',
                              fontsize=7, fontweight='bold')

        if hasattr(self.cache_fig, 'canvas'):
            self.cache_fig.canvas.draw_idle()

# Initialize global performance tracker
PERF_TRACKER = None




# Enhanced Simulation Controller with PHN support
def run_enhanced_phn_simulation(command_queue, network, traffic_generator):
    """Run simulation with PHN architecture support"""
    env = network.env
    operation_counter = 0

    global PERF_TRACKER
    PERF_TRACKER = EnhancedPerformanceTracker(env)

    LOGGER.log("=== ENHANCED PHN FAT-TREE CHI SIMULATION STARTED ===")
    LOGGER.log(f"PHN Architecture: G1(0-3), G2(4-7), G3(8-11), G_prime(12-13)")
    LOGGER.log(f"Traffic Pattern: {LOCAL_TRAFFIC_RATIO*100}% local, {CROSS_CLUSTER_RATIO*100}% cross-cluster")
    LOGGER.log(f"New Cache States: Modified(M), Shared(S), Invalid(I), Used(U), UpdatedOnce(UP)")
    LOGGER.log(f"PHN Nodes: {len(network.phn_nodes)} partial home nodes for cluster management")

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

                if node_id not in range(N_GPUS):
                    LOGGER.log(f"Only GPU nodes (0-{N_GPUS-1}) can initiate operations")
                    continue

                if not (0 <= address < GLOBAL_MEMORY_SIZE):
                    LOGGER.log(f"Invalid address {address}. Valid range: 0-{GLOBAL_MEMORY_SIZE-1}")
                    continue

                node = network.nodes[node_id]

                # Determine if this is local or cross-cluster
                is_local = node._is_local_address(address)
                cluster_marker = f"[{node.cluster}→LOCAL]" if is_local else f"[{node.cluster}→CROSS-CLUSTER]"

                if operation == 'read':
                    PERF_TRACKER.log_operation_start(operation_id, node_id, 'READ', address)
                    completion_event = node.issue_read_operation(address, operation_id)
                    result = env.run(until=env.any_of([completion_event, env.timeout(SIM_TIMEOUT)]))

                    if completion_event in result:
                        PERF_TRACKER.log_operation_complete(operation_id)
                        if is_local:
                            PERF_TRACKER.log_local_cluster_message()
                        else:
                            PERF_TRACKER.log_cross_cluster_message()
                        LOGGER.log(f"✅ READ #{operation_counter} completed (GPU{node_id} A{address}) {cluster_marker}")
                    else:
                        PERF_TRACKER.log_operation_complete(operation_id, 'TIMEOUT')
                        LOGGER.log(f"❌ READ #{operation_counter} TIMEOUT")

                elif operation == 'write':
                    if len(parts) < 4:
                        continue
                    value = int(parts[3])

                    PERF_TRACKER.log_operation_start(operation_id, node_id, 'WRITE', address, value)
                    completion_event = node.issue_write_operation(address, value, operation_id)
                    result = env.run(until=env.any_of([completion_event, env.timeout(SIM_TIMEOUT)]))

                    if completion_event in result:
                        PERF_TRACKER.log_operation_complete(operation_id)
                        if is_local:
                            PERF_TRACKER.log_local_cluster_message()
                        else:
                            PERF_TRACKER.log_cross_cluster_message()
                            PERF_TRACKER.log_one_time_use_operation()
                        LOGGER.log(f"✅ WRITE #{operation_counter} completed (GPU{node_id} A{address}={value}) {cluster_marker}")
                    else:
                        PERF_TRACKER.log_operation_complete(operation_id, 'TIMEOUT')
                        LOGGER.log(f"❌ WRITE #{operation_counter} TIMEOUT")

            except Exception as e:
                LOGGER.log(f"Operation error: {e}")

        except queue.Empty:
            continue
        except Exception as e:
            LOGGER.log(f"Simulation error: {e}")

# Enhanced GUI Application with PHN support
class EnhancedPHNSimulatorApp(tk.Tk):
    def __init__(self):
        super().__init__()
        self.title("Enhanced PHN Fat-Tree CHI Simulator [BlackMagnet]")
        self.geometry("1400x900")
        self.configure(bg='#F0F0F0')

        # Initialize components
        self.env = simpy.Environment()
        self.visualizer = EnhancedPHNVisualizer()
        self.network = EnhancedFatTreeNetwork(self.env, self.visualizer)
        self.traffic_generator = ClusterAwareTrafficGenerator(self.network)
        self.random_traffic_enabled = False

        self._create_enhanced_gui()
        self._initialize_simulation()
        self._start_update_loops()

        LOGGER.log("🚀 Enhanced PHN Fat-Tree CHI Simulator [BlackMagnet] Started!")
        LOGGER.log("=" * 70)
        LOGGER.log("PHN ARCHITECTURE:")
        LOGGER.log("  • Cluster G1: GPUs 0-3, Addresses 0-9")
        LOGGER.log("  • Cluster G2: GPUs 4-7, Addresses 10-19")
        LOGGER.log("  • Cluster G3: GPUs 8-11, Addresses 20-29")
        LOGGER.log("  • Cluster G_prime: GPUs 12-13, Addresses 30-31")
        LOGGER.log(f"  • Traffic Pattern: {LOCAL_TRAFFIC_RATIO*100}% local, {CROSS_CLUSTER_RATIO*100}% cross-cluster")
        LOGGER.log("ENHANCED CACHE STATES:")
        LOGGER.log("  • M: Modified (dirty, needs writeback)")
        LOGGER.log("  • S: Shared (multiple readers)")
        LOGGER.log("  • I: Invalid (no data)")
        LOGGER.log("  • U: Used (cross-cluster read, ONE-TIME only)")
        LOGGER.log("  • UP: UpdatedOnce (cross-cluster write, ONE-TIME only)")
        LOGGER.log("=" * 70)

    def _create_enhanced_gui(self):
        """Create enhanced GUI with PHN controls"""
        self.grid_rowconfigure(0, weight=1)
        self.grid_columnconfigure(0, weight=2)
        self.grid_columnconfigure(1, weight=1)

        # Main visualization panel
        viz_panel = ttk.LabelFrame(self, text="Enhanced PHN Fat-Tree Architecture [BlackMagnet]", padding=5)
        viz_panel.grid(row=0, column=0, sticky="nsew", padx=5, pady=5)

        self.canvas = FigureCanvasTkAgg(self.visualizer.main_fig, master=viz_panel)
        self.canvas.draw()
        self.canvas.get_tk_widget().pack(fill=tk.BOTH, expand=True)

        # Control panel
        control_panel = ttk.Frame(self)
        control_panel.grid(row=0, column=1, sticky="nsew", padx=5, pady=5)
        control_panel.grid_rowconfigure(7, weight=1)

        self._create_command_interface(control_panel)
        self._create_cluster_quick_actions(control_panel)
        self._create_phn_test_controls(control_panel)
        self._create_traffic_controls(control_panel)
        self._create_cache_controls(control_panel)
        self._create_phn_export_panel(control_panel)
        self._create_log_panel(control_panel)

    def _create_command_interface(self, parent):
        """Create command interface"""
        cmd_frame = ttk.LabelFrame(parent, text="Command Interface", padding=5)
        cmd_frame.grid(row=0, column=0, sticky="ew", pady=(0, 5))
        cmd_frame.grid_columnconfigure(1, weight=1)

        ttk.Label(cmd_frame, text="Command:").grid(row=0, column=0, sticky="w")

        self.command_var = tk.StringVar()
        self.command_entry = ttk.Entry(cmd_frame, textvariable=self.command_var, width=25)
        self.command_entry.grid(row=0, column=1, sticky="ew", padx=(5, 0))
        self.command_entry.bind("<Return>", lambda e: self.execute_command())

        ttk.Button(cmd_frame, text="Execute", command=self.execute_command).grid(row=0, column=2, padx=(5, 0))

    def _create_cluster_quick_actions(self, parent):
        """Create cluster-specific quick actions"""
        cluster_frame = ttk.LabelFrame(parent, text="Cluster-Specific Tests", padding=5)
        cluster_frame.grid(row=1, column=0, sticky="ew", pady=(0, 5))

        actions = [
            ("G1 Local Read", "read 1 5"),
            ("G1→G2 Cross Read", "read 1 15"),
            ("G2 Local Write", "write 5 12 100"),
            ("G2→G3 Cross Write", "write 5 25 200"),
            ("Compulsory Miss Test", lambda: self.run_compulsory_miss_test()),
            ("One-Time Use Test", lambda: self.run_one_time_use_test())
        ]

        for i, (text, action) in enumerate(actions):
            if callable(action):
                btn = ttk.Button(cluster_frame, text=text, command=action)
            else:
                btn = ttk.Button(cluster_frame, text=text,
                               command=lambda cmd=action: self.queue_command(cmd))
            btn.grid(row=i//2, column=i%2, padx=2, pady=2, sticky="ew")

        cluster_frame.grid_columnconfigure(0, weight=1)
        cluster_frame.grid_columnconfigure(1, weight=1)

    def _create_phn_test_controls(self, parent):
        """Create PHN-specific test controls"""
        phn_frame = ttk.LabelFrame(parent, text="PHN Architecture Tests", padding=5)
        phn_frame.grid(row=2, column=0, sticky="ew", pady=(0, 5))

        tests = [
            ("PHN Cache Hit Test", lambda: self.run_phn_cache_test()),
            ("Cross-Cluster Chain", lambda: self.run_cross_cluster_chain()),
            ("Writeback Chain Test", lambda: self.run_writeback_chain_test()),
            ("Traffic Pattern Test", lambda: self.run_traffic_pattern_test())
        ]

        for i, (text, action) in enumerate(tests):
            btn = ttk.Button(phn_frame, text=text, command=action)
            btn.grid(row=i//2, column=i%2, padx=2, pady=2, sticky="ew")

        phn_frame.grid_columnconfigure(0, weight=1)
        phn_frame.grid_columnconfigure(1, weight=1)

    def _create_traffic_controls(self, parent):
        """Create traffic controls"""
        traffic_frame = ttk.LabelFrame(parent, text="Cluster-Aware Traffic (85%/15%)", padding=5)
        traffic_frame.grid(row=3, column=0, sticky="ew", pady=(0, 5))

        self.random_traffic_var = tk.BooleanVar()
        ttk.Checkbutton(traffic_frame, text="Enable Smart Traffic",
                       variable=self.random_traffic_var,
                        command=self.toggle_random_traffic).pack(anchor='w')

        ttk.Button(traffic_frame, text="Verify Traffic Distribution",
                  command=self.verify_traffic_distribution).pack(fill='x', pady=2)

    def _create_cache_controls(self, parent):
        """Create cache controls"""
        cache_frame = ttk.LabelFrame(parent, text="Enhanced Cache & PHN View", padding=5)
        cache_frame.grid(row=4, column=0, sticky="ew", pady=(0, 5))

        ttk.Button(cache_frame, text="Open Enhanced Cache Window",
                   command=self.open_cache_window).pack(fill='x', pady=2)

    def _create_phn_export_panel(self, parent):
        """Create PHN export panel"""
        export_frame = ttk.LabelFrame(parent, text="PHN Performance Analytics", padding=5)
        export_frame.grid(row=5, column=0, sticky="ew", pady=(0, 5))

        ttk.Button(export_frame, text="Export PHN Logs (Excel)",
                   command=self.export_phn_logs).pack(fill='x', pady=2)

        ttk.Button(export_frame, text="PHN Performance Summary",
                  command=self.show_phn_performance_summary).pack(fill='x', pady=2)

        ttk.Button(export_frame, text="Cluster Statistics",
                  command=self.show_cluster_statistics).pack(fill='x', pady=2)

        # Enhanced info
        info_text = f"""PHN Architecture Benefits:
• {LOCAL_TRAFFIC_RATIO*100}% locality (85% local traffic)
• Reduced global HN traffic
• One-time use for cross-cluster
• Dual-write consistency
• Enhanced cache hierarchy

New Cache States:
• U: Cross-cluster read (one-time)
• UP: Cross-cluster write (one-time)  
• P: PHN cached data"""

        info_label = ttk.Label(export_frame, text=info_text, font=('Consolas', 8))
        info_label.pack(anchor='w', pady=(5, 0))

    def _create_log_panel(self, parent):
        """Create log panel"""
        log_frame = ttk.LabelFrame(parent, text="Enhanced PHN System Log", padding=3)
        log_frame.grid(row=6, column=0, sticky="nsew")
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
        """Initialize simulation thread"""
        self.command_queue = queue.Queue()
        self.simulation_thread = threading.Thread(
            target=run_enhanced_phn_simulation,
            args=(self.command_queue, self.network, self.traffic_generator),
            daemon=True
        )
        self.simulation_thread.start()

        self.animation = FuncAnimation(self.visualizer.main_fig, self.visualizer.update_animation,
                                     interval=100, blit=False, cache_frame_data=False)

    def _start_update_loops(self):
        """Start update loops"""
        self.after(100, self.update_log_display)
        self.after(2000, self.update_cache_display)
        self.after(int(RANDOM_TRAFFIC_PERIOD * 1000), self.generate_random_traffic)

    # Enhanced test methods
    def run_compulsory_miss_test(self):
        """Test compulsory misses in PHN architecture"""
        LOGGER.log("🧪 Testing COMPULSORY MISSES in PHN architecture...")
        LOGGER.log("   All PHN caches start empty - first access always misses")

        # Test sequence across different clusters
        test_sequence = [
            ("read 0 5", "G1 GPU accesses G1 memory (compulsory miss → PHN cache)"),
            ("read 1 5", "G1 GPU accesses same address (PHN cache hit)"),
            ("read 4 15", "G2 GPU accesses G2 memory (compulsory miss → PHN cache)"),
            ("read 0 15", "G1 GPU cross-cluster access (cross-cluster miss)"),
        ]

        for i, (command, description) in enumerate(test_sequence):
            delay = (i + 1) * 2000  # Stagger commands
            self.after(delay, lambda cmd=command, desc=description, step=i+1: [
                LOGGER.log(f"   Step {step}: {desc}"),
                self.queue_command(cmd)
            ])

    def run_one_time_use_test(self):
        """Test one-time use cache states"""
        LOGGER.log("🧪 Testing ONE-TIME USE cache states...")
        LOGGER.log("   Cross-cluster reads get U state, writes get UP state")

        test_sequence = [
            ("read 0 25", "G1→G3 cross-cluster read (should get U state)"),
            ("read 0 25", "Same GPU reads again (should miss - U state exhausted)"),
            ("write 4 5", "G2→G1 cross-cluster write (should get UP state)"),
            ("read 4 5", "Same GPU reads back (should miss - UP state exhausted)"),
        ]

        for i, (command, description) in enumerate(test_sequence):
            delay = (i + 1) * 3000
            self.after(delay, lambda cmd=command, desc=description, step=i+1: [
                LOGGER.log(f"   Step {step}: {desc}"),
                self.queue_command(cmd)
            ])

    def run_phn_cache_test(self):
        """Test PHN cache hit behavior"""
        LOGGER.log("🧪 Testing PHN CACHE behavior...")

        # Test PHN cache hits within cluster
        test_commands = [
            "read 1 7",   # GPU1 reads A7 (G1 cluster, PHN cache miss)
            "read 2 7",   # GPU2 reads A7 (should hit in PHN cache)  
            "read 3 7",   # GPU3 reads A7 (should hit in PHN cache)
            "write 1 8 150",  # GPU1 writes A8 (updates PHN cache)
            "read 2 8",   # GPU2 reads A8 (should hit in updated PHN cache)
        ]

        for i, command in enumerate(test_commands):
            delay = (i + 1) * 2000
            self.after(delay, lambda cmd=command, step=i+1: [
                LOGGER.log(f"   PHN Cache Test Step {step}: {cmd}"),
                self.queue_command(cmd)
            ])

    def run_cross_cluster_chain(self):
        """Test cross-cluster transaction chain"""
        LOGGER.log("🧪 Testing CROSS-CLUSTER transaction chain...")

        chain_sequence = [
            "write 0 25 100",  # G1→G3 cross write
            "read 8 25",       # G3 local read (should see updated value)
            "write 8 5 200",   # G3→G1 cross write  
            "read 1 5",        # G1 local read (should see G3's update)
        ]

        for i, command in enumerate(chain_sequence):
            delay = (i + 1) * 3000
            self.after(delay, lambda cmd=command, step=i+1: [
                LOGGER.log(f"   Cross-Cluster Chain Step {step}: {cmd}"),
                self.queue_command(cmd)
            ])

    def run_writeback_chain_test(self):
        """Test writeback chain through PHN to global"""
        LOGGER.log("🧪 Testing WRITEBACK CHAIN: GPU → PHN → Global...")

        writeback_sequence = [
            "write 2 6 111",   # GPU2 writes A6 (Modified in GPU, updated in PHN)
            "read 10 6",       # GPU10 cross-cluster read (triggers dual consistency)
            "write 0 6 222",   # GPU0 overwrites A6 (should trigger writeback chain)
            "read 12 6",       # G_prime GPU reads A6 (should see final value)
        ]

        for i, command in enumerate(writeback_sequence):
            delay = (i + 1) * 2500
            self.after(delay, lambda cmd=command, step=i+1: [
                LOGGER.log(f"   Writeback Chain Step {step}: {cmd}"),
                self.queue_command(cmd)
            ])

    def run_traffic_pattern_test(self):
        """Test 98%/2% traffic pattern"""
        LOGGER.log("🧪 Testing 98%/2% TRAFFIC PATTERN...")
        LOGGER.log("   Generating cluster-aware operations to verify locality...")

        # Enable traffic
        self.random_traffic_enabled = True
        self.random_traffic_var.set(True)

        # Schedule stop after 10 seconds
        def stop_traffic():
            self.random_traffic_enabled = False
            self.random_traffic_var.set(False)
            LOGGER.log("   Traffic pattern test completed")
            self.verify_traffic_distribution()

        self.after(10000, stop_traffic)

    def verify_traffic_distribution(self):
        """Verify traffic distribution meets target ratios"""
        if hasattr(self.traffic_generator, 'verify_traffic_distribution'):
            result = self.traffic_generator.verify_traffic_distribution()
            if result:
                LOGGER.log("✅ Traffic distribution VERIFIED - meets 85%/15% target")
            else:
                LOGGER.log("⚠️ Traffic distribution deviation detected")
        else:
            LOGGER.log("Traffic statistics not available")

    # Enhanced export methods
    def export_phn_logs(self):
        """Export PHN transaction logs"""
        try:
            if PERF_TRACKER:
                filename = PERF_TRACKER.export_to_excel()
                if filename:
                    messagebox.showinfo("Export Success", f"PHN transaction logs exported to:\n{filename}")
                    LOGGER.log(f"✅ PHN logs exported to {filename}")
                else:
                    messagebox.showerror("Export Error", "Failed to export PHN logs")
            else:
                messagebox.showwarning("No Data", "No PHN performance data available")
        except Exception as e:
            messagebox.showerror("Export Error", f"Error exporting PHN logs: {str(e)}")
            LOGGER.log(f"❌ Error exporting PHN logs: {e}")

    def show_phn_performance_summary(self):
        """Show PHN performance summary"""
        try:
            if PERF_TRACKER:
                summary_window = tk.Toplevel(self)
                summary_window.title("Enhanced PHN Performance Summary")
                summary_window.geometry("800x700")

                frame = ttk.Frame(summary_window)
                frame.pack(fill='both', expand=True, padx=10, pady=10)

                text_widget = ScrolledText(frame, wrap=tk.WORD, font=('Consolas', 10))
                text_widget.pack(fill='both', expand=True)

                sim_time = PERF_TRACKER.env.now if hasattr(PERF_TRACKER, 'env') else 1.0
                summary = PERF_TRACKER.compute_summary(sim_time)

                summary_text = f"""Enhanced PHN Fat-Tree Performance Summary
{"="*60}

SIMULATION PARAMETERS
Simulation Time: {sim_time:.6f} seconds
Architecture: Enhanced PHN Fat-Tree with Cluster Management
Traffic Pattern: {LOCAL_TRAFFIC_RATIO*100}% local, {CROSS_CLUSTER_RATIO*100}% cross-cluster

OPERATION STATISTICS
Total Operations: {summary['total_operations']}
Completed Operations: {summary['completed_operations']}
Failed Operations: {summary['failed_operations']}
Success Rate: {(summary['completed_operations']/max(summary['total_operations'], 1)*100):.2f}%

CLUSTER LOCALITY ANALYSIS
Local Cluster Operations: {summary['local_cluster_operations']} ({summary['locality_ratio_percent']:.1f}%)
Cross-Cluster Operations: {summary['cross_cluster_operations']} ({summary['cross_cluster_ratio_percent']:.1f}%)
One-Time Use Operations: {summary['one_time_use_operations']}

Target vs Actual Locality:
• Target Local: {LOCAL_TRAFFIC_RATIO*100}% | Actual: {summary['locality_ratio_percent']:.1f}%
• Target Cross: {CROSS_CLUSTER_RATIO*100}% | Actual: {summary['cross_cluster_ratio_percent']:.1f}%

NETWORK PERFORMANCE
Total Messages: {summary['total_messages']}
Average Hop Count: {summary['avg_hop_count']:.3f} hops/packet
Average Latency: {summary['avg_latency_s']*1e6:.3f} μs
Throughput: {summary['throughput_Bps']/1e6:.6f} MB/s

ENHANCED CACHE STATES SUMMARY
• Modified (M): Dirty data requiring writeback
• Shared (S): Clean data with multiple readers
• Invalid (I): No valid data
• Used (U): Cross-cluster read, ONE-TIME use only
• UpdatedOnce (UP): Cross-cluster write, ONE-TIME use only
• PHN Cached (P): Data cached at PHN level"""

                text_widget.insert('1.0', summary_text)
                text_widget.config(state='disabled')

                ttk.Button(summary_window, text="Close",
                          command=summary_window.destroy).pack(pady=5)
            else:
                messagebox.showwarning("No Data", "No PHN performance data available")
        except Exception as e:
            messagebox.showerror("Display Error", f"Error displaying PHN summary: {str(e)}")

    def show_cluster_statistics(self):
        """Show cluster-specific statistics"""
        try:
            cluster_window = tk.Toplevel(self)
            cluster_window.title("Cluster Statistics")
            cluster_window.geometry("600x500")

            frame = ttk.Frame(cluster_window)
            frame.pack(fill='both', expand=True, padx=10, pady=10)

            text_widget = ScrolledText(frame, wrap=tk.WORD, font=('Consolas', 10))
            text_widget.pack(fill='both', expand=True)

            stats_text = f"""PHN Cluster Statistics
{"="*40}

CLUSTER CONFIGURATION:
• G1 Cluster: GPUs 0-3, Addresses 0-9, PHN ID {PHN_G1_ID}
• G2 Cluster: GPUs 4-7, Addresses 10-19, PHN ID {PHN_G2_ID}  
• G3 Cluster: GPUs 8-11, Addresses 20-29, PHN ID {PHN_G3_ID}
• G_prime: GPUs 12-13, Addresses 30-31, Global HN ID {GLOBAL_MEMORY_ID}

PHN CACHE PERFORMANCE:
"""

            # Add PHN-specific statistics
            for i, phn in enumerate(self.network.phn_nodes):
                stats_text += f"""
{phn.cluster_name} PHN Statistics:
• Cache Hits: {phn.cache_hits}
• Cache Misses: {phn.cache_misses}
• Cross-Cluster Requests: {phn.cross_cluster_requests}
• Writebacks Received: {phn.writebacks_received}
• Current Cache Size: {len(phn.phn_cache)}/{PHN_CACHE_SIZE}
"""

            # Add traffic generator statistics if available
            if hasattr(self.traffic_generator, 'get_traffic_statistics'):
                traffic_stats = self.traffic_generator.get_traffic_statistics()
                if traffic_stats:
                    stats_text += f"""
TRAFFIC GENERATION STATISTICS:
• Total Operations: {traffic_stats['total_operations']}
• Local Operations: {traffic_stats['local_operations']} ({traffic_stats['actual_local_percentage']:.1f}%)
• Cross Operations: {traffic_stats['cross_operations']} ({traffic_stats['actual_cross_percentage']:.1f}%)
• Target Accuracy: {'✓ PASS' if traffic_stats['is_within_tolerance'] else '✗ FAIL'}
"""

            text_widget.insert('1.0', stats_text)
            text_widget.config(state='disabled')

            ttk.Button(cluster_window, text="Close",
                      command=cluster_window.destroy).pack(pady=5)

        except Exception as e:
            messagebox.showerror("Display Error", f"Error displaying cluster statistics: {str(e)}")

    def open_cache_window(self):
        """Open enhanced cache window"""
        self.visualizer.create_cache_window()
        self.update_cache_display()

    def queue_command(self, command):
        """Queue command for simulation"""
        self.command_queue.put(command)
        LOGGER.log(f"Queued: {command}")

    def execute_command(self):
        """Execute user command"""
        command = self.command_var.get().strip()
        if command:
            self.queue_command(command)
            self.command_var.set("")

    def toggle_random_traffic(self):
        """Toggle cluster-aware random traffic"""
        self.random_traffic_enabled = self.random_traffic_var.get()
        if self.random_traffic_enabled:
            LOGGER.log("🎯 Cluster-aware smart traffic ENABLED (85%/15% pattern)")
        else:
            LOGGER.log("🛑 Cluster-aware smart traffic DISABLED")

    def generate_random_traffic(self):
        """Generate cluster-aware random traffic"""
        if self.random_traffic_enabled:
            operation, node_id, address, value = self.traffic_generator.generate_cluster_aware_operation()

            if operation == 'read':
                command = f"read {node_id} {address}"
            else:
                command = f"write {node_id} {address} {value}"

            self.queue_command(command)

        self.after(int(RANDOM_TRAFFIC_PERIOD * 1000), self.generate_random_traffic)

    def update_cache_display(self):
        """Update cache display"""
        if hasattr(self.visualizer, 'cache_ax') and self.visualizer.cache_ax:
            self.visualizer.update_cache_display(self.network)
        self.after(2000, self.update_cache_display)

    def update_log_display(self):
        """Update log display with enhanced formatting"""
        messages = LOGGER.get_messages()
        for message in messages:
            self.log_display.insert(tk.END, message + "\n")

            line_start = self.log_display.index(tk.END + "-2c linestart")
            line_end = tk.END + "-1c"

            # Enhanced color coding for PHN features
            if "ERROR" in message or "TIMEOUT" in message or "❌" in message:
                self.log_display.tag_add("error", line_start, line_end)
                self.log_display.tag_config("error", foreground="red", font=("Consolas", 8, "bold"))
            elif "completed" in message or "✅" in message:
                self.log_display.tag_add("success", line_start, line_end)
                self.log_display.tag_config("success", foreground="green", font=("Consolas", 8, "bold"))
            elif "🧪" in message or "Testing" in message or "PHN" in message:
                self.log_display.tag_add("phn", line_start, line_end)
                self.log_display.tag_config("phn", foreground="purple", font=("Consolas", 8, "bold"))
            elif "CROSS-CLUSTER" in message or "[1×]" in message or "ONE-TIME" in message:
                self.log_display.tag_add("cross_cluster", line_start, line_end)
                self.log_display.tag_config("cross_cluster", foreground="orange", font=("Consolas", 8, "bold"))
            elif "G1→" in message or "G2→" in message or "G3→" in message:
                self.log_display.tag_add("cluster", line_start, line_end)
                self.log_display.tag_config("cluster", foreground="blue", font=("Consolas", 8, "bold"))
            elif "🎯" in message or "🛑" in message or "🚀" in message:
                self.log_display.tag_add("highlight", line_start, line_end)
                self.log_display.tag_config("highlight", foreground="darkgreen", font=("Consolas", 8, "bold"))

        if messages:
            self.log_display.see(tk.END)

        self.after(100, self.update_log_display)

    def clear_log(self):
        """Clear log display"""
        self.log_display.delete(1.0, tk.END)

    def close_application(self):
        """Close application with cleanup"""
        self.random_traffic_enabled = False

        try:
            self.command_queue.put('exit')
        except:
            pass

        if hasattr(self.visualizer, 'cache_window') and self.visualizer.cache_window:
            self.visualizer.cache_window.destroy()

        # Print final PHN performance summary
        if PERF_TRACKER:
            sim_time = PERF_TRACKER.env.now if hasattr(PERF_TRACKER, 'env') else 1.0
            summary = PERF_TRACKER.compute_summary(sim_time)

            LOGGER.log("=== FINAL PHN PERFORMANCE SUMMARY ===")
            LOGGER.log(f"Total Operations: {summary['total_operations']}")
            LOGGER.log(f"Local Cluster: {summary['local_cluster_operations']} ({summary['locality_ratio_percent']:.1f}%)")
            LOGGER.log(f"Cross Cluster: {summary['cross_cluster_operations']} ({summary['cross_cluster_ratio_percent']:.1f}%)")
            LOGGER.log(f"One-Time Use: {summary['one_time_use_operations']}")
            LOGGER.log(f"PHN Hit Rate: {summary['phn_hit_rate_percent']:.2f}%")

        self.destroy()

# Main Entry Point
def main():
    try:
        app = EnhancedPHNSimulatorApp()
        app.protocol("WM_DELETE_WINDOW", app.close_application)
        app.mainloop()
    except Exception as e:
        print(f"Startup failed: {e}")
        import traceback
        traceback.print_exc()

if __name__ == "__main__":
    main()
