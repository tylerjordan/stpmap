
import getopt
import csv
import logging
import time
import pprint
import netaddr
import re
import multiprocessing

from jnpr.junos import Device
from jnpr.junos.utils.sw import SW
from jnpr.junos.exception import *
from jnpr.junos.op.lldp import LLDPNeighborTable
from jnpr.junos.op.stpbridge import STPBridgeTable
from jnpr.junos.op.vlan import VlanTable
from jnpr.junos.op.phyport import PhyPortTable
from ncclient.operations.errors import TimeoutExpiredError
from utility import *
from os.path import join
from getpass import getpass
from prettytable import PrettyTable
from sys import stdout
from lxml import etree

# Global Variables
credsCSV = ""
username = ""
password = ""
ssh_port = 22

iplist_dir = ""
log_dir = ""
config_dir = ""
temp_dir = ""
csv_dir = ""
upgrade_dir = ""
images_dir = ""

system_slash = "/"   # This is the linux/mac slash format, windows format will be used in that case

remote_path = "/var/tmp"

dev_list = {
    "SF-A": "132.32.255.206",
    "SF-B": "132.32.255.207",
    "CN1": "132.32.255.201",
    "CN2": "132.32.255.202",
    "CN3": "132.32.255.203",
    "CN4": "132.32.255.204",
    "CN5": "132.32.255.205",
    "CDN-168": "132.32.255.209",
    "CDN-167": "132.32.255.212"
}

env_dict = [
    { "system_name": "CN3", "vlan_id": 281, "local_priority": 33049, "root_bridge": False, "root_port": "ge-0/0/5",
      "root_sys": "CN2", "root_priority": 4377,
      "downstream_ports": [ { "port": "ge-0/0/2", "sys": "CDN-475" }, { "port": "ge-0/0/1", "sys": "CDN-465" } ],
      "edge_ports": [ "ge-0/0/3", "ge-0/0/6" ]
    },
    {"system_name": "CN2", "vlan_id": 281, "local_priority": 4377, "root_bridge": True, "root_port": None,
     "root_sys": None, "root_priority": 4377,
     "downstream_ports": [ { "port": "ge-0/0/5", "sys": "CN3"} ],
     "edge_ports": [ None ]
     },
    {"system_name": "CDN-475", "vlan_id": 281, "local_priority": 33049, "root_bridge": False, "root_port": "ge-0/0/2",
     "root_sys": "CN3", "root_priority": 4377,
     "downstream_ports": [ None ],
     "edge_ports": ["ge-0/0/3"]
     }
]
all_chassis = {}

# Function to determine running environment (Windows/Linux/Mac) and use correct path syntax
def detect_env():
    """ Purpose: Detect OS and create appropriate path variables. """
    global credsCSV
    global iplist_dir
    global config_dir
    global log_dir
    global csv_dir
    global upgrade_dir
    global images_dir
    global temp_dir
    global system_slash
    global ssh_port
    global dir_path
    global username
    global password
    global vlan_json_file
    global stp_json_file
    global lldp_json_file

    dir_path = os.path.dirname(os.path.abspath(__file__))
    if platform.system().lower() == "windows":
        #print "Environment Windows!"
        iplist_dir = ".\\iplists\\"
        config_dir = ".\\configs\\"
        log_dir = ".\\logs\\"
        csv_dir = ".\\csv\\"
        upgrade_dir = ".\\upgrade\\"
        images_dir = ".\\images\\"
        temp_dir = ".\\temp\\"
        system_slash = "\\"
    else:
        #print "Environment Linux/MAC!"
        iplist_dir = "./iplists/"
        config_dir = "./configs/"
        log_dir = "./logs/"
        csv_dir = "./csv/"
        upgrade_dir = "./upgrade/"
        images_dir = "./images/"
        temp_dir = "./temp/"

    credsCSV = os.path.join(dir_path, "pass.csv")
    vlan_json_file = os.path.join(dir_path, "vlan-ext.json")
    stp_json_file = os.path.join(dir_path, "stp.json")
    lldp_json_file = os.path.join(dir_path, "lldp.json")

# Handles arguments provided at the command line
def getargs(argv):
    # Interprets and handles the command line arguments
    try:
        opts, args = getopt.getopt(argv, "hu:", ["user="])
    except getopt.GetoptError:
        print("stpmap.py -u <username>")
        sys.exit(2)
    for opt, arg in opts:
        if opt == '-h':
            print("stpmap.py -u <username>")
            sys.exit()
        elif opt in ("-u", "--user"):
            return arg

# A function to open a connection to devices and capture any exceptions
def connect(ip):
    """ Purpose: Attempt to connect to the device

    :param ip:          -   IP of the device
    :param indbase:     -   Boolean if this device is in the database or not, defaults to False if not specified
    :return dev:        -   Returns the device handle if its successfully opened.
    """
    dev = Device(host=ip, user=username, password=password, auto_probe=True)
    message = ""

    # Try to open a connection to the device
    try:
        dev.open()
    # If there is an error when opening the connection, display error and exit upgrade process
    except ConnectRefusedError as err:
        message = "Host Reachable, but NETCONF not configured."
        return False, message
    except ConnectAuthError as err:
        message = "Unable to connect with credentials. User:" + username
        return False, message
    except ConnectTimeoutError as err:
        message = "Timeout error, possible IP reachability issues."
        return False, message
    except ProbeError as err:
        message = "Probe timeout, possible IP reachability issues."
        return False, message
    except ConnectError as err:
        message = "Unknown connection issue."
        return False, message
    except Exception as err:
        message = "Undefined exception."
        return False, message
    # If try arguments succeeded...
    else:
        return dev

# Create a log
def create_timestamped_log(prefix, extension):
    now = datetime.datetime.now()
    return log_dir + prefix + now.strftime("%Y%m%d-%H%M") + "." + extension

def capture_vlan_info(selected_vlan, vlaninfo):
    vlan_dict = {}
    #print("******* VLAN INFO ******")
    for name in vlaninfo:
        if name.tag == selected_vlan:
            #print("{} | {} | {} | {}".format(name.name, name.tag, name.members, name.l3interface))
            vlan_dict["name"] = name.name
            vlan_dict["tag"] = name.tag
            vlan_dict["members"] = name.members
            vlan_dict["l3interface"] = name.l3interface
    return vlan_dict

# This function assumes capturing "show vlan extensive | display json" output
def capture_json_vlan_info(selected_vlan, raw_dict):
    vlan_dict = {}
    vlan_found = False
    for l1 in raw_dict["l2ng-l2ald-vlan-instance-information"]:
        for l2 in l1["l2ng-l2ald-vlan-instance-group"]:
            if l2["l2ng-l2rtb-vlan-tag"]:
                for vtag in l2["l2ng-l2rtb-vlan-tag"]:
                    if vtag["data"] == selected_vlan:
                        vlan_dict["tag"] = vtag["data"]
                        print("Found vlan {}".format(vtag["data"]))
                        vlan_found = True
                        break
            if vlan_found:
                intf_list = []
                for vname in l2["l2ng-l2rtb-vlan-name"]:
                    vlan_dict["name"] = vname["data"]
                    break
                for l3 in l2["l2ng-l2rtb-vlan-member"]:
                    for vmember in l3["l2ng-l2rtb-vlan-member-interface"]:
                        intf_list.append(vmember["data"])
                        break
                vlan_dict["members"] = intf_list
                for l3interface in l2["l2ng-l2rtb-vlan-l3-interface"]:
                    vlan_dict["l3interface"] = l3interface["data"]
                    break
                break
        # If the vlan has been found, break out of the top level loop
        if vlan_found:
            break
    return(vlan_dict)

# Collects all VLANs from the provided VLAN output
def collect_vlan_list(raw_dict):
    vlan_list = []
    for l1 in raw_dict["l2ng-l2ald-vlan-instance-information"]:
        for l2 in l1["l2ng-l2ald-vlan-instance-group"]:
            if l2["l2ng-l2rtb-vlan-tag"]:
                for vtag in l2["l2ng-l2rtb-vlan-tag"]:
                    if vtag["data"]:
                        vlan_list.append(vtag["data"])
                        break
    return vlan_list

def capture_span_info(selected_vlan, stpbridge):
    stp_dict = {}
    #print("\n******* STP BRIDGE INFO ******")
    for vlan_id in stpbridge:
        if vlan_id.vlan_id == selected_vlan:
            #print("{} | {}({}) | {}({}) | {}".format(vlan_id.vlan_id, vlan_id.root_bridge_mac,
            #                                         vlan_id.root_bridge_priority, vlan_id.local_bridge_mac,
            #                                         vlan_id.local_bridge_priority, vlan_id.root_port))
            stp_dict["vlan_id"] = vlan_id.vlan_id
            stp_dict["vlan_rb_mac"] = vlan_id.root_bridge_mac
            stp_dict["vlan_rb_prio"] = vlan_id.root_bridge_priority
            stp_dict["vlan_local_mac"] = vlan_id.local_bridge_mac
            stp_dict["vlan_local_prio"] = vlan_id.local_bridge_priority
            stp_dict["vlan_root_port"] = vlan_id.root_port
            stp_dict["vlan_root_cost"] = vlan_id.root_cost
            stp_dict["topo_change_count"] = vlan_id.topo_change_count
            stp_dict["time_since_last_tc"] = vlan_id.time_since_last_tc
    return stp_dict

# This function assumes capturing "show spanning-tree bridge | display json" output
def capture_json_stp_info(selected_vlan, raw_dict):
    stp_dict = {}
    stp_found = False
    for l1 in raw_dict["stp-bridge"]:
        for l2 in l1["vst-bridge-parameters"]:
            for vlan_id in l2["vlan-id"]:
                if vlan_id["data"] == selected_vlan:
                    stp_dict["vlan_id"] = vlan_id["data"]
                    stp_found = True
                    break
            if stp_found:
                for rb_info in l2["root-bridge"]:
                    for rb_mac in rb_info["bridge-mac"]:
                        stp_dict["vlan_rb_mac"] = rb_mac["data"]
                    for rb_prio in rb_info["bridge-priority"]:
                        stp_dict["vlan_rb_prio"] = rb_prio["data"]
                for local_info in l2["this-bridge"]:
                    for local_mac in local_info["bridge-mac"]:
                        stp_dict["vlan_local_mac"] = local_mac["data"]
                    for local_prio in local_info["bridge-priority"]:
                        stp_dict["vlan_local_prio"] = local_prio["data"]
                for root_port in l2["root-port"]:
                    stp_dict["vlan_root_port"] = root_port["data"]
                for root_cost in l2["root-cost"]:
                    stp_dict["vlan_root_cost"] = root_cost["data"]
                for topo_change_count in l2["topology-change-count"]:
                    stp_dict["topo_change_count"] = topo_change_count["data"]
                for time_since_last_tc in l2["time-since-last-tc"]:
                    stp_dict["time_since_last_tc"] = time_since_last_tc["data"]
                break
        if stp_found:
            break
    return(stp_dict)

def capture_lldp_info(lldpneigh, members):
    lldp_ld = []
    #print("\n******* LLDP NEIGHBORS ******")
    for li in lldpneigh:
        # If the members are a list
        if type(members) == list:
            for item in members:
                lldp_dict = {}
                if li.local_parent != "-" and li.local_parent == item.split(".")[0]:
                    #print("{}: {}: {}".format(li.local_parent, li.remote_chassis_id,
                    #                          li.remote_sysname))
                    lldp_dict["local_int"] = li.local_parent
                    lldp_dict["remote_chassis_id"] = li.remote_chassis_id
                    lldp_dict["remote_sysname"] = li.remote_sysname
                    lldp_ld.append(lldp_dict)
                elif li.local_int == item.split(".")[0]:
                    #print("{}: {}: {}".format(li.local_int, li.remote_chassis_id,
                    #                          li.remote_sysname))
                    lldp_dict["local_int"] = li.local_int
                    lldp_dict["remote_chassis_id"] = li.remote_chassis_id
                    lldp_dict["remote_sysname"] = li.remote_sysname
                    lldp_ld.append(lldp_dict)
        # If the members is a string
        elif members:
            lldp_dict = {}
            if li.local_parent != "-" and li.local_parent == members.split(".")[0]:
                #print("{}: {}: {}".format(li.local_parent, li.remote_chassis_id,
                 #                         li.remote_sysname))
                lldp_dict["local_int"] = li.local_parent
                lldp_dict["remote_chassis_id"] = li.remote_chassis_id
                lldp_dict["remote_sysname"] = li.remote_sysname
                lldp_ld.append(lldp_dict)
            elif li.local_int == members.split(".")[0]:
                #print("{}: {}: {}".format(li.local_int, li.remote_chassis_id,
                 #                         li.remote_sysname))
                lldp_dict["local_int"] = li.local_int
                lldp_dict["remote_chassis_id"] = li.remote_chassis_id
                lldp_dict["remote_sysname"] = li.remote_sysname
                lldp_ld.append(lldp_dict)
    # Return LLDP
    #print("LLDP_LD")
    #print(lldp_ld)
    return(lldp_ld)

# This function assumes capturing "show spanning-tree bridge | display json" output
def capture_json_lldp_info(selected_vlan, raw_dict, members):
    lldp_ld = []
    lldp_found = False
    for l1 in raw_dict["lldp-neighbors-information"]:
        lldp_dict = {}
        for l2 in l1["lldp-neighbor-information"]:
            for local_port in l2["lldp-local-port-id"]:
                for member in members:
                    #print("Member: {}".format(member))
                    #print("Local Port: {}".format(local_port["data"]))
                    if local_port["data"] == member.split(".")[0]:
                        lldp_dict["local_int"] = local_port["data"]
                        lldp_found = True
                        break
            if lldp_found:
                for remote_chassis_id in l2["lldp-remote-chassis-id"]:
                    lldp_dict["remote_chassis_id"] = remote_chassis_id["data"]
                for remote_sysname in l2["lldp-remote-system-name"]:
                    lldp_dict["remote_sysname"] = remote_sysname["data"]
                lldp_ld.append(lldp_dict)
                lldp_found = False
    return(lldp_ld)

def get_non_lldp_intf(lldp_dict, vlan_dict, root_port):
    non_lldp_intf = []
    # Check if the list consists of only one vlan interface
    if vlan_dict["members"] != None:
        if type(vlan_dict["members"]) != list:
            non_lldp_dict = {}
            # If this vlan interface doesn't exist in the LLDP list, it's either a (non-LLDP) trunk or endpoint
            if not any(d["local_int"] == vlan_dict["members"].split(".")[0] for d in lldp_dict):
                non_lldp_dict["intf"] = vlan_dict["members"].split("*")[0]
                if "*" in vlan_dict["members"]:
                    non_lldp_dict["active"] = True
                else:
                    non_lldp_dict["active"] = False
                non_lldp_intf.append(non_lldp_dict)
        # If there are multiple vlan interfaces to check...
        else:
            # Check all the vlan interfaces
            for vlan_int in vlan_dict["members"]:
                non_lldp_dict = {}
                # If this vlan interface doesn't exist in the LLDP list, it's either a (non-LLDP) trunk or endpoint
                if not any(d["local_int"] == vlan_int.split(".")[0] for d in lldp_dict):
                    non_lldp_dict["intf"] = vlan_int.split("*")[0]
                    if "*" in vlan_int:
                        non_lldp_dict["active"] = True
                    else:
                        non_lldp_dict["active"] = False
                    non_lldp_intf.append(non_lldp_dict)
    return non_lldp_intf

def get_upstream_host(lldp_dict, root_port):
    upstream_peer = {}
    for one_int in lldp_dict:
        if one_int["local_int"] == root_port:
            #print("Upstream Int: {} Root Port: {} Sysname: {}".format(one_int["local_int"], root_port, one_int["remote_sysname"]))
            upstream_peer["name"] = one_int["remote_sysname"]
            upstream_peer["intf"] = one_int["local_int"]
    #print("Upstream Peer")
    #print(upstream_peer)
    return upstream_peer

def get_downstream_hosts(lldp_dict, root_port):
    downstream_raw = []
    downstream_list = []
    #print("Root Port: {}".format(root_port))
    # Create list of downstream hosts
    for one_int in lldp_dict:
        host_int_dict = {}
        if one_int["local_int"] != root_port:
            #print("Local Int: {} Sysname: {}".format(one_int["local_int"], one_int["remote_sysname"]))
            host_int_dict["name"] = one_int["remote_sysname"]
            host_int_dict["intf"] = one_int["local_int"]
            #print("Host Int Dict: {}".format(host_int_dict))
            downstream_raw.append(host_int_dict)
            #print("Downstream Raw: {}".format(downstream_raw))
    # Remove duplicates
    #print("List")
    #print(downstream_raw)
    for i in downstream_raw:
        if i not in downstream_list:
            downstream_list.append(i)
    return downstream_list

def capture_chassis_info(selected_vlan, host, using_network):
    chassis_dict = {}
    vlan_dict = {}
    stp_dict = {}
    lldp_dict = {}

    ip = dev_list[host]
    chassis_dict["hostname"] = host
    chassis_dict["ip"] = ip

    if using_network:
        stdout.write("-> Connecting to " + ip + " ... \n")
        with Device(host=ip, user=username, password=password) as jdev:
            print(starHeading(host, 5))
            # Raw collected information
            # VLAN Info (show vlans)
            vlaninfo = VlanTable(jdev)
            vlaninfo.get(extensive=True)
            vlan_dict = capture_vlan_info(selected_vlan, vlaninfo)
            #print("VLAN DICT")
            #print(vlan_dict)
            # STP Info (show spanning-tree bridge)
            stpbridge = STPBridgeTable(jdev)
            stpbridge.get()
            stp_dict = capture_span_info(selected_vlan, stpbridge)
            #print("STP DICT")
            #print(stp_dict)
            # Check if vlan_dict and stp_dict are populated
            if vlan_dict:
                # LLDP Info (show lldp neighbors)
                lldpneigh = LLDPNeighborTable(jdev)
                lldpneigh.get()
                lldp_dict = capture_lldp_info(lldpneigh, vlan_dict["members"])
            # If no vlan or stp information exists, provide an empty dict
            else:
                lldp_dict = {}
            #print("LLDP DICT")
            #print(lldp_dict)
            # Phy Info (show
    else:
        # Pull VLAN info from JSON file
        vlan_json_file = os.path.join(dir_path, (host + "_vlan-ext.json"))
        raw_dict = json_to_dict(vlan_json_file)
        vlan_dict = capture_json_vlan_info(selected_vlan, raw_dict)
        print("VLAN DICT")
        print(vlan_dict)

        # Pull STP info from JSON file
        stp_json_file = os.path.join(dir_path, (host + "_stp.json"))
        stp_dict = capture_json_stp_info(selected_vlan, json_to_dict(stp_json_file))
        print("STP DICT")
        print(stp_dict)

        # Pull LLDP info from JSON file
        lldp_json_file = os.path.join(dir_path, (host + "_lldp.json"))
        lldp_dict = capture_json_lldp_info(selected_vlan, json_to_dict(lldp_json_file), vlan_dict["members"])
        print("LLDP DICT")
        print(lldp_dict)

    # Computed variables
    chassis_dict["vlan"] = vlan_dict
    chassis_dict["stp"] = stp_dict
    chassis_dict["lldp"] = lldp_dict
    # Check if vlan dict exists
    if vlan_dict:
        # Check if the mac of the RB and local mac is the same, to check if this is the RB
        if stp_dict["vlan_rb_mac"] == stp_dict["vlan_local_mac"]:
            chassis_dict["root_bridge"] = True
        else:
            chassis_dict["root_bridge"] = False
        chassis_dict["upstream_peer"] = get_upstream_host(lldp_dict, stp_dict["vlan_root_port"])
        chassis_dict["downstream_peers"] = get_downstream_hosts(lldp_dict, stp_dict["vlan_root_port"])
        chassis_dict["non-lldp-intf"] = get_non_lldp_intf(lldp_dict, vlan_dict, stp_dict["vlan_root_port"])

    return(chassis_dict)

def create_stp_paths():
    path_list = []
    rb_key = "root_bridge"
    host_count = 1
    #print("All Chassis")
    #print(all_chassis)

def create_stp_stats():
    rb_key = "root_bridge"
    myTable = PrettyTable(["Host", "# of Topo Changes", "Time Since Last Change", "Root Cost"])

    for host in all_chassis["chassis"]:
        host_content = []
        if rb_key in host.keys():
            if host["root_bridge"]:
                adj_name = host["name"] + " (RB)"
            elif host["name"] == all_chassis["backup_root_bridge"]:
                adj_name = host["name"] + " (BRB)"
            else:
                adj_name = host["name"]
            host_content.append(adj_name)
            # Populate Topology Change Count Cell
            host_content.append(host["topo_change_count"])
            # Populate Seconds Since Change Cell (convert to hours:mintues:seconds)
            host_content.append(time.strftime("%H:%M:%S", time.gmtime(int(host["time_since_last_tc"]))))
            # Populate Root Cost Cell
            host_content.append(host["root_cost"])
            # Populate Hops from Root

            myTable.add_row(host_content)
        else:
            adj_name = host["name"] + " (NV)"
            host_content = [adj_name, "-", "-", "-", "-"]
            myTable.add_row(host_content)
    #print(myTable)
def create_chart():
    key = "upstream_peer"
    rb_key = "root_bridge"
    # Specify the Column Names while initializing the Table
    # Specify the Column Names while initializing the Table
    print("VLAN Name: {}".format(all_chassis["vlan_name"]))
    print("VLAN Tag: {}".format(all_chassis["vlan_id"]))

    myTable = PrettyTable(["Host", "Bridge Priority", "IRB Intf", "Upstream Intf", "Upstream Host", "Non-LLDP-Intfs",
                           "Downstream Intfs", "Downstream Hosts"])
    for host in all_chassis["chassis"]:
        host_content = []
        # Populate Host Cell
        if rb_key in host.keys():
            if host["root_bridge"]:
                adj_name = host["name"] + " (RB)"
            elif host["name"] == all_chassis["backup_root_bridge"]:
                adj_name = host["name"] + " (BRB)"
            else:
                adj_name = host["name"]
            host_content.append(adj_name)
            # Populate Bridge Priority Cell
            host_content.append(host["local_priority"])
            # Populate IRB Interface Cell
            if host["l3_interface"] == None:
                host_content.append("-")
            else:
                host_content.append(host["l3_interface"])
            # Check upstream exists, then populate Upstream Interface and Host or "-" if doesn't exist
            if key in host.keys():
                host_content.append(host["upstream_intf"])
                host_content.append(host["upstream_peer"])
            else:
                host_content.append("-")
                host_content.append("-")
            # Get number of non-LLDP interfaces
            lldp_length = 0
            lldp_active = 0
            if not host["non_lldp_intf"]:
                host_content.append(lldp_length)
            else:
                lldp_length = len(host["non_lldp_intf"])
                for non_lldp_int in host["non_lldp_intf"]:
                    if non_lldp_int["active"]:
                        lldp_active += 1
            if lldp_length:
                dis = str(lldp_length) + "(" + str(lldp_active) + ")"
                host_content.append(dis)
            # Populate Downstream Interfaces Cells
            first_intf = True
            if not host["downstream_peers"]:
                host_content.append("-")
                host_content.append("-")
                myTable.add_row(host_content)
            else:
                for down_peer in host["downstream_peers"]:
                    if first_intf:
                        first_intf = False
                    else:
                        host_content = ["-", "-", "-", "-", "-", "-"]
                    host_content.append(down_peer["intf"])
                    host_content.append(down_peer["name"])
                    myTable.add_row(host_content)
        # Host the deosn't have VLAN
        else:
            adj_name = host["name"] + " (NV)"
            host_content = [adj_name, "-", "-", "-", "-", "-", "-", "-"]
            myTable.add_row(host_content)
    #print(myTable)

def stp_map_files():
    print("*" * 50 + "\n" + " " * 10 + "STP MAP using Network\n" + "*" * 50)
    # Provide selection for sending a single command or multiple commands from a file
    selected_vlan = "4001"
    hosts = []
    hosts_list = []
    # Capture the available devices
    for a_host in dev_list.keys():
        hosts_list.append(a_host)
    # Select a host to start with
    host = getOptionAnswer("Select a starting Host", hosts_list)

    # Capture the available VLANs on the host selected
    vlan_json_file = os.path.join(dir_path, (host + "_vlan-ext.json"))
    raw_dict = json_to_dict(vlan_json_file)
    vlan_list = collect_vlan_list(raw_dict)

    # Select a VLAN from the host list
    selected_vlan = getOptionAnswer("Select a VLAN to analyze", vlan_list)

    # Add selected host the list
    hosts.append(host)

    all_chassis = scan_loop(selected_vlan, hosts, using_network=False)

    print("ALL CHASSIS")
    print(all_chassis)

def scan_loop(selected_vlan, hosts, using_network):
    # Loop over hosts list
    root_bridge_found = False
    all_chassis["chassis"] = []

    # Loop over hosts
    for host in hosts:
        chassis_dict = capture_chassis_info(selected_vlan, host, using_network)

        # Check if this device is the root bridge
        if chassis_dict["vlan"]:
            if chassis_dict["root_bridge"]:
                root_bridge_found = True
                # Search the LLDP dict for the dict with the root port
                print("-> {} is the root bridge of VLAN {}({})".format(host, chassis_dict["vlan"]["name"],
                                                                       chassis_dict["vlan"]["tag"]))
                # Generic variables
                all_chassis["root_bridge"] = host
                all_chassis["vlan_name"] = chassis_dict["vlan"]["name"]
                all_chassis["vlan_id"] = chassis_dict["vlan"]["tag"]

                # Chassis variables
                my_dict = {}
                my_dict["name"] = host
                my_dict["root_bridge"] = True
                my_dict["local_priority"] = chassis_dict["stp"]["vlan_local_prio"]
                my_dict["root_priority"] = chassis_dict["stp"]["vlan_rb_prio"]
                my_dict["topo_change_count"] = chassis_dict["stp"]["topo_change_count"]
                my_dict["time_since_last_tc"] = chassis_dict["stp"]["time_since_last_tc"]
                my_dict["root_cost"] = "-"
                my_dict["downstream_peers"] = chassis_dict["downstream_peers"]
                my_dict["non_lldp_intf"] = chassis_dict["non-lldp-intf"]
                my_dict["l3_interface"] = chassis_dict["vlan"]["l3interface"]

                if chassis_dict["downstream_peers"]:
                    for peer in chassis_dict["downstream_peers"]:
                        hosts.append(peer["name"])
                        print("-> Added {} to scan list".format(peer["name"]))

                # Add this chassis to the list
                all_chassis["chassis"].append(my_dict)
            # This device is not the root bridge
            else:
                # Check if the root bridge has already been found
                if root_bridge_found:
                    # Chassis variables
                    my_dict = {}
                    my_dict["name"] = host
                    my_dict["root_bridge"] = False
                    my_dict["local_priority"] = chassis_dict["stp"]["vlan_local_prio"]
                    # print("Local: {} | Backup: {}".format(my_dict["local_priority"], backup_rb["priority"]))
                    if int(my_dict["local_priority"]) < backup_rb["priority"]:
                        backup_rb["name"] = my_dict["name"]
                        backup_rb["priority"] = int(my_dict["local_priority"])
                    my_dict["topo_change_count"] = chassis_dict["stp"]["topo_change_count"]
                    my_dict["time_since_last_tc"] = chassis_dict["stp"]["time_since_last_tc"]
                    my_dict["upstream_peer"] = chassis_dict["upstream_peer"]["name"]
                    my_dict["upstream_intf"] = chassis_dict["upstream_peer"]["intf"]
                    my_dict["downstream_peers"] = chassis_dict["downstream_peers"]
                    my_dict["non_lldp_intf"] = chassis_dict["non-lldp-intf"]
                    my_dict["l3_interface"] = chassis_dict["vlan"]["l3interface"]
                    my_dict["root_cost"] = chassis_dict["stp"]["vlan_root_cost"]
                    # Add downstream interfaces
                    if chassis_dict["downstream_peers"]:
                        for peer in chassis_dict["downstream_peers"]:
                            hosts.append(peer["name"])
                            print("-> Added {} to scan list".format(peer["name"]))
                    # Add this chassis to the list
                    all_chassis["chassis"].append(my_dict)
                    # print("ALL CHASSIS")
                    # print(all_chassis)
                # If the root bridge hasn't been found, check the upstream device
                else:
                    print("-> {} is NOT the root bridge for VLAN({})".format(host, chassis_dict["vlan"]["name"],
                                                                             chassis_dict["vlan"]["tag"]))
                    # Append the upstream device name for the next device to check
                    hosts.append(chassis_dict["upstream_peer"]["name"])
            # Add the backup root bridge name to the large dict
            all_chassis["backup_root_bridge"] = backup_rb["name"]
        # This chassis doesn't have the chosen VLAN
        else:
            my_dict = {}
            my_dict["name"] = host
            my_dict["no_vlan"] = True
            all_chassis["chassis"].append(my_dict)
    return(all_chassis)

# Function for running operational commands to multiple devices
def stp_map_net(my_ips):
    print("*" * 50 + "\n" + " " * 10 + "STP MAP using Network\n" + "*" * 50)
    # Provide selection for sending a single command or multiple commands from a file
    selected_vlan = "None"
    hosts = []

    if not my_ips:
        my_ips = chooseDevices(iplist_dir)
    if my_ips:
        # Loop over commands and devices
        backup_rb = { "name": "None", "priority": 64000 }
        try:
            for ip in my_ips:
                stdout.write("-> Connecting to " + ip + " ... ")
                with Device(host=ip, user=username, password=password) as jdev:
                    vlan_list = []
                    vlaninfo = VlanTable(jdev)
                    vlaninfo.get()
                    for name in vlaninfo:
                        vlan_list.append(name.tag)
                    selected_vlan = getOptionAnswer("Choose a VLAN", vlan_list)
                    hosts.append(host_from_ip(dev_list, ip))
        except KeyboardInterrupt:
            print("Exiting Procedure...")

        all_chassis = scan_loop(selected_vlan, hosts, using_network=True)

        print("ALL CHASSIS")
        print(all_chassis)
        # Print the table
        #create_chart()
        #create_stp_stats()
        #create_stp_paths()
        exit()
    else:
        print("\n!! Configuration deployment aborted... No IPs defined !!!\n")

# Main execution loop
if __name__ == "__main__":
    # Detect the platform type
    detect_env()

    # Get a username and password from the user
    username = getargs(sys.argv[1:])
    if not username:
        print('Please supply a username as an argument: jshow.py -u <username>')
        exit()
    password = getpass(prompt="\nEnter your password: ")

    # Define menu options
    my_options = ['Scan Vlans (Files)', 'Scan Vlans (Network)', 'Quit']
    my_ips = []

    # Get menu selection
    while True:
        stdout.write("\n\n")
        print("*" * 50 + "\n" + " " * 10 + "JSHOW: MAIN MENU\n" + "*" * 50)
        answer = getOptionAnswerIndex('Make a Selection', my_options)
        if answer == "1":
            stp_map_files()
        elif answer == "2":
            stp_map_net(my_ips)
        elif answer == "3":
            quit()
