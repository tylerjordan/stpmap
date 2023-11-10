# STPMAP.PY
# The network-based functions pull information from the actual chassis. It uses an RPC that pulls data formatted by a
# YAML table/view:
# The YAML table/views are located under ../python3.11/site-packages/jnpr/junos/op
# The default YAML table/views may need to be modified so that the correct information can be pulled.
#
# List of table/views Needed:
# - vlan.yml
# - stpbridge.yml
# - lldp.yml
#
# Please find the included YAML files, they will need to be added to the path indicated for the network-based functions
# to work correctly.
#
# The file-based functions use the data pulled from "show" commands using the " | display json | no-more" option to
# correctly format the output. The files will likely need to be cleaned up. The output is in the form of .json files.
# Ensure that the files are UTF-8. Any other formats may cause problems, including UTF-8 with BOM encoding.
#
# List of commands used:
# - show vlan extensive | display json | no-more
# - show spanning-tree bridge | display json | no-more
# - show lldp neighbors | display json | no-more
#
# File Format:
# The format of the file name is important. The Chassis Hostname must be the :
# For LLDP file: <Chassis Hostname>_lldp.json
# For Spanning Tree file: <Chassis Hostname>_stp.json
# For VLAN file: <Chassis Hostname>_vlan-ext.json


import getopt
import sys
import csv
import logging
import time
from pprint import pprint
from operator import itemgetter

import netaddr
import re
import multiprocessing

from jnpr.junos import Device
from jnpr.junos.utils.sw import SW
from jnpr.junos.exception import *
from jnpr.junos.op.lldp import LLDPNeighborTable
from jnpr.junos.op.stpbridge import STPBridgeTable
from jnpr.junos.op.vlan import VlanTable
from jnpr.junos.op.elsethernetswitchingtable import ElsEthernetSwitchingTable
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

system_slash = "/"  # This is the linux/mac slash format, windows format will be used in that case

remote_path = "/var/tmp"

dev_list = {}
# Dictionary to hold chassis information
all_chassis = {}


# Function to determine running environment (Windows/Linux/Mac) and use correct path syntax
def detect_env():
    """ Purpose: Detect OS and create appropriate path variables. """
    global credsCSV
    global dev_list_file
    global iplist_dir
    global config_dir
    global log_dir
    global csv_dir
    global upgrade_dir
    global images_dir
    global temp_dir
    global json_dir
    global system_slash
    global ssh_port
    global dir_path
    global username
    global password
    global table_file
    global stp_chart
    global stp_stats
    global mac_scan_results

    dir_path = os.path.dirname(os.path.abspath(__file__))
    if platform.system().lower() == "windows":
        # print "Environment Windows!"
        config_dir = ".\\configs\\"
        log_dir = ".\\logs\\"
        csv_dir = ".\\csv\\"
        upgrade_dir = ".\\upgrade\\"
        images_dir = ".\\images\\"
        temp_dir = ".\\temp\\"
        json_dir = ".\\json\\"
        system_slash = "\\"

    else:
        # print "Environment Linux/MAC!"
        config_dir = "./configs/"
        log_dir = "./logs/"
        csv_dir = "./csv/"
        upgrade_dir = "./upgrade/"
        images_dir = "./images/"
        temp_dir = "./temp/"
        json_dir = "./json/"

    credsCSV = os.path.join(dir_path, "pass.csv")
    dev_list_file = os.path.join(dir_path, "dev_list.json")
    table_file = os.path.join(dir_path, "table_file.txt")
    stp_chart = os.path.join(dir_path, "stp_chart.txt")
    stp_stats = os.path.join(dir_path, "stp_stats.txt")
    mac_scan_results = os.path.join(dir_path, "mac_scan_results.txt")

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

# VLAN info captured via network
def extract_vlan_info(vlaninfo, selected_vlan='all'):
    vlan_ld = []
    # print("******* VLAN INFO ******")
    vlan_found = False
    for name in vlaninfo:
        vlan_dict = {}
        if selected_vlan == 'all' or name.tag == selected_vlan:
            # print("{} | {} | {} | {}".format(name.name, name.tag, name.members, name.l3interface))
            vlan_dict["name"] = name.name
            vlan_dict["tag"] = name.tag
            vlan_dict["state"] = name.state
            if name.members == None:
                vlan_dict["members"] = []
            else:
                vlan_dict["members"] = name.members
            if name.l3interface == None:
                vlan_dict["l3interface"] = ""
            else:
                vlan_dict["l3interface"] = name.l3interface
            vlan_found = True
        if selected_vlan != 'all' and vlan_found:
            return vlan_dict
        elif selected_vlan == 'all':
            vlan_ld.append(vlan_dict)
    return vlan_ld

# This function assumes capturing "show vlan extensive | display json" output
# vlan_dict {'tag': '','name': '','members': [], 'l3-interface': ''}
def extract_json_vlan_info(raw_dict, selected_vlan='all'):
    vlan_ld = []
    vlan_found = False
    for l1 in raw_dict["l2ng-l2ald-vlan-instance-information"]:
        for l2 in l1["l2ng-l2ald-vlan-instance-group"]:
            vlan_dict = {}
            if l2["l2ng-l2rtb-vlan-tag"]:
                for vtag in l2["l2ng-l2rtb-vlan-tag"]:
                    if selected_vlan == vtag["data"]:
                        vlan_dict["tag"] = vtag["data"]
                        #print("Found vlan {}".format(vtag["data"]))
                        vlan_found = True
                    elif selected_vlan == 'all':
                        vlan_dict["tag"] = vtag["data"]
                        vlan_found = True
                if vlan_found:
                    intf_list = []
                    for vname in l2["l2ng-l2rtb-vlan-name"]:
                        vlan_dict["name"] = vname["data"]
                        break
                    if "l2ng-l2rtb-vlan-member" in l2:
                        for l3 in l2["l2ng-l2rtb-vlan-member"]:
                            for vmember in l3["l2ng-l2rtb-vlan-member-interface"]:
                                intf_list.append(vmember["data"])
                                break
                    vlan_dict["members"] = intf_list
                    if "l2ng-l2rtb-vlan-l3-interface" in l2:
                        for l3interface in l2["l2ng-l2rtb-vlan-l3-interface"]:
                            vlan_dict["l3interface"] = l3interface["data"]
                            break
                    else:
                        vlan_dict["l3interface"] = ""
                if selected_vlan != 'all' and vlan_found:
                    return vlan_dict
                elif vlan_dict:
                    vlan_ld.append(vlan_dict)
                    vlan_found = False
    return vlan_ld

# Collects all VLANs from the provided VLAN output
def collect_vlan_list_json(raw_dict):
    vlan_list = []
    for l1 in raw_dict["l2ng-l2ald-vlan-instance-information"]:
        for l2 in l1["l2ng-l2ald-vlan-instance-group"]:
            if l2["l2ng-l2rtb-vlan-tag"]:
                for vtag in l2["l2ng-l2rtb-vlan-tag"]:
                    if vtag["data"]:
                        vlan_list.append(vtag["data"])
                        break
    return vlan_list

def extract_span_info(stpbridge, selected_vlan='all'):
    stp_ld = []
    # print("\n******* STP BRIDGE INFO ******")
    stp_found = False
    for vlan_id in stpbridge:
        stp_dict = {}
        if selected_vlan == 'all' or vlan_id.vlan_id == selected_vlan:
            stp_dict["vlan_id"] = vlan_id.vlan_id
            stp_dict["vlan_rb_mac"] = vlan_id.root_bridge_mac
            stp_dict["vlan_rb_prio"] = vlan_id.root_bridge_priority
            stp_dict["vlan_local_mac"] = vlan_id.local_bridge_mac
            stp_dict["vlan_local_prio"] = vlan_id.local_bridge_priority
            stp_dict["vlan_root_port"] = vlan_id.root_port
            stp_dict["vlan_root_cost"] = vlan_id.root_cost
            stp_dict["topo_change_count"] = vlan_id.topo_change_count
            stp_dict["time_since_last_tc"] = vlan_id.time_since_last_tc
            stp_found = True
        if selected_vlan != 'all' and stp_found:
            return stp_dict
        elif selected_vlan == 'all':
            stp_ld.append(stp_dict)

    return stp_ld

def extract_json_stp_int(raw_dict, selected_vlan='all'):
    stp_int_ld = []
    match_vlan = False
    if selected_vlan == 'all':
        one_vlan = False
    else:
        one_vlan = True
    for l1 in raw_dict["stp-interface-information"]:
        # Loop over VLANs
        for l2 in l1["stp-instance"]:
            # Check if the "vlan-id" key exists
            if "vlan-id" in l2.keys():
                # Create dict for this vlan
                for vlan_id in l2["vlan-id"]:
                    #print("VLAN ID: {}".format(vlan_id["data"]))
                    vlan_stp_dict = {}
                    if one_vlan:
                        if vlan_id["data"] == selected_vlan:
                            vlan_stp_dict["vlan_id"] = vlan_id["data"]
                            match_vlan = True
                    else:
                        vlan_stp_dict["vlan_id"] = vlan_id["data"]
                        match_vlan = True
                    # Check if the correct vlan was matched
                    if match_vlan:
                        # Loop over the interfaces for this specific VLAN
                        for stp_ints in l2["stp-interfaces"]:
                            vlan_stp_dict["interfaces"] = []
                            for stp_int in stp_ints["stp-interface-entry"]:
                                # Create a separate dict for each interface
                                stp_intf_dict = {}
                                for int_name in stp_int["interface-name"]:
                                    stp_intf_dict["int_name"] = int_name["data"]
                                    #print("Interface Name: {}".format(stp_intf_dict["int_name"]))
                                    break
                                for port_cost in stp_int["port-cost"]:
                                    stp_intf_dict["port_cost"] = port_cost["data"]
                                    break
                                for port_state in stp_int["port-state"]:
                                    stp_intf_dict["port_state"] = port_state["data"]
                                    break
                                for desg_bridge_mac in stp_int["designated-bridge-mac"]:
                                    stp_intf_dict["desg_bridge_mac"] = desg_bridge_mac["data"]
                                    break
                                for desg_bridge_prio in stp_int["designated-bridge-priority"]:
                                    stp_intf_dict["desg_bridge_prio"] = desg_bridge_prio["data"]
                                    break
                                for port_role in stp_int["port-role"]:
                                    stp_intf_dict["port_role"] = port_role["data"]
                                    break
                                # Add interface to vlan interface list
                                vlan_stp_dict["interfaces"].append(stp_intf_dict)
                        # Append this to the larger LD or return the dictionary
                        if selected_vlan != 'all' and one_vlan:
                            return vlan_stp_dict
                        elif vlan_stp_dict:
                            stp_int_ld.append(vlan_stp_dict)
                            match_vlan = False
                    break
            else:
                pass
                #print("Skipping RSTP instance...")
    return stp_int_ld
# This function assumes capturing "show spanning-tree bridge | display json" output
# stp_dict {'vlan-id': '', 'vlan_rb_mac': '', 'vlan_rb_prio': '', 'vlan_local_mac': '', 'vlan_local_prio': '',
#           'topology_change_count': '', 'time_since_last_tc': '', 'vlan_root_port': '', 'vlan_root_cost': ''}
# Returns LD if selected_vlan is "all"
# Returns Dict if selected_vlan is set
def extract_json_stp_info(raw_dict, selected_vlan='all'):
    stp_ld = []
    match_vlan = False
    if selected_vlan == 'all':
        one_vlan = False
    else:
        one_vlan = True
    for l1 in raw_dict["stp-bridge"]:
        for l2 in l1["vst-bridge-parameters"]:
            stp_dict = {}
            for vlan_id in l2["vlan-id"]:
                if one_vlan:
                    if vlan_id["data"] == selected_vlan:
                        stp_dict["vlan_id"] = vlan_id["data"]
                        match_vlan = True
                else:
                    stp_dict["vlan_id"] = vlan_id["data"]
                    match_vlan = True
                if match_vlan:
                    for rb_info in l2["root-bridge"]:
                        for rb_mac in rb_info["bridge-mac"]:
                            stp_dict["vlan_rb_mac"] = rb_mac["data"]
                            break
                        for rb_prio in rb_info["bridge-priority"]:
                            stp_dict["vlan_rb_prio"] = rb_prio["data"]
                            break
                        break
                    for local_info in l2["this-bridge"]:
                        for local_mac in local_info["bridge-mac"]:
                            stp_dict["vlan_local_mac"] = local_mac["data"]
                            break
                        for local_prio in local_info["bridge-priority"]:
                            stp_dict["vlan_local_prio"] = local_prio["data"]
                            break
                        break
                    for topo_change_count in l2["topology-change-count"]:
                        stp_dict["topo_change_count"] = topo_change_count["data"]
                        break
                    # Check if the topology change number is 0, if it is TC doesn't exist
                    if stp_dict["topo_change_count"] == "0":
                        stp_dict["time_since_last_tc"] = "0"
                    else:
                        for time_since_last_tc in l2["time-since-last-tc"]:
                            stp_dict["time_since_last_tc"] = time_since_last_tc["data"]
                            break
                    # Check if this device is the root bridge
                    if stp_dict["vlan_rb_mac"] == stp_dict["vlan_local_mac"]:
                        stp_dict["vlan_root_port"] = None
                        stp_dict["vlan_root_cost"] = None
                    # If this device is not root bridge
                    else:
                        for root_port in l2["root-port"]:
                            stp_dict["vlan_root_port"] = root_port["data"]
                            break
                        for root_cost in l2["root-cost"]:
                            stp_dict["vlan_root_cost"] = root_cost["data"]
                            break
                    # If a single vlan was provided return the stp_dict
                    if one_vlan:
                        #print("STP Dict")
                        #print(stp_dict)
                        return stp_dict
                    # If 'all' was provided, add stp_dict to the list
                    else:
                        stp_ld.append(stp_dict)
                    break
    return stp_ld

# Function to extract LLDP parameters from neighbors via Table/Views
# lldp_ld [
# lldp_dict {'local_int': '', 'remote_chassis_id': '', 'remote_sysname': ''}
# ]
def extract_lldp_info(lldpneigh, members='all'):
    lldp_ld = []
    # print("\n******* LLDP NEIGHBORS ******")
    for li in lldpneigh:
        # If the members are a list
        if type(members) == list:
            for item in members:
                lldp_dict = {}
                # This executes if the item matches and is an aggregate
                if li.local_parent != "-" and li.local_parent == item.split(".")[0]:
                    # print("{}: {}: {}".format(li.local_parent, li.remote_chassis_id,
                    #                          li.remote_sysname))
                    lldp_dict["local_int"] = li.local_parent
                    lldp_dict["remote_chassis_id"] = li.remote_chassis_id
                    lldp_dict["remote_sysname"] = li.remote_sysname
                    lldp_ld.append(lldp_dict)
                # If it is NOT an aggregate, check if it matches the item using local int
                elif li.local_int == item.split(".")[0]:
                    # print("{}: {}: {}".format(li.local_int, li.remote_chassis_id,
                    #                          li.remote_sysname))
                    lldp_dict["local_int"] = li.local_int
                    lldp_dict["remote_chassis_id"] = li.remote_chassis_id
                    lldp_dict["remote_sysname"] = li.remote_sysname
                    lldp_ld.append(lldp_dict)
        elif members == "all":
            lldp_dict = {}
            if li.local_parent != "-":
                # print("{}: {}: {}".format(li.local_parent, li.remote_chassis_id,
                #                         li.remote_sysname))
                lldp_dict["local_int"] = li.local_parent
                lldp_dict["remote_chassis_id"] = li.remote_chassis_id
                lldp_dict["remote_sysname"] = li.remote_sysname
                lldp_ld.append(lldp_dict)
            else:
                # print("{}: {}: {}".format(li.local_int, li.remote_chassis_id,
                #                         li.remote_sysname))
                lldp_dict["local_int"] = li.local_int
                lldp_dict["remote_chassis_id"] = li.remote_chassis_id
                lldp_dict["remote_sysname"] = li.remote_sysname
                lldp_ld.append(lldp_dict)
        # If the members is a string
        else:
            lldp_dict = {}
            if li.local_parent != "-" and li.local_parent == members.split(".")[0]:
                # print("{}: {}: {}".format(li.local_parent, li.remote_chassis_id,
                #                         li.remote_sysname))
                lldp_dict["local_int"] = li.local_parent
                lldp_dict["remote_chassis_id"] = li.remote_chassis_id
                lldp_dict["remote_sysname"] = li.remote_sysname
                lldp_ld.append(lldp_dict)
            elif li.local_int == members.split(".")[0]:
                # print("{}: {}: {}".format(li.local_int, li.remote_chassis_id,
                #                         li.remote_sysname))
                lldp_dict["local_int"] = li.local_int
                lldp_dict["remote_chassis_id"] = li.remote_chassis_id
                lldp_dict["remote_sysname"] = li.remote_sysname
                lldp_ld.append(lldp_dict)
    # Return LLDP
    # print("LLDP_LD")
    # print(lldp_ld)
    return lldp_ld

# This function assumes capturing "show spanning-tree bridge | display json" output
# lldp_ld [
# lldp_dict {'local_int': '', 'remote_chassis_id': '', 'remote_sysname': ''}
# ]
def extract_json_lldp_info(raw_dict, members='all'):
    lldp_ld = []
    for l1 in raw_dict["lldp-neighbors-information"]:
        for l2 in l1["lldp-neighbor-information"]:
            # Reset the LLDP dictionary
            parent_int = ""
            local_int = ""
            remote_chassis_id = ""
            remote_sysname = ""
            if "lldp-remote-system-name" in l2.keys():
                for sysname in l2["lldp-remote-system-name"]:
                    remote_sysname = sysname["data"]
            for p_int in l2["lldp-local-parent-interface-name"]:
                parent_int = p_int["data"]
            for l_int in l2["lldp-local-port-id"]:
                local_int = l_int["data"]
            for rem_c_id in l2["lldp-remote-chassis-id"]:
                remote_chassis_id = rem_c_id["data"]
            member_match = False
            # Loop over the members
            if type(members) == list:
                for member in members:
                    lldp_dict = {}
                    # print("Checking member: {}".format(member))
                    if parent_int != "-" and parent_int == member.split(".")[0]:
                        # print("Matched {}".format(local_port["data"]))
                        lldp_dict["local_int"] = parent_int
                        lldp_dict["remote_chassis_id"] = remote_chassis_id
                        lldp_dict["remote_sysname"] = remote_sysname
                        lldp_ld.append(lldp_dict)
                        member_match = True
                    elif local_int == member.split(".")[0]:
                        lldp_dict["local_int"] = local_int
                        lldp_dict["remote_chassis_id"] = remote_chassis_id
                        lldp_dict["remote_sysname"] = remote_sysname
                        lldp_ld.append(lldp_dict)
                        member_match = True
                    if member_match:
                        break
            elif members == 'all':
                lldp_dict = {}
                # print("Checking member: {}".format(member))
                if parent_int != "-":
                    # print("Matched {}".format(local_port["data"]))
                    lldp_dict["local_int"] = parent_int
                    lldp_dict["remote_chassis_id"] = remote_chassis_id
                    lldp_dict["remote_sysname"] = remote_sysname
                    lldp_ld.append(lldp_dict)
                else:
                    lldp_dict["local_int"] = local_int
                    lldp_dict["remote_chassis_id"] = remote_chassis_id
                    lldp_dict["remote_sysname"] = remote_sysname
                    lldp_ld.append(lldp_dict)
            elif members:
                lldp_dict = {}
                # print("Checking member: {}".format(member))
                if parent_int != "-" and parent_int == members.split(".")[0]:
                    # print("Matched {}".format(local_port["data"]))
                    lldp_dict["local_int"] = parent_int
                    lldp_dict["remote_chassis_id"] = remote_chassis_id
                    lldp_dict["remote_sysname"] = remote_sysname
                    lldp_ld.append(lldp_dict)
                    member_match = True
                elif local_int == members.split(".")[0]:
                    lldp_dict["local_int"] = local_int
                    lldp_dict["remote_chassis_id"] = remote_chassis_id
                    lldp_dict["remote_sysname"] = remote_sysname
                    lldp_ld.append(lldp_dict)
                    member_match = True
                if member_match:
                    break
    return lldp_ld

# Function to extract non-lldp interface information from Table/Views
# non_lldp_intf [
# non_lldp_dict {'intf': '', 'active': ''}
# ]
def extract_non_lldp_intf(lldp_dict, vlan_dict):
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
            # print("Upstream Int: {} Root Port: {} Sysname: {}".format(one_int["local_int"], root_port, one_int["remote_sysname"]))
            upstream_peer["name"] = one_int["remote_sysname"]
            upstream_peer["intf"] = one_int["local_int"]
    # print("Upstream Peer")
    # print(upstream_peer)
    return upstream_peer

def get_downstream_hosts(lldp_dict, root_port, stp_int_dict):
    downstream_raw = []
    downstream_list = []
    # print("Root Port: {}".format(root_port))
    # Create list of downstream hosts
    for one_int in lldp_dict:
        host_int_dict = {}
        if one_int["local_int"] != root_port:
            #print("Local Int: {} Remote Sysname: {}".format(one_int["local_int"], one_int["remote_sysname"]))
            host_int_dict["name"] = one_int["remote_sysname"]
            host_int_dict["intf"] = one_int["local_int"]
            for intf in stp_int_dict["interfaces"]:
                if intf["int_name"] == one_int["local_int"]:
                    host_int_dict["state"] = intf["port_state"]
                    host_int_dict["role"] = intf["port_role"]
            downstream_raw.append(host_int_dict)
            # print("Downstream Raw: {}".format(downstream_raw))
    # Remove duplicates
    for i in downstream_raw:
        if i not in downstream_list:
            #print("Host Int: {}".format(i))
            downstream_list.append(i)
    return downstream_list

def get_net_vlan_info(jdev, ip):
    stdout.write("-> Pulling VLAN info from " + ip + " ... \n")
    vlaninfo = VlanTable(jdev)
    vlaninfo.get(extensive=True)
    return vlaninfo

def get_file_vlan_info(host):
    vlan_json_file = os.path.join(selected_repo, (host + "_vlan-ext.json"))
    raw_dict = json_to_dict(vlan_json_file)
    return raw_dict

def get_net_stp_info(jdev, ip):
    stdout.write("-> Pulling Spanning-Tree info from " + ip + " ... \n")
    stpbridge = STPBridgeTable(jdev)
    stpbridge.get()
    return stpbridge

def get_file_stp_info(host):
    stp_json_file = os.path.join(selected_repo, (host + "_stp.json"))
    raw_dict = json_to_dict(stp_json_file)
    return raw_dict

def get_file_stp_int(host):
    stp_int_json_file = os.path.join(selected_repo, (host + "_stp-int.json"))
    raw_dict = json_to_dict(stp_int_json_file)
    return raw_dict

def get_net_lldp_info(jdev, ip):
    stdout.write("-> Pulling LLDP info from " + ip + " ... \n")
    lldpneigh = LLDPNeighborTable(jdev)
    lldpneigh.get()
    return lldpneigh

def get_net_ethersw_info(jdev, ip):
    stdout.write("-> Pulling Ethernet Switching Table info from " + ip + " ... \n")
    ethersw = ElsEthernetSwitchingTable(jdev)
    ethersw.get()
    return ethersw

def get_file_lldp_info(host):
    lldp_json_file = os.path.join(selected_repo, (host + "_lldp.json"))
    raw_dict = json_to_dict(lldp_json_file)
    return raw_dict

def get_net_facts(jdev, ip):
    facts_dict = {}
    stdout.write("-> Pulling basic facts from " + ip + " ... \n")
    facts_dict["hostname"] = jdev.facts['hostname']
    facts_dict["model"] = jdev.facts['model']
    facts_dict["version"] = jdev.facts['version']
    return facts_dict

def get_net_interface(jdev, ip):
    stdout.write("-> Pulling basic interface info from " + ip + " ... \n")
    phyintf = PhyPortTable(jdev)
    phyintf.get()
    return phyintf

def capture_chassis_info(selected_vlan, host, using_network):
    if host in dev_list.keys():
        ip = dev_list[host]
        chassis_dict = {"hostname": host, "ip": ip}
        # For using network
        if using_network:
            print(starHeading(host, 5))
            try:
                with Device(host=ip, user=username, password=password) as jdev:
                    # VLAN Info
                    vlan_dict = extract_vlan_info(get_net_vlan_info(jdev, ip), selected_vlan)
                    # STP Info (show spanning-tree bridge)
                    stp_dict = extract_span_info(get_net_stp_info(jdev, ip), selected_vlan)
                    # Check if vlan_dict and stp_dict are populated
                    if vlan_dict:
                        # LLDP Info (show lldp neighbors)
                        lldp_dict = extract_lldp_info(get_net_lldp_info(jdev, ip), vlan_dict["members"])
                    # If no vlan or stp information exists, provide an empty dict
                    else:
                        lldp_dict = {}
            except Exception as err:
                print("Connection failed. ERROR: {}".format(err))
                exit()
        # This will execute if we are using files for analysis
        else:
            # Pull VLAN info from JSON file
            vlan_dict = extract_json_vlan_info(get_file_vlan_info(host), selected_vlan)
            # Pull STP info from JSON file
            stp_dict = extract_json_stp_info(get_file_stp_info(host), selected_vlan)
            # Pull STP Interface info from JSON file
            stp_int_dict = extract_json_stp_int(get_file_stp_int(host), selected_vlan)
            #print("STP INT DICT")
            #print(stp_int_dict)

            # Pull LLDP info from JSON file
            if vlan_dict:
                lldp_dict = extract_json_lldp_info(get_file_lldp_info(host), vlan_dict["members"])
            else:
                lldp_dict = {}

        # Computed variables
        chassis_dict["vlan"] = vlan_dict
        chassis_dict["stp"] = stp_dict
        chassis_dict["stp-int"] = stp_int_dict
        chassis_dict["lldp"] = lldp_dict
        # Check if vlan dict exists
        if vlan_dict:
            # Check if the mac of the RB and local mac is the same, to check if this is the RB
            if stp_dict["vlan_rb_mac"] == stp_dict["vlan_local_mac"]:
                chassis_dict["root_bridge"] = True
            else:
                chassis_dict["root_bridge"] = False
            chassis_dict["upstream_peer"] = get_upstream_host(lldp_dict, stp_dict["vlan_root_port"])
            chassis_dict["downstream_peers"] = get_downstream_hosts(lldp_dict, stp_dict["vlan_root_port"], stp_int_dict)
            chassis_dict["non-lldp-intf"] = extract_non_lldp_intf(lldp_dict, vlan_dict)
        # print("Chassis Dict")
        # print(chassis_dict)
    # Go here if the host is not in the device list (ie. Cisco)
    else:
        chassis_dict = {"hostname": host}

    return chassis_dict

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
            # Add row to table
            myTable.add_row(host_content)
        else:
            adj_name = host["name"] + " (NV)"
            host_content = [adj_name, "-", "-", "-"]
            myTable.add_row(host_content)
    # Print this to the screen
    print(myTable)

    # Write it to a table
    with open(stp_stats, 'w') as w:
        w.write(str(myTable))

def create_chart():
    key = "upstream_peer"
    rb_key = "root_bridge"
    # Specify the Column Names while initializing the Table
    # Specify the Column Names while initializing the Table
    print("VLAN Name: {}".format(all_chassis["vlan_name"]))
    print("VLAN Tag: {}".format(all_chassis["vlan_id"]))
    myTable = PrettyTable(["Host", "Bridge Priority", "IRB Intf", "Upstream Intf", "Upstream Host", "Non-LLDP-Intfs",
                           "Downstream Intfs", "Downstream Hosts"])
    # Go over chassis
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
                    intf = down_peer["intf"] + "(" + down_peer["state"] + "|" + down_peer["role"] + ")"
                    host_content.append(intf)
                    host_content.append(down_peer["name"])
                    myTable.add_row(host_content)
        # Host the doesn't have VLAN
        else:
            adj_name = host["name"] + " (NV)"
            host_content = [adj_name, "-", "-", "-", "-", "-", "-", "-"]
            myTable.add_row(host_content)
    # Print it to the screen
    print(myTable)

    # Write it to a table
    with open(stp_chart, 'w') as w:
        w.write(str(myTable))

def stp_map_files():
    print("*" * 50 + "\n" + " " * 10 + "STP MAP using JSON Files\n" + "*" * 50)
    # Provide selection for sending a single command or multiple commands from a file
    hosts_list = []
    # Capture the available devices
    for a_host in dev_list.keys():
        hosts_list.append(a_host)

    # Collect all the vlans via json files, using repo location
    vlan_host_ld = collect_all_vlans_json(selected_repo)
    #print("VLAN HOST LD")
    #print(vlan_host_ld)

    # Select a VLAN from the host list then sort this list numerically
    vlan_list = []
    for vlan in vlan_host_ld:
        if vlan["vlan"].isnumeric():
            vlan_list.append(vlan["vlan"])
    # Sort the valid vlans
    vlan_list.sort(key=int)

    # Ask for a vlan to analyze
    selected_vlan = getOptionAnswer("Select a VLAN to analyze", vlan_list)

    # Get host list based on vlan selected
    host_list = []
    for my_vlan in vlan_host_ld:
        if my_vlan["vlan"] == selected_vlan:
            host_list = my_vlan["hosts"]

    # Process to capture information from hosts
    if selected_vlan:
        scan_loop(selected_vlan, host_list, using_network=False)
        # print("ALL CHASSIS")
        # print(all_chassis)
        # Print the table
        print("***********************")
        print("* Spanning Tree Chart *")
        print("***********************")
        create_chart()
        print("***********************")
        print("* Spanning Tree Stats *")
        print("***********************")
        create_stp_stats()
        # create_stp_paths()
    else:
        exit()

def scan_loop(selected_vlan, hosts, using_network):
    # Loop over hosts list
    root_bridge_found = False
    all_chassis["chassis"] = []

    # Provide dictionary for determining backup root bridge
    backup_rb = {'name': 'None', 'priority': 62000}

    # Loop over hosts
    for host in hosts:
        chassis_dict = capture_chassis_info(selected_vlan, host, using_network)

        # Check if this device is the root bridge
        if chassis_dict["vlan"]:
            if chassis_dict["root_bridge"]:
                root_bridge_found = True
                # Search the LLDP dict for the dict with the root port
                #print("-> {} is the root bridge of VLAN {}({})".format(host, chassis_dict["vlan"]["name"],
                #                                                       chassis_dict["vlan"]["tag"]))
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

                #if chassis_dict["downstream_peers"]:
                #    for peer in chassis_dict["downstream_peers"]:
                #        if peer["name"] in dev_list:
                #            hosts.append(peer["name"])
                #            print("-> Added {} to scan list (D1)".format(peer["name"]))

                # Add this chassis to the list
                all_chassis["chassis"].append(my_dict)
            # This device is not the root bridge
            else:
                print("Scanning: {}".format(host))
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
                    #if chassis_dict["downstream_peers"]:
                    #    for peer in chassis_dict["downstream_peers"]:
                    #        if peer["name"] in dev_list and peer["name"] not in hosts:
                    #            hosts.append(peer["name"])
                    #            print("-> Added {} to scan list (D2)".format(peer["name"]))
                            # print("-> Added {} to scan list".format(peer["name"]))
                    # Add this chassis to the list
                    all_chassis["chassis"].append(my_dict)

                # If the root bridge hasn't been found, check the upstream device
                else:
                    #print("-> {} is NOT the root bridge for VLAN({})".format(host, chassis_dict["vlan"]["name"],
                    #                                                        chassis_dict["vlan"]["tag"]))
                    # Re-add this device to the host
                    hosts.append(host)
                    #if chassis_dict["upstream_peer"]["name"] in dev_list and chassis_dict["upstream_peer"]["name"] not in hosts:
                    #    hosts.append(chassis_dict["upstream_peer"]["name"])

            # Add the backup root bridge name to the large dict
            all_chassis["backup_root_bridge"] = backup_rb["name"]
        # This chassis doesn't have the chosen VLAN
        else:
            my_dict = {}
            my_dict["name"] = host
            my_dict["no_vlan"] = True
            all_chassis["chassis"].append(my_dict)

def combine_ether_vlan_data(ether_dict, vlan_ld, phy_ld):
    # Find first two vlan / interface combinations
    #print("Ether Dict Original")
    #pprint(ether_dict)
    #print("Vlan LD Original")
    #pprint(vlan_ld)

    # Loop over the vlan records
    for vlan_rec in vlan_ld:
        vrec = {}
        vrec["vlan_tag"] = vlan_rec["vlan_tag"]
        # Collect the necessary information to update the ether records
        for vlan_intf in vlan_rec["interfaces"]:
            #print("Working on Intf: {} Vlan: {}".format(vlan_intf["name"], vlan_rec["vlan_tag"]))
            vrec["vlan_intf"] = vlan_intf["name"]
            vrec["tagged"] = vlan_intf["tagness"]
            vrec["mode"] = vlan_intf["mode"]
            vrec["active"] = vlan_intf["active"]
            # Loop over the ether records and update if interface/vlan matches
            for ether_intf in ether_dict["interfaces"]:
                if ether_intf["name"] == vrec["vlan_intf"]:
                    #print("Ether Intf...{}".format(ether_intf["name"]))
                    # Extract Interface Specific Info
                    for phy_int in phy_ld:
                        # Match the interfaces, need to remove last two characters to match physical interface
                        if phy_int["name"] == ether_intf["name"][:-2]:
                            #print("Matched phy name...{}".format(ether_intf["name"]))
                            ether_intf["oper_status"] = phy_int["oper_status"]
                            ether_intf["admin_status"] = phy_int["admin_status"]
                            ether_intf["speed"] = phy_int["speed"]
                    # Add macs to the interface
                    for ether_mac in ether_intf["macs"]:
                        if ether_mac["vlan_id"] == vrec["vlan_tag"]:
                            #print("Updating records for Intf: {} Vlan: {}".format(vrec["vlan_intf"], vrec["vlan_tag"]))
                            ether_mac["tagged"] = vrec["tagged"]
                            ether_mac["mode"] = vrec["mode"]
                            ether_mac["active"] = vrec["active"]
    return ether_dict

# Ether_LD Format
#ether_dict = { "interfaces": [
#    { "name": "ge-0/0/0.0",
#      "macs": [
#          { "mac": "ab:cd:ef:ab:cd:ef",
#            "vlan_id": "100",
#            "tagged": None,
#            "mode": None,
#            "active": False
#          },
#          {}
#        ],
#    }
#]
#}
def ether_switch_intf_data(raw_ether_data):
    ether_dict = {}
    ether_dict["interfaces"] = []
    temp_ld = []

    print("Performing Data Formatting...")
    # Extract all info into a list of dictionaries
    for info in raw_ether_data:
        ether_row = {}
        ether_row["interface"] = info.logical_interface
        ether_row["mac"] = info.mac_address
        ether_row["vlan_id"] = info.vlan_id
        temp_ld.append(ether_row)

    # Loop over the record list
    for temp_rec in temp_ld:
        # Create new mac record
        new_mac = {}
        new_mac["mac"] = temp_rec["mac"]
        new_mac["vlan_id"] = temp_rec["vlan_id"]
        new_mac["tagged"] = None
        new_mac["mode"] = None
        new_mac["active"] = False
        # If there are records currently in this LD
        if ether_dict["interfaces"]:
            intf_matched = False
            # Loop over the interfaces to try to find a match
            for ether_int_rec in ether_dict["interfaces"]:
                # If the interfaces match, create and add a record to the
                if ether_int_rec["name"] == temp_rec["interface"]:
                    intf_matched = True
                    # If "macs" key exists, create and add a dict to the list
                    if "macs" in ether_int_rec.keys():
                        ether_int_rec["macs"].append(new_mac)
                    # If "macs" key doesn't exist,
                    else:
                        pass
                        #print("The macs key doesn't exist")
            # If the interface from temp does not match any existing interfaces, create a new interface dict
            if not intf_matched:
                # Create the new interface dict
                new_intf = {}
                new_intf["name"] = temp_rec["interface"]
                new_intf["macs"] = []
                # Add the new mac dict to the interface
                new_intf["macs"].append(new_mac)
                # Add the interface dict to the larger dict
                ether_dict["interfaces"].append(new_intf)
            else:
                pass
                #print("The new mac was added.")
        # If there aren't any interfaces added to ether dict
        else:
            # Create a new interface dict
            new_intf = {}
            new_intf["name"] = temp_rec["interface"]
            new_intf["macs"] = []
            # Add the new mac dict to the interface
            new_intf["macs"].append(new_mac)
            # Add the interface dict to the larger dict
            ether_dict["interfaces"].append(new_intf)
    return ether_dict

#vlan_ld = [ { "vlan_name": "vlan-100",
#            "vlan_tag": "100",
#            "vlan_active": True,
#            "interfaces": [
#                { "name": "ge-0/0/0",
#                "tagness": True,
#                "mode": "trunk",
#                "active": True
#                }
#            ]
#        } ]
def vlan_intf_data(raw_vlan_data):
    vlan_ld = []
    temp_ld = []

    # Extract info from raw data structure
    for info in raw_vlan_data:
        vlan_dict = {}
        vlan_dict["name"] = info.name
        vlan_dict["tag"] = info.tag
        vlan_dict["state"] = info.state
        vlan_dict["interfaces"] = info.members
        vlan_dict["tagness"] = info.tagness
        vlan_dict["modes"] = info.mode
        temp_ld.append(vlan_dict)

    # Loop over records
    for temp_rec in temp_ld:
        vlan_dict = {}
        vlan_dict["vlan_name"] = temp_rec["name"]
        vlan_dict["vlan_tag"] = temp_rec["tag"]
        if temp_rec["state"] == "Active":
            vlan_dict["vlan_active"] = True
        else:
            vlan_dict["vlan_active"] = False
        vlan_dict["interfaces"] = []

        # If interfaces is a list (of strings) or string
        if type(temp_rec["interfaces"]) == list:
            #print("Interfaces is a list...")
            list_len = len(temp_rec["interfaces"])
            list_num = 0
            while list_num < list_len:
                temp_dict = {}
                if "*" in temp_rec["interfaces"][list_num]:
                    temp_dict["active"] = True
                else:
                    temp_dict["active"] = False
                if temp_dict["active"]:
                    temp_dict["name"] = temp_rec["interfaces"][list_num][:len(temp_rec["interfaces"][list_num])-1]
                else:
                    temp_dict["name"] = temp_rec["interfaces"][list_num]
                if temp_rec["tagness"][list_num] == "tagged":
                    temp_dict["tagness"] = True
                else:
                    temp_dict["tagness"] = False
                temp_dict["mode"] = temp_rec["modes"][list_num]
                list_num += 1
                vlan_dict["interfaces"].append(temp_dict)
        # If interfaces is a string...
        elif temp_rec["interfaces"]:
            temp_dict = {}
            if "*" in temp_rec["interfaces"]:
                temp_dict["active"] = True
            else:
                temp_dict["active"] = False
            if temp_dict["active"]:
                temp_dict["name"] = temp_rec["interfaces"][:len(temp_rec["interfaces"])-1]
            else:
                temp_dict["name"] = temp_rec["interfaces"]
            if temp_rec["tagness"] == "tagged":
                temp_dict["tagness"] = True
            else:
                temp_dict["tagness"] = False
            temp_dict["mode"] = temp_rec["modes"]
            vlan_dict["interfaces"].append(temp_dict)
        # Otherwise, if interfaces is not a good format, return empty interfaces list
        else:
            pass

        # Add this to the main list
        vlan_ld.append(vlan_dict)
    return vlan_ld

#all_chassis = [ { "chassis": "EX1",
#                "interfaces": [
#                    { "name": "ge-0/0/0",
#                      "vlan-id": "100",
#                      "tagged" : None,
#                      "mode": None }
#                ]
def ether_switch_net():
    print("*" * 50 + "\n" + " " * 10 + "Ether Switching using Network\n" + "*" * 50)
    # Provide selection for sending a single command or multiple commands from a file
    all_chassis = []

    #my_ips = chooseDevices(iplist_dir)
    my_ips = ['132.32.254.2', '132.32.255.1']
    if my_ips:
        # Loop over commands and devices
        for ip in my_ips:
            stdout.write("-> Connecting to " + ip + " ... ")
            jdev = connect(ip)
            # Chassis Facts
            chassis_facts = get_net_facts(jdev, ip)
            #print("Hostname: {} Model: {}".format(chassis_facts["hostname"], chassis_facts["model"]))
            temp_chassis = {}
            temp_chassis["chassis"] = chassis_facts["hostname"]
            temp_chassis["model"] = chassis_facts["model"]
            temp_chassis["interfaces"] = []

            # Interface Information
            phyinfo = get_net_interface(jdev, ip)
            phy_ld = []
            for info in phyinfo:
                phy_dict = {}
                #print("Interface Name: {} Oper Status: {} Admin Status: {} Speed: {}".format(info.name, info.oper, info.admin, info.speed))
                phy_dict["name"] = info.name
                phy_dict["oper_status"] = info.oper
                phy_dict["admin_status"] = info.admin
                phy_dict["speed"] = info.speed
                phy_ld.append(phy_dict)

            # Ethernet Switching Info Collection
            etherswinfo = get_net_ethersw_info(jdev, ip)
            #for info in etherswinfo:
            #    print("Logical Interface: {} MAC: {} VLAN: {}".format(info.logical_interface, info.mac_address, info.vlan_id))
            #print("Ether Switching Data")
            ether_dict = ether_switch_intf_data(etherswinfo)

            # Vlan Info Collection
            vlanextinfo = get_net_vlan_info(jdev, ip)
            #for info in vlanextinfo:
            #    print("Vlan Name(Tag): {}({}) State: {} Member: {} Tagness: {} Mode: {}".format(info.name, info.tag, info.state, info.members, info.tagness, info.mode))
            #print("VLAN INTF Data")
            vlan_ld = vlan_intf_data(vlanextinfo)

            # Combine Data
            parsed_results = combine_ether_vlan_data(ether_dict, vlan_ld, phy_ld)
            #print("Parsed Results")
            #pprint(parsed_results)

            # Add data to chassis data structure
            for intf in parsed_results["interfaces"]:
                temp_chassis["interfaces"].append(intf)

            # Add to all chassis structure
            all_chassis.append(temp_chassis)
        #print("All chassis")
        #pprint(all_chassis)

        # Print the results to the CLI
        print_suspect_interfaces(get_suspect_interfaces(all_chassis))

# - Extract the problems
#   - interfaces that have two mac addresses on the same vlan
#   - interfaces that are running at a speed less than 1G
def get_suspect_interfaces(all_chassis):
    results_ld = []

    for chassis in all_chassis:
        # Loop over the interfaces in the chassis
        for intf in chassis["interfaces"]:
            found_speed_discrep = False
            found_mac_discrep = False
            # Check if the interface is up/up
            if intf["admin_status"] == "up" and \
                    intf["oper_status"] == "up" and \
                    len(intf["macs"]) > 1:
                access_num = 0
                vlan_id = {}
                vlan_matched = "0"
                # Loop over macs
                for one_mac in intf["macs"]:
                    if one_mac["mode"] == "access":
                        access_num += 1
                        if one_mac["vlan_id"] in vlan_id.keys():
                            vlan_id[one_mac["vlan_id"]] += 1
                        else:
                            vlan_id[one_mac["vlan_id"]] = 1
                for key in vlan_id:
                    if vlan_id[key] > 1:
                        #print("Found {} MACs in VLAN ID: {}".format(vlan_id[key], key))
                        found_mac_discrep = True
                        vlan_matched = key
                if intf["speed"] == "100mbps" or intf["speed"] == "10mbps":
                    #print("Found interface speed at {}".format(intf["speed"]))
                    found_speed_discrep = True
                if found_mac_discrep:
                    for one_mac in intf["macs"]:
                        if one_mac["vlan_id"] == vlan_matched:
                            #print("One Mac: {}".format(one_mac["mac"]))
                            captured_macs = {}
                            captured_macs["chassis"] = chassis["chassis"]
                            captured_macs["interface"] = intf["name"]
                            captured_macs["speed"] = intf["speed"]
                            captured_macs["admin-oper"] = intf["admin_status"] + "|" + intf["oper_status"]
                            captured_macs["vlan_id"] = one_mac["vlan_id"]
                            captured_macs["mac"] = one_mac["mac"]
                            captured_macs["mode"] = one_mac["mode"]
                            #print("Captured Macs:")
                            #pprint(captured_macs)
                            results_ld.append(captured_macs)
                elif found_speed_discrep:
                    captured_macs = {}
                    captured_macs["chassis"] = chassis["chassis"]
                    captured_macs["interface"] = intf["name"]
                    captured_macs["speed"] = intf["speed"]
                    captured_macs["admin-oper"] = intf["admin_status"] + "|" + intf["oper_status"]
                    captured_macs["vlan_id"] = None
                    captured_macs["mac"] = None
                    captured_macs["mode"] = None
                    results_ld.append(captured_macs)
    #print("Results LD")
    #pprint(results_ld)
    return results_ld

def print_suspect_interfaces(results_ld):
    # Define the table column headings
    myTable = PrettyTable(["Chassis", "Interface", "Status", "Speed", "Host Mac", "Vlan", "Mode"])

    # Loop over results and assign results to a list to populate row
    for row in results_ld:
        row_list = []
        row_list.append(row["chassis"])
        row_list.append(row["interface"])
        row_list.append(row["admin-oper"])
        row_list.append(row["speed"])
        row_list.append(row["mac"])
        row_list.append(row["vlan_id"])
        row_list.append(row["mode"])
        myTable.add_row(row_list)

    # Print the complete table
    print(myTable)

    # Write it to a table
    with open(mac_scan_results, 'w') as w:
        w.write(str(myTable))

# Function for running operational commands to multiple devices
def stp_map_net():
    print("*" * 50 + "\n" + " " * 10 + "STP MAP using Network\n" + "*" * 50)
    # Provide selection for sending a single command or multiple commands from a file
    selected_vlan = "None"
    hosts = []

    my_ips = chooseDevices(iplist_dir)
    if my_ips:
        # Loop over commands and devices
        backup_rb = {"name": "None", "priority": 64000}
        for ip in my_ips:
            stdout.write("-> Connecting to " + ip + " ... ")
            jdev = connect(ip)
            vlan_list = []
            vlaninfo = VlanTable(jdev)
            vlaninfo.get()
            for name in vlaninfo:
                vlan_list.append(name.tag)
            selected_vlan = getOptionAnswer("Choose a VLAN", vlan_list)
            hosts.append(host_from_ip(dev_list, ip))

        # Captures the information into data structures
        scan_loop(selected_vlan, hosts, using_network=True)

        # Print the table
        print("***********************")
        print("* Spanning Tree Chart *")
        print("***********************")
        create_chart()
        print("***********************")
        print("* Spanning Tree Stats *")
        print("***********************")
        create_stp_stats()
        # create_stp_paths()
    else:
        print("\n!! Configuration deployment aborted... No IPs defined !!!\n")

# Function to analyze the spanning tree domains of VLANs in the network
def root_bridge_analysis(myselect="file"):
    print("*" * 50 + "\n" + " " * 10 + "Root Bridge Analysis\n" + "*" * 50)
    mac_ld = []
    vlans_ld = []
    all_vlans = []
    # Collect all vlans via network
    if myselect == "net":
        raw_vlan_list = []
        for host in dev_list:
            print("Host: {} IP: {}".format(host, dev_list[host]))
            try:
                with Device(host=dev_list[host], user=username, password=password) as jdev:
                    more_vlans = extract_vlan_info(get_net_vlan_info(jdev, dev_list[host]))
                    raw_vlan_list = raw_vlan_list + more_vlans
            except Exception as err:
                print("Connection failed. ERROR: {}".format(err))
                exit()
        vlan_only = []
        for one_vlan in raw_vlan_list:
            vlan_only.append(one_vlan["tag"])
        nodup_vlans = remove_duplicates(vlan_only)
    # Collect all vlans via json files
    else:
        nodup_vlans = []
        vlan_host_ld = collect_all_vlans_json(selected_repo)
        for vh in vlan_host_ld:
            nodup_vlans.append(vh["vlan"])

    # Create base of data structure to store all info
    for vlan in nodup_vlans:
        vlan_dict = {'vlan': vlan, 'chassis': []}
        vlans_ld.append(vlan_dict)
    # Loop over hosts and get STP info for each VLAN
    for host in dev_list.keys():
        print("Processing host {} ...".format(host))
        # Capture needed information from host
        first_pass = True
        stp_temp_ld = []
        stp_int_temp_ld = []
        vlan_temp_ld = []
        lldp_dict = {}
        if myselect == "file":
            stp_temp_ld = extract_json_stp_info(get_file_stp_info(host))
            stp_int_temp_ld = extract_json_stp_int(get_file_stp_int(host))
            vlan_temp_ld = extract_json_vlan_info(get_file_vlan_info(host))
            lldp_dict = remove_duplicates(extract_json_lldp_info(get_file_lldp_info(host)))
        else:
            ip = dev_list[host]
            print(starHeading(host, 5))
            try:
                with Device(host=ip, user=username, password=password) as jdev:
                    # VLAN Info
                    vlan_temp_ld = extract_vlan_info(get_net_vlan_info(jdev, ip))
                    # STP Info (show spanning-tree bridge)
                    stp_temp_ld = extract_span_info(get_net_stp_info(jdev, ip))
                    # Check if vlan_dict and stp_dict are populated
                    if vlan_dict:
                        # LLDP Info (show lldp neighbors)
                        lldp_dict = extract_lldp_info(get_net_lldp_info(jdev, ip))
                    # If no vlan or stp information exists, provide an empty dict
                    else:
                        lldp_dict = {}
            except Exception as err:
                print("Connection failed. ERROR: {}".format(err))
                exit()
        # Loop over the vlan data captured for this host
        for vlan_dict in vlan_temp_ld:
            # Loop over the vlans in the data structure
            for vlan in vlans_ld:
                # If the vlan data capture and data structure matches...
                if vlan["vlan"] == vlan_dict["tag"]:
                    temp_dict = {"host": host, "l3-interface": vlan_dict["l3interface"]}
                    # Loop over the spanning tree data collected
                    for stp_dict in stp_temp_ld:
                        # If the vlan_id info for this host matches the stp vlan_id
                        if vlan_dict["tag"] == stp_dict["vlan_id"]:
                            temp_dict["root-bridge-mac"] = stp_dict["vlan_rb_mac"]
                            temp_dict["root-bridge-priority"] = stp_dict["vlan_rb_prio"]
                            temp_dict["local-mac"] = stp_dict["vlan_local_mac"]
                            temp_dict["local-priority"] = stp_dict["vlan_local_prio"]
                            # Make root cost 0 if None is the value
                            if stp_dict["vlan_root_cost"] is None:
                                temp_dict["root-cost"] = "0"
                            else:
                                temp_dict["root-cost"] = stp_dict["vlan_root_cost"]
                            # Make root port "-" if its None
                            if stp_dict["vlan_root_port"] is None:
                                temp_dict["root-port"] = "None"
                            else:
                                temp_dict["root-port"] = stp_dict["vlan_root_port"]
                            temp_dict["topo-changes"] = stp_dict["topo_change_count"]
                            temp_dict["time-since-last-tc"] = stp_dict["time_since_last_tc"]
                            # Add the chassis to the LD
                            if first_pass:
                                mac_dict = {"hostname": host, "mac": stp_dict["vlan_local_mac"]}
                                mac_ld.append(mac_dict)
                                first_pass = False
                            # Select the downstream peers associated with the VLAN only
                            for stp_int_dict in stp_int_temp_ld:
                                if stp_int_dict["vlan_id"] == vlan_dict["tag"]:
                                    #print("Matched VLAN: {}".format(vlan_dict["tag"]))
                                    downstream_ld = get_downstream_hosts(lldp_dict, stp_dict["vlan_root_port"], stp_int_dict)
                                    temp_dict["downstream-peers"] = []
                                    for down_dict in downstream_ld:
                                        for member in vlan_dict["members"]:
                                            if down_dict["intf"] == member.split(".")[0] and "*" in member:
                                                temp_dict["downstream-peers"].append(down_dict["name"])
                                                break
                                    break
                    # Check if downstream-peers is in the dictionary
                    if "downstream-peers" not in temp_dict.keys():
                        #print(temp_dict)
                        temp_dict["downstream-peers"] = []
                    # Add the chassis dict to the "chassis" list
                    vlan["chassis"].append(temp_dict)
    # Print table to CLI
    create_root_analysis(vlans_ld, mac_ld)
    #vlans = [ { 'vlan': '4001',
    #            'chassis': [
    #                { 'host': 'SF-A',
    #                'root-bridge-mac': '2c:3b:1a:aa:bb:cc',
    #                'root-bridge-priority': '4000',
    #                'local-mac': '2c:3b:1a:aa:bb:cc',
    #                'local-priority': '4000',
    #                'root-cost': '0',
    #                'root-port': 'ge-0/0/0'
    #                'downstream-peers': [ 'CN1', 'SF-B' ],
    #                'topo-changes': '4',
    #                'time-since-last-tc': '2"
    #                'l3-interface': 'irb.4001'
    #                  },
    #                { 'host': 'SF-B'}
    #            ]
    #            },
    #          { 'vlan': '111',
    #            'chassis': [
    #                { 'name':
    #                }
    #            ]
    #           }}]
    # MAC - HOST Dictionary
    # mac = [ { 'hostname': 'SF-A', 'mac': '2c:3a:5b:aa:bb:cc'},
    #         { 'hostname': 'SF-B', 'mac': '2c:88:77:ab:bc:cd'}
    #       ]

def collect_vlan_list_net(vlan_ld):
    vlan_list = []
    for vlan in vlan_ld:
        if vlan["tag"]:
            vlan_list.append(vlan["tag"])
    return vlan_list

def collect_all_vlans_json(selected_repo):
    vlan_host_ld = []
    # Collect all the vlans via json files, using repo location
    for host in dev_list.keys():
        vlan_json_file = os.path.join(selected_repo, (host + "_vlan-ext.json"))
        v_list = collect_vlan_list_json(json_to_dict(vlan_json_file))
        # Loop over the complete VLAN list
        for this_vlan in v_list:
            vlan_found = False
            # Loop over the LD to find the correct vlan
            for vh_dict in vlan_host_ld:
                # If the VLAN dict exists, add the current host to the list
                if vh_dict["vlan"] == this_vlan:
                    # Add the host to the hosts list for this vlan
                    vh_dict["hosts"].append(host)
                    vlan_found = True
                    break
            # If the VLAN wasn't found, create a new dictionary and add the host to hosts and dict to the LD
            if not vlan_found:
                # Create dictionary entry for this vlan
                vlan_host_dict = {}
                vlan_host_dict["vlan"] = this_vlan
                vlan_host_dict["hosts"] = []
                # Add the current host to the hosts of this dict
                vlan_host_dict["hosts"].append(host)
                # Add the dictionary to the LD
                vlan_host_ld.append(vlan_host_dict)

    return vlan_host_ld

def create_root_analysis(vlans_ld, mac_ld):
    key = "upstream_peer"
    rb_key = "root_bridge"
    # Replacement strings to remove ot pare down system names
    replace_strs = {'FXBM-': '', '.ellsworth.af.mil': ''}
    # Specify the Column Names while initializing the Table
    # Specify the Column Names while initializing the Table
    myTable = PrettyTable(["VLAN", "Chassis", "Root Bridge (Cost)", "Local Priority", "Root Port", "Downstream Peers",
                           "Topo Changes (D|H|M)", "L3 Interface"])
    breakrow = ['----', '-------', '--------------------', '-----', '------------', '--------', '--------', '-------']
    # Loop over VLAN hierarchy
    for vlan in vlans_ld:
        vlan_sort_list = []
        for chassis in vlan["chassis"]:
            row_contents = []
            # Populate VLAN cell
            row_contents.append(vlan["vlan"])
            # Populate Chassis cell
            row_contents.append(remove_substrings(chassis["host"], replace_strs))
            # Populate Root Bridge cell
            if "local-mac" in chassis:
                if "root-bridge-mac" in chassis:
                    matched_mac = False
                    for mac_dict in mac_ld:
                        if mac_dict["mac"] == chassis["root-bridge-mac"]:
                            row_contents.append(remove_substrings(mac_dict["hostname"], replace_strs) + " (" + chassis["root-cost"] + ")")
                            matched_mac = True
                            break
                    if not matched_mac:
                        row_contents.append(chassis["root-bridge-mac"] + " (" + chassis["root-cost"] + ")")
                # Populate Local Priority
                row_contents.append(chassis["local-priority"])
                # Populate Root Port Cell
                row_contents.append(chassis['root-port'])
                # Populate Downstream Peers
                peer_list = ""
                #num = len(chassis["downstream-peers"])
                nondef = 0
                for peer in chassis["downstream-peers"]:
                    if peer in dev_list.keys():
                        peer_list = peer_list + peer + " "
                    else:
                        nondef += 1
                # Determine how to display this...
                if peer_list:
                    row_contents.append(remove_substrings(peer_list, replace_strs) + "(" + str(nondef) + ")")
                elif nondef > 0:
                    row_contents.append("(" + str(nondef) + ")")
                else:
                    row_contents.append("None")
                # Populate Topology Changes Number
                if int(chassis["topo-changes"]) and int(chassis["time-since-last-tc"]) < 432000:
                    # 432000 is 5 days in seconds
                    change_time = "{} TC({})".format(chassis["topo-changes"], seconds_to_dhm(int(chassis["time-since-last-tc"])))
                    row_contents.append(change_time)
                else:
                    row_contents.append(chassis["topo-changes"])
                # Populate L3 Interfaces
                if chassis["l3-interface"]:
                    row_contents.append(chassis["l3-interface"])
                else:
                    row_contents.append("-")
                row_contents.append(chassis["root-cost"])
                #myTable.add_row(row_contents)
                # Apply row to sort list
                vlan_sort_list.append(row_contents)
            else:
                pass
                #print("Vlan: {} Chassis: {} did not have a local-mac.".format(vlan["vlan"], chassis["host"]))
        # Sort the rows for this VLAN so that 0 root costs are first
        sorted_list = sorted(vlan_sort_list, key=itemgetter(8))

        # Put all the sorted rows in the table and remove the last element used for sorting
        for row in sorted_list:
            ele = row.pop()
            myTable.add_row(row)
        # Add this row to breakup the VLANs
        myTable.add_row(breakrow)
    # Print the table
    print(myTable)

    # Write it to a table
    with open(table_file, 'w') as w:
        w.write(str(myTable))

# Used to choose the repository for selecting
def select_repository():
    global selected_repo
    dirs = [d for d in os.listdir(json_dir) if os.path.isdir(os.path.join(json_dir, d))]
    answer = getOptionAnswer('Choose a source repository', dirs)
    selected_repo = os.path.join(dir_path, 'json', (answer + "/"))
    print("Path: {}".format(selected_repo))

# Main execution loop
if __name__ == "__main__":

    # Detect the platform type
    detect_env()

    # Get a username and password from the user
    username = getargs(sys.argv[1:])
    if not username:
        print('Please supply a username as an argument: jshow.py -u <username>')
        exit()

    # Define menu options
    my_options = ['Scan Vlans (Files)', 'Scan Vlans (Network)', 'Root Bridge Analysis (File)',
                  'Root Bridge Analysis (Network)', 'Mac Address Function', 'Quit']

    # Get menu selection
    while True:
        stdout.write("\n\n")
        print("*" * 50 + "\n" + " " * 10 + "JSHOW: MAIN MENU\n" + "*" * 50)
        answer = getOptionAnswerIndex('Make a Selection', my_options)
        if answer == "1":
            select_repository()
            dev_list = json_to_dict(os.path.join(selected_repo, 'dev_list.json'))
            stp_map_files()
        elif answer == "2":
            password = getpass(prompt="\nEnter your password: ")
            stp_map_net()
        elif answer == "3":
            select_repository()
            dev_list = json_to_dict(os.path.join(selected_repo, 'dev_list.json'))
            root_bridge_analysis()
        elif answer == "4":
            password = getpass(prompt="\nEnter your password: ")
            root_bridge_analysis('net')
        elif answer == "5":
            password = 'f0r5ak3n'
            #password = getpass(prompt="\nEnter your password: ")
            ether_switch_net()
        elif answer == "6":
            quit()
