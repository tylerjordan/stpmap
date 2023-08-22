
import getopt
import csv
import logging
import datetime
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
from ncclient.operations.errors import TimeoutExpiredError
from utility import *
from os.path import join
from getpass import getpass
#from prettytable import PrettyTable
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
    "CN5": "132.32.255.205"
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
chassis_ld = {}


# Function to determine running enviornment (Windows/Linux/Mac) and use correct path syntax
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
    print("Selected VLAN: {}".format(selected_vlan))
    print("\n******* VLAN INFO ******")
    for name in vlaninfo:
        if name.tag == selected_vlan:
            print("{}: {}: {}".format(name.name, name.tag, name.members))
            vlan_dict["name"] = name.name
            vlan_dict["tag"] = name.tag
            vlan_dict["members"] = name.members
    return vlan_dict

def capture_span_info(selected_vlan, stpbridge):
    stp_dict = {}
    print("\n******* STP BRIDGE INFO ******")
    for vlan_id in stpbridge:
        if vlan_id.vlan_id == selected_vlan:
            print("{} | {}({}) | {}({}) | {}".format(vlan_id.vlan_id, vlan_id.root_bridge_mac,
                                                     vlan_id.root_bridge_priority, vlan_id.local_bridge_mac,
                                                     vlan_id.local_bridge_priority, vlan_id.root_port))
            stp_dict["vlan_id"] = vlan_id.vlan_id
            stp_dict["vlan_rb_mac"] = vlan_id.root_bridge_mac
            stp_dict["vlan_rb_prio"] = vlan_id.root_bridge_priority
            stp_dict["vlan_local_mac"] = vlan_id.local_bridge_mac
            stp_dict["vlan_local_prio"] = vlan_id.local_bridge_priority
            stp_dict["vlan_root_port"] = vlan_id.root_port
    return stp_dict

def capture_lldp_info(lldpneigh, members):
    lldp_ld = []
    print("\n******* LLDP NEIGHBORS ******")
    for li in lldpneigh:
        if type(members) == list:
            for item in members:
                lldp_dict = {}
                if li.local_parent != "-" and li.local_parent == item.split(".")[0]:
                    print("{}: {}: {}".format(li.local_parent, li.remote_chassis_id,
                                              li.remote_sysname))
                    lldp_dict["local_int"] = li.local_parent
                    lldp_dict["remote_chassis_id"] = li.remote_chassis_id
                    lldp_dict["remote_sysname"] = li.remote_sysname
                    lldp_ld.append(lldp_dict)
                elif li.local_int == item.split(".")[0]:
                    print("{}: {}: {}".format(li.local_int, li.remote_chassis_id,
                                              li.remote_sysname))
                    lldp_dict["local_int"] = li.local_int
                    lldp_dict["remote_chassis_id"] = li.remote_chassis_id
                    lldp_dict["remote_sysname"] = li.remote_sysname
                    lldp_ld.append(lldp_dict)

        else:
            lldp_dict = {}
            if li.local_parent != "-" and li.local_parent == members.split(".")[0]:
                print("{}: {}: {}".format(li.local_parent, li.remote_chassis_id,
                                          li.remote_sysname))
                lldp_dict["local_int"] = li.local_parent
                lldp_dict["remote_chassis_id"] = li.remote_chassis_id
                lldp_dict["remote_sysname"] = li.remote_sysname
                lldp_ld.append(lldp_dict)
            elif li.local_int == members.split(".")[0]:
                print("{}: {}: {}".format(li.local_int, li.remote_chassis_id,
                                          li.remote_sysname))
                lldp_dict["local_int"] = li.local_int
                lldp_dict["remote_chassis_id"] = li.remote_chassis_id
                lldp_dict["remote_sysname"] = li.remote_sysname
                lldp_ld.append(lldp_dict)
    return(lldp_ld)

def get_downstream_hosts(lldp_dict, root_port):
    downstream_list = []
    for one_int in lldp_dict:
        if one_int["local_int"] != root_port:
            print("Local Int: {} Root Port: {} Sysname: {}".format(one_int["local_int"], root_port, lldp_dict["remote_sysname"]))
            downstream_list.append(lldp_dict["remote_sysname"])
    return downstream_list

def capture_chassis_info(selected_vlan, ip):
    chassis_dict = {}
    host = {i for i in dev_list if dev_list[i] == ip}
    stdout.write("-> Connecting to " + ip + " ... ")
    with Device(host=ip, user=username, password=password) as jdev:
        vlaninfo = VlanTable(jdev)
        vlaninfo.get()
        vlan_dict = capture_vlan_info(selected_vlan, vlaninfo)
        print("VLAN DICT")
        print(vlan_dict)

        stpbridge = STPBridgeTable(jdev)
        stpbridge.get()
        stp_dict = capture_span_info(selected_vlan, stpbridge)
        print("STP DICT")
        print(stp_dict)

        lldpneigh = LLDPNeighborTable(jdev)
        lldpneigh.get()
        lldp_dict = capture_lldp_info(lldpneigh, vlan_dict["members"])
        print("LLDP DICT")
        print(lldp_dict)

        chassis_dict["ip"] = ip
        chassis_dict["vlan"] = vlan_dict
        chassis_dict["stp"] = stp_dict
        chassis_dict["lldp"] = lldp_dict
        chassis_dict["upstream"] = stp_dict["vlan_root_port"]
        chassis_dict["downstream"] = get_downstream_hosts(lldp_dict, stp_dict["vlan_root_port"])

        chassis_ld[str(host)] = chassis_dict
    print(chassis_ld)

# Function for running operational commands to multiple devices
def oper_commands(my_ips):
    print("*" * 50 + "\n" + " " * 10 + "OPERATIONAL COMMANDS\n" + "*" * 50)
    # Provide selection for sending a single command or multiple commands from a file
    chassis_dict = {}
    if not my_ips:
        my_ips = chooseDevices(iplist_dir)
    if my_ips:
        # Loop over commands and devices
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
                capture_chassis_info(selected_vlan, ip)
                exit()
            # Check for the root port host
            if chassis_dict["stp"]["vlan_root_port"] != None:
                # Search the LLDP dict for the dict with the root port
                print("Searching Dict...")
                for lldp_int in chassis_dict["lldp"]:
                    if lldp_int["local_int"] == chassis_dict["stp"]["vlan_root_port"]:
                        print("Found Root Port and Host!!!")
                        print("Interface is: {}".format(chassis_dict["stp"]["vlan_root_port"]))
                        print("Host is: {}".format(lldp_int["remote_sysname"]))
                        print("IP is: {}".format(dev_list[lldp_int["remote_sysname"]]))
            else:
                print("This is the root bridge for VLAN {}".format(chassis_dict["vlan"]["tag"]))
            exit()

        except KeyboardInterrupt:
            print("Exiting Procedure...")
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
    my_options = ['Scan Vlans', 'Quit']
    my_ips = []

    # Get menu selection
    while True:
        stdout.write("\n\n")
        print("*" * 50 + "\n" + " " * 10 + "JSHOW: MAIN MENU\n" + "*" * 50)
        answer = getOptionAnswerIndex('Make a Selection', my_options)
        if answer == "1":
            oper_commands(my_ips)
        elif answer == "2":
            quit()
