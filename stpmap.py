
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

# Function for running operational commands to multiple devices
def oper_commands(my_ips):
    print("*" * 50 + "\n" + " " * 10 + "OPERATIONAL COMMANDS\n" + "*" * 50)
    # Provide selection for sending a single command or multiple commands from a file
    if not my_ips:
        my_ips = chooseDevices(iplist_dir)

    if my_ips:
        command_list = []
        print("\n" + "*" * 110 + "\n")
        command_list = getMultiInputAnswer("Enter a command to run")

        if getTFAnswer("Continue with operational requests?"):
            # Loop over commands and devices
            devs_unreachable = []
            devs_no_output = []
            devs_with_output = []
            loop = 0
            try:
                for ip in my_ips:
                    command_output = ""
                    loop += 1
                    stdout.write("-> Connecting to " + ip + " ... ")
                    with Device(host=ip, user=username, password=password) as jdev:
                        print("\n******* VLAN INFO ******\n")
                        vlaninfo = VlanTable(jdev)
                        vlaninfo.get()
                        for name in vlaninfo:
                            if name.tag == '111':
                                print("{}: {}: {}\n".format(name.name, name.tag, name.members))
                        print("******* STP BRIDGE INFO ******\n")
                        stpbridge = STPBridgeTable(jdev)
                        stpbridge.get()
                        for vlan_id in stpbridge:
                            if vlan_id.vlan_id == '111':
                                print("{}: {}: {}: {}\n".format(vlan_id.vlan_id, vlan_id.root_bridge_mac,
                                                          vlan_id.local_bridge_mac, vlan_id.root_port))
                        print("******* LLDP NEIGHBORS ******\n")
                        lldpneigh = LLDPNeighborTable(jdev)
                        lldpneigh.get()
                        for local_int in lldpneigh:
                            for item in name.members:
                                print("Local Int: {}\n".format(local_int.local_int))
                                print("Member Int: {}\n".format(item.split(".")[0]))
                                if local_int.local_int == item.split(".")[0]:
                                    print("{}: {}: {}\n".format(local_int.local_int, local_int.remote_chassis_id,
                                                                 local_int.remote_sysname))
            except KeyboardInterrupt:
                print("Exiting Procedure...")
        else:
            print("\n!!! Configuration deployment aborted... No changes made !!!\n")
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
    my_options = ['Execute Operational Commands', 'Execute Set Commands', 'Execute Template Commands',
                  'Upgrade Junipers', 'Quit']
    my_ips = []

    # Get menu selection
    while True:
        stdout.write("\n\n")
        print("*" * 50 + "\n" + " " * 10 + "JSHOW: MAIN MENU\n" + "*" * 50)
        answer = getOptionAnswerIndex('Make a Selection', my_options)
        if answer == "1":
            oper_commands(my_ips)
        #elif answer == "2":
        #    standard_commands(my_ips)
        #elif answer == "3":
        #    template_commands()
        #elif answer == "4":
        #    upgrade_menu()
        elif answer == "5":
            quit()
