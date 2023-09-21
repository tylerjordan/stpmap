# File: utility.py
# Author: Tyler Jordan
# Modified: 2/23/2018
# Purpose: Assist CBP engineers with Juniper configuration tasks

import sys, re, os, csv
import fileinput
import glob
import math
import paramiko  # https://github.com/paramiko/paramiko for -c -mc -put -get
import subprocess
import datetime
import platform
import json
import operator
import time
import pprint

from os import listdir
from os.path import isfile, join, exists
from jnpr.junos import Device
from jnpr.junos.utils.config import Config
from jnpr.junos.exception import ConnectError
from jnpr.junos.exception import LockError
from jnpr.junos.exception import UnlockError
from jnpr.junos.exception import ConfigLoadError
from jnpr.junos.exception import CommitError
from ncclient import manager  # https://github.com/ncclient/ncclient
from ncclient.transport import errors
from sys import stdout

# --------------------------------------
# ANSWER METHODS
#--------------------------------------
# Method for asking a question that has a single answer, returns answer
def getOptionAnswer(question, options):
    answer = ""
    loop = 0
    while not answer:
        print("\n" + question + ':\n')
        options.append('Quit')
        for option in options:
            loop += 1
            print('[' + str(loop) + '] -> ' + option)
        answer = input('\nYour Selection: ')
        print("*" * 50)
        try:
            if int(answer) >= 1 and int(answer) <= loop:
                index = int(answer) - 1
                if options[index] == 'Quit':
                    return False
                else:
                    return options[index]
        except Exception as err:
            print("Invalid Entry - ERROR: {0}".format(err))
        else:
            print("Bad Selection")
        answer = ""
        loop = 0

# Method for asking a question that can have multiple answers, returns list of answers
def getOptionMultiAnswer(question, options):
    answer_str = ""
    loop = 0
    while not answer_str and options:
        print("\n" + question + ':\n')
        for option in options:
            loop += 1
            print('[' + str(loop) + '] -> ' + option)
        answer_str = input('\nYour Selections: ')
        print("*" * 50)
        try:
            answer_list = []
            index_list = answer_str.split(",")
            for answer in index_list:
                index = int(answer) - 1
                answer_list.append(options[index])
            return answer_list
        except Exception as err:
            print("Invalid Entry - ERROR: {0}".format(err))
        else:
            print("Bad Selection")
        answer_str = ""
        loop = 0

# Method for asking a question that has a single answer, returns answer index
def getOptionAnswerIndex(question, options):
    answer = ""
    loop = 0
    while not answer:
        print("\n" + question + ':\n')
        for option in options:
            loop += 1
            print('[' + str(loop) + '] -> ' + option)
        answer = input('\nYour Selection: ')
        print("*" * 50)
        try:
            if int(answer) >= 1 and int(answer) <= loop:
                return answer
        except Exception as err:
            print("Invalid Entry - ERROR: {0}".format(err))
        else:
            print("Bad Selection")
        answer = ""
        loop = 0

# Method for asking a user input question
def getInputAnswer(question):
    answer = ""
    while not answer:
        answer = input(question + ': ')
    return answer

# Method for asking a user input question that can have multiple answers
def getMultiInputAnswer(question):
    answer_list = []
    answer = "placeholder"
    while answer:
        answer = input(question + ': ')
        if answer:
            answer_list.append(answer)
    return answer_list

# Method for asking a Y/N question
def getYNAnswer(question):
    answer = ""
    while not answer:
        print("")
        answer = input(question + '(y/n): ')
        print("")
        if answer == 'Y' or answer == 'y':
            answer = 'y'
        elif answer == 'N' or answer == 'n':
            answer = 'n'
        else:
            print("Bad Selection")
            answer = ""
    return answer

# Method for asking a Y/N question, return True or False
def getTFAnswer(question):
    answer = False
    while not answer:
        print("")
        ynanswer = input(question + '(y/n): ')
        print("")
        if ynanswer == 'Y' or ynanswer == 'y':
            answer = True
            return answer
        elif ynanswer == 'N' or ynanswer == 'n':
            answer = False
            return answer
        else:
            print("Bad Selection")

# Return list of files from a directory with an optional extension filter
def getFileList(mypath, ext_filter=False):
    tmpList = []
    fileList = []
    if exists(mypath):
        if ext_filter:
            pattern = mypath + '*.' + ext_filter
            # Sorts the files by modification time
            tmpList = sorted([x for x in glob.glob(pattern)], key=os.path.getmtime, reverse=True)
        else:
            tmpList = sorted([x for x in glob.glob(mypath + '*')], key=os.path.getmtime, reverse=True)
        #except Exception as err:
        #    print "Error accessing files {0} - ERROR: {1}".format(mypath, err)
        for f in tmpList:
            fileList.append(f[len(mypath):])
    else:
        print("Path: {0} does not exist!".format(mypath))
    return fileList

# Method for requesting IP address target
def getTarget():
    print(64*"=")
    print("= Scan Menu" + 52*" " + "=")
    print(64*"=")
    # Loop through the IPs from the file "ipsitelist.txt"
    loop = 0
    list = {};
    for line in fileinput.input('ipsitelist.txt'):
        # Print out all the IPs/SITEs
        loop += 1
        ip,site = line.split(",")
        list[str(loop)] = ip;
        print('[' + str(loop) + '] ' + ip + ' -> ' + site.strip('\n'))

    print("[c] Custom IP")
    print("[x] Exit")
    print("\n")

    response = ""
    while not response:
        response = input("Please select an option: ")
        if response >= "1" and response <= str(loop):
            return list[response]
        elif response == "c":
            capturedIp = ""
            while not capturedIp:
                capturedIp = input("Please enter an IP: ")
                return capturedIp
        elif response == "x":
            response = "exit"
            return response
        else:
            print("Bad Selection")

# This function creates a list of IPs from the IP
def extract_ips(ip):
    iplist = []
    ip_mask_regex = re.compile("^([1][0-9][0-9].|^[2][5][0-5].|^[2][0-4][0-9].|^[1][0-9][0-9].|^[0-9][0-9].|^[0-9].)"
                               "([1][0-9][0-9].|[2][5][0-5].|[2][0-4][0-9].|[1][0-9][0-9].|[0-9][0-9].|[0-9].)"
                               "([1][0-9][0-9].|[2][5][0-5].|[2][0-4][0-9].|[1][0-9][0-9].|[0-9][0-9].|[0-9].)"
                               "([1][0-9][0-9]|[2][5][0-5]|[2][0-4][0-9]|[1][0-9][0-9]|[0-9][0-9]|[0-9])"
                               "/([8]|[9]|1[0-9]|2[0-9]|3[0-1])$")
    ip_only_regex = re.compile("^([1][0-9][0-9].|^[2][5][0-5].|^[2][0-4][0-9].|^[1][0-9][0-9].|^[0-9][0-9].|^[0-9].)"
                               "([1][0-9][0-9].|[2][5][0-5].|[2][0-4][0-9].|[1][0-9][0-9].|[0-9][0-9].|[0-9].)"
                               "([1][0-9][0-9].|[2][5][0-5].|[2][0-4][0-9].|[1][0-9][0-9].|[0-9][0-9].|[0-9].)"
                               "([1][0-9][0-9]|[2][5][0-5]|[2][0-4][0-9]|[1][0-9][0-9]|[0-9][0-9]|[0-9])$")
    if ip_mask_regex.match(ip):
        try:
            n1 = ipaddress.ip_network(ip)
        except ValueError as err:
            print("Invalid IP address - skipping {0}".format(ip))
            return iplist
        else:
            for one_ip in n1.hosts():
                print("Adding IP: {0}".format(one_ip))
                iplist.append(str(one_ip))
    elif ip_only_regex.match(ip):
        print("Adding single IP: {0}".format(ip))
        iplist.append(ip)
    else:
        print("Invalid IP Format: {0} ... Ignoring".format(ip))

    return iplist

# Common method for accessing multiple routers
def chooseDevices(list_dir):
    # Define the routers to deploy the config to (file/cli)
    # IP Formats to recognize...
    #   - 10.10.10.X        // A single IP address
    #   - 10.10.10.X/XX     // A masked IP, probably network
    ip_list = []
    looping = True

    while looping:
        method_resp = getOptionAnswer('How would you like to define the devices by IP', ['file', 'manual'])
        # Choose a file from a list of options
        if method_resp == "file":
            path = list_dir + "*.ips"
            files=glob.glob(path)
            if files:
                file_resp = getOptionAnswer('Choose a file to use', files)
                # Print out all the IPs/SITEs
                if file_resp != 'Quit':
                    for line in fileinput.input(file_resp):
                        line = line.rstrip()
                        if line != '':
                            ip_list += extract_ips(line)
                        looping = False
            else:
                print("No valid files in {0}".format(path))
        # Define one or more IPs individually
        elif method_resp == "manual":
            print('Provide IPs - Correct format: X.X.X.X or X.X.X.X/X:')
            answer = ""
            while( answer != 'x' ):
                answer = getInputAnswer('Enter an ip address (x) to exit')
                if( answer != 'x'):
                    ip_list += extract_ips(answer)
            looping = False
        else:
            print("Exiting menu...")
            return False

    # Print the IPs that will be used
    if ip_list:
        checked_sorted_list = check_sort(ip_list)
        print("\n" + " " * 10 + "IPs Selected")
        print("-" * 50)
        for ip in checked_sorted_list:
            print(' -> {0}'.format(ip))
        print("-" * 50)
        print("Total IPs: {0}".format(len(checked_sorted_list)))
        return checked_sorted_list
    else:
        return ip_list

# Removes duplicates and sorts IPs intelligently
def check_sort(ip_list):
    # First remove all duplicates
    checked = []
    for ip in ip_list:
        if ip not in checked:
            checked.append(ip)

    # Sorting function
    for i in range(len(checked)):
        checked[i] = "%3s.%3s.%3s.%3s" % tuple(checked[i].split("."))
    checked.sort()
    for i in range(len(checked)):
        checked[i] = checked[i].replace(" ", "")

    return checked

# Converts listDict to CSV file
def listDictCSV(myListDict, filePathName, keys):
    addKeys = True
    if (os.path.isfile(filePathName)):
        addKeys = False
    try:
        f = open(filePathName, 'a')
    except Exception as err:
        print("Failure opening file in append mode - ERROR: {0}".format(err))
        print("Be sure {0} isn't open in another program.".format(filePathName))
    else:
        if addKeys:
            #Write all the headings in the CSV
            for akey in keys[:-1]:							# Runs for every element, except the last
                f.write(akey + ",")							# Writes most elements
            f.write(keys[-1])								# Writes last element
            f.write("\n")

        for part in myListDict:
            for bkey in keys[:-1]:
                #print "BKey: " + bkey + "  Value: " + part[bkey]
                f.write(str(part[bkey]) + ",")
            f.write(str(part[keys[-1]]))
            f.write("\n")
        f.close()
        print("\nCompleted appending to CSV.")

# Adds a dictionary to a CSV file
def dictCSV(myDict, filePathName, keys):
    addKeys = True
    if (os.path.isfile(filePathName)):
        addKeys = False
    try:
        f = open(filePathName, 'a')
    except Exception as err:
        print("Failure opening file in append mode - ERROR: {0}".format(err))
        print("Be sure {0} isn't open in another program.".format(filePathName))
    else:
        if addKeys:
            #Write all the headings in the CSV
            for akey in keys[:-1]:							# Runs for every element, except the last
                f.write(akey + ",")							# Writes most elements
            f.write(keys[-1])								# Writes last element
            f.write("\n")

        for key in keys[:-1]:
            f.write(str(myDict[key]) + ",")
        f.write(str(myDict[keys[-1]]))
        f.write("\n")
        f.close()
        print("\nCompleted appending to CSV.")

# Converts CSV file to listDict. First line is considered column headers.
def csvListDict(fileName, keys=''):
    myListDict = []
    try:
        with open(fileName) as myfile:
            firstline = True
            for line in myfile:
                if firstline:
                    if not keys:
                        keys = "".join(line.split()).split(',')
                    firstline = False
                else:
                    values = "".join(line.split()).split(',')
                    myListDict.append({keys[n]:values[n] for n in range(0,len(keys))})
    except Exception as err:
        print("Failure converting CSV to listDict - ERROR: {0}".format(err))
    else:
        print("File Import Complete!")
    return myListDict

# Converts JSON file to Dictionary
def json_to_dict(fileName):
    file = open(fileName, 'r')
    json_data = json.load(file)
    #print(type(json_data))
    #for key, value in json_data.items():
    #    print(f"\nKey: {key}")
    #    print(f"Value: {value}\n")
    #pp = pprint.PrettyPrinter(depth=8)
    #print("PPRINT")
    #pp.pprint(json_data)
    file.close()
    return json_data

# Converts CSV file to Dictionary
def csv_to_dict(filePathName):
    input_file = csv.DictReader(open(filePathName))
    for row in input_file:
        pass
    return row

# Gets a target code
def getCode(device, mypath):
    tar_code = ""

    # Does not have a target code, let's ask for one
    print("\n" + "*"*10)
    print("Hostname: " + device.hostname)
    print("IP: " + device.ip)
    print("Model: " + device.model)
    print("Current Code: " + device.curr_code)

    fileList = getFileList(mypath)
    if fileList:
        tar_code = getOptionAnswer("Choose an image", fileList)
    else:
        print("No images available.")
    print("*"*10 + "\n")

    return tar_code

# Get fact
def get_fact(ip, username, password, fact):
    """ Purpose: For collecting a single fact from the target system. The 'fact' must be one of the predefined ones.
        Examples:
            model, version, hostname, serialnumber,
            switch_style, last_reboot_reason, uptime,
            personality
        Parameters:
    """
    myfact = ""
    dev = Device(ip, user=username, password=password)
    try:
        dev.open()
    except Exception as err:
        print("Unable to open connection to: {0} | ERROR: {1}").format(ip, err)
        return False
    else:
        try:
            myfact = dev.facts[fact]
        except Exception as err:
            print("Reachability Issues... Standby: {0} | ERROR: {1}").format(ip, err)
            dev.close()
            return False
        else:
            dev.close()
            if myfact:
                return myfact
            else:
                return False

# Takes a text string and creates a top level heading
def topHeading(raw_text, margin):
    head_length = len(raw_text)
    equal_length = head_length + 6

    heading = " " * margin + "+" + "=" * equal_length + "+\n" + \
              " " * margin + "|   " + raw_text + "   |\n" + \
              " " * margin + "+" + "=" * equal_length + "+"

    return heading

# Takes a string and creates a sub heading
def subHeading(raw_text, margin):
    head_length = len(raw_text)
    dash_length = head_length + 2

    heading = " " * margin + "o" + "-" * dash_length + "o\n" + \
              " " * margin + "| " + raw_text + " |\n" + \
              " " * margin + "o" + "-" * dash_length + "o" + "\n"

    return heading

# Takes a string and adds stars to either side
def starHeading(raw_text, head_len):
    heading = ""
    heading += "*" * head_len + "\n"
    if len(raw_text) > head_len:
        half_text_len = int(math.ceil(len(raw_text) / 2))
        half_head_len = int(head_len / 2)
        start_text = half_head_len - half_text_len
        # Create heading
        heading += " " * start_text + raw_text + "\n"
    else:
        heading += raw_text + "\n"
    heading += "*" * head_len + "\n"

    return heading

# Run a single non-edit command and get the output returned
def op_command(ip, command, username, password, port=22):
    """ Purpose: For the -c flag, this function is called. It will connect to a device, run the single specified command, and return the output.
                 Paramiko is used instead of ncclient so we can pipe the command output just like on the CLI.
        Parameters:
            ip          -   String containing the IP of the remote device, used for logging purposes.
            host_name   -   The device host-name for output purposes.
            commands    -   String containing the command to be sent to the device.
            username    -   Username used to log into the device
            password    -   Password is needed because we are using paramiko for this.
    """
    ssh = paramiko.SSHClient()
    ssh.set_missing_host_key_policy(paramiko.AutoAddPolicy())
    device = ' -> Command: %s\n' % (command)
    command = command.strip() + ' | no-more\n'
    output = ''
    try:
        ssh.connect(ip, port=port, username=username, password=password)
        stdin, stdout, stderr = ssh.exec_command(command=command, timeout=900)
        stdin.close()
        # read normal output
        while not stdout.channel.exit_status_ready():
            output += stdout.read()
        stdout.close()
        # read errors
        while not stderr.channel.exit_status_ready():
            output += stderr.read()
        stderr.close()
        output = '%s\n%s' % (device, output)
        return output
    except paramiko.AuthenticationException:
        output = '*' * 45 + '\n\nBad username or password for device: %s\n' % ip
        return output

def set_command(ip, username, password, port, log_file, command_list):
    """ Purpose: This is the function for the -s or -sl flags. it will send set command(s) to a device, and commit the change.
        Parameters:
            connection  -   The NCClient manager connection to the remote device.
            ip          -   String containing the IP of the remote device, used for logging purposes.
            host_name   -   The device host-name for output purposes.
            commands    -   String containing the set command to be sent to the device, or a list of strings of multiple set commands.
                            Either way, the device will respond accordingly, and only one commit will take place.
    """
    dot = "."

    try:
        connection = run(ip, username, password, port)
    except Exception as err:
        screen_and_log(("Connection Error with {0}: Aborting Set Operation".format(ip)), log_file)
    else:
        software_info = connection.get_software_information(format='xml')
        hostname = software_info.xpath('//software-information/host-name')[0].text

        screen_and_log(("Applying configuration on {0} ({1}) ".format(hostname, ip)), log_file)
        screen_and_log(dot, log_file)
        try:
            connection.lock()
        except Exception as err:
            screen_and_log(("{0}: Unable to Lock configuration : {1}".format(ip, err)), log_file)
            return
        screen_and_log(dot, log_file)
        # Load configuration block
        try:
            connection.load_configuration(action='set', config=command_list)
        except (ConfigLoadError, Exception) as err:
            if 'statement not found' in err.message:
                #print "Bypassing warning through message"
                pass
            #elif err.rpc_error['severity'] == 'warning':
            #    print "Bypassing warning through severity"
            #    pass
            else:
                screen_and_log(("{0}: Unable to Load the configuration : {1}".format(ip, err)), log_file)
                screen_and_log(("{0}: Unlocking the configuration".format(ip)), log_file)
                try:
                    connection.unlock()
                except Exception as err:
                    screen_and_log(("{0}: Unable to Unlock the configuration : {1}".format(ip, err)), log_file)
                connection.close_session()
                return
        screen_and_log(dot, log_file)
        # Commit configuration block
        try:
            connection.commit()
        except Exception as err:
            screen_and_log(("{0}: Commit fails : {1}".format(ip, err)), log_file)
            return
        screen_and_log(dot, log_file)
        # Unlock configuration block
        try:
            connection.unlock()
        except Exception as err:
            screen_and_log(("{0}: Unable to Unlock the configuration : {1}".format(ip, err)), log_file)
            connection.close_session()
            return
        connection.close_session()
        screen_and_log(" Completed!\n", log_file)

def enable_netconf(ip, username, password, port, log_file=None):
    """ Purpose: To enable the netconf ssh service on a device that does not have it.
    """
    netconf_command = "set system services netconf ssh"
    print("Trying to enable NETCONF on {0}").format(ip)
    try:
        set_command(ip, username, password, port, log_file, netconf_command)
    except Exception as err:
        print("Failed to enable NETCONF.")
        return False
    else:
        print("Successfully enabled NETCONF!")
        return True

def run(ip, username, password, port):
    """ Purpose: To open an NCClient manager session to the device, and run the appropriate function against the device.
        Parameters:
            ip          -   String of the IP of the device, to open the connection, and for logging purposes.
            username    -   The string username used to connect to the device.
            password    -   The string password used to connect to the device.
    """
    output = ''
    try:
        #print "{0}: Establishing connection...".format(ip)
        connection = manager.connect(host=ip,
                                     port=port,
                                     username=username,
                                     password=password,
                                     timeout=15,
                                     device_params={'name':'junos'},
                                     hostkey_verify=False)
        connection.timeout = 300
    except errors.SSHError:
        output = '*' * 45 + '\n\nUnable to connect to device: %s on port: %s\n' % (ip, port)
        print(output)
    except errors.AuthenticationError:
        output = '*' * 45 + '\n\nBad username or password for device: %s\n' % ip
        print(output)
    else:
        return connection

# Pushes the configuration using PyEZ
def load_with_pyez(dev, conf_file, output_log, ip, hostname, username, password):
    """ Purpose: Perform the actual loading of the config file. Catch any errors.
        Parameters:
            format_opt      -   defines the format of input "set" or "hierarchical"
            merge_opt       -   the merge options selection, "loadmerge"
            overwrite_opt   -   the overwrite option selection, "loadoverwrite"
            conf_file       -   the configuration file name, including path and filename
            log_file        -   the log file name, including path and filename
            ip              -   ip address of device
            hostname        -   device hostname
            username        -   username for logging in
            password        -   password for username
    """
    #print "Commands To Be Run:"
    #print conf_file
    #with open(conf_file, 'r') as f:
    #    for line in f:
    #        print(line,)
    #    f.close()
    # Procedure to load configuration
    '''
    screen_and_log("Starting load procedure on {0} ({1})\n".format(hostname, ip), output_log)
    screen_and_log("Opening a connection...", output_log)
    try:
        dev = Device(ip, user=username, password=password, auto_probe=10)
        dev.open()
    except ConnectError as err:
        err_message = "{0}: Cannot connect to device - ERROR: {1}".format(hostname, err)
        screen_and_log("\n{0}\n".format(err_message), output_log)
        return err_message
    else:
        screen_and_log("Opened!\n", output_log)
    '''
    # Bind the config to the cu object
    dev.bind(cu=Config)

    # Lock the configuration
    try:
        dev.cu.lock()
    except LockError as err:
        err_message = "Unable to lock configuration"
        screen_and_log("{0} ({1}): ERROR - {2}: {3}\n".format(ip, hostname, err_message, err), output_log)
        return err_message
    else:
        screen_and_log("{0} ({1}): Locked Configuration.\n".format(ip, hostname), output_log)

    # Load the configuration changes
    try:
        dev.cu.load(path=conf_file, merge=True, format="set")
    except (ConfigLoadError, Exception) as err:
        #if err.rpc_error['severity'] == 'warning':
        #   pass
        #elif 'statement not found' in err.message:
        #    pass
        #else:
        err_message = "Unable to load configuration"
        screen_and_log("{0} ({1}): ERROR - {2}: {3}\n".format(ip, hostname, err_message, err), output_log)
        try:
            dev.cu.unlock()
        except UnlockError as err:
            err_message = "Unable to unlock configuration"
            screen_and_log("{0} ({1}): ERROR - {2}: {3}\n".format(ip, hostname, err_message, err), output_log)
            return err_message
        else:
            return err_message
    else:
        screen_and_log("{0} ({1}): Loaded Configuration.\n".format(ip, hostname), output_log)

    # Commit the configuration changes
    try:
        dev.cu.commit()
    except CommitError as err:
        err_message = "Unable to commit configuration"
        screen_and_log("{0} ({1}): ERROR - {2}: {3}\n".format(ip, hostname, err_message, err), output_log)
        try:
            dev.cu.unlock()
        except UnlockError as err:
            err_message = "Unable to unlock configuration"
            screen_and_log("{0} ({1}): ERROR - {2}: {3}\n".format(ip, hostname, err_message, err), output_log)
            return err_message
        else:
            return err_message
    else:
        screen_and_log("{0} ({1}): Committed Configuration.\n".format(ip, hostname), output_log)

    # Unlock after a successful commit
    try:
        dev.cu.unlock()
    except UnlockError as err:
        err_message = "Unable to unlock configuration"
        screen_and_log("{0} ({1}): ERROR - {2}: {3}\n".format(ip, hostname, err_message, err), output_log)
        return err_message
    else:
        screen_and_log("{0} ({1}): Unlocked Configuration.\n".format(ip, hostname), output_log)

    # End the NETCONF session and close the connection
    err_message = "Completed"
    screen_and_log("{0} ({1}): Completed Push!\n".format(ip, hostname), output_log)
    return err_message

# Return a specifically formatted timestamp
def get_now_time():
    """ Purpose: Create a formatted timestamp

    :return:            -   String of the timestamp in "YYYY-MM-DD_HHMM" format
    """
    now = datetime.datetime.now()
    return now.strftime("%Y-%m-%d_%H%M")

# Print output to the screen and a log file (either a list or string)
def screen_and_log(statement, file_list):
    # Print to screen
    stdout.write(statement)
    stdout.flush()
    # Print to log
    if type(file_list) is list:
        for log in file_list:
            log_only(statement, log)
    else:
        log_only(statement, file_list)

# Append output to log file only
def log_only(statement, logfile):
    # Print to log
    #print "Log File: {0}".format(logfile)
    try:
        logobj = open(logfile, 'a')
    except Exception as err:
        print("Error opening log file {0}".format(err))
    else:
        logobj.write(statement)
        logobj.close()

# Creates list from a text file
def txt_to_list(txt_file):
    command_list = []
    try:
        with open(txt_file) as f:
            command_list = f.read().splitlines()
    except Exception as err:
        print("Error turning file into list. ERROR: {0}".format(err))
        return False
    else:
        return command_list

# Creates text file from a list
def list_to_txt(dest_file, src_list):
    text_config = ""
    try:
        # Overwrites an existing file, if there is one
        with open(dest_file, 'w') as text_config:
            for line in src_list:
                text_config.write("{0}\n".format(line))
    except Exception as err:
        print("Error writing list to file. ERROR: {0}".format(err))
        return False
    else:
        return True

# Creates a string from a text file
def txt_to_string(src_file):
    # Create a string of the configuration file
    command_file = ""
    try:
        with open(src_file) as f:
            command_file = f.read()
    except Exception as err:
        print("Problems extracting commands from file. ERROR: {0}".format(err))
        return False
    else:
        return command_file

# Pings the provided IP and returns True/False, works on Windows or Linux/Mac
def ping(ip):
    """ Purpose: Determine if an IP is pingable
    :param ip: IP address of host to ping
    :return: True if ping successful
    """
    with open(os.devnull, 'w') as DEVNULL:
        try:
            # Check for Windows or Linux/MAC
            ping_param = "-n" if platform.system().lower() == "windows" else "-c"
            subprocess.check_call(
                ['ping', ping_param, '3', ip],
                stdout=DEVNULL,
                stderr=DEVNULL
            )
            return True
        except subprocess.CalledProcessError:
            return False
# Get key based on value
def host_from_ip(dict, val):
    for key, value in dict.items():
        if val == value:
            return key
    return None

# Clear out any duplicates from the provided list
def remove_duplicates(alist):
    nodup_list = []
    for i in alist:
        if i not in nodup_list:
            nodup_list.append(i)
        #else:
            #print(i,end=' ')
    return nodup_list
