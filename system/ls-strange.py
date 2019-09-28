#!/usr/bin/env python3

# List strange files, i.e. all files that are
# symbolic links, sockets or device files.

import sys, os

def list_strange(counter,path):
    if os.path.islink(path):
        print("Symbolic link detected: {}".format(path))
        counter["value"]+=1
    elif os.path.isfile(path):
        pass
    elif os.path.isdir(path):
        try:
            a = os.listdir(path)
            a.sort()
            for item in a:
                list_strange(counter,os.path.join(path,item))
        except PermissionError as e:
            print(e)
    else:
        print("Strange file detected: {}".format(path))
        counter["value"]+=1

try:
    counter = {"value": 0}
    list_strange(counter,sys.argv[1])
    n = counter["value"]
    if n>4:
        print("----")
        print("Detected {} strange files.\n".format(n))
except KeyboardInterrupt:
    print()

