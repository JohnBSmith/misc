
# List strange files, i.e. all files that are
# symbolic links, sockets or device files.

import sys, os

def list_strange(path):
    if os.path.islink(path):
        print("Symbolic link detected: {}".format(path))
    elif os.path.isfile(path):
        pass
    elif os.path.isdir(path):
        try:
            a = os.listdir(path)
            a.sort()
            for item in a:
                list_strange(os.path.join(path,item))
        except PermissionError as e:
            print(e)
    else:
        print("Strange file detected: {}".format(path))

try:
    list_strange(sys.argv[1])
except KeyboardInterrupt:
    print()

