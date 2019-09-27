
# List all hidden files and hidden directories.

import os, sys

def list_hidden(root):
    counter = 0
    for dirpath, dnames, fnames in os.walk(root):
        for f in fnames:
            if f[0]==".":
                print("[Hidden file]",os.path.join(dirpath,f))
                counter+=1
        for d in dnames:
            if d[0]==".":
                print("[Hidden dir.]",os.path.join(dirpath,d))
                counter+=1
    if counter>4:
        print("----")
        print("Detected {} hidden files.\n".format(counter))

list_hidden(sys.argv[1])


