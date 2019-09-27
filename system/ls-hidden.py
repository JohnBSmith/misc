
# List all hidden files and hidden directories.

import os, sys

def list_hidden(root):
    for dirpath, dnames, fnames in os.walk(root):
        for f in fnames:
            if f[0]==".":
                print("[Hidden file]",os.path.join(dirpath,f))
        for d in dnames:
            if d[0]==".":
                print("[Hidden dir.]",os.path.join(dirpath,d))

list_hidden(sys.argv[1])


