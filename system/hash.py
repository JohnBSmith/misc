#!/usr/bin/env python3

# Compute the cryptographic hash value of a file
# or directory. Metadata is not taken into account.

import os, sys
import hashlib

def eprint(s):
    print(s,file=sys.stderr)

def new_hasher():
    return hashlib.sha256()

BLOCKSIZE = 2**16
def hash_file(h,path):
    with open(path,"rb") as f:
        while True:
            buf = f.read(BLOCKSIZE)
            if len(buf)==0: break
            h.update(buf)
    return h

def hash_rec(path):
    h = new_hasher()
    if os.path.isfile(path):
        h = new_hasher()
        hash_file(h,path)
        h.update(path.encode("utf-8"))
    elif os.path.isdir(path):
        a = []
        for item in os.listdir(path):
            a.append(os.path.join(path,item))
        a.sort()
        for item in a:
            hrec = hash_rec(item)
            h.update(hrec.digest())
        h.update(path.encode("utf-8"))
    else:
        eprint("Strange file detected: {}".format(path))
        sys.exit(1)
    return h

path = sys.argv[1]
if os.path.isfile(path):
    print(hash_file(new_hasher(),path).hexdigest())
elif os.path.isdir(path):
    os.chdir(path)
    print(hash_rec("./").hexdigest())
else:
    eprint("Error: path '{}' cannot be accessed.".format(path))


