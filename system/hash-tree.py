#!/usr/bin/env python3

# hash-tree PATH -o HASHES.json
# Compute the hash tree of PATH.

# hash-tree PATH HASHES.json
# Compare the hash tree with the given directory tree to detect
# changes.

import os, sys
import hashlib
import json

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

def hash_rec(hashlist,path):
    h = new_hasher()
    if os.path.isfile(path):
        hash_file(h,path)
    elif os.path.isdir(path):
        a = []
        for item in os.listdir(path):
            a.append(os.path.join(path,item))
        a.sort()
        for item in a:
            digest = hash_rec(hashlist,item)
            h.update(digest)
        h.update("\x00".join(a).encode("utf-8"))
    hashlist.append([path,h.hexdigest()])
    return h.digest()

def hash_tree(path):
    hashlist = []
    hash_rec(hashlist,path)
    return hashlist

def generate(path):
    if os.path.isfile(path):
        digest = hash_file(new_hasher(),path).hexdigest()
        value = [[os.path.basename(path),digest]]
    elif os.path.isdir(path):
        os.chdir(path)
        value = hash_tree("./")
    else:
        eprint("Error: path '{}' cannot be accessed.".format(path))
        sys.exit(1)
    return value

def read_hashlist(path):
    with open(path) as f:
        return json.loads(f.read())

def compare(ipath, hash_list_path):
    a = read_hashlist(hash_list_path)
    b = dict(generate(ipath))
    diff_list = []
    for path, hpath in a:
        if path in b:
            h = b[path]
            if h!=hpath:
                diff_list.append(path)
    if len(diff_list)==0:
        print("All items match.")
    else:
        print("Detected modified items:")
        for path in diff_list:
            print(path)

def write_file(path,text):
    with open(path,"w") as f:
        f.write(text)

def usage():
    eprint("Usage: hash-tree PATH -o HASHES.json")
    eprint("check: hash-tree PATH HASHES.json")
    sys.exit(1)

if len(sys.argv)==4:
    if "o" in sys.argv[2]:
        opath = os.path.join(os.getcwd(), sys.argv[3])
        if os.path.exists(opath):
            eprint("Error: path {} already exists.".format(opath))
            sys.exit(1)
        hash_list = generate(sys.argv[1])
        write_file(opath, json.dumps(hash_list, indent=0))
    else:
        usage()
elif len(sys.argv)==3:
    compare(sys.argv[1], sys.argv[2])
else:
    usage()

