#!/usr/bin/env python3

# hash-list PATH -o list.json
# Compute the hash values of all files in the given directory tree.

# hash-list PATH list.json
# Compare the hash values with the given directory tree to detect
# changes.

# Note: This is not a Merkle tree, as the directories itself are
# omitted from hashing.

import os, sys
import hashlib
import json

log = False

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

def list_files(root):
    a = []
    for dirpath, dnames, fnames in os.walk(root):
        for f in fnames:
            path = os.path.join(dirpath,f)
            a.append(path)
    a.sort()
    return a

def hash_rec(root):
    a = []
    file_list = list_files(root)
    n = len(file_list)
    for k, path in enumerate(file_list):
        if log: print("[{} of {}] {}".format(k+1,n,path))
        digest = hash_file(new_hasher(),path).hexdigest()
        a.append([path,digest])
    return a

def write_file(path,text):
    with open(path,"w") as f:
        f.write(text)

def generate(output_path):
    path = sys.argv[1]
    if os.path.isfile(path):
        digest = hash_file(new_hasher(),path).hexdigest()
        value = [[os.path.basename(path),digest]]
    elif os.path.isdir(path):
        os.chdir(path)
        value = hash_rec("./")
    else:
        eprint("Error: path '{}' cannot be accessed.".format(path))
        sys.exit(1)
    write_file(output_path,json.dumps(value,indent=0))

def read_hashlist(path):
    with open(path) as f:
        return json.loads(f.read())

def compare(hashlist_path):
    a = read_hashlist(hashlist_path)
    if os.path.isdir(sys.argv[1]):
        os.chdir(sys.argv[1])
    else:
        fpath,fname = os.path.split(sys.argv[1])
        os.chdir(fpath)
    diff_list = []
    n = len(a)
    for k, (path, hpath) in enumerate(a):
        if log: print("[{} of {}] {}".format(k+1,n,path))
        if os.path.exists(path):
            h = hash_file(new_hasher(),path).hexdigest()
            if h!=hpath:
                diff_list.append(path)
        else:
            diff_list.append("[file not found] "+path)
    if len(diff_list)==0:
        print("All files match.")
    else:
        print("Detected modified files:")
        for path in diff_list:
            print(path)

if len(sys.argv)==4:
    output_path = os.path.join(os.getcwd(),sys.argv[3])
    if "l" in sys.argv[2]: log = True
    if "o" in sys.argv[2]:
        generate(output_path)
    else:
        compare(sys.argv[3])
elif len(sys.argv)==3:
    compare(sys.argv[2])
else:
    eprint("Usage: hash-list PATH -o FILE.json")
    eprint("check: hash-list PATH FILE.json")
    sys.exit(1)

