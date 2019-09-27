
# hash-list PATH > list.json
# Compute the hash values of all files in the given directory tree.

# hash-list PATH list.json
# Compare the hash values with the given directory tree to detect
# changes.

# Note: This is not a Merkle tree, as the directories itself are
# omitted from hashing.

import os, sys
import hashlib
import json

def new_hasher():
    return hashlib.sha256()

def read(path):
    with open(path,"rb") as file:
        return file.read()

def list_files(root):
    a = []
    for dirpath, dnames, fnames in os.walk(root):
        for f in fnames:
            path = os.path.join(dirpath,f)
            a.append(path)
    a.sort()
    return a

def hash_file(path):
    data = read(path)
    h = new_hasher()
    h.update(data)
    return h

def hash_rec(root):
    a = []
    for path in list_files(root):
        digest = hash_file(path).hexdigest()
        a.append([path,digest])
    return a

def generate():
    path = sys.argv[1]
    if os.path.isfile(path):
        value = [path,hash_file(path).hexdigest()]
    elif os.path.isdir(path):
        os.chdir(path)
        value = hash_rec("./")
    else:
        print("Error: path '{}' cannot be accessed.".format(path))
        sys.exit(1)
    
    print(json.dumps(value,indent=0))

def read_hashlist(path):
    with open(path) as f:
        return json.loads(f.read())

def compare():
    a = read_hashlist(sys.argv[2])
    os.chdir(sys.argv[1])
    diff_list = []
    for path, hpath in a:
        h = hash_file(path).hexdigest()
        if h!=hpath:
            diff_list.append(path)
    if len(diff_list)==0:
        print("All files match.")
    else:
        print("Detected modified files:")
        for path in diff_list:
            print(path)

if len(sys.argv)==2:
    generate()
else:
    compare()

