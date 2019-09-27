
# hash-tree PATH > list.json
# Compute the hash tree of PATH.

# hash-tree PATH list.json
# Compare the hash tree with the given directory tree to detect
# changes.

import os, sys
import hashlib
import json

def new_hasher():
    return hashlib.sha256()

def read(path):
    with open(path,"rb") as file:
        return file.read()

def hash_file(path):
    data = read(path)
    h = new_hasher()
    h.update(data)
    return h

def hash_rec(hashlist,path):
    h = new_hasher()
    if os.path.isfile(path):
        h = new_hasher()
        h.update(read(path))
    elif os.path.isdir(path):
        a = []
        for item in os.listdir(path):
            a.append(os.path.join(path,item))
        a.sort()
        for item in a:
            digest = hash_rec(hashlist,item)
            h.update(digest)
    hashlist.append([path,h.hexdigest()])
    return h.digest()

def hash_tree(path):
    hashlist = []
    hash_rec(hashlist,path)
    return hashlist

def generate():
    path = sys.argv[1]
    if os.path.isfile(path):
        value = [[path,hash_file(path).hexdigest()]]
    elif os.path.isdir(path):
        os.chdir(path)
        value = hash_tree("./")
    else:
        print("Error: path '{}' cannot be accessed.".format(path))
        sys.exit(1)
    return value

def read_hashlist(path):
    with open(path) as f:
        return json.loads(f.read())

def compare():
    a = read_hashlist(sys.argv[2])
    b = dict(generate())
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

if len(sys.argv)==2:
    value = generate()
    print(json.dumps(value,indent=0))
else:
    compare()

