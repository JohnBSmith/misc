
# Compute the cryptographic hash value of a file
# or directory. Metadata is not taken into account.

import os, sys
import hashlib

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

def hash(path):
    data = read(path)
    h = new_hasher()
    h.update(data)
    return h

def hash_rec(root):
    h = new_hasher()
    a = []
    for path in list_files(root):
        data = hash(path).digest()
        h.update(data)
    return h

path = sys.argv[1]
if os.path.isfile(path):
    print(hash(path).hexdigest())
elif os.path.isdir(path):
    print(hash_rec(path).hexdigest())
else:
    print("Error: path '{}' cannot be accessed.".format(path))


