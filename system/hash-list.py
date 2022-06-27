#!/usr/bin/env python3

# hash-list PATH -o list.json
# Compute the hash values of all files in the given directory tree.

# hash-list PATH list.json
# Compare the hash values with the given directory tree to detect
# changes.

# hash-list old.json -c new.json
# Compare the hash values with an older list to detect changes.

# Note: This is not a Merkle tree, as the directories itself are
# omitted from hashing.

import os, sys, hashlib, json

log = False

def eprint(s):
    print(s, file = sys.stderr)

def new_hasher():
    return hashlib.sha256()

BLOCKSIZE = 2**16
def hash_file(h, path):
    with open(path, "rb") as f:
        while True:
            buf = f.read(BLOCKSIZE)
            if len(buf) == 0: break
            h.update(buf)
    return h

def list_files(root):
    a = []
    for dirpath, dnames, fnames in os.walk(root):
        for f in fnames:
            path = os.path.join(dirpath, f)
            a.append(path)
    a.sort()
    return a

def hash_rec(root):
    a = []
    file_list = list_files(root)
    n = len(file_list)
    for k, path in enumerate(file_list):
        if log: print("[{} of {}] {}".format(k + 1, n, path))
        digest = hash_file(new_hasher(), path).hexdigest()
        a.append([path, digest])
    return a

def write_file(path, text):
    with open(path, "w") as f:
        f.write(text)

def generate(path):
    if os.path.isfile(path):
        digest = hash_file(new_hasher(), path).hexdigest()
        return [[os.path.basename(path), digest]]
    elif os.path.isdir(path):
        os.chdir(path)
        return hash_rec("./")
    else:
        eprint("Error: path '{}' cannot be accessed.".format(path))
        sys.exit(1)

def read_hashlist(path):
    with open(path) as f:
        return json.loads(f.read())

def inv_dict(a):
    d = {}
    for value, key in a:
        if key in d:
            d[key].append(value)
        else:
            d[key] = [value]
    return d

def compare(old, new):
    new_inv = inv_dict(new)
    new = dict(new)
    diff_list = []
    none_list = []
    move_list = []
    for path, h in old:
        if path in new:
            if h != new[path]: diff_list.append(path)
        else:
            if h in new_inv:
                move_list.append([path, new_inv[h]])
            else:
                none_list.append(path)
    if len(diff_list) + len(none_list) + len(move_list) == 0:
        print("All files match.")
    else:
        if len(move_list) != 0:
            print("Detected moved files:")
            for src, dest in move_list:
                print("{} to {}".format(src, ", ".join(dest)))
            print()
        if len(diff_list) + len(none_list) != 0:
            print("Detected modified files:")
            for path in diff_list:
                print(path)
            for path in none_list:
                print("[file not found]", path)
            print()

def compare_list_list(hl_path_old, hl_path_new):
    old = read_hashlist(hl_path_old)
    new = read_hashlist(hl_path_new)
    return compare(old, new)

def compare_dir_list(dir_path, hashlist_path):
    old = read_hashlist(hashlist_path)
    new = generate(dir_path)
    return compare(old, new)

if len(sys.argv) == 4:
    output_path = os.path.join(os.getcwd(), sys.argv[3])
    if "l" in sys.argv[2]: log = True
    if "o" in sys.argv[2]:
        if os.path.exists(output_path):
            eprint("Error: path {} already exists.".format(output_path))
            sys.exit(1)
        value = generate(sys.argv[1])
        write_file(output_path, json.dumps(value, indent = 0))
    elif "c" in sys.argv[2]:
        compare_list_list(sys.argv[1], sys.argv[3])
    else:
        compare_dir_list(sys.argv[1], sys.argv[3])
elif len(sys.argv) == 3:
    compare_dir_list(sys.argv[1], sys.argv[2])
else:
    eprint("Usage: hash-list PATH -o FILE.json")
    eprint("check: hash-list PATH FILE.json")
    eprint("check: hash-list OLD.json -c NEW.json")
    sys.exit(1)

