
# List all files of a directory tree, sorted by size.

import os, sys

def list_by_size(root):
    a = []
    for dirpath, dnames, fnames in os.walk(root):
        for f in fnames:
            path = os.path.join(dirpath,f)
            size = os.path.getsize(path)
            a.append([size,path])
    a.sort(key = lambda t: t[0])
    return a

os.chdir(sys.argv[1])
a = list_by_size("./")
for size,path in a:
    if path[:2]=="./": path = path[2:]
    if size<1000000:
        print("{:8.3f} KB  {}".format(size/1000.0,path))
    else:
        print("{:8.3f} MB  {}".format(size/1000000.0,path))

