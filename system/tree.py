#!/usr/bin/env python3

import sys, os

def print_tree(t,a,node):
    if isinstance(t,str):
        print("".join(a[:-1])+node+str(t))
    else:
        print("".join(a[:-1])+node+t[0])
        n = len(t)-2
        for i, x in enumerate(t[1:]):
            if i==n:
                print_tree(x,a+["   "],"└─ ")
            else:
                print_tree(x,a+["│  "],"├─ ")

def list_dir(path,name,depth):
    if depth==0 or not os.path.isdir(path):
        return name
    else:
        try:
            a = os.listdir(path)
            a.sort()
            b = [name]
            for item in a:
                item_path = os.path.join(path,item)
                b.append(list_dir(item_path,item,depth-1))
            return b
        except PermissionError:
            return name

def main():
    path = sys.argv[1]
    depth = int(sys.argv[2]) if len(sys.argv)==3 else -1
    t = list_dir(path,path,depth)
    print_tree(t,[],"")

main()
