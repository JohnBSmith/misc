#!/usr/bin/env python3

from sys import argv
from os import listdir
from os.path import splitext
from subprocess import run

def check(file_path):
    print(file_path)
    run(["parity", file_path, file_path + ".parity"])
    print()

def main():
    path = argv[1] if len(argv) > 1 else "."
    files = []
    for f in listdir(path):
        root, ext = splitext(f)
        if ext == ".parity":
            files.append(root)
    files.sort()
    for file_path in files:
        check(file_path)

main()

