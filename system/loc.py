#!/usr/bin/env python3

# A tool to examine how many lines of
# source code a directory contains

import os
from sys import argv

def loc_file(path):
    with open(path) as f:
        text = f.read()
    acc = 0
    for line in text.splitlines():
        if not (len(line) == 0 or line.isspace()):
            acc += 1
    return acc

def loc(path, allow, specific = False):
    allow = set(allow)
    acc = {}
    if specific:
        for ext in allow:
            acc[ext] = 0
    for (root, dirs, files) in os.walk(path):
        for file in files:
            (_, ext) = os.path.splitext(file)
            ext = ext[1:]
            if ext in allow:
                fpath = os.path.join(root, file)
                count = loc_file(fpath)
                if ext in acc:
                    acc[ext] += count
                else:
                    acc[ext] = count
    for (k, v) in sorted(acc.items(), key = lambda t: t[1]):
        print("{:8} .{}".format(v, k))

allow_default = [
    "asm", "awk", "c", "cc", "cpp", "cxx", "cs", "css", "csv", "d",
    "h", "hh", "hpp", "hxx", "htm", "html", "xhtml", "java", "js",
    "json", "lisp", "lua", "m", "mac", "md", "ml", "pas", "pl", "py",
    "r", "rb", "rs", "scm", "sh", "tex", "toml", "txt", "v"
]

def main():
    path = "./" if len(argv) < 2 else argv[1]
    if len(argv) < 3:
        loc(path, allow_default)
    else:
        loc(path, argv[2:], specific = True)

main()
