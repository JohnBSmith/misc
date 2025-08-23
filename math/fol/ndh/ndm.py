#!/usr/bin/env python3

USAGE = """\
The nd make tool. Verifies proofs, respecting dependencies
stated in manifest.txt.

ndm.py
    Verifies all proof modules listed in manifest.txt.

ndm.py proofs.txt
    Verifies the proofs in proofs.txt. Needs the library ./lib/

ndm.py -e
    Export all theorems. Creates the library ./lib/

ndm.py -c
    Clear. Removes the library ./lib/
"""

from subprocess import run
from sys import argv, exit

def parse_manifest(s):
    lines = s.splitlines()
    clean = []
    for line in lines:
        if "#" in line:
            line = line.split("#", 1)[0]
        clean.append(line)
    s = "".join(clean)
    acc = []; i = 0
    while i < len(s):
        if s[i] == "(":
            j = s.find(")", i + 1)
            if j == -1: break
            inner = s[i+1:j].strip()
            if ":" in inner:
                name_part, deps_part = inner.split(":", 1)
                name = name_part.strip()
                deps = deps_part.strip().split()
                acc.append((name, deps))
            i = j + 1
        else:
            i += 1
    return acc

def main():
    if len(argv) == 2 and argv[1] in ("-h", "--help"):
        print(USAGE)
        exit(0)
    with open("manifest.txt", "r") as manifest:
        modules = parse_manifest(manifest.read())
    if len(argv) == 2:
        if argv[1] == "-e":
            for (m, _) in modules:
                run(["ndexport.py", m + ".txt"])
            exit(0)
        elif argv[1] == "-l":
            for (m, _) in modules:
                run(["ndexport.py", m + ".txt", "/dev/stdout"])
                print()
            exit(0)
        elif argv[1] == "-doc":
            files = [m + ".txt" for (m, _) in modules]
            run(["nddoc.py"] + files)
            exit(0)
        elif argv[1] == "-c":
            run(["ndexport.py", "--clear"])
            exit(0)
        else:
            if argv[1][-4:] == ".txt":
                mod = argv[1][:-4]
            else:
                mod = argv[1]
            modules = dict(modules)
            dependencies = modules[mod]
            files = []
            for m in dependencies:
                files.append(f"./lib/{m}.txt")
            files.append(mod + ".txt")
    else:
        files = [m + ".txt" for (m, _) in modules]
    # run(["nd.py"] + files)
    run(["nd"] + files)

main()
