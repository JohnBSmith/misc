#!/usr/bin/env python3
from subprocess import run
from sys import argv, exit

modules = [
    ("MK", []),
    ("logic", ["MK"]),
    ("basic", ["MK", "logic"]),
    ("relations", ["MK", "logic", "basic"])
]

if len(argv) == 2:
    if argv[1] == "-e":
        for (m, _) in modules:
            run(["ndexport.py", m + ".txt"])
        exit(0)
    elif argv[1] == "-c":
        run(["ndexport.py", "--clear"])
        exit(0)
    else:
        modules = dict(modules)
        dependencies = modules[argv[1]]
        files = []
        for m in dependencies:
            files.append(f"./lib/{m}.txt")
        files.append(argv[1] + ".txt")
else:
    files = [m + ".txt" for (m, _) in modules]

run(["nd.py"] + files)
