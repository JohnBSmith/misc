#!/usr/bin/env python3
from subprocess import run
from sys import argv, exit

files = ["MK.txt", "logic.txt", "logic-eq.txt", "basic.txt"]

if len(argv) == 2:
    if argv[1] == "-e":
        for file in files:
            run(["ndexport.py", file])
        exit(0)
    elif argv[1] == "-c":
        run(["ndexport.py", "--clear"])
        exit(0)
    else:
        acc = []
        for file in files:
            if file != argv[1]:
                acc.append("./lib/" + file)
            else:
                acc.append(file)
                break
        files = acc

run(["nd.py"] + files)