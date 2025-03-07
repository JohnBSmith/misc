#!/usr/bin/env python3

# A tool that exports already proven theorems
# to shorten the loading time.

from sys import argv
from os.path import join, isdir
from os import mkdir
from shutil import rmtree

def consume_ident(s, n, i):
    while i < n and (s[i].isalpha() or s[i].isdigit() or s[i] in "_'"):
        i += 1
    return i

def consume_space(s, n, i):
    while i < n and s[i].isspace():
        i += 1
    return i

def consume_until_comma(s, n, i):
    bracket_level = 0
    while i < n:
        if s[i] == ',' and bracket_level == 0:
            break
        elif s[i] in "{(": bracket_level += 1
        elif s[i] in "})": bracket_level -= 1
        i += 1
    return i

def export_named(s):
    i = 0; n = len(s)
    acc = []
    while i < n:
        if s[i] == '\n' and i + 1 < n and (s[i+1].isalpha() or s[i+1] == '_'):
            i += 1
            j = consume_ident(s, n, i)
            j = consume_space(s, n, j)
            if not (j < n and s[j] == '.'):
                i = j
                continue
            j += 1
            while j < n and not s[j] in "|(⊢":
                j += 1
            j = consume_until_comma(s, n, i)
            k = consume_space(s, n, j + 1)
            if k + 2 < n and s[k:k+3] == "def":
                tail = "def"
            else:
                tail = "axiom"
            acc.append(s[i:j] + f", {tail}.")
            i = j
        elif s[i] == '(' and i + 1 < n and s[i + 1] == '*':
            i += 2
            while i < n:
                if s[i] == '*' and i + 1 < n and s[i + 1] == ')':
                    i += 2
                    break
                i += 1
        else:
            i += 1
    return "\n".join(acc)

def main():
    if len(argv) == 2:
        if argv[1] == "--clear":
            rmtree("./lib")
            return
        else:
            opath = join("./lib/", argv[1])
            if not isdir("./lib"):
                mkdir("./lib")
    else:
        opath = argv[2]
    with open(argv[1], "r") as fin:
        s = fin.read()
    s_ex = export_named(s)
    with open(opath, "w") as fout:
        fout.write(s_ex)

main()
