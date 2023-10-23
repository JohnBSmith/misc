
from sys import argv
from subprocess import run

def coqc(name):
    run(["coqc", name + ".v"])
    run(["rm", name + ".vok"])
    run(["rm", name + ".vos"])
    run(["rm", name + ".glob"])

def build(modules):
    if len(argv) == 2 and argv[1] == "clean":
        for name in modules:
            run(["rm", name + ".vo"])
            run(["rm", "." + name + ".aux"])
    else:
        for name in modules:
            coqc(name)

build([
    "axioms",
    "basic",
    "relations",
    "mappings",
    "order_sc",
    "closures",
    "card",
    "nat"
])
