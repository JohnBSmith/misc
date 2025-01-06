#!/usr/bin/env python3

# Translates IMP to Python

from sys import argv
from imp import read, scan, parse, C, SyntaxError

py_escape = {"True", "False", "sgn", "div", "abs"}
precedence = {
    "or": 10, "and": 20, "not": 30, "=": 40, "<=": 40,
    "+": 50, "-": 50, "*": 60, "/": 5
}

div_needed = False
div_impl = """\
def sgn(x):
    return 0 if x == 0 else -1 if x < 0 else 1

def div(x, y):
    return 0 if y == 0 else sgn(y)*(x//abs(y))
"""

def ident(a):
    return a + "_" if a in py_escape else a

def A(a, parent_prec = 0):
    global div_needed
    if type(a) is int:
        return a
    if type(a) is str:
        return ident(a)
    else:
        op = a[0]; prec = precedence[op]
        x = A(a[1], prec); y = A(a[2], prec)
        if op == "+":
            s = f"{x} + {y}"
        elif op == "-":
            s = f"{x} - {y}"
        elif op == "*":
            s = f"{x}*{y}"
        elif op == "/":
            div_needed = True
            s = f"div({x}, {y})"
        return f"({s})" if prec <= parent_prec else s
    raise ValueError("unreachable")

def B(b, parent_prec = 0):
    if type(b) is bool:
        return b
    elif type(b) is tuple:
        op = b[0]; prec = precedence[op]
        if op == "not":
            s = f"not {B(b[1], prec)}"
        elif op == "and":
            s = f"{B(b[1], prec)} and {B(b[2], prec)}"
        elif op == "or":
            s = f"{B(b[1], prec)} or {B(b[2], prec)}"
        elif op == "=":
            s = f"{A(b[1])} == {A(b[2])}"
        elif op == "<=":
            s = f"{A(b[1])} <= {A(b[2])}"
        return f"({s})" if prec <= parent_prec else s
    raise ValueError("unreachable")

def add_line(acc, s, indent):
    acc.append(" "*indent + s)

def C(c, acc, indent):
    if type(c) is tuple:
        op = c[0]
        if op == "skip":
            add_line(acc, "pass", indent)
        elif op == ":=":
            add_line(acc, f"{ident(c[1])} = {A(c[2])}", indent)
        elif op == ";":
            C(c[1], acc, indent)
            C(c[2], acc, indent)
        elif op == "if":
            add_line(acc, f"if {B(c[1])}:", indent)
            C(c[2], acc, indent + 4)
            if not (type(c[3]) is tuple and c[3][0] == "skip"):
                add_line(acc, "else:", indent)
                C(c[3], acc, indent + 4)
        elif op == "while":
            add_line(acc, f"while {B(c[1])}:", indent)
            C(c[2], acc, indent + 4)
        elif op == "print":
            add_line(acc, f"print({A(c[1])})", indent)
    else:
        raise ValueError("unreachable")

def main():
    source_code = read(argv[1])
    try:
        tokens = scan(source_code)
        c = parse(tokens)
        acc = []
        s = C(c, acc, 0)
        if div_needed:
            print(div_impl)
        print("\n".join(acc))
    except SyntaxError as e:
        print(f"Syntax error in line {e.line + 1}, col {e.col + 1}:")
        print(f"{e.text}.")

main()
