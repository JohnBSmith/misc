#!/usr/bin/env python3

# Compiler for the IMP programming language

from sys import argv
from imp import read, scan, parse, idiv, SyntaxError

operations = [
    "add", "sub", "mul", "div", "not", "and", "or", "eq", "le",
    "load", "store", "push", "jmp", "jz", "halt", "print", "alloc"
]
opcode = dict((op, code) for (code, op) in enumerate(operations))

def invert(d):
    return dict((y, x) for (x, y) in d.items())

def variable_map(t, var_map, count):
    if type(t) is str:
        if not t in var_map:
            var_map[t] = count
            return count + 1
        else:
            return count
    elif type(t) is tuple:
        for x in t[1:]:
            count = variable_map(x, var_map, count)
        return count
    else:
        return count
        
op_map = {
    "+": "add", "-": "sub", "*": "mul", "/": "div",
    "not": "not", "and": "and", "or": "or", "=": "eq", "<=": "le"
}

def compile_aexp(a, acc, var_map):
    if type(a) is str:
        acc.append(opcode["load"])
        acc.append(var_map[a])
    elif type(a) is int:
        acc.append(opcode["push"])
        acc.append(a)
    elif type(a) is tuple:
        op = a[0]
        for x in a[1:]:
            compile_aexp(x, acc, var_map)
        acc.append(opcode[op_map[op]])
    else:
        raise ValueError("todo")

def compile_bexp(b, acc, var_map):
    if type(b) is bool:
        if b:
            acc.append(opcode["push"])
            acc.append(1)
        else:
            acc.append(opcode["push"])
            acc.append(0)        
    elif type(b) is tuple:
        if b[0] in ("=", "<="):
            compile_aexp(b[1], acc, var_map)
            compile_aexp(b[2], acc, var_map)
            acc.append(opcode[op_map[b[0]]])
        elif b[0] in ("not", "and", "or"):
            op = b[0]
            for x in b[1:]:
                compile_bexp(x, acc, var_map)
            acc.append(opcode[op_map[op]])
        else:
            raise ValueError("unreachable")
    else:
        raise ValueError("unreachble")

def compile_command(c, acc, var_map):
    if type(c) is tuple:
        if c[0] == ":=":
            compile_aexp(c[2], acc, var_map)
            acc.append(opcode["store"])
            acc.append(var_map[c[1]])
        elif c[0] == "skip":
            pass
        elif c[0] == ";":
            compile_command(c[1], acc, var_map)
            compile_command(c[2], acc, var_map)
        elif c[0] == "if":
            compile_bexp(c[1], acc, var_map)
            acc.append(opcode["jz"])
            index0 = len(acc)
            acc.append("dummy")
            compile_command(c[2], acc, var_map)
            acc.append(opcode["jmp"])
            index1 = len(acc)
            acc.append("dummy")
            acc[index0] = len(acc)
            compile_command(c[3], acc, var_map)
            acc[index1] = len(acc)
        elif c[0] == "while":
            cond = c[1]; body = c[2]
            index0 = len(acc)
            compile_bexp(cond, acc, var_map)
            acc.append(opcode["jz"])
            index1 = len(acc)
            acc.append("dummy")
            compile_command(body, acc, var_map)
            acc.append(opcode["jmp"])
            acc.append(index0)
            acc[index1] = len(acc)
        elif c[0] == "print":
            compile_aexp(c[1], acc, var_map)
            acc.append(opcode["print"])
        else:
            raise ValueError("unreachable")
    else:
        raise ValueError("unreachable")

def compile(c):
    var_map = {}
    count = variable_map(c, var_map, 0)
    acc = []
    if count != 0:
        acc.append(opcode["alloc"])
        acc.append(count)
    compile_command(c, acc, var_map)
    acc.append(opcode["halt"])
    return acc

def disassemble(program):
    decode_op = invert(opcode)
    i = 0; n = len(program)
    acc = []
    while i < n:
        op = decode_op[program[i]]
        if op in ("load", "store", "push", "jmp", "jz", "alloc"):
            acc.append(f"{i:04} {op} {program[i + 1]}")
            i += 2
        elif op in ("add", "sub", "mul", "div", "not", "and", "or",
            "eq", "le", "halt", "print"):
            acc.append(f"{i:04} {op}")
            i += 1
        else:
            raise ValueError("unreachable")
    return "\n".join(acc)

def load_dispatch_table():
    def add(stack, program, ip):
        y = stack.pop(); x = stack.pop()
        stack.append(x + y)
        return ip + 1
    def sub(stack, program, ip):
        y = stack.pop(); x = stack.pop()
        stack.append(x - y)
        return ip + 1
    def mul(stack, program, ip):
        y = stack.pop(); x = stack.pop()
        stack.append(x * y)
        return ip + 1
    def div(stack, program, ip):
        y = stack.pop(); x = stack.pop()
        stack.append(idiv(x, y))
        return ip + 1
    def land(stack, program, ip):
        y = stack.pop(); x = stack.pop()
        stack.append(0 if x == 0 else y)
        return ip + 1
    def lor(stack, program, ip):
        y = stack.pop(); x = stack.pop()
        stack.append(1 if x == 1 else y)
        return ip + 1
    def lnot(stack, program, ip):
        x = stack.pop()
        stack.append(1 if x == 0 else 0)
        return ip + 1
    def eq(stack, program, ip):
        y = stack.pop(); x = stack.pop()
        stack.append(1 if x == y else 0)
        return ip + 1
    def le(stack, program, ip):
        y = stack.pop(); x = stack.pop()
        stack.append(1 if x <= y else 0)
        return ip + 1
    def push(stack, program, ip):
        stack.append(program[ip + 1])
        return ip + 2
    def load(stack, program, ip):
        index = program[ip + 1]
        value = stack[index]
        stack.append(value)
        return ip + 2
    def store(stack, program, ip):
        index = program[ip + 1]
        value = stack.pop()
        stack[index] = value
        return ip + 2
    def jmp(stack, program, ip):
        return program[ip + 1]
    def jz(stack, program, ip):
        cond = stack.pop()
        if cond == 0:
            return program[ip + 1]
        else:
            return ip + 2
    def println(stack, program, ip):
        print(stack.pop())
        return ip + 1
    def alloc(stack, program, ip):
        count = program[ip + 1]
        stack.extend([0]*count)
        return ip + 2
    def halt(stack, program, ip):
        return ip
    return dict((opcode[key], value) for (key, value) in {
        "add": add, "sub": sub, "mul": mul, "div": div,
        "and": land, "or": lor, "not": lnot, "eq": eq, "le": le,
        "push": push, "load": load, "store": store, "jmp": jmp,
        "jz": jz, "alloc": alloc, "print": println, "halt": halt
    }.items())

def run(program):
    dispatch = load_dispatch_table()
    ip = 0
    stack = []
    while True:
        op = program[ip]
        ip_last = ip
        ip = dispatch[op](stack, program, ip)
        if ip == ip_last:
            break

def main():
    if argv[1] == "--run":
        path = argv[2]
        run_program = True
    else:
        path = argv[1]
        run_program = False
    source_code = read(path)
    try:
        tokens = scan(source_code)
        c = parse(tokens)
        program = compile(c)
        if run_program:
            run(program)
        else:
            print(disassemble(program))
    except SyntaxError as e:
        print(f"Syntax error in line {e.line + 1}, col {e.col + 1}:")
        print(f"{e.text}.")

main()
