#!/usr/bin/env python3

# Interpreter for the IMP programming language. The input is converted
# into an abstract syntax tree, which is then executed according to the
# denotational semantics.

# Interpreter für die Programmiersprache IMP. Es findet eine Umwandlung
# der Eingabe in einen abstrakten Syntaxbaum statt. Dieser wird darauf-
# hin gemäß der denotationellen Semantik ausgeführt.

from sys import argv

def read(path):
    with open(path) as f:
        return f.read()

class SyntaxError(ValueError):
    def __init__(self, line, col, text):
        self.line = line; self.col = col; self.text = text

class Token():
    def __init__(self, kind, value, line, col):
        self.kind = kind; self.value = value
        self.line = line; self.col = col
    def __repr__(self):
        kind = str(self.kind); value = str(self.value)
        line = str(self.line); col = str(self.col)
        return f"({kind}, {value}, {line}, {col})"

IDENT = "identifier"
SYMBOL = "symbol"
INT = "integer"

KEYWORDS = {"true", "false", "not", "and", "or",
    "if", "then", "else", "end", "while", "do", "skip", "print"}

def scan(s):
    i = 0; n = len(s)
    tokens = []; line = 0; col = 0
    while i < n:
        if s[i].isalpha():
            j = i; col_start = col
            while i < n and (s[i].isalpha() or s[i].isdigit()):
                i += 1; col += 1
            t = Token(IDENT, s[j:i], line, col_start)
            if t.value in KEYWORDS:
                t.kind = SYMBOL
            tokens.append(t)
        elif s[i].isdigit():
            j = i; col_start = col
            while i < n and s[i].isdigit():
                i += 1; col +=1
            tokens.append(Token(INT, int(s[j:i]), line, col_start))
        elif s[i].isspace():
            if s[i] == "\n":
                i +=1; line += 1; col = 0
            else:
                i += 1; col += 1
        elif s[i] == '<' and i + 1 < n and s[i+1] == '=':
            tokens.append(Token(SYMBOL, "<=", line, col))
            i += 2; col += 2
        elif s[i] == ':' and i + 1 < n and s[i+1] == '=':
            tokens.append(Token(SYMBOL, ":=", line, col))
            i += 2; col += 2
        elif s[i] == '{':
            count = 1; i += 1
            while i < n and count != 0:
                if s[i] == '{': count += 1
                elif s[i] == '}': count -= 1
                if s[i] == '\n':
                    i += 1; line +=1; col = 0
                else:
                    i += 1; col += 1
        else:
            tokens.append(Token(SYMBOL, s[i], line, col))
            i += 1; col += 1
    tokens.append(Token(None, None, line, col))
    return tokens

def expect(tokens, i, kind, value):
    if tokens[i].kind != kind or tokens[i].value != value:
        raise SyntaxError(tokens[i].line, tokens[i].col,
            f"Expected '{value}'")

def atomic_term(tokens, i):
    t = tokens[i]
    if t.kind == INT or t.kind == IDENT:
        return i + 1, tokens[i].value
    elif t.kind == SYMBOL and t.value == "-" and tokens[i + 1].kind == INT:
        return i + 2, -tokens[i + 1].value
    elif t.kind == SYMBOL and t.value == "(":
        i, x = add_term(tokens, i + 1)
        expect(tokens, i, SYMBOL, ")")
        return i + 1, x
    else:
        raise SyntaxError(tokens[i].line, tokens[i].col,
            f"Unexpected token: '{tokens[i].value}'")

def mul_term(token, i):
    i, x = atomic_term(token, i)
    while token[i].kind == SYMBOL and token[i].value in ("*", "/"):
        op = token[i].value
        i, y = atomic_term(token, i + 1)
        x = (op, x, y)
    return i, x

def add_term(token, i):
    i, x = mul_term(token, i)
    while token[i].kind == SYMBOL and token[i].value in ("+", "-"):
        op = token[i].value
        i, y = mul_term(token, i + 1)
        x = (op, x, y)
    return i, x

def atomic_expression(tokens, i):
    t = tokens[i]
    if t.kind == SYMBOL and t.value in ("false", "true"):
        return i + 1, (False if t.value == "false" else True)
    elif t.kind == SYMBOL and t.value == "(":
        i, x = or_expression(tokens, i + 1)
        expect(tokens, i, SYMBOL, ")")
        return i + 1, x
    else:
        i, x = add_term(tokens, i)
        t = tokens[i]
        if t.kind != SYMBOL or not t.value in ("=", "<="):
            raise SyntaxError(tokens[i].line, tokens[i].col,
                "Expected '=' or '<='")
        op = t.value
        i, y = add_term(tokens, i + 1)
        return i, (op, x, y)

def not_expression(tokens, i):
    if tokens[i].kind == SYMBOL and tokens[i].value == "not":
        i, x = not_expression(tokens, i + 1)
        return i, ("not", x)
    else:
        return atomic_expression(tokens, i)

def and_expression(tokens, i):
    i, x = not_expression(tokens, i)
    while tokens[i].kind == SYMBOL and tokens[i].value == "and":
        i, y = not_expression(tokens, i + 1)
        x = ("and", x, y)
    return i, x

def or_expression(tokens, i):
    i, x = and_expression(tokens, i)
    while tokens[i].kind == SYMBOL and tokens[i].value == "or":
        i, y = and_expression(tokens, i + 1)
        x = ("or", x, y)
    return i, x

def atomic_command(tokens, i):
    t = tokens[i]
    if t.kind == SYMBOL and t.value == "if":
        i, b = or_expression(tokens, i + 1)
        expect(tokens, i, SYMBOL, "then")
        i, c1 = seq_command(tokens, i + 1)
        expect(tokens, i, SYMBOL, "else")
        i, c2 = seq_command(tokens, i + 1)
        expect(tokens, i, SYMBOL, "end")
        return i + 1, ("if", b, c1, c2)
    elif t.kind == SYMBOL and t.value == "while":
        i, b = or_expression(tokens, i + 1)
        expect(tokens, i, SYMBOL, "do")
        i, c = seq_command(tokens, i + 1)
        expect(tokens, i, SYMBOL, "end")
        return i + 1, ("while", b, c)
    elif t.kind == SYMBOL and t.value == "skip":
        return i + 1, ("skip",)
    elif t.kind == SYMBOL and t.value == "print":
        i, a = add_term(tokens, i + 1)
        return i, ("print", a)
    elif t.kind == IDENT:
        X = t.value
        expect(tokens, i + 1, SYMBOL, ":=")
        i, a = add_term(tokens, i + 2)
        return i, (":=", X, a)
    else:
        raise SyntaxError(tokens[i].line, tokens[i].col,
            f"Unexpected token: '{tokens[i].value}'")

def seq_command(tokens, i):
    i, x = atomic_command(tokens, i)
    while tokens[i].kind == SYMBOL and tokens[i].value == ";":
        i, y = atomic_command(tokens, i + 1)
        x = (";", x, y)
    return i, x

def parse(tokens):
    i, x = seq_command(tokens, 0)
    if tokens[i].kind != None:
        raise SyntaxError(tokens[i].line, tokens[i].col,
            "Expected ';' or end of input")
    return x

def sgn(x):
    return 0 if x == 0 else -1 if x < 0 else 1

def idiv(x, y):
    return 0 if y == 0 else sgn(y)*(x//abs(y))

def A(a, s):
    if type(a) is int:
        return a
    elif type(a) is str:
        return s[a] if a in s else 0
    else:
        op = a[0]; x = A(a[1], s); y = A(a[2], s)
        if op == "+":
            return x + y
        elif op == "-":
            return x - y
        elif op == "*":
            return x*y
        elif op == "/":
            return idiv(x, y)
    raise ValueError("unreachable")

def B(b, s):
    if type(b) is bool:
        return b
    elif type(b) is tuple:
        op = b[0]
        if op == "not":
            return not B(b[1], s)
        elif op == "and":
            return B(b[1], s) and B(b[2], s)
        elif op == "or":
            return B(b[1], s) or B(b[2], s)
        elif op == "=":
            return A(b[1], s) == A(b[2], s)
        elif op == "<=":
            return A(b[1], s) <= A(b[2], s)
    raise ValueError("unreachable")

def C(c, s):
    if type(c) is tuple:
        op = c[0]
        if op == "skip":
            return s
        elif op == ":=":
            s[c[1]] = A(c[2], s)
            return s
        elif op == ";":
            return C(c[2], C(c[1], s))
        elif op == "if":
            return C(c[2], s) if B(c[1], s) else C(c[3], s)
        elif op == "while":
            while B(c[1], s):
                s = C(c[2], s)
            return s
        elif op == "print":
            print(A(c[1], s))
            return s
    else:
        raise ValueError("unreachable")

def main():
    source_code = read(argv[1])
    try:
        tokens = scan(source_code)
        c = parse(tokens)
        s = C(c, {})
    except SyntaxError as e:
        print(f"Syntax error in line {e.line + 1}, col {e.col + 1}:")
        print(f"{e.text}.")

if __name__ == "__main__":
    main()
