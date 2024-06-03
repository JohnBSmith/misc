#!/usr/bin/env python3

# A tiny Hilbert calculus proof verifier for propositional logic.
# See verify-doc-en.htm for further information.
#
# USAGE
# verify.py proofs.txt
#     If the program stays quiet, the deductions should be correct.
#
# verify.py -f proofs.txt output.txt
#     Format ASCII input to common notation.

from sys import argv

class SyntaxError(ValueError):
    def __init__(self, line, text):
        self.line = line; self.text = text

class LogicError(ValueError):
    def __init__(self, line, text):
        self.line = line; self.text = text

sym2 = {"->": "->", "=>": "->", "/\\": "&", "\\/": "|"}
sym3 = {"<->": "<->", "<=>": "<->", "_|_": "_|_"}
kw_tab = {"and": "&", "or": "|", "not": "~", "false": "_|_"}

def scan(s):
    i = 0; n = len(s); a = []; line = 1
    while i < n:
        if s[i].isalpha():
            j = i
            while i < n and (s[i].isalpha() or s[i].isdigit() or s[i] == '_'):
                i += 1
            if s[j:i] in kw_tab:
                a.append((kw_tab[s[j:i]], line))
            else:
                a.append((s[j:i], line))
        elif s[i].isdigit():
            j = i
            while i < n and s[i].isdigit():
                i += 1
            a.append((int(s[j:i]), line))
        elif s[i].isspace():
            if s[i] == "\n": line += 1
            i += 1
        elif i + 1 < n and s[i:i+2] in sym2:
            a.append((sym2[s[i:i+2]], line))
            i += 2
        elif i + 2 < n and s[i:i+3] in sym3:
            a.append((sym3[s[i:i+3]], line))
            i += 3
        elif s[i] == '(' and i + 1 < n and s[i+1] == '*':
            while i + 1 < n and (s[i] != '*' or s[i+1] != ')'):
                if s[i] == '\n': line += 1
                i += 1
            i += 2
        else:
            a.append((s[i], line))
            i += 1
    a.append((None, line))
    return a

def atom(a, i):
    token = a[i][0]
    if isinstance(token, str) and token[0].isalpha():
        return i + 1, token
    elif token == "_|_" or token == "⊥":
        return i + 1, ("false",)
    elif token == "(":
        i, x = bijunction(a, i + 1)
        if a[i][0] != ")":
            raise SyntaxError(a[i][1], "expected ')'")
        return i + 1, x
    else:
        raise SyntaxError(a[i][1],
            "expected an atom, but got '{}'".format(token))

def negation(a, i):
    if a[i][0] == "~" or a[i][0] == "¬":
        i, x = negation(a, i + 1)
        return i, ("neg", x)
    else:
        return atom(a, i)

def conjunction(a, i):
    i, x = negation(a, i)
    while a[i][0] == "&" or a[i][0] == "∧":
        i, y = negation(a, i + 1)
        x = ("conj", x, y)
    return i, x

def disjunction(a, i):
    i, x = conjunction(a, i)
    while a[i][0] == "|" or a[i][0] == "∨":
        i, y = conjunction(a, i + 1)
        x = ("disj", x, y)
    return i, x

def subjunction(a, i):
    i, x = disjunction(a, i)
    if a[i][0] == "->" or a[i][0] == "→" or a[i][0] == "⇒":
        i, y = subjunction(a, i + 1)
        return i, ("subj", x, y)
    else:
        return i, x

def bijunction(a, i):
    i, x = subjunction(a, i)
    if a[i][0] == "<->" or a[i][0] == "↔" or a[i][0] == "⇔":
        i, y = subjunction(a, i + 1)
        return i, ("bij", x, y)
    else:
        return i, x

def is_identifier(t):
    return isinstance(t, str) and t[0].isalpha()

def rule_app(a, i):
    acc = []
    if not isinstance(a[i][0], int) and not is_identifier(a[i][0]):
        raise SyntaxError(a[i][1], "expected identifier or label")
    acc.append(a[i][0])
    i += 1
    while True:
        token = a[i][0]
        if isinstance(token, int) or is_identifier(token):
            acc.append(token); i += 1
        elif a[i][0] == ".":
            return i, acc
        else:
            raise SyntaxError(a[i][1], "expected identifier or label")

def parse_statement(i, a):
    label, line = a[i]; i += 1
    if a[i][0] != ".":
        raise SyntaxError(a[i][1], "expected '.'")
    i, A = bijunction(a, i + 1)
    if a[i][0] != ",":
        raise SyntaxError(a[i][1], "expected ','")
    i, rule = rule_app(a, i + 1)
    if a[i][0] != ".":
        raise SyntaxError(a[i][1], "expected '.'")
    return i + 1, (line, label, A, rule)

def parse(s):
    a = scan(s); i = 0; statements = []
    while a[i][0] != None:
        i, stmt = parse_statement(i, a)
        statements.append(stmt)
    return statements

def unify(A, pattern, subst):
    if isinstance(pattern, str):
        if pattern in subst:
            if not subst[pattern] == A: return False
        else:
            subst[pattern] = A
    else:
        if not isinstance(A, tuple): return False
        if len(A) != len(pattern): return False
        if A[0] != pattern[0]: return False
        for i in range(1, len(A)):
            if not unify(A[i], pattern[i], subst):
                return False
    return True

def modus_ponens(line, book, B, args):
    assert len(args) >= 1
    C = book[args[0]]
    subst = {}
    for i in range(1, len(args)):
        A = book[args[i]]
        if not isinstance(C, tuple) or C[0] != "subj":
            raise LogicError(line, "expected a subjunction")
        if not unify(A, C[1], subst):
            raise LogicError(line, "unification failed")
        C = C[2]
    if not unify(B, C, subst):
        raise LogicError(line, "unification failed")

def verify(s):
    try:
        statements = parse(s)
        book = {}
        for (line, label, B, rule) in statements:
            book[label] = B
            if rule[0] != "axiom":
                modus_ponens(line, book, B, rule)
    except SyntaxError as e:
        print("Syntax error in line {}:\n{}".format(e.line, e.text))
    except LogicError as e:
        print("Logic error in line {}:\n{}".format(e.line, e.text))

fmt_tab = {
    "&": "∧", "|": "∨", "~": "¬", "->": "→", "=>": "→",
    "/\\": "∧", "\\/": "∨", "<->": "↔", "<=>": "↔", "_|_": "⊥"
}
fmt_kw_tab = {
    "and": "∧", "or": "∨", "not": "¬", "false": "⊥"
}

def format_source_code(s):
    acc = []; i = 0; n = len(s)
    while i < n:
        fmt = False
        for k in range(3, 0, -1):
            if i + k - 1 < n and s[i:i+k] in fmt_tab:
                acc.append(fmt_tab[s[i:i+k]])
                i += k; fmt = True; break
        if not fmt:
            if s[i].isalpha() or s[i] == '_':
                j = i
                while i < n and (s[i].isalpha() or s[i].isdigit() or s[i] == '_'):
                    i += 1
                sji = s[j:i]; sf = fmt_kw_tab.get(sji)
                acc.append(sji if sf is None else sf)
                if sji == "not" and i < n and s[i] == ' ':
                    i += 1
            elif s[i] == '(' and i + 1 < n and s[i+1] == '*':
                while i + 1 < n and (s[i] != '*' or s[i+1] != ')'):
                    acc.append(s[i])
                    i += 1
                acc.append(s[i:i+2])
                i += 2
            else:
                acc.append(s[i])
                i += 1
    return "".join(acc)

def read_all(path):
    with open(path) as f:
        return f.read()

def main():
    if argv[1] == "-f":
        text = format_source_code(read_all(argv[2]))
        if len(argv) == 4:
            with open(argv[3], "w") as fout:
                fout.write(text)
        else:
            print(text)
    else:
        verify(read_all(argv[1]))

main()
