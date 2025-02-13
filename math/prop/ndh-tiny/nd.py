#!/usr/bin/env python3
from sys import argv

class Error(ValueError):
    def __init__(self, line, text):
        self.line = line; self.text = text

def scan(s):
    acc = []; line = 1; token = ""
    for c in s:
        if c.isspace():
            if token:
                acc.append((token, line))
                token = ""
            if c == "\n": line += 1
        elif c in "()":
            if token:
                acc.append((token, line))
                token = ""
            acc.append((c, line))
        else:
            token += c
    if token:
        acc.append((token, line))
    acc.append((None, line))
    return acc

def parse(s):
    i = 0; a = scan(s)
    def parse_expr():
        nonlocal i
        if a[i][0] is None:
            raise Error(a[i][1], "unexpected end of input")
        token, line = a[i]
        i += 1
        if token == '(':
            acc = []
            while not a[i][0] is None and a[i][0] != ')':
                acc.append(parse_expr())
            if a[i][0] is None or a[i][0] != ')':
                raise Error(line, "unclosed '('")
            i += 1
            return tuple(acc)
        elif token == ')':
            raise Error(line, "unexpected ')'")
        else:
            return int(token) if token.isdigit() else token
    statements = []
    while not a[i][0] is None:
        token, line = a[i]
        statements.append((line, parse_expr()))
    return statements

def subst_rec(A, subst):
    if isinstance(A, str):
        if not A in subst: subst[A] = A
        return subst[A]
    else:
        return (A[0],) + tuple(subst_rec(X, subst) for X in A[1:])

def conj_set(A, subst):
    if A == ("true",):
        return set()
    elif isinstance(A, tuple) and A[0] == "conj":
        return conj_set(A[1], subst) | conj_set(A[2], subst)
    elif not subst is None:
        return conj_set(subst_rec(A, subst), None)
    else:
        return {A}

def unify_seq(A, pattern, subst):
    if conj_set(A[1], None) != conj_set(pattern[1], subst):
        return False
    return unify(A[2], pattern[2], subst)

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
                if pattern[0] == "seq":
                    return unify_seq(A, pattern, subst)
                return False
    return True

def get(line, book, key):
    try:
        return book[key]
    except KeyError:
        raise Error(line, f"identifier '{key}' not found")

def modus_ponens(line, book, B, args):
    assert len(args) >= 1
    C = get(line, book, args[0])
    subst = {}
    for i in range(1, len(args)):
        A = get(line, book, args[i])
        if not isinstance(C, tuple) or C[0] != "subj":
            raise Error(line, "expected a rule/subjunction")
        if not unify(A, C[1], subst):
            raise Error(line,
                f"unification failed for {args[0]}, argument {i}")
        C = C[2]
    if not unify(B, C, subst):
        raise Error(line,
            f"unification failed for {args[0]}, in conclusion")

def verify(book, s):
    try:
        statements = parse(s)
        for (line, statement) in statements:
            if len(statement) == 4: 
                (label, Gamma, A, rule) = statement
                book[label] = ("seq", None, A)
                H = ("true",)
                for k in Gamma:
                    H = ("conj", H, get(line, book, k)[2])
                B = ("seq", H, A)
            else:
                (label, B, rule) = statement
            book[label] = B
            if label in rule:
                raise Error(line, "cyclic deduction")
            if rule[0] != "axiom":
                modus_ponens(line, book, B, rule)
    except Error as e:
        print(f"Error in line {e.line}:\n{e.text}")

def read_all(path):
    with open(path) as f:
        return f.read()

rules = """
(basic (seq (conj (true) H) H) (axiom))
(conj_intro (subj (seq H1 A) (subj (seq H2 B)
  (seq (conj H1 H2) (conj A B)))) (axiom))
(conj_eliml (subj (seq H (conj A B)) (seq H A)) (axiom))
(conj_elimr (subj (seq H (conj A B)) (seq H B)) (axiom))
(disj_introl (subj (seq H A) (seq H (disj A B))) (axiom))
(disj_intror (subj (seq H B) (seq H (disj A B))) (axiom))
(disj_elim (subj (seq H1 (disj A B)) (subj (seq (conj H2 A) C)
  (subj (seq (conj H3 B) C) (seq (conj H1 (conj H2 H3)) C)))) (axiom))
(subj_intro (subj (seq (conj H A) B) (seq H (subj A B))) (axiom))
(subj_elim (subj (seq H1 (subj A B)) (subj (seq H2 A)
  (seq (conj H1 H2) B))) (axiom))
(neg_intro (subj (seq (conj H A) (false)) (seq H (neg A))) (axiom))
(neg_elim (subj (seq H1 (neg A)) (subj (seq H2 A)
  (seq (conj H1 H2) (false)))) (axiom))
(wk (subj (seq H B) (seq (conj H A) B)) (axiom))
(exch (subj (seq H A) (seq H A)) (axiom))
"""

book = {}
verify(book, rules)
verify(book, read_all(argv[1]))
