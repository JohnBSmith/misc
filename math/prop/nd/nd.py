#!/usr/bin/env python3

# A small natural deduction proof verifier for propositional logic.
#
# USAGE
# nd.py proofs.txt
#     If the program stays quiet, the deductions should be correct.
#
# nd.py -f proofs.txt output.txt
#     Format ASCII input to common notation.

from sys import argv

class SyntaxError(ValueError):
    def __init__(self, line, text):
        self.line = line
        self.text = text

class LogicError(ValueError):
    def __init__(self, line, text):
        self.line = line
        self.text = text

sym2 = {"->": "->", "=>": "->", "|-": "|-", "/\\": "&", "\\/": "|"}
sym3 = {"<->": "<->", "<=>": "<->", "_|_": "#f"}

keywords = {
    "false": "#f", "true": "#t", "and": "&", "or": "|", "not": "~",
    "box": "#box", "dia": "#dia"
}

def scan(s):
    i = 0; n = len(s); a = []; line = 1
    while i < n:
        if s[i].isalpha():
            j = i
            while i < n and (s[i].isalpha() or s[i].isdigit() or s[i] == '_'):
                i += 1
            s0 = s[j:i]
            if s0 in keywords: s0 = keywords[s0]
            a.append((s0, line))
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
        elif s[i] == '#':
            while i < n and s[i] != '\n':
                i += 1
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
    elif token == "#f" or token == "⊥":
        return i + 1, ("false",)
    elif token == "#t":
        return i + 1, ("true",)
    elif token == "(":
        i, x = bijunction(a, i + 1)
        if a[i][0] != ")":
            raise SyntaxError(a[i][1], "expected ')'")
        return i + 1, x
    else:
        raise SyntaxError(a[i][1], "expected an atom, but got '{}'".format(token))

def negation(a, i):
    if a[i][0] == "~" or a[i][0] == "¬":
        i, x = negation(a, i + 1)
        return i, ("neg", x)
    elif a[i][0] == "#box" or a[i][0] == "□":
        i, x = negation(a, i + 1)
        return i, ("box", x)
    elif a[i][0] == "#dia" or a[i][0] == "◇":
        i, x = negation(a, i + 1)
        return i, ("dia", x)
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

def context(a, i):
    acc = []
    if a[i][0] == "|-" or a[i][0] == "⊢":
        return i, acc
    while True:
        token = a[i][0]
        if isinstance(token, int) or is_identifier(token):
            acc.append(token)
            i += 1
        if a[i][0] != ",": break
        i += 1
    return i, acc

def sequent(a, i):
    i, ctx = context(a, i)
    if a[i][0] == "|-" or a[i][0] == "⊢":
        i, x = bijunction(a, i + 1)
        return i, (ctx, x)
    else:
        raise SyntaxError(a[i][1], "expected context")

def union(Gamma1, Gamma2):
    Gamma = list(Gamma1)
    for X in Gamma2:
        if not X in Gamma1:
            Gamma.append(X)
    return tuple(Gamma)

def difference(Gamma, A):
    return tuple(X for X in Gamma if X != A)

def rule_app(a, i):
    acc = []
    if not is_identifier(a[i][0]):
        raise SyntaxError(a[i][1],
            "expected rule name, but got '{}'".format(a[i][0]))
    acc.append(a[i][0])
    i += 1
    while True:
        token = a[i][0]
        if isinstance(token, int) or is_identifier(token):
            acc.append(token)
            i += 1
        elif a[i][0] == ".":
            return i, acc
        else:
            raise SyntaxError(a[i][1], "expected label")

def parse_statement(i, a):
    label, line = a[i]; i += 1
    if a[i][0] != ".":
        raise SyntaxError(a[i][1], "expected '.'")
    i += 1
    i, (Gamma, A) = sequent(a, i)
    if a[i][0] != ",":
        raise SyntaxError(a[i][1],
            "expected ',', but got '{}'".format(a[i][0]))
    i, rule = rule_app(a, i + 1)
    if a[i][0] != ".":
        raise SyntaxError(a[i][1], "expected '.'")
    return i + 1, (line, label, Gamma, A, rule)

def parse(s):
    a = scan(s)
    i = 0; statements = []
    while a[i][0] != None:
        i, stmt = parse_statement(i, a)
        statements.append(stmt)
    return statements

def basic_seq(line, book, S, args):
    assert len(args) == 0
    Gamma, A = S
    if not A in Gamma:
        raise LogicError(line, "not a basic sequent")

def conj_intro(line, book, S, args):
    assert len(args) == 2
    Gamma1, A = book[args[0]]
    Gamma2, B = book[args[1]]
    S0 = (union(Gamma1, Gamma2), ("conj", A, B))
    if S != S0:
        raise LogicError(line, "conj_intro produces different sequent")

def conj_eliml(line, book, S, args):
    assert len(args) == 1
    Gamma, C = book[args[0]]
    if not isinstance(C, tuple) or C[0] != "conj":
        raise LogicError(line, "conj_eliml expected a conjunction")
    S0 = (Gamma, C[1])
    if S != S0:
        raise LogicError(line, "conj_eliml produces different sequent")
        
def conj_elimr(line, book, S, args):
    assert len(args) == 1
    Gamma, C = book[args[0]]
    if not isinstance(C, tuple) or C[0] != "conj":
        raise LogicError(line, "conj_elimr expected a conjunction")
    S0 = (Gamma, C[2])
    if S != S0:
        raise LogicError(line, "conj_elimr produces different sequent")

def subj_intro(line, book, S, args):
    assert len(args) == 1
    Gamma, B = book[args[0]]
    C = S[1]
    if not isinstance(C, tuple) or C[0] != "subj":
        raise LogicError(line, "subj_intro produces different sequent")
    A = C[1]
    if not A in Gamma:
        raise LogicError(line, "subj_intro failed: {} not in {}".format(A, Gamma))
    S0 = (difference(Gamma, A), ("subj", A, B))
    if S != S0:
        raise LogicError(line, "subj_intro produces different sequent")

def subj_elim(line, book, S, args):
    assert len(args) == 2
    Gamma1, C = book[args[0]]
    Gamma2, A = book[args[1]]
    if not isinstance(C, tuple) or C[0] != "subj" or C[1] != A:
        raise LogicError(line, "subj_elim expected a matching subjunction")
    S0 = (union(Gamma1, Gamma2), C[2])
    if S != S0:
        raise LogicError(line, "subj_elim produces different sequent")

def neg_intro(line, book, S, args):
    assert len(args) == 1
    Gamma, B = book[args[0]]
    C = S[1]
    if not isinstance(C, tuple) or C[0] != "neg":
        raise LogicError(line, "neg_intro produces different sequent")
    if B != ("false",):
        raise LogicError(line, "neg_intro expects ⊥")
    A = C[1]
    if not A in Gamma:
        raise LogicError(line, "neg_intro failed: {} not in {}".format(A, Gamma))
    S0 = (difference(Gamma, A), ("neg", A))
    if S != S0:
        raise LogicError(line, "neg_intro produces different sequent")

def neg_elim(line, book, S, args):
    assert len(args) == 2
    Gamma1, C = book[args[0]]
    Gamma2, A = book[args[1]]
    if not isinstance(C, tuple) or C[0] != "neg" or C[1] != A:
        raise LogicError(line, "neg_elim expected a matching negation")
    S0 = (union(Gamma1, Gamma2), ("false",))
    if S != S0:
        raise LogicError(line, "neg_elim produces different sequent")

def disj_introl(line, book, S, args):
    assert len(args) == 1
    Gamma, A = book[args[0]]
    C = S[1]
    if not isinstance(C, tuple) or C[0] != "disj":
        raise LogicError(line, "disj_introl produces different sequent")
    S0 = (Gamma, ("disj", A, C[2]))
    if S != S0:
        raise LogicError(line, "disj_introl produces different sequent")

def disj_intror(line, book, S, args):
    assert len(args) == 1
    Gamma, A = book[args[0]]
    C = S[1]
    if not isinstance(C, tuple) or C[0] != "disj":
        raise LogicError(line, "disj_introl produces different sequent")
    S0 = (Gamma, ("disj", C[1], A))
    if S != S0:
        raise LogicError(line, "disj_introl produces different sequent")

def disj_elim(line, book, S, args):
    assert len(args) == 3
    Gamma1, D = book[args[0]]
    Gamma2, C2 = book[args[1]]
    Gamma3, C3 = book[args[2]]
    if not isinstance(D, tuple) or D[0] != "disj":
        raise LogicError(line, "disj_elim expects a disjunction")
    if C2 != C3:
        raise LogicError(line, "disj_elim expects the same proposition in each case")
    Gamma23 = union(difference(Gamma2, D[1]), difference(Gamma3, D[2]))
    S0 = (union(Gamma1, Gamma23), C2)
    if S != S0:
        raise LogicError(line, "disj_elim produces different sequent")

def bij_intro(line, book, S, args):
    assert len(args) == 2
    Gamma1, A = book[args[0]]
    Gamma2, B = book[args[1]]
    if (not isinstance(A, tuple) or A[0] != "subj" or
        not isinstance(B, tuple) or B[0] != "subj" or
       A[1] != B[2] or A[2] != B[1]):
        raise LogicError(line, "bij_intro expects matching subjunctions")
    S0 = (union(Gamma1, Gamma2), ("bij", A[1], A[2]))
    if S != S0:
        raise LogicError(line, "bij_intro produces different sequent")

def bij_eliml(line, book, S, args):
    assert len(args) == 1
    Gamma, A = book[args[0]]
    if not isinstance(A, tuple) or A[0] != "bij":
        raise LogicError(line, "bij_eliml expects a bijunction")
    S0 = (Gamma, ("subj", A[1], A[2]))
    if S != S0:
        raise LogicError(line, "bij_eliml produces different sequent")

def bij_elimr(line, book, S, args):
    assert len(args) == 1
    Gamma, A = book[args[0]]
    if not isinstance(A, tuple) or A[0] != "bij":
        raise LogicError(line, "bij_eliml expects a bijunction")
    S0 = (Gamma, ("subj", A[2], A[1]))
    if S != S0:
        raise LogicError(line, "bij_eliml produces different sequent")

def axiom(line, book, S, args):
    assert len(args) == 0
    if not S[0] == ():
        raise LogicError(line, "axiom expects empty context")

def unify(A, pattern, subst):
    if isinstance(pattern, str):
        if pattern in subst:
            if not subst[pattern] == A: return False
        else:
            subst[pattern] = A
    else:
        if not isinstance(A, tuple): return False
        if not len(A) == len(pattern): return False
        if not A[0] == pattern[0]: return False
        for i in range(1, len(A)):
            if not unify(A[i], pattern[i], subst):
                return False
    return True

def substitution(line, book, S, args):
    assert len(args) == 1
    Gamma, A = book[args[0]]
    if len(Gamma) != 0:
        raise LogicError(line, "subst expects a theorem")
    if len(S[0]) != 0:
        raise LogicError(line, "subst produces a theorem")
    if not unify(S[1], A, {}):
        raise LogicError(line, "subst: unification failed")

def box_intro(line, book, S, args):
    assert len(args) == 1
    Gamma, A = book[args[0]]
    if len(Gamma) != 0:
        raise LogicError(line, "box_intro expects a theorem")
    if len(S[0]) != 0:
        raise LogicError(line, "box_intro produces a theorem")
    S0 = (Gamma, ("box", A))
    if S != S0:
        raise LogicError(line, "box_intro produces different sequent")

verify_tab = {
    "basic": basic_seq,
    "conj_intro": conj_intro,
    "conj_eliml": conj_eliml,
    "conj_elimr": conj_elimr,
    "disj_introl": disj_introl,
    "disj_intror": disj_intror,
    "disj_elim": disj_elim,
    "subj_intro": subj_intro,
    "subj_elim": subj_elim,
    "neg_intro": neg_intro,
    "neg_elim": neg_elim,
    "bij_intro": bij_intro,
    "bij_eliml": bij_eliml,
    "bij_elimr": bij_elimr,
    "mp": subj_elim,
    "subst": substitution,
    "axiom": axiom,
    "box_intro": box_intro
}

def verify(s):
    try:
        statements = parse(s)
        book = {}
        for (line, label, Gamma, A, rule) in statements:
            book[label] = (None, A)
            Gamma = tuple(book[k][1] for k in Gamma)
            book[label] = (Gamma, A)
            if not rule[0] in verify_tab:
                raise LogicError(line, "rule {} not found".format(rule[0]))
            verify_tab[rule[0]](line, book, (Gamma, A), rule[1:])
    except SyntaxError as e:
        print("Syntax error in line {}:\n{}".format(e.line, e.text))
    except LogicError as e:
        print("Logic error in line {}:\n{}".format(e.line, e.text))

fmt1_tab = {"&": "∧", "|": "∨", "~": "¬"}
fmt2_tab = {"->": "→", "=>": "→", "|-": "⊢", "/\\": "∧", "\\/": "∨"}
fmt3_tab = {"<->": "↔", "<=>": "↔", "_|_": "⊥"}
fmt_kw_tab = {"not": "¬", "and": "∧", "or": "∨", "false": "⊥",
  "box": "□", "dia": "◇"}
trim_tab = {"¬", "□", "◇"}

def format_source_code(s):
    acc = []; i = 0; n = len(s)
    while i < n:
        if i + 2 < n and s[i:i+3] in fmt3_tab:
            acc.append(fmt3_tab[s[i:i+3]])
            i += 3
        elif i + 1 < n and s[i:i+2] in fmt2_tab:
            acc.append(fmt2_tab[s[i:i+2]])
            i += 2
        elif s[i] in fmt1_tab:
            acc.append(fmt1_tab[s[i]])
            i += 1
        elif s[i].isalpha() or s[i] == '_':
            j = i
            while i < n and (s[i].isalpha() or s[i].isdigit() or s[i] == '_'):
                i += 1
            if s[j:i] in fmt_kw_tab:
                acc.append(fmt_kw_tab[s[j:i]])
            else:
                acc.append(s[j:i])
            if acc[-1] in trim_tab and i < n and s[i] == ' ':
                i += 1
        elif s[i] == '#':
            while s[i] != '\n':
                acc.append(s[i])
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
        text = f.read()
    return text

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
