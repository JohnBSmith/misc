#!/usr/bin/env python3

# A small natural deduction proof verifier for propositional logic that
# allows inference rules to be stated as axioms of a Hilbert system in
# which sequents are treated as propositions.
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
        self.line = line; self.text = text

class LogicError(ValueError):
    def __init__(self, line, text):
        self.line = line; self.text = text

sym2 = {"->": "->", "=>": "->", "/\\": "&", "\\/": "|", "|-": "|-"}
sym3 = {"<->": "<->", "<=>": "<->", "_|_": "_|_"}
kw_tab = {"and": "&", "or": "|", "not": "~", "false": "_|_"}

def scan(s):
    i = 0; n = len(s); a = []; line = 1
    while i < n:
        if s[i].isalpha() or s[i] == '_':
            j = i
            while i < n and (s[i].isalpha() or s[i].isdigit() or s[i] in "_'"):
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
    elif token == "_|_" or token == "⊥":
        return i + 1, ("false",)
    elif token == "(":
        i, x = sequent(a, i + 1)
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

def formulas(a, i):
    if a[i][0] == "{":
        i += 1; acc = ["formulas"]
        while True:
            i, x = bijunction(a, i)
            acc.append(x)
            if a[i][0] == "}":
                return i + 1, tuple(acc)
            elif a[i][0] == ',':
                i += 1
            else:
                raise SyntaxError(a[i][1], "expected ',' or '}'")
    elif (isinstance(a[i][0], str) and a[i][0][0].isalpha()):
        return i + 1, a[i][0]
    else:
        raise SyntaxError(a[i][1], "expected identifier or '{'")

def difference(a, i):
    i, x = formulas(a, i)
    if a[i][0] == "\\":
        i, y = formulas(a, i + 1)
        return i, ("difference", x, y)
    else:
        return i, x

def context(a, i):
    if a[i][0] == "|-" or a[i][0] == "⊢":
        return i, ("formulas",)
    else:
        i, x = difference(a, i)
        while a[i][0] == ",":
            i, y = difference(a, i + 1)
            x = ("union", x, y)
        return i, x

def sequent(a, i):
    if a[i][0] == "sq":
        i += 1
        (i, x) = context(a, i)
        if a[i][0] != "|-" and a[i][0] != "⊢":
            raise SyntaxError(a[i][1], "expected |-")
        i, y = sequent(a, i + 1)
        return i, ("seq", x, y)
    else:
        return bijunction(a, i)

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

def ref_context(a, i):
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

def ref_sequent(a, i):
    i, ctx = ref_context(a, i)
    if a[i][0] == "|-" or a[i][0] == "⊢":
        i, x = sequent(a, i + 1)
        return i, ("ref_seq", ctx, x)
    else:
        raise SyntaxError(a[i][1], "expected context")

def parse_statement(i, a):
    label, line = a[i]; i += 1
    if a[i][0] != ".":
        raise SyntaxError(a[i][1], "expected '.'")
    if a[i+1][0] == "(":
        i, A = sequent(a, i + 1)
    else:
        i, A = ref_sequent(a, i + 1)
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

def eval_context(Gamma, subst):
    if isinstance(Gamma, tuple) and Gamma[0] == "union":
        Gamma1 = eval_context(Gamma[1], subst)
        Gamma2 = eval_context(Gamma[2], subst)
        Gamma0 = Gamma1
        for A in Gamma2:
            if A not in Gamma0:
                Gamma0.append(A)
        return Gamma0
    elif isinstance(Gamma, tuple) and Gamma[0] == "difference":
        Gamma1 = eval_context(Gamma[1], subst)
        Gamma2 = eval_context(Gamma[2], subst)
        Delta = []
        for A in Gamma1:
            if not A in Gamma2:
                Delta.append(A)
        return Delta
    elif isinstance(Gamma, tuple) and Gamma[0] == "formulas":
        return [subst[A] for A in Gamma[1:]]
    else:
        assert isinstance(Gamma, str)
        Gamma = subst[Gamma]
        assert isinstance(Gamma, tuple) and Gamma[0] == "formulas"
        return list(Gamma[1:])

def unify_seq(S, pattern, subst):
    if not unify(S[2], pattern[2], subst): return False
    if (isinstance(pattern[1], tuple) and
        (pattern[1][0] == "union" or pattern[1][0] == "difference")):
        context = eval_context(pattern[1], subst)
        return S[1] == ("formulas",) + tuple(context)
    else:
        return unify(S[1], pattern[1], subst)

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
        if A[0] == "seq":
            return unify_seq(A, pattern, subst)
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
            raise LogicError(line, "expected a rule/subjunction")
        if not unify(A, C[1], subst):
            raise LogicError(line,
                "unification failed for {}, argument {}".format(args[0], i))
        C = C[2]
    if not unify(B, C, subst):
        raise LogicError(line,
            "unification failed for {}".format(args[0]))

def verify(book, s):
    try:
        statements = parse(s)
        for (line, label, B, rule) in statements:
            if isinstance(B, tuple) and B[0] == "ref_seq":
                Gamma = B[1]; A = B[2]
                book[label] = ("seq", None, A)
                Gamma = tuple(book[k][2] for k in Gamma)
                B = ("seq", ("formulas",)+Gamma, A)
                book[label] = B
            else:
                book[label] = B
            if label in rule:
                raise LogicError(line, "cyclic deduction")
            if rule[0] != "axiom":
                modus_ponens(line, book, B, rule)
    except SyntaxError as e:
        print("Syntax error in line {}:\n{}".format(e.line, e.text))
    except LogicError as e:
        print("Logic error in line {}:\n{}".format(e.line, e.text))

fmt_tab = {
    "&": "∧", "|": "∨", "~": "¬", "->": "→", "=>": "→",
    "/\\": "∧", "\\/": "∨", "|-": "⊢",
    "<->": "↔", "<=>": "↔", "_|_": "⊥"
}
fmt_kw_tab = {
    "and": "∧", "or": "∨", "not": "¬"
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

rules = """
basic. (sq {A} ⊢ A), axiom.
conj_intro. (sq Γ1 ⊢ A) → (sq Γ2 ⊢ B) → (sq Γ1, Γ2 ⊢ A ∧ B), axiom.
conj_eliml. (sq Γ ⊢ A ∧ B) → (sq Γ ⊢ A), axiom.
conj_elimr. (sq Γ ⊢ A ∧ B) → (sq Γ ⊢ B), axiom.
disj_introl. (sq Γ ⊢ A) → (sq Γ ⊢ A ∨ B), axiom.
disj_intror. (sq Γ ⊢ B) → (sq Γ ⊢ A ∨ B), axiom.
disj_elim. (sq Γ1 ⊢ A ∨ B) → (sq Γ2 ⊢ C) → (sq Γ3 ⊢ C) →
  (sq Γ1, Γ2 \ {A}, Γ3 \ {B} ⊢ C), axiom.
subj_intro. (sq Γ ⊢ B) → (sq Γ \ {A} ⊢ A → B), axiom.
subj_elim. (sq Γ1 ⊢ A → B) → (sq Γ2 ⊢ A) → (sq Γ1, Γ2 ⊢ B), axiom.
neg_intro. (sq Γ ⊢ ⊥) → (sq Γ \ {A} ⊢ ¬A), axiom.
neg_elim. (sq Γ1 ⊢ ¬A) → (sq Γ2 ⊢ A) → (sq Γ1, Γ2 ⊢ ⊥), axiom.
bij_intro. (sq Γ1 ⊢ A → B) → (sq Γ2 ⊢ B → A) → (sq Γ1, Γ2 ⊢ A ↔ B), axiom.
bij_eliml. (sq Γ ⊢ A ↔ B) → (sq Γ ⊢ A → B), axiom.
bij_elimr. (sq Γ ⊢ A ↔ B) → (sq Γ ⊢ B → A), axiom.
"""

def main():
    if argv[1] == "-f":
        text = format_source_code(read_all(argv[2]))
        if len(argv) == 4:
            with open(argv[3], "w") as fout:
                fout.write(text)
        else:
            print(text)
    else:
        book = {}
        verify(book, rules)
        verify(book, read_all(argv[1]))

main()
