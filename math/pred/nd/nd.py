#!/usr/bin/env python3

# A small natural deduction proof verifier for predicate logic.
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

sym2 = {"->": "->", "=>": "->", "|-": "|-", "/\\": "&", "\\/": "\\/"}
sym3 = {"<->": "<->", "<=>": "<->", "_|_": "#f"}

keywords = {
    "false": "#f", "true": "#t", "and": "&", "or": "\\/", "not": "~",
    "box": "#box", "dia": "#dia", "forall": "#forall", "exists": "#exists",
    "in": "#in", "sub": "#sub", "fn": "#lambda", "cap": "#cap", "cup": "#cup"
}

def init_tables():
    global predicate_symbols, function_symbols
    predicate_symbols = {"element": 2, "eq": 2}
    function_symbols = {"comp": 1}

init_tables()

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

def fmt_ast(t):
    if isinstance(t, str):
        return t
    else:
        return "(" + " ".join(fmt_ast(x) for x in t) + ")"

def fmt_subst(subst):
    return "{" + ", ".join(f"{A}: {fmt_ast(B)}" for (A, B) in subst.items()) + "}"

def is_identifier(t):
    return isinstance(t, str) and t[0].isalpha()

def is_unique_variable(t):
    return isinstance(t, str) and t[0] == '$'

var_count = 0
def unique_variable():
    global var_count
    var_count += 1
    return "$" + str(var_count)

def substitute_term_in_term(t, x, u):
    if is_unique_variable(t) or is_identifier(t):
        if isinstance(x, list):
            for i in range(len(x)):
                return u[i] if t == x[i] else t
        else:
            return u if t == x else t
    elif isinstance(t, tuple):
        return (t[0],) + tuple(substitute_term(s, x, u) for s in t[1:])
    else:
        return t

def substitute_term(t, x, u):
    if isinstance(t, tuple):
        if t[0] == "app":
            return (t[0], t[1]) + tuple(substitute_term_in_term(s, x, u) for s in t[2:])
        else:
            return (t[0],) + tuple(substitute_term(s, x, u) for s in t[1:])
    else:
        return t

def free_variables_term(t, fv):
    if is_identifier(t):
        fv.add(t)
    return fv

def free_variables(t, fv):
    if is_identifier(t):
        return fv
    elif isinstance(t, tuple):
        if t[0] == "app":
            free_variables_term(t[2], fv)
        else:
            for s in t[1:]:
                free_variables(s, fv)
        return fv

def free_variables_context(Gamma, fv):
    for A in Gamma:
        free_variables(A, fv)
    return fv

def form_eq(A, B):
    if isinstance(A, tuple):
        if not isinstance(B, tuple) or len(A) != len(B):
            return False
        if A[0] != B[0]: return False
        if A[0] == "forall" or A[0] == "exists" or A[0] == "lambda":
            u = unique_variable()
            A = substitute_term(A[2], A[1], u)
            B = substitute_term(B[2], B[1], u)
            return form_eq(A, B)
        else:
            for i in range(len(A)):
                if not form_eq(A[i], B[i]): return False
            return True
    else:
        return A == B

def form_in(A, Gamma):
    for X in Gamma:
        if form_eq(A, X): return True
    return False

def ctx_eq(Gamma1, Gamma2):
    if len(Gamma1) != len(Gamma2):
        return False
    for i in range(len(Gamma1)):
        if not form_eq(Gamma1[i], Gamma2[i]):
            return False
    return True

def seq_eq(S1, S2):
    Gamma1, A = S1; Gamma2, B = S2
    return ctx_eq(Gamma1, Gamma2) and form_eq(A, B)

def quantifier(a, i, op):
    token = a[i][0]
    if is_identifier(token):
        var = token; i += 1
    else:
        raise SyntaxError(a[i][1], "expected a variable")
    if a[i][0] == ":" or a[i][0] == ".":
        i += 1
    else:
        raise SyntaxError(a[i][1], "expected ':'")
    i, x = bijunction(a, i)
    u = unique_variable()
    x = substitute_term(x, var, u)
    return i, (op, u, x)

def lambda_term(a, i):
    token = a[i][0]
    if is_identifier(token):
        var = token; i += 1
    else:
        raise SyntaxError(a[i][1], "expected a variable")
    if a[i][0] == ":" or a[i][0] == ".":
        i += 1
    else:
        raise SyntaxError(a[i][1], "expected ':'")
    i, x = bijunction(a, i)
    u = unique_variable()
    x = substitute_term(x, var, u)
    return i, ("lambda", u, x)

def set_literal(a, i, x):
    x = ("app", "sg", x)
    while a[i][0] == ",":
        i, y = addition(a, i + 1)
        x = ("app", "union2", x, ("app", "sg", y))
    if a[i][0] != "}":
        raise SyntaxError(a[i][1], "expected '}'")
    return i + 1, x

def comprehension(a, i):
    line = a[i][1]
    i, x = addition(a, i)
    if a[i][0] == "," or a[i][0] == "}":
        return set_literal(a, i, x)
    elif a[i][0] != "|":
        raise SyntaxError(a[i][1], "expected '|'")
    if not is_identifier(x):
        raise SyntaxError(line, "expected identifier after '{'")
    i, A = bijunction(a, i + 1)
    if a[i][0] != "}":
        raise SyntaxError(a[i][1], "expected '}'")
    u = unique_variable()
    A = substitute_term(A, x, u)
    return i + 1, ("app", "comp", ("lambda", u, A))

def atom(a, i):
    token = a[i][0]
    if is_identifier(token):
        return i + 1, token
    elif token == "#f" or token == "⊥":
        return i + 1, ("false",)
    elif token == "#t":
        return i + 1, ("true",)
    elif token == "(":
        i, x = bijunction(a, i + 1)
        if a[i][0] == ",":
            i, y = addition(a, i + 1)
            x = ("app", "pair", x, y)
        if a[i][0] != ")":
            raise SyntaxError(a[i][1], "expected ')'")
        return i + 1, x
    elif token == "#forall" or token == "∀":
        return quantifier(a, i + 1, "forall")
    elif token == "#exists" or token == "∃":
        return quantifier(a, i + 1, "exists")
    elif token == "#lambda":
        return lambda_term(a, i + 1)
    elif token == "{":
        return comprehension(a, i + 1)
    else:
        raise SyntaxError(a[i][1], "expected an atom, but got '{}'".format(token))

def application(a, i):
    i, x = atom(a, i)
    if is_identifier(a[i][0]) or a[i][0] == "(" or a[i][0] == "{":
        args = []
        while is_identifier(a[i][0]) or a[i][0] == "(" or a[i][0] == "{":
            i, y = atom(a, i)
            args.append(y)
        return i, ("app", x) + tuple(args)
    else:
        return i, x

def multiplication(a, i):
    i, x = application(a, i)
    while a[i][0] == "#cap" or a[i][0] == "∩":
        i, y = application(a, i + 1)
        x = ("app", "intersection", x, y)
    return i, x

def addition(a, i):
    i, x = multiplication(a, i)
    while a[i][0] == "#cup" or a[i][0] == "∪":
        i, y = multiplication(a, i + 1)
        x = ("app", "union", x, y)
    return i, x

def relation(a, i):
    i, x = addition(a, i)
    if a[i][0] == "#in" or a[i][0] == "∈":
        i, y = addition(a, i + 1)
        return i, ("app", "element", x, y)
    elif a[i][0] == "#sub" or a[i][0] == "⊆":
        i, y = addition(a, i + 1)
        return i, ("app", "subset", x, y)
    elif a[i][0] == "=":
        i, y = addition(a, i + 1)
        return i, ("app", "eq", x, y)
    else:
        return i, x

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
        return relation(a, i)

def conjunction(a, i):
    i, x = negation(a, i)
    while a[i][0] == "&" or a[i][0] == "∧":
        i, y = negation(a, i + 1)
        x = ("conj", x, y)
    return i, x

def disjunction(a, i):
    i, x = conjunction(a, i)
    while a[i][0] == "\\/" or a[i][0] == "∨":
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
        if not form_in(X, Gamma1):
            Gamma.append(X)
    return tuple(Gamma)

def difference(Gamma, A):
    return tuple(X for X in Gamma if not form_eq(X, A))

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
    if not form_in(A, Gamma):
        raise LogicError(line, "not a basic sequent")

def conj_intro(line, book, S, args):
    assert len(args) == 2
    Gamma1, A = book[args[0]]
    Gamma2, B = book[args[1]]
    S0 = (union(Gamma1, Gamma2), ("conj", A, B))
    if not seq_eq(S, S0):
        raise LogicError(line, "conj_intro produces different sequent")

def conj_eliml(line, book, S, args):
    assert len(args) == 1
    Gamma, C = book[args[0]]
    if not isinstance(C, tuple) or C[0] != "conj":
        raise LogicError(line, "conj_eliml expected a conjunction")
    S0 = (Gamma, C[1])
    if not seq_eq(S, S0):
        raise LogicError(line, "conj_eliml produces different sequent")
        
def conj_elimr(line, book, S, args):
    assert len(args) == 1
    Gamma, C = book[args[0]]
    if not isinstance(C, tuple) or C[0] != "conj":
        raise LogicError(line, "conj_elimr expected a conjunction")
    S0 = (Gamma, C[2])
    if not seq_eq(S, S0):
        raise LogicError(line, "conj_elimr produces different sequent")

def subj_intro(line, book, S, args):
    assert len(args) == 1
    Gamma, B = book[args[0]]
    C = S[1]
    if not isinstance(C, tuple) or C[0] != "subj":
        raise LogicError(line, "subj_intro produces different sequent")
    A = C[1]
    if not form_in(A, Gamma):
        raise LogicError(line, "subj_intro failed: {} not in {}".format(A, Gamma))
    S0 = (difference(Gamma, A), ("subj", A, B))
    if not seq_eq(S, S0):
        raise LogicError(line, "subj_intro produces different sequent")

def subj_elim(line, book, S, args):
    assert len(args) == 2
    Gamma1, C = book[args[0]]
    Gamma2, A = book[args[1]]
    if not isinstance(C, tuple) or C[0] != "subj" or not form_eq(C[1], A):
        raise LogicError(line, "subj_elim expected a matching subjunction")
    S0 = (union(Gamma1, Gamma2), C[2])
    if not seq_eq(S, S0):
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
    if not form_in(A, Gamma):
        raise LogicError(line, "neg_intro failed: {} not in {}".format(A, Gamma))
    S0 = (difference(Gamma, A), ("neg", A))
    if not seq_eq(S, S0):
        raise LogicError(line, "neg_intro produces different sequent")

def neg_elim(line, book, S, args):
    assert len(args) == 2
    Gamma1, C = book[args[0]]
    Gamma2, A = book[args[1]]
    if not isinstance(C, tuple) or C[0] != "neg" or not form_eq(C[1], A):
        raise LogicError(line, "neg_elim expected a matching negation")
    S0 = (union(Gamma1, Gamma2), ("false",))
    if not seq_eq(S, S0):
        raise LogicError(line, "neg_elim produces different sequent")

def disj_introl(line, book, S, args):
    assert len(args) == 1
    Gamma, A = book[args[0]]
    C = S[1]
    if not isinstance(C, tuple) or C[0] != "disj":
        raise LogicError(line, "disj_introl produces different sequent")
    S0 = (Gamma, ("disj", A, C[2]))
    if not seq_eq(S, S0):
        raise LogicError(line, "disj_introl produces different sequent")

def disj_intror(line, book, S, args):
    assert len(args) == 1
    Gamma, A = book[args[0]]
    C = S[1]
    if not isinstance(C, tuple) or C[0] != "disj":
        raise LogicError(line, "disj_introl produces different sequent")
    S0 = (Gamma, ("disj", C[1], A))
    if not seq_eq(S, S0):
        raise LogicError(line, "disj_introl produces different sequent")

def disj_elim(line, book, S, args):
    assert len(args) == 3
    Gamma1, D = book[args[0]]
    Gamma2, C2 = book[args[1]]
    Gamma3, C3 = book[args[2]]
    if not isinstance(D, tuple) or D[0] != "disj":
        raise LogicError(line, "disj_elim expects a disjunction")
    if not form_eq(C2, C3):
        raise LogicError(line, "disj_elim expects the same proposition in each case")
    Gamma23 = union(difference(Gamma2, D[1]), difference(Gamma3, D[2]))
    S0 = (union(Gamma1, Gamma23), C2)
    if not seq_eq(S, S0):
        raise LogicError(line, "disj_elim produces different sequent")

def bij_intro(line, book, S, args):
    assert len(args) == 2
    Gamma1, A = book[args[0]]
    Gamma2, B = book[args[1]]
    if (not isinstance(A, tuple) or A[0] != "subj" or
        not isinstance(B, tuple) or B[0] != "subj" or
       not form_eq(A[1], B[2]) or not form_eq(A[2], B[1])):
        raise LogicError(line, "bij_intro expects matching subjunctions")
    S0 = (union(Gamma1, Gamma2), ("bij", A[1], A[2]))
    if not seq_eq(S, S0):
        raise LogicError(line, "bij_intro produces different sequent")

def bij_eliml(line, book, S, args):
    assert len(args) == 1
    Gamma, A = book[args[0]]
    if not isinstance(A, tuple) or A[0] != "bij":
        raise LogicError(line, "bij_eliml expects a bijunction")
    S0 = (Gamma, ("subj", A[1], A[2]))
    if not seq_eq(S, S0):
        raise LogicError(line, "bij_eliml produces different sequent")

def bij_elimr(line, book, S, args):
    assert len(args) == 1
    Gamma, A = book[args[0]]
    if not isinstance(A, tuple) or A[0] != "bij":
        raise LogicError(line, "bij_elimr expects a bijunction")
    S0 = (Gamma, ("subj", A[2], A[1]))
    if not seq_eq(S, S0):
        raise LogicError(line, "bij_elimr produces different sequent")

def axiom(line, book, S, args):
    assert len(args) == 0
    if not S[0] == ():
        raise LogicError(line, "axiom expects empty context")

def unify_pred(A, pattern, subst):
    P = pattern[1]; args = list(pattern[2:])
    if P in subst:
        P = subst[P]
        if not callable(P): return False
        B = P(args)
        return form_eq(A, B)
    else:
        subst[P] = lambda argv: substitute_term(A, args, argv)
        return True

def unify(A, pattern, subst):
    if isinstance(pattern, str):
        if pattern in predicate_symbols or pattern in function_symbols:
            return pattern == A
        elif pattern in subst:
            if not form_eq(subst[pattern], A): return False
        else:
            subst[pattern] = A
    else:
        if pattern[0] == "app" and not pattern[1] in predicate_symbols:
            return unify_pred(A, pattern, subst)
        if not isinstance(A, tuple): return False
        if not len(A) == len(pattern): return False
        if not A[0] == pattern[0]: return False
        if A[0] == "forall" or A[0] == "exists" or A[0] == "lambda":
            u = unique_variable()
            A = substitute_term(A[2], A[1], u)
            B = substitute_term(pattern[2], pattern[1], u)
            return unify(A, B, subst)
        for i in range(1, len(A)):
            if not unify(A[i], pattern[i], subst):
                return False
    return True

def unify_quant(A, pattern, subst):
    if isinstance(pattern, str):
        if pattern in predicate_symbols or pattern in function_symbols:
            return pattern == A
        elif pattern in subst:
            if not form_eq(subst[pattern], A):
                return False
        else:
            subst[pattern] = A
    else:
        if not isinstance(A, tuple): return False
        if not len(A) == len(pattern): return False
        if not A[0] == pattern[0]: return False
        for i in range(1, len(A)):
            if not unify_quant(A[i], pattern[i], subst):
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
    if not seq_eq(S, S0):
        raise LogicError(line, "box_intro produces different sequent")

def uq_intro(line, book, S, args):
    assert len(args) == 1
    Gamma, A = book[args[0]]
    uqA = S[1]
    if not isinstance(uqA, tuple) or uqA[0] != "forall":
        raise LogicError(line, "uq_intro produces a universal quantifier")
    subs = {}
    if not unify_quant(A, uqA[2], subs):
        raise LogicError(line, "uq_intro: unification failed")
    var = uqA[1]
    if var in subs:
        var = subs[var]
        if var in free_variables_context(Gamma, set()):
            raise LogicError(line, f"uq_intro: variable {var} cannot be generalized")
    if not ctx_eq(Gamma, S[0]):
        raise LogicError(line, "uq_intro produces different sequent")

def uq_elim(line, book, S, args):
    assert len(args) == 1
    Gamma, A = book[args[0]]
    if not isinstance(A, tuple) or A[0] != "forall":
        raise LogicError(line, "uq_elim expects a universal quantifier")
    subs = {}
    if not unify_quant(S[1], A[2], subs):
        raise LogicError(line, "uq_elim: unification failed")
    if not ctx_eq(Gamma, S[0]):
        raise LogicError(line, "uq_elim produces different sequent")

def ex_intro(line, book, S, args):
    assert len(args) == 1
    Gamma, A = book[args[0]]
    if not isinstance(S[1], tuple) or S[1][0] != "exists":
        raise LogicError(line, "ex_intro produces a existential quantifier")
    exA = S[1]; subs = {}
    if not unify_quant(A, exA[2], subs):
        raise LogicError(line, "ex_intro: unification failed")
    if not ctx_eq(Gamma, S[0]):
        raise LogicError(line, "ex_intro produces different sequent")

def ex_elim(line, book, S, args):
    assert len(args) == 2
    Gamma1, exA = book[args[0]]
    Gamma2, B = book[args[1]]
    if not isinstance(exA, tuple) or exA[0] != "exists":
        raise LogicError(line, "ex_elim expects an existential quantifier")
    if not len(Gamma2) != 0:
        raise LogicError(line, "ex_elim context of second sequent is empty")
    A = Gamma2[-1]; Gamma2 = Gamma2[:-1]
    subs = {}
    if not unify_quant(A, exA[2], subs):
        raise LogicError(line, "ex_elim: unification failed")
    var = exA[1]
    if var in subs:
        var = subs[var]
        if (var in free_variables_context(Gamma1, set()) or
            var in free_variables_context(Gamma2, set()) or
            var in free_variables(B, set()) or
            var in free_variables(exA, set())):
            raise LogicError(line, f"ex_elim: formulas depend on variable {var}")
    S0 = (union(Gamma1, Gamma2), B)
    if not seq_eq(S, S0):
        raise LogicError(line, "ex_elim produces different sequent")

def definition(line, book, S, args):
    assert len(args) == 0
    Gamma, C = S
    if len(Gamma) != 0:
        raise LogicError(line, "definition expects empty context")
    if isinstance(C, tuple) and C[0] == "bij":
        A = C[1]; B = C[2]
        if not isinstance(A, tuple) or A[0] != "app":
            raise LogicError(line, "malformed definition")
        if A[1] in predicate_symbols:
            raise LogicError(line, "already defined")
        predicate_symbols[A[1]] = len(A) - 2
    elif isinstance(C, tuple) and C[0] == "app" and C[1] == "eq":
        A = C[2]; B = C[3]
        if isinstance(A, str):
            if A in function_symbols:
                raise LogicError(line, "already defined")
            function_symbols[A] = 0
        else:
            if not isinstance(A, tuple) or A[0] != "app":
                raise LogicError(line, "malformed definition")
            if A[1] in function_symbols:
                raise LogicError(line, "already defined")
            function_symbols[A[1]] = len(A) - 2
    else:
        raise LogicError(line, "malformed definition")

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
    "box_intro": box_intro,
    "uq_intro": uq_intro,
    "uq_elim": uq_elim,
    "ex_intro": ex_intro,
    "ex_elim": ex_elim,
    "def": definition
}

def verify_plain(s):
    statements = parse(s)
    book = {}
    for (line, label, Gamma, A, rule) in statements:
        book[label] = (None, A)
        Gamma = tuple(book[k][1] for k in Gamma)
        book[label] = (Gamma, A)
        if not rule[0] in verify_tab:
            raise LogicError(line, "rule {} not found".format(rule[0]))
        verify_tab[rule[0]](line, book, (Gamma, A), rule[1:])

def verify(s):
    try:
        verify_plain(s)
    except SyntaxError as e:
        print("Syntax error in line {}:\n{}".format(e.line, e.text))
    except LogicError as e:
        print("Logic error in line {}:\n{}".format(e.line, e.text))

fmt1_tab = {"&": "∧", "~": "¬"}
fmt2_tab = {"->": "→", "=>": "→", "|-": "⊢", "/\\": "∧", "\\/": "∨"}
fmt3_tab = {"<->": "↔", "<=>": "↔", "_|_": "⊥"}
fmt_kw_tab = {"not": "¬", "and": "∧", "or": "∨", "false": "⊥",
   "box": "□", "dia": "◇", "forall": "∀", "exists": "∃",
   "in": "∈", "sub": "⊆", "cap": "∩", "cup": "∪"}
trim_tab = {"¬", "□", "◇", "∀", "∃"}

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

if __name__ == "__main__":
    main()

