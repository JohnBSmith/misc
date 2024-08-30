#!/usr/bin/env python3

# A small natural deduction proof verifier for first order logic.
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

class Formula:
    def __init__(self, node):
        self.node = node
    def __repr__(self):
        if isinstance(self.node, tuple):
            return "FORM(" + ", ".join(str(x) for x in self.node) + ")"
        else:
            return "FORM " + str(self.node)
    def __eq__(self, y):
        return isinstance(y, Formula) and self.node == y.node

class Term:
    def __init__(self, node):
        self.node = node
    def __repr__(self):
        if isinstance(self.node, tuple):
            return "TERM(" + ", ".join(str(x) for x in self.node) + ")"
        else:
            return "TERM " + str(self.node)
    def __eq__(self, y):
        return isinstance(y, Term) and self.node == y.node

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
            while i < n and (s[i].isalpha() or s[i].isdigit() or s[i] in "_'"):
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

def substitute_term(t, x, u):
    if isinstance(t, Formula):
        if isinstance(t.node, tuple):
            return Formula((t.node[0],) + tuple(substitute_term(s, x, u) for s in t.node[1:]))
        else:
            return t
    elif isinstance(t, Term):
        if is_unique_variable(t.node) or is_identifier(t.node):
            if isinstance(x, list):
                for i in range(len(x)):
                    return u[i] if t == x[i] else t
            else:
                return u if t == x else t
        else:
            return Term((t.node[0],) + tuple(substitute_term(s, x, u) for s in t.node[1:]))
    else:
        return t

def free_variables(t, fv):
    if isinstance(t, Formula) and is_identifier(t.node):
        return fv
    elif isinstance(t, Term) and is_identifier(t.node):
        fv.add(t.node)
        return fv
    elif (isinstance(t, Formula) or isinstance(t, Term)
    and isinstance(t.node, tuple)):
        if t.node[0] == "app":
            for s in t.node[2:]:
                free_variables(s, fv)
        else:
            for s in t.node[1:]:
                free_variables(s, fv)
        return fv
    elif isinstance(t, str) and t[0] == "$":
        return fv
    elif isinstance(t, Term) and isinstance(t.node, str) and t.node[0] == "$":
        return fv
    else:
        raise Exception("unreachable")

def free_variables_context(Gamma, fv):
    for A in Gamma:
        free_variables(A, fv)
    return fv

def form_eq(A, B):
    if isinstance(A, Formula) or isinstance(A, Term):
        if type(A) != type(B): return False
        if isinstance(A.node, tuple):
            if not isinstance(B.node, tuple) or len(A.node) != len(B.node):
                return False
            if A.node[0] != B.node[0]: return False
            if A.node[0] == "forall" or A.node[0] == "exists" or A.node[0] == "lambda":
                u = unique_variable()
                A = substitute_term(A.node[2], Term(A.node[1]), Term(u))
                B = substitute_term(B.node[2], Term(B.node[1]), Term(u))
                return form_eq(A, B)
            else:
                for i in range(len(A.node)):
                    if not form_eq(A.node[i], B.node[i]): return False
                return True
        else:
            return A == B
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

def ensure_formula(t, line):
    if isinstance(t, Formula):
        return t
    elif isinstance(t, Term):
        raise SyntaxError(line, "expected a formula")
    else:
        return Formula(t)

def ensure_term(t, line):
    if isinstance(t, Term):
        return t
    elif isinstance(t, Formula):
        raise SyntaxError(line, "expected a term")
    else:
        return Term(t)

def quantifier(a, i, op):
    token = a[i][0]
    if is_identifier(token):
        var = Term(token); i += 1
    else:
        raise SyntaxError(a[i][1], "expected a variable")
    if a[i][0] == ":" or a[i][0] == ".":
        i += 1
    else:
        raise SyntaxError(a[i][1], "expected ':'")
    line = a[i][1]
    i, x = bijunction(a, i)
    x = ensure_formula(x, line)
    u = unique_variable()
    x = substitute_term(x, var, Term(u))
    return i, (op, u, x)

def lambda_term(a, i):
    token = a[i][0]
    if is_identifier(token):
        var = Term(token); i += 1
    else:
        raise SyntaxError(a[i][1], "expected a variable")
    if a[i][0] == ":" or a[i][0] == ".":
        i += 1
    else:
        raise SyntaxError(a[i][1], "expected ':'")
    i, x = bijunction(a, i)
    u = unique_variable()
    x = substitute_term(x, var, Term(u))
    return i, Term(("lambda", u, x))

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
    if is_identifier(x):
        x = Term(x)
    else:
        raise SyntaxError(line, "expected identifier after '{'")
    line = a[i][1]
    i, A = bijunction(a, i + 1)
    A = ensure_formula(A, line)
    if a[i][0] != "}":
        raise SyntaxError(a[i][1], "expected '}'")
    u = unique_variable()
    A = substitute_term(A, x, Term(u))
    return i + 1, Term(("app", "comp", Term(("lambda", u, A))))

def typed(t, token, SortArgs, SortValue):
    line = token[1]
    if isinstance(t, tuple):
        acc = []
        if t[0] == "app":
            acc.append(t[1])
            start_index = 2
        else:
            start_index = 1
        for x in t[start_index:]:
            if isinstance(x, SortArgs):
                acc.append(x)
            elif isinstance(x, str) or isinstance(x, tuple):
                acc.append(SortArgs(x))
            else:
                sort = "term" if SortArgs == Term else "formula"
                raise SyntaxError(line, f"{token[0]} expects a {sort}")
        return SortValue((t[0],) + tuple(acc))
    else:
        raise Exception("unreachable")

def formula(t, token, Sort):
    return typed(t, token, Sort, Formula)

def term(t, token, Sort):
    return typed(t, token, Sort, Term)

def atom(a, i):
    token = a[i][0]
    if is_identifier(token):
        return i + 1, token
    elif token == "#f" or token == "⊥":
        return i + 1, Formula(("false",))
    elif token == "#t":
        return i + 1, Formula(("true",))
    elif token == "(":
        i, x = bijunction(a, i + 1)
        if a[i][0] == ",":
            i, y = addition(a, i + 1)
            x = term(("app", "pair", x, y), a[i], Term)
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
            line = a[i][1]
            i, y = atom(a, i)
            args.append(ensure_term(y, line))
        return i, ("app", x) + tuple(args)
    else:
        return i, x

def multiplication(a, i):
    i, x = application(a, i)
    while a[i][0] == "#cap" or a[i][0] == "∩":
        token = a[i]
        i, y = application(a, i + 1)
        x = term(("app", "intersection", x, y), token, Term)
    return i, x

def addition(a, i):
    i, x = multiplication(a, i)
    while a[i][0] == "#cup" or a[i][0] == "∪":
        token = a[i]
        i, y = multiplication(a, i + 1)
        x = term(("app", "union", x, y), token, Term)
    return i, x

def relation(a, i):
    i, x = addition(a, i)
    token = a[i]
    if a[i][0] == "#in" or a[i][0] == "∈":
        i, y = addition(a, i + 1)
        return i, formula(("app", "element", x, y), token, Term)
    elif a[i][0] == "#sub" or a[i][0] == "⊆":
        i, y = addition(a, i + 1)
        return i, formula(("app", "subset", x, y), token, Term)
    elif a[i][0] == "=":
        i, y = addition(a, i + 1)
        return i, formula(("app", "eq", x, y), token, Term)
    else:
        return i, x

def negation(a, i):
    token = a[i]
    if token[0] == "~" or token[0] == "¬":
        i, x = negation(a, i + 1)
        return i, formula(("neg", x), token, Formula)
    elif token[0] == "#box" or token[0] == "□":
        i, x = negation(a, i + 1)
        return i, formula(("box", x), token, Formula)
    elif token[0] == "#dia" or token[0] == "◇":
        i, x = negation(a, i + 1)
        return i, formula(("dia", x), token, Formula)
    else:
        return relation(a, i)

def conjunction(a, i):
    i, x = negation(a, i)
    while a[i][0] == "&" or a[i][0] == "∧":
        token = a[i]
        i, y = negation(a, i + 1)
        x = formula(("conj", x, y), token, Formula)
    return i, x

def disjunction(a, i):
    i, x = conjunction(a, i)
    while a[i][0] == "\\/" or a[i][0] == "∨":
        token = a[i]
        i, y = conjunction(a, i + 1)
        x = formula(("disj", x, y), token, Formula)
    return i, x
    
def subjunction(a, i):
    i, x = disjunction(a, i)
    token = a[i]
    if token[0] == "->" or token[0] == "→" or token[0] == "⇒":
        i, y = subjunction(a, i + 1)
        return i, formula(("subj", x, y), token, Formula)
    else:
        return i, x

def bijunction(a, i):
    i, x = subjunction(a, i)
    token = a[i]
    if token[0] == "<->" or token[0] == "↔" or token[0] == "⇔":
        i, y = subjunction(a, i + 1)
        return i, formula(("bij", x, y), token, Formula)
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
        line = a[i][1]
        i, x = bijunction(a, i + 1)
        x = ensure_formula(x, line)
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

def lookup(book, key, line):
    if not key in book:
        raise LogicError(line, f"label '{key}' not found")
    else:
        return book[key]

def expect_len(line, args, n, rule_name):
    s = "" if n == 1 else "s"
    raise LogicError(line,
        f"rule {rule_name} expects {n} argument{s}, but got {len(args)}")

def is_connective(A, symbol):
    return isinstance(A, Formula) and isinstance(A.node, tuple) and A.node[0] == symbol

def basic_seq(line, book, S, args):
    if len(args) != 0: expect_len(line, args, 0, "basic")
    Gamma, A = S
    if not form_in(A, Gamma):
        raise LogicError(line, "not a basic sequent")

def conj_intro(line, book, S, args):
    if len(args) != 2: expect_len(line, args, 2, "conj_intro")
    Gamma1, A = lookup(book, args[0], line)
    Gamma2, B = lookup(book, args[1], line)
    S0 = (union(Gamma1, Gamma2), Formula(("conj", A, B)))
    if not seq_eq(S, S0):
        raise LogicError(line, "conj_intro produces different sequent")

def conj_eliml(line, book, S, args):
    if len(args) != 1: expect_len(line, args, 1, "conj_eliml")
    Gamma, C = lookup(book, args[0], line)
    if not is_connective(C, "conj"):
        raise LogicError(line, "conj_eliml expected a conjunction")
    S0 = (Gamma, C.node[1])
    if not seq_eq(S, S0):
        raise LogicError(line, "conj_eliml produces different sequent")

def conj_elimr(line, book, S, args):
    if len(args) != 1: expect_len(line, args, 1, "conj_elimr")
    Gamma, C = lookup(book, args[0], line)
    if not is_connective(C, "conj"):
        raise LogicError(line, "conj_elimr expected a conjunction")
    S0 = (Gamma, C.node[2])
    if not seq_eq(S, S0):
        raise LogicError(line, "conj_elimr produces different sequent")

def subj_intro(line, book, S, args):
    if len(args) != 1: expect_len(line, args, 1, "subj_intro")
    Gamma, B = lookup(book, args[0], line)
    C = S[1]
    if not is_connective(C, "subj"):
        raise LogicError(line, "subj_intro produces different sequent")
    A = C.node[1]
    if not form_in(A, Gamma):
        raise LogicError(line, "subj_intro failed: {} not in {}".format(A, Gamma))
    S0 = (difference(Gamma, A), Formula(("subj", A, B)))
    if not seq_eq(S, S0):
        raise LogicError(line, "subj_intro produces different sequent")

def subj_elim(line, book, S, args):
    if len(args) != 2: expect_len(line, args, 2, "subj_elim")
    Gamma1, C = lookup(book, args[0], line)
    Gamma2, A = lookup(book, args[1], line)
    if not is_connective(C, "subj") or not form_eq(C.node[1], A):
        raise LogicError(line, "subj_elim expected a matching subjunction")
    S0 = (union(Gamma1, Gamma2), C.node[2])
    if not seq_eq(S, S0):
        raise LogicError(line, "subj_elim produces different sequent")

def neg_intro(line, book, S, args):
    if len(args) != 1: expect_len(line, args, 1, "neg_intro")
    Gamma, B = lookup(book, args[0], line)
    C = S[1]
    if not is_connective(C, "neg"):
        raise LogicError(line, "neg_intro produces different sequent")
    if B != Formula(("false",)):
        raise LogicError(line, "neg_intro expects ⊥")
    A = C.node[1]
    if not form_in(A, Gamma):
        raise LogicError(line, "neg_intro failed: {} not in {}".format(A, Gamma))
    S0 = (difference(Gamma, A), Formula(("neg", A)))
    if not seq_eq(S, S0):
        raise LogicError(line, "neg_intro produces different sequent")

def neg_elim(line, book, S, args):
    if len(args) != 2: expect_len(line, args, 2, "neg_elim")
    Gamma1, C = lookup(book, args[0], line)
    Gamma2, A = lookup(book, args[1], line)
    if not is_connective(C, "neg") or not form_eq(C.node[1], A):
        raise LogicError(line, "neg_elim expected a matching negation")
    S0 = (union(Gamma1, Gamma2), Formula(("false",)))
    if not seq_eq(S, S0):
        raise LogicError(line, "neg_elim produces different sequent")

def disj_introl(line, book, S, args):
    if len(args) != 1: expect_len(line, args, 1, "disj_introl")
    Gamma, A = lookup(book, args[0], line)
    C = S[1]
    if not is_connective(C, "disj"):
        raise LogicError(line, "disj_introl produces different sequent")
    S0 = (Gamma, Formula(("disj", A, C.node[2])))
    if not seq_eq(S, S0):
        raise LogicError(line, "disj_introl produces different sequent")

def disj_intror(line, book, S, args):
    if len(args) != 1: expect_len(line, args, 1, "disj_intror")
    Gamma, A = lookup(book, args[0], line)
    C = S[1]
    if not is_connective(C, "disj"):
        raise LogicError(line, "disj_introl produces different sequent")
    S0 = (Gamma, Formula(("disj", C.node[1], A)))
    if not seq_eq(S, S0):
        raise LogicError(line, "disj_introl produces different sequent")

def disj_elim(line, book, S, args):
    if len(args) != 3: expect_len(line, args, 3, "disj_elim")
    Gamma1, D = lookup(book, args[0], line)
    Gamma2, C2 = lookup(book, args[1], line)
    Gamma3, C3 = lookup(book, args[2], line)
    if not is_connective(D, "disj"):
        raise LogicError(line, "disj_elim expects a disjunction")
    if not form_eq(C2, C3):
        raise LogicError(line, "disj_elim expects the same proposition in each case")
    Gamma23 = union(difference(Gamma2, D.node[1]), difference(Gamma3, D.node[2]))
    S0 = (union(Gamma1, Gamma23), C2)
    if not seq_eq(S, S0):
        raise LogicError(line, "disj_elim produces different sequent")

def bij_intro(line, book, S, args):
    if len(args) != 2: expect_len(line, args, 2, "bij_intro")
    Gamma1, A = lookup(book, args[0], line)
    Gamma2, B = lookup(book, args[1], line)
    if (not is_connective(A, "subj") or not is_connective(B, "subj") or
        not form_eq(A.node[1], B.node[2]) or not form_eq(A.node[2], B.node[1])):
        raise LogicError(line, "bij_intro expects matching subjunctions")
    S0 = (union(Gamma1, Gamma2), Formula(("bij", A.node[1], A.node[2])))
    if not seq_eq(S, S0):
        raise LogicError(line, "bij_intro produces different sequent")

def bij_eliml(line, book, S, args):
    if len(args) != 1: expect_len(line, args, 1, "bij_eliml")
    Gamma, A = lookup(book, args[0], line)
    if not is_connective(A, "bij"):
        raise LogicError(line, "bij_eliml expects a bijunction")
    S0 = (Gamma, Formula(("subj", A.node[1], A.node[2])))
    if not seq_eq(S, S0):
        raise LogicError(line, "bij_eliml produces different sequent")

def bij_elimr(line, book, S, args):
    if len(args) != 1: expect_len(line, args, 1, "bij_elimr")
    Gamma, A = lookup(book, args[0], line)
    if not is_connective(A, "bij"):
        raise LogicError(line, "bij_elimr expects a bijunction")
    S0 = (Gamma, Formula(("subj", A.node[2], A.node[1])))
    if not seq_eq(S, S0):
        raise LogicError(line, "bij_elimr produces different sequent")

def axiom(line, book, S, args):
    if len(args) != 0: expect_len(line, args, 0, "axiom")
    if not S[0] == ():
        raise LogicError(line, "axiom expects empty context")

def unify_pred(A, pattern, subst):
    P = pattern.node[1]; args = list(pattern.node[2:])
    if P in subst:
        P = subst[P]
        if not callable(P): return False
        B = P(args)
        return form_eq(A, B)
    else:
        subst[P] = lambda argv: substitute_term(A, args, argv)
        return True

def unify(A, pattern, subst):
    if isinstance(pattern, Formula) and isinstance(pattern.node, str):
        if pattern.node in predicate_symbols or pattern.node in function_symbols:
            return pattern == A
        elif pattern.node in subst:
            if not form_eq(subst[pattern.node], A): return False
        else:
            subst[pattern.node] = A
        return True
    elif isinstance(pattern, Term) and isinstance(pattern.node, str):
        return pattern == A
    elif isinstance(pattern, Formula) or isinstance(pattern, Term):
        if type(A) != type(pattern): return False
        if (isinstance(pattern, Formula) and pattern.node[0] == "app"
        and not pattern.node[1] in predicate_symbols):
            return unify_pred(A, pattern, subst)
        if not isinstance(A.node, tuple): return False
        if not len(A.node) == len(pattern.node): return False
        if not A.node[0] == pattern.node[0]: return False
        if A.node[0] == "forall" or A.node[0] == "exists" or A.node[0] == "lambda":
            u = unique_variable()
            A = substitute_term(A.node[2], Term(A.node[1]), Term(u))
            B = substitute_term(pattern.node[2], Term(pattern.node[1]), Term(u))
            return unify(A, B, subst)
        for i in range(1, len(A.node)):
            if not unify(A.node[i], pattern.node[i], subst):
                return False
        return True
    elif isinstance(pattern, str):
        return pattern == A
    else:
        raise Exception("unreachable")

def unify_quant(A, pattern, subst):
    if isinstance(pattern, Term) and isinstance(pattern.node, str):
        if pattern.node in predicate_symbols or pattern.node in function_symbols:
            return pattern == A
        elif pattern.node in subst:
            if not form_eq(subst[pattern.node], A):
                return False
        else:
            subst[pattern.node] = A
        return True
    elif isinstance(pattern, Formula) and isinstance(pattern.node, str):
        return pattern == A
    elif isinstance(pattern, Formula) or isinstance(pattern, Term):
        if type(A) != type(pattern): return False        
        if not isinstance(A.node, tuple): return False
        if not len(A.node) == len(pattern.node): return False
        if not A.node[0] == pattern.node[0]: return False
        if A.node[0] == "forall" or A.node[0] == "exists" or A.node[0] == "lambda":
            u = unique_variable()
            A = substitute_term(A.node[2], Term(A.node[1]), Term(u))
            B = substitute_term(pattern.node[2], Term(pattern.node[1]), Term(u))
            return unify_quant(A, B, subst)
        for i in range(1, len(A.node)):
            if not unify_quant(A.node[i], pattern.node[i], subst):
                return False
        return True
    elif isinstance(pattern, str):
        return pattern == A
    else:
        raise Exception("unreachable")

def substitution(line, book, S, args):
    if len(args) != 1: expect_len(line, args, 1, "subst")
    Gamma, A = lookup(book, args[0], line)
    if len(Gamma) != 0:
        raise LogicError(line, "subst expects a theorem")
    if len(S[0]) != 0:
        raise LogicError(line, "subst produces a theorem")
    if not unify(S[1], A, {}):
        raise LogicError(line, "subst: unification failed")

def term_substitution(line, book, S, args):
    if len(args) != 1: expect_len(line, args, 1, "tsubst")
    Gamma, A = lookup(book, args[0], line)
    if len(Gamma) != 0:
        raise LogicError(line, "tsubst expects a theorem")
    if len(S[0]) != 0:
        raise LogicError(line, "tsubst produces a theorem")
    if not unify_quant(S[1], A, {}):
        raise LogicError(line, "tsubst: unification failed")

def box_intro(line, book, S, args):
    if len(args) != 1: expect_len(line, args, 1, "box_intro")
    Gamma, A = lookup(book, args[0], line)
    if len(Gamma) != 0:
        raise LogicError(line, "box_intro expects a theorem")
    if len(S[0]) != 0:
        raise LogicError(line, "box_intro produces a theorem")
    S0 = (Gamma, ("box", A))
    if not seq_eq(S, S0):
        raise LogicError(line, "box_intro produces different sequent")

def uq_intro(line, book, S, args):
    if len(args) != 1: expect_len(line, args, 1, "uq_intro")
    Gamma, A = lookup(book, args[0], line)
    uqA = S[1]
    if not is_connective(uqA, "forall"):
        raise LogicError(line, "uq_intro produces a universal quantifier")
    subs = {}
    if not unify_quant(A, uqA.node[2], subs):
        raise LogicError(line, "uq_intro: unification failed")
    var = uqA.node[1]
    if var in subs:
        var = subs[var]
        if not isinstance(var, Term) or not isinstance(var.node, str):
            raise LogicError(line, "uq_intro expects a variable")
        if var.node in free_variables_context(Gamma, set()):
            raise LogicError(line, f"uq_intro: variable {var} cannot be generalized")
    if not ctx_eq(Gamma, S[0]):
        raise LogicError(line, "uq_intro produces different sequent")

def uq_elim(line, book, S, args):
    if len(args) != 1: expect_len(line, args, 1, "uq_elim")
    Gamma, A = lookup(book, args[0], line)
    if not is_connective(A, "forall"):
        raise LogicError(line, "uq_elim expects a universal quantifier")
    subs = {}
    if not unify_quant(S[1], A.node[2], subs):
        raise LogicError(line, "uq_elim: unification failed")
    if not ctx_eq(Gamma, S[0]):
        raise LogicError(line, "uq_elim produces different sequent")

def ex_intro(line, book, S, args):
    if len(args) != 1: expect_len(line, args, 1, "ex_intro")
    Gamma, A = lookup(book, args[0], line)
    if not is_connective(S[1], "exists"):
        raise LogicError(line, "ex_intro produces a existential quantifier")
    exA = S[1]; subs = {}
    if not unify_quant(A, exA.node[2], subs):
        raise LogicError(line, "ex_intro: unification failed")
    if not ctx_eq(Gamma, S[0]):
        raise LogicError(line, "ex_intro produces different sequent")

def ex_elim(line, book, S, args):
    if len(args) != 2: expect_len(line, args, 2, "ex_elim")
    Gamma1, exA = lookup(book, args[0], line)
    Gamma2, B = lookup(book, args[1], line)
    if not is_connective(exA, "exists"):
        raise LogicError(line, "ex_elim expects an existential quantifier")
    if not len(Gamma2) != 0:
        raise LogicError(line, "ex_elim context of second sequent is empty")
    A = Gamma2[-1]; Gamma2 = Gamma2[:-1]
    subs = {}
    if not unify_quant(A, exA.node[2], subs):
        raise LogicError(line, "ex_elim: unification failed")
    var = exA.node[1]
    if var in subs:
        var = subs[var]
        if not isinstance(var, Term) or not isinstance(var.node, str):
            raise LogicError(line, "ex_elim expects a variable")
        var = var.node
        if (var in free_variables_context(Gamma1, set()) or
            var in free_variables_context(Gamma2, set()) or
            var in free_variables(B, set()) or
            var in free_variables(exA, set())):
            raise LogicError(line, f"ex_elim: formulas depend on variable {var}")
    S0 = (union(Gamma1, Gamma2), B)
    if not seq_eq(S, S0):
        raise LogicError(line, "ex_elim produces different sequent")

def definition(line, book, S, args):
    if len(args) != 0: expect_len(line, args, 0, "def")
    Gamma, C = S
    if len(Gamma) != 0:
        raise LogicError(line, "definition expects empty context")
    if is_connective(C, "bij"):
        A = C.node[1]; B = C.node[2]
        if not isinstance(A.node, tuple) or A.node[0] != "app":
            raise LogicError(line, "malformed definition")
        if A.node[1] in predicate_symbols:
            raise LogicError(line, "already defined")
        predicate_symbols[A.node[1]] = len(A.node) - 2
    elif (isinstance(C, Formula) and isinstance(C.node, tuple)
    and C.node[0] == "app" and C.node[1] == "eq"):
        A = C.node[2]; B = C.node[3]
        if isinstance(A.node, str):
            if A.node in function_symbols:
                raise LogicError(line, "already defined")
            function_symbols[A.node] = 0
        else:
            if not isinstance(A.node, tuple) or A.node[0] != "app":
                raise LogicError(line, "malformed definition")
            if A.node[1] in function_symbols:
                raise LogicError(line, "already defined")
            function_symbols[A.node[1]] = len(A.node) - 2
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
    "tsubst": term_substitution,
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
        Gamma = tuple(lookup(book, k, line)[1] for k in Gamma)
        book[label] = (Gamma, A)
        if not rule[0] in verify_tab:
            raise LogicError(line, "rule {} not found".format(rule[0]))
        args = rule[1:]
        if label in args:
            raise LogicError(line, "cyclic deduction")
        verify_tab[rule[0]](line, book, (Gamma, A), args)

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
