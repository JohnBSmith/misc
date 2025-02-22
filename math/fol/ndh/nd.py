#!/usr/bin/env python3

# A small natural deduction proof verifier for first order logic that
# allows inference rules to be stated as axioms of a Hilbert system in
# which sequents are treated as propositions.
#
# Note that the equivalence of A ∧ B ⊢ C and A, B ⊢ C is automatically
# applied in this verifier. As part of a rule, one can only type in the
# first one.
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

long = False
class Term:
    def __init__(self, node, type):
        self.node = node; self.type = type
    def __repr__(self):
        if type(self.node) is tuple:
            s = " ".join(str(x) for x in self.node)
            return f"({s}):{self.type}" if long else f"({s})"
        else:
            return f"{self.node}:{self.type}" if long else f"{self.node}"

Prop = "Prop"
Ind = "Ind"
Fn = "Fn"

def ensure_type(t, line, typ):
    if not type(t) is Term:
        print(t)
        raise ValueError("unreachable")
    if t.type is None:
        t.type = typ
    elif t.type != typ:
        raise SyntaxError(line, f"expected {t} to be of type {typ}")
    return t

def is_unique_variable(t):
    return type(t) is str and t[0] == '$'

var_count = 0
def unique_variable(typ):
    global var_count
    var_count += 1
    return Term("$" + str(var_count), typ)

def substitute_term(t, x, u):
    if type(t) is Term:
        if type(t.node) is tuple:
            return Term((t.node[0],) + tuple(substitute_term(s, x, u)
                for s in t.node[1:]), t.type)
        elif is_unique_variable(t.node) or is_identifier(t.node):
            if type(x) is list:
                for i in range(len(x)):
                    if t.node == x[i].node: return u[i]
            else:
                return u if t.node == x.node else t
    return t

def term_eq(A, B):
    if type(A) is Term:
        if A.type != B.type: return False
        if type(A.node) is tuple:
            if not type(B.node) is tuple or len(A.node) != len(B.node):
                return False
            if A.node[0] != B.node[0]: return False
            if A.node[0] in ("forall", "exists", "lambda"):
                u = unique_variable(Ind)
                A = substitute_term(A.node[2], Term(A.node[1], Ind), u)
                B = substitute_term(B.node[2], Term(B.node[1], Ind), u)
                return term_eq(A, B)
            else:
                for i in range(len(A.node)):
                    if not term_eq(A.node[i], B.node[i]): return False
                return True
        else:
            return A.node == B.node
    else:
        return A == B

def type_check(line, t, record, residual):
    if type(t) is Term and type(t.node) is str:
        if t.node in record:
            if record[t.node] != t.type:
                if t.type is None:
                    t.type = record[t.node]
                else:
                    raise LogicError(line, f"Type error for {t}")
        else:
            if t.type is None:
                residual.append(t)
            else:
                record[t.node] = t.type
    elif type(t) is Term and type(t.node) is tuple:
        for x in t.node:
            type_check(line, x, record, residual)
        if t.type is None:
            residual.append(t)

def is_connective(A, symbol):
    return type(A) is Term and type(A.node) is tuple and A.node[0] == symbol

def init_tables():
    global predicate_symbols, function_symbols
    predicate_symbols = {"element": 2, "eq": 2}
    function_symbols = {"comp": 1}

init_tables()

sym2 = {"->": "->", "=>": "->", "/\\": "&", "\\/": "|", "|-": "|-", "<=": "≤"}
sym3 = {"<->": "<->", "<=>": "<->", "_|_": "_|_"}
kw_tab = {"and": "&", "or": "|", "not": "~", "false": "_|_", "true": "#t",
    "box": "□", "dia": "◇", "forall": "#forall", "exists": "#exists",
    "in": "∈", "sub": "⊆", "cap": "∩", "cup": "∪", "Cap": "⋂", "Cup": "⋃",
    "times": "×"}

def scan(s):
    i = 0; n = len(s); a = []; line = 1
    while i < n:
        if s[i].isalpha():
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
        elif s[i] == '∅':
            a.append(("empty_set", line))
            i += 1
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

def infix_op(ident, ArgsType, ValueType):
    def cb(line, x, y):
        x = ensure_type(x, line, ArgsType)
        y = ensure_type(y, line, ArgsType)
        return Term((ident, x, y), ValueType)
    return cb

def infix_op_app(ident, ArgsType, ValueType):
    def cb(line, x, y):
        x = ensure_type(x, line, ArgsType)
        y = ensure_type(y, line, ArgsType)
        return Term(("app", Term(ident, Fn), x, y), ValueType)
    return cb

def prefix_op(ident, ArgType, ValueType):
    def cb(line, x):
        x = ensure_type(x, line, ArgType)
        return Term((ident, x), ValueType)
    return cb

def prefix_op_app(ident, ArgType, ValueType):
    def cb(line, x):
        x = ensure_type(x, line, ArgType)
        return Term(("app", Term(ident, Fn), x), ValueType)
    return cb

def prefix_seq(line, x):
    x = ensure_type(x, line, Prop)
    return Term(("seq", Term(("true",), Prop), x), Prop)

infix_table = {
    "*": (90, "left", infix_op_app("mul", Ind, Ind)),
    "×": (90, "left", infix_op_app("prod", Ind, Ind)),
    "∩": (90, "left", infix_op_app("intersection", Ind, Ind)),
    "\\":(90, "left", infix_op_app("diff", Ind, Ind)),
    "+": (80, "left", infix_op_app("add", Ind, Ind)),
    "∪": (80, "left", infix_op_app("union", Ind, Ind)),
    "<": (70, "left", infix_op_app("lt", Ind, Prop)),
    "≤": (70, "left", infix_op_app("le", Ind, Prop)),
    "⊆": (70, "left", infix_op_app("subset", Ind, Prop)),
    "∈": (70, "left", infix_op_app("element", Ind, Prop)),
    "=": (70, "left", infix_op_app("eq", Ind, Prop)),
    "∧": (50, "left", infix_op("conj", Prop, Prop)),
    "∨": (40, "left", infix_op("disj", Prop, Prop)),
    "→": (30, "right", infix_op("subj", Prop, Prop)),
    "↔": (20, "left", infix_op("bij", Prop, Prop)),
    "⊢": (10, "right", infix_op("seq", Prop, Prop))
}
def infix_synonyms(synonyms):
    for (key, value) in synonyms:
        infix_table[key] = infix_table[value]
infix_synonyms([
    ("&", "∧"), ("->", "→"), ("<->", "↔"),  ("|-", "⊢"), ("⋅", "*")])

prefix_table = {
    "⋂": (100, prefix_op_app("Intersection", Ind, Ind)),
    "⋃": (100, prefix_op_app("Union", Ind, Ind)),
    "~": ( 60, prefix_op("neg", Prop, Prop)),
    "¬": ( 60, prefix_op("neg", Prop, Prop)),
    "□": ( 60, prefix_op("nec", Prop, Prop)),
    "◇": ( 60, prefix_op("pos", Prop, Prop)),
    "⊢": ( 10, prefix_seq), "|-": (10, prefix_seq)
}

def is_identifier(t):
    return type(t) is str and t[0].isalpha()

def expect_token(a, i):
    if a[i][0] is None:
        raise SyntaxError(a[i][1], "unexpected end of input")
    else:
        return a[i]

def quantifier(a, i, op):
    token = a[i][0]
    if not is_identifier(token):
        raise SyntaxError(a[i][1], "expected a variable")
    var = Term(token, Ind); i += 1
    if a[i][0] != ":" and a[i][0] != ".":
        raise SyntaxError(a[i][1], "expected '.'")
    i += 1; line = a[i][1]
    i, x = formula(a, i)
    x = ensure_type(x, line, Prop)
    u = unique_variable(Ind)
    # todo
    #if occurs_as_fn(var.node, x):
    #    raise LogicError(line, "cannot quantify over a predicate/function")
    x = substitute_term(x, var, u)
    return i, Term((op, u.node, x), Prop)

def set_literal(a, i, x):
    x = Term(("app", Term("sg", Fn), ensure_type(x, a[i][1], Ind)), Ind)
    while a[i][0] == ",":
        i, y = formula(a, i + 1)
        y = Term(("app", Term("sg", Fn), ensure_type(y, a[i][1], Ind)), Ind)
        x = Term(("app", Term("union", Fn), x, y), Ind)
    if a[i][0] != "}":
        raise SyntaxError(a[i][1], "expected '}'")
    return i + 1, x

def comprehension(a, i, line):
    i, x = formula(a, i)
    if a[i][0] == "," or a[i][0] == "}":
        return set_literal(a, i, x)
    elif a[i][0] != "|":
        raise SyntaxError(a[i][1], "expected '|'")
    if not isinstance(x, Term) or not is_identifier(x.node):
        raise SyntaxError(line, "expected identifier after '{'")
    x.type = Ind
    line = a[i][1]
    i, A = formula(a, i + 1)
    A = ensure_type(A, line, Prop)
    if a[i][0] != "}":
        raise SyntaxError(a[i][1], "expected '}'")
    u = unique_variable(Ind)
    A = substitute_term(A, x, u)
    pred = Term(("lambda", u.node, A), (Ind, Prop))
    return i + 1, Term(("app", "comp", pred), Ind)

def nud(a, i):
    token, line = expect_token(a, i)
    if is_identifier(token):
        return i + 1, Term(token, None)
    elif token == "_|_" or token == "⊥":
        return i + 1, Term(("false",), Prop)
    elif token == "#t":
        return i + 1, Term(("true",), Prop)
    elif token == "(":
        i, x = formula(a, i + 1, 0)
        if a[i][0] == ",":
            i, y = formula(a, i + 1)
            x = infix_op_app("pair", Ind, Ind)(line, x, y)
        if expect_token(a, i)[0] != ")":
            raise SyntaxError(a[i][1], f"expected ')', but got '{a[i][0]}'")
        return i + 1, x
    elif token in prefix_table:
        bp, op = prefix_table[token]
        i, x = formula(a, i + 1, bp)
        return i, op(line, x)
    elif token == "#forall" or token == "∀":
        return quantifier(a, i + 1, "forall")
    elif token == "#exists" or token == "∃":
        return quantifier(a, i + 1, "exists")
    elif token == "{":
        return comprehension(a, i + 1, a[i][1])
    else:
        raise SyntaxError(line, f"unexpected symbol: '{token}'")

def application(a, i):
    line0 = a[i][1]
    i, x = nud(a, i)
    if is_identifier(a[i][0]) or a[i][0] == "(" or a[i][0] == "{":
        args = []
        while is_identifier(a[i][0]) or a[i][0] == "(" or a[i][0] == "{":
            line = a[i][1]
            i, y = nud(a, i)
            args.append(y)
        if not type(x) is Term or not type(x.node) is str:
            raise SyntaxError(line0, "predicate or function must be an identifier")
        x.type = Fn
        return i, Term(("app", x) + tuple(args), None)
    else:
        return i, x

def formula(a, i, rbp=0):
    i, x = application(a, i)
    while a[i][0] is not None and a[i][0] in infix_table:
        lbp, assoc, op = infix_table[a[i][0]]
        if rbp >= lbp: break
        next_rbp = lbp if assoc == "left" else lbp - 1
        i, y = formula(a, i + 1, next_rbp)
        x = op(a[i][1], x, y)
    return i, x

def formula_type_checked(a, i):
    line = a[i][1]
    i, x = formula(a, i)
    x = ensure_type(x, line, Prop)
    residual = []
    type_check(line, x, {}, residual)
    for t in residual:
        if t.type is None: t.type = Ind
    return i, x

def is_identifier(t):
    return type(t) is str and t[0].isalpha()

def rule_app(a, i):
    acc = []
    if not type(a[i][0]) is int and not is_identifier(a[i][0]):
        raise SyntaxError(a[i][1], "expected identifier or label")
    acc.append(a[i][0])
    i += 1
    while True:
        token = a[i][0]
        if type(token) is int or is_identifier(token):
            acc.append(token); i += 1
        elif a[i][0] == "." or a[i][0] == ",":
            return i, acc
        else:
            raise SyntaxError(a[i][1], "expected identifier or label")

def ref_context(a, i):
    acc = []
    if a[i][0] == "|-" or a[i][0] == "⊢":
        return i, acc
    while True:
        token = a[i][0]
        if type(token) is int or is_identifier(token):
            acc.append(token)
            i += 1
        if a[i][0] != ",": break
        i += 1
    return i, acc

def ref_sequent(a, i):
    i, ctx = ref_context(a, i)
    if a[i][0] == "|-" or a[i][0] == "⊢":
        i, x = formula_type_checked(a, i + 1)
        return i, ("ref_seq", ctx, x)
    else:
        raise SyntaxError(a[i][1], "expected context")

def parse_statement(i, a):
    label, line = a[i]; i += 1
    if a[i][0] != ".":
        raise SyntaxError(a[i][1], "expected '.'")
    if a[i+1][0] == "(":
        i, A = formula_type_checked(a, i + 1)
    else:
        i, A = ref_sequent(a, i + 1)
    if a[i][0] != ",":
        raise SyntaxError(a[i][1], "expected ','")
    i, rule = rule_app(a, i + 1)
    if a[i][0] == ",":
        i, hint = formula_type_checked(a, i + 1)
    else:
        hint = None
    if a[i][0] != ".":
        raise SyntaxError(a[i][1], "expected '.'")
    return i + 1, (line, label, A, rule, hint)

def parse(s):
    a = scan(s); i = 0; statements = []
    while a[i][0] != None:
        i, stmt = parse_statement(i, a)
        statements.append(stmt)
    return statements

def scheme(A):
    if type(A) is Term:
        if type(A.node) is str:
            if (A.node[0] != '$' and A.node != "nf" and
            not A.node in predicate_symbols and
            not A.node in function_symbols):
                return Term("?" + A.node, A.type)
            else:
                return A
        else:
            return Term((A.node[0],) + tuple(scheme(B) for B in A.node[1:]), A.type)
    else:
        return A

def subst_rec(A, subst):
    if is_scheme_var(A):
        if A.node in subst:
            return subst[A.node]
        else:
            return A
    elif type(A) is Term and type(A.node) is tuple:
        return Term((A.node[0],) + tuple(subst_rec(X, subst) for X in A.node[1:]), A.type)
    else:
        return A

def conj_list(A, subst):
    if is_connective(A, "true"):
        return []
    elif is_connective(A, "conj"):
        return conj_list(A.node[1], subst) + conj_list(A.node[2], subst)
    elif not subst is None:
        return conj_list(subst_rec(A, subst), None)
    else:
        return [A]

def set_in(A, b):
    return any(term_eq(A, B) for B in b)

def subset(a, b):
    return all(set_in(A, b) for A in a)

def set_eq(a, b):
    return subset(a, b) and subset(b, a)

def unify_seq(A, pattern, subst):
    result = unify(A.node[2], pattern.node[2], subst)
    if result: return result
    L = conj_list(pattern.node[1], subst)
    return None if set_eq(conj_list(A.node[1], None), L) else UErr(A, pattern)

class Substitution:
    def __init__(self, A, args):
        self.A = A; self.args = args
    def __call__(self, argv):
        return substitute_term(self.A, self.args, argv)
    def __repr__(self):
        return f"argv ↦ {self.A}[argv/{self.args}]"

def unify_args(A, pattern, subst):
    subst_copy = subst.copy()
    for i in range(1, len(A.node)):
        result = unify(A.node[i], pattern.node[i], subst)
        if result:
            if is_connective(pattern, "seq"):
                # todo: subst auf subst_copy setzen, sonst fürs
                # Debugging unsichtbar.
                return unify_seq(A, pattern, subst_copy)
            return result
    return None

def unify_pred(A, pattern, subst):
    if is_connective(A, "app") and A.type == pattern.type and len(A.node) == len(pattern.node):
        result = unify_args(A, pattern, subst)
    else:
        result = UErr(A, pattern)
    if result is None or not is_scheme_var(pattern.node[1]):
        return result
    P = pattern.node[1]; args = list(pattern.node[2:])
    if P.node in subst:
        P = subst[P.node]
        if not callable(P): return UErr(A, pattern)
        B = P(args)
        return unify(A, B, subst)
    else:
        for i in range(len(args)):
            if args[i].node in subst: args[i] = subst[args[i].node]
        subst[P.node] = Substitution(A, args)
        return None

def is_scheme_var(A):
    return type(A) is Term and type(A.node) is str and A.node[0] == '?'

class UErr:
    def __init__(self, A, pattern):
        self.A = A; self.pattern = pattern

def unify(A, pattern, subst):
    if type(pattern) is Term:
        if is_scheme_var(pattern):
            if pattern.node in subst:
                B = subst[pattern.node]
                return unify(A, B, subst)
            else:
                if pattern.type != A.type:
                    return UErr(A, pattern)
                subst[pattern.node] = A
                return None
        elif type(pattern.node) is str:
            return None if term_eq(A, pattern) else UErr(A, pattern)
        elif type(pattern.node) is tuple:
            if is_connective(pattern, "app"):
                return unify_pred(A, pattern, subst)
            if A.type != pattern.type: return UErr(A, pattern)
            if not type(A.node) is tuple: return UErr(A, pattern)
            if len(A.node) != len(pattern.node): return UErr(A, pattern)
            if A.node[0] != pattern.node[0]: return UErr(A, pattern)
            if A.node[0] in ("forall", "exists", "lambda"):
                u = unique_variable(Ind)
                A = substitute_term(A.node[2], Term(A.node[1], Ind), u)
                B = substitute_term(pattern.node[2], Term(pattern.node[1], Ind), u)
                return unify(A, B, subst)
            return unify_args(A, pattern, subst)
        else:
            raise ValueError("unreachable")
    elif type(pattern) is str:
        return None if A == pattern else UErr(A, pattern)
    else:
        return UErr(A, pattern)

def side_condition(C, conds, subst):
    if is_connective(C, "subj") and is_connective(C.node[1], "app") and C.node[1].node[1].node == "nf":
        x, A = C.node[1].node[2:]
        conds.append((x, A))
        return side_condition(C.node[2], conds, subst)
    return C

def free_in(x, A, subst):
    if type(A) is Term:
        if type(A.node) is str and A.node[0] != "$":
            if A.node in subst:
                if not term_eq(A, subst[A.node]):
                    return free_in(x, subst[A.node], subst)
            if A.type != Prop:
                return term_eq(x, A)
            return False
        elif type(A.node) is tuple:
            start = 2 if A.node[0] == "app" else 1
            for B in A.node[start:]:
                if free_in(x, B, subst): return True
            return False
        elif type(A.node) is str and A.node[0] == "$":
            return False
        else:
            raise ValueError("unreachable")
    elif type(A) is str and A[0] == "$":
        return False
    else:
        raise ValueError("unreachable")

def unification_hint(line, hint, subst):
    if is_connective(hint, "bij"):
        lhs = hint.node[1]; rhs = hint.node[2]
        if is_connective(lhs, "app"):
            P = lhs.node[1]; args = list(lhs.node[2:])
            subst["?" + P.node] = Substitution(rhs, args)
            return None
    raise LogicError(line, f"invalid unification hint: {hint}")

def is_parameter(x):
    return type(x) is Term and type(x.node) is str and not x.node[0] in "?$"

def is_quantifier_rule(C):
    if is_connective(C, "subj") and is_connective(C.node[2], "seq"):
        A = C.node[2].node[2]
        return is_connective(A, "forall") or is_connective(A, "exists")
    return False

def conclusion(line, B, C, subst, args):
    result = unify(B, C, subst)
    if result:
        # dev.uerr_info(B, C, result, subst)
        raise LogicError(line,
            f"unification failed for {args[0]}, in conclusion")

def modus_ponens(line, book, B, args, hint):
    assert len(args) >= 1
    C = lookup(book, args[0], line)
    C = scheme(C)
    subst = {}
    conds = []
    C = side_condition(C, conds, subst)
    reverse = False
    if not hint is None:
        unification_hint(line, hint, subst)
    if is_quantifier_rule(C):
        conclusion(line, B, C.node[2], subst, args)
        reverse = True
    for i in range(1, len(args)):
        A = lookup(book, args[i], line)
        if not is_connective(C, "subj"):
            raise LogicError(line, "expected a rule/subjunction")
        result = unify(A, C.node[1], subst)
        if result:
            # dev.uerr_info(A, C.node[1], result, subst)
            raise LogicError(line,
                f"unification failed for {args[0]}, argument {i}")
        C = C.node[2]
    if not reverse:
        conclusion(line, B, C, subst, args)
    for (x, A) in conds:
        if x.node in subst:
            x = subst[x.node]
        if not is_parameter(x) or free_in(x, A, subst):
            raise LogicError(line, f"in {args[0]}: {x} occurs free in {A}")

def expect_len(line, args, n, rule_name):
    s = "" if n == 1 else "s"
    raise LogicError(line,
        f"rule {rule_name} expects {n} argument{s}, but got {len(args)}")

def definition(line, book, S, args):
    if len(args) != 0: expect_len(line, args, 0, "def")
    if not is_connective(S.node[1], "true"):
        raise LogicError(line, "definition expects empty context")
    C = S.node[2]
    if is_connective(C, "bij"):
        A = C.node[1]; B = C.node[2]
        if not isinstance(A.node, tuple) or A.node[0] != "app":
            raise LogicError(line, "malformed definition")
        if A.node[1].node in predicate_symbols:
            raise LogicError(line, "already defined")
        predicate_symbols[A.node[1].node] = len(A.node) - 2
    elif is_connective(C, "app") and C.node[1].node == "eq":
        A = C.node[2]; B = C.node[3]
        if isinstance(A.node, str):
            if A.node in function_symbols:
                raise LogicError(line, "already defined")
            function_symbols[A.node] = 0
        else:
            if not isinstance(A.node, tuple) or A.node[0] != "app":
                raise LogicError(line, "malformed definition")
            if A.node[1].node in function_symbols:
                raise LogicError(line, "already defined")
            function_symbols[A.node[1].node] = len(A.node) - 2
    else:
        raise LogicError(line, "malformed definition")

def lookup(book, key, line):
    if not key in book:
        raise LogicError(line, f"label '{key}' not found")
    else:
        return book[key]

def verify_plain(book, s):
    statements = parse(s)
    for (line, label, B, rule, hint) in statements:
        if type(B) is tuple and B[0] == "ref_seq":
            Gamma = B[1]; A = B[2]
            book[label] = Term(("seq", None, A), Prop)
            H = Term(("true",), Prop)
            for k in Gamma:
                H = Term(("conj", H, book[k].node[2]), Prop) # todo
            B = Term(("seq", H, A), Prop)
            book[label] = B
        else:
            book[label] = B
        if label in rule:
            raise LogicError(line, "cyclic deduction")
        if rule[0] == "def":
            definition(line, book, B, rule[1:])
        elif rule[0] != "axiom":
            modus_ponens(line, book, B, rule, hint)

def verify(book, s):
    try:
        verify_plain(book, s)
    except SyntaxError as e:
        print("Syntax error in line {}:\n{}".format(e.line, e.text))
    except LogicError as e:
        print("Logic error in line {}:\n{}".format(e.line, e.text))

fmt_tab = {
    "&": "∧", "~": "¬", "->": "→", "=>": "→", "/\\": "∧", "\\/": "∨",
    "|-": "⊢", "<->": "↔", "<=>": "↔", "_|_": "⊥", "*": "⋅", "<=": "≤"
}
fmt_kw_tab = {
    "and": "∧", "or": "∨", "not": "¬", "box": "□", "dia": "◇",
    "forall": "∀", "exists": "∃", "in": "∈", "sub": "⊆",
    "cup": "∪", "cap": "∩", "Cap": "⋂", "Cup": "⋃", "times": "×",
    "empty_set": "∅"
}
unspace_set = {"not", "box", "dia", "forall", "exists", "Cap", "Cup"}

def format_source_code(s):
    acc = []; i = 0; n = len(s)
    while i < n:
        fmt = False
        for k in range(3, 0, -1):
            if i + k - 1 < n and s[i:i+k] in fmt_tab:
                acc.append(fmt_tab[s[i:i+k]])
                i += k; fmt = True; break
        if not fmt:
            if s[i].isalpha():
                j = i
                while i < n and (s[i].isalpha() or s[i].isdigit() or s[i] in "_'"):
                    i += 1
                sji = s[j:i]; sf = fmt_kw_tab.get(sji)
                acc.append(sji if sf is None else sf)
                if sji in unspace_set and i < n and s[i] == ' ':
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
        return f.read()

rules = """
basic. (true ∧ H ⊢ H), axiom.
conj_intro. (H1 ⊢ A) → (H2 ⊢ B) → (H1 ∧ H2 ⊢ A ∧ B), axiom.
conj_eliml. (H ⊢ A ∧ B) → (H ⊢ A), axiom.
conj_elimr. (H ⊢ A ∧ B) → (H ⊢ B), axiom.
disj_introl. (H ⊢ A) → (H ⊢ A ∨ B), axiom.
disj_intror. (H ⊢ B) → (H ⊢ A ∨ B), axiom.
disj_elim. (H1 ⊢ A ∨ B) → (H2 ∧ A ⊢ C) → (H3 ∧ B ⊢ C) →
  (H1 ∧ H2 ∧ H3 ⊢ C), axiom.
subj_intro. (H ∧ A ⊢ B) → (H ⊢ A → B), axiom.
subj_elim. (H1 ⊢ A → B) → (H2 ⊢ A) → (H1 ∧ H2 ⊢ B), axiom.
neg_intro. (H ∧ A ⊢ ⊥) → (H ⊢ ¬A), axiom.
neg_elim. (H1 ⊢ ¬A) → (H2 ⊢ A) → (H1 ∧ H2 ⊢ ⊥), axiom.
bij_intro. (H1 ⊢ A → B) → (H2 ⊢ B → A) → (H1 ∧ H2 ⊢ A ↔ B), axiom.
bij_eliml. (H ⊢ A ↔ B) → (H ⊢ A → B), axiom.
bij_elimr. (H ⊢ A ↔ B) → (H ⊢ B → A), axiom.
wk. (H ⊢ B) → (H ∧ A ⊢ B), axiom.
exch. (H ⊢ A) → (H ⊢ A), axiom.
uq_intro. (nf u (H ∧ ∀x. A x)) → (H ⊢ A u) → (H ⊢ ∀x. A x), axiom.
uq_elim. (H ⊢ ∀x. A x) → (H ⊢ A t), axiom.
ex_intro. (H ⊢ A t) → (H ⊢ ∃x. A x), axiom.
ex_elim. (nf u (H1 ∧ H2 ∧ B ∧ ∃x. A x)) →
  (H1 ⊢ ∃x. A x) → (H2 ∧ A u ⊢ B) → (H1 ∧ H2 ⊢ B), axiom.
lift_impl. (⊢ A → B) → (H ⊢ A) → (H ⊢ B), axiom.
lift_impl_ii. (⊢ A → B → C) → (H1 ⊢ A) → (H2 ⊢ B) → (H1 ∧ H2 ⊢ C), axiom.
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

if __name__ == "__main__":
    main()
