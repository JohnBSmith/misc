
class SyntaxError(Exception):
    pass

def scan(s):
    a = []; i = 0; n = len(s)
    while i < n:
        if s[i] in "+-*/^()":
            a.append(s[i])
            i += 1
        elif s[i].isdigit():
            j = i
            while i < n and s[i].isdigit(): i += 1
            a.append(int(s[j:i]))
        elif s[i].isspace():
            i += 1
        else:
            raise SyntaxError(f"unexpected character: '{s[i]}'")
    a.append(None)
    return a

infix_table = {
    "+": ("+", 10, "left"),
    "-": ("-", 10, "left"),
    "*": ("*", 20, "left"),
    "/": ("/", 20, "left"),
    "^": ("^", 40, "right")
}

prefix_table = {
    "-": ("~", 30)
}

def expect_token(a, i):
    if a[i] is None:
        raise SyntaxError("unexpected end of input")
    else:
        return a[i]

def nud(a, i):
    token = expect_token(a, i)
    if type(token) is int:
        return i + 1, token
    elif token == "(":
        i, x = parse(a, i + 1, 0)
        if expect_token(a, i) != ")":
            raise SyntaxError(f"')' was expected, but got '{a[i]}'")
        return i + 1, x
    elif token in prefix_table:
        op, bp = prefix_table[token]
        i, x = parse(a, i + 1, bp)
        return i, (op, x)
    else:
        raise SyntaxError(f"unexpected symbol: '{t}'")

def parse(a, i, rbp):
    i, x = nud(a, i)
    while a[i] is not None and a[i] in infix_table:
        op, lbp, assoc = infix_table[a[i]]
        if rbp >= lbp: break
        next_rbp = lbp if assoc == "left" else lbp - 1
        i, y = parse(a, i + 1, next_rbp)
        x = (op, x, y)
    return i, x

def ast(s):
    a = scan(s)
    i, t = parse(a, 0, 0)
    if not a[i] is None:
        raise SyntaxError(
            f"end of input was expected, but got: '{a[i]}'")
    return t

dispatch = {
    "+": lambda x, y: x + y,
    "-": lambda x, y: x - y,
    "*": lambda x, y: x * y,
    "/": lambda x, y: x / y,
    "^": lambda x, y: x ** y,
    "~": lambda x: -x
}

def evaluate(t):
    if type(t) is int:
        return t
    else:
        return dispatch[t[0]](*map(evaluate, t[1:]))

if __name__ == "__main__":
    while True:
        try:
            s = input("> ")
            if s == "":
                continue
            t = ast(s)
            print(f"Abstract syntax tree:\n  {t}\n")
            print(f"Result:\n  {evaluate(t)}")
        except SyntaxError as e:
            print(f"Syntax error: {e}")
        except (KeyboardInterrupt, EOFError):
            print()
            break
