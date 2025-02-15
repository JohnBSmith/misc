
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

op_table = {
    "+": ("+", 10, "left"),
    "-": ("-", 10, "left"),
    "*": ("*", 20, "left"),
    "/": ("/", 20, "left"),
    "~": ("~", 30, None),
    "^": ("^", 40, "right")
}

def operate(op, buf):
    try:
        if op == "~":
            x = buf.pop()
            buf.append((op, x))
        else:
            y = buf.pop()
            x = buf.pop()
            buf.append((op, x, y))
    except IndexError:
        raise SyntaxError("too many operators")

def parse(a):
    buf = []; stack = []
    prefix = True
    for token in a:
        if prefix and token == "-":
            token = "~"
        if type(token) is int:
            buf.append(token)
            prefix = False
        elif token in op_table:
            op, prec, assoc = op_table[token]
            while len(stack) != 0:
                top = stack[-1]
                if not top in op_table:
                    break
                top_op, top_prec, top_assoc = op_table[top]
                if assoc == "left":
                    if prec > top_prec: break
                elif assoc == "right":
                    if top_assoc == "right":
                        if prec <= top_prec: break
                    else:
                        if prec > top_prec: break
                elif assoc is None:
                    if top_assoc == "right":
                        if prec < top_prec: break
                    else:
                        if prec >= top_prec: break
                operate(top_op, buf)
                stack.pop()
            stack.append(token)
            prefix = True
        elif token == "(":
            stack.append(token)
            prefix = True
        elif token == ")":
            found = False
            while len(stack) != 0:
                top = stack.pop()
                if top == "(":
                    found = True
                    break
                operate(op_table[top][0], buf)
            if not found:
                raise SyntaxError("bracket mismatch")
        elif token is None:
            break
        else:
            return SyntaxError(f"unknown symbol: {token}")
    while len(stack) != 0:
        top = stack.pop()
        if top == "(":
            raise SyntaxError("bracket mismatch")
        operate(op_table[top][0], buf)
    if len(buf) == 1:
        return buf[0]
    else:
        raise SyntaxError("too few operators")

def ast(s):
    return parse(scan(s))

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
            if s == "": continue
            t = ast(s)
            print(f"Abstract syntax tree:\n  {t}\n")
            print(f"Result:\n  {evaluate(t)}")
        except SyntaxError as e:
            print(f"Syntax error: {e}")
        except (KeyboardInterrupt, EOFError):
            print()
            break
