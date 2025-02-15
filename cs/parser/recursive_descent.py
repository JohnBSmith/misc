
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

def expect_token(a, i):
    if a[i] is None:
        raise SyntaxError("unexpected end of input")
    else:
        return a[i]

def atom(a, i):
    token = expect_token(a, i)
    if type(token) is int:
        return i + 1, a[i]
    elif token == "(":
        i, x = expression(a, i + 1)
        if expect_token(a, i) != ")":
            raise SyntaxError(
                f"')' was expected, but got '{a[i]}'")
        return i + 1, x
    else:
        raise SyntaxError(f"unexpected symbol: '{token}'")

def power(a, i):
    i, x = atom(a, i)
    if a[i] == "^":
        i, y = negation(a, i + 1)
        return i, ("^", x, y)
    else:
      return i, x

def negation(a, i):
    if a[i] == "-":
        i, x = negation(a, i + 1)
        return i, ("~", x)
    else:
        return power(a, i)

def multiplication(a, i):
    i, x = negation(a, i)
    op = a[i]
    while op == "*" or op == "/":
        i, y = negation(a, i + 1)
        x = (op, x, y)
        op = a[i]
    return i, x

def addition(a, i):
    i, x = multiplication(a, i)
    op = a[i]
    while op == "+" or op == "-":
        i, y = multiplication(a, i + 1)
        x = (op, x, y)
        op = a[i]
    return i, x

def expression(a, i):
    return addition(a, i)

def ast(s):
    a = scan(s)
    i, t = expression(a, 0)
    if a[i] is None:
        return t
    else:
        raise SyntaxError(
            f"end of input was expected, but got: '{a[i]}'")

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
