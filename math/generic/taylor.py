
from math import factorial

class TruncatedPolynomial:
    def __init__(self, a):
        self.coeff = a
    def __str__(self):
        return "TruncatedPolynomial([{}])".format(
            ", ".join(str(x) for x in self.coeff))
    def __repr__(self):
        return "TruncatedPolynomial({})".format(self.coeff)
    def __neg__(self):
        return TruncatedPolynomial([-a for a in self.coeff])
    def __add__(self, rhs):
        if isinstance(rhs, TruncatedPolynomial):
            n = len(self.coeff)
            acc = []
            for k in range(n):
                a = self.coeff[k] if k < n else 0
                b = rhs .coeff[k] if k < n else 0
                acc.append(a + b)
            return TruncatedPolynomial(acc)
        else:
            c = self.coeff
            return TruncatedPolynomial([c[k] + rhs if k == 0 else c[k]
                for k in range(len(c))])
    def __sub__(self, rhs):
        if isinstance(rhs, TruncatedPolynomial):
            n = len(self.coeff)
            acc = []
            for k in range(n):
                a = self.coeff[k] if k < n else 0
                b = rhs .coeff[k] if k < n else 0
                acc.append(a - b)
            return TruncatedPolynomial(acc)
        else:
            c = self.coeff
            return TruncatedPolynomial([c[k] - rhs if k == 0 else c[k]
                for k in range(len(c))])
    def __radd__(self, lhs):
        c = self.coeff
        return TruncatedPolynomial([lhs + c[k] if k == 0 else c[k]
            for k in range(len(c))])
    def __rsub__(self, lhs):
        c = self.coeff
        return TruncatedPolynomial([lhs - c[k] if k == 0 else -c[k]
            for k in range(len(c))])
    def __mul__(self, rhs):
        if isinstance(rhs, TruncatedPolynomial):
            n = len(self.coeff)
            acc = []
            for k in range(n):
                s = 0
                for i in range(k + 1):
                    a = self.coeff[i] if i < n else 0
                    b = rhs .coeff[k - i] if k - i < n else 0
                    s += a*b
                acc.append(s)
            return TruncatedPolynomial(acc)
        else:
            return TruncatedPolynomial([a*rhs for a in self.coeff])
    def __rmul__(self, lhs):
        return TruncatedPolynomial([lhs*a for a in self.coeff])
    def __truediv__(self, rhs):
        return self*reciprocal(rhs)
    def __rtruediv__(self, lhs):
        a = self.coeff
        b = [lhs/a[0]]
        for n in range(1, len(a)):
             b.append(-lhs*sum(a[i]*b[n - i] for i in range(1, n + 1))/a[0])
        return TruncatedPolynomial(b)
    def __pow__(self, n):
        assert isinstance(n, int) and n >= 0
        a = self; acc = TruncatedPolynomial([1] + (len(a.coeff) - 1)*[0])
        while True:
            if n%2 != 0: acc *= a
            if n == 0: return acc
            a *= a; n //= 2
    def __call__(self, x):
        acc = 0; p = 1
        for a in self.coeff:
            acc += a*p; p *= x
        return acc

def reciprocal(a):
    a = a.coeff
    b = [1/a[0]]
    for n in range(1, len(a)):
         b.append(-sum(a[i]*b[n - i] for i in range(1, n + 1))/a[0])
    return TruncatedPolynomial(b)

def taylor(f, x, n):
    return f(TruncatedPolynomial([x, 1] + (n - 1)*[0])).coeff

def diff_list(f, x, n):
    a = f(TruncatedPolynomial([x, 1] + (n - 1)*[0])).coeff
    return [a[k]*factorial(k) for k in range(len(a))]

