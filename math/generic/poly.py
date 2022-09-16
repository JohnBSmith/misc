
class Polynomial:
    def __init__(self, a):
        self.coeff = a
    def __str__(self):
        return "Polynomial({})".format(self.coeff)
    def __repr__(self):
        return "Polynomial({})".format(self.coeff)
    def __neg__(self):
        return Polynomial([-a for a in self.coeff])
    def __add__(self, rhs):
        na = len(self.coeff); nb = len(rhs.coeff)
        n = max(na, nb)
        acc = []
        for k in range(n):
            a = self.coeff[k] if k < na else 0
            b = rhs .coeff[k] if k < nb else 0
            acc.append(a + b)
        return Polynomial(acc)
    def __sub__(self, rhs):
        na = len(self.coeff); nb = len(rhs.coeff)
        n = max(na, nb)
        acc = []
        for k in range(n):
            a = self.coeff[k] if k < na else 0
            b = rhs .coeff[k] if k < nb else 0
            acc.append(a - b)
        return Polynomial(acc)
    def __mul__(self, rhs):
        if isinstance(rhs, Polynomial):
            na = len(self.coeff); nb = len(rhs.coeff)
            acc = []
            for k in range(na + nb - 1):
                s = 0
                for i in range(k + 1):
                    a = self.coeff[i] if i < na else 0
                    b = rhs .coeff[k - i] if k - i < nb else 0
                    s += a*b
                acc.append(s)
            return Polynomial(acc)
        else:
            return Polynomial([a*rhs for a in self.coeff])
    def __rmul__(self, lhs):
        return Polynomial([lhs*a for a in self.coeff])
    def __pow__(self, n):
        assert isinstance(n, int) and n >= 0
        a = self; acc = Polynomial([1])
        while True:
            if n%2 != 0: acc *= a
            if n == 0: return acc
            a *= a; n //= 2
    def __call__(self, x):
        acc = 0; p = 1
        for a in self.coeff:
            acc += a*p; p *= x
        return acc
