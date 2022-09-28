
class Dual:
    def __init__(self, x, y):
        self.re = x
        self.im = y
    def __str__(self):
        return "Dual({}, {})".format(self.re, self.im)
    def __repr__(self):
        return "Dual({}, {})".format(self.re, self.im)
    def __eq__(self, rhs):
        if isinstance(rhs, Dual):
            return self.re == rhs.re and self.im == rhs.im
        else:
            return self.re == rhs and self.im == 0
    def __req__(self, lhs):
        return lhs == self.re and self.im == 0
    def __neg__(self):
        return Dual(-self.re, -self.im)
    def __add__(self, rhs):
        if isinstance(rhs, Dual):
            return Dual(self.re + rhs.re, self.im + rhs.im)
        else:
            return Dual(self.re + rhs, self.im)
    def __radd__(self, lhs):
        return Dual(lhs + self.re, self.im)
    def __sub__(self, rhs):
        if isinstance(rhs, Dual):
            return Dual(self.re - rhs.re, self.im - rhs.im)
        else:
            return Dual(self.re - rhs, self.im)
    def __rsub__(self, lhs):
        return Dual(lhs - self.re, -self.im)
    def __mul__(self, rhs):
        if isinstance(rhs, Dual):
            return Dual(self.re*rhs.re, self.im*rhs.re + self.re*rhs.im)
        else:
            return Dual(self.re*rhs, self.im*rhs)
    def __rmul__(self, lhs):
        return Dual(lhs*self.re, lhs*self.im)
    def __truediv__(self, rhs):
        if isinstance(rhs, Dual):
            return Dual(self.re/rhs.re,
                (self.im*rhs.re - self.re*rhs.im)/(rhs.re*rhs.re))
        else:
            return Dual(self.re/rhs, self.im/rhs)
    def __rtruediv__(self, lhs):
        return Dual(lhs/self.re, -lhs*self.im/(self.re*self.re))
    def __pow__(self, n):
        assert isinstance(n, int) and n >= 0
        a = self; acc = Dual(1, 0)
        while True:
            if n%2 != 0: acc *= a
            if n == 0: return acc
            a *= a; n //= 2
    def conj(self):
        return Dual(self.re, -self.im)

def imag(x):
    return x.im if isinstance(x, Dual) else x

def diff(f, x, n = 1):
    if n == 1:
        return imag(f(Dual(x, 1)))
    elif n == 0:
        return f(x)
    else:
        return imag(diff(f, Dual(x, 1), n - 1))

