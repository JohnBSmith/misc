
class Complex:
    def __init__(self, x, y):
        self.re = x
        self.im = y
    def __str__(self):
        return "Complex({}, {})".format(self.re, self.im)
    def __repr__(self):
        return "Complex({}, {})".format(self.re, self.im)
    def __eq__(self, rhs):
        if isinstance(rhs, Complex):
            return self.re == rhs.re and self.im == rhs.im
        else:
            return self.re == rhs and self.im == 0
    def __req__(self, lhs):
        return lhs == self.re and self.im == 0
    def __neg__(self):
        return Complex(-self.re, -self.im)
    def __add__(self, rhs):
        if isinstance(rhs, Complex):
            return Complex(self.re + rhs.re, self.im + rhs.im)
        else:
            return Complex(self.re + rhs, self.im)
    def __radd__(self, lhs):
        return Complex(lhs + self.re, self.im)
    def __sub__(self, rhs):
        if isinstance(rhs, Complex):
            return Complex(self.re - rhs.re, self.im - rhs.im)
        else:
            return Complex(self.re - rhs, self.im)
    def __rsub__(self, lhs):
        return Complex(lhs - self.re, -self.im)
    def __mul__(self, rhs):
        if isinstance(rhs, Complex):
            return Complex(
                self.re*rhs.re - self.im*rhs.im,
                self.re*rhs.im + self.im*rhs.re)
        else:
            return Complex(self.re*rhs, self.im*rhs)
    def __rmul__(self, lhs):
        return Complex(lhs*self.re, lhs*self.im)
    def __truediv__(self, rhs):
        if isinstance(rhs, Complex):
            r_sq = rhs.re*rhs.re + rhs.im*rhs.im
            return Complex(
                (self.re*rhs.re + self.im*rhs.im)/r_sq,
                (self.im*rhs.re - self.re*rhs.im)/r_sq)
        else:
            return Complex(self.re/rhs, self.im/rhs)
    def __rtruediv__(self, lhs):
        r_sq = self.re*self.re + self.im*self.im
        return Complex(lhs*self.re/r_sq, -lhs*self.im/r_sq)
    def __pow__(self, n):
        assert isinstance(n, int) and n >= 0
        a = self; acc = Complex(1, 0)
        while True:
            if n%2 != 0: acc *= a
            if n == 0: return acc
            a *= a; n //= 2
    def conj(self):
        return Complex(self.re, -self.im)
    def abs_sq(self):
        return self.re*self.re + self.im*self.im
