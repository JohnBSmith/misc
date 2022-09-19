
class Matrix:
    def __init__(self, a, dim = None):
        if dim != None:
            self.dim = dim
            self.a = a
        else:
            self.dim = (len(a), len(a[0]))
            self.a = [x for v in a for x in v]
    def __repr__(self):
        n = self.dim[1]
        return "matrix({})".format(", ".join(str(self.a[k:k+n])
            for k in range(0, len(self.a), n)))
    def __str__(self):
        n = self.dim[1]
        l = ["[{}]".format(", ".join(str(x) for x in self.a[k:k+n]))
            for k in range(0, len(self.a), n)]
        return "matrix(\n{}\n)".format(",\n".join(l))
    def __neg__(self):
        return Matrix([-x for x in self.a], self.dim)
    def __add__(self, rhs):
        if isinstance(rhs, Matrix):
            assert self.dim == rhs.dim
            a = [x + y for (x, y) in zip(self.a, rhs.a)]
            return Matrix(a, self.dim)
        else:
            (m, n) = self.dim; a = self.a
            return Matrix([a[i*n + j] + rhs if i == j else a[i*n + j]
                for i in range(m) for j in range(n)], self.dim)
    def __radd__(self, lhs):
        return self + lhs
    def __sub__(self, rhs):
        if isinstance(rhs, Matrix):
            assert self.dim == rhs.dim
            a = [x - y for (x, y) in zip(self.a, rhs.a)]
            return Matrix(a, self.dim)
        else:
            (m, n) = self.dim; a = self.a
            return Matrix([a[i*n + j] - rhs if i == j else a[i*n + j]
                for i in range(m) for j in range(n)], self.dim)
    def __rsub__(self, lhs):
        (m, n) = self.dim; a = self.a
        return Matrix([lhs - a[i*n + j] if i == j else -a[i*n + j]
            for i in range(m) for j in range(n)], self.dim)
    def __mul__(self, rhs):
        if isinstance(rhs, Matrix):
            assert self.dim[1] == rhs.dim[0]
            (m, p) = self.dim; n = rhs.dim[1]
            a = [sum(self.a[i*p + k]*rhs.a[k*n + j] for k in range(p))
                for i in range(m) for j in range(n)]
            return Matrix(a, (m, n))
        elif isinstance(rhs, Vector):
            (m, n) = self.dim
            assert n == len(rhs.a)
            a = self.a; b = rhs.a
            return Vector([sum(a[i*n + k]*b[k] for k in range(n))
                for i in range(m)])
        else:
            return Matrix([x*rhs for x in self.a], self.dim)
    def __rmul__(self, r):
        return Matrix([r*x for x in self.a], self.dim)
    def __truediv__(self, rhs):
        if isinstance(rhs, Matrix):
            return self*invert(rhs)
        else:
            return Matrix([x/rhs for x in self.a], self.dim)
    def __rtruediv__(self, lhs):
        return lhs*invert(self)
    def __pow__(self, n):
        assert isinstance(n, int)
        if n < 0: return invert(self)**(-n)
        a = self; acc = identity(self.dim[0])
        while True:
            if n%2 != 0: acc *= a
            if n == 0: return acc
            a *= a; n //= 2
    def __getitem__(self, i):
        if isinstance(i, tuple):
            return self.a[self.dim[1]*i[0] + i[1]]
        else:
            n = self.dim[1]; offset = n*i
            return self.a[offset:offset+n]
    def __setitem__(self, i, x):
        if isinstance(i, tuple):
            self.a[self.dim[1]*i[0] + i[1]] = x
        else:
            n = self.dim[1]; offset = n*i
            self.a[offset:offset+n] = x
    def __eq__(self, rhs):
        return self.dim == rhs.dim and self.a == rhs.a
    def map(self, f):
        return Matrix([f(x) for x in self.a], self.dim)

class Vector:
    def __init__(self, a):
        self.a = a
    def __repr__(self):
        return "vector({})".format(", ".join(repr(x) for x in self.a))
    def __str__(self):
        return "vector({})".format(", ".join(str(x) for x in self.a))
    def __neg__(self):
        return Vector(-x for x in self.a)
    def __add__(self, rhs):
        return Vector(x + y for (x, y) in zip(self.a, rhs.a))
    def __sub__(self, lhs):
        return Vector(x - y for (x, y) in zip(self.a, rhs.a))
    def __mul__(self, rhs):
        if isinstance(rhs, Vector):
            return sum(x*y for (x, y) in zip(self.a, rhs.a))
        else:
            return Vector(x*rhs for x in self.a)
    def __rmul__(self, r):
        return Vector(r*x for x in self.a)
    def __getitem__(self, i):
        return self.a[i]
    def map(self, f):
        return Vector(f(x) for x in self.a)

def matrix(*a):
    return Matrix(a)

def vector(*a):
    return Vector(a)

def row_vector(a):
    return Matrix(a, (len(a), 1))

def col_vector(a):
    return Matrix(a, (1, len(a)))

def identity(n):
    a = [1 if i == j else 0 for i in range(n) for j in range(n)]
    return Matrix(a, (n, n))

def transpose(A):
    (m, n) = A.dim
    a = [A.a[j*n + i] for i in range(n) for j in range(m)]
    return Matrix(a, (n, m))

def invert(A):
    n = A.dim[1]
    assert A.dim[0] == n
    A = Matrix(A.a.copy(), A.dim)
    X = identity(n)
    gauss_jordan(A, X, n)
    return X

def proj(v, w):
    return ((v*w)/(v*v))*v

def cols(A):
    (m, n) = A.dim
    return [Vector([A.a[j*n + i] for i in range(n)]) for j in range(m)]

def mul_scalar_vec(r, v):
    if isinstance(v, list):
        return [r*v[i] for i in range(0, len(v))]
    else:
        return r*v

def add_vec(r, v, s, w):
    if isinstance(v, list):
        return [r*v[i] + s*w[i] for i in range(0, len(v))]
    else:
        return r*v + s*w

def pivoting(A, B, n, j):
    m = abs(A[j][j])
    k = j
    for i in range(j + 1, n):
        if m < abs(A[i][j]):
            m = abs(A[i][j])
            k = i
    A[j], A[k] = A[k], A[j]
    B[j], B[k] = B[k], B[j]
    return m

def gauss_jordan(A, B, n):
    zero_pivot = False
    for j in range(0, n):
        pivot = pivoting(A, B, n, j)
        if pivot == 0:
            zero_pivot = True
            break
        B[j] = mul_scalar_vec(1/A[j][j], B[j])
        A[j] = mul_scalar_vec(1/A[j][j], A[j])
        for i in range(j + 1, n):
            if A[i][j] != 0:
                B[i] = add_vec(1/A[i][j], B[i], -1, B[j])
                A[i] = add_vec(1/A[i][j], A[i], -1, A[j])
    for i in range(0, n - 1):
        for j in range(i + 1, n):
            B[i] = add_vec(1, B[i], -A[i][j], B[j])
            A[i] = add_vec(1, A[i], -A[i][j], A[j])
    if zero_pivot:
        return None
    return B
