
from generic.dual import Dual, imag
from generic.la import Vector, Vectorial,\
    basis_from_dim, matrix_from_cols, transpose

# Derivative of a vector valued function
def diff(f, t):
    y = f(Dual(t, 1))
    return y.map(imag) if isinstance(y, Vectorial) else imag(y)

# Directional derivative
def diffv(f, x, v):
    y = f(Dual(x, v))
    return y.map(imag) if isinstance(y, Vectorial) else imag(y)

# Partial derivative
def pdiff_from_dim(n):
    basis = basis_from_dim(n)
    def pdiff(f, x, k):
        return diffv(f, x, basis[k])
    return pdiff

# Gradient
def grad_from_dim(n):
    basis = basis_from_dim(n)
    def grad(f, x):
        return Vector([diffv(f, x, v) for v in basis])
    return grad

# Divergence
def div_from_dim(n):
    pdiff = pdiff_from_dim(n)
    def div(f, x):
        return sum(pdiff(f, x, k)[k] for k in range(n))
    return div

# Jacobi matrix
def Diff_from_dim(n):
    pdiff = pdiff_from_dim(n)
    def Diff(f, x):
        return matrix_from_cols([pdiff(f, x, k) for k in range(n)])
    return Diff

# Metric tensor
def induced_metric(n, Phi):
    Diff = Diff_from_dim(n)
    def g(x):
        J = Diff(Phi, x)
        return transpose(J)*J
    return g

