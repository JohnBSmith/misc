
from generic.la import Matrix, gauss_jordan
from generic.poly import Polynomial

def interpolation_polynomial(points):
    n = len(points)
    X = Matrix([[x**k for k in range(n)] for (x, y) in points])
    Y = [y for (x, y) in points]
    coeff = gauss_jordan(X, Y, n)
    return Polynomial(coeff)

