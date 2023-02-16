
from generic.la import Vector, invert, transpose
from generic.diffgeo import grad_from_dim
from generic.dual import diff

def sgn(x):
    return -1 if x < 0 else 1 if x > 0 else 0

def bisection(f, a, b, tol = 1E-14, max_iter = 60):
    for _ in range(max_iter):
        c = (a + b)/2
        if f(c) == 0: return c
        if sgn(f(a)) != sgn(f(c)):
            b = c
        else:
            a = c
        if abs(b - a) < tol: break
    return (a + b)/2

def zeros(f, a, b, tol = 1E-14, n = 1000, max_iter = 60):
    h = (b - a)/n
    acc = []
    for k in range(n):
        x0 = a + h*k; x1 = a + h*(k + 1)
        if f(x0) == 0:
            acc.append(x0)
        elif f(x1) != 0 and sgn(f(x0)) != sgn(f(x1)):
            acc.append(bisection(f, x0, x1, tol, max_iter))
    return acc

def critical_locations(f, a, b, tol = 1E-14, n = 1000, max_iter = 60):
    return zeros(lambda x: diff(f, x), a, b, tol, n, max_iter) 

def minimum(f, a, b, tol):
    return bisection(lambda x: diff(f, x), a, b, tol, 20)

def gradient_descent(f, start, rate, tol = 1E-14, max_iter = None):
    if isinstance(start, list):
        dim = len(start)
        start = Vector(start)
    else:
        dim = len(start.a)
    if not isinstance(rate, list): rate = [0, rate]
    grad = grad_from_dim(dim)
    x = start; k = 0
    while k != max_iter:
        v = grad(f, x)
        if v*v < tol: break
        gamma = minimum(lambda r: f(x - v*r), rate[0], rate[1],  1E-6)
        x = x - gamma*v
        k += 1
    return x

