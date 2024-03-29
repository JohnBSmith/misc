
import sys
sys.path.append("..")

from itertools import product
from fractions import Fraction
from generic.complex import Complex
from generic.dual import Dual, diff
from generic.poly import Polynomial
from generic.gmath import exp, log, log10, sqrt, erf, erfc,\
    sin, cos, tan, sinh, cosh, tanh,\
    asin, acos, atan, asinh, acosh, atanh
from generic.la import matrix, vector, identity, det, trace,\
    transpose as tp
from generic.diffgeo import diffv, grad_from_dim, Diff_from_dim,\
    div_from_dim, induced_metric, ext_from_dim, diff as vdiff
from math import pi
from random import randint

eps = 1E-14
j = Complex(0, 1)

z1 = (1 + 2*j) + (3 + 4*j); z2 = (1 + 2j) + (3 + 4j)
assert z1.re == z2.real and z1.im == z2.imag

z1 = (1 + 2*j) + 3; z2 = (1 + 2j) + 3
assert z1.re == z2.real and z1.im == z2.imag

z1 = 3 + (1 + 2*j); z2 = 3 + (1 + 2j)
assert z1.re == z2.real and z1.im == z2.imag

z1 = (1 + 2*j)*(3 + 4*j); z2 = (1 + 2j)*(3 + 4j)
assert z1.re == z2.real and z1.im == z2.imag

z1 = 2*(3 + 4*j); z2 = 2*(3 + 4j)
assert z1.re == z2.real and z1.im == z2.imag

z1 = (3 + 4*j)*2; z2 = (3 + 4j)*2
assert z1.re == z2.real and z1.im == z2.imag

for n in range(0, 20):
    z1 = (1 + 2*j)**n; z2 = (1 + 2j)**n
    assert z1.re == z2.real and z1.im == z2.imag

z1 = (1 + 2*j)/(3 + 4*j); z2 = (1 + 2j)/(3 + 4j)
assert abs(z1.re - z2.real) < eps and abs(z1.im - z2.imag) < eps

z1 = 1/(3 + 4*j); z2 = 1/(3 + 4j)
assert abs(z1.re - z2.real) < eps and abs(z1.im - z2.imag) < eps

z1 = (3 + 4*j)/2; z2 = (3 + 4j)/2
assert abs(z1.re - z2.real) < eps and abs(z1.im - z2.imag) < eps

z1 = Dual(10, 20) + Dual(1, 2)
assert z1.re == 11 and z1.im == 22

z1 = Dual(10, 20) - Dual(1, 2)
assert z1.re == 9 and z1.im == 18

z1 = -Dual(1, 2)
assert z1.re == -1 and z1.im == -2

z1 = Dual(10, 20)*Dual(2, 3)
assert z1.re == 20 and z1.im == 70

assert diff(lambda x: -x, 2) == -1
assert diff(lambda x: x*x, 3) == 6
assert diff(lambda x: x*x*x + x*x, 3) == 33
assert diff(lambda x: x*x*x - x*x, 3) == 21
assert diff(lambda x: x**2, 3) == 6
assert diff(lambda x: x**3 + x**2, 3) == 33
assert diff(lambda x: x**3 - x**2, 3) == 21

f = Polynomial([1, 2, 3, 4])
g = Polynomial([10, 20])
assert (-f).coeff == [-1, -2, -3, -4]
assert (f + g).coeff == [11, 22, 3, 4]
assert (g + f).coeff == (f + g).coeff
assert (f - g).coeff == [-9, -18, 3, 4]
assert (g - f).coeff == [9, 18, -3, -4]
assert (f*g).coeff == [10, 40, 70, 100, 80]
assert (g*f).coeff == (f*g).coeff

f = Polynomial([1])
assert f(2) == 1
assert (f**2).coeff == [1]
assert (f*f).coeff == [1]

f = Polynomial([1, 2])
assert f(2) == 5
assert (f**2).coeff == [1, 4, 4]
assert (f*f).coeff == (f**2).coeff
assert (f**3).coeff == [1, 6, 12, 8]
assert ((f*f)*f).coeff == (f**3).coeff
assert (f*(f*f)).coeff == (f**3).coeff
assert (f**4).coeff == [1, 8, 24, 32, 16]
assert (f*f*f*f).coeff == (f**4).coeff
assert (f*(f*f)*f).coeff == (f**4).coeff
assert (f*((f*f)*f)).coeff == (f**4).coeff
assert (f*(f*(f*f))).coeff == (f**4).coeff

f = Polynomial([1, 2, 3])
assert f(2) == 17
assert (f**2).coeff == [1, 4, 10, 12, 9]
assert (f*f).coeff == (f**2).coeff
assert (f**3).coeff == [1, 6, 21, 44, 63, 54, 27]
assert ((f*f)*f).coeff == (f**3).coeff
assert (f*(f*f)).coeff == (f**3).coeff

f = Polynomial([1, 2, 3, 4])
assert f(2) == 49
assert (f**2).coeff == [1, 4, 10, 20, 25, 24, 16]
assert (f*f).coeff == (f**2).coeff

assert (Polynomial([1, 2]) + 10).coeff == [11, 2]
assert (Polynomial([1, 2]) - 10).coeff == [-9, 2]
assert (10 + Polynomial([1, 2])).coeff == [11, 2]
assert (10 - Polynomial([1, 2])).coeff == [9, -2]

assert abs(diff(exp, 1) - exp(1)) < eps
assert abs(diff(log, 2) - 1/2) < eps
assert abs(diff(log10, 2) - 1/(log(10)*2)) < eps
assert abs(diff(sqrt, 2) - 1/(2*sqrt(2))) < eps
assert abs(diff(sin, 1) - cos(1)) < eps
assert abs(diff(cos, 1) + sin(1)) < eps
assert abs(diff(tan, 1) - (1 + tan(1)**2)) < eps
assert abs(diff(sinh, 1) - cosh(1)) < eps
assert abs(diff(cosh, 1) - sinh(1)) < eps
assert abs(diff(tanh, 1) - (1 - tanh(1)**2)) < eps
assert abs(diff(asin, 1/2) - 2/sqrt(3)) < eps
assert abs(diff(acos, 1/2) + 2/sqrt(3)) < eps
assert abs(diff(atan, 1/2) - 4/5) < eps
assert abs(diff(asinh, 1) - 1/sqrt(2)) < eps
assert abs(diff(acosh, 2) - 1/sqrt(3)) < eps
assert abs(diff(atanh, 1/2) - 4/3) < eps
assert abs(diff(erf, 1) - 2*exp(-1)/sqrt(pi)) < eps
assert abs(diff(erfc, 1) + 2*exp(-1)/sqrt(pi)) < eps

f = lambda x: 2/(exp(-2*x) + 1) - 1
assert abs(diff(f, 1) - (1 - tanh(1)**2)) < eps

f = lambda x: log(x**2 + 1)
assert abs(diff(f, 2) - 4/5) < eps

a = vector(1, 2)
b = vector(3, 4)
assert 2*a == vector(2, 4)
assert 2*a == a + a and 3*a == a + a + a
assert -a == (-1)*a and -a == vector(-1, -2)
assert a + b == vector(4, 6)
assert a - b == vector(-2, -2)
assert b - a == vector(2, 2)
assert 5*a + 7*b == vector(26, 38)
assert 5*a - (-7)*b == vector(26, 38)
assert a*b == 11
assert (a + b)*(a + b) == 52
assert (a + b)*(a + b) == a*a + 2*a*b + b*b
assert (a - b)*(a - b) == 8 and (b - a)*(b - a) == 8
assert (a + b)*(a - b) == -20
assert (a + b)*(a - b) == a*a - b*b

A = matrix([1, 2], [3, 4])
B = matrix([5, 6], [7, 8])
E = matrix([1, 0], [0, 1])
Z = matrix([0, 0], [0, 0])
assert 2*A == matrix([2, 4], [6, 8])
assert 7*A == matrix([7, 14], [21, 28])
assert (-1)*A == matrix([-1, -2], [-3, -4])
assert -A == (-1)*A
assert A + A == 2*A and A - A == Z
assert A + (-A) == Z and (-A) + A == Z
assert A + (-1)*A == Z and (-1)*A + A == Z
assert A + B == matrix([6, 8], [10, 12])
assert B + A == A + B
assert A*A == matrix([7, 10], [15, 22])
assert A*B == matrix([19, 22], [43, 50])
assert B*A == matrix([23, 34], [31, 46])

assert A**0 == E
assert A**1 == A
assert A**2 == matrix([7, 10], [15, 22])
assert A**3 == matrix([37, 54], [81, 118])
assert A**4 == matrix([199, 290], [435, 634])
assert A**5 == matrix([1069, 1558], [2337, 3406])
assert A**6 == matrix([5743, 8370], [12555, 18298])
assert A**7 == matrix([30853, 44966], [67449, 98302])
assert A**8 == matrix([165751, 241570], [362355, 528106])
assert A**9 == matrix([890461, 1297782], [1946673, 2837134])
assert A**2 == A*A
assert A**3 == A*A*A and A**3 == A*(A*A) 
assert A**4 == A*A*A*A and A**4 == A*(A*A*A)
assert A**4 == A*(A*(A*A)) and A**4 == (A*A)*(A*A)

assert tp(17*A) == 17*tp(A) and tp(-A) == -tp(A)
assert tp(A + B) == tp(A) + tp(B)
assert tp(A + B) == tp(B) + tp(A)
assert tp(A - B) == tp(A) - tp(B)
assert tp(A*B) == tp(B)*tp(A)
assert all(tp(A**k) == tp(A)**k for k in range(0, 10))
assert trace(A) == 5 and trace(B) == 13
assert trace(tp(A)) == 5 and trace(tp(B)) == 13

A = matrix([1, 2, 3])
B = matrix([4, 5, 6])
assert tp(B) == matrix([4], [5], [6])
assert tp(tp(B)) == B
assert A*tp(B) == matrix([32])
assert tp(B)*A == matrix([4, 8, 12], [5, 10, 15], [6, 12, 18])
assert tp(B)*A == matrix([4], [5], [6])*A

A = matrix([1, 2, 3], [4, 5, 6])
B = matrix([7, 8], [9, 10], [11, 12])
assert tp(A) == matrix([1, 4], [2, 5], [3, 6])
assert tp(B) == matrix([7, 9, 11], [8, 10, 12])
assert tp(tp(A)) == A
assert tp(tp(B)) == B
assert A*B == matrix([58, 64], [139, 154])
assert tp(A*B) == matrix([58, 139], [64, 154])
assert tp(A*B) == tp(B)*tp(A)
assert A*B == tp(tp(B)*tp(A))
assert B*A == matrix([39, 54, 69], [49, 68, 87], [59, 82, 105])
assert tp(B*A) == matrix([39, 49, 59], [54, 68, 82], [69, 87, 105])
assert tp(B*A) == tp(A)*tp(B)
assert B*A == tp(tp(A)*tp(B))
assert A*tp(A) == matrix([14, 32], [32, 77])
assert tp(A)*A == matrix([17, 22, 27], [22, 29, 36], [27, 36, 45])
assert tp(A*tp(A)) == A*tp(A)
assert tp(tp(A)*A) == tp(A)*A

A = matrix([1, 2], [3, 4]).map(Fraction)
E = matrix([1, 0], [0, 1])
assert det(A) == -2
assert A**-1 == matrix([-2, 1], [Fraction(3, 2), -Fraction(1, 2)])
assert (A**-1)*A == E and A*(A**-1) == E
assert (A**-1)**2*A**2 == E and A**2*(A**-1)**2 == E
assert (A**2)**-1 == (A**-1)**2 == A**-2

A = matrix([1, 2, 3], [4, 5, 6], [7, 8, 11]).map(Fraction)
E = identity(3)
assert trace(A) == 17 and trace(tp(A)) == 17
assert det(A) == -6
assert (A**-1)*A == E and A*(A**-1) == E
assert (A**-1)**2*A**2 == E and A**2*(A**-1)**2 == E
assert (A**2)**-1 == (A**-1)**2 == A**-2

A = matrix(
    [ 2,  3,  5,  7],
    [11, 13, 17, 19],
    [23, 29, 31, 37],
    [41, 43, 47, 53]
).map(Fraction)
E = identity(4)
assert trace(A) == 99 and trace(tp(A)) == 99
assert det(A) == 880
assert (A**-1)*A == E and A*(A**-1) == E
assert (A**-1)**2*A**2 == E and A**2*(A**-1)**2 == E
assert (A**2)**-1 == (A**-1)**2 == A**-2

A = matrix([1, 2, 3], [4, 5, 6], [7, 8, 9]).map(Fraction)
assert det(A) == 0
assert det(A*A) == 0

A = matrix(
    [ 1,  2,  3,  4],
    [ 5,  6,  7,  8],
    [ 9, 10, 11, 12],
    [13, 14, 15, 16]
).map(Fraction)
assert det(A) == 0
assert det(A*A) == 0

vec = vector
f = lambda t: vec(t**2 + t, t**3)
for t in range(4):
    assert vdiff(f, t) == vec(2*t + 1, 3*t**2)

f = lambda x: x[0]**2 + x[1]**2
g = lambda x: x*x
for (x, y, vx, vy) in product(range(4), repeat = 4):
    assert diffv(f, vec(x, y), vec(vx, vy)) == 2*(x*vx + y*vy)
    assert diffv(g, vec(x, y), vec(vx, vy)) == 2*(x*vx + y*vy)

f = lambda x: (x[0] + x[1])**2
for (x, y, vx, vy) in product(range(4), repeat = 4):
    assert diffv(f, vec(x, y), vec(vx, vy)) == 2*(x + y)*(vx + vy)

f = lambda x: vec(x[0]**2 + x[1]**2, (x[0] - x[1])**2)
for (x, y, vx, vy) in product(range(4), repeat = 4):
    z = diffv(f, vec(x, y), vec(vx, vy))
    assert z == vec(2*(x*vx + y*vy), 2*(x - y)*(vx - vy))

f = lambda x: 2*x
for (x, y, vx, vy) in product(range(4), repeat = 4):
    assert diffv(f, vec(x, y), vec(vx, vy)) == 2*vec(vx, vy)

A = matrix([1, 2], [3, 4])
f = lambda x: A*x
for (x, y, vx, vy) in product(range(4), repeat = 4):
    assert diffv(f, vec(x, y), vec(vx, vy)) == A*vec(vx, vy)

f = lambda x: x*(A*x)
for (x, y, vx, vy) in product(range(4), repeat = 4):
    z = diffv(f, vec(x, y), vec(vx, vy))
    assert z == (A + tp(A))*vec(x, y)*vec(vx, vy)
    assert z == vec(x, y)*((A + tp(A))*vec(vx, vy))

f = lambda X: X*X
V = matrix([1, 2], [3, 4])
for (a11, a12, a21, a22) in product(range(4), repeat = 4):
    A = matrix([a11, a12], [a21, a22])
    assert diffv(f, A, V) == A*V + V*A
    assert diffv(f, V, A) == A*V + V*A

grad = grad_from_dim(2)
f = lambda x: x[0]**2 + x[1]**2
for (x, y) in product(range(4), repeat = 2):
    assert grad(f, vec(x, y)) == vec(2*x, 2*y)

f = lambda x: 3*x[0]**2*x[1]**3 - 2*x[0]*x[1]
for (x, y) in product(range(4), repeat = 2):
    assert grad(f, vec(x, y)) == vec(6*x*y**3 - 2*y, 9*(x*y)**2 - 2*x)

Diff = Diff_from_dim(2); div = div_from_dim(2)
Phi = lambda x: vec(x[0]**2 + x[1]**2, x[0] + x[1]**3)
g = induced_metric(2, Phi)
for (x, y) in product(range(4), repeat = 2):
    assert Diff(Phi, vec(x, y)) == matrix([2*x, 2*y], [1, 3*y**2])
    assert div(Phi, vec(x, y)) == 2*x + 3*y**2
    r1 = [4*x**2 + 1, 4*x*y + 3*y**2]
    r2 = [4*x*y + 3*y**2, 4*y**2 + 9*y**4]
    assert g(vec(x, y)) == matrix(r1, r2)

ext = ext_from_dim(2)
f = lambda x: vec(x[0]**2 + x[1]**2, x[0]*x[1]**2)
for (x, y) in product(range(4), repeat = 2):
    assert ext(f, vec(x, y)) == matrix([0, y**2 - 2*y], [2*y - y**2, 0])

def random_matrix(n, a, b):
    acc = []
    for i in range(n):
        acc.append([randint(a, b) for j in range(n)])
    return matrix(*acc)

def matrix_inv_test(N):
    for n in range(1, 10):
        E = identity(n)
        for i in range(N):
            A = random_matrix(n, -10, 10).map(Fraction)
            if det(A) != 0:
                B = A**-1
                assert B*A == E and A*B == E

matrix_inv_test(10)
