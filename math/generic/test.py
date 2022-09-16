
from complex import Complex
from dual import Dual, diff
from poly import Polynomial

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

