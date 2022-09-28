
import sys, math, cmath
from generic.dual import Dual

__dispatch_exp__ = {
    int: math.exp,
    float: math.exp,
    complex: cmath.exp,
}

__dispatch_sin__ = {
    int: math.sin,
    float: math.sin,
    complex: cmath.sin
}

__dispatch_cos__ = {
    int: math.cos,
    float: math.cos,
    complex: cmath.cos
}

__dispatch_tan__ = {
    int: math.tan,
    float: math.tan,
    complex: cmath.tan
}

__dispatch_sinh__ = {
    int: math.sinh,
    float: math.sinh,
    complex: cmath.sinh
}

__dispatch_cosh__ = {
    int: math.cosh,
    float: math.cosh,
    complex: cmath.cosh
}

__dispatch_tanh__ = {
    int: math.tanh,
    float: math.tanh,
    complex: cmath.tanh
}

def exp(x):
    return __dispatch_exp__[type(x)](x)

def sin(x):
    return __dispatch_sin__[type(x)](x)

def cos(x):
    return __dispatch_cos__[type(x)](x)

def tan(x):
    return __dispatch_tan__[type(x)](x)

def sinh(x):
    return __dispatch_sinh__[type(x)](x)

def cosh(x):
    return __dispatch_cosh__[type(x)](x)

def tanh(x):
    return __dispatch_tanh__[type(x)](x)

def __dual_exp__(x):
    return Dual(exp(x.re), x.im*exp(x.re))
def __dual_sin__(x):
    return Dual(sin(x.re), x.im*cos(x.re))
def __dual_cos__(x):
    return Dual(cos(x.re), -x.im*sin(x.re))
def __dual_tan__(x):
    return Dual(tan(x.re), x.im*(1 + tan(x.re)**2))
def __dual_sinh__(x):
    return Dual(sinh(x.re), x.im*cosh(x.re))
def __dual_cosh__(x):
    return Dual(cosh(x.re), x.im*sinh(x.re))
def __dual_tanh__(x):
    return Dual(tanh(x.re), x.im*(1 - tanh(x.re)**2))
__dispatch_exp__[Dual] = __dual_exp__
__dispatch_sin__[Dual] = __dual_sin__
__dispatch_cos__[Dual] = __dual_cos__
__dispatch_tan__[Dual] = __dual_tan__
__dispatch_sinh__[Dual] = __dual_sinh__
__dispatch_cosh__[Dual] = __dual_cosh__
__dispatch_tanh__[Dual] = __dual_tanh__

