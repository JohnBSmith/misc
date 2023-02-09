
import math, cmath
from generic.dual import Dual

__dispatch_exp__ = {
    int: math.exp,
    float: math.exp,
    complex: cmath.exp,
}

__dispatch_log__ = {
    int: math.log,
    float: math.log,
    complex: cmath.log
}

__dispatch_log10__ = {
    int: math.log10,
    float: math.log10,
    complex: cmath.log10
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

__dispatch_sqrt__ = {
    int: math.sqrt,
    float: math.sqrt,
    complex: cmath.sqrt
}

__dispatch_asin__ = {
    int: math.asin,
    float: math.asin,
    complex: cmath.asin
}

__dispatch_acos__ = {
    int: math.acos,
    float: math.acos,
    complex: cmath.acos
}

__dispatch_atan__ = {
    int: math.atan,
    float: math.atan,
    complex: cmath.atan
}

__dispatch_asinh__ = {
    int: math.asinh,
    float: math.asinh,
    complex: cmath.asinh
}

__dispatch_acosh__ = {
    int: math.acosh,
    float: math.acosh,
    complex: cmath.acosh
}

__dispatch_atanh__ = {
    int: math.atanh,
    float: math.atanh,
    complex: cmath.atanh
}

__dispatch_erf__ = {
    int: math.erf,
    float: math.erf
}

__dispatch_erfc__ = {
    int: math.erfc,
    float: math.erfc
}

def exp(x):
    return __dispatch_exp__[type(x)](x)

def log(x):
    return __dispatch_log__[type(x)](x)

def log10(x):
    return __dispatch_log10__[type(x)](x)

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

def asin(x):
    return __dispatch_asin__[type(x)](x)

def acos(x):
    return __dispatch_acos__[type(x)](x)

def atan(x):
    return __dispatch_atan__[type(x)](x)

def asinh(x):
    return __dispatch_asinh__[type(x)](x)

def acosh(x):
    return __dispatch_acosh__[type(x)](x)

def atanh(x):
    return __dispatch_atanh__[type(x)](x)

def sqrt(x):
    return __dispatch_sqrt__[type(x)](x)

def erf(x):
    return __dispatch_erf__[type(x)](x)

def erfc(x):
    return __dispatch_erfc__[type(x)](x)

def __dual_exp__(x):
    return Dual(exp(x.re), x.im*exp(x.re))
def __dual_log__(x):
    return Dual(log(x.re), x.im/x.re)
def __dual_log10__(x):
    return Dual(log10(x.re), x.im/(math.log(10)*x.re))
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
def __dual_asin__(x):
    return Dual(asin(x.re), x.im/sqrt(1 - x.re*x.re))
def __dual_acos__(x):
    return Dual(acos(x.re), -x.im/sqrt(1 - x.re*x.re))
def __dual_atan__(x):
    return Dual(atan(x.re), x.im/(x.re*x.re + 1))
def __dual_asinh__(x):
    return Dual(asinh(x.re), x.im/sqrt(x.re*x.re + 1))
def __dual_acosh__(x):
    return Dual(acosh(x.re), x.im/sqrt(x.re*x.re - 1))
def __dual_atanh__(x):
    return Dual(atanh(x.re), x.im/(1 - x.re*x.re))
def __dual_sqrt__(x):
    return Dual(sqrt(x.re), x.im/(2*sqrt(x.re)))
def __dual_erf__(x):
    return Dual(erf(x.re), x.im*2/sqrt(math.pi)*exp(-x.re*x.re))
def __dual_erfc__(x):
    return Dual(erf(x.re), -x.im*2/sqrt(math.pi)*exp(-x.re*x.re))

__dispatch_exp__[Dual] = __dual_exp__
__dispatch_log__[Dual] = __dual_log__
__dispatch_log10__[Dual] = __dual_log10__
__dispatch_sin__[Dual] = __dual_sin__
__dispatch_cos__[Dual] = __dual_cos__
__dispatch_tan__[Dual] = __dual_tan__
__dispatch_sinh__[Dual] = __dual_sinh__
__dispatch_cosh__[Dual] = __dual_cosh__
__dispatch_tanh__[Dual] = __dual_tanh__
__dispatch_asin__[Dual] = __dual_asin__
__dispatch_acos__[Dual] = __dual_acos__
__dispatch_atan__[Dual] = __dual_atan__
__dispatch_asinh__[Dual] = __dual_asinh__
__dispatch_acosh__[Dual] = __dual_acosh__
__dispatch_atanh__[Dual] = __dual_atanh__
__dispatch_sqrt__[Dual] = __dual_sqrt__
__dispatch_erf__[Dual] = __dual_erf__
__dispatch_erfc__[Dual] = __dual_erfc__

