
# misc – Small tools, scripts, modules 

## Proof verifiers

```
math/prop/
    Contains proof verifiers for natural deduction and Hilbert calculus
    for propositional logic.

math/fol/
    Contains proof verifiers for natural deduction and Hilbert calculus
    for first order logic.

math/prover/ ⚠️🏗️
    Contains a theorem prover for propositional calculus. It also finds
    counter models for propositions of intuitionistic, classical and
    modal propositional logic.
```

## Math tools

```
math/generic/complex.py
    A generic implementation of complex number arithmetic. One can have
    complex int, complex Fraction, complex Decimal and so on.

math/generic/dual.py
    A generic implementation of dual number arithmetic. With this one
    can compute exact derivatives of functions, of vector valued
    functions too.

math/generic/la.py
    A generic implementation of linear algebra.

math/generic/gmath.py
    A generic analog of the math module. It extends dual number
    arithmetic to the elementary functions.

math/generic/diffgeo.py
    Functions for vector calculus and differential geometry.
```

## Computer science

```
cs/parser/
    Prototypical expression parsers that can be adapted and extended to
    the desired language.

cs/imp/
    An implementation of the IMP language from "The Formal Semantics of
    Programming Languages" by Glynn Winskel. It contains an interpreter,
    a byte code compiler and a transcompiler targeting Python.

cs/imp/proofs/
    A computer-assisted formalization of the IMP language, its
    denotational semantics and the Hoare calculus.
```

## System tools

```
system/
    Mostly integrity tools that seem to be missing in the linux
    command-line utilities. For example, hash-list.py computes the
    list of all hash values of the files in a directory.
```
