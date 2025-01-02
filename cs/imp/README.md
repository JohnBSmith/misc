
## An interpreter for the IMP language

This directory contains an interpreter and a compiler for IMP, a small
programming language used as an object of study in *The Formal Semantics
of Programming Languages* by Glynn Winskel.

* `imp.py` &ndash; An interpreter that executes IMP programs directly
  according to the denotational semantics of IMP.
* `impc.py` &ndash; A compiler that generates the machine code for a
  virtual machine.
* `impc.py --run` &ndash; Generates machine code and runs it.
* `imptopy.py` &ndash; Translates an IMP program to Python.

Example programs:

* `p1.txt` &ndash; Naive exponentiation.
* `p2.txt` &ndash; Exponentiation by squaring.
* `p3.txt` &ndash; Generates prime numbers.