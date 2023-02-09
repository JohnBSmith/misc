
from generic.la import det, matrix_from_cols,\
    transpose, basis_from_dim, invert
from fractions import Fraction

def is_linear_independent(system):
    A = matrix_from_cols(system).map(Fraction)
    if A.dim[0] != A.dim[1]:
        A = tranpose(A)*A
    return det(A) != 0

def basis_as_matrix(A):
    if A is None: return None
    if isinstance(A, list):
        return matrix_from_cols(A)
    else:
        return A

def transformation_matrix(n, f, A = None, B = None):
    A = basis_as_matrix(A)
    B = basis_as_matrix(B)
    e = basis_from_dim(n)
    M = matrix_from_cols([f(e[k]) for k in range(n)])
    if A is not None:
        return invert(B)*M*A if B is not None else M*A
    else:
        return invert(B)*M if B is not None else M

def transition_matrix(A, B):
    A = basis_as_matrix(A)
    B = basis_as_matrix(B)
    return invert(B)*A

