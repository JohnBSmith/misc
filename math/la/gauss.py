
# Gauss-Jordan elimination, generating solution path.

from fractions import Fraction

def div(x, y):
    return Fraction(x)/y

def format_vec(v, f = str):
    return "[{}]".format(", ".join(f(r) for r in v))
    
def row_str(A, j):
    if isinstance(A[0], list):
        return "".join(["{:>8}".format(str(x)) for x in A[j]])
    else:
        return "{:>8}".format(str(A[j]))

def print_system(A, B, n):
    for j in range(0, n):
        print(row_str(A, j), "|", row_str(B, j))
    print()

def mul_matrix_vec(A, v):
    return [sum(A[i][j]*v[j] for j in range(0, len(v)))
        for i in range(0, len(A))]

def mul_scalar_vec(r, v):
    if isinstance(v, list):
        return [r*v[i] for i in range(0, len(v))]
    else:
        return r*v

def add_vec(r, v, s, w):
    if isinstance(v, list):
        return [r*v[i] + s*w[i] for i in range(0, len(v))]
    else:
        return r*v + s*w

def pivoting(A, B, n, j):
    m = abs(A[j][j])
    k = j
    for i in range(j + 1, n):
        if m < abs(A[i][j]):
            m = abs(A[i][j])
            k = i
    A[j], A[k] = A[k], A[j]
    B[j], B[k] = B[k], B[j]
    return m

def gauss_jordan(A, B, n):
    print("Lineares Gleichungssystem:")
    print_system(A, B, n)
    zero_pivot = False
    for j in range(0, n):
        pivot = pivoting(A, B, n, j)
        if pivot == 0:
            zero_pivot = True
            break
        print("Zeilenvertauschung:")
        print_system(A, B, n)
        B[j] = mul_scalar_vec(1/A[j][j], B[j])
        A[j] = mul_scalar_vec(1/A[j][j], A[j])
        for i in range(j + 1, n):
            if A[i][j] != 0:
                B[i] = add_vec(1/A[i][j], B[i], -1, B[j])
                A[i] = add_vec(1/A[i][j], A[i], -1, A[j])
        print("Schritt:")
        print_system(A, B, n)
    for i in range(0, n - 1):
        for j in range(i + 1, n):
            B[i] = add_vec(1, B[i], -A[i][j], B[j])
            A[i] = add_vec(1, A[i], -A[i][j], A[j])
        print("Schritt zur reduzierten Stufenform:")
        print_system(A, B, n)
    if zero_pivot:
        print("Die Matrix ist singulär.")
    return B

def unit_matrix(n, f):
    return [[f(int(i == j)) for i in range(n)] for j in range(n)]

def solve(A, b):
    A = [[Fraction(r) for r in x] for x in A]
    b = [Fraction(r) for r in b]
    x =  gauss_jordan(A, b, len(b))
    assert add_vec(-1, b, 1, mul_matrix_vec(A, x)) == [0]*len(b)

def invert(A):
    A = [[Fraction(r) for r in x] for x in A]
    B = unit_matrix(len(A), Fraction)
    X = gauss_jordan(A, B, len(A))


