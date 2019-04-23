
from numpy import matrix, array, arange
from numpy.linalg import solve

def regression_quadratic(data):
    n = len(data)
    sx = sum(x for [x,y] in data)
    sx2 = sum(x**2 for [x,y] in data)
    sx3 = sum(x**3 for [x,y] in data)
    sx4 = sum(x**4 for [x,y] in data)
    sy = sum(y for [x,y] in data)
    sxy = sum(x*y for [x,y] in data)
    sx2y = sum(x**2*y for [x,y] in data)

    A = matrix([
        [sx4,sx3,sx2],
        [sx3,sx2,sx],
        [sx2,sx,n]
    ])
    v = array([sx2y,sxy,sy])
    [a,b,c] = solve(A,v)
    return {
        "a": a, "b": b, "c": c,
        "f": lambda x: a*x**2+b*x+c
    }

def regression(data,X,step):
    import matplotlib.pyplot as plot

    t = regression_quadratic(data)

    print("a = {}".format(t["a"]))
    print("b = {}".format(t["b"]))
    print("c = {}".format(t["c"]))

    [x,y] = zip(*data)
    plot.plot(x,y,'o',color='black')

    x = arange(X[0],X[1],step)
    plot.plot(x,t["f"](x),color='black')

    plot.show()

data = [
    [0,2], [1,2.5], [1,3], [2,3.4],
    [2.5,4], [3,4.2], [4,4.2], [5,4.0]
]
regression(data,X=[0,6],step=0.1)
