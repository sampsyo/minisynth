import z3


def ex0():
    x = z3.Int('x')
    print(solve(x / 7 == 6))

    y = z3.BitVec('y', 8)
    print(solve(y << 3 == 336))

    z = z3.Int('z')
    n = z3.Int('n')
    print(solve(z3.ForAll([z], z * n == z)))


def solve(phi):
    s = z3.Solver()
    s.add(phi)
    s.check()
    return s.model()


if __name__ == '__main__':
    ex0()
