import z3


def ex1_goal():
    x = z3.BitVec('x', 8)
    y = z3.BitVec('y', 8)
    h = z3.BitVec('h', 8)

    phi_n = (y == x * 4)
    phi_s = (y == x << h)

    return (z3.ForAll([x, y], phi_n == phi_s))


def solve(phi):
    s = z3.Solver()
    s.add(phi)
    s.check()
    return s.model()


if __name__ == '__main__':
    goal = ex1_goal()
    print(solve(goal))
