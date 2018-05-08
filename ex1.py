import z3


def ex1_goal():
    x = z3.BitVec('x', 8)
    y = z3.BitVec('y', 8)
    h = z3.BitVec('h', 8)

    phi_n = (y == x * 4)
    phi_s = (y == x << h)

    return (z3.ForAll([x, y], phi_n == phi_s))


def ex1():
    goal = ex1_goal()

    s = z3.Solver()
    s.add(goal)
    s.check()
    print(s.model())


if __name__ == '__main__':
    ex1()
