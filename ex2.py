import lark
import z3

# A language based on a Lark example from:
# https://github.com/lark-parser/lark/wiki/Examples
GRAMMAR = """
?start: sum

?sum: term
  | sum "+" term   -> add
  | sum "-" term   -> sub

?term: item
  | term "*"  item -> mul
  | term "/"  item -> div
  | term ">>" item -> shr
  | term "<<" item -> shl

?item: NUMBER      -> num
  | "-" item       -> neg
  | WORD           -> var
  | "(" sum ")"

%import common.NUMBER
%import common.WS
%import common.WORD
%ignore WS
""".strip()


def interp(tree, lookup):
    """Evaluate the arithmetic expression.

    Pass a tree as a Lark `Tree` object for the parsed expression. For
    `lookup`, provide a function for mapping variable names to values.
    """

    op = tree.data
    if op in ('add', 'sub', 'mul', 'div', 'shl', 'shr'):  # Binary operators.
        lhs = interp(tree.children[0], lookup)
        rhs = interp(tree.children[1], lookup)
        if op == 'add':
            return lhs + rhs
        elif op == 'sub':
            return lhs - rhs
        elif op == 'mul':
            return lhs * rhs
        elif op == 'div':
            return lhs / rhs
        elif op == 'shl':
            return lhs << rhs
        elif op == 'shr':
            return lhs >> rhs
    elif op == 'neg':  # Negation.
        sub = interp(tree.children[0], lookup)
        return -sub
    elif op == 'num':  # Literal number.
        return int(tree.children[0])
    elif op == 'var':  # Variable lookup.
        return lookup(tree.children[0])


def run(tree, env):
    """Ordinary expression evaluation.

    `env` is a mapping from variable names to values.
    """

    return interp(tree, lambda n: env[n])


def z3_expr(tree):
    """Create a Z3 expression from a tree.

    All variables are represented as BitVecs of width 8.
    """

    return interp(tree, lambda n: z3.BitVec(n, 8))


def ex2():
    parser = lark.Lark(GRAMMAR)
    tree = parser.parse("1 * 2 + (1 - x) << 1")
    print(run(tree, {'x': 9}))
    print(z3_expr(tree))


if __name__ == '__main__':
    ex2()
