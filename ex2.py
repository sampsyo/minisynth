import lark

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
  | "(" sum ")"

%import common.NUMBER
%import common.WS
%ignore WS
""".strip()


def interp(tree):
    """Evaluate the arithmetic expression.
    """

    op = tree.data
    if op in ('add', 'sub', 'mul', 'div', 'shl', 'shr'):  # Binary operators.
        lhs, rhs = interp(tree.children[0]), interp(tree.children[1])
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
        sub = interp(tree.children[0])
        return -sub
    elif op == 'num':  # Literal number.
        return int(tree.children[0])


def ex2():
    parser = lark.Lark(GRAMMAR)
    tree = parser.parse("1 * 2 + (1 - 5) << 1")
    print(interp(tree))


if __name__ == '__main__':
    ex2()
