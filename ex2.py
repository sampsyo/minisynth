import lark

# A language based on a Lark example from:
# https://github.com/lark-parser/lark/wiki/Examples
GRAMMAR = """
?start: sum

?sum: product
  | sum "+" product  -> add
  | sum "-" product  -> sub

?product: item
  | product "*" item -> mul
  | product "/" item -> div

?item: NUMBER        -> num
  | "-" item         -> neg
  | "(" sum ")"

%import common.NUMBER
%import common.WS
%ignore WS
""".strip()


def interp(tree):
    if tree.data == 'add':
        lhs, rhs = interp(tree.children[0]), interp(tree.children[1])
        return lhs + rhs
    elif tree.data == 'sub':
        lhs, rhs = interp(tree.children[0]), interp(tree.children[1])
        return lhs - rhs
    elif tree.data == 'mul':
        lhs, rhs = interp(tree.children[0]), interp(tree.children[1])
        return lhs * rhs
    elif tree.data == 'div':
        lhs, rhs = interp(tree.children[0]), interp(tree.children[1])
        return lhs / rhs
    elif tree.data == 'neg':
        sub = interp(tree.children[0])
        return -sub
    elif tree.data == 'num':
        return int(tree.children[0])


def ex2():
    parser = lark.Lark(GRAMMAR)
    tree = parser.parse("1 * 2 + (1 - 5)")
    print(interp(tree))


if __name__ == '__main__':
    ex2()
