import lark
import z3
import sys

# A language based on a Lark example from:
# https://github.com/lark-parser/lark/wiki/Examples
GRAMMAR = """
?start: sum
  | sum "?" sum ":" sum -> cond

?sum: term
  | sum "+" term        -> add
  | sum "-" term        -> sub

?term: item
  | term "*"  item      -> mul
  | term "/"  item      -> div
  | term ">>" item      -> rshift
  | term "<<" item      -> lshift

?item: NUMBER           -> num
  | "-" item            -> neg
  | CNAME               -> var
  | "(" start ")"

%import common.NUMBER
%import common.WS
%import common.CNAME
%ignore WS
""".strip()

class Transformer:
    "A tree transformer inspired by Lark's transformers"

    depth = 0

    def transform(self, tree):
        self.depth += 1
        children = [self.transform(c) if isinstance(c, lark.Tree) else c for c in tree.children]
        self.depth -= 1
        try:
            f = getattr(self, tree.data)
        except AttributeError:
            return self.__default__(tree.data, *children)
        else:
            return f(*children)

    def __default__(self, data, children):
        raise Exception("Unhandled node", data, children)


class Interp(Transformer):
    def __init__(self, lookup):
        self.lookup = lookup

    from operator import (
        add, sub, mul, neg, lshift, rshift,
        truediv as div,
    )

    num = int

    def var(self, n):
        return self.lookup(n)

    def cond(self, cond, true, false):
        return (cond != 0) * true + (cond == 0) * false

def interp(tree, lookup):
    return Interp(lookup).transform(tree)


class Pretty(Transformer):
    """Pretty-print a tree, with optional substitutions applied."""

    def __init__(self, subst):
        self.subst = subst

    def par(self, s):
        return '('+s+')' if self.depth else s

    def neg(self, x):
        return '-' + x

    def num(self, n):
        return n

    def var(self, name):
        return str(self.subst.get(name, name))

    def cond(self, cond, true, false):
        return self.par('{} ? {} : {}'.format(cond, true, false))

    def __default__(self, op, lhs, rhs):
        assert op in ('add', 'sub', 'mul', 'div', 'lshift', 'rshift')
        c = {
            'add': '+',
            'sub': '-',
            'mul': '*',
            'div': '/',
            'lshift': '<<',
            'rshift': '>>',
        }[op]
        return self.par('{} {} {}'.format(lhs, c, rhs))

def pretty(tree, subst={}):
    return Pretty(subst).transform(tree)


def run(tree, env):
    """Ordinary expression evaluation.

    `env` is a mapping from variable names to values.
    """

    return interp(tree, lambda n: env[n])


def z3_expr(tree, vars=None):
    """Create a Z3 expression from a tree.

    Return the Z3 expression and a dict mapping variable names to all
    free variables occurring in the expression. All variables are
    represented as BitVecs of width 8. Optionally, `vars` can be an
    initial set of variables.
    """

    vars = dict(vars) if vars else {}

    # Lazily construct a mapping from names to variables.
    def get_var(name):
        if name in vars:
            return vars[name]
        else:
            v = z3.BitVec(name, 8)
            vars[name] = v
            return v

    return interp(tree, get_var), vars


def solve(phi):
    """Solve a Z3 expression, returning the model.
    """

    s = z3.Solver()
    s.add(phi)
    s.check()
    return s.model()


def model_values(model):
    """Get the values out of a Z3 model.
    """
    return {
        d.name(): model[d]
        for d in model.decls()
    }


def synthesize(tree1, tree2):
    """Given two programs, synthesize the values for holes that make
    them equal.

    `tree1` has no holes. In `tree2`, every variable beginning with the
    letter "h" is considered a hole.
    """

    expr1, vars1 = z3_expr(tree1)
    expr2, vars2 = z3_expr(tree2, vars1)

    # Filter out the variables starting with "h" to get the non-hole
    # variables.
    plain_vars = {k: v for k, v in vars1.items()
                  if not k.startswith('h')}

    # Formulate the constraint for Z3.
    goal = z3.ForAll(
        list(plain_vars.values()),  # For every valuation of variables...
        expr1 == expr2,  # ...the two expressions produce equal results.
    )

    # Solve the constraint.
    return solve(goal)


def ex2(source):
    src1, src2 = source.strip().split('\n')

    parser = lark.Lark(GRAMMAR)
    tree1 = parser.parse(src1)
    tree2 = parser.parse(src2)

    model = synthesize(tree1, tree2)
    print(pretty(tree1))
    print(pretty(tree2, model_values(model)))


if __name__ == '__main__':
    ex2(sys.stdin.read())
