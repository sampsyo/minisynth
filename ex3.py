import ex2
import sys
import lark


def desugar_hole(source):
    parts = source.split('??')
    out = []
    for (i, part) in enumerate(parts[:-1]):
        out.append(part)
        out.append('(hb{0} ? x : hn{0})'.format(i))
    out.append(parts[-1])
    return ''.join(out)


def ex3(source):
    src1, src2 = source.strip().split('\n')

    src2 = desugar_hole(src2)  # Allow ?? in the sketch part.

    parser = lark.Lark(ex2.GRAMMAR)
    tree1 = parser.parse(src1)
    tree2 = parser.parse(src2)

    model = ex2.synthesize(tree1, tree2)
    print(ex2.pretty(tree1))
    print(ex2.pretty(tree2, ex2.model_values(model)))


if __name__ == '__main__':
    ex3(sys.stdin.read())
