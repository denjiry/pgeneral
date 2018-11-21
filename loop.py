class Term():
    def __init__(self, name=None):
        self.name = name
        return

    def __repr__(self):
        return self.name if self.name else 'term'


class Not(Term):
    def __init__(self, term):
        assert isinstance(term, Term)
        self.term = term
        return

    def __repr__(self):
        return 'Not('+self.term.__repr__()+')'


class And(Term):
    def __init__(self, term1, term2):
        assert isinstance(term1, Term) and isinstance(term2, Term)
        self.term1 = term1
        self.term2 = term2
        return

    def __repr__(self):
        return '('+self.term1.__repr__()+' & '+self.term2.__repr__()+')'


class Or(Term):
    def __init__(self, term1, term2):
        assert isinstance(term1, Term) and isinstance(term2, Term)
        self.term1 = term1
        self.term2 = term2
        return

    def __repr__(self):
        return '('+self.term1.__repr__()+' or '+self.term2.__repr__()+')'


class Node():
    def __init__(self, term, main, branch=None):
        assert isinstance(term, Term)
        assert isinstance(main, Node) or (main is None)
        assert isinstance(branch, Node) or (branch is None)
        self.term = term
        self.main = main
        self.branch = branch
        return


class Tree():
    def __init__(self):
        return


def tail_main(root):
    if root.main is None:
        ret = root
    else:
        ret = tail_main(root.main)
    return ret


def collect_tails(root):
    tails = []
    node = root
    next_node = None
    prev = None
    parents = [None]
    while next_node != root:
        print(node.term)
        if prev is parents[-1]:
            if node.main is not None:
                next_node = node.main
            elif node.branch is not None:
                next_node = node.branch
            else:
                tails.append(node)
                next_node = parents.pop()
        elif prev is node.main:
            if node.branch:
                next_node = node.branch
            else:
                next_node = parents.pop()
        else:
            next_node = parents.pop()
        # update
        if (next_node is node.main) or (next_node is node.branch):
            parents.append(node)
        prev = node
        node = next_node
    return tails


def is_separable(term):
    separable = [And, Or]
    ret = False
    for separable_type in separable:
        if isinstance(term, separable_type):
            ret = True
            break
    return ret


def tableau(term_list):
    for term in term_list:
        if is_separable(term):
            pass
    return True


def test_node():
    print('test_node')
    a = Term('a')
    b = Term('b')
    aandb = And(a, b)
    aornotb = Or(a, Not(b))
    aornotborb = Or(aornotb, b)
    root = Node(a, Node(b, Node(aandb, Node(aornotb, None))))
    print(tail_main(root).term)
    tail_main(root).main = Node(aornotborb, None)
    print(tail_main(root).term)
    print('test_collect_tails')
    root.main.main.branch = Node(Term('c'), None)
    tails = collect_tails(root)
    print('tails:', [t.term for t in tails])
    return root


def test_and_or():
    print('test_and_or')
    a = Term('a')
    b = Term('b')
    aandb = And(a, b)
    aornotb = Or(a, Not(b))
    aornotborb = Or(aornotb, b)
    print(aandb)
    print(aornotb)
    print(aornotborb)
    return


def test_Not():
    a = Term('a')
    nota = Not(a)
    notnota = Not(nota)
    print(nota)
    print(notnota)
    return


def test():
    test_Not()
    test_and_or()
    test_node()
    return


def main():
    print('main')
    a = Term('a')
    b = Term('b')
    c = Term('c')
    d = Term('d')
    ex = [a,
          Or(a, b),
          And(b, c),
          Or(c, Not(d)),
          d]
    ex_bool = tableau(ex)
    for term in ex:
        print(term)
    print('is', ex_bool)
    return


if __name__ == '__main__':
    test()
    main()
