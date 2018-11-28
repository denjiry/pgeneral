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
        self.checked = False
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
    if (root.main is None) and (root.branch is None):
        # if root is a node
        return []
    while next_node != root:
        print(node.term, end=', ')
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
    print('TERM END.')
    return tails


def is_separable(term):
    # TODO: implement Not(a /\ b), Not(a \/ b)
    assert isinstance(term, Term)
    separable = [And, Or]
    ret = False
    for separable_type in separable:
        if isinstance(term, separable_type):
            ret = True
            break
    return ret


def separate(node):
    if isinstance(node, Or):
        return [Node(node.term1, None), Node(node.term1, None)]
    elif isinstance(node, And):
        return [Node(node.term1, Node(node.term2, None))]
    return []


def open_top_node(tree):
    tails = collect_tails(tree)
    if is_separable(tree.term):
        separated = separate(tree.term)
        for tail in tails:
            if len(separated) == 2:
                tail.main = separated[0]
                tail.branch = separated[1]
            elif len(separated) == 1:
                tail.main = separated[0]
            else:
                raise(NotImplementedError)
    return tree


def tableau(root):
    node = root
    next_node = None
    prev = None
    parents = [None]
    is_tableau_closed = True
    if (root.main is None) and (root.branch is None):
        # if root is a node
        return []
    while next_node != root:
        print('current node:', node.term)
        if prev is parents[-1]:
            if node.main is not None:
                next_node = node.main
            elif node.branch is not None:
                next_node = node.branch
            else:
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
    return is_tableau_closed


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
    print('test_open_top_node')
    root = Node(aornotb, Node(aandb, Node(a, None)))
    root.main.branch = Node(Term('c'), None)
    print('before tails:', [t.term for t in collect_tails(root)])
    opened = open_top_node(root)
    print('opened tails:', [t.term for t in collect_tails(opened)])
    print('test_tableau')
    root = Node(a, Node(b, Node(aandb, Node(aornotb, None))))
    root.main.main.branch = Node(Term('c'), None)
    tree = tableau(root)
    # print('opened:', [t.term for t in tree])
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
    # print('main')
    # a = Term('a')
    # b = Term('b')
    # c = Term('c')
    # d = Term('d')
    # ex = [a,
    #       Or(a, b),
    #       And(b, c),
    #       Or(c, Not(d)),
    #       d]
    # ex_bool = tableau(ex)
    # for term in ex:
    #     print(term)
    # print('is', ex_bool)
    return


if __name__ == '__main__':
    test()
    main()
