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


class TableauLeaf():
    def __init__(self, parent, main, branch):
        self.parent = parent
        self.main = main
        self.branch = branch
        return


def is_separable(term):
    separable = [And, Or]
    ret = False
    for separable_type in separable:
        if isinstance(term, separable_type):
            ret = True
    return ret


def tableau(term_list):
    for term in term_list:
        if is_separable(term):
            pass
    return True


def test_and_or():
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
    return


def main():
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
