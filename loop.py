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


def tableu(prop_list):
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
    ex = [['a', 'and', 'b'],
          ['b', 'or', 'c'],
          ['a', '>', 'd']]
    ex_bool = tableu(ex)
    for term in ex:
        print(term)
    print('is', ex_bool)
    return


if __name__ == '__main__':
    test()
    main()
