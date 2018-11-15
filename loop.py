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


def tableu(prop_list):
    return True


def main():
    a = Term('a')
    nota = Not(a)
    notnota = Not(nota)
    print(nota)
    print(notnota)
    ex = [['a', 'and', 'b'],
          ['b', 'or', 'c'],
          ['a', '>', 'd']]
    ex_bool = tableu(ex)
    for term in ex:
        print(term)
    print('is', ex_bool)
    return


if __name__ == '__main__':
    main()
