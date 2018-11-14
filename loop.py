def tableu(prop_list):
    return True


def main():
    ex = ["a and b",
          'b or c',
          'a > d']
    ex_bool = tableu(ex)
    for term in ex:
        print(term)
    print('is', ex_bool)
    return


if __name__ == '__main__':
    main()
