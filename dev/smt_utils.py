import z3

def expression(coeff, var):
    if coeff == 1:
        return var
    elif coeff == -1:
        return -var
    elif coeff != 0:
        return coeff * var
    else:
        return z3.IntVal(0)

def comparator(comparison):
    if comparison == "=":
        return lambda x, y: x == y
    elif comparison == ">=":
        return lambda x, y: x >= y
    elif comparison == ">":
        return lambda x, y: x > y
    elif comparison == "<=":
        return lambda x, y: x <= y
    elif comparison == "<":
        return lambda x, y: x < y
    elif comparison == "!=":
        return lambda x, y: x != y
    else:
        raise ValueError("Comparison {} not supported.".format(comparison))
