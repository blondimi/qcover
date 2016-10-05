def leq(x, y):
    return all(x[i] <= y[i] for i in range(len(x)))

def subseteq_upward(A, B):
    return all(any(leq(y, x) for y in B) for x in A)

def in_upward(v, basis):
    return subseteq_upward({v}, basis)

def minimize(basis):
    return {v for v in basis if all(u == v or not leq(u, v) for u in
                                      basis)}

# Merges A and B into A
def merge_upward(A, B):
    A.difference_update(B) # To avoid removing all instances of an element
    A.difference_update({x for x in A if any(leq(y, x) for y in B)})
    A.update({x for x in B if not any(leq(y, x) for y in A)})

# Removes B from A
def setdiff_upward(A, B):
    A.difference_update({x for x in A if any(leq(y, x) for y in B)})

# Adds vector to basis
def update_upward(basis, vector):
    to_remove = set()

    if vector in basis:
        return

    for v in basis:
        if leq(vector, v):
            to_remove.add(v)
        elif leq(v, vector):
            return

    basis.add(vector)
    basis.difference_update(to_remove)
