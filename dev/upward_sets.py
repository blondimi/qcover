class Upward:
    @staticmethod
    def subseteq(A, B):
        return all(any(y <= x for y in B) for x in A)

    @staticmethod
    def elem_of(v, basis):
        return Upward.subseteq({v}, basis)

    @staticmethod
    def minimize(basis):
        return {v for v in basis if all(u == v or not u <= v for u in
                                        basis)}

    # Merges A and B into A
    @staticmethod
    def merge(A, B):
        A.difference_update(B) # To avoid removing all instances of an element
        A.difference_update({x for x in A if any(y <= x for y in B)})
        A.update({x for x in B if not any(y <= x for y in A)})

    # Removes B from A
    @staticmethod
    def diff(A, B):
        A.difference_update({x for x in A if any(y <= x for y in B)})

    # Adds vector to basis
    @staticmethod
    def update(basis, vector):
        to_remove = set()

        if vector in basis:
            return

        for v in basis:
            if vector <= v:
                to_remove.add(v)
            elif v <= vector:
                return

        basis.add(vector)
        basis.difference_update(to_remove)
