from configuration import Configuration

class Marking(Configuration):
    def __init__(self, *entries):
        marking = []

        for x in entries:
            if any(isinstance(x, t) for t in [list, tuple, Marking]):
                marking.extend(x)
            else:
                marking.append(x)

        self._marking = tuple(marking)

    @staticmethod
    def zeros(length, value=0):
        return Marking([value] * length)

    @staticmethod
    def one(length, index, value=1):
        return Marking([0 if i != index else value for i in range(length)])

    def get_support(self):
        return {p for p in range(len(self._marking)) if self._marking[p] > 0}

    def sum_norm(self):
        return sum(self._marking)

    def __eq__(self, other):
        return self._marking == other._marking

    def __ne__(self, other):
        return self._marking != other._marking

    def __gt__(self, other):
        return other.__lt__(self)

    def __ge__(self, other):
        return other.__le__(self)

    def __lt__(self, other):
        strict = False

        for i in range(len(self._marking)):
            if self._marking[i] > other._marking[i]:
                return False
            elif self._marking[i] < other._marking[i]:
                strict = True

        return strict

    def __le__(self, other):
        return all(self._marking[i] <= other._marking[i]
                   for i in range(len(self._marking)))

    def __len__(self):
        return len(self._marking)

    def __getitem__(self, key):
        return self._marking[key]

    def __hash__(self):
        return hash(self._marking)

    def __repr__(self):
        return tuple.__repr__(self._marking)
    
    def __str__(self):
        return tuple.__str__(self._marking)

    def __add__(self, other):
        return Marking([self[i] + other[i] for i in range(len(self))])

    def __sub__(self, other):
        return Marking([self[i] - other[i] for i in range(len(self))])
