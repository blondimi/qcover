from configuration import Configuration
from marking import Marking

class VassConfig(Configuration):
    def __init__(self, *entries):
        marking = []
        
        for x in entries[1:]:
            if any(isinstance(x, t) for t in [list, tuple, Marking]):
                marking.extend(x)
            else:
                marking.append(x)

        self._state   = entries[0]
        self._marking = Marking(marking)

    def state(self):
        return self._state

    def vector(self):
        return self._marking

    def __eq__(self, other):
        return (self._state == other._state) and (self._marking ==
                                                  other._marking)

    def __ne__(self, other):
        return (self._state != other._state) or (self._marking !=
                                                 other._marking)

    def __gt__(self, other):
        return (self._state == other._state) and (self._marking >
                                                  other._marking)
    def __ge__(self, other):
        return (self._state == other._state) and (self._marking >=
                                                  other._marking)

    def __lt__(self, other):
        return (self._state == other._state) and (self._marking <
                                                  other._marking)

    def __le__(self, other):
        return (self._state == other._state) and (self._marking <=
                                                  other._marking)

    def __hash__(self):
        return hash((self._state, self._marking))

    def __repr__(self):
        return str(self._state) + Marking.__repr__(self._marking)
    
    def __str__(self):
        return str(self._state) + Marking.__str__(self._marking)
