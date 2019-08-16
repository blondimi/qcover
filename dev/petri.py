# Copyright 2017 Michael Blondin, Alain Finkel, Christoph Haase, Serge Haddad

# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at

#     http://www.apache.org/licenses/LICENSE-2.0

# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.
import numpy as np
import numpy.matlib
from scipy.sparse import lil_matrix, csr_matrix
from marking import Marking
from upward_sets import Upward

class Petri:
    # Matrix representation modes (constants)
    DENSE  = "dense"
    SPARSE = "sparse"

    def __init__(self, num_places=0, num_transitions=0, mode=None,
                 precision=np.int8):
        if mode is None:
            mode = Petri.DENSE

        if mode == Petri.DENSE or mode is None:
            matrix_type = np.matlib.zeros
        elif mode == Petri.SPARSE:
            matrix_type = lil_matrix
        else:
            raise ValueError("Unsupported mode: {}".format(mode))

        self._repr_mode = mode
        self._pre_matrix  = matrix_type((num_places, num_transitions),
                                        dtype=precision)
        self._post_matrix = matrix_type((num_places, num_transitions),
                                        dtype=precision)
        self._precision = precision

    def num_places(self):
        return self._pre_matrix.shape[0]

    def num_transitions(self):
        return self._pre_matrix.shape[1]

    def get_pre(self, place, transition):
        return self._pre_matrix[place, transition].item()

    def get_post(self, place, transition):
        return self._post_matrix[place, transition].item()

    def set_pre(self, place, transition, value):
        self._pre_matrix[place, transition] = value

    def set_post(self, place, transition, value):
        self._post_matrix[place, transition] = value

    def successors(self, marking):
        succ = set()

        for t in range(self.num_transitions()):
            if self.fireable(marking, t):
                succ.add(self.fire(marking, t))

        return succ

    def predecessors(self, marking):
        succ = set()

        for t in range(self.num_transitions()):
            if self.fireable(marking, t, reverse=True):
                succ.add(self.fire(marking, t, reverse=True))

        return succ

    def predecessors_upward(self, marking):
        pred = set()

        for t in range(self.num_transitions()):
            pre_marking = [0] * self.num_places()

            for p in range(self.num_places()):
                pre, post = self.get_pre(p, t), self.get_post(p, t)
                pre_marking[p] = max(pre, marking[p] + pre - post)

            Upward.update(pred, Marking(pre_marking))

        return pred

    def freeze(self):
        if self._repr_mode == Petri.SPARSE:
            self._pre_matrix  = csr_matrix(self._pre_matrix)
            self._post_matrix = csr_matrix(self._post_matrix)

    def _coverability_matrix(self, constrained_marking, marking_type):
        comparisons, marking = constrained_marking

        to_cover = [i for (i, c) in enumerate(comparisons) if c == ">="]

        if self._repr_mode == Petri.DENSE:
            matrix_type = np.matlib.zeros
        elif self._repr_mode == Petri.SPARSE:
            matrix_type = lil_matrix

        pre_matrix  = matrix_type((len(marking), len(to_cover)),
                                  dtype=self._precision)
        post_matrix = matrix_type((len(marking), len(to_cover)),
                                  dtype=self._precision)

        for t in range(len(to_cover)):
            if marking_type == "init":
                post_matrix[to_cover[t], t] = 1
            elif marking_type == "target":
                pre_matrix[to_cover[t], t] = 1
                
        if self._repr_mode == Petri.SPARSE:
            pre_matrix  = csr_matrix(pre_matrix)
            post_matrix = csr_matrix(post_matrix)
        
        return (pre_matrix, post_matrix)

    def _embed_coverability(self, init, target):
        pre_init,   post_init   = self._coverability_matrix(init, "init")
        pre_target, post_target = self._coverability_matrix(target, "target")

        if self._repr_mode == Petri.DENSE:
            stack_func = np.hstack
        elif self._repr_mode == Petri.SPARSE:
            stack_func = lambda m: hstack(m, format="csr")
            
        pre_matrix  = stack_func([m for m in [self._pre_matrix, pre_init,
                                              pre_target] if m.shape[1] > 0])
        post_matrix = stack_func([m for m in [self._post_matrix, post_init,
                                              post_target] if m.shape[1] > 0])

        self._pre_matrix  = pre_matrix
        self._post_matrix = post_matrix

    def make_lossy(self, init=None):
        if init is None:
            init = (tuple(["="] * self.num_places()),
                    Marking([0] * self.num_places()))

        target = (tuple([">="] * self.num_places()),
                  Marking([0] * self.num_places()))

        self._embed_coverability(init, target)

    def fireable(self, marking, transition, reverse=False):
        matrix = self._pre_matrix if not reverse else self._post_matrix

        if self._repr_mode == Petri.DENSE:
            column = matrix[:,transition].getA1()
        elif self._repr_mode == Petri.SPARSE:
            column = matrix.getcol(transition).toarray().flatten()

        return all(marking[i] >= column[i] for i in range(len(marking)))

    def fire(self, marking, transition, reverse=False):
        pre_matrix, post_matrix = self._pre_matrix, self._post_matrix
        
        if reverse:
            pre_matrix, post_matrix = post_matrix, pre_matrix
        
        if self._repr_mode == Petri.DENSE:
            pre_col  = pre_matrix[:,transition].getA1()
            post_col = post_matrix[:,transition].getA1()
        elif self._repr_mode == Petri.SPARSE:
            pre_col  = pre_matrix.getcol(transition).toarray().flatten()
            post_col = post_matrix.getcol(transition).toarray().flatten()

        effect = (pre_col + post_col).tolist()

        return Marking([marking[i] + effect[i] for i in range(len(marking))])

    def places_set(self, transitions, reverse=False, pre=True, post=True):
        places = set()

        if reverse:
            pre, post = post, pre

        if pre:
            if self._repr_mode == Petri.DENSE:
                subnet = self._pre_matrix.take(list(transitions), axis=1)
                places |= set(np.ravel(subnet.nonzero()[0]))
            elif self._repr_mode == Petri.SPARSE:
                for t in transitions:
                    places |= set(self._pre_matrix.getcol(t).nonzero()[0])

        if post:
            if self._repr_mode == Petri.DENSE:
                subnet = self._post_matrix.take(list(transitions), axis=1)
                places |= set(np.ravel(subnet.nonzero()[0]))
            elif self._repr_mode == Petri.SPARSE:
                for t in transitions:
                    places |= set(self._post_matrix.getcol(t).nonzero()[0])

        return places

    def places_preset(self, transitions, reverse=False):
        return self.places_set(transitions, reverse, pre=True, post=False)

    def places_postset(self, transitions, reverse=False):
        return self.places_set(transitions, reverse, pre=False, post=True)

    def transitions_set(self, places, reverse=False, pre=True, post=True):
        transitions = set()

        if reverse:
            pre, post = post, pre

        if pre:
            if self._repr_mode == Petri.DENSE:
                subnet = self._post_matrix.take(list(places), axis=0)        
                transitions |= set(np.ravel(subnet.nonzero()[1]))
            elif self._repr_mode == Petri.SPARSE:
                for p in places:
                    transitions |= set(self._post_matrix.getrow(p).nonzero()[1])

        if post:
            if self._repr_mode == Petri.DENSE:
                subnet = self._pre_matrix.take(list(places), axis=0)
                transitions |= set(np.ravel(subnet.nonzero()[1]))
            elif self._repr_mode == Petri.SPARSE:
                for p in places:
                    transitions |= set(self._pre_matrix.getrow(p).nonzero()[1])

        return transitions

    def transitions_preset(self, places, reverse=False):
        return self.transitions_set(places, reverse, pre=True, post=False)

    def transitions_postset(self, places, reverse=False):
        return self.transitions_set(places, reverse, pre=False, post=True)
