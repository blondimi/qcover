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
from marking import Marking
from upward_sets import Upward
from vass_configuration import VassConfig

class VASS:
    def __init__(self, dim, states=None, transitions=None):
        self._dim = dim
        self._states = states if states is not None else set()
        self._transitions     = {}
        self._fwd_transitions = {}
        self._bwd_transitions = {}

        if transitions is not None:
            for p in transitions:
                for (update, q) in transitions[p]:
                    self.add_transition(p, update, q)

    def dim(self):
        return self._dim

    def num_states(self):
        return len(self._states)

    def num_transitions(self):
        return len(self._transitions)

    def states(self):
        return self._states

    def transitions(self):
        return self._transitions

    def add_state(self, p):
        self._states.add(p)

    def outgoing_transitions(self, p):
        return set(self._fwd_transitions.get(p, set()))

    def ingoing_transitions(self, p):
        return set(self._bwd_transitions.get(p, set()))

    def adjacent_out(self, p):
        adj = set()

        for t in self._fwd_transitions.get(p, set()):
            _, _, q = self._transitions[t]

            adj.add(q)

        return adj

    def adjacent_in(self, p):
        adj = set()

        for t in self._bwd_transitions.get(p, set()):
            q, _, _ = self._transitions[t]

            adj.add(q)

        return adj

    def add_transition(self, p, update, q):
        if len(update) != self.dim():
            raise ValueError("Expected dimension: {}".format(self.dim()))

        name = "t" + str(self.num_transitions())

        self._transitions[name] = (p, Marking(update), q)

        succ = self._fwd_transitions.get(p, None)
        pred = self._bwd_transitions.get(q, None)

        if succ is not None:
            succ.add(name)
        else:
            self._fwd_transitions[p] = {name}

        if pred is not None:
            pred.add(name)
        else:
            self._bwd_transitions[q] = {name}

    def successors(self, config):
        succ = set()

        for t in self._fwd_transitions.get(config.state(), set()):
            _, update, q = self._transitions[t]
            new_vector = config.vector() + update

            if new_vector >= Marking.zeros(len(update)):
                succ.add(VassConfig(q, new_vector))
        
        return succ

    def predecessors(self, config):
        pred = set()

        for t in self._bwd_transitions.get(config.state(), set()):
            p, update, _ = self._transitions[t]
            new_vector = config.vector() - update

            if new_vector >= Marking.zeros(len(update)):
                pred.add(VassConfig(p, new_vector))
        
        return pred

    def predecessors_upward(self, config):
        pred = set()

        for t in self._bwd_transitions.get(config.state(), set()):
            p, update, _ = self._transitions[t]
            pre_vector = []

            for i in range(len(update)):
                pre_vector.append(max(0, config.vector()[i] - update[i]))

            Upward.update(pred, VassConfig(p, Marking(pre_vector)))

        return pred

    def take_transition(self, config, transition):
        p, update, q = self._transitions[transition]

        if config.state() != p:
            return None
        else:
            new_vector = config.vector() + update
            
            if new_vector >= Marking.zeros(self.dim()):
                return VassConfig(q, new_vector)
            else:
                return None

    def adjacency_list(self):
        adj = {}

        for p in self.states():
            adj[p] = list(self.adjacent_out(p))

        return adj
