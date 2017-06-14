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
import copy
from marking import Marking

class PetriFromVass:
    def __init__(self, vass, copy_vass=False):
        self._vass = vass if not copy_vass else copy.deepcopy(vass)
        self._state_to_id      = {}
        self._transition_to_id = {}
        self._id_to_state      = {}
        self._id_to_transition = {}

        for i, p in enumerate(vass.states()):
            self._state_to_id[p] = i
            self._id_to_state[i] = p

        for i, t in enumerate(vass.transitions()):
            self._transition_to_id[t] = i
            self._id_to_transition[i] = t

    # Places = states then components
    def num_places(self):
        return self._vass.num_states() + self._vass.dim()

    def num_transitions(self):
        return self._vass.num_transitions()

    def state_place_num(self, state):
        return self._state_to_id[state]

    def component_place_num(self, component):
        return self._vass.num_states() + component

    def transition_num(self, transition):
        return self._transition_to_id[transition]

    def _is_state(self, place):
        return 0 <= place < self._vass.num_states()

    def get_pre(self, place, transition):
        trans = self._id_to_transition[transition]
        
        if self._is_state(place):
            state = self._id_to_state[place]

            if trans in self._vass.outgoing_transitions(state):
                return 1
            else:
                return 0
        else:
            component    = place - self._vass.num_states()
            _, update, _ = self._vass.transitions()[trans]

            value = update[component]

            return abs(value) if value < 0 else 0

    def get_post(self, place, transition):
        trans = self._id_to_transition[transition]
        
        if self._is_state(place):
            state = self._id_to_state[place]

            if trans in self._vass.ingoing_transitions(state):
                return 1
            else:
                return 0
        else:
            component    = place - self._vass.num_states()
            _, update, _ = self._vass.transitions()[trans]

            value = update[component]

            return value if value > 0 else 0

    def set_pre(self, place, transition, value):
        raise NotImplementedError()

    def set_post(self, place, transition, value):
        raise NotImplementedError()

    def successors(self, marking):
        raise NotImplementedError()

    def predecessors(self, marking):
        raise NotImplementedError()

    def predecessors_upward(self, marking):
        raise NotImplementedError()

    def freeze(self):
        pass

    def make_lossy(self, init=None):
        raise NotImplementedError()

    def _transition_effect(self, transition, reverse=False):
        trans = self._id_to_transition[transition]
        p, update, q = self._vass.transitions()[trans]

        if reverse:
            p, q = q, p

        p_place = self._state_to_id[p]
        q_place = self._state_to_id[q]

        left = [0] * self._vass.num_states()
        left[p_place] -= 1
        left[q_place] += 1

        return Marking(left + list(update))
        
    def fireable(self, marking, transition, reverse=False):
        effect = self._transition_effect(transition, reverse)

        return marking + effect >= Marking.zeros(self.num_places())

    def fire(self, marking, transition, reverse=False):
        effect = self._transition_effect(transition, reverse)

        return marking + effect

    def places_set(self, transitions, reverse=False, pre=True, post=True):
        places = set()
        
        for transition in transitions:
            trans = self._id_to_transition[transition]
            p, update, q = self._vass.transitions()[trans]

            if reverse:
                p, q = q, p

            if pre:  places.add(self._state_to_id[p])
            if post: places.add(self._state_to_id[q])

            for i in range(len(update)):
                neg, pos = update[i] < 0, update[i] > 0
                
                if reverse:
                    neg, pos = pos, neg

                if (pre and neg) or (post and pos):
                    places.add(self._vass.num_states() + i)

        return places

    def places_preset(self, transitions, reverse=False):
        return self.places_set(transitions, reverse, pre=True, post=False)

    def places_postset(self, transitions, reverse=False):
        return self.places_set(transitions, reverse, pre=False, post=True)

    def transitions_set(self, places, reverse=False, pre=True, post=True):
        transitions = set()

        for place in places:
            if self._is_state(place):
                state = self._id_to_state[place]
                ingoing  = self._vass.ingoing_transitions(state)
                outgoing = self._vass.outgoing_transitions(state)

                if reverse:
                    ingoing, outgoing = outgoing, ingoing

                if pre:
                    transitions.update({self._transition_to_id[t] for
                                        t in ingoing})
                if post:
                    transitions.update({self._transition_to_id[t] for
                                        t in outgoing})
            else:
               i = place - self._vass.num_states()

               for t in self._vass.transitions():
                   _, update, _ = self._vass.transitions()[t]
                   neg, pos = update[i] < 0, update[i] > 0
                   
                   if reverse:
                       neg, pos = pos, neg

                   if (pre and pos) or (post and neg):
                       transitions.add(self._transition_to_id[t])

        return transitions

    def transitions_preset(self, places, reverse=False):
        return self.transitions_set(places, reverse, pre=True, post=False)

    def transitions_postset(self, places, reverse=False):
        return self.transitions_set(places, reverse, pre=False, post=True)
