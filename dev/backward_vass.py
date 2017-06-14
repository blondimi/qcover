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
import z3
from backward import backward_coverability
from cpn import add_firing_constraints
from petri_from_vass import PetriFromVass
from vass_smt import build_zvass_solver, set_configurations, set_configuration, forbid_upward

def _petrinet_marking_vars(vass, petrinet, variables):
    state_vars, vector_vars = variables
    marking_vars = [None] * petrinet.num_places()

    for state in vass.states():
        place = petrinet.state_place_num(state)
        marking_vars[place] = state_vars[state]

    for i in range(vass.dim()):
        place = petrinet.component_place_num(i)
        marking_vars[place] = vector_vars[i]

    return marking_vars

def _add_cpn_firing_constraints(vass, solver, variables):
    petrinet = PetriFromVass(vass)
    init_vars, target_vars, transitions_vars = variables

    init_marking_vars   = _petrinet_marking_vars(vass, petrinet, init_vars)
    target_marking_vars = _petrinet_marking_vars(vass, petrinet, target_vars)
    petri_transitions_vars = [None] * petrinet.num_transitions()

    for t in transitions_vars:
        num = petrinet.transition_num(t)
        petri_transitions_vars[num] = transitions_vars[t]

    add_firing_constraints(petrinet, init_marking_vars,
                           target_marking_vars, solver,
                           petri_transitions_vars)

def coverability(vass, init, targets):
    system = (vass, init, targets)

    solver, variables = build_zvass_solver(vass)
    init_vars, target_vars, _ = variables

    set_configuration(solver, init_vars, init)
    # _add_cpn_firing_constraints(vass, solver, variables)
    solver.check()

    # Precondition
    solver.push()
    set_configurations(solver, target_vars, targets, ">=")
    result = solver.check()
    solver.pop()

    if result == z3.unsat:
        return False

    # Pruning
    def z_pruning(configs):
        def pred(c):
            solver.push()
            set_configuration(solver, target_vars, c, ">=")
            result = solver.check()
            solver.pop()

            return result == z3.unsat

        pruned = {c for c in configs if pred(c)}
        
        for config in pruned:
            forbid_upward(solver, target_vars, config)

        return pruned

    return backward_coverability(system, z_pruning)
