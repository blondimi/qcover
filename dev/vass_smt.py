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
import smt_utils

def build_zvass_solver(vass):
    places_vars   = {p: z3.Int( "p_{}".format(p)) for p in vass.states()}
    flow_in_vars  = {p: z3.Int("fi_{}".format(p)) for p in vass.states()}
    flow_out_vars = {p: z3.Int("fo_{}".format(p)) for p in vass.states()}
    transitions_vars = {t: z3.Int( "t_{}".format(t)) for t in
                        vass.transitions()}
    init_state_vars   = {p: z3.Int("ip_{}".format(p)) for p in vass.states()}
    target_state_vars = {p: z3.Int("tp_{}".format(p)) for p in vass.states()}
    init_vec_vars   = [z3.Int("x_{}".format(d)) for d in range(vass.dim())]
    target_vec_vars = [z3.Int("y_{}".format(d)) for d in range(vass.dim())]

    solver = z3.Solver()

    # Non negative variables
    solver.add([places_vars[p]       >= 0 for p in vass.states()])
    solver.add([flow_in_vars[p]      >= 0 for p in vass.states()])
    solver.add([flow_out_vars[p]     >= 0 for p in vass.states()])
    solver.add([transitions_vars[t]  >= 0 for t in vass.transitions()])
    solver.add([init_state_vars[p]   >= 0 for p in vass.states()])
    solver.add([target_state_vars[p] >= 0 for p in vass.states()])

    # Unique initial/target state
    solver.add(z3.Sum([init_state_vars[p]   for p in init_state_vars])   == 1)
    solver.add(z3.Sum([target_state_vars[p] for p in target_state_vars]) == 1)

    for p in vass.states():
        in_var    = flow_in_vars[p]
        out_var   = flow_out_vars[p]

        # Consistent flow
        ingoing  = [transitions_vars[t] for t in vass.ingoing_transitions(p)]
        outgoing = [transitions_vars[t] for t in vass.outgoing_transitions(p)]

        if len(ingoing) > 0:
            solver.add(in_var == z3.Sum(ingoing))
        else:
            solver.add(in_var == z3.IntVal(0))

        if len(outgoing) > 0:
            solver.add(out_var == z3.Sum(outgoing))
        else:
            solver.add(out_var == z3.IntVal(0))

        solver.add(in_var  + init_state_vars[p] ==
                   out_var + target_state_vars[p])

        # Connected flow
        place_var = places_vars[p]

        solver.add(z3.Implies(in_var + out_var > 0, place_var > 0))
        solver.add(z3.Implies(place_var > 0, in_var + out_var > 0))

        # if p is initial and non trivial execution -> place_var = 1
        solver.add(z3.Implies(init_state_vars[p] == 1,
                              z3.If(in_var + out_var > 0,
                                    place_var == 1,
                                    place_var == 0)))

        # if p non initial and used -> predecessor numbered smaller
        solver.add(z3.Implies(z3.And(init_state_vars[p] == 0, place_var > 0),
                              z3.Or([z3.And(place_var > places_vars[q],
                                            places_vars[q] > 0) for q in
                                     vass.adjacent_in(p)])))

    # State equation
    transitions = vass.transitions()
    incidence = [[] for _ in range(vass.dim())]

    for t in transitions:
        _, update, _ = transitions[t]

        for d in range(vass.dim()):
            incidence[d].append(smt_utils.expression(update[d],
                                                     transitions_vars[t]))

    for d in range(vass.dim()):
        solver.add(init_vec_vars[d] + z3.Sum(incidence[d]) ==
                   target_vec_vars[d])

    return (solver,
            ((init_state_vars, init_vec_vars),
             (target_state_vars, target_vec_vars),
             transitions_vars))

def set_vectors(solver, variables, vectors, comparison="="):
    disjunct = []
    
    comparator = smt_utils.comparator(comparison)

    for vector in vectors:
        disjunct.append(z3.And([comparator(variables[d], vector[d]) for d in
                                range(len(variables))]))

    solver.add(z3.Or(disjunct))

def set_vector(solver, variables, vector, comparison="="):
    set_vectors(solver, variables, {vector}, comparison)

def set_states(solver, variables, states):
    solver.add(z3.Or([variables[p] == 1 for p in states]))

def set_state(solver, variables, state):
    set_states(solver, variables, {state})

def set_configurations(solver, variables, configs, comparison="="):
    disjunct = []
    state_vars, vec_vars = variables
    comparator = smt_utils.comparator(comparison)

    for config in configs:
        vec_constraint = z3.And([comparator(vec_vars[d], config.vector()[d])
                                 for d in range(len(vec_vars))])
        disjunct.append(z3.And(state_vars[config.state()] == 1,
                               vec_constraint))
                              
    solver.add(z3.Or(disjunct))

def set_configuration(solver, variables, config, comparison="="):
    set_configurations(solver, variables, {config}, comparison)


def forbid_upward(solver, variables, config):
    state_vars, vec_vars = variables
    
    solver.add(z3.Or(state_vars[config.state()] == 0,
                     z3.Or([vec_vars[d] < config.vector()[d]
                            for d in range(len(vec_vars))])))
