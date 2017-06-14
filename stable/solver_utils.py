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
from fractions import Fraction
import numpy as np
import z3
import config
from petri import places_set, places_preset, places_postset, transitions_preset, transitions_postset, constraint_vector

DOMAINS = {'R': z3.Real, 'N': z3.Int}

def _expression(coeff, var):
    if coeff == 1:
        return var
    elif coeff == -1:
        return -var
    elif coeff != 0:
        return coeff * var
    else:
        return 0

unique_tag = 0

def _add_firing_constraints_places(petrinet, marking, solver,
                                   variables, backward=False):
    num_places, num_transitions = petrinet[0].shape
    tag = 'bl' if backward else 'fl'

    global unique_tag
    places_variables = [z3.Int('{}_{}_{}'.format(tag, unique_tag, p))
                        for p in range(num_places)]
    unique_tag += 1
    
    for p in range(num_places):
        var = places_variables[p]
        preset = transitions_preset(petrinet, {p}, reverse=backward)
        constraints = []

        for t in preset:
            t_preset = places_preset(petrinet, {t}, reverse=backward)

            constraint = z3.And(variables[t] > 0,
                                z3.And([z3.And(places_variables[q] > 0,
                                               var > places_variables[q])
                                        for q in t_preset]))
            constraints.append(constraint)

        solver.add(z3.Implies(marking[p] >  0, var == 1))
        solver.add(z3.Implies(marking[p] == 0, z3.Implies(var > 0,
                                                   z3.Or(constraints))))
    
    for t in range(num_transitions):
        places = places_set(petrinet, {t}, pre=True, post=True,
                            reverse=backward)

        places_reachable = z3.And([places_variables[p] > 0 for p in
                                   places])
        
        solver.add(z3.Implies(variables[t] > 0, places_reachable))

def add_firing_constraints(petrinet, init_marking, target_marking,
                           solver, variables):
    _add_firing_constraints_places(petrinet, init_marking, solver,
                                   variables)
    _add_firing_constraints_places(petrinet, target_marking, solver,
                                   variables, backward=True)

def incidence_sums(petrinet, variables, subnet_transitions='all',
                   reverse=False):
    pre_matrix, post_matrix = petrinet
    num_places, num_transitions = pre_matrix.shape

    if subnet_transitions == 'all':
        subnet_transitions = set(range(num_transitions))

    if reverse:
        pre_matrix, post_matrix = post_matrix, pre_matrix

    sums = []

    for p in range(num_places):
        if config.representation_mode == config.DENSE:
            nonzero = np.union1d(pre_matrix[p].getA1().nonzero()[0],
                                 post_matrix[p].getA1().nonzero()[0])
        elif config.representation_mode == config.SPARSE:
            nonzero = np.union1d(pre_matrix.getrow(p).nonzero()[1],
                                 post_matrix.getrow(p).nonzero()[1])

        incidence_row = [(post_matrix[p, t] - pre_matrix[p, t],
                          variables[t]) for t in nonzero if t in
                         subnet_transitions]
 
        sum_elements = [_expression(coeff, var) for coeff,
                        var in incidence_row if coeff != 0]

        curr_sum = z3.Sum(sum_elements) if len(sum_elements) > 0 else z3.IntVal(0)

        sums.append(curr_sum)

    return sums

def _build_solver(petrinet, init_marking, target_marking, domain='R',
                  subnet_transitions='all'):
    pre_matrix, post_matrix = petrinet
    num_places, num_transitions = pre_matrix.shape

    if subnet_transitions == 'all':
        subnet_transitions = set(range(num_transitions))

    # Instantiate solver
    solver = z3.Solver()
    variables = [DOMAINS[domain]('t_{}'.format(t)) for t in
                 range(num_transitions)]

    solver.add([variables[i] >= 0 for i in range(num_transitions) if i
                in subnet_transitions])

    solver.add([variables[i] == 0 for i in range(num_transitions) if i
                not in subnet_transitions])

    sums = incidence_sums(petrinet, variables, subnet_transitions)
    
    for p in range(num_places):
        solver.add(init_marking[p] + sums[p] == target_marking[p])

    return solver, variables

def build_solver(petrinet, init_marking, target_marking, domain='R',
                 subnet_transitions='all'):
    return _build_solver(petrinet, init_marking, target_marking,
                         domain, subnet_transitions)
        
def build_solver_nomarking(petrinet, domain='R',
                           subnet_transitions='all'):
    num_places = petrinet[0].shape[0]
    init = [DOMAINS[domain]('m0_{}'.format(t)) for t in
            range(num_places)]
    target = [DOMAINS[domain]('m_{}'.format(t)) for t in
              range(num_places)]

    solver, variables = _build_solver(petrinet, init, target, domain,
                                      subnet_transitions)

    solver.add([var >= 0 for var in init])
    solver.add([var >= 0 for var in target])

    return solver, (variables, init, target)

def get_solution(solver, variables, domain='R', subnet_transitions='all'):
    model = solver.model()

    if subnet_transitions == 'all':
        subnet_transitions = set(range(len(variables)))

    solution = [0] * len(variables)

    if domain == 'R':
        for t in range(len(variables)):
            if t in subnet_transitions:
                var = variables[t]
                solution[t] = Fraction(model[var].numerator_as_long(),
                                       model[var].denominator_as_long())
            else:
                solution[t] = Fraction(0, 1)
    elif domain == 'N':
        for t in range(len(variables)):
            if t in subnet_transitions:
                solution[t] = model[variables[t]].as_long()
            else:
                solution[t] = 0
    else:
        raise ValueError('{} is not a valid domain'.format(domain))

    return solution

def set_markings(solver, variables, markings):
    solver.add(z3.Or([z3.And(variables[p] == m[p] for p in
                             range(len(variables))) for m in
                      markings]))

def set_marking(solver, variables, marking):
    set_markings(solver, variables, [marking])

def set_markings_constrained(solver, variables, constrained_markings):
    disjunct = []

    for c in constrained_markings:
        marking = constraint_vector(c)

        conjunct = []

        for i in range(len(c)):
            comparison = c[i][0]

            if comparison == '=':
                conjunct.append(variables[i] == marking[i])
            elif comparison == '>=':
                conjunct.append(variables[i] >= marking[i])
            elif comparison == '<=':
                conjunct.append(variables[i] <= marking[i])
            else:
                raise ValueError('Comparison not supported.')

        disjunct.append(z3.And(conjunct))

    solver.add(z3.Or(disjunct))

def set_marking_constrained(solver, variables, constrained_marking):
    set_markings_constrained(solver, variables, [constrained_marking])
