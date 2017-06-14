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
import re
import numpy as np
import numpy.matlib
from scipy.sparse import lil_matrix, hstack
import config

def add_constraints(data, places_indices, constraints_list):
    COMPARISONS = ['>=', '=']  # List order matters here.
    entries = data.split(',')
    
    # Parse constraints
    for rule in entries:
        for comparison in COMPARISONS:
            if comparison in rule:
                place, value = rule.strip().split(comparison)
                place = place.strip()
                value = int(value)

                constraints_list[places_indices[place]] = (comparison,
                                                           value)

                break # Important, '=' appears in '>=' so would parse twice

    # Return trailing incomplete constraint
    if len([comp for comp in COMPARISONS if comp in entries[-1]]) == 0:
        return entries[-1]
    else:
        return ''

def add_transition(petrinet, places, transition, rule):
    pre_matrix, post_matrix = petrinet
    pos = rule.find('->')
    guards_str  = rule[:pos]
    updates_str = rule[pos+2:]
    guards  = {}
    updates = {}
    
    # Parse guards
    for guard in guards_str.split(','):
        var, value = guard.split('>=')

        guards[var.strip()] = int(value)

    # Parse updates
    for update in updates_str.split(','):
        match = re.search('\s*(.*)\'\s*=\s*(.*)\s*(\+|-)\s*(.*)\s*',
                          update) # xi' = xj {+,-} value
        
        if match is not None:
            var_in  = match.group(1).strip()
            var_out = match.group(2).strip()
            value   = int(match.group(3) + match.group(4))

            if var_in != var_out:
                raise ValueError('x_i\' = x_j + c illegal with i != j')

            updates[var_in] = value

    # Add transition
    for p in range(len(places)):
        guard  = guards[places[p]]  if places[p] in guards  else 0
        update = updates[places[p]] if places[p] in updates else 0

        if update >= 0:
            pre, post = guard, guard + update
        elif update < 0:
            pre, post = max(guard, -update), max(0, guard + update)

        # Add value to sparse matrix if necessary
        if pre != 0:
            pre_matrix[p, transition] = pre

        if post != 0:
            post_matrix[p, transition] = post

def load_petrinet(filename):
    MODES = ['vars', 'rules', 'init', 'target', 'invariants']

    places  = []
    init    = []
    targets = []

    pre_matrix, post_matrix = None, None
    places_indices  = []
    num_transitions = 0

    # Precompute number of transitions
    with open(filename) as input_file:
        for row in input_file:
            if ';' in row:
                num_transitions += 1
    
    # Load data
    with open(filename) as input_file:
        mode      = 'none'
        rules_acc = ''
        acc       = ''
        curr_transition = 0

        for row in input_file:
            data = row.strip()

            # Ignore empty/commented lines
            if len(data) == 0 or data[0] == '#':
                continue

            # Mode detection
            if data in MODES:
                mode = data

                # Allocate matrix for the Petri net, and places
                if mode == MODES[1]:
                    if config.representation_mode == config.DENSE:
                        matrix_type = np.matlib.zeros
                    elif config.representation_mode == config.SPARSE:
                        matrix_type = lil_matrix

                    pre_matrix = matrix_type((len(places),
                                              num_transitions),
                                             dtype=config.precision)
                    post_matrix = matrix_type((len(places),
                                               num_transitions),
                                              dtype=config.precision)
                    init = [('>=', 0)] * len(places)
                    places_indices = {value: key for key, value in
                                      enumerate(places)}
            else:
                # Places
                if mode == MODES[0]:
                    places.extend(data.split(' '))
                # Rules
                elif mode == MODES[1]:
                    rules_acc += data
                    pos = rules_acc.find(';')

                    if pos >= 0:
                        add_transition((pre_matrix, post_matrix),
                                       places, curr_transition,
                                       rules_acc[:pos])
                        curr_transition += 1
                        rules_acc = rules_acc[pos+1:]
                # Initial values
                elif mode == MODES[2]:
                    acc = add_constraints(acc + data, places_indices, init)
                # Target values
                elif mode == MODES[3]:
                    new_target = [('>=', 0)] * len(places)
                    trailing = add_constraints(data, places_indices,
                                               new_target) 
                    targets.append(new_target)
                   
                    if len(trailing.strip()) > 0:
                        raise ValueError('Incomplete target constraint.')
                # # Invariants (not supported)
                # #elif mode == MODES[4]:
                # #

    # Finish rules parsing (if necessary)
    while True:
        pos = rules_acc.find(';')

        if pos >= 0:
            add_transition((pre_matrix, post_matrix), places,
                           curr_transition, rules_acc[:pos])
            curr_transition += 1
            rules_acc = rules_acc[pos+1:]
        else:
            break

    if config.representation_mode == config.SPARSE:
        pre_matrix  = config.sparse_matrix(pre_matrix)
        post_matrix = config.sparse_matrix(post_matrix)
    
    return ((pre_matrix, post_matrix), init, targets)

def _coverability_matrix(constraints, mode):
    to_cover = [index for index, (comparison, _) in
                enumerate(constraints) if comparison == '>=']

    if config.representation_mode == config.DENSE:
        matrix_type = np.matlib.zeros
    elif config.representation_mode == config.SPARSE:
        matrix_type = lil_matrix

    pre_matrix  = matrix_type((len(constraints), len(to_cover)),
                              dtype=config.precision)
    post_matrix = matrix_type((len(constraints), len(to_cover)),
                              dtype=config.precision)

    for t in range(len(to_cover)):
        if mode == 'init':
            post_matrix[to_cover[t], t] = 1
        elif mode == 'target':
            pre_matrix[to_cover[t], t] = 1

    if config.representation_mode == config.SPARSE:
        pre_matrix  = config.sparse_matrix(pre_matrix)
        post_matrix = config.sparse_matrix(post_matrix)
        
    return (pre_matrix, post_matrix)

def constraint_vector(constraint):
    return [value for (_, value) in constraint]

def petrinet_coverability(petrinet, init, target):
    pre_matrix, post_matrix = petrinet
    pre_init,   post_init   = _coverability_matrix(init, 'init')
    pre_target, post_target = _coverability_matrix(target, 'target')

    if config.representation_mode == config.DENSE:
        stack_func = np.hstack
    elif config.representation_mode == config.SPARSE:
        stack_func = lambda m: hstack(m, format=config.sparse_type)

    pre = stack_func([m for m in [pre_matrix, pre_init, pre_target] if
                      m.shape[1] > 0])
    post = stack_func([m for m in [post_matrix, post_init, post_target] if
                       m.shape[1] > 0])

    return (pre, post)

def petrinet_lossy(petrinet, init=None):
    num_places = petrinet[0].shape[0]

    if init == None:
        init = [('=', 0)] * num_places

    return petrinet_coverability(petrinet, init, [('>=', 0)] * num_places)

def fireable(petrinet, marking, transition):
    if config.representation_mode == config.DENSE:
        column = petrinet[0][:,transition].getA1()
    elif config.representation_mode == config.SPARSE:
        column = petrinet[0].getcol(transition).toarray().flatten()

    new_marking = marking - column
        
    return all([value >= 0 for value in new_marking])

def fire(petrinet, marking, transition):
    if config.representation_mode == config.DENSE:
        pre_column  = petrinet[0][:,transition].getA1()
        post_column = petrinet[1][:,transition].getA1()
    elif config.representation_mode == config.SPARSE:
        pre_column  = petrinet[0].getcol(transition).toarray().flatten()
        post_column = petrinet[1].getcol(transition).toarray().flatten()

    return (marking - pre_column + post_column).tolist()

def places_set(petrinet, transitions, reverse=False, pre=False, post=False):
    pre_matrix, post_matrix = petrinet
    places = set()

    if reverse:
        pre, post = post, pre

    if pre:
        if config.representation_mode == config.DENSE:
            subnet = pre_matrix.take(list(transitions), axis=1)
            places = places | set(subnet.nonzero()[0].getA1())
        elif config.representation_mode == config.SPARSE:
            for t in transitions:
                places = places | set(pre_matrix.getcol(t).nonzero()[0])

    if post:
        if config.representation_mode == config.DENSE:
            subnet = post_matrix.take(list(transitions), axis=1)
            places = places | set(subnet.nonzero()[0].getA1())
        elif config.representation_mode == config.SPARSE:
            for t in transitions:
                places = places | set(post_matrix.getcol(t).nonzero()[0])

    return places

def places_preset(petrinet, transitions, reverse=False):
    return places_set(petrinet, transitions, reverse, pre=True)

def places_postset(petrinet, transitions, reverse=False):
    return places_set(petrinet, transitions, reverse, post=True)

def transitions_set(petrinet, places, reverse=False, pre=False, post=False):
    pre_matrix, post_matrix = petrinet
    transitions = set()

    if reverse:
        pre, post = post, pre

    if pre:
        if config.representation_mode == config.DENSE:
            subnet      = post_matrix.take(list(places), axis=0)
            transitions = transitions | set(subnet.nonzero()[1].getA1())
        elif config.representation_mode == config.SPARSE:
            for p in places:
                transitions |= set(post_matrix.getrow(p).nonzero()[1])

    if post:
        if config.representation_mode == config.DENSE:
            subnet      = pre_matrix.take(list(places), axis=0)
            transitions = transitions | set(subnet.nonzero()[1].getA1())
        elif config.representation_mode == config.SPARSE:
            for p in places:
                transitions |= set(pre_matrix.getrow(p).nonzero()[1])

    return transitions

def transitions_preset(petrinet, places, reverse=False):
    return transitions_set(petrinet, places, reverse, pre=True)

def transitions_postset(petrinet, places, reverse=False):
    return transitions_set(petrinet, places, reverse, post=True)

def get_support(marking):
    return {p for p in range(len(marking)) if marking[p] > 0}
