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
from petri import load_petrinet, constraint_vector, petrinet_lossy
from cpn import reachable, build_cpn_solver
from solver_utils import set_markings_constrained
from upward_sets import update_upward, in_upward, merge_upward

def sum_norm(v):
    return sum(v)

def support_norm(v):
    return len([0 for x in v if x > 0])

# Add omegas to places that can take arbitrary values
def _omega_marking(cmp_marking):
    x = [0] * len(cmp_marking)

    for i in range(len(x)):
        comparison, value = cmp_marking[i]
        x[i] = value if comparison == '=' else float('inf')

    return tuple(x)

def pre_upward(petrinet, markings, precomputed=None, prune=True):
    pre_matrix, post_matrix = petrinet
    num_places, num_transitions = pre_matrix.shape
    basis = set()

    for m in markings:
        if precomputed is not None and m in precomputed:
            to_merge = {pre_m for pre_m in precomputed[m] if not
                        in_upward(pre_m, markings)}
            merge_upward(basis, to_merge)
            continue
        else:
            precomputed[m] = set()

        for t in range(num_transitions):
            pre_m = [0] * num_places

            for p in range(num_places):
                pre, post = int(pre_matrix[p, t]), int(post_matrix[p, t])
                pre_m[p] = max(pre, m[p] + pre - post)

            pre_m = tuple(pre_m)
            
            if precomputed is not None:
                update_upward(precomputed[m], pre_m)

            if not prune or not in_upward(pre_m, markings):
                update_upward(basis, pre_m)

    return basis

def check_cpn_coverability(petrinet, init, targets):
    petri_cover = petrinet_lossy(petrinet, init)
    init_marking = tuple(constraint_vector(init))

    has_unknown = False

    for target in targets:
        target_marking = tuple(constraint_vector(target))

        result = reachable(petri_cover, init_marking, target_marking)[0]

        if result is None:
            has_unknown = True
        elif result == True:
            return True

    return None if has_unknown else False

def check_cpn_coverability_z3(solver, target_vars, markings):
    solver.push()
    set_markings_constrained(solver, target_vars, [[('>=', p) for p in m] 
                                                   for m in markings])
    result = solver.check()
    solver.pop()

    if result == z3.sat:
        return True
    elif result == z3.unsat:
        return False
    else:
        return None

def non_coverable(petrinet, init, targets):
    MAX_TARGETS_SINGLE_TEST = 10

    if len(targets) <= MAX_TARGETS_SINGLE_TEST:
        if check_cpn_coverability(petrinet, init, targets) == False:
            return True
    else:
        solver, _ = build_cpn_solver(petrinet, init, targets, domain='N')
        
        if solver.check() == z3.unsat:
            return True

    return False

def coverability(petrinet, init, targets, prune=False, max_iter=None):
    # Verify if non coverable in CPN first
    if prune and non_coverable(petrinet, init, targets):
        return False

    # Otherwise, proceed with backward coverability
    def smallest_elems(x):
        return set(sorted(x, key=sum_norm)[:int(10 + 0.2 * len(x))])

    solver, variables = build_cpn_solver(petrinet, init, targets=None,
                                         domain='N')
    _, _, target_vars = variables

    def coverable(markings):
        return check_cpn_coverability_z3(solver, target_vars, markings)

    init_marking = _omega_marking(init)
    basis = {tuple(constraint_vector(m)) for m in targets}
    precomputed = {}
    covered = False
    num_iter = 0

    while not covered:
        if max_iter is not None and num_iter >= max_iter:
            return None # Unknown result
        else:
            num_iter += 1

        # Compute prebasis
        prebasis = pre_upward(petrinet, basis, precomputed)

        # Coverability pruning
        pruned = {x for x in prebasis if prune and not coverable([x])}
        prebasis.difference_update(pruned)

        for x in pruned:
            solver.add(z3.Or([target_vars[p] < x[p] for p in
                              range(len(x))]))

        # Continue?
        if len(prebasis) == 0:
            break
        else:
            prebasis = smallest_elems(prebasis)
            merge_upward(basis, prebasis)
            covered = in_upward(init_marking, basis)

    return covered
