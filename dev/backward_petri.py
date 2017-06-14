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
import z3
from backward import backward_coverability
from cpn import reachable, build_cpn_solver
from marking import Marking
from petri_utils import omega_marking
from petri_smt import set_constrained_markings
from upward_sets import Upward

def check_q_coverability(petrinet, init, targets):
    petri_cover = copy.deepcopy(petrinet)
    petri_cover.make_lossy(init)

    _, init_marking = init

    has_unknown = False

    for target in targets:
        _, target_marking = target

        result = reachable(petri_cover, init_marking, target_marking)[0]

        if result is None:
            has_unknown = True
        elif result == True:
            return True
   
    return None if has_unknown else False

def check_q_coverability_z3(solver, target_vars, markings):
    solver.push()
    constrained_markings = [(tuple([">="] * len(m)), m) for m in markings]
    set_constrained_markings(solver, target_vars, constrained_markings)

    result = solver.check()
    solver.pop()

    if result == z3.sat:
        return True
    elif result == z3.unsat:
        return False
    else:
        return None

def q_coverable(petrinet, init, targets):
    MAX_TARGETS_SINGLE_TEST = 10

    if len(targets) <= MAX_TARGETS_SINGLE_TEST:
        if check_q_coverability(petrinet, init, targets) == True:
            return True
    else:
        solver, _ = build_cpn_solver(petrinet, init, targets, domain="N")
        
        if solver.check() == z3.sat:
            return True

    return False

def coverability(petrinet, init, targets):
    if q_coverable(petrinet, init, targets) is False:
        return False

    # System
    init_config    = omega_marking(init)
    target_configs = {m for _, m in targets}

    system = (petrinet, init_config, target_configs)

    # Pruning
    solver, variables = build_cpn_solver(petrinet, init, targets=None,
                                         domain="N")
    _, _, target_vars = variables

    def q_pruning(markings):
        def pred(m):
            return not check_q_coverability_z3(solver, target_vars, {m})

        pruned = {x for x in markings if pred(x)}

        for x in pruned:
            solver.add(z3.Or([target_vars[p] < x[p] for p in
                              range(len(x))]))

        return pruned

    # New candidates
    def smallest_markings(markings):
        sorted_markings = sorted(markings, key=lambda m: m.sum_norm())

        return set(sorted_markings[:int(10 + 0.2 * len(markings))])

    return backward_coverability(system, q_pruning, smallest_markings)
