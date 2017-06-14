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
import z3
from smt_utils import expression

DOMAINS = {"R": z3.Real, "N": z3.Int}

def incidence_sums(petrinet, variables, subnet_transitions="all",
                   reverse=False):
    if subnet_transitions == "all":
        subnet_transitions = set(range(petrinet.num_transitions))

    sums = []

    for p in range(petrinet.num_places()):
        nonzero = petrinet.transitions_set({p}, reverse)
        incidence_row = [(petrinet.get_post(p, t) - petrinet.get_pre(p, t),
                          variables[t]) for t in nonzero if t in
                         subnet_transitions]

        sum_elements = [expression(coeff, var) for coeff, var in
                        incidence_row if coeff != 0]

        curr_sum = z3.Sum(sum_elements) if len(sum_elements) > 0 else z3.IntVal(0)

        sums.append(curr_sum)

    return sums

def _build_solver(petrinet, init_marking, target_marking, domain="R",
                  subnet_transitions="all"):
    if subnet_transitions == "all":
        subnet_transitions = set(range(petrinet.num_transitions()))

    # Instantiate solver
    solver = z3.Solver()
    variables = [DOMAINS[domain]("tr_{}".format(t)) for t in
                 range(petrinet.num_transitions())]

    solver.add([variables[i] >= 0 for i in range(petrinet.num_transitions())
                if i in subnet_transitions])
    solver.add([variables[i] == 0 for i in range(petrinet.num_transitions())
                if i not in subnet_transitions])

    sums = incidence_sums(petrinet, variables, subnet_transitions)
    
    for p in range(petrinet.num_places()):
        solver.add(init_marking[p] + sums[p] == target_marking[p])

    return solver, variables

def build_solver(petrinet, init_marking, target_marking, domain="R",
                 subnet_transitions="all"):
    return _build_solver(petrinet, init_marking, target_marking,
                         domain, subnet_transitions)
        
def build_solver_nomarking(petrinet, domain="R", subnet_transitions="all"):
    init = [DOMAINS[domain]("m0_{}".format(t)) for t in
            range(petrinet.num_places())]
    target = [DOMAINS[domain]("m_{}".format(t)) for t in
              range(petrinet.num_places())]

    solver, variables = _build_solver(petrinet, init, target, domain,
                                      subnet_transitions)

    solver.add([var >= 0 for var in init])
    solver.add([var >= 0 for var in target])

    return solver, (variables, init, target)

def get_solution(solver, variables, domain="R", subnet_transitions="all"):
    model = solver.model()

    if subnet_transitions == "all":
        subnet_transitions = set(range(len(variables)))

    solution = [0] * len(variables)

    if domain == "R":
        for t in range(len(variables)):
            if t in subnet_transitions:
                var = variables[t]
                solution[t] = Fraction(model[var].numerator_as_long(),
                                       model[var].denominator_as_long())
            else:
                solution[t] = Fraction(0, 1)
    elif domain == "N":
        for t in range(len(variables)):
            if t in subnet_transitions:
                solution[t] = model[variables[t]].as_long()
            else:
                solution[t] = 0
    else:
        raise ValueError("{} is not a valid domain".format(domain))

    return tuple(solution)

def set_markings(solver, variables, markings):
    solver.add(z3.Or([z3.And(variables[p] == m[p] for p in
                             range(len(variables))) for m in
                      markings]))

def set_marking(solver, variables, marking):
    set_markings(solver, variables, [marking])

def set_constrained_markings(solver, variables, constrained_markings):
    disjunct = []

    for c in constrained_markings:
        comparisons, marking = c
        conjunct = []

        for i in range(len(marking)):
            if comparisons[i] == "=":
                conjunct.append(variables[i] == marking[i])
            elif comparisons[i] == ">=":
                conjunct.append(variables[i] >= marking[i])
            else:
                raise ValueError("Comparison not supported.")

        disjunct.append(z3.And(conjunct))

    solver.add(z3.Or(disjunct))

def set_constrained_marking(solver, variables, constrained_marking):
    set_constrained_markings(solver, variables, [constrained_marking])
