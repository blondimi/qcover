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
import multiprocessing
import z3
import config
from petri import places_set, get_support
from solver_utils import build_solver, build_solver_nomarking, set_marking_constrained, set_markings_constrained, add_firing_constraints

def _check_strict(solver, context, variables_global, queue_in, queue_out):
    while True:
        var = queue_in.get()

        if var is None:
            break
        else:
            solver.push()
            solver.add(variables_global[var].translate(context) > 0)

            if solver.check() == z3.sat:
                queue_out.put(var)
            else:
                queue_out.put(None)

            solver.pop()

def _max_support_parallel(solver, variables, transitions,
                          num_processes=multiprocessing.cpu_count()):
    contexts = [z3.Context() for _ in range(num_processes)]
    solvers  = [z3.Solver(ctx=c) for c in contexts]
    
    for i in range(num_processes):
        solvers[i].add(solver.assertions().translate(contexts[i]))

    # Instantiate processes
    queue_in  = multiprocessing.Queue(1)
    queue_out = multiprocessing.Queue()
    processes = [multiprocessing.Process(target=_check_strict, 
                                         args=(solvers[i], contexts[i],
                                               variables,
                                               queue_in, queue_out))
                 for i in range(num_processes)]

    # Start processes
    for proc in processes:
        proc.daemon = True
        proc.start()

    # Send data to processes
    for t in transitions:
        queue_in.put(t)

    for _ in range(num_processes):
        queue_in.put(None)

    # Retrieve results
    support = {queue_out.get() for _ in range(len(transitions))} - {None}

    # Terminate processes
    for p in processes:
        p.join()

    return support

def max_support(solver, variables, transitions, parallel=False):
    if parallel:
        support = _max_support_parallel(solver, variables, transitions)
    else:
        support = set()

        for t in transitions:
            solver.push()
            solver.add(variables[t] > 0)
            
            if solver.check() == z3.sat:
                support.add(t)

            solver.pop()

    return support
    
def max_firingset(petrinet, marking, transitions, reverse=False):
    transitions_subset = set()

    places = places_set(petrinet, transitions, reverse, pre=True,
                        post=True)
    places_subset = places & get_support(marking)

    while len(transitions_subset) < len(transitions):
        new = False

        for t in transitions - transitions_subset:
            preset = places_set(petrinet, {t}, reverse, pre=True)

            if preset <= places_subset:
                postset = places_set(petrinet, {t}, reverse, post=True)
                transitions_subset = transitions_subset | {t}
                places_subset = places_subset | postset
                new = True

        if not new:
            break

    return transitions_subset

def reachable(petrinet, init_marking, target_marking, limreach=False):
    _, num_transitions = petrinet[0].shape
    
    # if initial marking = target marking return trivial solution
    if init_marking == target_marking:
        return (True, set())

    transitions = set(range(num_transitions))
    solver, variables = build_solver(petrinet, init_marking,
                                     target_marking, domain='R')
    # Algorithm main loop
    while len(transitions) > 0:
        support = set()

        # Verify state equation first
        result = solver.check()

        if result == z3.unsat:
            return (False, None)
        elif result == z3.unknown:
            return (None, None)
        
        # Build maximal support
        support = max_support(solver, variables, transitions,
                              parallel=config.parallel)

        # Constrain maximal support with forward/backward firing sets
        prev_transitions = transitions.copy()
        transitions = support.copy()
        transitions = max_firingset(petrinet, init_marking, transitions)

        if not limreach:
            transitions = max_firingset(petrinet, target_marking,
                                        transitions, reverse=True)

        # If support unchanged return solution, else solve for new subnet
        if len(transitions) == len(prev_transitions):
            return (True, transitions)
        else:
            solver, variables = build_solver(petrinet, init_marking,
                                             target_marking,
                                             domain='R',
                                             subnet_transitions=transitions)

    return (False, None)

def build_cpn_solver(petrinet, init=None, targets=None, domain='R'):
    solver, variables = build_solver_nomarking(petrinet, domain)
    transitions_vars, init_vars, target_vars = variables

    # Set initial and target markings
    if init is not None:
        set_marking_constrained(solver, init_vars, init)

    if targets is not None:
        set_markings_constrained(solver, target_vars, targets)

    # Add forward/backward firing constraints
    add_firing_constraints(petrinet, init_vars, target_vars, solver,
                           transitions_vars)

    return (solver, variables)
