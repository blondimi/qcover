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
from petri_smt import build_solver, build_solver_nomarking, set_constrained_marking, set_constrained_markings

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

def _max_support(solver, variables, transitions, parallel=False):
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

    places = petrinet.places_set(transitions, reverse, pre=True, post=True)
    places_subset = places & marking.get_support()

    while len(transitions_subset) < len(transitions):
        new = False

        for t in transitions - transitions_subset:
            preset = petrinet.places_preset({t}, reverse)

            if preset <= places_subset:
                postset = petrinet.places_postset({t}, reverse)
                transitions_subset = transitions_subset | {t}
                places_subset = places_subset | postset
                new = True
                
        if not new:
            break

    return transitions_subset

def reachable(petrinet, init_marking, target_marking, limreach=False):
    # if initial marking = target marking return trivial solution
    if init_marking == target_marking:
        return (True, set())

    transitions = set(range(petrinet.num_transitions()))
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
        support = _max_support(solver, variables, transitions,
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
        set_constrained_marking(solver, init_vars, init)

    if targets is not None:
        set_constrained_markings(solver, target_vars, targets)

    # Add forward/backward firing constraints
    add_firing_constraints(petrinet, init_vars, target_vars, solver,
                           transitions_vars)

    return (solver, variables)

_unique_tag = 0 # GLOBAL VARIABLE for _add_firing_constraints_places
                # z3 requires unique name for each new variable...
def _add_firing_constraints_places(petrinet, marking, solver,
                                   variables, backward=False):
    tag = "bl" if backward else "fl"

    global _unique_tag
    places_variables = [z3.Int("{}_{}_{}".format(tag, _unique_tag, p))
                        for p in range(petrinet.num_places())]
    _unique_tag += 1
    
    for p in range(petrinet.num_places()):
        var = places_variables[p]
        preset = petrinet.transitions_preset({p}, reverse=backward)
        constraints = []

        for t in preset:
            t_preset = petrinet.places_preset({t}, reverse=backward)

            constraint = z3.And(variables[t] > 0,
                                z3.And([z3.And(places_variables[q] > 0,
                                               var > places_variables[q])
                                        for q in t_preset]))
            constraints.append(constraint)

        solver.add(z3.Implies(marking[p] >  0, var == 1))
        solver.add(z3.Implies(marking[p] == 0, z3.Implies(var > 0,
                                                   z3.Or(constraints))))

    for t in range(petrinet.num_transitions()):
        places = petrinet.places_set({t}, pre=True, post=True, 
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
