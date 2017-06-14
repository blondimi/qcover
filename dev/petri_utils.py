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
import config
from petri import Petri
from marking import Marking

def _add_constraints(data, places_indices, constraints_list):
    COMPARISONS = [">=", "="]  # List order matters here.
    entries = data.split(",")
    
    # Parse constraints
    for rule in entries:
        for comparison in COMPARISONS:
            if comparison in rule:
                place, value = rule.strip().split(comparison)
                place = place.strip()
                value = int(value)

                constraints_list[places_indices[place]] = (comparison,
                                                           value)

                break # Important, "=" appears in ">=" so would parse twice

    # Return trailing incomplete constraint
    if len([comp for comp in COMPARISONS if comp in entries[-1]]) == 0:
        return entries[-1]
    else:
        return ""

def _add_transition(petrinet, places, transition, rule):
    pos = rule.find("->")
    guards_str  = rule[:pos]
    updates_str = rule[pos+2:]
    guards  = {}
    updates = {}
    
    # Parse guards
    for guard in guards_str.split(","):
        var, value = guard.split(">=")

        guards[var.strip()] = int(value)

    # Parse updates
    for update in updates_str.split(","):
        match = re.search("\s*(.*)\'\s*=\s*(.*)\s*(\+|-)\s*(.*)\s*",
                          update) # xi' = xj {+,-} value
        
        if match is not None:
            var_in  = match.group(1).strip()
            var_out = match.group(2).strip()
            value   = int(match.group(3) + match.group(4))

            if var_in != var_out:
                raise ValueError("x_i\' = x_j + c illegal with i != j")

            updates[var_in] = value

    # Add transition
    for p in range(len(places)):
        guard  = guards[places[p]]  if places[p] in guards  else 0
        update = updates[places[p]] if places[p] in updates else 0

        if update >= 0:
            pre, post = guard, guard + update
        elif update < 0:
            pre, post = max(guard, -update), max(0, guard + update)

        # Add values if non zero
        if pre != 0:
            petrinet.set_pre(p, transition, pre)

        if post != 0:
            petrinet.set_post(p, transition, post)

def load_petrinet_from_spec(filename):
    MODES = ["vars", "rules", "init", "target", "invariants"]

    places  = []
    init    = []
    targets = []

    petrinet = None
    places_indices  = []
    num_transitions = 0

    # Precompute number of transitions
    with open(filename) as input_file:
        for row in input_file:
            if ";" in row:
                num_transitions += 1
    
    # Load data
    with open(filename) as input_file:
        mode      = "none"
        rules_acc = ""
        acc       = ""
        curr_transition = 0

        for row in input_file:
            data = row.strip()

            # Ignore empty/commented lines
            if len(data) == 0 or data[0] == "#":
                continue

            # Mode detection
            if data in MODES:
                mode = data

                # Allocate matrix for the Petri net, and places
                if mode == MODES[1]:
                    petrinet = Petri(len(places), num_transitions,
                                     config.representation_mode,
                                     config.precision)
                    init = [(">=", 0)] * len(places)
                    places_indices = {value: key for key, value in
                                      enumerate(places)}
            else:
                # Places
                if mode == MODES[0]:
                    places.extend(data.split(" "))
                # Rules
                elif mode == MODES[1]:
                    rules_acc += data
                    pos = rules_acc.find(";")

                    if pos >= 0:
                        _add_transition(petrinet, places,
                                        curr_transition,
                                        rules_acc[:pos])
                        curr_transition += 1
                        rules_acc = rules_acc[pos+1:]
                # Initial values
                elif mode == MODES[2]:
                    acc = _add_constraints(acc + data, places_indices, init)
                # Target values
                elif mode == MODES[3]:
                    new_target = [(">=", 0)] * len(places)
                    trailing = _add_constraints(data, places_indices,
                                                new_target) 
                    targets.append(tuple(new_target))
                   
                    if len(trailing.strip()) > 0:
                        raise ValueError("Incomplete target constraint.")
                # Invariants (not supported)
                elif mode == MODES[4]:
                    pass

    # Finish rules parsing (if necessary)
    while True:
        pos = rules_acc.find(";")

        if pos >= 0:
            _add_transition(petrinet, places, curr_transition,
                            rules_acc[:pos])
            curr_transition += 1
            rules_acc = rules_acc[pos+1:]
        else:
            break

    petrinet.freeze()

    init    = _to_constrained_marking(init)
    targets = [_to_constrained_marking(target) for target in targets]

    return (petrinet, init, targets)

def _to_constrained_marking(x):
    comp, marking = zip(*x)

    return (comp, Marking(marking))

# Add omegas to places that can take arbitrary values
def omega_marking(constrained_marking):
    comparisons, marking = constrained_marking
    new_marking = []

    for i in range(len(marking)):
        if comparisons[i] == ">=":
            new_marking.append(float("inf"))
        else:
            new_marking.append(marking[i])

    return Marking(new_marking)

def remove_omegas(marking, value=0):
    marking_omegaless = []
    
    for x in marking:
        if x == float("inf"):
            marking_omegaless.append(value)
        else:
            marking_omegaless.append(x)

    return Marking(marking_omegaless)
