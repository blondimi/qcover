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
from vass import VASS
from vass_configuration import VassConfig
from marking import Marking

def _name_state(number):
    return "p" + str(number)

def _add_thread_transition(vass, init, target, num_loc):
    init_state, init_loc     = init
    target_state, target_loc = target

    init_state   = _name_state(init_state)
    target_state = _name_state(target_state)

    update = [0] * num_loc
        
    if init_loc != target_loc:
        update[init_loc]   = -1
        update[target_loc] =  1

        vass.add_transition(init_state, Marking(update), target_state)
    else:
        new_state = _name_state(vass.num_states())
        vass.add_state(new_state)

        update[init_loc] = -1
        vass.add_transition(init_state, Marking(update), new_state)

        update[init_loc] =  1
        vass.add_transition(new_state, Marking(update), target_state)

def _add_spawn_transition(vass, init, target, num_loc):
    init_state, init_loc     = init
    target_state, target_loc = target

    init_state   = _name_state(init_state)
    target_state = _name_state(target_state)
        
    new_state = _name_state(vass.num_states())
    vass.add_state(new_state)

    update = [0] * num_loc

    update[init_loc] = -1
    vass.add_transition(init_state, Marking(update), new_state)

    if init_loc != target_loc:
        update[init_loc]   = 1
        update[target_loc] = 1
    else:
        update[init_loc] = 2

    vass.add_transition(new_state, Marking(update), target_state)

def load_vass_from_tts(tts_file, prop_file):
    vass = None
    header_read = False

    with open(tts_file) as input_file:
        for row in input_file:
            if "#" in row:
                row = row[:row.index("#")]

            data = row.strip()

            if len(data) == 0:
                continue

            if not header_read:
                num_states, num_loc = tuple(map(int, data.split()))
                states = {_name_state(i) for i in range(num_states)}
                vass = VASS(num_loc, states)
                header_read = True
            else:
                transition_type = None

                for symb in ["->", "+>"]:
                    if symb in data:
                        transition_type = symb
                        break

                if transition_type is None:
                    error = "Transition type unsupported in: {}".format(data)
                    raise ValueError(error)

                init, target = data.split(symb)
                init   = tuple(map(int, init.split()))
                target = tuple(map(int, target.split()))

                if transition_type == "->":
                    _add_thread_transition(vass, init, target, num_loc)
                elif transition_type == "+>":
                    _add_spawn_transition(vass, init, target, num_loc)

    init_state = _name_state(0)

    # On first state: self loop +1 on first counter
    vass.add_transition(init_state, Marking.one(num_loc, 0), init_state)

    # Init configuration
    init_config = VassConfig(init_state, Marking.one(num_loc, 0))

    # Target configuration
    state_num, loc_nums = _load_config_from_prop(prop_file)
    init_vector = [0] * num_loc

    for i in loc_nums:
        init_vector[i] += 1

    target_config = VassConfig(_name_state(state_num), Marking(init_vector))

    return (vass, init_config, target_config)

def _load_config_from_prop(filename):
    read = False

    with open(filename) as input_file:
        for row in input_file:
            if read:
                raise ValueError("File contains multiple configurations.")

            data   = row.strip()

            state_num, loc_nums = data.split("|")

            state_num = int(state_num)
            loc_nums  = map(int, loc_nums.split(","))

            read   = True

    if not read:
        raise ValueError("File does not contain any configuration.")

    return (state_num, loc_nums)
