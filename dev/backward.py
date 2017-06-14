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
from upward_sets import Upward

def _new_predecessors_upward(sys, markings, precomputed=None):
    basis = set()

    for m in markings:
        if precomputed is not None:
            if m in precomputed:
                to_merge = {pred_m for pred_m in precomputed[m] if not
                            Upward.elem_of(pred_m, markings)}
                Upward.merge(basis, to_merge)
                continue
            else:
                precomputed[m] = set()

        predecessors = sys.predecessors_upward(m)

        for pred_m in predecessors:
            if not Upward.elem_of(pred_m, markings):
                Upward.update(basis, pred_m)

        if precomputed is not None:
            Upward.merge(precomputed[m], predecessors)

    return basis

def backward_coverability(system, prune=None, new_candidates=None):
    sys, init_config, target_configs = system

    basis   = {c for c in target_configs}
    covered = Upward.elem_of(init_config, basis)

    if new_candidates is None:
        new_candidates = lambda x: x

    while not covered:
        prebasis = _new_predecessors_upward(sys, basis)

        if prune is not None:
            pruned = prune(prebasis)
            prebasis.difference_update(pruned)

        if len(prebasis) == 0:
            break
        else:
            prebasis = new_candidates(prebasis)
            Upward.merge(basis, prebasis)
            covered = Upward.elem_of(init_config, basis)

    return covered
