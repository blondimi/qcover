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
import argparse
import os
import backward_petri
import backward_vass
from petri_utils import load_petrinet_from_spec
from vass_utils import load_vass_from_tts

def main(path):
    filename, extension = os.path.splitext(path)

    if extension == ".spec":
        petrinet, init, targets = load_petrinet_from_spec(path)

        result = backward_petri.coverability(petrinet, init, targets)
    elif extension == ".tts":
        vass, init, target = load_vass_from_tts(path, filename + ".prop")

        result = backward_vass.coverability(vass, init, {target})

    if result is None:
        print "Unknown"
    elif result:
        print "Unsafe"
    else:
        print "Safe"

# Entry point
if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="QCover is an efficient coverability verifier for discrete and continuous Petri nets.")

    parser.add_argument("path", metavar="Path", type=str,
                        help="File (.spec or .tts) to verify.")

    args = parser.parse_args()

    main(args.path)
