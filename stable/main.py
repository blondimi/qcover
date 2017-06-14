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
from petri import load_petrinet
from coverability import coverability

def main(path):
    petrinet, init, targets = load_petrinet(path)

    result = coverability(petrinet, init, targets, prune=True,
                          max_iter=None)
            
    if result is None:
        print 'Unknown'
    elif result:
        print 'Unsafe'
    else:
        print 'Safe'

# Entry point
if __name__ == '__main__':
    parser = argparse.ArgumentParser(description='Performs coverability safety verification.')

    parser.add_argument('path', metavar='Filename', type=str,
                        help='File (.spec) to verify.')

    args = parser.parse_args()

    main(args.path)
