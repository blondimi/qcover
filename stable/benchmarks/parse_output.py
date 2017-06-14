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
import re

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Parse other tools results")
    parser.add_argument("logfile", metavar="Log file", type=str)

    parser.add_argument("--tool", dest="tool", action="store",
                        help="mist-backward, bfc")

    args = parser.parse_args()

    with open(args.logfile) as file_content:
        if args.tool == "mist-backward":
            match = re.search("concludes (.*)", file_content.read())
        elif args.tool == "bfc":
            match = re.search("VERIFICATION ([A-Z]*)", file_content.read())
        
        if match is not None:
            result = match.group(1).strip()

            if args.tool  == "mist-backward":
                if result == "safe":
                    print "Safe"
                elif result == "unsafe":
                    print "Unsafe"
                else:
                    print "Unknown"
            elif args.tool == "bfc":
                if result == "SUCCESSFUL":
                    print "Safe"
                elif result == "FAILED":
                    print "Unsafe"
                else:
                    print "Unknown"
