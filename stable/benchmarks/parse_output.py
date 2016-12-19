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
