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
