"""
This module takes programs in the form of transition systems, creates an .smt2 
file for a ranking witness, and then executes PolyHorn to find a ranking
function that proves the termination of the program.
"""
import os
import sys
import subprocess
import time
from argparse import ArgumentParser

from programs import *
from programs import __all__
from transition import TransitionSystem
from witness import CINDem


FILE_LOCATION = os.path.abspath(os.path.dirname(os.path.realpath(__file__)))
POLYHORN_PATH = os.path.abspath(os.path.join(FILE_LOCATION, 'PolyHorn', 'PolyHorn'))


def parse_unknown_args(args):
    """
    Parse unknown arguments passed to the script.

    Parameters
    ----------
    args : list
        The list of arguments passed to the script.

    Returns
    -------
    dict
        The parsed arguments.
    """
    parsed_args = {}
    for i in range(len(args)):
        if args[i].startswith('--'):
            key = args[i][2:]
            value = args[i + 1]
            # Check if value is a boolean or a number
            if value.lower() == 'true':
                value = True
            elif value.lower() == 'false':
                value = False
            elif value.isdigit():
                value = int(value)
            else:
                try:
                    value = float(value)
                except ValueError:
                    pass
            parsed_args[key] = value
    return parsed_args

if __name__ == "__main__":
    parser = ArgumentParser(description='Find a ranking function for a given program', allow_abbrev=False)
    parser.add_argument('--program', type=str, help='The program to be analyzed', choices=__all__, required=True)
    parser.add_argument('--config', type=str, help='The configuration file for PolyHorn', default=os.path.abspath(os.path.join(FILE_LOCATION, 'polyhorn_config.json')))
    parser.add_argument('--use-invariants', action='store_true', help='Use invariants in the constraint pair')
    parser.add_argument('--use-trivial-g', action='store_true', help='Use trivial g')
    args, other_args = parser.parse_known_args()
    print(args, other_args)
    program: Program = getattr(sys.modules[__name__], args.program)(**parse_unknown_args(other_args))
    ts: TransitionSystem = program.get_transition_system()
    witness = CINDem(ts, 
                     use_invariants=args.use_invariants,
                     use_trivial_g=args.use_trivial_g)
    
    start_create = time.time()
    witness.find_witness()
    end_create = time.time()

    smt2_file = os.path.abspath(os.path.join(FILE_LOCATION, 'out', f'{ts.name}.smt2'))

    
    # Run the ./PolyHorn from within the PolyHorn directory
    # cd PolyHorn
    # ./PolyHorn -smt2 ../out/test.smt2 ../ph_config.json
    os.chdir(os.path.join(FILE_LOCATION, 'PolyHorn'))
    start_solve = time.time()
    result = subprocess.run([POLYHORN_PATH, '-smt2', smt2_file, args.config], capture_output=True, text=True)
    end_solve = time.time()
    print("PolyHorn output:")
    print(result.stdout)

    if result.returncode != 0:
        print("PolyHorn error:")
        print(result.stderr)
    print(f"Time to create witness: {end_create - start_create}")
    print(f"Time to solve with PolyHorn: {end_solve - start_solve}")
    print(f"Total time: {end_solve - start_solve + end_create - start_create}")