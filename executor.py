"""
This module takes programs in the form of transition systems, creates an .smt2 
file for a ranking witness, and then executes PolyHorn to find a ranking
function that proves the termination of the program.
"""
import os
import sys
import time
from argparse import ArgumentParser

from polyqent.main import execute, load_config

from programs import *
from programs import __all__
from transition import TransitionSystem
from util import set_timeout
from rank_remain_witness import RRW

ROOT_FOLDER = os.path.abspath(os.path.dirname(os.path.realpath(__file__)))
CONFIGS_FOLDER = os.path.abspath(os.path.join(ROOT_FOLDER, 'configs'))


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
    parser = ArgumentParser(
        description='Find a ranking function for a given program', allow_abbrev=False)
    parser.add_argument('--program', type=str,
                        help='The program to be analyzed', choices=__all__, required=True)
    parser.add_argument('--use-invariants', action='store_true',
                        help='Use invariants in the constraint pair')
    parser.add_argument('--use-trivial-g', action='store_true',
                        help='Use trivial g')
    parser.add_argument('--use-heuristic', action='store_true',
                        help='Use heuristic for finding the witness')
    parser.add_argument('--c', type=int, default=1,
                        help='The number of conjunctions in the heuristic')
    parser.add_argument('--d', type=int, default=1,
                        help='The number of disjunctions in the heuristic')
    args, other_args = parser.parse_known_args()
    print(args, other_args)
    program: Program = getattr(sys.modules[__name__], args.program)(
        **parse_unknown_args(other_args))

    ts: TransitionSystem = program.get_transition_system()

    witness = RRW(ts)

    start_create = time.time()
    witness.find_witness()
    end_create = time.time()

    smt2_file = os.path.abspath(os.path.join(
        ROOT_FOLDER, 'out', f'{ts.name}.smt2'))

    for config in sorted(os.listdir(CONFIGS_FOLDER)):
        print(f"Trying config: {config}")
        config_dict = load_config(os.path.join(CONFIGS_FOLDER, config))
        config_dict["output_path"] = config.replace(".json", ".txt")

        try:
            start_solve = time.time()
            result = set_timeout(execute, 60, smt2_file, config_dict, debug_mode=True)
            end_solve = time.time()
        except TimeoutError:
            print(f"Config {config} timed out")
            continue

        if result[0] == 'sat':
            break
        print(f"Config {config} failed with result {result[0]}")

    print("PolyHorn output:")
    print(result[0])
    print("Model:")
    witness.print_model(result[1])

    print(f"Time to create witness: {end_create - start_create}")
    print(f"Time to solve with PolyHorn: {end_solve - start_solve}")
    print(f"Total time: {end_solve - start_solve + end_create - start_create}")
