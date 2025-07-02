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

from cinderella import CONFIGS_DIR
from cinderella.util import set_timeout



def execute_polyqent(file_path: str):   

    for config in sorted(os.listdir(CONFIGS_DIR)):
        print(f"Trying config: {config}")
        config_dict = load_config(os.path.join(CONFIGS_DIR, config))
        
        try:
            start_solve = time.time()
            result = set_timeout(execute, 10, file_path, config_dict, debug_mode=False)
            end_solve = time.time()
        except TimeoutError:
            print(f"Config {config} timed out")
            continue

        if result[0] == 'sat':
            break
        print(f"Config {config} failed with result {result[0]}")
    print(f"Time to solve with PolyHorn: {end_solve - start_solve}")

    return result[0], result[1]