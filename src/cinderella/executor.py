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

import numpy as np


def execute_polyqent(file_path: str, repeat: int = 10):   

    config = os.path.join(CONFIGS_DIR, 'farkas-z3.json')
    config_dict = load_config(config)
    print(f"Using config: {config}")

    times = []
    
    final_result = None

    for i in range(repeat):
        
        try:
            start_solve = time.time()
            result = set_timeout(execute, 300, file_path, config_dict, debug_mode=False)
            end_solve = time.time()
        except TimeoutError:
            print(f"Config {config} timed out")
            continue

        if result[0] == 'sat':
            times.append(end_solve - start_solve)
            final_result = result
        else:
            print(f"Config {config} failed with result {result[0]}")
            
    if not times:
        print("No successful runs found.")
        return 'unsat', None
    
    avg, std = np.mean(times), np.std(times)
    print(f"Average time to solve with PolyHorn: {avg:.3f} +/- {std:.3f} seconds over {len(times)} runs")
    return final_result[0], final_result[1]


def execute_polyqent_variable_config(file_path: str):   

    for config in sorted(os.listdir(CONFIGS_DIR)):
        print(f"Trying config: {config}")
        config_dict = load_config(os.path.join(CONFIGS_DIR, config))
        
        try:
            start_solve = time.time()
            result = set_timeout(execute, 60, file_path, config_dict, debug_mode=False)
            end_solve = time.time()
        except TimeoutError:
            print(f"Config {config} timed out")
            continue

        if result[0] == 'sat':
            break
        print(f"Config {config} failed with result {result[0]}")
    print(f"Time to solve with PolyHorn: {end_solve - start_solve}")

    return result[0], result[1]
