#!/bin/bash

files=(
    src/cinderella/witness/cinderella_15.py
    src/cinderella/witness/cinderella_17.py
    src/cinderella/witness/cinderella_19.py
    src/cinderella/witness/cinderella_small_eps.py
    src/cinderella/witness/cinderella_vareps.py
    src/cinderella/witness/cinderella_l2_15.py
    src/cinderella/witness/cinderella_l2_17.py
    src/cinderella/witness/cinderella_l2_19.py
    src/cinderella/witness/cinderella_l2_small_eps.py
    # src/cinderella/witness/cinderella_l2_vareps.py
    src/cinderella/witness/robot_cocktail.py
)

for file in "${files[@]}"; do
    echo "Running $file"
    uv run "$file"
done

echo "All experiments executed."
