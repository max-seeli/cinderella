#!/bin/bash

# Run all Python files in the current directory, one after another

uv run src/cinderella/witness/cinderella_19.py
uv run src/cinderella/witness/cinderella_l2_19.py
uv run src/cinderella/witness/cinderella_vareps.py
uv run src/cinderella/witness/tag.py

echo "All experiments executed."