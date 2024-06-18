# __init__.py
import os
import sys
import glob
from importlib import import_module
import inspect
from .program import Program

# Get the current directory of this file (__init__.py)
directory = os.path.dirname(__file__)

# List all Python files in this directory (excluding __init__.py)
python_files = glob.glob(os.path.join(directory, "*.py"))

# Import all classes from each Python file
for file_path in python_files:
    module_name = os.path.basename(file_path)[:-3]  # Remove .py from filename
    if module_name == "__init__":
        continue
    module = import_module(f".{module_name}", package='programs')
    
    # Dynamically import all names that are classes of type 'type'
    for name in dir(module):
        attribute = getattr(module, name)
        if isinstance(attribute, type):
            globals()[name] = attribute

# Filter for subclasses of "Program"
__all__ = [name
            for name, cls in inspect.getmembers(sys.modules[__name__], inspect.isclass)
            if issubclass(cls, Program)]
