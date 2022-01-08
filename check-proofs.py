# %%
from subprocess import run
from pathlib import Path
import os
import sys

for file in Path(os.getcwd()).rglob('*.agda'):
    print('check file: ' + str(file))
    result = run(['agda', str(file)], check=False)
    if result != 0:
        sys.exit(1)



