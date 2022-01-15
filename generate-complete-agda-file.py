# %%
from pathlib import Path
import os

currentDirectory = os.getcwd()
imports = []

for file in Path(currentDirectory).rglob('*.agda'):
    relativeFilePath = os.path.relpath(str(file), currentDirectory)    
    if relativeFilePath == 'index.agda':
        continue

    split = os.path.split(relativeFilePath)
    assert len(split) > 0, split

    if split[0] == '':
        split = split[1:]

    fileName = split[-1]
    assert fileName.endswith('.agda'), fileName
        
    module = fileName.split('.agda')
    assert len(module) == 2, module
    assert module[1] == '', module

    split = split[:-1] + (module[0],)
    completeModuleName = '.'.join(split)
    
    imports.append('import ' + completeModuleName + '\n')

print('generated complete agda file: \n\n')
print(''.join(imports))

everythingFile = open('index.agda', 'w')
everythingFile.write(''.join(imports))
everythingFile.close()    

# %%
