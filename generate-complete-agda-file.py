# %%
from pathlib import Path
import os

currentDirectory = os.getcwd()
imports = []

for file in Path(currentDirectory).rglob('*.agda'):
    relativeFilePath = os.path.relpath(str(file), currentDirectory)    
    split = relativeFilePath.split('\\')
    assert len(split) > 0, split

    fileName = split[len(split) - 1]
    assert fileName.endswith('.agda'), fileName
        
    module = fileName.split('.agda')
    assert len(module) == 2, module
    assert module[1] == '', module

    split[len(split) - 1] = module[0]
    completeModuleName = '.'.join(split)
    
    imports.append('import ' + completeModuleName + '\n')

print('generated complete agda file:')
print(''.join(imports))

everythingFile = open('everything.agda', 'w')
everythingFile.write(''.join(imports))
everythingFile.close()    
