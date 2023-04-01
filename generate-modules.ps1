function GetModuleDirectoryPath {
    param (
        [Parameter(Mandatory)]
        [System.IO.DirectoryInfo]$Directory
    )

    if ($Directory.Name -eq "Dave") {
        return $Directory.Name + "."
    }

    $parentPart = GetModuleDirectoryPath -Directory $Directory.Parent
    return $parentPart + $Directory.Name + "."
}

function GetModuleName {
    param (
        [Parameter(Mandatory)]
        [System.IO.DirectoryInfo]$Directory
    )

    return (GetModuleDirectoryPath -Directory $Directory) + "Module"
}

function GetModuleFile {
    param (
        [Parameter(Mandatory)]
        [System.IO.DirectoryInfo]$Directory
    )

    Join-Path -Path $directory.FullName -ChildPath "Module.agda"
}

function GenerateModuleCode {
    param (
        [Parameter(Mandatory)]
        [string]$ModuleNamePrefix,
        [Parameter(Mandatory)]
        [string]$DirectoryPath       
    )

    $builder = [System.Text.StringBuilder]::new()

    [void]$builder.Append("module ")
    [void]$builder.Append($ModuleNamePrefix)
    [void]$builder.AppendLine("Module where")

    foreach ($agdaFile in Get-ChildItem -Path $DirectoryPath -File -Filter "*.agda") {                
        [void]$builder.Append(" open import ")
        [void]$builder.Append($ModuleNamePrefix)

        $moduleName = $agdaFile.Name.Substring(0, $agdaFile.Name.Length - ".agda".Length)
        [void]$builder.Append($moduleName)
        [void]$builder.AppendLine(" public")
    }

    return $builder.ToString()
}

function ExistsAnyAgdaFiles {
    param (
        [Parameter(Mandatory)]
        [string]$DirectoryPath
    )

    $count = (Get-ChildItem -Path $DirectoryPath -File -Filter "*.agda").Count
    $anyAgdaFilesInDirectory = $count -gt 0 
    return $anyAgdaFilesInDirectory
}

function DeleteAllModuleFiles {
    $directories = Get-ChildItem -Recurse -Directory -Path "Dave"
    foreach ($directory in $directories) {
        $moduleFile = Join-Path -Path $directory.FullName -ChildPath "Module.agda"
        if (Test-Path $moduleFile) {
            Remove-Item $moduleFile
        }
    }
}

function CreateModules {
    $directories = Get-ChildItem -Recurse -Directory -Path "Dave" | Where-Object { ExistsAnyAgdaFiles -Directory $_.FullName } | Sort-Object -Property FullName
    foreach ($directory in $directories) {
        $ModuleNamePrefix = GetModuleDirectoryPath -Directory $directory
        $moduleFile = GetModuleFile -Directory $directory
        $moduleName = GetModuleName -Directory $directory        
        
        Write-Host "Create Module: " -NoNewLine
        Write-Host $moduleName    

        Set-Content -Path $moduleFile -Value (GenerateModuleCode -ModuleNamePrefix $ModuleNamePrefix -DirectoryPath $directory.FullName)        
    }
}

function CreateIndexFile {
    $moduleFiles = Get-ChildItem -Recurse -File -Filter "Module.agda" -Path "Dave" | Sort-Object -Property FullName     

    $builder = [System.Text.StringBuilder]::new()

    foreach ($moduleFile in $moduleFiles) {
        [void]$builder.Append("import ")        

        $moduleName = GetModuleName -Directory $moduleFile.Directory
        
        Write-Host "Add Module: " -NoNewLine
        Write-Host $moduleName
        
        [void]$builder.AppendLine($moduleName)
    }

    Set-Content -Path "index.agda" -Value $builder.ToString()
}

DeleteAllModuleFiles
CreateModules
CreateIndexFile