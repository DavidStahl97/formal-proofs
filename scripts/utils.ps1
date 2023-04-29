function getSrcFolder {
    $srcFolder = Join-Path -Path $PSScriptRoot -ChildPath "..\src"
    Write-Host "Src Folder: " -NoNewline
    Write-Host $srcFolder
    Write-Host ""
    return $srcFolder
}

function getLibrariesFolder {
    param(
        $CreateIfNotExists=$true
    )

    $srcFolder = getSrcFolder

    [string]$libDirectory = Join-Path -Path $srcFolder -ChildPath "libs"
    Write-Host "Libraries Folder: " -NoNewline
    Write-Host $libDirectory
    Write-Host ""

    if ($CreateIfNotExists) {
        Write-Host (New-Item -ErrorAction Ignore -Path $libDirectory -ItemType Directory)    
    }

    $libDirectory
}