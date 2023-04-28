$srcFolder = . $PSScriptRoot\getSrcLocation.ps1

$libraryFolder = "$srcFolder\libraries"
Write-Host "Libraries Folder: " -NoNewline
Write-Host $libraryFolder
Write-Host ""

try 
{
    New-Item -Path $libraryFolder -ItemType Directory --ErrorAction Stop
}
catch 
{
    Write-Host "Library folder already exits"
}

return $libraryFolder