Write-Host "Type Check Agda Code"

. $PSScriptRoot\utils.ps1
$srcFolder = getSrcFolder

$indexFilePath = Join-Path -Path $srcFolder -ChildPath "Index.agda"
$librariesFilePath = Join-Path -Path $srcFolder -ChildPath "libraries"

try
{
     Push-Location
     Set-Location $srcFolder
     
     agda --version
     agda --html --html-dir=docs --no-caching --library-file=$librariesFilePath $indexFilePath
}
finally
{
     Pop-Location
}
