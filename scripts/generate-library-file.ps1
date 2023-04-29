Write-Host "Gnerate libraries file"

. $PSScriptRoot\utils.ps1
$srcFolder = getSrcFolder

$libraryFilePath = Join-Path -Path $srcFolder -ChildPath "libraries"
$librariesFolder = Join-Path -Path $srcFolder -ChildPath "libs"

$libraries = @(
    "agda-stdlib/standard-library.agda-lib"
)

$builder = [System.Text.StringBuilder]::new()

foreach ($library in $libraries) 
{
    $libPath = Join-Path -Path $librariesFolder -ChildPath $library
    $builder.AppendLine($libPath)
}

Set-Content -Path $libraryFilePath -Value $builder.ToString()