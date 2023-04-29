$libraryFilePath = Join-Path -Path $PSScriptRoot -ChildPath "..\src\libraries"
$librariesFolder = Join-Path -Path $PSScriptRoot -ChildPath "..\src\libs"

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