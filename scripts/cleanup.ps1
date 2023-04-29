Write-Host "cleanup project"

. $PSScriptRoot\utils.ps1
$srcFolder = getSrcFolder

$toBeDeletedFiles = @(
    "*.agdai"
    "*.agda~"
    "*.agda#"
)

Write-Host "Remove agda files from type checking"
Get-ChildItem $srcFolder -Include $toBeDeletedFiles -Recurse | Remove-Item -Force -ErrorAction Ignore

Write-Host "Remove libs folder"
Remove-Item -LiteralPath (Join-Path -Path $srcFolder -ChildPath "libs") -Force -Recurse -ErrorAction Ignore

Write-Host "Remove _build folder"
Remove-Item -LiteralPath (Join-Path -Path $srcFolder -ChildPath "_build") -Force -Recurse -ErrorAction Ignore

Write-Host "Remove Index.agda"
Remove-Item (Join-Path -Path $srcFolder -ChildPath "Index.agda") -Force -ErrorAction Ignore

Write-Host "Remove libraries file"
Remove-Item (Join-Path -Path $srcFolder -ChildPath "libraries") -Force -ErrorAction Ignore