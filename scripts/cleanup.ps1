$srcFolder = . $PSScriptRoot\getSrcLocation.ps1

$toBeDeletedFiles = @(
    "*.agdai"
    "*.agda~"
    "*.agda#"
)

Get-ChildItem $srcFolder -Include $toBeDeletedFiles -Recurse | Remove-Item -Force -ErrorAction Ignore

Remove-Item -LiteralPath (Join-Path -Path $srcFolder -ChildPath "libs") -Force -Recurse -ErrorAction Ignore
Remove-Item -LiteralPath (Join-Path -Path $srcFolder -ChildPath "_build") -Force -Recurse -ErrorAction Ignore
Remove-Item (Join-Path -Path $srcFolder -ChildPath "Index.agda") -Force -ErrorAction Ignore
Remove-Item (Join-Path -Path $srcFolder -ChildPath "libraries") -Force -ErrorAction Ignore