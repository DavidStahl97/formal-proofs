$srcFolder = . $PSScriptRoot\getSrcLocation.ps1

$libraryFolder = "$srcFolder\libs"
Write-Host "Libraries Folder: " -NoNewline
Write-Host $libraryFolder
Write-Host ""

New-Item -ErrorAction Ignore -Path $libraryFolder -ItemType Directory    

return $libraryFolder