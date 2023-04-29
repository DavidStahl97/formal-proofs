param (
    [Parameter(Mandatory=$true)]
    [string]$Version
)   

Write-Host "Download Stdlib"
Write-Host ""

. $PSScriptRoot\utils.ps1
$librariesFolder = getLibrariesFolder

Remove-Item -ErrorAction Ignore -LiteralPath (Join-Path -Path $librariesFolder -ChildPath "agda-stdlib") -Force -Recurse    
Remove-Item -ErrorAction Ignore -LiteralPath (Join-Path -Path $librariesFolder -ChildPath "agda-stdlib.tar") -Force

$downloadUrl = "https://github.com/agda/agda-stdlib/archive/v$Version.tar.gz"
Write-Host "Download Url: " -NoNewline
Write-Host $downloadUrl
Write-Host ""

$zippedFile = Join-Path -Path $librariesFolder -ChildPath "agda-stdlib.tar"
Write-Host "Output File: " -NoNewline
Write-Host $zippedFile
Write-Host ""

Write-Host $zippedFile
Write-Host $librariesFolder

Invoke-WebRequest -O $zippedFile $downloadUrl -ErrorAction Stop
tar -zxvf $zippedFile -C $librariesFolder

Remove-Item $zippedFile -ErrorAction Stop
Rename-Item -Path "$librariesFolder/agda-stdlib-$Version" -NewName "agda-stdlib" -ErrorAction Stop

$agdaStdlibLocation = Join-Path -Path $librariesFolder -ChildPath "agda-stdlib/standard-library.agda-lib"
(Get-Content $agdaStdlibLocation).Replace("name: standard-library-$Version", "name: agda-stdlib") | Set-Content $agdaStdlibLocation