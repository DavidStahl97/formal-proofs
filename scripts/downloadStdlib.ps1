param (
    [Parameter(Mandatory=$true)]
    [string]$Version
)   

$librariesFolder = . $PSScriptRoot\getLibrariesFolder.ps1

try {
    Remove-Item -LiteralPath "$librariesFolder\agda-stdlib" -Force -Recurse --ErrorAction Stop    
}
catch {
    Write-Host "agda-stdlib was already deleted"
}


$downloadUrl = "https://github.com/agda/agda-stdlib/archive/v$Version.tar.gz"
Write-Host "Download Url: " -NoNewline
Write-Host $downloadUrl
Write-Host ""

$tarFile = "$librariesFolder\agda-stdlib.tar"
Write-Host "Output File: " -NoNewline
Write-Host $tarFile
Write-Host ""

Invoke-WebRequest -O $tarFile $downloadUrl
tar -zxvf $tarFile
Remove-Item $tarFile

Rename-Item -Path "$librariesFolder/agda-stdlib-$Version" -NewName "agda-stdlib"

$agdaStdlibLocation = "$librariesFolder/agda-stdlib"
(Get-Content $agdaStdlibLocation).Replace("name: standard-library-$Version", "name: agda-stdlib") | Set-Content $agdaStdlibLocation