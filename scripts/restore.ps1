Write-Host "Download Stdlib"
Write-Host ""
. $PSScriptRoot\downloadStdlib.ps1 -Version "1.7.1"

. $PSScriptRoot\generate-module.ps1