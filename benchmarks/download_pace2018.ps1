[CmdletBinding()]
param(
    [string]$Destination = (Join-Path $PSScriptRoot 'pace2018')
)

$commit = '4df73cea9c311faea7d03e6d6bffa8733c34a1aa'
$archiveName = "SteinerTree-PACE-2018-instances-$commit.zip"
$url = "https://github.com/PACE-challenge/SteinerTree-PACE-2018-instances/archive/$commit.zip"
$expectedSha256 = '32FFDFEE349D2D352AC98248A1E23392D2537F5A37A48EC76169B9737DEC8378'
$tempRoot = Join-Path ([IO.Path]::GetTempPath()) 'skip-jack-benchmarks'
$archivePath = Join-Path $tempRoot $archiveName
$extractPath = Join-Path $tempRoot "pace2018-$commit"

New-Item -ItemType Directory -Force -Path $tempRoot | Out-Null

if (-not (Test-Path -LiteralPath $archivePath)) {
    Write-Host "Downloading pinned PACE 2018 archive..."
    Invoke-WebRequest -Uri $url -OutFile $archivePath
}

$actualSha256 = (Get-FileHash -Algorithm SHA256 -LiteralPath $archivePath).Hash.ToUpperInvariant()
if ($actualSha256 -ne $expectedSha256) {
    throw "PACE archive hash mismatch. Expected $expectedSha256 but got $actualSha256."
}

if (Test-Path -LiteralPath $Destination) {
    $existing = Get-ChildItem -LiteralPath $Destination -Force
    if ($existing.Count -gt 0) {
        throw "Destination is not empty: $Destination"
    }
}
else {
    New-Item -ItemType Directory -Force -Path $Destination | Out-Null
}

New-Item -ItemType Directory -Force -Path $extractPath | Out-Null
Expand-Archive -LiteralPath $archivePath -DestinationPath $extractPath -Force

$source = Join-Path $extractPath "SteinerTree-PACE-2018-instances-$commit"
Copy-Item -LiteralPath (Join-Path $source 'Track1') -Destination (Join-Path $Destination 'Track1') -Recurse
Copy-Item -LiteralPath (Join-Path $source 'Track2') -Destination (Join-Path $Destination 'Track2') -Recurse
Copy-Item -LiteralPath (Join-Path $source 'Track3') -Destination (Join-Path $Destination 'Track3') -Recurse
Copy-Item -LiteralPath (Join-Path $source 'track1.csv') -Destination $Destination
Copy-Item -LiteralPath (Join-Path $source 'track2.csv') -Destination $Destination
Copy-Item -LiteralPath (Join-Path $source 'track3.csv') -Destination $Destination
Copy-Item -LiteralPath (Join-Path $source 'README.md') -Destination (Join-Path $Destination 'PACE-README.md')
Copy-Item -LiteralPath (Join-Path $source 'LICENSE') -Destination (Join-Path $Destination 'LICENSE')

Write-Host "PACE 2018 benchmark data installed at $Destination"
Write-Host "Track1: $((Get-ChildItem (Join-Path $Destination 'Track1') -Filter '*.gr').Count) instances"
Write-Host "Track2: $((Get-ChildItem (Join-Path $Destination 'Track2') -Filter '*.gr').Count) instances"
Write-Host "Track3: $((Get-ChildItem (Join-Path $Destination 'Track3') -Filter '*.gr').Count) instances"
