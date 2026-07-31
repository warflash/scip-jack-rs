$ErrorActionPreference = 'Stop'
$repo = 'F:\Repositories\skip-jack-rs'
$exe = 'C:\Users\nwies\AppData\Local\Temp\skip-jack-pace-benchmark-full.exe'
$resultPath = Join-Path $repo 'benchmarks\pace2018-results\pace-exact-full-current.csv'
$dataRoot = Join-Path $repo 'benchmarks\pace2018'
$tempDir = Join-Path $env:TEMP 'skip-jack-pace-full-output-cont'
New-Item -ItemType Directory -Force -Path $tempDir | Out-Null

$done = @{}
if (Test-Path -LiteralPath $resultPath) {
    foreach ($r in @(Import-Csv -LiteralPath $resultPath)) {
        $done["$($r.Track)|$($r.Instance)"] = $true
    }
}
$all = @()
foreach ($track in @('Track1','Track2')) {
    $optPath = Join-Path $dataRoot ($track.ToLowerInvariant() + '.csv')
    $opts = @{}
    foreach ($o in @(Import-Csv -LiteralPath $optPath)) {
        $opts[$o.paceName.Trim()] = $o.opt.Trim()
    }
    foreach ($f in @(Get-ChildItem -LiteralPath (Join-Path $dataRoot $track) -Filter '*.gr' | Sort-Object Name)) {
        $all += [pscustomobject]@{ Track=$track; Instance=$f.Name; File=$f.FullName; Optimum=$opts[$f.Name] }
    }
}
$total = $all.Count
$pending = @($all | Where-Object { -not $done["$($_.Track)|$($_.Instance)"] })
Write-Output "Resuming full suite: $($total-$pending.Count)/$total already recorded; $($pending.Count) remaining."

$index = $total - $pending.Count
foreach ($item in $pending) {
    $index++
    $safe = "$($item.Track)-$($item.Instance)"
    $outPath = Join-Path $tempDir ($safe + '.out')
    $errPath = Join-Path $tempDir ($safe + '.err')
    Remove-Item -LiteralPath $outPath,$errPath -Force -ErrorAction SilentlyContinue
    $sw = [Diagnostics.Stopwatch]::StartNew()
    $p = Start-Process -FilePath $exe -ArgumentList @($item.File,'--time-limit','120','--quiet') -RedirectStandardOutput $outPath -RedirectStandardError $errPath -WindowStyle Hidden -PassThru
    $external = $false
    while (-not $p.HasExited -and $sw.Elapsed.TotalSeconds -lt 150) {
        Start-Sleep -Milliseconds 100
    }
    if (-not $p.HasExited) {
        $external = $true
        taskkill.exe /PID $p.Id /T /F | Out-Null
        $p.WaitForExit()
    }
    $sw.Stop()
    $err = if (Test-Path -LiteralPath $errPath) { Get-Content -LiteralPath $errPath -Raw } else { '' }
    $status = ''
    $primal = ''
    $dual = ''
    $gap = ''
    $solverTime = ''
    $verified = 'false'
    if ($external) {
        $status = 'ExternalTimeout'
    } else {
        $m = [regex]::Match($err, '(?m)^\s*Status:\s*(.+?)\s*$'); if ($m.Success) { $status = $m.Groups[1].Value.Trim() }
        $m = [regex]::Match($err, '(?m)^\s*Primal bound:\s*([-+0-9.eE]+)\s*$'); if ($m.Success) { $primal = $m.Groups[1].Value.Trim() }
        $m = [regex]::Match($err, '(?m)^\s*Dual bound:\s*([-+0-9.eE]+)\s*$'); if ($m.Success) { $dual = $m.Groups[1].Value.Trim() }
        $m = [regex]::Match($err, '(?m)^\s*Gap:\s*([-+0-9.eE]+)%\s*$'); if ($m.Success) { $gap = $m.Groups[1].Value.Trim() }
        $m = [regex]::Match($err, '(?m)^\s*Time:\s*([-+0-9.eE]+)s\s*$'); if ($m.Success) { $solverTime = $m.Groups[1].Value.Trim() }
        if ($err -match '(?im)^\s*Verified:\s*true\s*$') { $verified = 'true' }
    }
    $row = [pscustomobject]@{
        Track=$item.Track
        Instance=$item.Instance
        PublishedOptimum=$item.Optimum
        Primal=$primal
        Dual=$dual
        GapPct=$gap
        SolverTimeSec=$solverTime
        WallTimeSec=('{0:F6}' -f $sw.Elapsed.TotalSeconds)
        Status=$status
        Verified=$verified
        ExternalTimeout=([string]$external)
    }
    $row | Export-Csv -LiteralPath $resultPath -Append -NoTypeInformation
    Remove-Item -LiteralPath $outPath,$errPath -Force -ErrorAction SilentlyContinue
    Write-Output ("DONE {0}/{1} {2} {3} {4} wall={5:F1}s" -f $index,$total,$item.Track,$item.Instance,$status,$sw.Elapsed.TotalSeconds)
}
Write-Output 'Full suite complete.'
