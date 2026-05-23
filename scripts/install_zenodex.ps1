param(
  [string]$BinDir = "$HOME\.zenodex\bin",
  [switch]$DryRun
)

$ErrorActionPreference = "Stop"

if (-not (Get-Command python -ErrorAction SilentlyContinue) -and -not (Get-Command python3 -ErrorAction SilentlyContinue)) {
  throw "python or python3 not found on PATH"
}

$python = if (Get-Command python3 -ErrorAction SilentlyContinue) { "python3" } else { "python" }
$ScriptDir = Split-Path -Parent $MyInvocation.MyCommand.Path
$RepoDir = Resolve-Path (Join-Path $ScriptDir "..")

function Install-Wrapper {
  param(
    [string]$Name,
    [string]$Target
  )

  $Out = Join-Path $BinDir "$Name.cmd"
  if ($DryRun) {
    Write-Output "would install $Out -> $Target"
    return
  }

  New-Item -ItemType Directory -Force -Path $BinDir | Out-Null
  $Content = @(
    "@echo off",
    "$python `"$Target`" %*"
  )
  Set-Content -Path $Out -Value $Content -Encoding ASCII
  Write-Output "installed $Out"
}

Install-Wrapper -Name "zenoctl" -Target (Join-Path $RepoDir "tools\zenoctl.py")
Install-Wrapper -Name "zenodex-node" -Target (Join-Path $RepoDir "tools\zeno_ledger_node.py")

$LocalTestnetOut = Join-Path $BinDir "zenodex-local-testnet.cmd"
if ($DryRun) {
  Write-Output "would install $LocalTestnetOut -> tools\zenoctl.py testnet local"
} else {
  New-Item -ItemType Directory -Force -Path $BinDir | Out-Null
  $ZenoctlTarget = Join-Path $RepoDir "tools\zenoctl.py"
  $Content = @(
    "@echo off",
    "$python `"$ZenoctlTarget`" testnet local %*"
  )
  Set-Content -Path $LocalTestnetOut -Value $Content -Encoding ASCII
  Write-Output "installed $LocalTestnetOut"
}

if (-not $DryRun) {
  Write-Output "run: $BinDir\zenoctl.cmd doctor --engine none --strict"
  Write-Output "run: $BinDir\zenodex-local-testnet.cmd up --out-dir %TEMP%\zenodex-local"
}
