param(
    [ValidateSet("up", "down", "logs", "status", "smoke")]
    [string] $Action = "up",
    [ValidateSet("auto", "docker", "podman")]
    [string] $Engine = "auto",
    [int] $UiPort = 3000,
    [string] $ApiToken = "zenodex-local-demo-token",
    [switch] $WithTau,
    [switch] $DryRun
)

$ErrorActionPreference = "Stop"
$RepoRoot = Resolve-Path (Join-Path $PSScriptRoot "..")
Set-Location $RepoRoot

if ($UiPort -lt 1 -or $UiPort -gt 65535) {
    throw "invalid UiPort: $UiPort"
}

if ($Engine -eq "auto") {
    if (Get-Command docker -ErrorAction SilentlyContinue) {
        $Engine = "docker"
    } elseif (Get-Command podman -ErrorAction SilentlyContinue) {
        $Engine = "podman"
    } elseif ($DryRun) {
        $Engine = "docker"
    } else {
        throw "container engine not found: install Docker or Podman"
    }
} elseif (-not $DryRun -and -not (Get-Command $Engine -ErrorAction SilentlyContinue)) {
    throw "container engine not found: $Engine"
}

function Invoke-CommandLine {
    param([string[]] $Command)
    if ($DryRun) {
        Write-Output ("+ " + ($Command -join " "))
        return
    }
    $Program = $Command[0]
    $Rest = @()
    if ($Command.Length -gt 1) {
        $Rest = $Command[1..($Command.Length - 1)]
    }
    & $Program @Rest
    if ($LASTEXITCODE -ne 0) {
        throw "command failed with exit code $LASTEXITCODE"
    }
}

function Invoke-DemoCompose {
    param([string[]] $Args)
    $env:UI_PORT = [string] $UiPort
    $env:DEMO_API_TOKEN = $ApiToken
    Invoke-CommandLine -Command (@($Engine, "compose", "-f", "docker-compose.yml", "-f", "docker-compose.testnet-demo.yml") + $Args)
}

function Invoke-TauCompose {
    param([string[]] $Args)
    $env:UI_PORT = [string] $UiPort
    $env:DEMO_API_TOKEN = $ApiToken
    Invoke-CommandLine -Command (@($Engine, "compose", "-f", "docker-compose.yml", "-f", "docker-compose.permissionless.yml", "--profile", "local-node") + $Args)
}

switch ($Action) {
    "up" {
        Invoke-DemoCompose @("up", "-d", "--build", "zenodex")
        if ($WithTau) {
            Invoke-TauCompose @("up", "-d", "tau-local")
        }
        Write-Output "ZenoDEX local testnet demo is starting."
        Write-Output "UI:       http://127.0.0.1:$UiPort"
        Write-Output "API:      proxied through the UI at /api/*"
        Write-Output "Token:    injected into the local runtime UI config"
        Write-Output "Stop:     .\scripts\zenodex_testnet_demo.ps1 down -UiPort $UiPort"
        Write-Output "Node test: .\scripts\zenodex_testnet_demo.ps1 smoke"
    }
    "down" {
        Invoke-DemoCompose @("down")
        if ($WithTau) {
            Invoke-TauCompose @("down")
        }
    }
    "logs" {
        Invoke-DemoCompose @("logs", "-f", "zenodex")
    }
    "status" {
        Invoke-DemoCompose @("ps")
        Write-Output "UI: http://127.0.0.1:$UiPort"
    }
    "smoke" {
        Invoke-CommandLine -Command @("python", "tools/zenoctl.py", "testnet", "up", "--profile", "docker-two-node", "--engine", $Engine)
    }
}
