# Dependency Audit Snapshot - 2026-04-27

This is an engineering audit note, not a full supply-chain certification.

## Commands Run

```bash
(cd tools/dex-ui && npm audit --json)

python3 -m venv /tmp/zenodex-pip-audit-venv
/tmp/zenodex-pip-audit-venv/bin/python -m pip install --upgrade pip
/tmp/zenodex-pip-audit-venv/bin/python -m pip install 'pip-audit>=2.7,<3'
/tmp/zenodex-pip-audit-venv/bin/python -m pip_audit -r requirements-core.lock.txt
/tmp/zenodex-pip-audit-venv/bin/python -m pip_audit -r requirements-agents.lock.txt

(cd zk/state_proof_risc0 && cargo audit --json --no-fetch)
python3 tools/check_risc0_dependency_audit.py --no-fetch
RISC0_SKIP_BUILD=1 cargo check --manifest-path zk/state_proof_risc0/Cargo.toml --workspace
tools/_secbin/trivy fs --quiet --format json --scanners vuln .
```

## Results

| Surface | Result | Notes |
| --- | --- | --- |
| DEX UI npm lock | Clean | `npm audit` reported `total = 0` vulnerabilities across 217 dependencies. |
| Python runtime lock | Clean | `pip-audit -r requirements-core.lock.txt` reported no known vulnerabilities. |
| Python agent lock | Clean | `pip-audit -r requirements-agents.lock.txt` reported no known vulnerabilities. |
| RISC Zero state-proof workspace | Clean for RustSec vulnerabilities; three warnings remain | The workspace pins RISC Zero `2.3.2`, removing the critical `risc0-zkvm` / `risc0-zkvm-platform` alerts. A local `ark-relations 0.5.1` compatibility patch upgrades optional R1CS tracing from `tracing-subscriber 0.2.x` to the patched `0.3.x` line. |

## Rust Dependency Refresh

The RISC Zero workspace had several patchable transitive advisories in addition
to the arkworks `tracing-subscriber` blocker. The refresh now includes
compatible lockfile updates, a RISC Zero `1.2.6 -> 2.3.2` migration, and a
narrow local `ark-relations 0.5.1` patch for the optional R1CS tracing
subscriber:

| Package | Old | New | Cleared advisory |
| --- | --- | --- | --- |
| `risc0-zkvm` | `1.2.6` | `2.3.2` | `CVE-2025-61588` |
| `risc0-zkvm-platform` | `1.2.6` | `2.2.2` | `CVE-2025-61588` |
| `bytes` | `1.11.0` | `1.11.1` | `RUSTSEC-2026-0007` |
| `quinn-proto` | `0.11.13` | `0.11.14` | `RUSTSEC-2026-0037` |
| `rustls-webpki` | `0.103.8` | `0.103.13` | `RUSTSEC-2026-0049`, `RUSTSEC-2026-0098`, `RUSTSEC-2026-0099`, `RUSTSEC-2026-0104` |
| `rand` | `0.8.5` | `0.8.6` | `RUSTSEC-2026-0097` warning |
| `rand` | `0.9.2` | `0.9.3` | `RUSTSEC-2026-0097` warning |
| `tracing-subscriber` | `0.2.25` | `0.3.23` | `RUSTSEC-2025-0055` / `GHSA-xwfj-jgwm-7wp5` |

`RISC0_SKIP_BUILD=1 cargo check --workspace` passes after the refresh. The
local machine does not have the RISC Zero guest target installed, so the methods
crate reports placeholder methods unless `riscv32im-risc0-zkvm-elf` is
installed for the `risc0` toolchain.

## Local Arkworks Patch

The remaining RustSec vulnerability was in optional R1CS tracing:

- package: `tracing-subscriber`
- old locked version: `0.2.25`
- fixed range: `>=0.3.20`
- new locked version: `0.3.23`
- path before the local patch:

```text
tracing-subscriber 0.2.25
-> ark-relations 0.5.1
-> ark-groth16 / ark-crypto-primitives
-> risc0-groth16 2.0.3
-> risc0-zkvm 2.3.2
-> tau-state-proof-risc0-{guest,cli}
```

The published `ark-relations 0.5.1` crate requires
`tracing-subscriber = ^0.2`, so a direct lockfile refresh is not enough:

```bash
cargo update -p tracing-subscriber --precise 0.3.20
```

The workspace therefore carries a narrow `[patch.crates-io]` override at
`zk/state_proof_risc0/patches/ark-relations-0.5.1`. The patch keeps the
published crate source shape, upgrades only `tracing-subscriber` to `0.3.20+`,
and renames the tracing `Layer` hook from `new_span` to `on_new_span` for the
0.3 API.

Plain English: the RISC Zero 2.3 line has moved off the vulnerable RISC Zero VM
crates, and this repo now locally bridges the remaining arkworks tracing
dependency until arkworks or RISC Zero publishes the same dependency shift
upstream.

## Current Risk Posture

`cargo audit` and Trivy filesystem scanning now report zero known
vulnerabilities for the checked dependency surfaces. The RISC Zero audit still
reports non-vulnerability warnings for unmaintained transitive crates:

- `RUSTSEC-2025-0141`: `bincode 1.3.3` unmaintained
- `RUSTSEC-2024-0388`: `derivative 2.2.0` unmaintained
- `RUSTSEC-2024-0436`: `paste 1.0.15` unmaintained

The audit command preserves visibility of those warnings while failing on any
RustSec vulnerability:

```bash
python3 tools/check_risc0_dependency_audit.py
```

Plain English: there is no longer a default RustSec vulnerability exception for
the RISC Zero workspace. Warnings remain visible so they can be tracked without
being confused with active vulnerability findings.

## Required Follow-Up

1. Continue tracking a RISC Zero / arkworks upgrade path that removes the local
   `ark-relations` patch.
2. Re-evaluate `bincode` usage in `tau-state-proof-risc0-cli`; it is direct and
   should eventually move to a maintained encoding or a pinned compatibility
   wrapper.
3. Keep `cargo audit` in the security gate with no default vulnerability
   allowlist.
4. Rerun state-proof build and verification checks after any RISC Zero upgrade.

## Upgrade Feasibility Notes

Earlier checks were run in `/tmp` copies of `zk/state_proof_risc0`; the
RISC Zero `2.3.2` migration has now been applied to the repo.

### RISC Zero 2.3.x

Patch tested:

```text
risc0-zkvm = 2.3.1 / 2.3.2
risc0-build = 2.3.1 / 2.3.2
```

Result:

- `RISC0_SKIP_BUILD=1 cargo check` passes.
- Without the local arkworks patch, `cargo audit` still fails on
  `RUSTSEC-2025-0055`.
- With the local arkworks patch, `cargo audit` and Trivy filesystem scanning
  report zero known vulnerabilities.

Plain English: RISC Zero 2.3.x is build-compatible with the current code shape
and removes the critical RISC Zero CVEs. The remaining arkworks tracing alert is
closed locally by a small compatibility patch while upstream catches up.

### RISC Zero 3.0.x

Patch tested:

```text
risc0-zkvm = 3.0.5
risc0-build = 3.0.5
```

Result:

- `RISC0_SKIP_BUILD=1 cargo check` fails with the current local Rust toolchain
  (`rustc 1.87.0`), because transitive dependencies require Rust 1.88 and 1.90.
- Without the local arkworks patch, `cargo audit` still fails on
  `RUSTSEC-2025-0055`.
- `cargo audit` also reports `RUSTSEC-2023-0071` for `rsa 0.9.10` through
  `rzup 0.5.1`.

Plain English: RISC Zero 3.0.x is not the clean migration target for this repo
as-is. It raises the Rust MSRV and adds a second vulnerability while leaving the
upstream `tracing-subscriber` dependency shift unresolved.
