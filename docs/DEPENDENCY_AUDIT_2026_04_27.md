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
(cd zk/state_proof_risc0 && cargo audit --ignore RUSTSEC-2025-0055)
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
| RISC Zero state-proof workspace | One low-severity vulnerability plus three allowed warnings | The workspace now pins RISC Zero `2.3.2`, which removes the critical `risc0-zkvm` / `risc0-zkvm-platform` dependency alerts. The remaining audit blocker is `RUSTSEC-2025-0055` in transitive `tracing-subscriber 0.2.25`. |

## Rust Dependency Refresh

The RISC Zero workspace had several patchable transitive advisories in addition
to the arkworks `tracing-subscriber` blocker. The refresh now includes both
compatible lockfile updates and a RISC Zero `1.2.6 -> 2.3.2` migration:

| Package | Old | New | Cleared advisory |
| --- | --- | --- | --- |
| `risc0-zkvm` | `1.2.6` | `2.3.2` | `CVE-2025-61588` |
| `risc0-zkvm-platform` | `1.2.6` | `2.2.2` | `CVE-2025-61588` |
| `bytes` | `1.11.0` | `1.11.1` | `RUSTSEC-2026-0007` |
| `quinn-proto` | `0.11.13` | `0.11.14` | `RUSTSEC-2026-0037` |
| `rustls-webpki` | `0.103.8` | `0.103.13` | `RUSTSEC-2026-0049`, `RUSTSEC-2026-0098`, `RUSTSEC-2026-0099`, `RUSTSEC-2026-0104` |
| `rand` | `0.8.5` | `0.8.6` | `RUSTSEC-2026-0097` warning |
| `rand` | `0.9.2` | `0.9.3` | `RUSTSEC-2026-0097` warning |

`RISC0_SKIP_BUILD=1 cargo check --workspace` passes after the refresh. The
local machine does not have the RISC Zero guest target installed, so the methods
crate reports placeholder methods unless `riscv32im-risc0-zkvm-elf` is
installed for the `risc0` toolchain.

## Rust Finding

`RUSTSEC-2025-0055`:

- package: `tracing-subscriber`
- locked version: `0.2.25`
- fixed version: `>=0.3.20`
- path:

```text
tracing-subscriber 0.2.25
-> ark-relations 0.5.1
-> ark-groth16 / ark-crypto-primitives
-> risc0-groth16 2.0.3
-> risc0-zkvm 2.3.2
-> tau-state-proof-risc0-{guest,cli}
```

Direct lockfile refresh is not enough:

```bash
cargo update -p tracing-subscriber --precise 0.3.20
```

fails because `ark-relations 0.5.1` requires `tracing-subscriber = ^0.2`.

Plain English: the current RISC Zero 2.3 line has moved off the vulnerable
RISC Zero VM crates, but its arkworks stack still cannot consume the patched
`tracing-subscriber` line. The remaining fix requires an upstream arkworks /
RISC Zero dependency shift, not a small cargo update.

## Current Risk Posture

The remaining advisory is terminal/log output poisoning through ANSI escape
sequences in logged untrusted input. The local ZK state-proof code does not
directly import or initialize `tracing-subscriber`, but the vulnerable crate is
present in the lockfile through the proof stack. Treat this as a real
supply-chain finding until the arkworks dependency stack is upgraded or
isolated.

Temporary audit command that preserves visibility of the remaining warnings:

```bash
python3 tools/check_risc0_dependency_audit.py
```

That command exits successfully only if `RUSTSEC-2025-0055` is the sole
vulnerability. It still reports warning IDs, including:

- `RUSTSEC-2025-0141`: `bincode 1.3.3` unmaintained
- `RUSTSEC-2024-0388`: `derivative 2.2.0` unmaintained
- `RUSTSEC-2024-0436`: `paste 1.0.15` unmaintained

Plain English: this is a narrow remaining exception, not a full clean bill of
health. It keeps the temporary exception from silently expanding while the
arkworks `tracing-subscriber` blocker remains open.

## Required Follow-Up

1. Continue tracking a RISC Zero / arkworks upgrade path that removes
   `tracing-subscriber 0.2.25`.
2. Re-evaluate `bincode` usage in `tau-state-proof-risc0-cli`; it is direct and
   should eventually move to a maintained encoding or a pinned compatibility
   wrapper.
3. Keep `cargo audit` in the security gate, but do not treat an ignore for
   `RUSTSEC-2025-0055` as a permanent fix.
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
- `cargo audit` still fails on `RUSTSEC-2025-0055`.
- The vulnerable path moves from `ark-relations 0.4.0` to `ark-relations 0.5.1`,
  but `tracing-subscriber 0.2.25` remains.
- Trivy filesystem scanning drops from two critical RISC Zero findings plus one
  low finding to the single low `tracing-subscriber` finding.

Plain English: RISC Zero 2.3.x is build-compatible with the current code shape
and removes the critical RISC Zero CVEs, but it does not remove the final low
`tracing-subscriber` audit blocker.

### RISC Zero 3.0.x

Patch tested:

```text
risc0-zkvm = 3.0.5
risc0-build = 3.0.5
```

Result:

- `RISC0_SKIP_BUILD=1 cargo check` fails with the current local Rust toolchain
  (`rustc 1.87.0`), because transitive dependencies require Rust 1.88 and 1.90.
- `cargo audit` still fails on `RUSTSEC-2025-0055`.
- `cargo audit` also reports `RUSTSEC-2023-0071` for `rsa 0.9.10` through
  `rzup 0.5.1`.

Plain English: RISC Zero 3.0.x is not the clean migration target for this repo
as-is. It raises the Rust MSRV and adds a second vulnerability while leaving the
original `tracing-subscriber` issue unresolved.
