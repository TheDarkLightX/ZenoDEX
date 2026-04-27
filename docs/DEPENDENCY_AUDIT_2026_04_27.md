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
(cd zk/state_proof_risc0 && cargo check)
```

## Results

| Surface | Result | Notes |
| --- | --- | --- |
| DEX UI npm lock | Clean | `npm audit` reported `total = 0` vulnerabilities across 217 dependencies. |
| Python runtime lock | Clean | `pip-audit -r requirements-core.lock.txt` reported no known vulnerabilities. |
| Python agent lock | Clean | `pip-audit -r requirements-agents.lock.txt` reported no known vulnerabilities. |
| RISC Zero state-proof workspace | One vulnerability plus three allowed warnings | Compatible lock refreshes removed six patchable RustSec vulnerabilities. The remaining audit blocker is `RUSTSEC-2025-0055` in transitive `tracing-subscriber 0.2.25`. |

## Rust Lockfile Refresh

The RISC Zero workspace had several patchable transitive advisories in addition
to the RISC Zero / arkworks `tracing-subscriber` blocker. These were removed
with compatible lockfile-only updates:

| Package | Old | New | Cleared advisory |
| --- | --- | --- | --- |
| `bytes` | `1.11.0` | `1.11.1` | `RUSTSEC-2026-0007` |
| `quinn-proto` | `0.11.13` | `0.11.14` | `RUSTSEC-2026-0037` |
| `rustls-webpki` | `0.103.8` | `0.103.13` | `RUSTSEC-2026-0049`, `RUSTSEC-2026-0098`, `RUSTSEC-2026-0099`, `RUSTSEC-2026-0104` |
| `rand` | `0.8.5` | `0.8.6` | `RUSTSEC-2026-0097` warning |
| `rand` | `0.9.2` | `0.9.3` | `RUSTSEC-2026-0097` warning |

`cargo check` passes after the refresh. The local machine does not have the
RISC Zero guest target installed, so the methods crate reports placeholder
methods unless `riscv32im-risc0-zkvm-elf` is installed for the `risc0`
toolchain.

## Rust Finding

`RUSTSEC-2025-0055`:

- package: `tracing-subscriber`
- locked version: `0.2.25`
- fixed version: `>=0.3.20`
- path:

```text
tracing-subscriber 0.2.25
-> ark-relations 0.4.0
-> ark-groth16 / ark-crypto-primitives
-> risc0-groth16 1.2.6
-> risc0-zkvm 1.2.6
-> tau-state-proof-risc0-{guest,cli}
```

Direct lockfile refresh is not enough:

```bash
cargo update -p tracing-subscriber --precise 0.3.20
```

fails because `ark-relations 0.4.0` requires `tracing-subscriber = ^0.2`.

Plain English: the current RISC Zero 1.2 line pulls an arkworks 0.4 stack that
cannot consume the patched `tracing-subscriber` line. The clean fix is a RISC
Zero / arkworks major-version migration, not a small cargo update.

## Current Risk Posture

The advisory is terminal/log output poisoning through ANSI escape sequences in
logged untrusted input. The local ZK state-proof code does not directly import
or initialize `tracing-subscriber`, but the vulnerable crate is present in the
lockfile through the proof stack. Treat this as a real supply-chain finding
until the RISC Zero dependency stack is upgraded or isolated.

Temporary audit command that preserves visibility of the remaining warnings:

```bash
python3 tools/check_risc0_dependency_audit.py
```

That command exits successfully only if `RUSTSEC-2025-0055` is the sole
vulnerability. It still reports warning IDs, including:

- `RUSTSEC-2025-0141`: `bincode 1.3.3` unmaintained
- `RUSTSEC-2024-0388`: `derivative 2.2.0` unmaintained
- `RUSTSEC-2024-0436`: `paste 1.0.15` unmaintained

Plain English: this is a ratchet, not a fix. It keeps the current temporary
exception from silently expanding while the RISC Zero migration remains open.

## Required Follow-Up

1. Plan a RISC Zero major-version upgrade for `zk/state_proof_risc0`.
2. Re-evaluate `bincode` usage in `tau-state-proof-risc0-cli`; it is direct and
   should eventually move to a maintained encoding or a pinned compatibility
   wrapper.
3. Keep `cargo audit` in the security gate, but do not treat an ignore for
   `RUSTSEC-2025-0055` as a permanent fix.
4. Rerun state-proof build and verification checks after any RISC Zero upgrade.

## Upgrade Feasibility Notes

These checks were run in `/tmp` copies of `zk/state_proof_risc0`; no repo source
files were changed for the experiment.

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

Plain English: RISC Zero 2.3.x is build-compatible with the current code shape,
but it does not remove the audit blocker.

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
