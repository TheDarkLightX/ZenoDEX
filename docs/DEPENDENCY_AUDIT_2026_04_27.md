# Dependency Audit Snapshot - 2026-04-27

This is an engineering audit note, not a full supply-chain certification.

## Commands Run

```bash
cd tools/dex-ui
npm audit --json

python3 -m venv /tmp/zenodex-pip-audit-venv
/tmp/zenodex-pip-audit-venv/bin/python -m pip install --upgrade pip
/tmp/zenodex-pip-audit-venv/bin/python -m pip install 'pip-audit>=2.7,<3'
/tmp/zenodex-pip-audit-venv/bin/python -m pip_audit -r requirements-core.lock.txt
/tmp/zenodex-pip-audit-venv/bin/python -m pip_audit -r requirements-agents.lock.txt

cd zk/state_proof_risc0
cargo audit
cargo audit --ignore RUSTSEC-2025-0055
```

## Results

| Surface | Result | Notes |
| --- | --- | --- |
| DEX UI npm lock | Clean | `npm audit` reported `total = 0` vulnerabilities across 217 dependencies. |
| Python runtime lock | Clean | `pip-audit -r requirements-core.lock.txt` reported no known vulnerabilities. |
| Python agent lock | Clean | `pip-audit -r requirements-agents.lock.txt` reported no known vulnerabilities. |
| RISC Zero state-proof workspace | One vulnerability plus three allowed warnings | `cargo audit` failed on `RUSTSEC-2025-0055` in transitive `tracing-subscriber 0.2.25`. |

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
cd zk/state_proof_risc0
cargo audit --ignore RUSTSEC-2025-0055
```

That command exits successfully but still reports:

- `RUSTSEC-2025-0141`: `bincode 1.3.3` unmaintained
- `RUSTSEC-2024-0388`: `derivative 2.2.0` unmaintained
- `RUSTSEC-2024-0436`: `paste 1.0.15` unmaintained

## Required Follow-Up

1. Plan a RISC Zero major-version upgrade for `zk/state_proof_risc0`.
2. Re-evaluate `bincode` usage in `tau-state-proof-risc0-cli`; it is direct and
   should eventually move to a maintained encoding or a pinned compatibility
   wrapper.
3. Keep `cargo audit` in the security gate, but do not treat an ignore for
   `RUSTSEC-2025-0055` as a permanent fix.
4. Rerun state-proof build and verification checks after any RISC Zero upgrade.
