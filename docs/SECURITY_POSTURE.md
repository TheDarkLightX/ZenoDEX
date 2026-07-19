---
title: SECURITY_POSTURE
type: note
permalink: autonomous-tau-dex-review/docs/security-posture
---

# Security Posture

This document records a few intentional hardening choices in the runtime and why
they exist. The goal is to make the repo's security posture inspectable from
source, not inferred from tribal knowledge.

## Runtime Boundaries

- The primary semantic acceptance gate is the strong settlement validator in
  `src/core/` and `src/integration/validation.py`.
- Tau is an additional, fail-closed verification layer for specific bounded
  checks. It is not the sole runtime authority.
- The unsigned in-memory perps and zUSD APIs were deleted. Production exposes
  only signed wallet/ledger transports, and retired demo environment settings
  cause startup refusal rather than re-enabling a compatibility path.
- Production wallet transports import the verifier-only Tau RPC boundary in
  `src/integration/tau_net_rpc.py`. Raw private-key parsing, transaction/intent
  signing, `createblock`, and signed-transaction construction live under
  `src/nonproduction/`; the legacy local-testnet client facade and autotrader
  executor are removed during production image assembly.
- Production images are assembled from a curated builder-stage source tree.
  Development/local-testnet modules and stale bytecode never enter a final OCI
  layer, and a build-time artifact scanner enforces that exclusion.

## Hardening Decisions

### No `assert` on exposed runtime or signing paths

`assert` statements disappear under `python -O`. On trust boundaries we want an
explicit, fail-closed decision rather than an optimization-dependent check.

Applied to:
- BLS signature verification paths
- proof-verifier subprocess setup
- Tau subprocess setup
- exposed API request parsing / state-transition glue

Reasoning:
- Failures on these paths should surface as deterministic rejections or explicit
  misconfiguration errors.
- They should never depend on interpreter optimization flags.

### Canonical encoding for hash/signature inputs

Hash inputs must use the shared canonical encoder in `src/state/canonical.py`.

Applied to:
- agent-side intent ID generation
- policy-artifact serialization helpers

Reasoning:
- Mixed encoders create drift between signing, hashing, receipts, and replay
  validation.
- The shared encoder rejects floats and invalid Unicode scalar values, which
  removes ambiguous or implementation-defined hash inputs.

### Fail-closed external tool resolution

The zUSD Tau gate now defaults `ZUSD_TAU_ALLOW_PATH_LOOKUP=false`.

Reasoning:
- Security-sensitive verifier and Tau binaries should resolve to explicit paths
  in production.
- `PATH` lookup is convenient for local development but weakens determinism and
  makes accidental tool substitution easier.

### Static assets inherit the same security headers

The nginx static-asset cache location now repeats the security headers applied
at the server level, and the API proxy now sets an explicit body limit.

Reasoning:
- Nested `add_header` directives can unintentionally narrow the header set.
- The API body limit should be explicit and aligned with bounded parsing in the
  Python layer.

### Runtime dependencies are smaller than local/dev dependencies

The repo now splits:
- `requirements-core.txt` for production/runtime
- `requirements-agents.txt` for optional agent/orchestration features
- `requirements.txt` as a convenience umbrella for local checkouts
- `requirements-core.lock.txt`, `requirements-agents.lock.txt`, and
  `requirements-dev.lock.txt` for hash-locked installs

Reasoning:
- The production image should not pull in agent/LLM packages unless an operator
  explicitly opts into them.
- Smaller runtime dependency sets reduce both supply-chain exposure and operator
  confusion about what is actually needed in production.

### Python install surfaces are hash-locked or explicitly classified

`tools/check_python_hash_locks.py` verifies that the three root lockfiles are
flattened, hash-complete, and generated with `pip-compile --generate-hashes`.
It also scans supported install surfaces for Python package installation
commands. Root repo dependencies must install a root lockfile with
`--require-hashes`, and unlocked root manifests are rejected.

The audit records the remaining unhashed Python install commands as named
exceptions in its JSON report. Current exceptions are optional local Tau Testnet
checkout dependencies, optional GPU backend recommendations, the remote ESSO
experiment bootstrap, and the optional PyInstaller native-oracle bundle builder.
These exceptions are outside the production image and release gate.

### Proof metadata binds proof toolchain lock state

ZenoLedger proof metadata includes `toolchain_lock_hash`. By default, local
metadata builders compute it from a repo manifest that hashes the Python
lockfiles, Docker build files, Lean toolchain/lake manifests, Risc0 Cargo
workspace locks, and Rust TEE verifier locks.

Reasoning:
- A proof receipt should carry the replay/toolchain lock posture that shaped the
  verifier and public-input environment.
- The hash is a file-manifest commitment. Live external binaries and services
  still need their own attestation or operator approval.

### Tau transaction envelopes reject malformed numeric metadata

Tau transaction signing now rejects boolean and negative values for
`sequence_number` and `expiration_time`.

Reasoning:
- These fields are ordering / expiry metadata, not free-form payloads.
- Booleans are technically `int` in Python and should not be accepted as valid
  sequence or expiry values.
- Negative values do not make sense for transaction ordering or expiration.
- The helper still accepts other integer-like values that normalize cleanly so
  existing local tooling does not break unnecessarily during hardening.

### Quote-receipt witness validation stays fail-closed per receipt group

The DEX engine validates quote-receipt leg bindings per `quote_receipt_hash`,
rejecting duplicate bindings and incomplete coverage before settlement
application.

Reasoning:
- Quote-bound intents should only prove coverage of the receipt they actually
  reference.
- Reusing leg index `0` across unrelated receipts must remain valid.
- Duplicate or incomplete bindings must remain deterministic rejections even if
  the implementation is simplified internally.

### Mechanism-design findings are contained in the production posture

The mechanism-design evidence program
(`experiments/mechanism_design_math_v1/`, research-only) surfaced three economic
deviations. Each was traced to its production exposure; all three are contained.
Evidence per finding is named below: the config-gated CoW containment is
regression-tested, while the perp bypass (shell gate) and the tie-break
(off-chain tooling) are established by the shell's existing runtime-gate tests
and by code inspection respectively.

- **Perp settlement bypass via `advance_epoch` (O-PT-02 / H-MD-PT-002).** The
  pure-core `guard_advance_epoch` (`src/core/perp_v2/guards.py`) checks only the
  epoch bound, so in the *pure core* a trader could advance past an unfavorable
  settlement. This is **not live-exploitable**: the engine shell
  (`apply_perp_ops` → `perp_runtime_risk_gate`,
  `src/core/perp_runtime_risk_gate.py`) rejects advance-before-settle with
  `cannot advance epoch before settling current epoch`. The settle-before-advance
  invariant lives in the shell; the permissive core guard is a **defense-in-depth
  gap only**. Hardening the pure-core guard to mirror the shell's
  `epoch_settled_ok` is a candidate left for human review (consensus-critical
  core; not changed autonomously).
- **CoW self-netting LP fee+spread capture (O-SS-06 / H-MD-SS-007).** The
  experimental `swap_ordering == "cow_pair_netting_v1"` fills matched pairs at
  `fee_paid = 0` with no pool interaction, diverting fee+spread from LPs. CoW is
  **opt-in and disabled in production**: both authority configs (`DexConfig`,
  `DexEngineConfig`) default to `greedy_ab_refined`, and no shipped deploy config
  selects CoW. Containment is locked in behaviorally by
  `tests/integration/test_production_settlement_ordering_containment.py` (a pair
  that would CoW-net is routed through the pool under the default ordering, LPs
  earn the fee).
- **Improvement-bounty tie-break selectability (O-VM-03 / H-MD-VM-003).** Ties in
  the route-improvement bounty resolve by a submitter-chosen `miner_id`, so tie
  wins are costlessly selectable. The tie-break selector lives in **off-chain
  tooling** (`tools/gpu_jobs/improvement_bounty_round_route_v1.py`); it is not
  imported by, or reachable from, the spot/perp authority settlement computation
  or validation path. (Consensus code in `src/` does consume proof-mining claim
  artifacts under the same round schema, but not this winner-selection tie-break.)
  So it is a tooling-fairness consideration, not a consensus security exposure.

## Operator Notes

- Production/container builds should install with
  `python3 -m pip install --require-hashes -r requirements-core.lock.txt`.
- Local development should install with
  `python3 -m pip install --require-hashes -r requirements-dev.lock.txt`.
- For sensitive APIs, use `ZENODEX_EXTERNAL_AUTH_ENFORCED=1` for a real gateway
  or `ZENODEX_API_BEARER_TOKEN` for controlled local/testnet operators.
  The retired `DEMO_API_TOKEN` and `ALLOW_DEMO_TOKEN_AUTH` settings cause startup
  refusal and cannot re-enable the deleted compatibility surface.
- If Tau-backed gates are enabled in production, prefer absolute binary paths.
