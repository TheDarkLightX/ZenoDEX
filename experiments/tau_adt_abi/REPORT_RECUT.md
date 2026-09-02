# Tau ADT logical ABI V1 — re-cut of PR #534 (2026-09-02)

Branch `codex/tau-adt-logical-abi-recut-20260902` (single-parent child of PR #534's head `95b3cd6e1`).
Research-only; authority NONE. Numbers below are measured, not estimated.

## What the PR claimed and what replayed

| Item | Result |
|---|---|
| CI runs 211–214 | fail before Tau runs (in-gate source build; runner has no Boost.Log) |
| PR test unmodified at its exact pin `1c1e58ae` (local build 8 m 21 s via the PR's helper) | 1 failed, 1 passed: the asset `always` theorem raises `Unresolved function or predicate symbol min(b2, b1) found. Returning unsat` and still prints `%1: T`; the harness refuses on `(Error)` |
| Cause | `bounded_fee(required, cap):bv[16] := min(required, cap).` is echoed without its return annotation; `min` is reached untyped through `fee_within_cap` |
| Fix (this branch) | `fee_within_cap(required, cap) := (min(required:bv[16], cap:bv[16]) = required:bv[16]).` — always-theorem T with no errors at `1c1e58ae` and `3c24bad9`; strict variant F |
| The PR's theorems | definitional projections of their own predicates (review receipt F3); kept as 18 labelled capability probes, all pass at the pin with the fixed spec |

## Vector-bound tier (renderer v2)

- ADT declarations are read verbatim from the spec; the reject-code map is derived from
  `AssetTransferRejectCodeV1` declaration order (0 = accept, 1..12), and the spec's closed ceiling literal is
  pinned to the enum size.
- 26 vectors built by running the real Python transition: 24 recompute (9 reject classes + accept, guard-edge
  boundaries, 8 adjacent-pair precedence discriminators whose expected code comes from the oracle) and 2
  contract (host-produced `EFFECT_DELTA_OVERFLOW` from a `MAX_ATOMS_V1`-scale delta and
  `POST_STATE_RESOURCE_BOUND_EXCEEDED` from 4097 balance rows).
- Recompute program shape: `ex k ex c ex s ( bindings && all r ( chain(k,c,s,r) -> expected(r) ) )` plus a
  non-vacuity program `ex r ( chain )`; `expected` is built from the OBSERVED Python value (code,
  pre/post-root equality, effects emptiness). Contract shape: the observed record pinned member-for-member and
  checked by the spec's own `asset_transfer_result_ok` plus the expected code.
- Falsification selftest recorded in the receipt: wrong expectation → F; guard chain weakened to admit every
  result → F; contract record with the wrong code → F; contract record with effects not empty → F; broken
  program → FAIL_CLOSED.
- `BALANCE_OVERFLOW` is unreachable from a well-formed state (balances ≤ supply ≤ MAX) and has no vector.

## Results

| Binary | Vectors | Probes | Wall | Transcript sha256 |
|---|---|---|---|---|
| `1c1e58ae` (pin; sha `4be1965b…`) | 26/26 | 18/18 | 15 m 37 s | `cde873220eb96a54…` |
| `3c24bad9` (differential; sha `b62c0706f682d305…`) | 26/26 | n/a (interim renderer, vectors identical) | 15 m 8 s | `5620f3c61dbae0ed…` |
| Rust leg (real Rust transition, identical vectors) | 26/26 | n/a | < 1 s | committed `tests/data/tau_adt_logical_abi_rust_leg_v1.json` |

Python == Rust == Tau is therefore direct on these 26 vectors: the Rust leg agrees with the Python oracle
vector-for-vector, and every Tau program built from the Python observation answers T.

## Evidence contract

- The committed receipt `tests/data/tau_adt_logical_abi_replay_receipt_v1.json` is hash-bound to the asset
  spec, the journal spec, the lock and the renderer; `tests/tau/test_tau_adt_logical_abi_v1.py` verifies it
  offline (schema, ok, commit, verdicts, selftest, probes, coverage of all 11 reachable codes, Rust-leg
  agreement). Any edit to those bytes without a fresh receipt is red.
- Live execution is opt-in (`ZENO_TAU_ADT_LIVE=1`) and fails closed with `TAU_PIN_UNAVAILABLE` when the
  binary is absent. CI does not build Tau.

## Limits (deliberate)

- Bounded shadow domain bv[16]; roots are equality tags, not hashes; identities are tokens.
- Guard precedence in Tau is hand-mirrored and pinned by discriminators, not derived from the Python source.
- The contract tier checks the closed result algebra over a host-produced record, weaker than recomputation.
- Each universal program costs 15–90 s at this pin; a full run is 15–35 minutes.

## Engine facts recorded (PopperPad, domain tau-language)

- Default `charvar on` treats identifiers as single characters; `set charvar off` first.
- A return-annotated definition wrapper drops its annotation; `min` reached through it is unresolved.
- An unresolved symbol under `valid` yields an `(Error)` line AND a `T` verdict line; fail closed on `(Error)`.
