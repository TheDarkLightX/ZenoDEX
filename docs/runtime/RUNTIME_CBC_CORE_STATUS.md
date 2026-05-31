# Runtime CBC Core Status

Date: 2026-05-31

This document states the current correctness-by-construction status of the
required ZenoDEX trusted runtime core. It separates authority promotion from
proof grade so a surface is not overcounted just because it is live-wired.

## CBC Grade Definition

For this repo, a runtime surface is CBC-grade only when all of these hold:

1. The trusted transition is in the Rust functional core or generated from a
   verified artifact.
2. The public-testnet authority path is `rust_authority_with_python_shadow`, or
   the surface is an internal helper called by such a path.
3. There is a machine-checked implementation contract on the actual Rust core
   with a replayable receipt, or generated Rust with a replayable verified-model
   receipt.
4. Wrapper and serialization behavior is covered by Python/Rust differentials,
   golden vectors, property tests, and fail-closed deployment/profile checks.
5. The receipt states the remaining model-to-code and wrapper assumptions.

Lean, ESSO, Tau, and TLA artifacts prove or search the intended model. Kani
proves local contracts about the Rust implementation that actually runs. A
surface reaches full CBC grade only when the model evidence and implementation
evidence are both linked to the authority path.

## Current Score

Public-testnet Rust authority coverage:

```text
10 / 10 promoted public-testnet trusted-core surfaces are live as
rust_authority_with_python_shadow.
```

CBC-grade implementation coverage:

```text
4 / 10 promoted public-testnet surfaces are full CBC-grade by the definition
above: replay guard, balance accounting, fee router, burn rails.
```

Partial CBC coverage:

```text
3 / 10 promoted public-testnet surfaces have machine-checked sub-core evidence
but still rely on property/differential evidence for a larger wrapper or
arithmetic slice: CPMM per-pool settlement, perp stateless math, perp stateful.
```

Tested authority coverage:

```text
3 / 10 promoted public-testnet surfaces are authority-wired and heavily tested,
but do not yet have Kani or generated-code evidence on the running Rust core:
canonical primitives, state root v5, zUSD single-vault.
```

Conservative completion estimate for the full CBC-core goal:

```text
Authority wiring: 100% for promoted public-testnet core surfaces.
CBC-grade proof linkage: about 40% by surface count.
Defensive hardening and fail-closed coverage: about 70% by promoted-surface
count, lower if weighted by complexity because zUSD, state root, CPMM arithmetic,
and perps wrappers remain large.
```

## Surface Matrix

| Surface | Public-testnet authority | Rust core | Machine-checked implementation evidence | Wrapper / differential evidence | CBC grade |
|---|---:|---:|---|---|---|
| Replay guard | yes | yes | Kani on `classify_sequence`: totality, accept iff strict successor, reject codes, non-vacuity | golden, Python/Rust differential, disaster/fuzz, selector tests | full |
| Balance accounting | yes | yes | Kani on transfer/credit arithmetic: totality, exact move, conservation, overflow, non-vacuity | golden, Python/Rust differential, disaster/fuzz, selector tests | full |
| Fee router | yes | yes | Kani on split/dust core plus ESSO finite model and generated Rust receipt for the 4-way dust core | property tests, differential, live path, disaster/fuzz | full |
| Burn rails | yes | yes | Kani on `verify_rails`: totality, accepted budget/supply/batch conservation, non-vacuity | burn receipt differential, live path, disaster/fuzz | full |
| CPMM per-pool settlement | yes | yes | Kani on init/fail-closed/non-vacuity, malformed-fee and zero-denominator helper rejects, small-domain fee-ceil boundedness, and small-domain exact-in reserve shape. Full live-domain exact-in/out arithmetic remains outside Kani | unit k-invariant tests, Python/Rust differential, live path, disaster/fuzz, Tau/ESSO/Lean model evidence | partial |
| Perp stateless math | yes | yes | Kani on checked materializer-effect helpers and arith primitives. Full equivalence to plain helpers remains differential/property evidence | static and randomized Python/Rust differential, live path, disaster/fuzz | partial |
| Perp stateful isolated ops | yes | yes | Kani on funding-auto bounded-sink helpers. Other op wrappers remain differential/live-shadow covered | all 10 ops materialized, golden/live tests, security regressions, disaster/fuzz | partial |
| Canonical primitives | yes | yes | no Kani receipt yet on running primitive encoders | vectors, fuzz, state-root/receipt differential, live selector | tested authority |
| State root v5 | yes | yes | no Kani receipt yet on running root encoder/hash wrapper | state-root differential, malformed/duplicate rejects, fuzz, live selector | tested authority |
| zUSD single-vault | yes | yes | no Kani receipt yet on running BigInt-heavy `step` | golden, Python/Rust differential, semantic invariants, disaster/fuzz, live selector | tested authority |

## Current Delta From This Pass

This pass moved two surfaces forward:

- Burn rails moved from tested authority to full CBC grade for the rail core.
  Evidence: `docs/runtime/receipts/cbc_runtime_core_kani_v1/` now records
  `burn_receipts::kani_contracts::*`.
- CPMM gained helper decomposition for exact-in/exact-out arithmetic, explicit
  malformed-fee validation before swap math, and checked multiply/divide helper
  boundaries. Kani now proves initialization, uninitialized swap fail-closed
  behavior, invalid-fee and zero-denominator helper behavior, small-domain
  fee-ceil boundedness, small-domain exact-in reserve shape, and non-vacuity.
  Full live-domain exact-in/out division remains property/differential backed;
  direct public-swap and exact-out helper Kani attempts timed out under CBMC.

This pass also integrated four open security PR fixes onto the branch:

- partial-liquidate Rust-authority unknown-field validation;
- clear-breaker Rust-authority unknown-field validation;
- delayed oracle fact computation until after Python authorization in shadow
  mode;
- apply-funding-auto liquidation-flag parity.

The older funding PR branch is superseded by the stronger funding fix that
includes the live-shadow regression.

## Remaining Work To Reach 100 Percent CBC Grade

1. Continue CPMM proof decomposition: either split exact-out further or replace
   the division-heavy formula with a verified/generated arithmetic kernel. Keep
   public function parity locked by differential/property tests.
2. Add Kani contracts for canonical primitive helpers that are tractable:
   uvarint length/roundtrip properties over bounded domains, domain-separator
   preconditions, and fixed-hex validation. Keep SHA-256 and heap-heavy JSON as
   vector/differential evidence unless a tractable helper boundary is added.
3. Add Kani or codegen/refinement evidence for state-root section encoders.
   Hashing and BTreeMap traversal should stay tested by vectors and differential
   checks unless a finite section encoder can be isolated.
4. Split zUSD into Kani-checkable scalar guards and BigInt policy helpers. Keep
   full `step` equality under Python/Rust differential until the BigInt core is
   generated or separately verified.
5. Extend perps Kani coverage from funding-auto sub-core to account ops,
   publish/advance, set-market-params, partial-liquidate, and settle helper
   contracts, using the same assume-guarantee decomposition pattern.
6. Close or merge the original GitHub PRs after this integrated branch lands, so
   duplicate open PRs do not linger as misleading security debt.

## Evidence Commands

Latest checked commands for this status:

```bash
cd rust-runtime/crates/zenodex-runtime-core
cargo kani --lib --output-format terse -j 4 --harness-timeout 10m -Z unstable-options
```

Result:

```text
Manual Harness Summary:
Complete - 35 successfully verified harnesses, 0 failures, 35 total.
```

Focused tests after integrating the security fixes:

```bash
cargo test -q -p zenodex-runtime-core
cargo test -q -p zenodex-runtime-cli perp_isolated_op
python3 -m pytest -q tests/runtime/test_perp_stateful_live_shadow.py
python3 -m pytest -q tests/integration/test_perp_engine.py tests/integration/test_perp_engine_partial_liquidate.py
cargo fmt --check
cargo clippy --workspace --all-targets -- -D warnings
python3 tools/check_deployment_profiles.py
git diff --check
```

All passed in this pass.
