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
6 / 10 promoted public-testnet surfaces have machine-checked sub-core evidence
but still rely on property/differential evidence for a larger wrapper or
arithmetic/encoder slice: canonical primitives, CPMM per-pool settlement, perp
stateless math, perp stateful, state root v5, zUSD single-vault.
```

Tested authority coverage:

```text
0 / 10 promoted public-testnet surfaces are authority-wired and heavily tested
without any Kani or generated-code evidence on the running Rust core.
```

Conservative completion estimate for the full CBC-core goal:

```text
Authority wiring: 100% for promoted public-testnet core surfaces.
CBC-grade proof linkage: about 40% by surface count.
Machine-checked sub-core linkage: 100% by surface count.
Defensive hardening and fail-closed coverage: about 85% by promoted-surface
count, lower if weighted by complexity because zUSD, state root, canonical
encoders, CPMM arithmetic, and perps wrappers remain large.
```

## Surface Matrix

| Surface | Public-testnet authority | Rust core | Machine-checked implementation evidence | Wrapper / differential evidence | CBC grade |
|---|---:|---:|---|---|---|
| Replay guard | yes | yes | Kani on `classify_sequence`: totality, accept iff strict successor, reject codes, non-vacuity | golden, Python/Rust differential, disaster/fuzz, selector tests | full |
| Balance accounting | yes | yes | Kani on transfer/credit arithmetic: totality, exact move, conservation, overflow, non-vacuity | golden, Python/Rust differential, disaster/fuzz, selector tests | full |
| Fee router | yes | yes | Kani on split/dust core plus ESSO finite model and generated Rust receipt for the 4-way dust core | property tests, differential, live path, disaster/fuzz | full |
| Burn rails | yes | yes | Kani on `verify_rails`: totality, accepted budget/supply/batch conservation, non-vacuity | burn receipt differential, live path, disaster/fuzz | full |
| CPMM per-pool settlement | yes | yes | Kani on init/fail-closed/non-vacuity, malformed-fee and zero-denominator helper rejects, small-domain fee-ceil boundedness, and small-domain exact-in reserve shape. Full live-domain exact-in/out arithmetic remains outside Kani | unit k-invariant tests, Python/Rust differential, live path, disaster/fuzz, Tau/ESSO/Lean model evidence | partial |
| Perp stateless math | yes | yes | Kani on checked materializer-effect helpers, bridge-domain classifiers, `abs_val` safety, oracle helper totality, sign classifiers, flat-position liquidation rejection, and arith primitives. Full live-domain multiplication/division equivalence remains differential/property evidence | static and randomized Python/Rust differential, live path, disaster/fuzz | partial |
| Perp stateful isolated ops | yes | yes | Kani on `advance_epoch` and `publish_clearing_price` totality/accept shape/reachability, account-op domain/deposit/clear-breaker tractable slice, settle-epoch helper classifiers, partial-liquidate boundary/full-close slice, set-market-params scalar/no-account overlay slice, plus funding-auto bounded-sink helpers. Other op wrappers remain differential/live-shadow covered | all 10 ops materialized, golden/live tests, security regressions, disaster/fuzz | partial |
| Canonical primitives | yes | yes | Kani on heap-free helper predicates: ASCII domain-label byte classifier, ASCII hex digit classifier, fixed-width hex length arithmetic, and selected LEB128 length boundaries. Full `Vec`/`String` encoders, SHA-256, and canonical JSON remain outside Kani | vectors, fuzz, state-root/receipt differential, live selector | partial |
| State root v5 | yes | yes | Kani on scalar root-admission guards: pool fee bps, nonce bounds, LP duration metadata presence, and pool-status code distinctness. Full section encoding, duplicate detection, BigUint curve-param parsing, and SHA-256 remain outside Kani | state-root differential, malformed/duplicate rejects, fuzz, live selector, LP duration-risk exhaustive field grid plus Z3 semantic injectivity | partial |
| zUSD single-vault | yes | yes | Kani on BigInt-free scalar risk helpers: oracle freshness, base-rate decay, fee cap, and debt-floor guard. Full BigInt CDP ratio arithmetic and full `step` remain outside Kani | golden, Python/Rust differential, semantic invariants, disaster/fuzz, live selector | partial |

## Current Delta From This Pass

This campaign moved seven surfaces forward:

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
- Canonical primitives gained heap-free helper decomposition. Kani now proves
  the domain-label byte classifier, hex-digit byte classifier, fixed-width hex
  length arithmetic, and selected LEB128 length boundaries. `hex_to_bytes_fixed`
  now fails closed when an impossible requested width would overflow the expected
  length calculation. Full canonical `Vec`/`String` encoders, SHA-256, and
  canonical JSON remain vector/fuzz/differential backed.
- State root gained hash-free scalar guard decomposition. Kani now proves the
  fee-bps guard, nonce guard, LP duration metadata presence predicate, and pool
  status code domain/distinctness. This pass also added a deterministic
  LP duration-risk field grid: the sparse all-default metadata tuple is a no-op,
  the 80 present optional-field tuples produce distinct Python roots, Z3 proves
  semantic tuple injectivity for the optional-field shape, and Rust matches
  Python for all 80 present tuples. Full section encoding, duplicate detection,
  BigUint curve-param parsing, and SHA-256 remain vector/fuzz/differential
  backed.
- zUSD gained BigInt-free scalar helper decomposition. Kani now proves oracle
  freshness, base-rate decay, effective fee capping, and the debt-floor guard.
  Full BigInt CDP ratio arithmetic and full `step` remain vector/property/
  differential backed.
- Perp stateless math gained explicit bridge-domain classifiers and scalar
  helper decomposition. Kani now proves classifier exactness, `abs_val` safety
  under the bridge domain, oracle helper totality, exact sign predicates,
  flat-position liquidation rejection, checked-effect helper totality, and
  non-vacuity. Full symbolic live-domain multiplication/division for notional,
  PnL, funding, margin, and liquidation remains property/differential backed.
- Perp stateful gained Kani contracts on the two global-only ops:
  `advance_epoch` and `publish_clearing_price`. Kani now proves totality for any
  `i128` input struct, phase classifier exactness, accept-state shapes, and
  non-vacuity of accept/reject outcomes. Kani also now proves the account-op
  domain predicate is total, deposit accept shape, clear-breaker accept shape,
  and account-op accept/reject reachability. Set-market-params now has no-account
  no-op shape, funding-rate cap clamp shape, and scalar reachability contracts.
  Settle-epoch now has helper classifier contracts for phase admission, account
  domain, flat-account fast path, and the global guard. Partial-liquidate now
  has parameter-boundary, non-open guard, concrete full-close shape, and
  reachability contracts. Withdraw and set-position margin paths,
  set-market account-safety scans, settle per-account PnL/liquidation
  accumulation, and partial-liquidate auto-fraction/liquidation arithmetic remain
  differential/live-shadow backed except for funding-auto's bounded-sink
  arithmetic.

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
2. Continue canonical proof decomposition: full `encode_uvarint`,
   `encode_bytes`, domain-separator construction, fixed-hex decoding, SHA-256,
   and canonical JSON remain outside Kani. Keep SHA-256 and heap-heavy JSON as
   vector/differential evidence unless a tractable helper boundary is added.
3. Continue state-root proof decomposition: finite section encoder helpers,
   duplicate-key guards, and curve-config parsers remain outside Kani. Hashing
   and BTreeMap traversal should stay tested by vectors and differential checks
   unless a finite section encoder can be isolated.
4. Continue zUSD proof decomposition: BigInt CDP ratio arithmetic, redemption
   selection, liquidation arithmetic, and full `step` remain outside Kani. Keep
   full `step` equality under Python/Rust differential until the BigInt core is
   generated or separately verified.
5. Extend perps Kani coverage from the current funding-auto, global-op,
   account-op, settle-helper, partial-liquidate boundary, and set-market scalar
   slices into withdraw/set-position margin paths, set-market account scans,
   settle per-account PnL/liquidation accumulation, and partial-liquidate
   auto-fraction/liquidation arithmetic, using the same assume-guarantee
   decomposition pattern.
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
Complete - 78 successfully verified harnesses, 0 failures, 78 total.
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
