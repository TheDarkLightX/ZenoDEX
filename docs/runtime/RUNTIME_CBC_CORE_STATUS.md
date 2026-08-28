# Runtime CBC Core Status

> **Authority update (2026-07-22):** The score below is historical evidence
> inventory, not the current deployment decision. Public testnet now retains
> Rust authority with Python shadow only for the four surfaces graded full CBC
> here: replay guard, balances, fee router, and burn receipts. Canonical, CPMM,
> perps stateless/stateful, state root, and zUSD are Python authority. zUSD is
> additionally semantically stale against the total-debt-cap and finalized-
> Oracle relation. See `RUST_FCIS_BASELINE_20260722.json`.

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
| CPMM per-pool settlement | yes | yes | Kani on init/fail-closed/non-vacuity, malformed-fee and zero-denominator helper rejects, small-domain fee-ceil boundedness, and small-domain exact-in reserve shape. Full live-domain exact-in/out arithmetic remains outside Kani | unit k-invariant tests, Python/Rust differential, live path, disaster/fuzz, Tau/ESSO/Lean model evidence, exhaustive small-domain exact-in/out arithmetic grid, bounded Z3 fee-inversion and Lean exact-swap safety checks, plus Julia BigInt boundary witnesses replayed against Python quote logic and Rust `cpmm-op` | partial |
| Perp stateless math | yes | yes | Kani on checked materializer-effect helpers, bridge-domain classifiers, `abs_val` safety, oracle helper totality, sign classifiers, flat-position liquidation rejection, partial-liquidation boundary cases, and arith primitives. Full live-domain multiplication/division equivalence remains differential/property evidence | static and randomized Python/Rust differential, live path, disaster/fuzz, partial-close bounded-domain property tests | partial |
| Perp stateful isolated ops | yes | yes | Kani on `advance_epoch` and `publish_clearing_price` totality/accept shape/reachability, account-op domain plus deposit/withdraw/set-position/clear-breaker accept shape and reachability, settle-epoch helper classifiers, partial-liquidate boundary/full-close slice, set-market-params scalar/no-account overlay slice, plus funding-auto bounded-sink helpers. Other op wrappers remain differential/live-shadow covered | all 10 ops materialized, golden/live tests, security regressions, disaster/fuzz | partial |
| Canonical primitives | yes | yes | Kani on heap-free helper predicates: ASCII domain-label byte classifier, ASCII hex digit classifier, hex-nibble/pair decoding exactness, fixed-width hex length arithmetic, selected LEB128 length boundaries, and fixed-array uvarint helper totality/terminator shape. Full `Vec`/`String` encoders, SHA-256, and canonical JSON remain outside Kani | vectors, fuzz, state-root/receipt differential, live selector, exhaustive control-character JSON escape grid with independent encoder oracle, raw uvarint/encode-bytes framing grid with Rust parity | partial |
| State root v5 | yes | yes | Kani on scalar root-admission guards: pool fee bps, nonce bounds, LP duration metadata presence, decoded-byte pool-asset order, and pool-status code distinctness. Full section encoding, duplicate detection, BigUint curve-param parsing, and SHA-256 remain outside Kani | state-root differential, malformed/duplicate rejects, fuzz, live selector, LP duration-risk exhaustive field grid plus Z3 semantic injectivity, one-hot section-framing grid with strict decoder and Rust parity, curve-config normalization/BigUint parser grid | partial |
| zUSD single-vault | yes | yes | Kani on BigInt-free scalar risk helpers: oracle freshness, base-rate decay, fee cap, debt-floor guard, and liquidation compensation split totality/conservation on the runtime state domain. Full BigInt CDP ratio arithmetic and full `step` remain outside Kani | golden, Python/Rust differential, semantic invariants, disaster/fuzz, live selector, independent CDP threshold arithmetic grid plus bounded Lean boundary formula checks, liquidation compensation accounting grid with Rust parity | partial |

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
  This pass also added an independent arithmetic grid for the division-heavy
  formulas: 10,368 exact-in cases and 4,752 exact-out cases compare the Python
  authority to a standalone integer reference, a curated boundary subset matches
  Rust `cpmm-op`, Z3 checks the bounded exact-out fee-inversion identity for
  `1 <= net_in <= 200` and `0 <= fee_bps < 10000`, and Lean checks that same
  fee-inversion slice plus the bounded exact-in/exact-out accepted-case safety
  grids over the small runtime-test domain. It also adds a dependency-free
  Julia generator for 14 BigInt boundary witnesses across exact-in and
  exact-out: near-reserve max accept/reject, full-fee rejects, high-fee
  one-unit-net acceptance, overdelivery-gap accept/reject, amount-out-at-reserve
  rejection, slippage, and reserve-domain ordering. The witnesses replay
  through Python quote logic and Rust `cpmm-op`.
  Full live-domain exact-in/out division remains property/differential backed;
  direct public-swap and exact-out helper Kani attempts timed out under CBMC.
- Canonical primitives gained heap-free helper decomposition. Kani now proves
  the domain-label byte classifier, hex-digit byte classifier, fixed-width hex
  length arithmetic, exact hex-nibble/pair decoding, selected LEB128 length
  boundaries, and the heap-free fixed-array uvarint helper's totality/nonempty/
  bounded-length/final-byte terminator shape. `hex_to_bytes_fixed` now fails
  closed when an impossible requested width would overflow the expected length
  calculation and decodes validated fixed-width hex with the core's own checked
  pair decoder instead of delegating to the external `hex` decoder. Balance
  accounting and replay guard now use this canonical fixed-hex path for their
  root/receipt raw-byte lowering instead of local `hex::decode(...).expect(...)`
  calls. This pass also added an independent canonical JSON escape grid over every ASCII control byte,
  quote/backslash escapes, non-ASCII UTF-8, escaped object keys, key ordering,
  and nested values, comparing Python and Rust to a small reference encoder. It
  also added raw framing differential ops and an independent grid for unsigned
  LEB128 thresholds through `u128::MAX` plus length-prefixed byte strings at
  lengths 0, 1, 3, 127, 128, and 256. Full public `Vec`/`String` wrappers,
  SHA-256, and canonical JSON remain vector/fuzz/differential backed.
- State root gained hash-free scalar guard decomposition. Kani now proves the
  fee-bps guard, nonce guard, LP duration metadata presence predicate,
  decoded-byte pool-asset canonical order, equal-asset rejection, and pool
  status code domain/distinctness. This pass also added a deterministic
  LP duration-risk field grid: the sparse all-default metadata tuple is a no-op,
  the 80 present optional-field tuples produce distinct Python roots, Z3 proves
  semantic tuple injectivity for the optional-field shape, and Rust matches
  Python for all 80 present tuples. This pass also added a one-hot section
  framing grid using the strict preimage decoder: each v5 section changes
  exactly its own framed body relative to empty state, all one-hot roots are
  distinct, and Rust matches Python on the same section cases. It also added a
  curve-config grid for all supported curve tags, BigUint-sized canonical
  params, zero and nonzero reduced blend ratios, Python normalization collapse,
  and Rust rejection of raw non-normalized curve fields. Full section encoding,
  duplicate detection, BigUint curve-param parsing, and SHA-256 remain vector/
  fuzz/differential backed.
- zUSD gained BigInt-free scalar helper decomposition. Kani now proves oracle
  freshness, base-rate decay, effective fee capping, the debt-floor guard, and
  liquidation compensation split totality/conservation over the validated
  runtime state domain. The liquidation branch now uses the checked helper for
  `fixed + ceil(collateral * variable_bps / 10000)` before capping the
  liquidator compensation at the liquidated collateral, rather than relying on
  unchecked `u128` addition after BigInt helper conversion.
  This pass also added a non-Kani CDP threshold grid for the BigInt ratio
  boundary: mint, withdraw, redeem, and liquidation cases compare the Python
  authority to an independent integer oracle, a curated threshold subset matches
  Rust `zusd-op`, and Lean checks the finite boundary formula slice. It also
  added a liquidation compensation grid covering fixed compensation, variable
  compensation with ceiling behavior, compensation capped at full collateral,
  stability-pool cap reject/no-op behavior, and curated Rust `zusd-op` parity.
  Full BigInt CDP ratio arithmetic and full `step` remain vector/property/
  differential backed.
- Perp stateless math gained explicit bridge-domain classifiers and scalar
  helper decomposition. Kani now proves classifier exactness, `abs_val` safety
  under the bridge domain, oracle helper totality, exact sign predicates,
  flat-position liquidation rejection, checked-effect helper totality,
  partial-liquidation remaining-position boundary cases, and non-vacuity. A
  Rust property test now covers the bounded runtime-domain invariant that a
  partial close never increases position magnitude and preserves side direction
  until full close. Full symbolic live-domain multiplication/division for
  notional, PnL, funding, margin, and liquidation remains
  property/differential backed.
- Perp stateful gained Kani contracts on the two global-only ops:
  `advance_epoch` and `publish_clearing_price`. Kani now proves totality for any
  `i128` input struct, phase classifier exactness, accept-state shapes, and
  non-vacuity of accept/reject outcomes. Kani also now proves the account-op
  domain predicate is total, deposit/withdraw/set-position/clear-breaker accept
  shapes, and account-op accept/reject reachability for all four account-op
  arms. Set-market-params now has no-account no-op shape, funding-rate cap clamp
  shape, and scalar reachability contracts. Settle-epoch now has helper
  classifier contracts for phase admission, account domain, flat-account fast
  path, and the global guard. Partial-liquidate now has parameter-boundary,
  non-open guard, concrete full-close shape, and reachability contracts. Deep
  withdraw/set-position margin arithmetic implications, set-market account-safety
  scans, settle per-account PnL/liquidation accumulation, and partial-liquidate
  auto-fraction/liquidation arithmetic remain differential/live-shadow backed
  except for funding-auto's bounded-sink arithmetic.

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
   the division-heavy formula with a verified/generated arithmetic kernel. The
   Julia witnesses are replayable high-precision boundary evidence, not a proof
   layer. Keep public function parity locked by differential/property tests.
2. Continue canonical proof decomposition: public `Vec`/`String` wrapper
   allocation, `encode_bytes`, domain-separator construction, fixed-hex
   wrapper lowering, SHA-256, and canonical JSON remain outside Kani. The
   fixed-hex nibble and pair decoder is now machine-checked, but the public
   `hex_to_bytes_fixed` string/Vec wrapper remains covered by unit tests and
   Python/Rust replay. Keep SHA-256 and heap-heavy JSON as vector/differential
   evidence unless a tractable helper boundary is added.
3. Continue state-root proof decomposition: finite section encoder helpers,
   duplicate-key guards, and curve-config parsers remain outside Kani. Hashing
   and BTreeMap traversal should stay tested by vectors and differential checks
   unless a finite section encoder can be isolated. Pool asset ordering is now
   an explicit helper with a fixed-width Kani contract; full `PoolEntry`
   lowering still depends on hex decoding and heap-backed section assembly.
4. Continue zUSD proof decomposition: BigInt CDP ratio arithmetic, redemption
   selection, the full liquidation domain, and full `step` remain outside Kani.
   The CDP threshold grid, liquidation compensation grid, Kani compensation
   split helper, and Lean boundary slice cover high-value pieces; they do not
   prove the whole live `step`. Keep full `step` equality under Python/Rust
   differential until the BigInt core is generated or separately verified.
5. Extend perps Kani coverage from the current funding-auto, global-op,
   account-op accept-shape, settle-helper, partial-liquidate boundary, and
   set-market scalar slices into deep withdraw/set-position margin arithmetic
   implications, set-market account scans, settle per-account PnL/liquidation
   accumulation, and partial-liquidate auto-fraction/liquidation arithmetic,
   using the same assume-guarantee decomposition pattern. The
   remaining-position boundary cases are now Kani-checked, but the
   division-heavy partial-close arithmetic still relies on the bounded-domain
   property test and Python/Rust differential evidence.
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
Complete - 89 successfully verified harnesses, 0 failures, 89 total.
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
