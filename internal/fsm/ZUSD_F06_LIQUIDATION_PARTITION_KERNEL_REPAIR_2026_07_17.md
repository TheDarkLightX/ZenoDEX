# zUSD F06 Liquidation Partition Kernel Repair

Date: 2026-07-17
Profile: `zenodex/zusd-liquity-v1-minimum`
Status: unmounted arithmetic kernel; composition and migration remain blocked

## Result sought

Close the arithmetic portion of `ZUSD-SP-002` without granting a local helper
authority over liquidation eligibility, vault selection, Stability Pool
accumulators, Default Pool redistribution, custody, or settlement.

## ShapeForge working model

```text
Phi := <
  M   = zenodex_world_model.seed.json,
  S   = F06 ordinary liquidation offset and redistribution partition,
  A   = Stability Pool capacity relative to liquidated debt,
  T   = one exact, exhaustive, immutable debt/collateral partition,
  V   = liquidated debt, post-keeper collateral, SP principal,
  O   = compute_liquity_v1_liquidation_partition,
  G   = positive U256 debt and nonnegative U256 collateral/principal,
  Obs = offset debt, SP collateral, redistributed debt/collateral, branch,
  K   = no selector key in this slice,
  E   = pinned source + ESSO bounded proof + Lean arithmetic + differential tests,
  Gap = no F04/F05/F19/F17/F16 composition or runtime mount,
  N   = full-SP-only liquidation rejects source-valid partial offsets,
  Delta = make the complete ordinary partition representable and checked
>
```

## Source and existing evidence

- Liquity V1 pin:
  `liquity/dev@8f52f2906f99414c0b1c3a84c95c74c319b7a8c6`
- Source function: `TroveManager._getOffsetAndRedistributionVals`
- Normative design:
  `ZUSD_LIQUITY_V1_MINIMUM_CONFORMANCE_V2_2026_07_16.md` section 9
- BDD witness: `ZUSD-SP-002`
- ESSO IR:
  `internal/fsm/esso/liquity_v1_sp_offset_redistribution_bounded.yaml`
- Existing ESSO result: Z3 and CVC5 agree on both inductive obligations over
  the declared `0..4` bounded domain.

## Refactoring preflight

### Artifact and authority

- New core file owns only the arithmetic partition.
- It is a pure deterministic projection with no shell or commit authority.
- Strongest pre-change evidence is bounded ESSO verification.

### Construction and ownership

- Inputs and plans are frozen dataclasses containing integers and an enum only.
- Exact-type checks reject Boolean/integer aliases.
- The plan constructor rechecks every derived field and conservation identity,
  so a forged or modified plan is not representable through normal construction.

### Semantics

For debt `d > 0`, post-keeper collateral `c`, and SP principal `D`:

```text
d_offset        = min(d, D)
c_sp            = floor(c * d_offset / d)
d_redistributed = d - d_offset
c_redistributed = c - c_sp
```

The branch sum is exhaustive:

```text
D = 0       -> FullRedistribution
0 < D < d   -> PartialOffsetAndRedistribution
D >= d      -> FullOffset
```

All persisted inputs and outputs are U256. The multiplication is checked in
the U512 domain. There are no floats, clamps, implicit defaults, or mutable
collections.

### Encoding and proof binding

- This slice defines no live encoding or receipt.
- The profile and source formula are fixed properties, not caller-selected
  fields.
- A future F06 receipt must additionally bind actor, vault, pre-root, oracle,
  risk-mode decision, keeper compensation, surplus, accumulator inputs,
  post-roots, and the complete effect-plan root.

### Commit and failure model

- No commit occurs here.
- Invalid construction raises before a candidate plan exists.
- Live use remains blocked until one F16 atomic composition commits F04, F05,
  F19, F17, F21, nonce/nullifier, receipt, and outbox effects together.

## Evidence plan

1. Regenerate the bounded Rust and Python references from the ESSO IR.
2. Differentially compare the typed Python projection over the complete ESSO
   input domain.
3. Test all branches, exact-type rejection, forged-plan rejection, and U256
   boundary multiplication.
4. Prove unbounded natural-number debt and collateral partition identities in
   Lean with no placeholders.
5. Run generated Rust tests, Python tests, Lean check, Ruff, Mypy, and scoped
   diff checks.

## Explicit nonclaims

- No claim of complete Liquity V1 liquidation.
- No claim that the generated `i128` bounded Rust kernel is production U256
  runtime code.
- No proof of Recovery Mode liquidation bands or capped liquidation.
- No proof of P/S/G or L accumulator updates and their feedback errors.
- No runtime-to-spec or shell refinement claim.
- No production mount or UI change.
