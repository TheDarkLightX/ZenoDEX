# zUSD RISC0 Minimum-Profile Integrity Repair

Date: 2026-07-17
Profile: `zenodex/zusd-liquity-v1-minimum`
Status: implementation submitted; release evidence pending

## Findings

The direct zUSD RISC0 guest previously delegated immediately to the scoped
`DepositMint` helper. That helper checked the sum of imported vault debt, but it
did not check the sum of imported zUSD balances. A malformed snapshot could
therefore begin with more or less scoped zUSD supply than scoped debt and still
produce a transition journal after minting equal deltas on top of the mismatch.

The same proof input accepted every caller-selected `mcr_bps` value above
10,000. That is a valid configurable arithmetic experiment, but it is not the
source-pinned Liquity V1 minimum profile, whose MCR is exactly 11,000 basis
points. A stronger caller-selected value is also not interchangeable because it
changes the transition relation and theorem identity.

Finally, `pre_app_hash_present = false` allowed the direct guest to omit the
canonical prestate comparison. The resulting journal committed a zero/absent
prestate marker instead of proving continuity from one exact mounted prestate.

## Repair

The guest now executes a small pure admission kernel before the scoped
transition:

```text
input
  -> require snapshot version 1
  -> require pre_app_hash_present
  -> require mcr_bps = 11000
  -> checked sum(vault debt) = declared total debt
  -> checked sum(balance supply) = declared total debt
  -> execute existing scoped transition
  -> commit journal
```

The admission check deliberately repeats debt conservation even though the
lower helper also checks it. Proof authority is narrower than helper
applicability: a future relaxation of a reusable helper must not silently widen
the guest's authoritative language.

## Mechanical guarantees

- Balance and debt sums use checked `u128` arithmetic.
- Any mismatch or overflow aborts before state transition or journal creation.
- The pinned minimum-profile MCR cannot be weakened, strengthened, or selected
  by the caller.
- Every authoritative direct zUSD proof requires an exact canonical prestate
  hash; the existing transition helper performs the equality check after
  admission.
- The kernel is deterministic, immutable, free of I/O, and separately testable
  from the imperative RISC0 entrypoint.

## Explicit nonclaims

This repair does not make `DepositMint` a complete zUSD protocol proof. It does
not prove governed policy provenance, oracle reporter authorization or truth,
borrowing fees, gas-pool reserve issuance, Stability Pool state, redistribution,
redemption, owner close, shutdown, cross-module custody, or mounted Python/Rust
refinement. Those surfaces must remain outside the proof's public authority
until separately bound.
