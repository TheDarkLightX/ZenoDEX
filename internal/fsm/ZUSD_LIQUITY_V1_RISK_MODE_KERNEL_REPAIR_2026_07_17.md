# zUSD Liquity V1 Exact Risk-Mode Kernel Repair

Date: 2026-07-17
Profile: `zenodex/zusd-liquity-v1-minimum`
Status: pure profile kernel and theorem evidence added; mounted profile binding pending

## Finding

The existing generic SimplexBorrow-style helper derives TCR from:

```text
vault collateral + Stability Pool collateral + protocol collateral
```

That is not the adopted Liquity V1 minimum relation. Source-pinned Liquity V1
uses only the Active Pool and Default Pool debt and collateral when deriving
system TCR and Recovery Mode. Stability Pool, Gas Pool, borrower-surplus,
wallet, and fee custody balances do not become risk-bearing system collateral.

Changing the generic helper would silently change its broader mathematical
profile. The repair therefore introduces a separately typed Liquity-minimum
kernel rather than relabeling or narrowing the generic helper.

## Exact relation

```text
total_collateral_source = active_collateral_source + default_collateral_source
total_debt_source       = active_debt_source + default_debt_source

if total_debt_source = 0:
    tcr_e18 = MAX_U256
    mode = Normal
else:
    tcr_e18 = floor(
        total_collateral_source * price_source_e18 / total_debt_source
    )
    mode = Recovery iff tcr_e18 < 15000 * 10^14
```

The comparison occurs at exact E18 precision. Flooring to basis points before
branch selection is forbidden.

## Type and arithmetic boundary

- Collateral source atoms, zUSD source atoms, and E18 price are distinct frozen
  nominal values.
- Persisted inputs and outputs are checked U256 values.
- Aggregate additions downcast to U256 only after an exact intermediate.
- Collateral-price and ratio products are bounded in U512 before division.
- The risk state type contains only Active and Default Pool fields, so excluded
  custody cannot enter the aggregate by configuration or a caller-selected flag.
- Mode is derived output, never stored state.
- The decision constructor recomputes collateral value, TCR, and mode so a
  forged inconsistent decision is not normally constructible.

## Evidence

- Python scenario and boundary tests cover the total partition, exact CCR
  boundary, Active+Default aggregation, nominal type separation, E18 precision,
  aggregate overflow, and forged decision rejection.
- `Proofs/ZUSDLiquityV1RiskMode.lean` proves totality, zero-debt Normal mode,
  below-CCR Recovery, at-or-above-CCR Normal, exact Active+Default aggregation,
  exact E18 ratio preservation, and the adopted boundary examples.

## Explicit nonclaims

- This slice does not mount the kernel into F04/F23 or consume a one-use risk
  decision receipt.
- It does not authenticate the oracle, policy, authority, command, or composite
  prestate roots.
- It does not implement the liquidation sequence's sticky Recovery-to-Normal
  tracker.
- It does not prove U512 correspondence to a Rust implementation or RISC0 guest.
- The generic `src/core/zusd.py` risk helper remains a separate nonbaseline
  SimplexBorrow-style relation and must not inherit this profile's claims.
