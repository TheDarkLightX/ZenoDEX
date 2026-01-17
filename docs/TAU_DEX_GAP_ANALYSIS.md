# TauSwap Tau Spec Gap Analysis

This document maps current Tau specs to DEX requirements, identifies expressiveness gaps, and lists external computation needs for Tau Net Alpha.

## Current Tau Specs (as of this repo)
- `cpmm_v1.tau`: basic swap admissibility (fee bounds, positivity, `amount_out <= reserve_out`).
- `swap_exact_in_v1.tau`: exact-in swap bounds, slippage, and reserve transition checks.
- `swap_exact_out_v1.tau`: exact-out swap bounds, slippage, and reserve transition checks.
- `balance_safety_v1.tau`: non-negativity of balance/delta limbs.
- `balance_transition_v1.tau`: checks `balance_after = balance_before + delta_add - delta_sub` using 32-bit limbs.
- `batching_v1.tau`, `batching_v1_4.tau`: deterministic ordering of intents.
- `batch_canonical_v1_4.tau`: canonical batch encoding.
- `protocol_token_v1.tau`: transfer/mint/burn transitions for a 32-bit token.
- `tokenomics_buyback_burn_v1.tau`: fee split and buyback/burn bounds.

## Expressiveness Gaps (Requires External Computation)
- **256-bit arithmetic**: swaps, LP math, and reserve invariants exceed 32-bit widths.
- **Division / sqrt / ratios**: CPMM pricing, LP minting, and slippage checks depend on division and sqrt.
- **Cryptography**: signatures, hashing, intent IDs, pool IDs, and canonical JSON.
- **Table state**: account balances, pools, and intents are naturally tables (not in current parser grammar).

## Specs Still Needed for a “Complete” DEX
1. **Liquidity add/remove**
   - Validate `lp_minted`, `amount_used`, `amount_out` vs. reserves and supply.
   - Requires external math; Tau checks bounds and monotone transitions.
2. **Global conservation**
   - Sum of account deltas + pool deltas per asset equals zero.
   - Practical only with fixed-size witness lists or external aggregation proof.
3. **Intent validation**
   - One-hot intent type, parameter bounds, deadline checks, and fee caps.
   - Signature and hash validation must be external.
4. **Settlement-level checks**
   - Each intent appears exactly once; fill/reject consistency.
   - Requires a canonical “intent list” interface and batch encoding.

## Integration Requirements for Tau Net Alpha
- **Extralogical API**: implement CPMM math, LP math, signature checks, hashing, and batch sorting externally; provide witness limbs to Tau.
- **State encoding**: define tables for pools, balances, LP supply, and intent queues; canonicalize keys.
- **Deterministic batching**: enforce canonical ordering (already constrained by Tau) and provide executed order as witness.
- **Constraint aggregation**: produce per-intent and per-pool witnesses for Tau to validate.

## Near-Term Actions
- Expand Tau specs for liquidity actions and settlement aggregation (bounded witnesses).
- Define the DEX transaction/intent schema and the exact witness values passed into Tau.
- Add a “Tau validation harness” in Python to emit Tau inputs and check outputs.
