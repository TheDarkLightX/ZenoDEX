# Tau DEX Readiness (2025-12-20)

This report answers: **Do we have enough to build a DEX on Tau Net Alpha?**
It uses the formal completeness tool: `tests/tau/check_formal_completeness.py`.

## Current Completeness Snapshot

```
python3 tests/tau/check_formal_completeness.py --summary --lint-only
```

- **Complete**: 130 specs
- **Incomplete**: 10 specs

## Core DEX Logic (src/tau_specs)

**Complete (ready):**
- `src/tau_specs/cpmm_v1.tau`
- `src/tau_specs/batching_v1.tau`
- `src/tau_specs/batching_v1_4.tau`
- `src/tau_specs/batch_canonical_v1_4.tau`
- `src/tau_specs/balance_safety_v1.tau`
- `src/tau_specs/balance_transition_v1.tau`
- `src/tau_specs/swap_exact_in_v1.tau`
- `src/tau_specs/swap_exact_out_v1.tau`
- `src/tau_specs/tokenomics_buyback_burn_v1.tau`
- `src/tau_specs/protocol_token_v1.tau`
- `src/tau_specs/settlement_v1.tau`
- `src/tau_specs/tdex_buyback_pulsex_v1.tau`
- `src/tau_specs/settlement_v2_buyback.tau`
- `src/tau_specs/tdex_buyback_floor_v1.tau`
- `src/tau_specs/tdex_buyback_floor_fixedpoint_v1.tau`
- `src/tau_specs/tdex_fee_rebate_v1.tau`
- `src/tau_specs/tdex_lock_weight_v1.tau`
- `src/tau_specs/settlement_v3_buyback_floor.tau`
- `src/tau_specs/settlement_v4_buyback_floor_rebate_lock.tau`
- `src/tau_specs/revision_policy_v1.tau`
- `src/tau_specs/parameter_registry_v1.tau`
- `src/tau_specs/governance_timelock_v1.tau`

**Incomplete (non-blocking for core DEX):**
- See formal completeness summary for the remaining experimental composites.

## Verified Specs (experiments/)

The "verified" set is now **formally complete** per the tool:
- `experiments/23_minimal_verified.tau`
- `experiments/24_temporal_verified.tau`
- `experiments/25_complete_verified_dex.tau`
- `experiments/35_circuit_breaker.tau`
- `experiments/36_median_oracle.tau`
- `experiments/37_adaptive_fee.tau`
- `experiments/38_composite_dex_gate.tau`

## Decision: Are We Ready to Build on Tau Net Alpha?

**Answer:** **Yes for core DEX + buyback/burn.** We now have complete specs for swap validation, balances, protocol token transitions, and settlement (with and without buyback burn). We can proceed with Tau Net Alpha integration using `settlement_v1.tau` (core) or `settlement_v2_buyback.tau` (PulseX-style buyback). The new fee-rebate and lock-weight specs are complete but not yet wired into settlement.

## Immediate Next Actions

1. Decide whether to integrate `tdex_fee_rebate_v1.tau` and `tdex_lock_weight_v1.tau` into a `settlement_v4_*` composite.
2. Extend `settlement_v3_buyback_floor.tau` with fixed-point unit checks (`tdex_buyback_floor_fixedpoint_v1.tau`).
3. For incomplete experiments, prioritize fixes for `experiments/20_ultimate_dex.tau` and `experiments/39_frontier_composite_dex.tau`.
4. Keep a short trace-test for each new spec (1-2 hand-checked cases).
5. Re-run completeness lint after each spec change.

## Notes on Tokenomics Extensions
- Fee rebate validation is available in `tdex_fee_rebate_v1.tau` (basis-points rounding gate + cap).
- Lock-duration weighting is available in `tdex_lock_weight_v1.tau` (tiered weights + weighted stake check).
- Fixed-point + floor constraints are combined in `tdex_buyback_floor_fixedpoint_v1.tau`.
   - balance safety + transition
   - swap exact in/out
   - protocol token validation
3. Validate this with the formal completeness tool and a short truth-table trace.
