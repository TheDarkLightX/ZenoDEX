# Perps Mechanism Spec (Morph Mechanical Scientist)

This spec is generated from Morph A/B evidence and defines which incentive/game-theory clauses are eligible for promotion.

## Evidence Tiers

| Domain | Status | has_lift_rate | solved_rate_delta | avg_seconds_reduction | Artifact |
|---|---:|---:|---:|---:|---|
| `perp_oracle_manipulation_reward_subsidy` | `promote` | 100.0% | 0.000 | 0.030217 | `runs/mech_sci_iter/loop_ab_r13_reward/perp_oracle_manipulation_reward_subsidy/ab_sweep.json` |
| `perp_oracle_manipulation_lp` | `explore` | 50.0% | 0.000 | 0.004749 | `runs/mech_sci_iter/loop_ab_r17_lp_reward/perp_oracle_manipulation_lp/ab_sweep.json` |
| `perp_settlement_bounty_farming` | `hold` | 75.0% | 0.000 | -0.000099 | `runs/mech_sci_iter/loop_ab_r18_exotic/perp_settlement_bounty_farming/ab_sweep.json` |
| `perp_funding_rate_gaming` | `hold` | 12.5% | 0.000 | -0.000072 | `runs/mech_sci_iter/loop_ab_r18_exotic/perp_funding_rate_gaming/ab_sweep.json` |
| `perp_oracle_manipulation` | `explore` | 30.0% | 0.000 | 0.000155 | `runs/mech_sci_iter/loop_ab_r8/perp_oracle_manipulation/ab_sweep.json` |
| `perp_collateral_depeg` | `hold` | 0.0% | 0.000 | -0.000044 | `runs/mech_sci_iter/spec_design_probe/perp_collateral_depeg/ab_sweep.json` |

## Required Protocol Guarantees

- `C-USD-1` (required): **Collateral Value Floor**. Perp collateral is valued with deterministic haircut bands; opening/increasing positions must use haircut-adjusted collateral, not nominal quote balances.
- `C-ORACLE-1` (required): **Signed + Fresh Oracle Inputs**. Clearing-price publication requires authorized signature + nonce + positive price; all position/funding state transitions fail closed on stale or non-positive index price.
- `C-RWD-1` (required): **Reward Source Non-Recapturable**. Any subsidy/rebate must be bounded by extracted protocol fees and never by recapturable LP fees or raw reported volume.
- `C-LP-1` (required): **Attacker-As-LP Cost Model**. Manipulation deterrence uses non-recapturable cost floor; risk checks assume attacker may own LP share and recapture pool fees.
- `C-FUND-1` (standby): **Funding Budget Balance**. Funding application must preserve net funding budget balance across open accounts or fail closed.
- `C-KEEPER-1` (standby): **Keeper Bounty Anti-Farming**. Keeper bounty must satisfy `bounty <= collected_penalty` with notional/penalty floors and per-epoch caps.
- `C-DEPEG-1` (standby): **Depeg Stress Guardrails**. Maintain dynamic leverage and maintenance requirements under collateral depeg stress; trigger deterministic breaker/deleveraging when haircut-adjusted margin fails.

## Stable Settlement + Price Feed Baseline

- Settlement asset must have deterministic valuation policy (haircuts/depeg bands) applied in margin checks.
- Oracle publication must be signed, replay-protected, and stale-price fail-closed.
- Funding/liquidation incentives must remain revenue-bounded and non-farmable under attacker-as-LP assumptions.

## Promotion Gate

- `has_lift_rate >= 0.80`, `solved_rate_delta >= 0.00`, and `avg_seconds_reduction >= 0.000000`.
- Promote only `status=promote`; others remain shadow-mode or blocked.
