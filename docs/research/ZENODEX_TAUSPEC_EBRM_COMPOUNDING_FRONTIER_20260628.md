# ZenoDEX TauSpecEBRM Compounding Frontier - 2026-06-28

## Executive Result

A replayable certificate for choosing the next high-value Tau specification frontier from a bounded candidate pool.

- Candidate pool: `13`
- Top-3 frontier score: `341`
- Baseline max top-3 score: `341`
- Tau cases: `12`
- Invalid accepts: `0`
- False rejects: `0`
- Report ok: `True`

## Selected Top 10

- `solver_portfolio_upgrade_certificate_v1`
- `optimizer_quotient_certificate_v1`
- `negative_frontier_entropy_campaign_certificate_v1`
- `route_split_window_certificate_v1`
- `exact_in_staircase_hostile_certificate_v1`
- `frontier_certificate_menu_v1`
- `evidence_dag_hitting_set_certificate_v1`
- `route_dominance_frontier_envelope_v1`
- `tokenomics_pol_sybil_threshold_certificate_v1`
- `ab_cow_exact_solver_envelope_v1`

## Selector Facts

| fact | value |
| --- | ---: |
| `selector_active` | `1` |
| `candidate_pool_bound_ok` | `1` |
| `tau_traces_passed` | `1` |
| `invalid_accepts_zero` | `1` |
| `topk_not_worse_than_baselines` | `1` |
| `work_item_1_ab_covered` | `1` |
| `work_item_2_cow_covered` | `1` |
| `deterministic_replay_ok` | `1` |
| `advisory_model_only` | `1` |
| `performance_profile_bound_ok` | `1` |
| `no_authority_effect` | `1` |

## Non-Claims

- TauSpecEBRM is advisory and cannot authorize settlement, oracle updates, governance, production promotion, or state mutation.
- The report compares a bounded candidate pool, not every possible Tau specification.
- Host-projected facts remain external obligations until their owning host or kernel verifier replays them.

## Replay

```bash
python3 tools/zenodex_tauspec_ebrm_compounding_frontier_20260628.py
```
