# ZenoDEX TauSpecEBRM Compounding Frontier - 2026-06-28

## Executive Result

`tauspec_ebrm_compounding_frontier_certificate_v1` is a Tau certificate for a compounding Research Kernel frontier selector.
It admits only when a bounded expanded candidate pool passes Tau replay, has zero invalid accepts, matches or beats deterministic top-k baselines, keeps recent supported discoveries visible, and preserves the no-authority boundary.

The expanded pool has `13` candidates. `tau_spec_ebrm_v2` top-10 coverage is `{'AB': True, 'CoW': True, 'exact_out_split_routing': True, 'exact_in_staircase': True, 'negative_frontier': True, 'evidence_dag': True, 'tokenomics_pol': True}` with `0` invalid accepts.

Authority boundary: model proposes and ranks. Tau traces plus host/kernel verifiers decide acceptance.

## Tau Gate

- Spec: `src/tau_specs/recommended/tauspec_ebrm_compounding_frontier_certificate_v1.tau`
- Latest Tau ok: `True`
- Selector cases: `9`
- Selector invalid accepts: `0`

Selector facts:
- `candidate_pool_bound_ok` = `1`
- `tau_traces_passed` = `1`
- `invalid_accepts_zero` = `1`
- `topk_not_worse_than_baselines` = `1`
- `work_item_1_ab_covered` = `1`
- `work_item_2_cow_covered` = `1`
- `exact_out_split_routing_covered` = `1`
- `exact_in_staircase_covered` = `1`
- `negative_frontier_covered` = `1`
- `evidence_dag_covered` = `1`
- `tokenomics_pol_covered` = `1`
- `deterministic_replay_ok` = `1`
- `performance_profile_bound_ok` = `1`

## Expanded Candidate Pool

| spec | primary | latest | invalid accepts | score | energy | work items |
| --- | --- | --- | ---: | ---: | ---: | --- |
| `frontier_certificate_menu_v1` | `o4` | `True` | `0` | `145.0000` | `-143.4580` | `-` |
| `route_dominance_frontier_envelope_v1` | `o4` | `True` | `0` | `142.0000` | `-140.6695` | `-` |
| `oracle_polytope_frontier_envelope_v1` | `o5` | `True` | `0` | `132.0000` | `-130.4135` | `-` |
| `ab_cow_exact_solver_envelope_v1` | `o6` | `True` | `0` | `129.0000` | `-124.4370` | `AB, CoW` |
| `optimizer_quotient_certificate_v1` | `o7` | `True` | `0` | `163.0000` | `-160.2100` | `AB, CoW` |
| `proof_mining_slot_batch_certificate_v1` | `o6` | `True` | `0` | `116.0000` | `-114.7880` | `-` |
| `sealed_bid_marginal_bucket_certificate_v1` | `o4` | `True` | `0` | `116.0000` | `-115.7150` | `-` |
| `route_split_window_certificate_v1` | `o4` | `True` | `0` | `146.0000` | `-146.3555` | `-` |
| `exact_in_staircase_hostile_certificate_v1` | `o4` | `True` | `0` | `143.0000` | `-143.0555` | `-` |
| `negative_frontier_entropy_campaign_certificate_v1` | `o4` | `True` | `0` | `155.0000` | `-154.4975` | `AB, CoW` |
| `evidence_dag_hitting_set_certificate_v1` | `o5` | `True` | `0` | `137.0000` | `-135.1035` | `-` |
| `solver_portfolio_upgrade_certificate_v1` | `o6` | `True` | `0` | `159.0000` | `-156.3405` | `AB, CoW` |
| `tokenomics_pol_sybil_threshold_certificate_v1` | `o4` | `True` | `0` | `134.0000` | `-133.8350` | `-` |

## Baseline Comparison

| method | top 3 | top-3 score | invalid accepts top 3 | first high-value valid rank |
| --- | --- | ---: | ---: | ---: |
| `tau_spec_ebrm_v2` | `optimizer_quotient_certificate_v1, solver_portfolio_upgrade_certificate_v1, negative_frontier_entropy_campaign_certificate_v1` | `477.0000` | `0` | `1` |
| `highest_value` | `exact_in_staircase_hostile_certificate_v1, frontier_certificate_menu_v1, optimizer_quotient_certificate_v1` | `451.0000` | `0` | `1` |
| `most_projected_facts` | `evidence_dag_hitting_set_certificate_v1, solver_portfolio_upgrade_certificate_v1, negative_frontier_entropy_campaign_certificate_v1` | `451.0000` | `0` | `1` |
| `host_projection_heuristic` | `solver_portfolio_upgrade_certificate_v1, evidence_dag_hitting_set_certificate_v1, negative_frontier_entropy_campaign_certificate_v1` | `451.0000` | `0` | `1` |
| `grammar_minimal` | `route_split_window_certificate_v1, frontier_certificate_menu_v1, route_dominance_frontier_envelope_v1` | `433.0000` | `0` | `1` |
| `existing_profile_choice` | `frontier_certificate_menu_v1, route_dominance_frontier_envelope_v1, oracle_polytope_frontier_envelope_v1` | `419.0000` | `0` | `1` |
| `seeded_random_20260628` | `negative_frontier_entropy_campaign_certificate_v1, solver_portfolio_upgrade_certificate_v1, optimizer_quotient_certificate_v1` | `477.0000` | `0` | `1` |

## Compounding Targets

- `evidence_dag_hitting_set_certificate_v1`: top-10 covered = `True`
- `exact_in_staircase_hostile_certificate_v1`: top-10 covered = `True`
- `negative_frontier_entropy_campaign_certificate_v1`: top-10 covered = `True`
- `optimizer_quotient_certificate_v1`: top-10 covered = `True`
- `route_split_window_certificate_v1`: top-10 covered = `True`
- `tokenomics_pol_sybil_threshold_certificate_v1`: top-10 covered = `True`

## Non-Claims

- TauSpecEBRM is advisory and cannot authorize settlement, oracle updates, governance, production promotion, or state mutation.
- The report compares a bounded expanded candidate pool, not every Tau spec in the repository.
- Host-projected facts remain external obligations until their owning host/kernel verifier replays them.

## Replay

```bash
python3 tools/zenodex_tauspec_ebrm_compounding_frontier_20260628.py
```
