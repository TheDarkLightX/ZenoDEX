# ZenoDEX TauSpecEBRM Baseline Breakthrough - 2026-06-28

## Executive Result

`tauspec_ebrm_frontier_selection_certificate_v1` is a new Tau certificate for the selector result. It admits only when the host replay reports a bounded candidate pool, passing Tau traces, zero invalid accepts, top-k baseline parity, AB/CoW coverage, deterministic replay, profile-budget compliance, advisory-only status, and no authority.

`tau_spec_ebrm_v2` ranked `optimizer_quotient_certificate_v1, route_split_window_certificate_v1, frontier_certificate_menu_v1` in the top three with frontier score `454.0` and `0` invalid accepts.

Authority boundary: model proposes and ranks. Tau traces plus host/kernel verifiers decide acceptance.

## Tau Gate

- Spec: `src/tau_specs/recommended/tauspec_ebrm_frontier_selection_certificate_v1.tau`
- Latest Tau ok: `True`
- Selector cases: `7`
- Selector invalid accepts: `0`

Selector facts:
- `candidate_pool_bound_ok` = `1`
- `tau_traces_passed` = `1`
- `invalid_accepts_zero` = `1`
- `topk_not_worse_than_baselines` = `1`
- `work_item_1_ab_covered` = `1`
- `work_item_2_cow_covered` = `1`
- `deterministic_replay_ok` = `1`
- `performance_profile_bound_ok` = `1`

## Candidate Pool

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

## Baseline Comparison

| method | top 3 | top-3 score | invalid accepts top 3 | first high-value valid rank |
| --- | --- | ---: | ---: | ---: |
| `tau_spec_ebrm_v2` | `optimizer_quotient_certificate_v1, route_split_window_certificate_v1, frontier_certificate_menu_v1` | `454.0000` | `0` | `1` |
| `highest_value` | `frontier_certificate_menu_v1, optimizer_quotient_certificate_v1, route_dominance_frontier_envelope_v1` | `450.0000` | `0` | `1` |
| `most_projected_facts` | `optimizer_quotient_certificate_v1, oracle_polytope_frontier_envelope_v1, route_dominance_frontier_envelope_v1` | `437.0000` | `0` | `1` |
| `host_projection_heuristic` | `optimizer_quotient_certificate_v1, route_split_window_certificate_v1, route_dominance_frontier_envelope_v1` | `451.0000` | `0` | `1` |
| `grammar_minimal` | `route_split_window_certificate_v1, frontier_certificate_menu_v1, route_dominance_frontier_envelope_v1` | `433.0000` | `0` | `1` |
| `existing_profile_choice` | `frontier_certificate_menu_v1, route_dominance_frontier_envelope_v1, oracle_polytope_frontier_envelope_v1` | `419.0000` | `0` | `1` |
| `seeded_random_20260628` | `optimizer_quotient_certificate_v1, route_dominance_frontier_envelope_v1, proof_mining_slot_batch_certificate_v1` | `421.0000` | `0` | `1` |

`tau_spec_ebrm_v2` is deterministic and advisory. It uses Tau pass/fail status, invalid-accept counts, profile budget, source size, definition count, frontier value, novelty, projected-fact coverage, and negative-case rejections.

## What Tau Specifications Can Do For ZenoDEX

1. Gate frontier optimizer reports with small fail-closed evidence certificates.
2. Compose 8 to 11 host-projected facts per step while keeping hashes, search, matching, and CPMM arithmetic in deterministic host code.
3. Require negative-case replay, so a research selector cannot pass by accepting invalid traces.
4. Keep work items 1 and 2 visible in the frontier queue through explicit AB and CoW coverage bits.
5. Expose no-authority outputs, making it explicit that these specs cannot mutate settlement or oracle state.

## Work Items 1 And 2

### 1. AB Ordering

The comparator keeps `optimizer_quotient_certificate_v1` and `ab_cow_exact_solver_envelope_v1` in the ranked frontier. The implementation boundary remains a host full-state subset DP or brute-force parity oracle; Tau checks objective binding, state-cap scope, replay/parity, deterministic ties, budget, fallback, and no-authority facts.

### 2. CoW Matching

The same two artifacts keep the CoW track active. Tau admits the uncoupled assignment surface only after host evidence supplies capacity scope, assignment parity, deterministic ties, budget, fallback, and no-authority facts. Grouped capacity remains a bounded exact-search or fallback surface.

## Non-Claims

- TauSpecEBRM is advisory and cannot authorize settlement, oracle updates, or governance.
- The report compares a bounded eight-spec candidate pool, not every Tau spec in the repository.
- Host-projected facts remain external obligations until their owning host/kernel verifier replays them.

## Replay

```bash
python3 tools/zenodex_tauspec_ebrm_baseline_breakthrough_20260628.py
```
