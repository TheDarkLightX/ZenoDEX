# ZenoDEX Tau Semantic Coverage Selector - 2026-06-28

## Executive Result

A replayable Tau certificate and report generator that converts runtime-active Tau semantic gaps into a deterministic promotion frontier.

- Active Tau specs: `366`
- Focus candidates: `19`
- Proposed specs: `3`
- Tau surfaces: `3`
- Tau cases: `44`
- Required-fact mutations: `38`
- Invalid accepts: `0`
- False rejects: `0`

## Proposed Specifications

| work item | spec | benefit |
| --- | --- | --- |
| `1_ab_ordering` | `ab_ordering_held_karp_dp_certificate_v1` | Certifies that an AB-ordering upgrade used full CPMM state, bounded brute-force parity, deterministic ties, state-cap fallback, and no settlement authority. |
| `2_cow_matching` | `cow_hungarian_matching_certificate_v1` | Certifies that an uncoupled CoW matching upgrade supplied primal/dual assignment evidence, bounded parity, grouped-capacity fallback, deterministic ties, and no settlement authority. |
| `semantic_coverage_frontier` | `tau_semantic_coverage_selector_certificate_v1` | Certifies that the active Tau inventory and refinement queue were replayed and that AB/CoW promotion targets remain selected. |

## Tau Replay

| surface | cases | mutations | invalid accepts | false rejects | ok |
| --- | ---: | ---: | ---: | ---: | --- |
| `semantic_selector` | `17` | `15` | `0` | `0` | `True` |
| `ab_ordering` | `13` | `11` | `0` | `0` | `True` |
| `cow_matching` | `14` | `12` | `0` | `0` | `True` |

## Selector Facts

| fact | value |
| --- | ---: |
| `active_inventory_built` | `1` |
| `advisory_selection_only` | `1` |
| `budget_profile_ok` | `1` |
| `coverage_gaps_present` | `1` |
| `critical_bucket_coverage_ok` | `1` |
| `deterministic_priority_order_ok` | `1` |
| `mutation_atlas_dependency_bound` | `1` |
| `no_runtime_authority_effect` | `1` |
| `proposed_spec_artifacts_present` | `1` |
| `selector_active` | `1` |
| `semantic_contract_next_actions_bound` | `1` |
| `semantic_refinement_queue_built` | `1` |
| `tau_replay_invalid_accepts_zero` | `1` |
| `work_item_1_ab_selected` | `1` |
| `work_item_2_cow_selected` | `1` |

## Non-Claims

- This artifact does not prove the proposed host algorithms correct.
- This artifact does not authorize settlement, oracle updates, governance actions, or state roots.
- The selector ranks the current bounded repo inventory and proposed work-item specs; it does not rank an unbounded Tau language space.
- The AB certificate does not validate compressed one-record Held-Karp state.
- The CoW certificate does not claim arbitrary grouped-capacity matching is polynomial.

## Replay

```bash
python3 tools/zenodex_tau_semantic_coverage_selector_20260628.py
```
