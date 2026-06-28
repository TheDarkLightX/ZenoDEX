# ZenoDEX TauSpec Counterexample Synthesis Breakthrough - 2026-06-28

## Executive Result

`tauspec_counterexample_synthesis_certificate_v1` is a new Tau certificate for counterexample-driven spec synthesis. It admits only when generated candidates pass bounded grammar, parse/lint, host-projection, positive trace, negative trace, mutation rejection, value/profile, AB/CoW coverage, advisory-only, and no-authority facts.

Latest Tau replay passed `9` cases with `0` invalid accepts and `8` negative rejections.

Authority boundary: model proposes or repairs candidate specs; deterministic Tau traces, linting, host-projection checks, and kernel tests decide acceptance.

## Tau Specification

- Spec: `src/tau_specs/recommended/tauspec_counterexample_synthesis_certificate_v1.tau`
- Latest Tau: `Tau Language Framework version 0.7.0-alpha (401d756b)`
- Direct bitvector ops: `0`
- Inputs/outputs: `14` / `7`

The spec stays in the supported host-projection fragment: Tau composes boolean facts; host tools own expensive arithmetic, matching, parsing, semantic linting, and replay.

## New Specifications Tau Can Support

| spec | status | host facts | direct bv ops | benefit |
| --- | --- | ---: | ---: | --- |
| `tauspec_counterexample_synthesis_certificate_v1` | `implemented_replayed` | `14` | `0` | Certifies generated Tau-spec candidates only after parse/lint, host-projection, positive and negative trace replay, mutation rejection, value/profile, AB/CoW coverage, and no-authority facts. |
| `cow_capacity_scope_counterexample_gate_v1` | `next_spec_candidate` | `10` | `0` | Would require grouped-capacity CoW counterexamples to be replayed before a matching-only certificate can claim the uncoupled Hungarian surface. |
| `ab_state_compression_refuter_gate_v1` | `next_spec_candidate` | `9` | `0` | Would keep the one-record Held-Karp compression counterexample attached to future AB ordering proposals. |
| `route_split_window_mutation_gate_v1` | `next_spec_candidate` | `11` | `0` | Would require local-window split-routing certificates to reject missing parity, missing quote replay, and authority-leak mutations. |

## Work Items 1 And 2

### 1. AB ordering

The synthesis certificate requires AB work-item coverage and can keep the unsafe Held-Karp compression counterexample attached to future generated AB specs.

Current artifacts:
- `ab_cow_exact_solver_envelope_v1.tau`
- `ab_frontier_dp_certificate_v1.tau`
- `optimizer_quotient_certificate_v1.tau`

### 2. CoW matching

The synthesis certificate requires CoW work-item coverage and can prevent uncoupled Hungarian claims from leaking into grouped-capacity cases without replay evidence.

Current artifacts:
- `ab_cow_exact_solver_envelope_v1.tau`
- `optimizer_quotient_certificate_v1.tau`

## Counterexample Replay

| case | ok | rationale |
| --- | --- | --- |
| `synthesis_certificate_pass` | `True` | All generated-spec evidence, counterexample, value, coverage, and authority facts admit. |
| `parse_or_lint_reject` | `True` | A generated candidate without a successful parse cannot certify. |
| `missing_negative_trace_reject` | `True` | A synthesis run without negative trace replay is not accepted. |
| `mutation_accepts_reject` | `True` | A candidate that does not reject its counterexample mutation fails closed. |
| `baseline_value_reject` | `True` | A generated spec must beat or match the baseline frontier value, or add scoped new coverage. |
| `authority_leak_reject` | `True` | Generated specs carrying settlement, oracle, or governance authority are rejected. |
| `work_item_1_reject` | `True` | The run must keep AB ordering coverage visible while producing the new spec. |
| `work_item_2_reject` | `True` | The run must keep CoW matching coverage visible while producing the new spec. |
| `inactive_safe` | `True` | Inactive synthesis certificates do not admit while the no-authority rail remains safe. |

## Non-Claims

- This is a research certificate for generated Tau specs, not a settlement, oracle, or governance authorizer.
- The next-spec candidates are design targets until they receive their own replay evidence.
- Host-projected facts remain obligations owned by deterministic host tools and kernel tests.

## Replay

```bash
python3 tools/zenodex_tauspec_counterexample_synthesis_breakthrough_20260628.py
```
