# ZenoDEX Tau Performance Frontier Breakthrough - 2026-06-28

## Executive Result

`tau_performance_frontier_certificate_v1` is a new Tau certificate for performance-frontier evidence. It admits only when the host supplies profile-lattice, budget, candidate-feature, latest/runtime replay, direct-bv gating, host-projection default, zero-invalid-accept, negative-control, high-value coverage, advisory-only, and no-authority facts.

Latest Tau passed `8` cases in `1.251703` seconds. Runtime Tau passed `8` cases in `1.256947` seconds. Combined invalid accepts: `0`.

Design rule: Use host-projected boolean envelopes by default; allow direct Tau bitvectors only for small bounded kernels with replayed profile evidence and zero invalid accepts.

## Profile Evidence

- Profiles: `4`
- Components: `28`
- Variants: `86`
- Budget lattice ok: `True`
- Semantic contracts: `35`
- Host-projection contracts: `11`

## Candidate Feature Scan

| spec | bytes | direct bv ops | max bv width | width cast |
| --- | ---: | ---: | ---: | --- |
| `src/tau_specs/recommended/frontier_certificate_menu_v1.tau` | `2208` | `0` | `0` | `False` |
| `src/tau_specs/recommended/optimizer_quotient_certificate_v1.tau` | `4180` | `0` | `0` | `False` |
| `src/tau_specs/recommended/ab_cow_exact_solver_envelope_v1.tau` | `3062` | `0` | `0` | `False` |
| `src/tau_specs/recommended/solver_portfolio_upgrade_certificate_v1.tau` | `3333` | `0` | `0` | `False` |
| `src/tau_specs/recommended/tauspec_counterexample_synthesis_certificate_v1.tau` | `2910` | `0` | `0` | `False` |
| `src/tau_specs/recommended/receipt_sequence_bv16_guard_v1.tau` | `2078` | `30` | `16` | `False` |

## Tau Replay

| profile | ok | elapsed | invalid accepts | negative rejections |
| --- | --- | ---: | ---: | ---: |
| `latest` | `True` | `1.251703` | `0` | `7` |
| `runtime` | `True` | `1.256947` | `0` | `7` |

## Counterexample Cases

| case | latest ok | runtime ok | rationale |
| --- | --- | --- | --- |
| `performance_frontier_pass` | `True` | `True` | All profile, trace, encoding, evidence, and authority facts admit the performance-frontier certificate. |
| `missing_profile_lattice_reject` | `True` | `True` | A certificate without the profile lattice cannot claim performance fit. |
| `latest_budget_reject` | `True` | `True` | Latest Tau replay must be inside the declared profile budget. |
| `direct_bv_unprofiled_reject` | `True` | `True` | Direct bitvector islands require profile-gated replay evidence. |
| `invalid_accepts_reject` | `True` | `True` | Any invalid accept invalidates performance-frontier promotion. |
| `coverage_reject` | `True` | `True` | A profile result without high-value coverage is not a frontier result. |
| `authority_reject` | `True` | `True` | Performance certificates cannot carry settlement, oracle, or governance authority. |
| `inactive_safe` | `True` | `True` | Inactive certificates do not admit while the no-authority rail remains safe. |

## Non-Claims

- This does not authorize settlement, oracle updates, governance, or production release.
- This does not prove arbitrary direct Tau arithmetic is acceptable.
- Profile fit is evidence for a bounded candidate set and must be replayed after Tau or spec changes.

## Replay

```bash
python3 tools/zenodex_tau_performance_frontier_breakthrough_20260628.py
```
