# ZenoDEX CPSS-BC Research Scope Certificate - 2026-06-28

## Executive Result

`cpss_bc_research_scope_certificate_v1` admits the CPSS-BC research bundle only when its formal claims, falsifications, replay artifacts, and no-authority boundary are all present.
The certificate is deliberately scoped as research evidence. It does not implement production clearing or authorize settlement.

## Facts

- `artifacts_present` = `1`
- `lean_compile_ok` = `1`
- `lean_no_forbidden_tokens` = `1`
- `compressed_state_scope_ok` = `1`
- `adaptive_window_empirical_only` = `1`
- `single_user_sp_proven` = `1`
- `group_sp_falsified` = `1`
- `precommit_collusion_documented` = `1`
- `cpss_greedy_dominance_falsified` = `1`
- `production_nonclaims_bound` = `1`
- `replay_scripts_present` = `1`
- `no_authority_effect` = `1`

## Lean Verification

| file | compile | seconds |
| --- | --- | ---: |
| `lean-mathlib/Proofs/CompressedStateSubsetDP.lean` | `True` | `6.004311` |
| `lean-mathlib/Proofs/CommitRevealStrategyproof.lean` | `True` | `5.410663` |
| `lean-mathlib/Proofs/CommitRevealBothParamsSP.lean` | `True` | `5.415178` |
| `lean-mathlib/Proofs/WindowBound.lean` | `True` | `6.252898` |
| `lean-mathlib/Proofs/StrongConcavityWindowBound.lean` | `True` | `5.689043` |

## Tau Cases

| case | ok | admitted |
| --- | --- | ---: |
| `research_scope_certificate_pass` | `True` | `1` |
| `missing_window_scope_reject` | `True` | `0` |
| `missing_group_sp_falsification_reject` | `True` | `0` |
| `missing_precommit_collusion_reject` | `True` | `0` |
| `missing_cpss_falsification_reject` | `True` | `0` |
| `authority_reject` | `True` | `0` |
| `inactive_safe` | `True` | `0` |

## Non-Claims

- This certificate does not implement production batch clearing.
- This certificate does not prove group strategyproofness.
- This certificate does not prove universal CPSS greedy dominance.
- This certificate does not promote adaptive-window exactness beyond the recorded empirical scope.

## Replay

```bash
python3 tools/zenodex_cpss_bc_research_scope_certificate_20260628.py
```
