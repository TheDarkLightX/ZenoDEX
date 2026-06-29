# ZenoDEX Research Kernel Frontier Hygiene - 2026-06-29

## Executive Result

A local closure map now connects the sampled n=8 child-frontier proof-object chain certificate to the Research Kernel frontier items it actually covers.
The receipt also lists frontier items that remain open, so the map improves discovery without broadening the supported claim.

- Closure rows: `4`
- Resolved rows: `2`
- Specialized rows: `2`
- Open frontier rows retained: `5`

## Closure Map

| frontier atom | closure kind | resolver |
| --- | --- | --- |
| `atom_ef1f5b6ebed246eb` | `resolves` | `n8_chain_resolves_canonical_merkle_refutation_risk` |
| `atom_d64b2781e6604d77` | `resolves` | `n8_chain_resolves_bidirectional_transition_refutation_risk` |
| `atom_e4b9b11387894204` | `specializes` | `n8_chain_specializes_tau_specification_reformulation` |
| `atom_41092f7feb7f4df8` | `specializes` | `n8_chain_specializes_proof_object_compression_reformulation` |

## Open Frontier

| frontier atom | reason open | next action |
| --- | --- | --- |
| `atom_f16f64e92cd14d74` | n7 Tau scope refutation risk is separate from the sampled n8 proof-object chain. | Replay the n7 Tau certificate risk against its own source report and add an explicit RK edge if it closes. |
| `atom_e867f667225442a4` | n7 bidirectional transition mutation risk is separate from the sampled n8 transition chain. | Build or replay a n7-specific chain/transition closure receipt with mutation controls. |
| `atom_c0f2558fe81046cf` | record-set monotone-reserve dominance is a Lean/record-set claim, not covered by the n8 child-frontier chain. | Run a dedicated refutation pass over the record-set certificate and register the outcome. |
| `atom_5e7aa160e5604f79` | observed-summary bridge scope is not implied by the n8 child-frontier proof-object chain. | Replay the observed-summary bridge and check stale overclaims separately. |
| `atom_0641a88159d6456b` | reserve-state observed-summary bridge scope is not implied by the n8 child-frontier proof-object chain. | Replay the reserve-state observed-summary bridge and add a closure row only if its own checks pass. |

## Research Kernel Edges To Add

| target atom | edge type | closure kind |
| --- | --- | --- |
| `atom_ef1f5b6ebed246eb` | `SUPERSEDES` | `resolves` |
| `atom_d64b2781e6604d77` | `SUPERSEDES` | `resolves` |
| `atom_e4b9b11387894204` | `SPECIALIZES` | `specializes` |
| `atom_41092f7feb7f4df8` | `SPECIALIZES` | `specializes` |

## Non-Claims

- This receipt does not mutate Research Kernel frontier ranking by itself; explicit RK edges are required.
- This receipt closes only the listed n8 sampled child-frontier items.
- This receipt intentionally leaves unrelated n7, observed-summary, and record-set risks open.
- This receipt records research-evidence closure only and grants no settlement, governance, state-root, or production authority.
- Generated report JSON files are replay outputs; tracked source artifacts and replay commands are the durable evidence handles.

## Replay

```bash
python3 tools/check_research_kernel_frontier_hygiene_20260629.py
```

Refresh prerequisite report first:

```bash
python3 tools/check_research_kernel_frontier_hygiene_20260629.py --refresh
```
