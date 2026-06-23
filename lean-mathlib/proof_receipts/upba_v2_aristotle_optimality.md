---
title: UPBA V2 Aristotle Optimality Receipt
type: proof_receipt
permalink: autonomous-tau-dex-review/proof-receipts/upba-v2-aristotle-optimality
---

# UPBA V2 Aristotle Optimality Receipt

Aristotle project:

```text
abee69ad-e2a3-47ce-8c0f-71491635f5d3
```

Purpose: independent proof-search for the starter UPBA optimality boundary.

The submitted packet asked Aristotle to preserve the theorem statements in a
small Lean project and fill four proof holes:

- `aggregate_uniform_volume_upper_bound`
- `aggregate_clear_quantity_feasible`
- `aggregate_clear_quantity_volume_optimal`
- `upper_bound_certificate_implies_weak_optimal`

The returned packet proved all four theorem statements without adding
assumptions, axioms, `unsafe`, or placeholders.

Local checks on the returned packet:

```bash
cd /tmp/aristotle-upba-optimality-result/aristotle-upba-optimality_aristotle
lake build
```

Result:

```text
Build completed successfully (3 jobs).
```

Trust scan on returned Lean:

```bash
rg -n '\b(sorry|admit|axiom|unsafe|sorryAx)\b' \
  /tmp/aristotle-upba-optimality-result/aristotle-upba-optimality_aristotle/UPBAOptimalityTask.lean
```

Result: no matches.

Integration decision: accepted the theorem surface and proof ideas, kept the
local checked implementation in `lean-mathlib/Proofs/UniformBatchOptimality.lean`.
The local proof is equivalent in substance and follows the repository comment
style.

Follow-up local extension: the repository proof file now also includes
`upper_bound_certificate_with_winner_implies_present_and_weak_optimal`, which
adds the runtime requirement that the declared winner is present in the audited
candidate list. This theorem was proved locally with the direct checker:

```bash
cd lean-mathlib
~/.elan/bin/lean Proofs/UniformBatchOptimality.lean
```

Second local extension: the repository proof file now also includes a precise
global-optimality bridge and a negative boundary theorem:

- `complete_audit_set_lifts_weak_optimal_to_global`
- `complete_upper_bound_certificate_implies_global_weak_optimal`
- `audited_set_optimality_does_not_exclude_omitted_better_candidate`

These theorems make the Aristotle result's scope explicit. The audited-set
certificate is exact inside the supplied finite candidate set. It becomes a
global weak-optimality proof only with a winner-feasibility proof and an
audit-set-completeness proof. Without completeness, a better omitted candidate
can exist.

Boundary: these are model-level optimality lemmas. They do not prove global
price-search completeness, fair order inclusion, solver correctness, or MEV
elimination.

## Second Aristotle Packet: Partial-Fill Bounded Grid

Aristotle project:

```text
5ab11e96-962e-46a7-a342-17e65b796141
```

Purpose: independent proof-search for the UPBA v2 partial-fill bounded-grid
bridge.

The submitted packet is in
`internal/aristotle/upba_v2_partial_fill_grid_20260517`. It asks Aristotle to
fill the proof holes for:

- `partialFillCanonicalGridCandidates_complete`
- `partialFillCanonicalGridCandidates_sound`
- `partialFillCanonicalGridCandidates_complete_audit_set`
- `partialFillCanonicalGridCandidates_sound_audit_set`
- `partialFillCanonicalGridCandidates_exact_audit_set`
- `upba_v2_partial_fill_bounded_grid_upper_bound_certificate_implies_global_weak_optimal`

Local pre-submission check:

```bash
cd internal/aristotle/upba_v2_partial_fill_grid_20260517
~/.elan/bin/lake build
```

Result: build completed successfully with only the expected `sorry` warnings in
the challenge file.

Returned result path:

```text
internal/aristotle/results/upba_v2_partial_fill_grid_5ab11e96/result.tar.gz
```

Local returned-packet check:

```bash
cd internal/aristotle/results/upba_v2_partial_fill_grid_5ab11e96/upba_v2_partial_fill_grid_20260517_aristotle
~/.elan/bin/lake build
```

Result:

```text
Build completed successfully (3 jobs).
```

Trust scan on returned Lean:

```bash
rg -n '\b(sorry|admit|axiom|unsafe|sorryAx)\b' \
  internal/aristotle/results/upba_v2_partial_fill_grid_5ab11e96/upba_v2_partial_fill_grid_20260517_aristotle/AristotleTask.lean
```

Result: no matches.

Integration decision: accepted the theorem statement preservation and proof
ideas as an independent replay of the UPBA v2 partial-fill bridge. No code was
copied into `lean-mathlib/Proofs/UniformBatchOptimality.lean` because the local
proofs were already present, checked, and more explicit than the generated
proof text. The returned proof remains recorded as corroborating evidence, not
as the canonical source file.
