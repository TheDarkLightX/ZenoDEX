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

Boundary: these are model-level optimality lemmas. They do not prove global
price-search completeness, fair order inclusion, solver correctness, or MEV
elimination.
