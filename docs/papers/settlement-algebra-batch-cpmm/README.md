---
title: README
type: note
permalink: autonomous-tau-dex-review/docs/papers/settlement-algebra-batch-cpmm/readme
---

# Settlement Algebra + Batch CPMM (Paper Draft)

This folder contains a compiled paper PDF describing the mathematical model and
mechanized Lean proofs in:

- `lean-mathlib/Proofs/SettlementAlgebra.lean`
- `lean-mathlib/Proofs/BatchOptimality.lean`
- `lean-mathlib/Proofs/CPMMInvariants.lean`
- `lean-mathlib/Proofs/CPMMSettlement.lean`
- `lean-mathlib/Proofs/BatchCPMMUnification.lean`
- `lean-mathlib/Proofs/SettlementCanonicalExecution.lean`
- `lean-mathlib/Proofs/SettlementMechanism.lean`

## Notes

- The repository intentionally tracks the compiled artifact `settlement-algebra-batch-cpmm.pdf`.
- The LaTeX sources are tracked and should be treated as the editable source of truth.
- The paper now frames settlement algebra as a new ZenoDEX-specific synthesis over
  known netting, accounting-algebra, AMM, and formal-verification ingredients.
