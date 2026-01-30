# Settlement Algebra + Batch CPMM (Paper Draft)

This folder contains an academic-style LaTeX draft describing the mathematical
model and mechanized Lean proofs in:

- `lean-mathlib/Proofs/SettlementAlgebra.lean`
- `lean-mathlib/Proofs/BatchOptimality.lean`
- `lean-mathlib/Proofs/CPMMInvariants.lean`
- `lean-mathlib/Proofs/CPMMSettlement.lean`
- `lean-mathlib/Proofs/BatchCPMMUnification.lean`

## Build

```bash
cd docs/papers/settlement-algebra-batch-cpmm
latexmk -pdf main.tex
```

If `latexmk` is unavailable:

```bash
pdflatex main.tex
bibtex main
pdflatex main.tex
pdflatex main.tex
```
