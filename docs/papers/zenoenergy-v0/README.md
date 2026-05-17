# ZenoEnergy v0 Paper

This directory contains the ZenoEnergy v0 research paper:

- [paper.md](./paper.md)
- [zenoenergy-v0.tex](./zenoenergy-v0.tex)
- [zenoenergy-v0.pdf](./zenoenergy-v0.pdf)

The paper summarizes the verifier-preserving candidate-ordering experiment for
UPBA v2 partial-fill exact-in settlement search.

Build:

```bash
pdflatex -interaction=nonstopmode -halt-on-error zenoenergy-v0.tex
```

Primary artifacts:

- `docs/ZENO_ENERGY_V0.md`
- `docs/ZENO_ENERGY_RESULTS.md`
- `src/energy/`
- `tools/generate_upba_energy_dataset.py`
- `tools/train_upba_energy.py`
- `tools/evaluate_upba_energy.py`
- `tools/benchmark_upba_energy_search.py`
- `lean-mathlib/Proofs/UniformBatchOptimality.lean`
