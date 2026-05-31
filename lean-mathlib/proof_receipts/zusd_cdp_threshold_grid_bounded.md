# zUSD CDP threshold grid Lean receipt

Date: 2026-05-31

File:

```text
lean-mathlib/Proofs/ZUSDCDPThresholdGrid.lean
```

Commands:

```bash
lean lean-mathlib/Proofs/ZUSDCDPThresholdGrid.lean
lean -R lean-mathlib lean-mathlib/Proofs/ZUSDCDPThresholdGrid.lean
rg -n "sorry|admit|axiom|unsafe" lean-mathlib/Proofs/ZUSDCDPThresholdGrid.lean || true
```

Results:

```text
lean: exit 0
lean -R lean-mathlib: exit 0
placeholder scan: no matches
```

Checked declarations:

```text
Proofs.ZUSDCDPThresholdGrid.cdpBoundaryGridOk_true
Proofs.ZUSDCDPThresholdGrid.cdpBoundaryWitnesses
```

Scope:

```text
bounded finite boundary formula checks only
```

The receipt does not claim full live-domain zUSD refinement. It supplements the
runtime threshold grid and the existing Python/Rust differential suite.
