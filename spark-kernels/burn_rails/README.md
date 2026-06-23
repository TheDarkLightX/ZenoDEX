# Advisory SPARK burn-rail conservation kernel

A tiny SPARK 2014 kernel that specifies the buyback **burn (do_burn = 1)
conservation** property the Python reference (`src/core/burn_receipts.py` rails)
and the Rust shadow (`zenodex-runtime-core::burn_receipts`) implement:

```
supply_after            = supply_before - burn_amount
batch_after             = batch_before + burn_amount
supply_before - supply_after = batch_after - batch_before   (one-for-one)
supply_after >= 0                                            (cannot cross zero)
burn_amount <= burn_budget                                   (budget-capped)
```

## Status

`gnatprove` / the GNAT/SPARK toolchain is **not installed** in the container that
produced this kernel, so the proof has **not** been discharged here. The sources
are written to be proved by SPARK 2014; run the commands below in an environment
with the toolchain. Until then this kernel is **advisory and vector-checked**
only (see below) — it is never claimed as "proven".

## Contract

The `Burn` procedure (`burn_rails.ads`) carries the conservation /
non-negativity / budget precondition and postcondition above. The two
assignments in `burn_rails.adb` are exact integer ops, so the verification
conditions are straightforward (no products, no overflow within the
`[0, 0x7FFF]` / `[0, 0xFFFF]` field bounds).

## Build & prove

```bash
gprbuild -P burn_rails.gpr
gnatprove -P burn_rails.gpr --level=2 --report=all
```

## Shared test vectors

`test_vectors.json` is generated from the Python authority's rails and is the
common oracle for Python, Rust, and SPARK:

```bash
python3 spark-kernels/burn_rails/export_test_vectors.py          # regenerate
python3 spark-kernels/burn_rails/export_test_vectors.py --check   # CI: fail if stale
```

`tests/runtime/test_burn_rails_shared_vectors.py` validates that every vector
satisfies the Python rails and the conservation identity, and that the committed
file is byte-stable.
