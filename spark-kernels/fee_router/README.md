# SPARK/Ada Fee-Split Conservation Kernel (advisory)

A tiny high-assurance sidecar that specifies and (under `gnatprove`) proves the
**single-split fee conservation** property used by the ZenoDEX fee router:

```
buyburn + stakers + reserve + hosts + dust = amount
all outputs >= 0
```

This is the optional **Phase 7** deliverable from
`../../docs/runtime/RUST_RUNTIME_MIGRATION_PLAN.md`. It is **advisory / checker
evidence only** — it is not on any runtime path and is not authoritative.

## Status in this environment

`gnatprove` / the GNAT/SPARK toolchain is **not installed** in the container
that produced this kernel, so the proof has **not** been discharged here. The
sources are written to be proved by SPARK 2014; run the commands below in an
environment with the toolchain.

## Files

| File | Role |
|------|------|
| `fee_router.ads` | Package spec with the `Pre`/`Post` contract. |
| `fee_router.adb` | Body (floor split + dust). |
| `fee_router.gpr` | GNAT project (build + prove). |
| `test_vectors.json` | Shared oracle vectors, generated from the Python reference. |
| `export_test_vectors.py` | Regenerates `test_vectors.json`. |

## Contract

```ada
procedure Route (Amount : in Money; S : in Split; ... ; Dust : out Money)
with
  Pre  => Sums_To_Denom (S),                 --  shares sum to 10000
  Post => Buyburn + Stakers + Reserve + Hosts + Dust = Amount
    and then Buyburn >= 0 and then ... and then Dust >= 0;
```

* `Money` is bounded (`0 .. 2**40`) so `Amount * Bps` cannot overflow
  `Long_Long_Integer` — the overflow VCs are trivial.
* The conservation VC is trivial (`Dust := Amount - Distributed`).
* The `Dust >= 0` VC relies on **floor subadditivity** (the sum of per-bucket
  floors never exceeds `Amount` when the shares sum to the denominator). Modern
  SMT back-ends usually discharge this at `--level=2`; if not, add a small ghost
  lemma over the division.

## Toolchain

Install GNAT + SPARK (e.g. via [Alire](https://alire.ada.dev)):

```bash
alr toolchain --select   # pick a gnat + gnatprove
# or use a FSF GNAT + SPARK Pro / Community install
```

## Build & prove

```bash
cd spark-kernels/fee_router
gprbuild -P fee_router.gpr
gnatprove -P fee_router.gpr --level=2 --report=all
```

## Shared test vectors

`test_vectors.json` is generated from the authoritative Python runtime and is
the common oracle for all three runtimes:

```bash
python3 spark-kernels/fee_router/export_test_vectors.py \
  --out spark-kernels/fee_router/test_vectors.json
```

* **Python**: validated by `tests/runtime/test_fee_router_shared_vectors.py`
  (every vector reproduced exactly; file kept up to date).
* **Rust**: parity with Python is already enforced by the differential suite
  (`tests/runtime/test_fee_router_conformance.py`), which subsumes these
  vectors.
* **SPARK**: use the vectors as test cases for an `AUnit`/assertion harness
  alongside the proof (the proof covers *all* in-range inputs; the vectors give
  concrete regression points and cross-runtime equality).

Acceptance (per the migration task): the SPARK proof passes, the **same vectors
pass in Python and Rust**, and SPARK stays advisory unless integration is
explicitly approved.
