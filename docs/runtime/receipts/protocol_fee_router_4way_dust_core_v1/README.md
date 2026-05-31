# protocol_fee_router_4way_dust_core_v1 Receipt

This receipt records the finite ESSO proof/codegen evidence for the 4-way
protocol-fee dust core modeled in:

```text
src/kernels/dex/protocol_fee_router_4way_dust_core_v1.yaml
```

The model captures the arithmetic core of
`zenodex-runtime-core::fee_router::split_with_dust`: four bucket shares
(`buyburn`, `stakers`, `reserve`, `hosts`), four per-bucket remainders, and the
folded carried dust. Its cumulative invariant is:

```text
total_input == total_routed + dust
```

Preservation of that invariant gives the per-call conservation contract:

```text
amount + dust_in == buyburn + stakers + reserve + hosts + dust_out
```

## Commands

```bash
PYTHONPATH='/home/trevormoc/Downloads/Autonomous Tau DEX' \
  python3 -m ESSO validate \
  src/kernels/dex/protocol_fee_router_4way_dust_core_v1.yaml

PYTHONPATH='/home/trevormoc/Downloads/Autonomous Tau DEX' \
  python3 -m ESSO verify-multi \
  src/kernels/dex/protocol_fee_router_4way_dust_core_v1.yaml \
  --solvers z3,cvc5 \
  --timeout-ms 30000 \
  --output /tmp/esso_fee4 \
  --write-report \
  --export-smtlib

PYTHONPATH='/home/trevormoc/Downloads/Autonomous Tau DEX' \
  python3 -m ESSO codegen-rust-kernel \
  src/kernels/dex/protocol_fee_router_4way_dust_core_v1.yaml \
  --output-root generated/rust

cd generated/rust/protocol_fee_router_4way_dust_core_v1
cargo test -q
```

## Results

- `verification_report.json` / `.md`: `VERIFIED`, Z3 and CVC5 agree on
  `init_implies_inv` and `inductive_route`.
- `codegen_rust_kernel.json`: ESSO emitted a Rust kernel crate under
  `generated/rust/protocol_fee_router_4way_dust_core_v1`.
- `generated_crate_cargo_test.txt`: generated crate tests passed.

The generated crate is reproducible output and is not tracked because
`generated/` is ignored in this checkout. The live runtime still calls the
hand-written `fee_router.rs`; this receipt strengthens the formal/codegen side
of the arithmetic-core contract.

I attempted the generated crate's broad Kani suite, but the first harness did
not finish in a useful local time window. It is therefore not counted as
evidence in this receipt.
