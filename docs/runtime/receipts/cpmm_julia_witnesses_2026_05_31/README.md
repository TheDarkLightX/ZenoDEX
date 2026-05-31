# CPMM Julia Boundary Witness Replay Receipt

Date: 2026-05-31

This receipt records an offline Julia witness lane for CPMM arithmetic-heavy
boundaries. Julia is used only to generate deterministic BigInt witnesses. It
is not runtime authority, not an oracle in production, and not a proof system.

The value is independent arithmetic pressure on exact-in and exact-out cases
that are awkward for full-domain Kani because of division, ceiling division,
reserve bounds, and reject ordering.

## Artifacts

- `tools/runtime/cpmm_julia_witnesses.jl`
- `tests/runtime/test_cpmm_julia_witnesses.py`

Generator schema:

```text
zenodex.cpmm_julia_witnesses.v1
```

Witness count:

```text
14 cases: 6 accepted, 8 rejected
```

Covered boundaries:

- exact-in small floor acceptance
- exact-in near reserve maximum acceptance
- exact-in reserve-domain rejection
- exact-in full-fee trade-too-small rejection
- exact-in high-fee one-unit-net acceptance
- exact-in slippage rejection
- exact-out small acceptance
- exact-out overdelivery accepted when the gap policy is open
- exact-out overdelivery rejected under the default gap policy
- exact-out near reserve maximum acceptance
- exact-out reserve-domain rejection
- exact-out amount-at-reserve rejection
- exact-out full-fee rejection
- exact-out slippage rejection

The pytest replay checks every witness against both:

1. Python CPMM quote logic in `settlement_swap_runtime_v1.py`.
2. Rust `cpmm-op` through the runtime CLI bridge.

## Evidence

```bash
julia tools/runtime/cpmm_julia_witnesses.jl | python3 -m json.tool >/tmp/cpmm_julia_witnesses.pretty.json
python3 - <<'PY'
import json
p='/tmp/cpmm_julia_witnesses.pretty.json'
doc=json.load(open(p))
print(doc['schema'], doc['case_count'])
print(sum(1 for c in doc['cases'] if c['expect']['accept']), sum(1 for c in doc['cases'] if not c['expect']['accept']))
PY
```

Result:

```text
zenodex.cpmm_julia_witnesses.v1 14
6 8
```

```bash
PYTEST_DISABLE_PLUGIN_AUTOLOAD=1 pytest -q tests/runtime/test_cpmm_julia_witnesses.py
```

Result:

```text
1 passed in 1.01s
```

```bash
PYTEST_DISABLE_PLUGIN_AUTOLOAD=1 pytest -q \
  tests/runtime/test_cpmm_exact_arithmetic_grid.py \
  tests/runtime/test_cpmm_julia_witnesses.py \
  tests/runtime/test_cpmm_settlement_conformance.py \
  tests/runtime/test_cpmm_settlement_disaster_state.py \
  tests/runtime/test_cpmm_settlement_live_path.py \
  tests/runtime/test_cpmm_settlement_semantic_invariants.py
```

Result:

```text
39 passed in 2.55s
```

```bash
cd rust-runtime
cargo test -q -p zenodex-runtime-core cpmm_swap
cargo test -q -p zenodex-runtime-cli cpmm
```

Result:

```text
zenodex-runtime-core: 9 passed; 0 failed; 165 filtered out
zenodex-runtime-cli: 0 passed; 0 failed; 80 filtered out
```

## Boundary

This lane strengthens CPMM's tested-refinement evidence by adding a small,
deterministic, high-precision witness source. It does not move CPMM to full CBC
grade. Full live-domain exact-in/exact-out arithmetic remains outside Kani and
is still covered by decomposition, property tests, differentials, bounded SMT,
Lean slices, and this replayable witness set.
