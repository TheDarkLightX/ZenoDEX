# OCaml executable specification oracle

A third, **independent** pure implementation of two small runtime surfaces, used
as a *differential oracle* alongside the Python authority and the Rust shadow.

It is **not** a production runtime path and never decides network state. Its only
job is to catch a bug that Python and Rust share — the failure mode a two-way
differential cannot see (see `../docs/runtime/SEMANTIC_DRIFT_CONTROLS.md`).

## Surfaces

- `runtime_spec/fee_router.ml` — the four-way fee split + dust conservation.
- `runtime_spec/replay_guard.ml` — the strict-sequential per-sender nonce policy.

Both are pure functions over OCaml `int` (63-bit; the vector domain — fee amounts
≤ 1e9, nonces ≤ 2^32 — fits comfortably).

## Vectors

The OCaml test reads tab-separated vectors generated from the **Python
authority** (so all three implementations check against one oracle):

```bash
python3 ../tools/runtime/ocaml_spec_vectors.py          # (re)generate
python3 ../tools/runtime/ocaml_spec_vectors.py --check   # CI: fail if stale
```

`test/vectors/{fee_router,replay_guard}.tsv` are committed so `dune test` runs
without Python.

## Build & test

```bash
# Requires an opam switch with dune (e.g. opam install dune).
cd ocaml-runtime
dune build
dune test
```

`dune test` exits non-zero on any mismatch against the Python-derived vectors.
