# Canonical raw-framing grid

Date: 2026-05-31

This receipt records a deterministic non-Kani evidence slice for the raw
canonical framing primitives:

- `encode_uvarint` over the Rust bridge domain `0 <= value <= u128::MAX`;
- `encode_bytes`, defined as `encode_uvarint(len(bytes)) || bytes`;
- the Rust `canonical-hash` differential harness ops that expose both
  primitives to Python/Rust parity tests.

Kani covers selected scalar helper boundaries. This grid targets the
heap-allocating `Vec` encoders and CLI bridge behavior. It is bounded
cross-runtime evidence, not a proof of Python's full 256-bit `encode_uvarint`
domain.

## Covered finite grid

The runtime test is:

```text
tests/runtime/test_canonical_framing_grid.py
```

It uses a small independent unsigned-LEB128 oracle, then checks:

- uvarint thresholds around `0`, `127`, `128`, `16383`, `16384`, `2^32`,
  `2^64`, `2^127`, and `u128::MAX`;
- rejection of negative, boolean, string, and `2^128` values at the Rust bridge
  boundary;
- length-prefixed bytes for lengths `0`, `1`, `3`, `127`, `128`, and `256`;
- rejection of missing-prefix, odd-nibble, non-hex, embedded-whitespace, and
  non-string byte inputs;
- Python and Rust emit identical per-case `ok` and `bytes` results.

The static canonical differential corpus now also includes representative
`uvarint` and `encode_bytes` cases.

## Commands

Focused new grid:

```bash
PYTEST_DISABLE_PLUGIN_AUTOLOAD=1 pytest -q tests/runtime/test_canonical_framing_grid.py
```

Result:

```text
..                                                                       [100%]
2 passed in 0.12s
```

Focused canonical family:

```bash
PYTEST_DISABLE_PLUGIN_AUTOLOAD=1 pytest -q \
  tests/runtime/test_canonical_primitives_vectors.py \
  tests/runtime/test_canonical_primitives_disaster_state.py \
  tests/runtime/test_canonical_json_escape_grid.py \
  tests/runtime/test_canonical_authority_promotion.py \
  tests/runtime/test_canonical_live_path.py \
  tests/runtime/test_tx_receipt_hash_vectors.py \
  tests/state/test_canonical_size_bounds.py
```

Result:

```text
...........................................................            [100%]
61 passed in 1.20s
```

Rust focused checks:

```bash
cd rust-runtime
cargo fmt --check
cargo test -q -p zenodex-runtime-cli canonical
cargo test -q -p zenodex-runtime-core canonical
```

Result:

```text
cargo fmt --check: no output

running 1 test
.
test result: ok. 1 passed; 0 failed; 0 ignored; 0 measured; 79 filtered out; finished in 0.00s

running 20 tests
....................
test result: ok. 20 passed; 0 failed; 0 ignored; 0 measured; 154 filtered out; finished in 0.25s
```

Deployment/profile and diff hygiene:

```bash
python3 tools/check_deployment_profiles.py
git diff --check
```

Result:

```text
local-dev: ok
production-strict: ok
public-testnet: ok
git diff --check: no output
```
