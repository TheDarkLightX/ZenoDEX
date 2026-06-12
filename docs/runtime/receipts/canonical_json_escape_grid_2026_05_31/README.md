# Canonical JSON escape grid

Date: 2026-05-31

This receipt records a deterministic non-Kani evidence slice for canonical JSON
serialization. Kani currently proves heap-free helper predicates for canonical
primitives, while full `String`/`Vec` JSON serialization remains outside the
symbolic tractability boundary.

## Covered finite grid

The runtime test is:

```text
tests/runtime/test_canonical_json_escape_grid.py
```

It uses a small independent JSON string encoder oracle and compares:

- Python `canonical_json_bytes`;
- Rust `canonical-hash` / `canonical_json_bytes`;
- the independent expected UTF-8 bytes.

Covered values:

- every ASCII control character `0x00..0x1f`;
- the JSON short escapes for quote, backslash, backspace, tab, newline,
  form-feed, and carriage return;
- raw non-ASCII UTF-8 strings (`é`, `漢字`, `😀`);
- object key sorting with escaped control-character keys, quote/backslash keys,
  ASCII keys, and non-ASCII keys;
- nested object/list serialization;
- a planted raw-newline encoder violation to prove the oracle has teeth.

This is bounded serialization evidence. It does not claim full canonical JSON
correctness over every possible input tree.

## Commands

Focused new grid:

```bash
PYTEST_DISABLE_PLUGIN_AUTOLOAD=1 pytest -q tests/runtime/test_canonical_json_escape_grid.py
```

Result:

```text
...                                                                      [100%]
3 passed in 0.13s
```

Focused canonical family:

```bash
PYTEST_DISABLE_PLUGIN_AUTOLOAD=1 pytest -q \
  tests/runtime/test_canonical_json_escape_grid.py \
  tests/runtime/test_canonical_primitives_vectors.py \
  tests/runtime/test_canonical_primitives_fuzz_gate.py \
  tests/runtime/test_canonical_primitives_disaster_state.py \
  tests/runtime/test_canonical_authority_promotion.py \
  tests/runtime/test_canonical_live_path.py \
  tests/state/test_canonical_size_bounds.py
```

Result:

```text
......................................................                   [100%]
54 passed in 1.17s
```

Rust unit focus:

```bash
cd rust-runtime
cargo test -q -p zenodex-runtime-core canonical
```

Result:

```text
20 passed
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
```
