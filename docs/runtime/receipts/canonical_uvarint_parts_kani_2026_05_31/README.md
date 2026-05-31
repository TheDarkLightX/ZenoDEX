# Canonical uvarint helper Kani receipt

Date: 2026-05-31

This receipt records a CBC decomposition slice for the Rust canonical uvarint
encoder. The public `encode_uvarint(u128) -> Vec<u8>` now delegates to a
heap-free helper:

```text
encode_uvarint_parts(u128) -> ([u8; 19], len)
```

Kani verifies the helper is total on the full `u128` domain, returns a nonempty
length bounded by the exact LEB128 maximum for `u128`, and the final emitted byte
has its continuation bit cleared. Byte-for-byte semantics of the public `Vec`
wrapper remain covered by Rust unit vectors and the Python/Rust canonical
framing grid.

## Kani command

```bash
cd rust-runtime
cargo kani -p zenodex-runtime-core \
  --harness canonical::kani_contracts::encode_uvarint_parts_total_and_len_bounded \
  --output-format terse \
  -Z unstable-options \
  --harness-timeout 5m
```

Result:

```text
Checking harness canonical::kani_contracts::encode_uvarint_parts_total_and_len_bounded...

VERIFICATION RESULT:
 ** 0 of 41 failed

VERIFICATION:- SUCCESSFUL
Verification Time: 0.26142544s

Manual Harness Summary:
Complete - 1 successfully verified harnesses, 0 failures, 1 total.
```

## Regression commands

```bash
cd rust-runtime
cargo fmt --check
cargo test -q -p zenodex-runtime-core canonical
cargo test -q -p zenodex-runtime-cli canonical
```

Result:

```text
zenodex-runtime-core canonical: 20 passed
zenodex-runtime-cli canonical: 1 passed
```

Python/Rust framing grid:

```bash
PYTEST_DISABLE_PLUGIN_AUTOLOAD=1 pytest -q tests/runtime/test_canonical_framing_grid.py
```

Result:

```text
..                                                                       [100%]
2 passed in 0.67s
```

Deployment/profile gate:

```bash
python3 tools/check_deployment_profiles.py
```

Result:

```text
local-dev: ok
production-strict: ok
public-testnet: ok
```

## Negative tractability note

Two stronger Kani targets were attempted and timed out under the 5 minute
harness limit:

- public `Vec` encoder shape plus round-trip over full `u128`;
- heap-free helper shape plus round-trip over symbolic bounded domains.

Those semantic byte-equality claims stay in the deterministic grid and vector
tests. This Kani slice is intentionally limited to totality and canonical
termination shape on the actual helper used by the public encoder.
