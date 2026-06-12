# State-root LP duration-risk exhaustive field grid

Date: 2026-05-31

This receipt records a small deterministic assurance slice for the state-root v5
LP duration-risk metadata section. The target is field separation across the
optional metadata fields:

```text
(last_mint_timestamp, last_remove_timestamp, churn_tier, last_churn_update_timestamp)
```

The grid covers all combinations over:

```text
last_mint_timestamp in {None, 0, 1}
last_remove_timestamp in {None, 0, 1}
churn_tier in {0, 1, 2}
last_churn_update_timestamp in {None, 0, 1}
```

That is 81 tuples. The all-default tuple is sparse and must be a no-op under
the Python table model. The remaining 80 tuples must each produce a distinct
state root for the same `(pubkey, pool_id)` LP position.

Evidence added:

- Python authority sparse no-op check for all-default metadata.
- Python authority injectivity check over the 80 present metadata tuples.
- Z3 semantic injectivity check for the optional-field tuple encoding.
- Python/Rust differential check for all 80 present metadata tuples through the
  `verify-state-root` runtime CLI.

This is a field-separation grid, not a whole-state proof. It is intended to
close an example-only gap around optional LP duration-risk metadata without
adding another broad fuzz lane.

## Commands

```bash
python3 -m pytest -q tests/runtime/test_state_root_lp_duration_exhaustive_grid.py
```

Result:

```text
....                                                                     [100%]
4 passed in 0.65s
```

```bash
python3 -m pytest -q \
  tests/runtime/test_state_root_vectors.py \
  tests/runtime/test_state_root_disaster_state.py \
  tests/runtime/test_state_root_injectivity_proof.py \
  tests/runtime/test_state_root_lp_duration_exhaustive_grid.py
```

Result:

```text
..........................                                      [100%]
35 passed in 1.36s
```

## Optional Miri check

Attempted:

```bash
cargo miri test -q -p zenodex-runtime-core state_root::tests::lp_duration_present_entry_encodes
```

Result:

```text
error: the 'miri' component which provides the command 'cargo-miri' is not available for the 'stable-x86_64-unknown-linux-gnu' toolchain
```

No Miri evidence is claimed from this slice.
