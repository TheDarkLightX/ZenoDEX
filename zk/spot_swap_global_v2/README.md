# Spot swap/global V2 native successor

This standalone crate is the native Rust counterpart of the reviewed Python
pure joint Spot/asset/global successor (`src/core/spot_swap_plan_v2.py`,
`spot_swap_state_v2.py`, `spot_swap_global_v2.py`). Its values are pure
candidates with no authentication, settlement, receipt, publication or runtime
authority. It reuses the pinned GlobalSettlementABI V2 path dependency for
assets, global state, occurrences, effect plans and the shared refiner; it does
not alter that crate, any existing image or release profile.

## What it implements

- `SpotSwapStateV2`: one CPMM pool (all eleven `PoolState` fields), the complete
  LP owner/share table with the four duration/churn metadata fields (dormant
  rows included), the minimum locked owner, canonical `compute_pool_id`
  identity, per-sender inner intent nonces, the existing 4096-row and 1 MiB
  ceilings (row capacities are checked before any row is validated).
- `SpotSwapIntentV2`: the complete legacy `SwapIntent` body. Field scalars keep
  the codec's exact integer text (at most 256 bits) or text; a non-scalar value
  is carried as `Nested` and classified in Python order.
- `quote_cpmm_swap_exact_in_v2` / `quote_cpmm_swap_exact_out_v2`: the v8
  equations with the settlement wrapper (ceil gross fee wholly retained in
  reserves, floor output, minimal sufficient exact-output gross input, 200-bps
  overdelivery ceiling) using checked `u128` intermediates. The bound argument
  is in `src/quote.rs`; the largest intermediate is below `2^108`.
- `plan_spot_swap_v2`: the scalar planner with the Python rejection order.
- `transition_spot_swap_global_v2`: complete asset-origin, projection, policy,
  identity, plan, nonce, statement and successor derivation through the
  unchanged global refiner. Economic rejections carry the Python code strings;
  structural failures are `SpotSwapInputErrorV2` with stable `INPUT_*` codes.

`SpotSwapGlobalRejectedV2` stores one state root. Its `post_state_root()`
accessor returns that same pre-state root, so a rejection cannot carry a
contradictory successor root. The parity response bytes remain unchanged.
Projection comparisons borrow existing rows instead of allocating copied
tables; complete validation remains in place. The local benchmark found no
meaningful speedup, and no validation cache was introduced.

## Shared execution frame

`prepare_spot_swap_global_from_frame_v2` decodes a bounded canonical frame and
calls the same pure transition. Native replay and the candidate guest import
this function. The separate [execution workspace](../spot_swap_global_risc0/README.md)
specifies the six components, accepted-only two-root journal and verifier
obligations. Each input and complete successor component is limited to 1 MiB;
this additional transport ceiling restricts the global state's larger row-bound
domain. A successor exceeding it produces `SuccessorBounds` without a journal.
Native replay is tested; the actual zkVM target and genuine receipt are unqualified.

The Rust scalar pool representation covers the joint state's admitted domain.
Its `u64` LP supply does not represent every standalone Python pool snapshot
(which permits `u128`). Scalar context subjects retain Python's nonempty,
512-character bound. Arbitrary forged Python objects and oversized unsupported
nested intent fields are outside the correspondence claim.

Rejection precedence, copied from the Python transition:

```text
UNSUPPORTED_FIELDS -> OCCURRENCE_CONTEXT_MISMATCH -> REPLAY_ALREADY_CONSUMED
-> OCCURRENCE_COMMAND_MISMATCH -> PROJECTION_MISMATCH -> ASSET_ORIGIN_MISMATCH
-> UNSUPPORTED_ASSET_POLICY -> [sender/recipient identity input error]
-> SUBJECT_MISMATCH -> EXPIRED -> INVALID_NONCE (range) -> POOL_MISMATCH
-> ASSET_MISMATCH -> POOL_INACTIVE -> UNSUPPORTED_CURVE -> QUOTE_REJECTED
-> SLIPPAGE_LIMIT -> INSUFFICIENT_BALANCE -> BALANCE_OVERFLOW
-> INVALID_NONCE (sequence) -> SUCCESSOR_REJECTED
```

## Parity transport (`examples/parity.rs`)

Test transport only; it defines no production receipt or wire successor. One
request per line:

```json
{"assets": <AssetLaneCustodyStateV2.to_canonical()>,
 "spot": <SpotSwapStateV2.to_canonical()>,
 "state": <GlobalEconomicStateV2.to_canonical()>,
 "intent": <spot_swap_command_body_v2(intent)>,
 "occurrence": <EconomicCommandOccurrenceV2.to_canonical()>,
 "block_timestamp": <int>}
```

Exactly those six keys are admitted. Responses:

```json
{"status": "accepted", "post_assets": ..., "post_spot": ..., "post_state": ...,
 "effects": ..., "statement_root": "0x..", "refinement_root": "0x.."}
{"status": "rejected", "code": "<Python code value>", "pre_state_root": "0x..",
 "post_state_root": "0x..", "effects": <empty canonical plan>}
{"status": "input_error", "code": "<INPUT_*>"}
```

Input error codes: `INPUT_LINE`, `INPUT_JSON`, `INPUT_REQUEST_SHAPE`,
`INPUT_ASSETS`, `INPUT_SPOT_STATE`, `INPUT_GLOBAL_STATE`, `INPUT_OCCURRENCE`,
`INPUT_BLOCK_TIMESTAMP`, `INPUT_INTENT`, `INPUT_SENDER_IDENTITY`,
`INPUT_RECIPIENT_IDENTITY`, `INPUT_INTERNAL`. The detail text goes to stderr.

Bounds: 16 MiB per line; assets and Spot components at most 1 MiB (the ABI
rootable ceiling); occurrence at most 64 KiB; intent at most 128 KiB. The line
is parsed by a strict visitor that rejects duplicate object keys after JSON
unescaping (so `"reserve0"` next to `"reserve0"` is a duplicate). Each
typed component must then re-encode to the bytes of the parsed JSON value.
Raw-line key order and whitespace are normalised by the parser before that
check and are not observed. Requests exceeding this transport's bounds remain
unqualified, even if their component states are independently valid. Increasing
these bounds requires a separate resource review.

`examples/quote.rs` is the separate bounded quote tool for exhaustive
arithmetic differential testing (schema in its module docs).

## Build and check (offline, bounded)

```text
export CARGO_TARGET_DIR=/dev/shm/zenodex-spot-native-20260914
cargo check   --offline --locked --manifest-path zk/spot_swap_global_v2/Cargo.toml --all-targets -j 2
cargo test    --offline --locked --manifest-path zk/spot_swap_global_v2/Cargo.toml -j 2
cargo clippy  --offline --locked --manifest-path zk/spot_swap_global_v2/Cargo.toml --all-targets -j 2 -- -D warnings
cargo build   --offline --locked --manifest-path zk/spot_swap_global_v2/Cargo.toml --examples -j 2
python -m pytest -q tests/core/test_spot_swap_global_rust_v2.py
```

Check that `/dev/shm` has at least 4 GiB free first and keep the target below
1 GiB. The parity suite removes its own temporary mutation-build directory.
`cargo generate-lockfile --offline --manifest-path zk/spot_swap_global_v2/Cargo.toml`
reproduced the checked lockfile unchanged. Review dependency differences before
adopting any future lockfile regeneration.

## Nonclaims

No formal completeness, no genuine receipt, no finality, no historical
migration, no mounted publication, no LP mint/burn/transfer, no permanent-pool
policy change, no parity claim without root's independent Python/Rust run.
