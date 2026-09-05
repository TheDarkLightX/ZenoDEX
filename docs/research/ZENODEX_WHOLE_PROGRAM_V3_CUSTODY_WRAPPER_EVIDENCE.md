# Custody-complete wrapper: isolated pure implementation evidence

2026-09-05. This packet implements the first bounded step of the [custody repair design](ZENODEX_WHOLE_PROGRAM_V3_CUSTODY_REPAIR_DESIGN.md). The new wrapper is unmounted: release selection, receipt admission, raw publication pipeline and RISC0 guest entry points retain their prior behavior. No live profile, balance or authority changed.

## Implemented contract

`transition_asset_transfer_lane_module_custody_v1` consumes the existing exact V1 lane input and invokes the retained legacy wrapper. Its input snapshot validates complete physical balances plus custody against bounded supply. The wrapper already constructs identical pre/post custody. On acceptance the successor derives each conservation scalar from its corresponding actual private projection, then rebuilds the effect-plan root, port's effect root, journal's effect/private-port roots and semantic receipt root before validating the complete accepted value.

The leaf state, movement rows, fees, supply, issue/burn authority, replay occurrence, module pre/post roots and outbox remain those of the unchanged leaf execution. All leaf rejections pass through with their exact no-op result. No public boolean, callback, source-acquisition capability or receipt-witness constructor was introduced.

`recompute_asset_transfer_lane_module_custody_v1` independently recomputes the complete owned successor and requires equality with the revalidated supplied accepted value. Its return is ordinary freshly computed data. Release/receipt authority requires a later controlled adapter and cryptographic verifier.

The only existing file changed by this wrapper packet is the Rust crate's two-line module/export addition. The legacy Python/Rust leaf, wrapper, receipt admission and historical regression expectations remain unchanged. Other coordinator changes belong to the parent's separately reviewed repair, described below.

## Failing evidence and controls

The first focused test failed because the new wrapper module did not yet exist. Existing retained tests already exhibit the legacy nonzero-custody conservation mismatch. After implementation, the focused Python successor controls accept custody 0, 1, 7, 2^127, MAX_U128−116 and MAX_U128−115 against a 115-atom account total. They independently sum physical amounts, check exact frame/fee/replay fields and compose through the existing Python coordinator. The zero-custody observation is byte-identical to legacy for the same input/context.

The maximum valid total equals MAX_U128. Its next neighbor keeps each individual amount within u128 while making the aggregate overflow, and rejects during complete input validation. Additional controls cover 4096 custody rows including the last entry, 4097 refusal, duplicate keys, unrelated-asset custody, all three fee-owner alias classes, zero amount, insufficient balance, fee limit, unauthorized subject, coherent foreign accepted results, legacy-result substitution and retained mutable input aliases.

Two source mutations retain their actual adverse observations: omitting custody from both totals produces a structurally valid balances-only result which the coordinator refuses; omitting the private-port-root rebind is refused by the accepted-value constructor. No opaque receipt metadata is fabricated for these tests.

The new shared fixture has ten deterministic cases: seven complete accepted values (including an account at 2^127 with delta −32) and three exact leaf rejections. A separate malformed input has individually bounded amounts and an overflowing complete projection. The fixture is generated with independent expected totals and reject codes, using:

```bash
PYTHONDONTWRITEBYTECODE=1 python3 tools/render_asset_transfer_lane_module_custody_v1_golden.py
PYTHONDONTWRITEBYTECODE=1 python3 tools/render_asset_transfer_lane_module_custody_v1_golden.py --check
```

No existing golden fixture was regenerated for this successor.

## New coordinator counterexample retained

The initial Rust successor test first established complete Python/Rust accepted-value equality at custody 2^127, then failed its intended coordinator-acceptance assertion. The original coordinator converted each absolute holding to i128 before subtraction in `expected_movement_deltas`, lines 82–85. The unchanged custody row has delta zero but its absolute value cannot be converted to i128. The actual result was:

```text
custody_170141183460469231731687303715884105728
Rejected: STATE_EFFECT_MISMATCH
pre_lane_root = post_lane_root =
  0xce82dc8fa7965373ba068440e61ffc4aaec4c13e9a83dd47bb7e19ad7ac31fec
rows, conservation, fees, writes, consumptions and outbox = empty
```

This observation was obtained by `cargo test --offline --test asset_transfer_lane_module_custody -- --nocapture`, exiting 101, before the parent's separate coordinator repair. It is a fail-closed completeness/parity gap, not a demonstrated unauthorized publication. A second minimal input sets Alice's account to 2^127 and performs a 30-atom transfer with a two-atom fee; the required delta is −32 even though the pre-balance is above i128::MAX. The Python coordinator accepts both cases.

The correct invariant is signed representability of the difference. The parent owns replacing absolute narrowing with the existing `checked_signed_delta_v1(post, pre)`, including negative i128::MIN and typed refusal outside the signed range. The new successor test keeps the intended positive coordinator contract; the historical failing observation above remains visible rather than becoming a permanent incorrect refusal expectation.

## Python and Lean execution

The following combined command passed **58 tests in 11.82 seconds**, including 24 new wrapper controls, three actual Lean companion checks, three retained lane-wrapper tests and 28 retained epoch-consumer tests:

```bash
PYTHONDONTWRITEBYTECODE=1 python3 -m pytest -q --tb=short -p no:cacheprovider \
  tests/core/test_asset_transfer_lane_module_custody_v1.py \
  tests/formal/test_lean_asset_transfer_custody_completion_v1.py \
  tests/core/test_asset_transfer_lane_module_v1.py \
  tests/core/test_asset_transfer_epoch_allocation_v1.py
```

Ruff and mypy passed on the new core file, Python test, renderer and Lean companion. Style routing selected deterministic core/typed Rust; final hotspot routing reported no flagged function in the new production/renderer files. Redflag routing reported no finding in the two new production files. These scanners are advisory triage.

```bash
python3 -m ruff check \
  src/core/asset_transfer_lane_module_custody_v1.py \
  tests/core/test_asset_transfer_lane_module_custody_v1.py \
  tools/render_asset_transfer_lane_module_custody_v1_golden.py \
  tests/formal/test_lean_asset_transfer_custody_completion_v1.py
python3 -m mypy --cache-dir=/dev/null \
  src/core/asset_transfer_lane_module_custody_v1.py \
  tests/core/test_asset_transfer_lane_module_custody_v1.py \
  tools/render_asset_transfer_lane_module_custody_v1_golden.py \
  tests/formal/test_lean_asset_transfer_custody_completion_v1.py
```

[AssetTransferCustodyCompletionV1.lean](../../lean-mathlib/Proofs/AssetTransferCustodyCompletionV1.lean) imports only `Std.Tactic`. Direct compilation passed under the installed pinned Lean 4.27.0 with warnings treated as errors:

```bash
cd lean-mathlib
lean -DwarningAsError=true Proofs/AssetTransferCustodyCompletionV1.lean
```

Six statements are compiled and audited using actual `#print axioms` output: `completed_totals_preserve_supply`, `checked_completion_accepts_valid_projection`, `checked_success_is_u128`, `maximum_total_accepts`, `overflow_neighbor_rejects` and `custody_frame_is_necessary`. The main lemma universally derives equal bounded completed totals from explicit account conservation, unchanged custody, exact pre-projection supply and a u128 supply bound. The frame counterexample exhibits unequal post totals if custody changes.

Two mutations alter definitions only, preserving all theorem statements: omit the pre-custody term or erase the u128 bound guard. Each fails the fixed theorem packet and independently evaluates a concrete bad outcome to `true`. For the omitted-term mutation only the unused-variable warning is disabled, so that warning cannot supply the mutation verdict. The exact relation from these natural-number sums to actual runtime tables and leaf-conservation evidence remains an explicit refinement obligation.

## Source manifest and qualification ceiling

### Completed Rust repair and replay

The separately reviewed coordinator repair now computes signed differences
without narrowing absolute holdings. It also refuses either failed movement
derivation before comparing successful maps. The latter correction closes
CDR-01; the retained negative control uses unavailable-result sentinels. See
the [independent coordinator review](ZENODEX_WHOLE_PROGRAM_V3_COORDINATOR_DELTA_REVIEW.md)
for the initial finding, exact source hashes and closure review.

The combined cached, offline Rust command passed **153 tests**: 22 library,
five coordinator, three custody-wrapper, four projection, 41 economic
refinement and 78 receipt-binding tests. The high-custody and high-account
positive controls now compose successfully. Executed from
`zk/global_settlement_abi_v1`:

```bash
CARGO_INCREMENTAL=0 cargo test --offline --lib \
  --test asset_lane_coordinator \
  --test asset_transfer_lane_module_custody \
  --test lane_module_release_route_binding \
  --test global_accounting_allocation_projection \
  --test global_economic_state_effect_refinement
CARGO_INCREMENTAL=0 cargo clippy --offline --lib \
  --test asset_lane_coordinator \
  --test asset_transfer_lane_module_custody \
  --test lane_module_release_route_binding \
  --test global_accounting_allocation_projection \
  --test global_economic_state_effect_refinement -- -D warnings
```

Clippy passed. Retained test log `zenodex-v3-asset-coordinator-complete-green01.log`
has SHA-256 `fe7b5910bc8ae2be2ee152d1fcb352fadf7de6fef1ba0f67ffde71e30733becd`;
Clippy log `zenodex-v3-asset-coordinator-complete-clippy01.log` has SHA-256
`a63ed18a713c4e7d6f94b47189b556ee44d0b9677b1073a5cbee0c88a0eb991a`.
These are actual host Rust executions, with no new guest or production claim.

The original counterexample coordinator at commit `45003d8d286fce4921a183bab148474f44c03f1d` has SHA-256 `f4b8e0a1f79855136072168938df0c2003e830966b2e1e73b45fe3adebb5de5f`.

| Owned file | SHA-256 |
|---|---|
| `src/core/asset_transfer_lane_module_custody_v1.py` | `0d2118f275f6aa5bd308125b83b7c4528dbfc086749c8cb744bacea15983b45e` |
| `zk/global_settlement_abi_v1/src/asset_transfer_lane_module_custody.rs` | `28f1e2847ec28f07ed95f7c2c9e0dbcafdf781bafc446bd1d550ebae1b8c422b` |
| `zk/global_settlement_abi_v1/src/lib.rs` | `e5ee646b88420a3144d00665b5248569102fc629664aa6517e365fd731d9a35c` |
| `tests/core/test_asset_transfer_lane_module_custody_v1.py` | `15700d24078987cdf70376b4f9b8cefcf6cbcbb6aba96b9f6102c3006652e808` |
| `zk/global_settlement_abi_v1/tests/asset_transfer_lane_module_custody.rs` | `bccaf107542e7966149f139bd66811cd661addf51c25b7b0da49ae86cb2d4f75` |
| `tools/render_asset_transfer_lane_module_custody_v1_golden.py` | `c553fdc9eddfa36d3a5968495a8ff26a6faf9e2e9e5d5a6d857d54d8e44a2652` |
| `tests/data/asset_transfer_lane_module_custody_v1_golden.json` | `45c95f8d4be03dd67bed3414391c00eb4d6485357c68f2b9bef51ccfce827734` |
| `lean-mathlib/Proofs/AssetTransferCustodyCompletionV1.lean` | `fc6869b223a427ef22d040e71276d57c1f7b5bca9b95b471d4059ae771a1f8dc` |
| `tests/formal/test_lean_asset_transfer_custody_completion_v1.py` | `337c8466d6795419478334ffda31a0a07f6318e720e16627d220fcc86c7c7d93` |

No new guest, cryptographic receipt, production release or mounted custody path is qualified by this packet. Changed guest images require fresh evidence even for zero custody; retained old-image receipts remain valid for their exact old subjects. No heavy proof build, dependency download or remote job ran. Cached offline Rust and Std-only local Lean were the authorized compilation scope. Full u128 example coverage, full-runtime refinement, initial claimant ownership and whole-program safety are not inferred from these results.
