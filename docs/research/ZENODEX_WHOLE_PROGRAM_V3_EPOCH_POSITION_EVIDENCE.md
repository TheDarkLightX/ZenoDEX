# Restricted ASSET epoch-position extension

Date: 2026-09-05. Exact observed base: `d02e2693476e597bbbb7cae75fb2905e004b0fff` plus the owned files below. Other concurrent authentication, publisher and raw-receipt-pipeline changes are outside this packet. The earlier one-command consumer checkpoint remains retained at `38c4a75e0` and in the allocation publication contract. This successor changes the pure allocation consumer; it grants no publication authority.

## Contract and source ownership

The acquired initial committed source has height H. Every command in one economic epoch executes at H + 1. The first allocation pair uses the exact acquired source; each later pair uses the preceding checked prospective post-state. Its command pre-root must equal that predecessor's actual complete state root. Intermediate global heights therefore remain H + 1. Incrementing the height for each command contradicts the existing epoch refinement contract.

The new data-only `AssetTransferEpochPositionV1(epoch_source, occurrence_index)` has an exact index in 0–63. The shell authenticates the initial source; the pure consumer checks equality with the epoch candidate's complete pre-state and supplies positions from its ordered fold. Position data alone does not authenticate a source or establish ancestry for a separately invoked later pair.

Python's new `verify_asset_transfer_epoch_fragment_receipt_v1(witness, candidate, position)` validates an owned position and candidate before selecting the closed private epoch mode. Rust exposes `check_asset_transfer_epoch_allocation_v1(candidate, position)` for pure diagnostics and the corresponding receipt admission function. The existing standalone relation and admission retain adjacent-height semantics and their original public signatures. Unknown private mode values, including a forged same-type Python enum instance, reject.

The consumer's public `check_asset_transfer_epoch_allocation_v1` signature is unchanged. It still enforces exact ordered cardinality, singleton ASSET lane/module membership, occurrence identity, complete predecessor binding, unchanged claimant and unsupported-table rules, the 12-slot projection, and mandatory allocation certificate checking. Only the allocation admission invoked inside the fold changes. No wire schema, journal identity, state root, occurrence height or serialized profile is normalized or reinterpreted.

The existing controlled module admission still binds the private-port preimage to an opaque verified module witness before lifting the fragment to the coordinator projection root. `fragment.binding_root` remains the required supplied binding root; the receipt root is a different identity. This packet does not make ordinary accepted diagnostics into an authority capability.

## Executable evidence

The final combined Python command passed **270 tests in 35.30 seconds**:

```bash
PYTHONDONTWRITEBYTECODE=1 python3 -m pytest -q --tb=short -p no:cacheprovider \
  tests/core/test_asset_transfer_epoch_position_v1.py \
  tests/core/test_asset_transfer_epoch_allocation_v1.py \
  tests/core/test_asset_transfer_global_allocation_v1.py \
  tests/core/test_asset_transfer_receipt_admission_v1.py \
  tests/core/test_global_accounting_allocation_projection_v1.py \
  tests/core/test_global_accounting_allocation_certificate_v1_golden.py \
  tests/formal/test_lean_asset_transfer_epoch_position_v1.py
```

The new consumer positives cover 1, 2, 8, 9 and 64 commands. Each is also accepted by the existing complete epoch verifier using deterministic mock receipt ports. Retained zero/65, omission, reordering, module-membership, conserved reassignment, malformed-input, unsupported-table and mandatory-checker controls remain. The original two-command discovery test now directly exercises the unchanged standalone admission: the second pair still rejects with `GLOBAL_OCCURRENCE_DRIFT` there and succeeds under the explicit epoch position.

Eleven shared Python/Rust relation vectors cover first and second acceptance, first/second index swaps, source height/context/history substitutions, u64 source-height overflow, hidden intermediate height, wrong predecessor and history drift. The source-equality omission mutant is admitted by the mutated predicate and refused by the retained correct guard. These are independent expected outcomes using real deterministic module recomputation; cryptographic witness constructors are exercised through recording mock verifier ports.

The scoped offline Rust command passed **103 tests**: 20 library tests, one epoch-position vector test, four projection tests and 78 retained receipt/composition tests. It used an existing populated ABI target directory, with incremental compilation disabled; no guest build or dependency download ran.

```bash
cd zk/global_settlement_abi_v1
CARGO_INCREMENTAL=0 cargo test --offline --lib \
  --test lane_module_release_route_binding \
  --test global_accounting_allocation_projection \
  --test asset_transfer_epoch_position
CARGO_INCREMENTAL=0 cargo clippy --offline --lib \
  --test lane_module_release_route_binding \
  --test global_accounting_allocation_projection \
  --test asset_transfer_epoch_position -- -D warnings
```

Rust test compilation took 18.92 seconds; the receipt harness took 14.11 seconds. Clippy passed in 16.91 seconds. After the test run, a Python admission docstring was corrected to assign initial authentication to the shell, and both golden files were regenerated. The Rust source and every semantic vector remained unchanged; the final Clippy run and final 270-test Python run include the corrected documentation/source pins.

The Rust receipt test constructs a real second deterministic module output and obtains its opaque witness through the existing recording verifier. It confirms distinct predecessor/current roots, unchanged target height, old standalone refusal, new admission success and final projection/certificate agreement. This admission-only fixture includes custody; it does not establish coordinator or publication acceptance for nonzero custody.

Ruff and mypy passed over these eight paths:

```bash
python3 -m ruff check \
  src/core/asset_transfer_epoch_position_v1.py \
  src/core/asset_transfer_epoch_allocation_v1.py \
  src/core/asset_transfer_global_allocation_v1.py \
  src/core/asset_transfer_receipt_admission_v1.py \
  tests/core/test_asset_transfer_epoch_position_v1.py \
  tests/core/test_asset_transfer_epoch_allocation_v1.py \
  tools/render_asset_transfer_epoch_position_v1_golden.py \
  tests/formal/test_lean_asset_transfer_epoch_position_v1.py
python3 -m mypy --cache-dir=/dev/null \
  src/core/asset_transfer_epoch_position_v1.py \
  src/core/asset_transfer_epoch_allocation_v1.py \
  src/core/asset_transfer_global_allocation_v1.py \
  src/core/asset_transfer_receipt_admission_v1.py \
  tests/core/test_asset_transfer_epoch_position_v1.py \
  tests/core/test_asset_transfer_epoch_allocation_v1.py \
  tools/render_asset_transfer_epoch_position_v1_golden.py \
  tests/formal/test_lean_asset_transfer_epoch_position_v1.py
```

Style routing selected deterministic core and typed Rust kernels. Redflag routing found 20 medium findings, all `expect`/`unwrap`/`unreachable!` uses inside existing Rust test code; no production finding was reported. Complexity routing retained the two inherited long module-admission functions and flagged the shared ordered Python relation at 70 nonblank lines/five parameters. Its single private mode parameter preserves the existing contiguous guard order and semantic mutation controls; the docstring records this deliberate local exception. Scanner output is triage evidence only.

## Narrow Lean result

[AssetTransferEpochPositionV1.lean](../../lean-mathlib/Proofs/AssetTransferEpochPositionV1.lean) imports only `Std.Tactic`. The installed pinned Lean compiler was verified as 4.27.0, commit `db93fe1608548721853390a10cd40580fe7d22ae`. No Lake build, Mathlib download or remote proof job ran.

```bash
cd lean-mathlib
lean --version
lean -DwarningAsError=true Proofs/AssetTransferEpochPositionV1.lean
```

The companion gate compiles all eight fixed statements and prints their axioms. Only the permitted standard Lean axioms may appear. The statement inventory is:

- `accepted_step_binds_height_and_predecessor`: accepted steps bind output height H + 1, exact predecessor root and index < 64.
- `run_append` and `accepted_prefix_has_exact_intermediate_state`: a successful concatenated fold has an exact intermediate state shared by its accepted prefix and suffix.
- `accepted_run_length_bound`: an accepted run starting at i ≤ 64 has i + length ≤ 64.
- `accepted_nonempty_run_height`: every accepted nonempty fold ends at H + 1.
- `two_command_nonempty_control`, `wrong_prefix_root_rejects` and `hidden_intermediate_height_rejects`: inhabited acceptance and independent rejection controls.

Three mutations alter only `step`, preserving every theorem statement: omit predecessor-root equality, construct height H, or remove the index limit. Every mutant fails compilation of the unchanged theorem packet and independently evaluates a concrete bad trace to `true` with definitions alone. Proof-term errors therefore are not the sole mutation oracle.

The model uses natural-number roots and heights. Connecting these symbols to canonical cryptographic identities, decoded full state and deployed admission remains an explicit refinement premise. Runtime use requires H < 2^64 - 1; the Rust relation checks addition and the Python relation cannot match an out-of-range target against validated u64 state. This control-flow theorem adds no claim about ownership, signatures, accounting correctness or durable publication.

## Retained nonzero-custody disagreement

The new epoch position does not repair an independent accounting mismatch. The retained test `test_nonzero_custody_retains_module_coordinator_conservation_disagreement` rebuilds module evidence for controlled USD custody at 1, 7 and 2^127 atoms. In each case:

```text
private_port.pre_state.owned_and_custodied_atoms(USD)
  = module_effect.owned_and_custodied_pre_atoms + controlled_custody
```

[asset_transfer_module_v1.py](../../src/core/asset_transfer_module_v1.py) populates the effect's pre/post conservation totals from `_account_totals` (lines 256–257 at this subject). [asset_lane_coordinator_v1.py](../../src/core/asset_lane_coordinator_v1.py) compares them with the private port's balances-plus-custody totals (lines 119–126), yielding `CONSERVATION_STATE_MISMATCH`. The test uses recomputed module/private-port inputs; it does not forge a verified receipt.

The 1–64 end-to-end positives therefore use zero custody. The retained zero-amount claimant test is a refusal/identity control and does not qualify a nonzero custody workflow. Existing nonzero standalone allocation tests remain useful for that narrower relation. This mismatch remains a feature blocker until the producer/coordinator accounting contract is separately reconciled and proved; disabling the case does not complete that feature.

## Regeneration and immutable subject

Both fixtures were regenerated by their recorded commands:

```bash
PYTHONDONTWRITEBYTECODE=1 python3 tools/render_asset_transfer_global_allocation_v1_golden.py
PYTHONDONTWRITEBYTECODE=1 python3 tools/render_asset_transfer_epoch_position_v1_golden.py
PYTHONDONTWRITEBYTECODE=1 python3 tools/render_asset_transfer_global_allocation_v1_golden.py --check
PYTHONDONTWRITEBYTECODE=1 python3 tools/render_asset_transfer_epoch_position_v1_golden.py --check
```

The original standalone fixture differs from the observed base in exactly its four `source_sha256` values. Removing only that metadata object leaves exactly equal parsed JSON; no expected result, amount, root or semantic mutant was changed.

| Owned file | SHA-256 |
|---|---|
| `src/core/asset_transfer_epoch_position_v1.py` | `87e04c3ea4bf0fc8889b978a691f3d644110dbf7406001d47e015b39da39bf78` |
| `src/core/asset_transfer_epoch_allocation_v1.py` | `34a5012d84f130921ce80c87e367c56bfe92d6e6d7c59ccd6774d8fbc3bcb071` |
| `src/core/asset_transfer_global_allocation_v1.py` | `a4099cb3e53c26ef981e384e92cbdc5c04b80d5bdf7c14cd3b2d296a8830f028` |
| `src/core/asset_transfer_receipt_admission_v1.py` | `2a954812ee4d4cbcb537872ff108c52576c6c5aef7eaca28bab124d27488837f` |
| `tests/core/test_asset_transfer_epoch_position_v1.py` | `7d5ad3420167182277d28eb5e2ef87423ec1582ebbc856f1826d3eec6039a26a` |
| `tests/core/test_asset_transfer_epoch_allocation_v1.py` | `d7dc522f8321d083bd332557bb47890739e3013e05be6bbce0a92c68f5d4afd1` |
| `tests/data/asset_transfer_epoch_position_v1_golden.json` | `2d04f988928e1402eed64645fd55aceb78e2d8606045397c0b1746158745e844` |
| `tests/data/asset_transfer_global_allocation_v1_golden.json` | `269653cae098016e7239f56d6de0cc95eccfee5db14b8628d77bbd7185fbcf0b` |
| `tools/render_asset_transfer_epoch_position_v1_golden.py` | `47c7a971a34924e0e70e91f93fb6910e598035f333cac347e63782b18b941668` |
| `lean-mathlib/Proofs/AssetTransferEpochPositionV1.lean` | `7ec2f791e70661cf7e252c2d256ecbbcac769e2f64c21013dacbb511bcf024ac` |
| `tests/formal/test_lean_asset_transfer_epoch_position_v1.py` | `f87111809f84e71cf8a0657fed97b20f4ac8d8ad7376b8625a986626f73f27bb` |
| `zk/global_settlement_abi_v1/src/asset_transfer_global_allocation.rs` | `3d785828fb676c0c2d112a55714b82ec13f245ee1886d175f122b482cd88c9bd` |
| `zk/global_settlement_abi_v1/src/asset_transfer_receipt_admission.rs` | `3edf5982fd2c3642da198968d28f14fd084c42a93207a1f8ef7c91d3c349a76d` |
| `zk/global_settlement_abi_v1/tests/asset_transfer_epoch_position.rs` | `4f9dd627182831a95d8382176d25a62031a1b7cb38c616f5a709993e1dd9b4fb` |
| `zk/global_settlement_abi_v1/tests/allocation_projection/receipt_tests.rs` | `fe400c58ace188ddec004e2bbd7d7a6a1fc0f8c12900d4f68bc7e1176f8999ea` |

## Qualification limits and next work

This is source-bound pure-consumer and admission evidence. The initial state must still come from an authenticated committed source and each module witness from the intended cryptographic verifier; initial claimant ownership is not inferred from conservation. Complete epoch verification, command authentication, context/profile admission, current writer authority and atomic publication remain separate required gates.

At freeze, the raw receipt pipeline remains explicitly one occurrence, and the existing real route guest still invokes the standalone adjacent-height relation. No wider pipeline mount or real multi-command ASSET route proof is established here. ABI source closure changed, so old real receipts/proof manifests remain historical evidence for their exact subjects until their measured guests and profiles are separately requalified.

Whole-program preservation, all twelve lanes, the four cross-lane routes, datastore refinement, deployment-complete no-bypass, initial ownership and concrete signature semantics are not proved by this packet. Full local repository gates, new RISC0 guest builds and remote jobs were not run. No release/profile activation, migration or live balance change occurred. The next consumer integration should preserve authenticated ordered evidence at every index, then qualify its actual guest/profile subject while the custody mismatch is repaired separately.
