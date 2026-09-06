# Custody successor receipt boundary

Python and Rust now provide `verify_asset_transfer_lane_module_custody_receipt_v1`
over the existing receipt candidate and verifier port. This additive entry
checks the reviewed custody semantic family, authenticated occurrence,
governed structural binding and supplied binding identity before exactly one
custody recomputation. The retained receipt helper then supplies the selected
module image and the recomputed canonical journal bytes to the verifier port.
The legacy transfer entry retains its previous recomputation behavior.

The new entry inherits the succinct-only receipt kind, nonempty receipt,
16 MiB receipt ceiling, ACTIVE_NEW release and `accepts_new_objects` checks,
plus the selected release's canonical journal ceiling. Its returned witness
retains the existing controlled constructor. It grants no publication authority.
Current store head and writer authority remain shell admission obligations.

## Executable evidence

The root replay passed 122 Python cases across the new receipt suite and the
retained binding, custody and shared-vector suites. The new suite contributes
18 cases. Root Rust replay passed 18 tests in the new receipt target, 10 in
the custody binding target, 3 in custody execution and 78 in retained
release-route/receipt behavior. The new Rust target includes the 10 existing
binding tests; these counts must not be summed as distinct obligations.

Positive controls record the exact image, journal and receipt bytes at the
port. Negative controls cover each coherently rebuilt semantic-root mismatch,
foreign authenticated occurrence and profile, foreign module context, supplied
binding mismatch, inactive or malformed release state, receipt kind, empty and
oversize receipt, and exactly fitting versus one-byte-over journal size.
Python instruments custody and legacy recomputation counts. Rust observes
guard precedence through an incompatible legacy acceptance and checks the
single custody call in the source. Neither observation proves universal
implementation refinement.

Two disposable-process Python semantic mutants were killed by named tests:

- Replacing `_bind_asset_transfer_custody_output_structural_v1` with the legacy
  structural helper causes all three cases of
  `test_custody_semantic_root_mismatches_reject_before_recomputation_or_receipt_port`
  to fail.
- Replacing the canonical journal ceiling condition with `False` causes
  `test_exact_journal_release_ceiling_accepts_and_one_more_byte_rejects` to fail.

The worker's Rust candidate initially failed to compile because its included
fixture used inner module documentation. Converting that fixture header to
ordinary comments preserved its tests and enabled the include. Root also
repaired an invalid negative fixture that panicked while hashing its registry;
it now supplies the malformed ordinary Rust registry directly to the receipt
entry and observes the exact rejection. The shared fixture gained explicit
epoch and journal-ceiling parameters so the new boundary cases rebuild their
committed identities coherently. Python test wrappers now carry their exact
input and output types. No production guard or legacy expectation was weakened.

```bash
python3 -B -m pytest -q -p no:cacheprovider \
  tests/core/test_asset_transfer_custody_receipt_verification_v1.py \
  tests/core/test_lane_module_release_route_binding_v1.py \
  tests/core/test_asset_transfer_custody_release_route_binding_v1.py \
  tests/core/test_asset_transfer_custody_binding_vector_v1.py \
  tests/core/test_asset_transfer_lane_module_custody_v1.py

cargo test --manifest-path zk/global_settlement_abi_v1/Cargo.toml --offline --locked \
  --test asset_transfer_custody_receipt_verification \
  --test asset_transfer_custody_release_route_binding \
  --test lane_module_release_route_binding \
  --test asset_transfer_lane_module_custody

python3 -B -m ruff check src/core/lane_module_receipt_verification_v1.py \
  tests/core/test_asset_transfer_custody_receipt_verification_v1.py
python3 -B -m mypy --explicit-package-bases --follow-imports=silent \
  src/core/lane_module_receipt_verification_v1.py \
  tests/core/test_asset_transfer_custody_receipt_verification_v1.py
```

## Qualification boundary

Signature helpers and receipt verifiers in these tests are synthetic doubles.
Their accepting release/evidence metadata is test data. Zero-custody tests
observe successor-image dispatch; they do not demonstrate cryptographic
rejection of a genuine receipt for an older image. This increment supplies no
genuine RISC0 receipt, measured successor guest, qualified release/profile,
store-current admission, activation, publisher mount or migration. Whole-core
formal completeness and production value-safety remain open.
