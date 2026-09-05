# Isolated BLS proof-input preparation replay

Date: 2026-09-05. Authority: `NONE`. Result: deterministic local input
preparation and genuine BLS verification, with no new RISC0 receipt generation.

The prepared profile is
`0x0dd53a549df3b3c045f0932ad2f3176c871d6fbdcf90d1c426a00a292dd7a9f8`.
It retains the four measured guest images from the
[previous receipt qualification](ZENODEX_WHOLE_PROGRAM_V3_FINAL_RECEIPT_QUALIFICATION.md).
It replaces the historical placeholder signer policy with a canonical public
test key and a SHADOW signature-verifier release selected explicitly for
`ISOLATED_QUALIFICATION`. The five isolated evidence references have retained
preimages. No production evidence labels are added.

## Inputs and authority boundary

The checked compatibility seed is
`tests/data/isolated_bls_proof_seed_v1.json`, 35,907 bytes, SHA-256
`e6d7cb2a1b19e3e9f40fef98b85b168ad04c4cfb4d4b443b13fa08ef676d6ee6`.
It is byte-identical to `inputs/188-route.input.json` in the previously retained
`zenodex-v3-final-replay02-subject.tar.gz`, SHA-256
`7a7aff73da3834ba590c3a996ea82fd7d328d901052d7e3fb8cc03e36487d2a1`.
The seed contains public isolated state and assumed economic release labels;
it contains no machine paths or signing secrets.

The public scalar is the constant 25. Its authorization permits only the
existing ASSET transfer, selected final route, nonce 9 and height 1. The
existing policy transfers 30 USD atoms to Bob and charges 2 atoms to treasury.
The existing kernels independently of the signature backend produce balances
Alice 68, Bob 40 and treasury 7 from 100, 10 and 5. These are test-state units;
genesis ownership and live token issuance are unverified assumptions.

The genesis allocation assumption commits explicit atom occurrences together
with chain, deployment and writer epoch. It excludes the final profile and
full state hash. The initial-state statement separately binds the complete
final state. This removes the profile/policy/source-commitment cycle without
claiming authenticated genesis ownership.

The builder produces module, coordinator, route, initialization and epoch
inputs; raw command body, signing message and signature; the authorization
and signature registries; and predicted journals. The signature verifies the
exact economic-intent message, including final profile/policy/release context.
The existing production authentication entry remains unavailable to this
isolated verifier purpose.

The retained guests can carry the rebuilt policy and profile roots in their
existing schemas. They do not perform BLS verification. The existing
file-driven route exporter consumes `route.input.json` without invoking the
historical placeholder-signature fixture. A future genuine receipt batch must
still pass raw-signature reauthentication, receipt-backed composition, the
allocation consumer, epoch admission and publication mediation.

## Acquired evidence

The retained preparation contains 743 source files, 12,417,843 bytes, including
the complete current Python `src` subtree and the exact preparation tools,
test and seed. Source manifest SHA-256:
`5ad80fa51bf5c77f4e86835bd5a07c324370e56f74730630efc3cc823885bac9`.

The runtime snapshot contains 534 files, 33,937,443 bytes: the interpreter,
observed imported standard-library files, and installed active base-dependency
distribution files. Runtime manifest SHA-256:
`ae9a48221a27a611126655e4dca8a92785f88b6b4e5ffb6f28aa65f3f47504fa`.
Bytecode caches and `direct_url.json` are explicitly omitted. Installed RECORD
inventories supply the BLS dependency file sets. The existing packaging tool
has no RECORD, so its two installed directories receive a separately labeled
bounded filesystem inventory.

The observed versions are py-ecc 8.0.0, eth-typing 5.2.1, eth-utils 5.3.1,
eth-hash 0.7.1, cytoolz 1.1.0, toolz 1.1.0, typing-extensions 4.15.0,
pydantic 2.12.5, pydantic-core 2.41.5, annotated-types 0.7.0 and
typing-inspection 0.4.2. Packaging 24.0 is existing evidence tooling, with no
new installation or dependency addition. CPython remains the previously
observed 3.12.3 interpreter. The installed dependency snapshot is an observed
subject, not a portable package lock or proof of loaded-code correspondence.

Seven fixed control requests, independent of the final profile, exercise raw BLS, foreign
key, wrong message, legacy prehash, short signature, noncanonical key and wrong
algorithm. Their retained report SHA-256 is
`0a38402a51c9fa650c0b80eb94822236dfb2b3d9ad284304f58316c763f8bca4`.
The final economic signing message also verifies through the concrete acquired
artifact binder. The full source inventory, interpreter, dependency resolution
and file bytes are checked both before and after preparation. Replay fails
closed if any selected source or dependency changes during the checks.

The four previously qualified verifier binaries are acquired again and checked
against their retained SHA-256s. Their exact bytes, historical receipt-verifier
manifest and registry are copied into the output. This is artifact measurement;
no new receipt verification or publication occurs during preparation.

## Replay and retained artifacts

Use fresh output directories and the retained four-endpoint metadata:

```bash
PYTHONDONTWRITEBYTECODE=1 python3 tools/prepare_isolated_bls_proof_v1.py \
  --output "$ZENODEX_BLS_INPUT_DIR" \
  --evidence "$ZENODEX_BLS_EVIDENCE_DIR" \
  --retained-verifier-metadata "$ZENODEX_RETAINED_VERIFIER_METADATA"
```

The local invocation completed successfully. A second preparation from the
frozen evidence reproduced every prepared input byte. All 27 output artifact
hashes passed an independent file-hash replay; direct G2Basic verification of
the retained raw message and signature passed.

| Artifact | SHA-256 |
| --- | --- |
| `zenodex-v3-bls-preparation01.tar.gz` | `9a2d09b38ae5344729f9ea0d25c9cf799d1b4372732d34fc5a150063cbde4e0a` |
| `zenodex-v3-bls-preparation01-manifest.json` | `7ad0438ee8d7cfceca3c9c450d789c5e0fb6476c1bb1f49500c1279ab49fc1b6` |

The archive is 16,022,208 bytes. Its 1,313 regular members include source and
runtime preimages, input artifacts, replay report and preparation output. Every
member size and SHA-256 was replayed successfully. No symlinks or path escapes
are present.

The focused command
`PYTHONDONTWRITEBYTECODE=1 python3 -m pytest -q -x -p no:cacheprovider tests/test_prepare_isolated_bls_proof_v1.py`
passed all 20 tests in 22.28 seconds after the input-assembly split. Controls
cover source/dependency drift before and during preparation, changed or
ambiguous input, conserved misattribution, wrong retained verifier bytes,
genesis cycle independence, exact replay and refusal to overwrite output.
Ruff and focused mypy passed for all three tools. Scanner results are triage
only. The explicit authentication and initial-input constructors retain seven
and five parameters respectively so their separate governed inputs stay visible;
these tooling helpers grant no authority.

## Remaining qualification

After preparation, an independent current-source Rust replay consumed the
exact prepared `route.input.json`. The existing `final_input_economic_reference`
test in the route-composer shared crate passed. All six exported fields agree
exactly with the Python prediction: input, lane journal, route journal, effect
plan, projection root and refinement root. The route composer's independent
`check_reference.py` also passed, including its conserved-misattribution
refusal and independently computed account amounts. The original prepared
`reference.json` remains labeled as a Python prediction.

```bash
# From zk/asset_transfer_route_composer_risc0; use the existing cached ABI target.
CARGO_TARGET_DIR="$ZENODEX_CACHED_ABI_TARGET" CARGO_INCREMENTAL=0 \
  ZENODEX_FINAL_ROUTE_INPUT="$ZENODEX_BLS_INPUT_DIR/route.input.json" \
  ZENODEX_FINAL_ROUTE_REFERENCE="$ZENODEX_CURRENT_RUST_REFERENCE" \
  cargo test --offline -p zenodex-asset-transfer-route-composer-risc0-shared \
    --test final_input_reference -- --ignored --exact final_input_economic_reference
python3 check_reference.py "$ZENODEX_CURRENT_RUST_REFERENCE"
```

The retained output is `zenodex-v3-bls-rust-reference-current01.json`, accompanied
by its Rust and Python replay logs. This host replay compiled in 20.29 seconds
and executed its single test in 0.07 seconds. It downloaded no dependency and
generated no guest, proof or publication. The retained guest image versions
differ from the current expanded ABI source closure; this current-source
agreement does not establish correspondence to the retained ELF execution.
Later custody and epoch-position work is not retroactively qualified by those
images.

The subsequent [retained-source preflight](ZENODEX_RETAINED_GUEST_BLS_PREFLIGHT_20260905.md)
also matched all five journals using the exact saved shared libraries and
dependency pins. It remains a native replay. The earlier GPU batch completed
for its original profile and inputs; this new BLS profile requires fresh
receipts. Runpod is intentionally off, and no restart is requested here.

The next proof batch requires the exact retained build subject or direct
execution of its retained ELFs. Portable guest-image reproducibility remains
unqualified. Prove the three actual transfer receipts and the initialization
and epoch ROOT receipts, then verify their exact predicted journals through
the measured four-endpoint set and the raw-evidence publication pipeline.
Any source or policy amendment requires a new prepared subject.

The epoch's data-availability field carries a local source-manifest digest;
the finality field carries an explicit isolated assumption. Neither attests
external data availability or external finality. Loaded Python/dependency
correspondence, operating-system integrity, genesis ownership, complete epoch
commitment derivation, production no-bypass, durability and whole-program
refinement remain separate obligations. No live migration, activation,
provisioning, remote work or spending occurred in this preparation.
