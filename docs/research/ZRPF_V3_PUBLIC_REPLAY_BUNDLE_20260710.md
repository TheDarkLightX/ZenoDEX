# ZRPF V3 Structural Public Replay Bundle

Status: source-frozen bundle; scoped replay claim requires native `--execute`

Evidence date: 2026-07-10
Scope: four-leaf, two-level ZRPF V3 structural tree

## Result

ZenoDEX now publishes a source-frozen replay bundle for one concrete Zeno
Recursive Proof Fabric (ZRPF) V3 tree. The bundle contains 21
manifest-governed artifacts plus its canonical manifest. It supports two
verification modes:

1. Static validation checks the external reference, manifest, complete file
   inventory, artifact hashes and modes, frozen source-closure records,
   transcript structure, tree facts, claim boundary, and exact seal-mutation
   relation.
2. Native replay additionally executes the digest-pinned verifier. It verifies
   seven RISC0 Succinct receipts, reconstructs the two level-one journals and
   level-two root, and confirms a one-bit Succinct-seal mutation receives the
   typed `receipt_verification_failed` rejection.

Static success reports `execution_checked=false`,
`scoped_public_replay_claim_allowed=false`, and
`status=static_bundle_accepted`. Native success reports
`execution_checked=true`, `scoped_public_replay_claim_allowed=true`, and
`status=executed_replay_accepted`.

The scoped replay claim accepted only after native replay is:

```text
PinnedReference
and ExactBundleInventory
and ExactArtifactDigests
and StaticTreeBindings
and NativeVerifierAcceptsSevenReceiptTree
and NativeVerifierRejectsExactSealMutation
-> ScopedPublicArtifactReplayAccepted
```

The checker always reports `production_claim_allowed=false`. This bundle has
no settlement, ledger-admission, release, or production authority.

## Published Files

The governed bundle is
[`evidence/zrpf-v3-structural-public-replay-v1`](../../evidence/zrpf-v3-structural-public-replay-v1/manifest.json).
Its external reference is
[`config/proof_profiles/zrpf_v3_public_replay_reference_v1.json`](../../config/proof_profiles/zrpf_v3_public_replay_reference_v1.json).

The 21 governed artifacts are:

| Role | Count | Replay authority | Purpose |
| --- | ---: | --- | --- |
| verifier binary | 1 | yes | Linux x86-64 verifier used by `--execute` |
| receipt | 8 | yes | four adapter leaves, two level-one nodes, one root, and one mutated root |
| positive transcript | 1 | yes | exact expected output for the accepted tree |
| mutation transcript | 1 | yes | exact expected typed rejection for the changed seal |
| source proof context | 4 | no | original Spot V1 proof artifacts retained for inspection |
| guest ELF context | 3 | no | adapter, level-one, and level-two guest programs retained for inspection |
| frozen source-closure context | 2 | no | proof-generation and verifier-build source records |
| toolchain-lock context | 1 | no | recorded RISC0 toolchain identity |

The manifest assigns `replay_authority=true` only to the verifier, receipts,
and expected transcripts. The other ten files are context records. The public
checker hashes and inventories them, while it does not use them to rebuild
guests, regenerate proofs, recompute image IDs, or establish provenance.

The compiled verifier and guest artifacts retain absolute compiler paths,
including an upstream build path inside RISC0's pinned `v1compat.elf`.
Source-path remapping is incomplete. These strings are build provenance inside
the proved or verifying artifact bytes; rewriting them would change the
cryptographic program or verifier identity. The manifest records publisher
review for private names and also records that the public checker does not scan
artifact bytes for private names. These facts prevent the bundle from serving
as a source-remapped release artifact.

## Anchors And Identities

The external reference pins the canonical manifest, verifier binary,
proof-generation source closure, and verifier-build source closure. The
manifest pins every artifact and the tree's three method image IDs, root
receipt, root journal, and exact mutated receipt.

| Fact | SHA-256 or identity |
| --- | --- |
| reference file SHA-256 | `521fb021c75c5ad7d4826cbfc35ff1301040abe46c1926624f7f57e5cc88af21` |
| manifest SHA-256 | `c4d9c0652cdf0b03ede5437f136583a808704c187800e4cd7dec52b625379bae` |
| native verifier SHA-256 | `c196c56e8e61cc757142e8199aeb6f27a31c071f7fe20c0e54825b527d63c1bc` |
| native verifier size | `3,850,880` bytes |
| proof-generation source closure | `929d645f2275a918f731e08649445703c51cc102663578df40f068f0e6e1281b` |
| verifier-build source closure | `35a8095eb9f2388864c48f463545ebd801747b52c7b4f53df250bef9349df985` |
| verifier closure file SHA-256 | `62802663b9bf982293e362523b9b164b430f29832b59900dc76b2a3480241c81` |
| adapter image ID | `71f282b5517fc6108988c1cc9b4601807a40ae331c0e0f0f5505d12b241e5574` |
| level-one image ID | `4272be5165f65e29cb134f815d6c6fc40d7f492979f596082cac10c3f0d43c2b` |
| level-two image ID | `3b858d113cb155b2946e1c733fdf5fe5592b6bf46c903d0a3cfb322099845736` |
| root receipt SHA-256 | `edd25fca20b0205c2f778b866605b343922615623256abcc1a098957664c2d16` |
| root journal SHA-256 | `da94385eb3d1f6cfd9ca8b440371e34ebf59882f0b13dc2d748c01bb76f81290` |
| root journal protocol hash | `2089ecc187077d4b719c8539076651753c1ead1415724c9bc788758bddfa3768` |
| mutated root receipt SHA-256 | `27c71152044124762efd5398fa6206a9627a5eae2ed9db851b1bb33783c6e985` |
| positive transcript SHA-256 | `fdebd421bec1ed222967daee972b00dff5f9e69f941c2522689f356787838807` |
| mutation transcript SHA-256 | `9e37c7456320c35ffddded50e50b1a8b06c3fc77f60d9bf7f10834f8590155e4` |

The root represents four authenticated source transition receipts in seven
tree nodes. Its structural facts are:

```text
node_level               = 2
immediate_child_count    = 2
leaf_count               = 4
operation_count          = 4 source_transition_receipts
subtree_node_count       = 7
partition                = [0, 4)
receipt_bytes            = 593320
```

`operation_count=4` counts source transition receipts. It carries no claim of
four end-user transactions.

## Bundle Construction Controls

The maintainer builder accepts explicit proof and verifier source closures,
proof and verifier target roots, a reviewed verifier binary, frozen evidence,
and the four source proof artifacts. It permits only the governed repository
bundle and reference paths. Both outputs must be absent before construction.

Every file is read as a bounded, non-symlink regular file. The builder uses a
fixed artifact inventory, requires the reviewed verifier digest, creates each
output with exclusive create-new semantics, flushes file and directory state,
and generates both transcripts by executing the staged verifier. It writes the
canonical manifest only after the positive replay and mutation control pass.

The checker applies these size limits:

| Input class | Maximum |
| --- | ---: |
| canonical JSON envelope | 16 MiB |
| individual bundle artifact | 32 MiB |
| native stdout or stderr transcript | 128 KiB |

Stable-file reads bind the opened inode, bytes, and mode. After validating the
source reference, manifest, inventory, and artifact policy, the checker copies
each exact hash-validated artifact into a private temporary snapshot with the
governed mode. All remaining static checks and optional native execution use
that snapshot. A final pass rechecks every staged size, digest, type, mode, and
inventory entry before acceptance.

## Trust Model

### Reviewed checker and reference

The trust anchor begins with reviewed repository source. The checker pins the
exact reference-file SHA-256 and verifier SHA-256 in
[`src/integration/zrpf_public_replay_bundle.py`](../../src/integration/zrpf_public_replay_bundle.py).
The reference separately pins the manifest, verifier, proof-generation source
closure, and verifier-build source closure.

Changing an artifact, manifest, reference, or verifier causes rejection unless
the corresponding reviewed source anchor is also changed. A repository commit
that changes the checker and every anchor defines a new review event.

### Static mode

Static mode performs no native execution. It fails closed on:

- a reference file that differs from the checker-pinned digest;
- a manifest that differs from the reference-pinned digest;
- duplicate or unknown JSON fields, noncanonical JSON, invalid versions, or
  unsupported claim values;
- a missing, extra, duplicated, unsorted, symlinked, oversized, or incorrectly
  executable artifact;
- any artifact size or SHA-256 mismatch;
- a verifier that differs from the checker-pinned digest;
- malformed or externally inconsistent frozen source closures;
- transcript facts that differ from receipt hashes, root facts, image IDs, or
  the manifest;
- a mutation that changes seal length, changes any word other than index 1,
  uses a mask other than XOR 1, or changes any byte outside that seal word;
- inventory changes observed during checking.

Static acceptance establishes integrity and internal consistency for this
published evidence envelope. Its report has `execution_checked=false`,
`scoped_public_replay_claim_allowed=false`, and
`status=static_bundle_accepted`. It does not cryptographically verify the RISC0
seals or authorize the scoped replay claim.

### Native replay mode

`--execute` repeats every static check, copies the already hash-validated
verifier and receipt files into a mode-restricted temporary directory, and
runs the verifier with a minimal deterministic environment. Each process has a
120-second timeout, zero-byte core-dump limit, and 128 KiB file-size limit.
Stdout and stderr are written to temporary files and must also remain below the
128 KiB post-run acceptance cap. Live output must match the published canonical
transcript byte for byte.

The positive run verifies:

```text
four adapter receipts
  -> exact left and right level-one journals
  -> two level-one receipts
  -> exact level-two root journal
  -> one level-two root receipt
```

At startup, the native verifier recomputes all three image IDs from its embedded
guest ELFs and compares them with the compiled IDs. Every receipt then crosses
`VerifiedNodeReceiptV3`, which verifies the governed image, pinned
receipt-security profile, cryptographic seal, strict journal, program identity,
claim binding, and projected child descriptor. Aggregate journals are
independently re-derived from their already verified children and compared byte
for byte.

The negative run first verifies the complete baseline tree. It then verifies
that the candidate root differs only at Succinct seal word 1, where the low bit
changes from 0 to 1. Restoring that word must restore the exact original
receipt bytes. The candidate must fail at the receipt-verification boundary
with stable reject code `receipt_verification_failed`.
The recorded boundary is
`VerifiedNodeReceiptV3::verify_exact_succinct_bytes`.

Successful native replay reports `execution_checked=true`,
`scoped_public_replay_claim_allowed=true`, and
`status=executed_replay_accepted`. Production authority remains false.

### Native execution warning

`--execute` runs a precompiled, dynamically linked GNU/Linux x86-64 executable
as the current user. Digest validation establishes its published identity. It
does not provide process sandboxing, operating-system attestation, or an
authenticated runtime root filesystem.

Review the pinned verifier hash before opting in. Run native replay with least
privilege inside a disposable VM or container when the host security policy
requires isolation. Static mode remains available on hosts where native
execution is inappropriate or unsupported.

## Receipt Profile And Persisted Envelope

The sealed host type `VerifiedNodeReceiptV3` is the only authority-bearing
representation of a verified V3 receipt and journal. Its fields are private.
The public construction boundary accepts persisted receipt bytes and requires:

1. a nonzero expected image ID;
2. a nonempty receipt no larger than 16 MiB;
3. exact typed JSON round-trip equality, which rejects alternate whitespace,
   duplicate fields, unknown fields, and other noncanonical encodings;
4. the compiled receipt-security profile
   `risc0_succinct_poseidon2_resolve_3_0_5_v1`;
5. RISC0 Succinct receipt kind;
6. verifier-parameter digest
   `ece5e9b8ae2cd6ea6b1827b464ff0348f9a7f4decd269c0087fdfd75098da013`;
7. metadata and inner verifier-parameter equality;
8. `poseidon2` as the exact hash suite;
9. `resolve.zkr` control ID
   `53a7b23d07f99e5d5685e85874f5181e8486aa267a0ae607ffe9ba47c8bdda4a`;
10. verification in an explicit context containing only the governed
    Poseidon2 suite and default Succinct verifier parameters;
11. cryptographic receipt verification under the expected image;
12. strict exact decoding of `NodeJournalV3`;
13. journal `actual_program_id` equality with the verified image;
14. locally derived claim binding and canonical child projection;
15. exact expected-journal bytes when the caller supplies an expected parent.

The verifier is compiled with RISC0 dev mode disabled. Its explicit verifier
context does not consult `RISC0_DEV_MODE`. Stable machine-readable error codes
cover envelope, profile, receipt, journal, program, claim-binding, and child-
projection failures.

The byte boundary applies equally to loaded evidence and newly generated
receipts. A fresh prover receipt is canonically encoded, bounded, decoded, and
verified through the same path before it can become a `VerifiedNodeReceiptV3`.

## Two Frozen Source Closures

The bundle carries two source snapshots because proof generation and final
public replay verification occurred at distinct reviewed commits.

### Proof-generation closure

`source/proof-generation-source-closure.json` records 37 exact source and
build files at commit
`dc99a7f96c816ff7f86b0f184d25817bea338166`. Its closure root is
`929d645f2275a918f731e08649445703c51cc102663578df40f068f0e6e1281b`.
This snapshot covers the guest programs, adapter and aggregate mappings,
protocol dependencies, proof harness, and verifier sources used for the frozen
proof run.

### Verifier-build closure

`source/verifier-build-source-closure.json` records the same governed set of 37
paths at commit `f948f57f17f0995e7f145aaf9a11ddb48b80fb22`. Its closure root is
`35a8095eb9f2388864c48f463545ebd801747b52c7b4f53df250bef9349df985`.
The closure file itself has SHA-256
`62802663b9bf982293e362523b9b164b430f29832b59900dc76b2a3480241c81`.
This snapshot records the later host verifier build that added the final
receipt-profile, byte-only persisted-envelope, and replay-control hardening.

Each closure hashes sorted records containing role, repository-relative path,
file SHA-256, and byte size. The snapshots record a clean worktree and reject
unlisted Rust files or in-scope `target` directories when originally created.

Both closures have `publisher_record_only` authority in the public manifest.
The public checker validates their canonical structure, internal closure root,
file count, and reference binding. It does not compare them with a current
checkout, rebuild either binary set, or independently prove the recorded Git
commit and build history. These limits keep
`proof_generation_provenance_machine_verified=false` and
`verifier_build_provenance_machine_verified=false`.

## Usage

Run all commands from the repository root.

### Static validation

```bash
python3 tools/check_zrpf_v3_public_replay_bundle.py
```

Expected report:

```json
{"checked_artifacts":21,"errors":[],"execution_checked":false,"ok":true,"production_claim_allowed":false,"schema":"zenodex/zrpf_v3_public_replay_check/v1","scoped_public_replay_claim_allowed":false,"status":"static_bundle_accepted"}
```

### Static validation plus native replay

```bash
python3 tools/check_zrpf_v3_public_replay_bundle.py --execute
```

Expected report:

```json
{"checked_artifacts":21,"errors":[],"execution_checked":true,"ok":true,"production_claim_allowed":false,"schema":"zenodex/zrpf_v3_public_replay_check/v1","scoped_public_replay_claim_allowed":true,"status":"executed_replay_accepted"}
```

Custom paths are available for an exact copy of the governed bundle and
reference:

```bash
python3 tools/check_zrpf_v3_public_replay_bundle.py \
  --bundle <BUNDLE_DIRECTORY> \
  --reference <REFERENCE_JSON>
```

The checker still requires the exact reviewed reference digest, manifest
digest, inventory, and artifact hashes.

## Exact Claims

The manifest declares exactly three scoped claims as `true`:

- `four_leaf_two_level_structural_tree`;
- `public_artifact_replay`;
- `typed_succinct_seal_mutation_rejection`.

These are pinned policy declarations. Static validation checks their exact
shape and bundle bindings without accepting them as replay evidence. Native
`--execute` acceptance establishes that the published verifier accepts the
exact seven-receipt tree and rejects the exact one-bit seal mutation under the
scoped replay contract.

## Exact Non-Claims

The manifest sets these claims to `false`:

- `fresh_proof_artifacts_from_source_frozen_run`;
- `proof_generation_provenance_machine_verified`;
- `verifier_build_provenance_machine_verified`;
- `guest_elf_image_ids_recomputed_by_public_checker`;
- `source_proofs_bound_to_leaf_journals_by_public_checker`;
- `toolchain_lock_semantically_validated_by_public_checker`;
- `reproducible_build`;
- `cross_host_reproducibility`;
- `release_backed`;
- `full_zenodex_semantic_composition`;
- `data_availability_or_carry_semantics`;
- `asset_conservation_or_value_flow`;
- `ledger_or_settlement_admission_authority`;
- `production_authority`;
- `zero_knowledge_or_witness_privacy`.

The manifest also records explicit non-claims for reproducible builds,
cross-host reproducibility, authenticated runtime filesystems, release
authority, complete ZenoDEX semantics, data availability, carry continuity,
asset conservation, ZenoLedger or settlement admission, production authority,
witness privacy, and receipt-byte determinism.

RISC0 receipt bytes can differ across proving runs while the authenticated
journal remains identical. The three image IDs remain temporary,
compiler-visible identities until a governed release process establishes
release authority.

## Next Assurance Steps

The native `--execute` lane closes the public-artifact replay gap for this
bounded structural tree. Static bundle acceptance alone does not close that
gap. Production promotion still requires:

1. reproducible or independently corroborated builds with governed release
   manifests;
2. cross-host replay and build evidence;
3. native V3 semantic leaves and complete ZenoDEX value-flow composition;
4. verified data availability, carry continuity, and conflict scheduling;
5. durable exact-once ZenoLedger admission and atomic state persistence;
6. release-key governance, revocation, and production admission policy;
7. measured proving, verification, data-availability, and end-to-end capacity
   evidence.
