# ZRPF RISC0 Structural Proof Profile

This workspace is the RISC0 compatibility and structural-recursion profile for
the Zeno Recursive Proof Fabric (ZRPF) used by ZenoDEX.

The implemented path authenticates four existing Spot V1 transition receipts,
adapts each receipt to the common `NodeJournalV3` format, joins the four leaves
into two level-one structural receipts, and joins those receipts into one
level-two structural root:

```text
four governed Spot V1 Succinct receipts
                 |
                 v
four V1 adapter Succinct receipts       NodeJournalV3, level 0
           |                 |
           v                 v
two structural L1 Succinct receipts     NodeJournalV3, level 1
                 |
                 v
one structural L2 Succinct receipt      NodeJournalV3, level 2
```

Each aggregate guest verifies its exact child receipts inside the zkVM before
it decodes child journals or derives the parent. The same `NodeJournalV3` type
therefore crosses both recursive levels.

This profile proves receipt authentication, exact journal binding, bounded tree
structure, deterministic structural root composition, and the execution of the
adapter and aggregate guests. Application semantics remain outside the current
aggregate relation. The parent commitment fields are field-specific roots over
authenticated child commitments. They do not establish ZenoDEX conservation,
data availability, carry continuity, conflict freedom, or settlement validity.

## Implemented Features

### Spot V1 compatibility leaves

The adapter path:

- accepts only the compile-time governed Spot V1 image, proof profile, and lane;
- strictly checks the canonical source proof artifact and its Succinct receipt;
- verifies the exact source receipt again inside the adapter guest;
- maps the authenticated V1 journal into a canonical `NodeJournalV3` leaf;
- derives source provenance, task identity, scope, partition, count unit,
  commitments, compatibility manifest, and node statement locally;
- labels `operation_count` as one `source_transition_receipt`, because V1 does
  not disclose the underlying transaction count;
- emits distinct nonzero unsupported sentinels for DA-certificate and carry
  fields that V1 cannot establish.

### Sealed receipt boundary

`VerifiedNodeReceiptV3` has private fields and enforces this order:

```text
require the compiled RISC0 3.0.5 Succinct receipt-security profile
  -> require metadata and inner verifier-parameter equality
  -> verify under an explicit Poseidon2-only, dev-mode-disabled context
  -> verify the receipt under the expected image
  -> strict-decode exact canonical NodeJournalV3 bytes
  -> require journal actual_program_id == verified image
  -> derive the claim binding locally
  -> expose a projected child descriptor
```

The compiled receipt-security profile is
`risc0_succinct_poseidon2_3_0_5_v1`. It pins the verifier-parameter digest,
`poseidon2` hash suite, and control ID independently of the node computation
profile. Unknown or mutated receipt-security fields reject before a verified
node is returned. The explicit verifier context does not consult
`RISC0_DEV_MODE`.

This prevents a caller-selected claim hash or self-reported program label from
becoming proof authority.

### Bounded structural aggregates

The structural aggregate input codec is manually framed, exact, and bounded.
It accepts `1..=8` child journals, caps each child journal at 4,096 bytes,
rejects trailing data, and bounds total input allocation before decoding.

Two compile-time policies are implemented:

- level one accepts only adapter children under the pinned adapter image,
  profile, compatibility manifest, and level zero;
- level two accepts only level-one children under the pinned level-one image,
  profile, structural manifest, and level one.

Both guests call `env::verify` for every exact child journal before structural
composition. The composer then enforces shared scope and count units, canonical
dense partitions, unique immediate task/claim/journal identities, checked
counts, and the protocol bounds. It derives the parent task, statement,
manifest, all 23 parent commitment roots, and all child-set roots.

Each aggregate input carries its expected self image because a guest cannot
derive its own image ID without a circular build. That field becomes trusted
only when the next recursive level or `VerifiedNodeReceiptV3` verifies the
receipt under the governed aggregate image and requires the journal program ID
to match. A standalone structural receipt must cross that sealed outer boundary
before it can be used as an authenticated node.

### Tree harness and negative controls

The adapter harness proves or replays compatibility leaves and exercises:

- missing source assumption rejection;
- exact source-journal substitution rejection;
- proof-bearing false adapter self-label rejection.

`prove_structural_tree`:

- loads exactly four canonical adapter receipt files;
- sealed-verifies every adapter receipt;
- independently derives each expected parent journal on the host;
- proves two level-one nodes and one level-two root with Succinct receipts;
- exact-verifies every generated aggregate receipt;
- persists each receipt with create-new semantics and an `fsync` boundary;
- exercises a missing level-one child-assumption rejection mode.

`verify_structural_tree` performs the same sealed checks and host-side expected-
journal derivation over seven persisted receipts without generating new proofs.
Swapping the two level-one receipt files changes the expected child grouping
and rejects at exact-journal equality.

Pure tests also reject wrong child program, manifest, profile, level,
duplicates, partition gaps, oversized inputs, and noncanonical codecs.

## Compiled Bounds And Current Evidence

The common protocol supports at most fanout 8 and level 2, which gives a
structural capacity of 64 leaves and 73 total nodes. The current proof evidence
uses fanout 2 at both levels:

```text
leaf_count             = 4
operation_count        = 4 source_transition_receipts
subtree_node_count     = 7
root partition         = [0, 4)
```

The operation count does not represent four transactions.

The currently evidenced temporary-path method identities are:

| Method | Image ID |
| --- | --- |
| V1 Spot adapter | `71f282b5517fc6108988c1cc9b4601807a40ae331c0e0f0f5505d12b241e5574` |
| structural aggregate L1 | `4272be5165f65e29cb134f815d6c6fc40d7f492979f596082cac10c3f0d43c2b` |
| structural aggregate L2 | `3b858d113cb155b2946e1c733fdf5fe5592b6bf46c903d0a3cfb322099845736` |

One local proof instance produced:

| Fact | Value |
| --- | --- |
| root journal hash | `2089ecc187077d4b719c8539076651753c1ead1415724c9bc788758bddfa3768` |
| exact root receipt SHA-256 | `021af13025e7dc7c40e06d689ad30e3194e58793435cd11ae07d684c80ddfd33` |

Receipt serialization can differ across proving runs even when the
authenticated journal is identical. These compiler-visible image identities
have temporary local-evidence scope and no release authority.

## Workspace Layout

- `shared`: guest-safe Spot policy, strict adapter codec, source provenance,
  and deterministic V1-to-V3 projection;
- `aggregate_shared`: guest-safe structural policies, strict aggregate codec,
  and deterministic parent composition;
- `methods/v1_leaf_adapter`: receipt-authenticated compatibility guest;
- `methods/structural_aggregate_l1`: adapter-to-level-one guest;
- `methods/structural_aggregate_l2`: level-one-to-level-two guest;
- `methods`: generated ELF and image-ID constants;
- `verifier`: sealed host receipt-verification boundary;
- `harness`: adapter proof, controls, structural-tree proving, and verifier-only
  persisted-tree replay binaries.

## Verify The Source And Pure Logic

Select the pinned RISC0 Rust toolchain explicitly:

```bash
PINNED_BIN="$HOME/.risc0/toolchains/v1.94.1-rust-x86_64-unknown-linux-gnu/bin"
export PATH="$PINNED_BIN:$PATH"
export RUSTC="$PINNED_BIN/rustc"
export RUSTDOC="$PINNED_BIN/rustdoc_tool_binary"
```

From this workspace:

```bash
cargo fmt --all -- --check
RISC0_SKIP_BUILD=1 cargo test --locked \
  -p zenodex-zrpf-risc0-shared \
  -p zenodex-zrpf-risc0-aggregate-shared \
  -p zenodex-zrpf-risc0-verifier \
  -p zenodex-zrpf-risc0-harness
RISC0_SKIP_BUILD=1 cargo clippy --locked --workspace --all-targets -- -D warnings
```

The guest packages must not run as host test binaries. The package-scoped test
command avoids host execution of zkVM syscalls.

From the repository root, check the independent protocol and adapter vectors:

```bash
python3 tools/check_zrpf_v1_leaf_adapter_source_policy.py
python3 tools/check_zrpf_v1_leaf_adapter_vector.py
python3 tools/check_zrpf_v3_hash_vector.py
python3 tools/check_recursive_stark_cbc_spec.py --pretty
```

## Build And Prove A Four-Leaf Tree

Use an external target directory so build outputs do not enter the source
closure:

```bash
export CARGO_TARGET_DIR="<ABSOLUTE_EXTERNAL_TARGET>"
unset RISC0_SKIP_BUILD
cargo build --locked --release -p zenodex-zrpf-risc0-harness --bins

HARNESS="$CARGO_TARGET_DIR/release/zenodex-zrpf-risc0-harness"
TREE="$CARGO_TARGET_DIR/release/prove_structural_tree"
VERIFY_TREE="$CARGO_TARGET_DIR/release/verify_structural_tree"
EVIDENCE_DIR="<EVIDENCE_DIRECTORY>"
mkdir -p "$EVIDENCE_DIR/leaves"
```

Supply four distinct canonical Spot V1 proof artifacts with equal ZRPF scope.
Assign dense leaf ordinals:

```bash
"$HARNESS" <SPOT_PROOF_0_JSON> --ordinal 0 \
  --receipt-out "$EVIDENCE_DIR/leaves/leaf0.receipt.json"
"$HARNESS" <SPOT_PROOF_1_JSON> --ordinal 1 \
  --receipt-out "$EVIDENCE_DIR/leaves/leaf1.receipt.json"
"$HARNESS" <SPOT_PROOF_2_JSON> --ordinal 2 \
  --receipt-out "$EVIDENCE_DIR/leaves/leaf2.receipt.json"
"$HARNESS" <SPOT_PROOF_3_JSON> --ordinal 3 \
  --receipt-out "$EVIDENCE_DIR/leaves/leaf3.receipt.json"
```

Replay a persisted leaf through the sealed verifier:

```bash
"$HARNESS" <SPOT_PROOF_0_JSON> --ordinal 0 \
  --verify-receipt "$EVIDENCE_DIR/leaves/leaf0.receipt.json"
```

Prove the two-level tree. The output directory must not already contain the
three aggregate receipt names:

```bash
"$TREE" \
  "$EVIDENCE_DIR/leaves/leaf0.receipt.json" \
  "$EVIDENCE_DIR/leaves/leaf1.receipt.json" \
  "$EVIDENCE_DIR/leaves/leaf2.receipt.json" \
  "$EVIDENCE_DIR/leaves/leaf3.receipt.json" \
  "$EVIDENCE_DIR/tree"
```

The tree command creates:

```text
tree/structural-l1-left.receipt.json
tree/structural-l1-right.receipt.json
tree/structural-l2-root.receipt.json
```

Its canonical JSON output reports every leaf and node journal hash, receipt
hash, receipt size, partition, level, leaf count, operation count, and subtree
node count.

Replay all seven persisted receipts without proving again:

```bash
"$VERIFY_TREE" \
  "$EVIDENCE_DIR/leaves/leaf0.receipt.json" \
  "$EVIDENCE_DIR/leaves/leaf1.receipt.json" \
  "$EVIDENCE_DIR/leaves/leaf2.receipt.json" \
  "$EVIDENCE_DIR/leaves/leaf3.receipt.json" \
  "$EVIDENCE_DIR/tree/structural-l1-left.receipt.json" \
  "$EVIDENCE_DIR/tree/structural-l1-right.receipt.json" \
  "$EVIDENCE_DIR/tree/structural-l2-root.receipt.json"
```

This command verifies each receipt cryptographically, reconstructs the exact
left and right level-one journals from the four leaves, reconstructs the exact
level-two journal from those two nodes, and rejects any mismatch. Passing the
two level-one receipt paths in reverse order is a deterministic negative check.

## Run The Binding Controls

Adapter controls:

```bash
"$HARNESS" <SPOT_PROOF_0_JSON> --missing-assumption
"$HARNESS" <SPOT_PROOF_0_JSON> --substituted-source-journal
"$HARNESS" <SPOT_PROOF_0_JSON> --ordinal 0 --mislabeled-adapter
```

Structural missing-assumption control:

```bash
"$TREE" \
  "$EVIDENCE_DIR/leaves/leaf0.receipt.json" \
  "$EVIDENCE_DIR/leaves/leaf1.receipt.json" \
  "$EVIDENCE_DIR/leaves/leaf2.receipt.json" \
  "$EVIDENCE_DIR/leaves/leaf3.receipt.json" \
  "$EVIDENCE_DIR/unused-negative-output" \
  --missing-assumption
```

Each successful negative control prints a specific rejection status. Internal
RISC0 assumption error text is diagnostic evidence rather than a stable public
reject ABI.

## Check The Evidence Records

From the repository root, validate the reviewed manifests and their current
relative source closures:

```bash
python3 tools/check_zrpf_v1_spot_adapter_temporary_evidence.py
python3 tools/check_zrpf_v3_structural_tree_temporary_evidence.py
python3 tools/zrpf_evidence_boundary_concolic.py --format text
```

The adapter checker can additionally hash one saved adapter receipt, its source
proof artifact, and the adapter ELF through `--adapter-receipt`,
`--source-proof`, and `--elf`. The tree checker accepts `--artifact-root` for
the seven saved receipts and four path-redacted replay/control transcripts.
These Python tools validate schema, reviewed facts, paths, hashes, and sizes.
They do not verify RISC0 seals; the Rust harnesses own that boundary.
The boundary-atlas command performs deterministic, depth-two malformed-manifest
exploration and deduplicates reject paths. It is an offline bug-discovery
sidecar, with no correctness-proof or receipt authority.

## Authority And Non-Claims

The following work remains outside the current authority boundary:

- native V3 semantic leaves and parent semantic composition;
- transaction-count claims for compatibility leaves;
- nonempty receipt-set and cross-lane-message disclosures;
- descendant-wide uniqueness and complete conflict schedules;
- asset-delta-row conservation and complete ZenoDEX value-flow coverage;
- verified data availability and DA-certificate policy;
- carry-queue continuity;
- durable exact-once ZenoLedger admission and atomic value-state persistence;
- governed release manifests, public replay, and cross-host reproducibility;
- witness or system privacy;
- settlement and production authority;
- throughput, latency, and proving-cost claims.

The protocol specification is
`docs/research/ZRPF_V3_CORRECT_BY_CONSTRUCTION_SPEC_20260710.md`. The exact V1
field mapping is
`docs/research/ZRPF_V1_LEAF_ADAPTER_COMPATIBILITY_SPEC_20260710.md`.
