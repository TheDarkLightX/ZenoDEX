# ZRPF V4 Spot Value-Leaf Evidence

Status: source-anchored retained-receipt replay for one bounded V4 residual
Spot leaf; no ledger, settlement, release, privacy, or production authority

Date: 2026-07-12

## Purpose

This evidence lane connects the historical backend-bound V4 value-node
protocol to one real RISC0 Succinct receipt. It establishes an executable
reference for the smallest V4 node before recursive V4 aggregation is
introduced.

The represented source transition is intentionally narrow. It is ordinal zero
from the retained Spot evidence, contains zero asset rows, and leaves the raw
application state unchanged. This isolates receipt authentication, semantic
projection, journal construction, and replay from later closed-epoch economic
semantics.

V4 is a historical compatibility lane. Its guest input carries a host-declared
self image, and only the exact sealed V4 verifier compares that declaration
with the image used for cryptographic receipt verification. Ordinary receipt
verification followed by journal decoding does not authenticate the claimed
runtime identity. The retained bytes remain frozen; active authority work uses
a proof-neutral successor ABI.

## What the proof does

```text
retained Spot source proof
  -> retained V1 adapter receipt
  -> V4 guest verifies the exact adapter receipt and image
  -> guest derives the bounded SemanticSubtreeV2
  -> guest constructs the exact NodeJournalV4 residual leaf
  -> RISC0 emits one Succinct V4 receipt
  -> host verifies receipt, image, profile, journal, and residual statement
  -> ExactSpotValueLeafReceiptV4
```

The host cannot create `ExactSpotValueLeafReceiptV4` from decoded journal data,
metadata, or a caller-provided Boolean. Construction begins with bounded receipt
bytes and crosses the cryptographic verifier before the journal gains
authenticated status.

## New assurance features

### Exact retained artifact set

The evidence directory contains exactly two declared receipt artifacts:

| Artifact | Size | SHA-256 |
| --- | ---: | --- |
| accepted V4 Succinct receipt | 601,394 bytes | `794a69746b3f833f56e15c968c16ab7d4ee9089f555eb210d38a1c0ea37d18c7` |
| seal-word-1 XOR-1 candidate | 601,394 bytes | `2772e497dc94d937e5840bae87f2e606122269ffc8cb2a1d38667216747d2530` |

The static checker rejects extra files, missing files, symlinks, special files,
hash drift, size drift, and noncanonical receipt JSON.

### Exact mutation relation

The negative artifact differs from the accepted receipt in exactly one
Succinct seal word:

```text
seal word count = 55,667
changed index   = 1
XOR mask        = 1
journal bytes   = unchanged
all other JSON  = unchanged
```

This relation is checked independently of the two artifact hashes. The live
Rust verifier then rejects the candidate at cryptographic receipt verification.

### Split source anchors

The manifest records two distinct source identities:

| Role | Commit | Tree |
| --- | --- | --- |
| proof generation | `247f40da13563990d3f9f687f706228c9283562f` | `68792f420a54d96290add01c2c94e1b25032ae9c` |
| current native replay verifier | `074e4a4327b4387606955a1ece868889ba50e502` | `34684c47769ec69681ba13590ce76ba61fe48f70` |

The proof-generation anchor is the publisher-reported commit where the
retained receipt was created. The live checker builds and executes the later
hardened verifier. Neither anchor establishes complete build-input closure or
historical execution provenance.

### Strict static manifest

The governed manifest is:

```text
docs/research/ZRPF_V4_SPOT_VALUE_LEAF_LOCAL_EVIDENCE_20260712.json
SHA-256 284e6eafdf83c2f1c0d930c8b27780dc5c297060c8cae8bdf6aaa991535ae62b
```

The checker requires exact field sets, exact Python value types, canonical JSON
bytes, the pinned manifest hash, both Git tree identities, the pinned toolchain
lock, the exact artifact inventory, and all supporting-input identities.
Boolean/integer substitution, unknown fields, claim promotion, path escape,
and coherent field drift reject.

Static success reports these execution facts as false:

```text
execution_checked
positive_receipt_cryptographically_verified
mutation_receipt_cryptographically_rejected
scoped_native_replay_claim_allowed
```

### Source-built live replay

Live mode performs the following additional sequence:

```text
static manifest acceptance
  -> private detached source snapshot at the verifier commit
  -> pinned Cargo, rustc, and rustdoc identity checks
  -> frozen offline release build with four jobs
  -> unchanged source-snapshot check
  -> create-new staged replay inputs with fsync
  -> verifier copied into a fully sealed Linux memfd
  -> bounded child-process execution
  -> exact canonical output validation
```

The live lane executes three controls:

1. The accepted receipt must produce the exact 2,750-byte positive report.
2. Any `RISC0_DEV_MODE=1` environment must produce the exact 287-byte typed
   process-start rejection before receipt parsing or verification.
3. The one-bit seal mutation must produce the exact 472-byte typed
   cryptographic rejection.

The canonical report identities are:

| Report | Size | SHA-256 |
| --- | ---: | --- |
| positive replay | 2,750 bytes | `3715cf4d0741be698d9e7b4ab32c544ed2bacf4e6e2a23e43c5525fedbfe3b86` |
| ambient dev-mode rejection | 287 bytes | `c2c5473d739693bce97c22efc94f643211c5726dcbaf4014bbad0c652467247f` |
| seal-mutation rejection | 472 bytes | `22e7aa5beffcd0d4e94aa15df8e458774048951ef7feee90e4feeba5cd866134` |

### Reproducibility observation

Three clean source paths produced different native verifier bytes even with
the configured path remapping:

```text
recorded comparison: 61c99170466c15de7a10c94dd2a54828aca9d63b1d989d0b47d2df62e9593796
                     3,248,296 bytes
earlier clean path:  6afd70fc68ec90621ac53823fed88682e95a1161e8be9a4d114b7492e5350d83
                     3,248,264 bytes
guarded final path:  6d8e07578402b1042fd0fb2d0c746f0c148b9d1b9e162afa6ff1cee16c2230bb
                     3,248,160 bytes
```

All three source-built verifiers produced the same exact positive and negative
contracts. The manifest records
`cross_path_reproducible_executable=false` and does not require the live binary
to match the recorded comparison identity. This is same-host, local
source-built retained-receipt replay. Same-UID race resistance and
path-independent executable reproducibility remain pending.

### Boundary mutation atlas

The offline depth-two atlas now includes V4 mutations for:

- unknown nested fields;
- settlement and production claim promotion;
- Boolean/integer substitution;
- proof and verifier source drift;
- verifier binary, receipt, and journal hash drift;
- seal-mutation index drift;
- supporting-path escape;
- positive and dev-mode report drift;
- disabling the ambient dev-mode rejection policy.

The atlas deduplicates exact `(outcome, path)` pairs. It is a bug-discovery and
regression tool. It does not verify RISC0 seals or prove checker correctness.

## How to use it

### Static validation

From the repository root:

```bash
python3 -I tools/check_zrpf_v4_spot_value_leaf_local_evidence.py --json
```

Expected result:

```text
mode = static
ok = true
execution_checked = false
scoped_native_replay_claim_allowed = false
```

### Native retained-receipt replay

Choose a private parent directory outside the repository. The target path must
not already exist.

```bash
python3 -I tools/check_zrpf_v4_spot_value_leaf_local_evidence.py \
  --live \
  --risc0-home "$HOME/.risc0" \
  --target-dir "$PRIVATE_PARENT/zrpf-v4-live-replay" \
  --json
```

The build uses four Cargo jobs and can take several minutes on a clean target.
It verifies retained receipts and does not regenerate proofs.

Expected live facts include:

```text
execution_checked = true
positive_receipt_cryptographically_verified = true
mutation_receipt_cryptographically_rejected = true
dev_mode_environment_rejected = true
source_built_retained_receipt_v4_value_leaf_replay_verified = true
```

### Boundary atlas

Run the V4 target alone:

```bash
python3 tools/zrpf_evidence_boundary_concolic.py \
  --target v4_spot_value_leaf_evidence \
  --format text
```

Run the complete evidence atlas through its regression suite:

```bash
python3 -m pytest -q tests/test_zrpf_evidence_boundary_concolic.py
```

## Exact V4 public identities

```text
V4 image ID
  dd58afedb9be399a3f9bbaa34229e5dc63c170873962e99307b52c5d25e7f743

guest ELF SHA-256
  195f1cd4bd4b6b4ddc4765d9ab33664834e64d58ee6c468dd0b254ea0012fa6e

application statement hash
  35ebda5b6748cec7be31b04ad065231628ae642fdf1d23108bc04d2ceda9e9a0

claim binding
  2fa0a2cf480701b2a377a8b15a98f1efbb5cad0156628dac921f2b457a90566c

canonical V4 journal hash
  d3b3b1616f9f90f80b3b67a904ce9b5561f238a4891746587b186ae840bd50c4

journal byte SHA-256
  4b177dccd6919caa03627d2440f38362700b9c3f4cc2267333d94e5fd597d7bc

value-subtree root
  839a52046406e3ee016bd339c07c9c1980a346f1f18b8035817a4dfebc8e06a4
```

## Claim boundary

This evidence establishes one current-image V4 residual leaf receipt and a
source-built verifier replay of its exact bytes. It does not establish:

- proof regeneration or proof-byte determinism;
- complete build-input closure or cross-path/cross-host reproducibility;
- same-UID race resistance for source, Cargo-cache, and target artifacts;
- source-to-guest-ELF provenance;
- nonempty asset-flow or issuance semantics;
- complete-root conservation or semantic finality;
- data availability, schedule, message, or carry verification;
- durable atomic ZenoLedger admission;
- sandbox, side-channel, or covert-channel resistance;
- release, settlement, privacy, throughput, or production authority.

## Next implementation target

The next protocol milestone is the V4 aggregate node:

```text
bounded child receipt bytes
  -> verify every exact V4 child receipt and expected image
  -> decode only authenticated child journals
  -> merge SemanticSubtreeV2 values canonically
  -> reject descendant duplicates and state discontinuities
  -> construct one exact parent NodeJournalV4
  -> prove and host-verify the parent receipt
```

The first aggregate evidence should include a nonempty ordinary-flow leaf, a
governed-issuance leaf, at least two distinct child receipts, cross-subtree
duplicate-source rejection, child omission/substitution controls, and a final
ledger-owned expected-statement comparison. Atomic admission remains a later
separate transition.
