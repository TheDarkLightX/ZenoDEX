# ZRPF Semantic Epoch V1 Specification

> Historical status (2026-07-12): V1 remains an immutable retained-receipt
> replay profile. Its guest accepted a host-declared semantic self-image and
> relied on the exact outer verifier to authenticate that declaration. New
> semantic proof work uses the V2 statement in
> `ZRPF_SEMANTIC_EPOCH_V2_CBC_SPEC_20260712.md`. V1 grants no V2, admission,
> release, settlement, or production authority.

Status: experimental bounded local semantic proof evidence
Date: 2026-07-11

## Purpose

ZRPF V3 structural aggregation authenticates an actual proof tree. Immediate
parents reject duplicate children, while an L2 parent cannot inspect semantic
identities hidden inside separate L1 subtrees. Semantic Epoch V1 defines the
smallest compatibility statement that can later flatten authenticated V1
adapter leaves and reject duplicate source claims, semantic sources, and tasks.

The protocol carries two roots:

```text
proof_tree_root
    proposed commitment to the concrete recursive proof topology

semantic_epoch_root
    deterministic commitment to one exact ordered semantic-leaf sequence
```

For an identical ordered `ProposedSemanticLeafV1` sequence and identical epoch
inputs, changing only `proof_tree_root` preserves `semantic_epoch_root` and
changes `proposal_hash`.

This V1 statement does not claim independence across different leaf proof
implementations, leaf numbering, or semantically equivalent leaf encodings.
Leaf program, profile, statement, manifest, partition, and complete commitment
identities are included in `leaf_records_root`.

## Historical scoped claim

The Rust protocol constructs and exactly encodes a bounded
`ProposedSemanticEpochV1`. The `semantic_shared` crate adds an exact raw guest
ABI, post-verification disclosure binding, complete L1 recomposition,
structural L2 recomposition, and semantic proposal construction. Input leaves
can be constructed only through the profile-specific
`ProposedSemanticLeafV1::bind_v1_adapter_journal` path. That path enforces:

- a caller-governed expected V1 adapter program ID;
- the exact V1 adapter profile, derived manifest, count unit, and one-operation
  leaf shape;
- singleton partitions;
- the semantic-source opening against both `provenance_root` and
  `semantic_source_set_root`;
- the journal task against `task_set_root`;
- the task and partition against `partition_plan_root`;
- exact V1 adapter node-statement recomposition;
- canonical empty accepted receipts, rejected receipts, outbox, inbox, and
  message-ID roots.

The epoch constructor enforces:

- 1 through 64 singleton leaf partitions with exact dense origin `[0, n)`;
- one exact scope, count unit, and adapter program across all leaves;
- globally unique source-claim IDs, semantic-source IDs, and task IDs;
- checked operation and leaf counts;
- canonical domain-separated SHA-256 roots;
- an exact bounded Postcard proposal codec.

`ProposedSemanticEpochV1` is self-consistent data. It has no constructor or
conversion into a verified receipt, ledger-admissible root, or settlement fact.
The separate sealed `VerifiedSemanticEpochReceiptV1` host type begins with
bounded canonical receipt bytes and verifies the pinned Succinct profile,
semantic guest image, exact proposal, governed A/B/C dependency manifest, and
claim binding before exposing an authenticated proposal.

The retained local evidence authenticates one three-leaf, two-L1-group instance
under the fresh A/B/C/D image ladder. It also executes one cross-subtree
duplicate-semantic-source control after both L1 assumptions are verified. The
guest rejects that control at the typed semantic-composition boundary. This is
a bounded compatibility-profile result and does not establish complete
ZenoDEX economic semantics.

## V1 adapter opening

The compatibility profile defines:

```text
source_claim_id
    = profile-checked NodeCommitmentsV3.input_root proposal

semantic_source_id
    = disclosed SourceBindingV3 canonical hash

task_id
    = profile-checked NodeJournalV3.task_id proposal
```

The semantic-source member cannot be recovered from its singleton roots. A
semantic guest receives the exact 32-byte member opening, then requires:

```text
singleton(provenance_domain, semantic_source_id)
    == commitments.provenance_root

singleton(semantic_source_domain, semantic_source_id)
    == commitments.semantic_source_set_root
```

The adapter statement is recomputed with that same member. A caller cannot
relabel an existing leaf with a different semantic-source value.

The source-claim value is profile-specific. Treating `input_root` as a source
claim is valid only after the exact V1 adapter program/profile boundary is
established. These proposed identities gain cryptographic authentication only
when the L1 receipt-verification and exact-recomposition chain executes inside
the semantic guest and the outer verifier accepts its receipt.

## Authority progression

The implemented authority-bearing guest preserves this order:

```text
bounded framing-only envelope
  -> verify pinned L1 receipt against exact L1 journal bytes
  -> exact NodeJournalV3 decode
  -> exact bounded leaf-opening decode
  -> independently recompose the complete expected L1 journal
  -> require byte equality with the authenticated L1 journal
  -> bind each exact V1 adapter journal and semantic-source opening
  -> flatten leaves and enforce global uniqueness
  -> derive ProposedSemanticEpochV1
  -> commit exact proposal bytes
```

An outer verifier must then authenticate the semantic guest receipt, image ID,
receipt-security profile, exact proposal bytes, expected program/manifest, and
claim binding before it may expose `VerifiedSemanticEpochReceiptV1`.

No opening may be interpreted as authenticated before its structural L1 receipt
and exact recomposition pass.

## Bounds

```text
maximum leaves                    64
maximum L1 groups                  8
maximum leaves per L1 group        8
operations per compatibility leaf 1
maximum operations in V1 proposal 64
maximum raw guest input bytes 297,147
maximum encoded proposal bytes 4,096
```

The underlying V3 protocol retains its broader 128 operations per leaf and
8,192 operations per structural root bounds. This semantic compatibility
profile deliberately narrows every leaf to one source-transition receipt.

## Canonical proposed leaf

`ProposedSemanticLeafV1` binds:

```text
partition
operation count and count unit
task ID
complete scope
profile-specific source claim ID
opened and root-checked semantic source ID
leaf program and proof profile IDs
leaf statement and program-manifest roots
complete NodeCommitmentsV3 hash
```

The leaf and proposal types have private fields and no generic `Deserialize`
implementation. The bounded exact proposal decoder parses a private wire type,
validates self-consistency, and rejects noncanonical or trailing bytes.
Canonical leaf order is `(partition.start, partition.end_exclusive, task_id)`.
The epoch input must use exact ordinals `[0, 1), [1, 2), ..., [n-1, n)`.

## Semantic commitments

The proposal commits to:

```text
leaf_records_root
pre_state_roots_root
post_state_roots_root
transaction_roots_root
effect_roots_root
asset_delta_roots_root
source_claim_ids_root
semantic_source_ids_root
task_ids_root
```

Accepted/rejected receipt IDs, messages, and nullifiers are absent from this
profile. Retained V1 adapter leaves authenticate only empty receipt and message
sets, and `NodeJournalV3` has no nullifier commitment. A future nonempty profile
requires per-leaf authenticated openings before adding those roots.

## Semantic epoch root

Let `C` be the canonical hash of `SemanticEpochCommitmentsV1`, and let `S` be
the canonical `NodeScopeV3` hash.

```text
semantic_epoch_root = H(
    "zenodex.zrpf.semantic_epoch_root.v1",
    semantic_version,
    semantic_profile_id,
    S,
    partition.start,
    partition.end_exclusive,
    leaf_count,
    operation_count,
    count_unit_id,
    C
)
```

`proof_tree_root`, the future semantic guest program ID, and its manifest root
are excluded from `semantic_epoch_root`. They are included in `proposal_hash`.
The guest manifest root is derived inside the protocol from the semantic guest
program ID, fixed semantic profile ID, pinned adapter/L1/L2 program IDs, and the
`unreleased_semantic_epoch_manifest` class. Dependency roles are named in a
typed input so swapping L1 and L2 identities changes the manifest. It is never
a free host-selected semantic field.

Historical fixed vectors:

```text
semantic profile ID
1f85ab429c2fd960e2ba02486b55a1055a735c11b9552e5672d9dee847016d29

two-leaf semantic epoch root
0955053e6305585103d60a7a6429d06a991cc7c1552ed52fd155f807f0d5dff7

two-leaf proposal hash
785e4d7882eaa2590f6c21b92209433e92a73fb3ed2074932cc6e55b02b95023
```

These test vectors use synthetic nonzero leaf fields. They are protocol vectors,
not proof receipts.

## Evidence in this tranche

### Fresh program identities

The staged canonical build and a separate final clean same-host rebuild agree
byte-for-byte on all four guest programs:

```text
A  V1 adapter
   d2c2f1a321c53e0228455b2cf22942fde7595030a379c3fd5484af446ac75d64

B  structural L1
   71e9af087cce2074f2272ea8dec3a16383651014effcf65eac18c48a2722e9a9

C  structural L2 recomposition policy
   a92e8ec445e2fea9f61928e0ddf1192552044018e0b49f24374bfa59a45085b3

D  semantic epoch
   dea9abab5cc382af0929779bf84bfcb5430f33b337b86f57e7712b303f3c3c51
```

The final 56-file repository source closure is:

```text
50e7ab1790de7d9505abc241e3780c15144c9266ba5c6ac348a587d06c867eaa
```

That closure binds the guest and proof-generation source at commit
`70bc574c`. The separately built persisted verifier is bound by a 57-file
source closure at commit `04e292d9`:

```text
8273e6df9f535ca0fe0cf5531de8e267482cd3e5c0160dec8f21793dc5f6a21d
```

This establishes a same-host canonical-path rebuild match. Complete build-input
closure, cross-host reproducibility, and path-independent reproducibility
remain false.

### Positive semantic receipt

The retained positive instance contains:

```text
group 0: adapter ordinals 0 and 1 under one B receipt
group 1: adapter ordinal 2 under one B receipt
leaf count:      3
operation count: 3
```

The D guest verifies both exact B assumptions before interpreting their
disclosed A journals. It recomposes both B journals, recomposes the structural
C journal locally, binds all three semantic openings, enforces global
source-claim, semantic-source, and task uniqueness, and commits:

```text
semantic receipt SHA-256
d2d726e1647bc7693908f7bf28e81970a34a50d4bc7ef1d7a4364ff486aa2caa

semantic epoch root
663ac6c9b21d060f98da255987942b9aff864085efa3f7457f1559e081f2150e

proof tree root
a1b15dae40499eb2d6b6dc9f2be973a29b4f95a7329cc896548118d2321b21dc

proposal hash
84b8ad570c614c3f29a3a1a2331ec3d54b8d13ca4930d7a07a008116a7dd7751

program manifest root
47f58f695381daea1cb279185ff8398674bbb1a485db92727792d08b92050a44
```

The persisted-receipt verifier separately reloads every retained A and B
receipt, reconstructs the exact expected proposal from governed program IDs and
typed openings, and verifies the D receipt against that proposal. Ambient
`RISC0_DEV_MODE` values `0`, `1`, and `true` produce the same canonical
verification report.

### Cryptographic mutation control

The persisted verifier clones the already verified D receipt, XORs Succinct
seal word 1 by exactly 1, writes the candidate with create-new semantics,
reopens the same file version, and proves that restoring the word yields the
exact original canonical receipt. The candidate SHA-256 is:

```text
47e6f2bb250dfaeeb06344f692b4a0f712c9e3fb5ed62d9237f4158da5a4db99
```

The exact verifier rejects it as:

```text
ReceiptArtifact(ReceiptVerificationFailed)
```

### Duplicate-source execution control

The negative instance reuses the semantic opening from ordinal 1 at ordinal 2
under a separate authenticated B subtree. The adapter and B receipts are
distinct. The exact host mirror returns `DuplicateSemanticSource`, and D guest
execution reaches the stable `duplicate_semantic_source` reject after both B
assumptions are supplied.

Failed guest execution produces no receipt. The dynamic-loader closure of the
local R0VM execution is also unverified. The negative report therefore keeps
`authoritative_negative_evidence=false` and
`cryptographic_reject_receipt_exists=false`.

### Verification boundary

The retained evidence uses RISC0 `3.0.5`, Succinct receipts, Poseidon2, the
governed resolver control ID, and exact verifier parameters. A Rust verifier
authenticates seals and proposals. The Python evidence checker authenticates
canonical bytes, complete inventory, hashes, topology, reports, source
closure, and claim policy; it explicitly records
`python_verifies_risc0_seals=false`.

The complete 27-file retained bundle passed the bounded public-artifact privacy
denylist with zero findings. This scan does not establish complete artifact
confidentiality or side-channel freedom.

### Protocol and source tests

The protocol and guest-safe kernel tests cover:

- an independent adapter-hash mirror and fixed legacy empty-root vectors;
- exact proposal encode/decode and fixed root vectors;
- proof-tree-root-only changes preserving the semantic root;
- duplicate source claim, semantic source, and task across distinct partitions;
- reordered, gapped, nonzero-origin, mixed-scope, and mixed-program leaves;
- semantic-source relabeling;
- wrong adapter program, profile, manifest, count unit, provenance, task set,
  semantic-source set, partition plan, auxiliary roots, operation count, and
  statement;
- 65-leaf rejection;
- every truncated encoded prefix and an oversized input;
- compile-fail generic-deserialization checks for leaves and proposals;
- semantic-root substitution rejection through the exact bounded decoder;
- real adapter projection parity through the semantic leaf binder;
- bounded depth-two byte-mutation exploration;
- exact 297,147-byte guest framing, every truncated prefix, maximum fanout,
  zero/oversized journals, stale schema, trailing bytes, and opaque openings;
- post-verification raw-opening binding and zero-opening rejection;
- exact L1 recomposition with missing, substituted, reordered, malformed,
  wrong-program, wrong-profile, gapped, and cross-subtree duplicate controls;
- structural L2 recomposition and cross-subtree scope rejection;
- equal semantic roots and distinct proof-tree roots under two valid groupings;
- semantic manifest binding to the semantic, adapter, L1, and L2 programs;
- sealed semantic receipt construction from bounded canonical Succinct bytes;
- fake-receipt rejection and compile-fail proposal-to-receipt conversion;
- source-contract checks for verify-before-interpret ordering and fail-closed
  placeholder methods.

Boundary mutation evidence is an offline bug-discovery layer. It is not a
correctness proof.

## Explicit non-claims

This tranche does not establish:

- complete build-input closure, cross-host reproducibility, or
  path-independent builds;
- reproducible semantic proof generation or receipt-byte determinism;
- an independent verifier implementation or public source-built replay;
- cryptographic proof of the failed duplicate-source execution;
- nonempty receipt, message, or nullifier proof evidence;
- semantic identity across distinct leaf proof implementations or encodings;
- asset conservation or authorized mint and burn semantics;
- pre-state and post-state chain continuity;
- schedule, carry, or data-availability validity;
- durable atomic ledger admission;
- release, settlement, or production authority;
- privacy or zero-knowledge confidentiality.

All corresponding claim flags remain false.

## Next implementation tranche

Add the first value-bearing semantic profile. Its leaf disclosure must open
authenticated asset rows and state transitions, and its composer must prove
global asset conservation, authorized mint and burn transformations, and exact
pre-state to post-state continuity across the canonical leaf order. Preserve
the retained structural and semantic roots as separate identities. Add nonempty
receipt, message, schedule, carry, and data-availability profiles only after
their authenticated opening languages and global composition laws are defined.
