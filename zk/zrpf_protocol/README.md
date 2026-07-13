# ZRPF V3 Protocol Nucleus

This workspace contains the proof-system-neutral structural protocol candidate
for the Zeno Recursive Proof Fabric used by ZenoDEX.

The crate currently provides:

- nonzero typed identifiers and commitments;
- a shared leaf-and-aggregate `NodeJournalV3` shape;
- application, domain, epoch, policy, dependency, and toolchain scope binding;
- verifier IDs derived from program ID, proof profile, and journal version;
- exact, bounded, canonical Postcard decoding;
- canonical dense child partitions and checked tree counts;
- explicit operation-count units, with mixed-unit aggregation rejected;
- a mandatory provenance commitment for source-proof adapters;
- derived child task, claim, journal, program, profile, verifier, statement,
  manifest, effect, provenance, and data-availability roots;
- a bounded fanout-8, depth-2 profile covering at most 64 leaves;
- a bounded canonical `EconomicActionRecordV1` whose action ID excludes proof,
  receipt, salt, and signature representation fields;
- an action-bound `AuthorizationConsumptionNullifierV1` compatibility identity
  for binding a canonical action to a grant;
- an `AuthorizationGrantSpendNullifierV1` derived only from application,
  domain, grant, and nonce for durable single-use enforcement;
- a bounded `EconomicActionBatchV1` that rejects duplicate actions,
  grant-and-nonce spends, and cross-action consumed objects;
- a bounded canonical `SettlementEpochCertificateV1` proof-neutral journal
  that binds semantic, action, effect-plan, state, policy, certificate, and
  dependency roots without runtime verifier identity;
- a proof-neutral `SparseMerkleCellTransitionWitnessV1` for the initial
  ordinary Spot profile, with one fixed 256-level MSB-first path, nonzero
  siblings, independently derived pre/post roots, and exact equality to one
  `LedgerCellWriteV2`;
- a `ValidatedSparseMerkleBatchTransitionV1` that chains 1..=64 exact cell
  witnesses in strictly increasing key order, requires one unique economic
  action ID per write, and binds the first and final roots;
- a bounded `ProgramManifestV1` that commits proof backend, program, declared
  build identity inputs, verifier policy, receipt codec, security level, and
  privacy claim;
- a bounded `ProofTaskV1` whose derived task ID commits scope, statement,
  manifest, inputs, DA root, resource ceilings, reward ceiling, redundancy,
  privacy, and deterministic sequence deadlines;
- a bounded `ProofAssignmentPolicyV1` and deterministic compatibility verdict
  for task, manifest, profile, codec, policy-root, security, epoch, privacy,
  resource, and redundancy checks.

## Authority Boundary

This crate validates structure. It does not verify a proof receipt or ZenoDEX
effect semantics.

`ProjectedChildDescriptorV3::project_canonical_journal` derives metadata from
exact canonical journal bytes. The resulting descriptor has no proof authority.
A proof-backend adapter must verify the exact receipt claim, governed program,
and exact journal bytes before an authority-bearing aggregate guest uses it.
The additive `zk/zrpf_risc0` profile implements that ordering for the Spot V1
compatibility adapter and the bounded level-one and level-two structural guests.

`NodeCommitmentsV3` makes all ZenoDEX commitment fields mandatory and nonzero.
The compatibility adapter derives its field-specific values from an
authenticated V1 journal, and the structural guests derive roots over those
authenticated child commitments. A separate native leaf and semantic aggregate
profile must derive or verify their ZenoDEX meanings. The current structural
profile does not establish conservation, descendant uniqueness, message
cancellation, scheduling, carry continuity, or data availability.

The economic-action and authorization identities are deterministic data. The
action-bound compatibility identity is not a single-use grant key. The
grant-spend nullifier supplies that key, while this crate does not verify a
signature or grant, derive ZenoDEX effect semantics, persist uniqueness state,
or authorize value movement.

The settlement certificate is a canonical proof-neutral journal. Its source
claim binding and DA, schedule, carry, plan, and state roots remain
unauthenticated data until a guest verifies their source obligations and a
sealed host verifier authenticates the exact receipt, runtime image, receipt
profile, and governed manifest. Decoding or hashing the certificate grants no
ledger authority.

The sparse-Merkle witness closes only one cell transition. Its leaf hash binds
the cell key and value hash, each internal hash binds its root-indexed depth and
ordered children, and the action ID is checked when the witness is bound to the
complete `LedgerCellWriteV2`. The validated projection has private fields and
exposes the two derived roots. The bounded batch profile composes those
projections sequentially: each pre-root must equal the preceding post-root, and
the outer roots must match the first and final witnesses. V1 deliberately
carries every 256-sibling path and permits one cell write per economic action.
It does not authenticate a receipt, atomically persist writes, admit a ledger
transition, or establish a compressed multiproof. A future compression profile
must define one canonical multiproof ABI, preserve the same key order and root
result, reject duplicate keys, and bind the complete canonical write set.

The manifest and task objects are canonical proposals. A manifest becomes
eligible only after a separately governed release policy authorizes its exact
root. A task becomes payable only after an assigned proof verifies and the
ledger admits the governed result. Sequence deadlines are explicit protocol
inputs; these objects never read a wall clock.

The task and manifest objects alone do not establish cross-object compatibility.
`evaluate_proof_assignment_compatibility_v1` checks them against an explicit
assignment policy and preserves standby-diversity ambiguity as a typed pending
verdict. The supplied policy still requires external governance authentication,
and a compatible snapshot carries no proof, payment, or admission authority.

The full claim boundary and next steps are documented in
`docs/research/ZRPF_V3_CORRECT_BY_CONSTRUCTION_SPEC_20260710.md` from the
repository root. The action and grant-spend formulas are specified in
`docs/research/ZRPF_ECONOMIC_ACTION_NULLIFIER_V1_CBC_SPEC_20260712.md`. Assignment
compatibility is specified in
`docs/research/ZRPF_PROOF_ASSIGNMENT_COMPATIBILITY_V1_CBC_SPEC_20260712.md`.

## Verification

Run with the repository-pinned Rust toolchain:

```bash
cargo fmt --all -- --check
cargo test --locked --all-targets
cargo clippy --locked --all-targets -- -D warnings
cargo test --locked --doc
```

The independent Python hash-vector replay is run from the repository root:

```bash
python3 tools/check_zrpf_v3_hash_vector.py
```
