# ZRPF Source-Opened Ordinary Spot V6 CBC Specification

Date: 2026-07-13

Status: implementation present; current-source V2 adapter contract pending its
deterministic source observation; final local proof-chain and retained replay
evidence pending

## Scope

This specification governs one bounded source-opened ordinary Spot path:

```text
authenticated RISC0 Spot source receipt
  -> current-source V2 adapter receipt
  -> source-opened Spot value leaf V6
  -> Value Aggregate L1 V6
  -> Value Aggregate L2 V6
  -> source-opened ordinary Spot settlement V6
  -> receipt-authenticated settlement-admission statement
  -> atomic replay, provenance, and effect-plan persistence
```

The path represents one ordinary Spot action. L1 and L2 each consume exactly
one child in the current proof harness. This supplies a real recursive receipt
chain after the evidence run succeeds. It supplies no multi-leaf fanout,
maximum-topology, or throughput claim.

## Authority Law

Every authority transition is explicit:

```text
untrusted bounded bytes
  -> strict typed decode
  -> exact RISC0 receipt/profile/image verification
  -> authenticated journal
  -> independent expected-journal recomposition
  -> byte equality
  -> private authenticated result
  -> transactional admission plan
```

No host Boolean, report field, artifact name, file path, or caller-selected
program identifier creates proof authority.

## Historical Baseline Program Chain

These image IDs describe the pre-PR426 baseline proof run. The source hardening
change invalidated the source, adapter, leaf, L1, L2, and settlement identities.
They must not be used as the final current-source chain:

| Program | RISC0 image ID |
| --- | --- |
| source-opened Spot value leaf V6 | `67494a413c729cbb4b6095036425ba0b86edcc30625c19b525409f8e8ff022d1` |
| Spot value aggregate L1 V6 | `a2b4c32ef76c0a81643f1758c476fc21f6a7c2afd11d2a6e08fae022418e2e15` |
| Spot value aggregate L2 V6 | `5c8f94b4ada70ad5ba0d6ac6bd6b0055a9e148c329372e7b24a81249ff07a76f` |
| source-opened Spot settlement V6 | `73a1c5c275d85f39443f68803932df9caac670b420b9948b7e7b2dffe1f2e98d` |

Each successor pins the exact predecessor image:

```text
leaf V6       pins the governed adapter image
L1 V6         pins leaf V6
L2 V6         pins L1 V6
settlement V6 pins L2 V6
host verifier pins settlement V6
```

The settlement program manifest additionally binds the semantic profile and
the fixed `ZRPFSAV1` settlement-admission journal contract.

## Current-Source V2 Adapter Bootstrap

The historical V1 source policy, adapter guest, anchor, policy JSON, and
retained evidence remain byte-preserved. The successor uses a distinct guest
and profile:

```text
source policy module   source_policy_v2.rs
adapter guest          zenodex-zrpf-risc0-v2-leaf-adapter
adapter profile        zrpf_v2_leaf_adapter_compatibility_v2
anchor schema          zenodex/zrpf_current_source_anchor/v2
policy schema          zenodex/zrpf_v2_leaf_adapter_source_policy/v2
```

The committed V2 Rust policy contains zero identity sentinels. Its governance
documents contain `null` identity fields and set receipt, release, settlement,
and production authority to false. The adapter therefore rejects before source
journal interpretation until the deterministic build observes and repins all
three source values:

```text
source image ID
source program SHA-256
state-proof workspace source-closure root
```

The source-closure root covers the tracked `zk/state_proof_risc0` workspace.
It excludes `zk/zrpf_risc0`, including the V2 source policy and adapter guest.
This prevents the policy from committing to a broad inventory that contains
itself. The broader three-workspace inventory remains a separate repository
superset observation.

After stage 1, the planner emits an unpromoted anchor candidate from the exact
source observation. After stage 2, it emits an unpromoted adapter-policy
candidate from the exact V2 adapter observation. Both candidates retain every
authority Boolean as false. The V6 leaf pin is updated only from the observed
V2 adapter image ID. No image ID is predicted or copied from the baseline.

## Source Opening

The leaf host boundary strictly decodes the source request and proof envelope,
requires the singleton ordered Spot profile, checks matching state identity,
decodes the embedded receipt with bounded canonical base64, and requires a
Succinct receipt under the governed source image.

It independently recomposes the source transition journal from the typed
source input and requires byte equality with the verified source receipt
journal. It then verifies the exact adapter receipt and builds the V6 guest
input from:

- the adapter's authenticated journal;
- the exact typed source input encoded with Postcard;
- the authenticated source journal.

The guest verifies the adapter receipt before interpreting the adapter journal.
It recomposes the source transition and the V6 value statement. A valid source
receipt whose typed request does not recompose to its journal rejects.

## Recursive Aggregation

L1 V6 verifies every supplied child under the compile-time leaf V6 image before
decoding and composing child journals. L2 V6 applies the same ordering with the
compile-time L1 V6 image.

The current proof harness bounds both levels to one child. The protocol types
retain broader bounded aggregation support, but promotion of fanout requires
fresh distinct leaves, state-compatible semantics, resource measurements, and
negative duplicate evidence.

The recursive statements commit to the operational V5 surface, including:

- economic action identity and authorization-nullifier roots;
- state and transition commitments;
- asset, message, carry, reward, receipt, task, and schedule commitments;
- program, profile, dependency, feature, policy, and toolchain identities.

## State-Bound Settlement

The settlement guest verifies the exact L2 V6 receipt before interpreting its
journal. It recomposes the expected L2 proposal and derives the semantic claim
binding from the verified L2 image and canonical proposal bytes.

The ordinary Spot compatibility composer then validates:

- one canonical economic action;
- one authorization consumption and grant spend;
- one sparse-Merkle cell transition witness;
- two ordinary conserved asset rows;
- zero mint, burn, reward, carry, and cross-shard message rows;
- exact pre-state and post-state roots derived from the cell witness;
- the exact settlement-effect plan commitment;
- a full-blob content certificate over the source-opened replay bytes.

The current harness uses deterministic synthetic sparse-Merkle siblings. The
receipt is state-bound to those exact roots. It is not evidence that the roots
were read from or committed by a live ZenoLedger instance.

## Settlement-Admission Journal

The settlement guest commits one fixed outer frame:

```text
magic = ZRPFSAV1
version
settlement certificate bytes and SHA-256
settlement effect-plan bytes and SHA-256
```

The strict Rust and Python decoders independently enforce:

- exact discriminator and version;
- bounded lengths before allocation;
- nonempty canonical inner objects;
- exact component hashes;
- complete byte consumption;
- deterministic certificate identity derivation.

The frame is a proof-neutral codec until it is obtained from a receipt verified
under the governed settlement image.

## External Verifier

`source-opened-spot-settlement-verifier-v6` accepts canonical compact JSON in
the exact field order:

```text
schema, receipt_hex, guest_input_hex
```

It verifies the settlement receipt exactly once, strict-decodes the supplied
guest input, independently recomposes the expected settlement-admission
journal, and requires byte equality. It emits one canonical response binding:

- receipt and guest-input bytes and hashes;
- admission journal, certificate, and effect-plan bytes and hashes;
- governed settlement program, profile, manifest, and receipt-security
  identities;
- settlement claim binding;
- the narrow singleton ordinary-Spot execution projection.

The execution projection rejects messages, carry, rewards, nonordinary rows,
supply effects, unexpected authority, cross-action rows, and nonconservation.

## Python Projection Boundary

`PinnedSourceOpenedSpotSettlementVerifierV6` pins and executes the governed
Rust verifier. It requires exact canonical request and response bytes, decodes
the returned `ZRPFSAV1` frame independently, and checks every duplicated byte,
length, hash, and identity field.

It projects only shared singleton ordinary-Spot semantics into
`SettlementEffectPlanV1`. Rust V2 binary-domain commitments and Python V1
JSON-domain commitments are distinct. The adapter does not claim equality
between those domains. A separate domain-separated projection binding commits
to the exact admission journal and canonical Python projection.

## Atomic Durable Admission

SQLite schema V4 persists the following in one `BEGIN IMMEDIATE` transaction:

- exact settlement receipt bytes and SHA-256;
- exact settlement guest-input bytes and SHA-256;
- exact settlement-admission journal bytes and SHA-256;
- reconstructed source-opened replay bytes and SHA-256;
- exact full-blob content-certificate bytes and SHA-256;
- exact settlement certificate and effect-plan bytes;
- certificate ID and certificate commitment;
- governed program, profile, manifest, and receipt-security identities;
- canonical Python execution projection and projection binding;
- action, authorization, grant-spend, replay, and cursor state.

Unique indexes, cursor compare-and-swap, and a monotonic association count make
concurrent replay and row-deletion downgrade fail closed. Restart validation
rehashes, redecodes, reconstructs, and rebinds the persisted artifacts before
exposing state. Migration to V4 is allowed only when prior certificate history
is empty.

This transaction establishes exact-once local persistence of the authenticated
statement and its projected effects. It does not apply a live ZenoLedger
balance tree or grant settlement authority.

## Required Evidence

Promotion of the scoped local claim requires:

1. deterministic source and V2 adapter observations followed by a source-pinned
   build record for all four V6 guests;
2. independently recomputed RISC0 program-binary hashes, sizes, and image IDs;
3. one real Succinct receipt at leaf, L1, L2, and settlement;
4. exact source request/proof, adapter receipt, guest inputs, replay bytes,
   content certificate, admission journal, and verifier transcript inventory;
5. exact seal mutation rejection at every retained proof layer;
6. wrong-image, child-substitution, guest-input-substitution, journal, plan,
   certificate, and transcript mutation rejection;
7. byte-identical normal and ambient-dev verifier output for real receipts,
   with fake/dev receipts still rejected;
8. restart, concurrency, row-deletion, and persisted-artifact mutation tests;
9. required CI coverage for source build, image identity, retained replay,
   evidence validation, dependency audit, and artifact privacy scanning.

The final evidence record must distinguish executed commands from planned or
inferred commands.

## Build-Record Authority Boundary

`ZRPF_SOURCE_OPENED_SPOT_V6_BUILD_RECORD_20260712.json` uses schema V3. Its
checker owns the governed record SHA-256 and the exact Rust, Cargo, `r0vm`, and
`cargo-risczero` identities. A caller-supplied record hash is an additional
cross-check only. It cannot authorize a different record.

The checker mechanically derives the four guest crates from the Spot V6 build
orchestrator and recursively follows normal and build-time local Cargo path
dependencies. The governed 15-crate graph includes
`zk/zrpf_risc0/aggregate_shared`. The selected source inventory also includes
the build orchestrator and settlement root-policy source. Current and committed
inventories are bounded and hash-equal. The current inventory is rechecked
globally at the end of each validation.

The record qualifies historical build and clean-target statements as
publisher-reported observations. The checker does not independently verify
those historical commands or global worktree cleanliness. With all four
external program binaries and the checker-owned `r0vm`, it can establish the
narrow observation that the governed record, binary sizes and hashes, and four
recomputed image IDs agree at check time.

```text
GovernedRecordHash
&& ExactOfficialToolIdentity
&& FourRecordedBinaryIdentitiesMatch
&& FourImageIdsRecompute
-> LiveGovernedArtifactSetObserved
```

This observation is not evidence that Cargo produced those binaries from the
recorded source. It grants no proof, release, settlement, or production
authority.

## Explicit Non-Claims

The current V6 path does not establish:

- more than one ordinary Spot action;
- multi-leaf fanout, a 64-leaf tree, maximum topology, throughput, latency, or
  prover-market capacity;
- end-user signature validity or live authorization-grant registry authority;
- live ZenoLedger sparse-Merkle membership, current-state continuity, balance
  mutation, rollback protection, or application consensus;
- protocol-fee, mint, burn, reward, carry, cross-shard message, perps, zUSD,
  oracle, or cross-lane settlement semantics;
- storage-provider retention, network retrievability, erasure coding, sampling,
  quorum availability, or external data finality;
- source-chain finality beyond the exact retained local source artifact;
- proof-byte determinism;
- path-independent or cross-host reproducible builds;
- independent verification of the publisher-reported historical build
  commands or clean external target;
- global worktree cleanliness;
- source-to-program-binary build provenance or reproducibility;
- any current source or V2 adapter image identity before the deterministic
  build observations are recorded;
- Tau or external-chain finality;
- governed release, settlement, or production authority;
- witness privacy, zero knowledge, covert-channel freedom, or hardware
  side-channel resistance;
- Firecracker isolation for this V6 verifier path.

The strongest current checked build-record claim is:

> One checker-governed V3 record binds the selected source closure at commit
> `87c7a5b1146482d7a55428179ed6d3453b43a7e7`, the complete governed local Cargo
> path-dependency graph, exact official tool identities, and four recorded
> program-binary identities. A live check can additionally recompute and match
> all four governed image IDs without creating build-provenance or proof
> authority.

The strongest proof-and-replay target claim remains:

> Demonstrate one governed, source-opened, singleton ordinary Spot transition
> through a real leaf-to-L1-to-L2-to-settlement RISC0 chain, independent
> reverification and recomposition, and atomic persistence with exact provenance
> and effect projection.

That claim becomes true only after the required proof and replay evidence
succeeds and its checked record is committed.
