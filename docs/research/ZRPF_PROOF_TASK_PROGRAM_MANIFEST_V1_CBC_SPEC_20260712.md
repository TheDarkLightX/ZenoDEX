# ZRPF Proof Task And Program Manifest V1 CBC Specification

Date: 2026-07-12

Status: implemented proof-neutral protocol objects; no market or release authority

## Scope

`zk/zrpf_protocol` defines two bounded objects required by the ZenoDEX-facing
ZRPF proof market:

- `ProgramManifestV1`, a versioned declared program and verifier identity;
- `ProofTaskV1`, a deterministic unit of assigned proving work.

Both objects have private fields, validated constructors, domain-separated
derived identities, exact Postcard codecs, and explicit input bounds. They
perform no I/O and read no environment, filesystem, network, random source, or
wall clock.

## Program manifest

The manifest commits:

```text
manifest_version
proof_system_id
proof_system_version_id
program_id
source_tree_hash
compiler_hash
outer_cargo_hash?
nested_cargo_hash?
linker_hash
dependency_lock_hash
build_config_hash
verifier_binary_hash
verifier_policy_root
receipt_codec_id
security_level_bits
privacy_claim
revocation_epoch?
```

Optional values use a one-byte presence tag before their fixed-width value.
The manifest root hashes the exact field sequence under
`zenodex.zrpf.program_manifest_root.v1`. A decoded manifest independently
rederives the root and rejects substitution.

`security_level_bits` is bounded to `1..=512`. `revocation_epoch` uses the full
unsigned 64-bit domain when present. The privacy claim is a typed enum with
`PublicComputation` and `WitnessPrivate` variants. A privacy label remains a
claim until a governed verifier profile and evidence establish it.

## Proof task

The task commits:

```text
task_version
task_kind
application_id
chain_or_domain_id
epoch_id
priority
proof_profile_id
accepted_proof_systems[1..=8]
program_manifest_root
statement_hash
input_commitment_root
data_availability_root
parent_task_id?
expected_child_task_root?
max_input_bytes
max_cycles_or_trace_rows
max_memory_bytes
deadline_sequence
reward_asset_id
max_reward_atoms
redundancy_policy
privacy_policy
created_sequence
```

The constructor sorts accepted proof-system IDs by exact bytes and rejects a
duplicate. Aggregate and epoch-checkpoint tasks require a child-task root.
Leaf and DA tasks prohibit one. Every resource ceiling is nonzero and bounded:

```text
max_input_bytes          <= 64 MiB
max_cycles_or_trace_rows <= 2^48
max_memory_bytes         <= 16 GiB
```

The deadline is a deterministic protocol sequence and must exceed the creation
sequence. The task never obtains authority from a host wall clock. Translation
from a human time policy into a sequence deadline belongs to governed scheduler
state and must be committed before task construction.

Redundancy requires `1..=8` primary proofs, `0..=8` standby provers, and at
least one accepted proof system. The requested number of distinct proof
systems cannot exceed the accepted set.

The task ID hashes every field above under
`zenodex.zrpf.proof_task_id.v1`. A decoded task independently rederives the ID.

## Disaster-state closures

| Disaster state | Closure |
| --- | --- |
| task publisher changes a resource or payout field after bidding | task ID binds every resource and reward ceiling |
| aggregate task omits the expected child set | aggregate and checkpoint constructors require the child-task root |
| leaf is relabeled with an unauthenticated child set | leaf and DA constructors reject a child-task root |
| accepted backend order produces different IDs | constructor sorts exact proof-system IDs |
| one backend is duplicated to satisfy diversity | duplicate proof-system IDs reject; distinct-system minimum is bounded by the set |
| verifier binary or policy changes under one manifest | manifest root binds both exact identities |
| ambient wall clock changes task validity | task uses committed sequence numbers only |
| oversized declared input triggers allocation | exact codec caps bytes; bounded sequence visitor rejects count above eight before payload allocation |
| persisted identity is substituted | decode rederives manifest root or task ID and exact-reencodes bytes |
| extension field is silently ignored | typed JSON decoding and Postcard wire types deny unknown fields |

## Evidence

Run:

```bash
cargo fmt --manifest-path zk/zrpf_protocol/Cargo.toml --all -- --check
cargo test --manifest-path zk/zrpf_protocol/Cargo.toml --locked --all-targets
cargo clippy --manifest-path zk/zrpf_protocol/Cargo.toml --locked --all-targets -- -D warnings
cargo test --manifest-path zk/zrpf_protocol/Cargo.toml --locked --doc
```

The focused test suite covers exact codec round trips, all truncated prefixes,
trailing and oversized input, root and task-ID substitution, unknown fields,
proof-system permutation and duplication, child binding, resource and deadline
bounds, redundancy, and task-field separation.

An independent test reconstructs both hash preimages without the production
hash helpers and freezes these vectors:

```text
program_manifest_root = a20cb20b458c693bb53ed14a51db5ed55ac7553f2934c0753acfb59c51bda2c7
proof_task_id          = fe3a5d92a37aec9f4d9286403679fd8811eff0393164c3d9b331245987c88ade

optional_manifest_root = ec629c23da31ad790e3dc38138837ab9753c315861f4660b0c14fa069a227c8d
aggregate_task_id      = 8414b0c77fbbe029ed69084766a3ccc09360de8640561dd79d15f64f4ce646d5
```

## Non-claims

These two objects alone do not establish:

- source-to-binary reproducibility or completeness of declared build inputs;
- that a manifest root is governed, unrevoked, or eligible for release;
- that a declared security level is achieved by the proof system or verifier;
- compatibility without an explicit validated assignment policy;
- that a task input or DA root is available;
- that a prover is assigned, bonded, independent, or capable;
- resolution of whether standby provers count toward requested proof-system
  diversity;
- that a proof was produced, verified, included, admitted, or paid;
- confidentiality solely from a privacy label;
- economic action validity, settlement, ledger admission, finality, throughput,
  public replay, or production authority.

## Next boundary

`ProofAssignmentPolicyV1` and
`evaluate_proof_assignment_compatibility_v1` implement the local compatibility
checks described in
`ZRPF_PROOF_ASSIGNMENT_COMPATIBILITY_V1_CBC_SPEC_20260712.md`. A governed
registry must still authenticate the exact policy, manifest root, and
revocations. Payment may occur only after the verifier emits an authenticated
receipt for the task and ZenoLedger atomically admits the result and payout.
