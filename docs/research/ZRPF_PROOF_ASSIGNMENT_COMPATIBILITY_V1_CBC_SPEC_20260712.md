# ZRPF Proof Assignment Compatibility V1 CBC Specification

Date: 2026-07-12

Status: implemented proof-neutral compatibility; deterministic local tests only

## Scope

This specification closes the local compatibility gap between
`ProgramManifestV1` and `ProofTaskV1`. It defines:

- `ProofAssignmentPolicyV1`, a bounded policy supplied by a governed caller;
- `evaluate_proof_assignment_compatibility_v1`, a pure deterministic check;
- `ProofAssignmentCompatibilityVerdictV1`, with compatible, rejected, and
  pending outcomes;
- `CompatibleProofAssignmentV1`, a private-construction snapshot of the exact
  task, manifest, proof system, and assignment epoch that passed.

These objects perform no I/O and read no wall clock, registry, environment,
filesystem, network, or mutable global state.

Compatibility does not verify a proof, authorize a prover, authorize payment,
admit ledger state, or prove that a policy came from governance.

## Existing schema inventory

The compatibility check uses only meanings already present in the V1 schemas:

| Owner | Field | Meaning used by compatibility |
| --- | --- | --- |
| task | `program_manifest_root` | exact manifest identity requested by the task |
| manifest | `manifest_root` | recomputed identity of all manifest fields |
| manifest | `proof_system_id` | proof backend selected by this manifest |
| task | `accepted_proof_systems` | canonical set from which the selected backend must come |
| task | `proof_profile_id` | governed profile identity required by the task |
| manifest | `receipt_codec_id` | receipt encoding declared by the selected manifest |
| manifest | `verifier_policy_root` | exact verifier-policy hash declared by the manifest |
| manifest | `security_level_bits` | declared security level; compatibility treats it only as a declaration |
| manifest | `privacy_claim` | `PublicComputation` or `WitnessPrivate` declaration |
| task | `privacy_policy` | public, private-allowed, or private-required task constraint |
| manifest | `revocation_epoch` | manifest is ineligible at and after this epoch when present |
| task | three resource ceilings | input bytes, cycles or trace rows, and memory bytes |
| task | redundancy policy | primary proofs, standby provers, and minimum distinct systems |

No V1 task field directly names a receipt codec or verifier-policy root. No V1
manifest field directly names a proof profile. Compatibility therefore needs an
explicit governed policy mapping those three identities.

## Assignment policy

```text
ProofAssignmentPolicyV1 {
  policy_version: 1
  authorized_program_manifest_root: bytes32
  required_proof_profile_id: bytes32
  required_receipt_codec_id: bytes32
  required_verifier_policy_root: bytes32
  minimum_security_level_bits: u16
  valid_from_epoch: u64
  valid_through_epoch: u64
  max_input_bytes: u64
  max_cycles_or_trace_rows: u64
  max_memory_bytes: u64
}
```

Validity endpoints are inclusive. Construction rejects a reversed validity
range, zero security floor, a security floor above 512, zero resource ceilings,
or resource ceilings above the global V1 task bounds.

The policy has an exact bounded Postcard codec and validated private fields. It
has no derived policy hash. A caller that persists or governs the policy must
bind the exact canonical bytes or a separately governed external identity.

## Compatibility decision order

The evaluator receives a validated task, manifest, policy, and explicit
`assignment_epoch`. It checks in this order:

1. task self-validation;
2. manifest self-validation;
3. policy self-validation;
4. task manifest root equals the supplied manifest root;
5. supplied manifest root equals the policy-authorized root;
6. manifest proof system belongs to the task's accepted set;
7. task proof profile equals the policy-required profile;
8. manifest receipt codec equals the policy-required codec;
9. manifest verifier-policy root equals the policy-required root;
10. declared manifest security is at least the policy floor;
11. assignment epoch is within the inclusive policy interval;
12. assignment epoch is strictly before manifest revocation when present;
13. task privacy policy is compatible with the manifest privacy claim;
14. each task resource ceiling is at most the corresponding policy ceiling;
15. redundancy counts are locally feasible or classified pending.

The first failed check determines the typed reject. No external effects occur.
The caller owns the meaning and authenticity of `assignment_epoch`. V1 does
not equate it with the task's `epoch_id` because the existing schemas do not
define that relationship.

## Privacy matrix

| Task policy | Public computation manifest | Witness-private manifest |
| --- | --- | --- |
| `PublicInputs` | compatible | compatible |
| `PrivateWitnessAllowed` | compatible | compatible |
| `PrivateWitnessRequired` | reject privacy downgrade | compatible |

Public inputs can coexist with a private witness. `Allowed` does not require a
private-witness-capable manifest. A compatible privacy pair still provides no
confidentiality evidence.

## Redundancy decision

The existing task constructor already enforces:

- primary proofs in `1..=8`;
- standby provers in `0..=8`;
- minimum distinct proof systems in `1..=accepted_system_count`.

Compatibility adds the strongest policy-neutral conclusions available:

```text
slots = required_primary_proofs + standby_provers

minimum_distinct > slots
  -> reject ImpossibleRedundancy

required_primary_proofs < minimum_distinct <= slots
  -> pending StandbyDiversitySemantics

minimum_distinct <= required_primary_proofs
  -> locally coherent
```

The pending row preserves the unresolved meaning of standby diversity. It does
not assume whether standby provers count toward the required proof-system
diversity.

## Compatible snapshot

A compatible verdict returns a private-construction snapshot containing:

```text
task_id
program_manifest_root
selected_proof_system_id
proof_profile_id
receipt_codec_id
verifier_policy_root
assignment_epoch
```

The snapshot records what passed this pure check. It is not a capability,
receipt, authorization, payment instruction, proof, or ledger-admission token.

## Disaster-state closures

| Disaster state | Closure |
| --- | --- |
| task is paired with a different manifest | exact task-to-manifest root equality |
| ungoverned manifest is substituted | policy-authorized root equality |
| manifest backend is unsupported by the task | exact accepted-set membership |
| task profile is paired with another codec or verifier policy | explicit governed profile/codec/policy-root mapping |
| declared security is downgraded | minimum security floor |
| expired policy is reused | explicit inclusive validity interval |
| revoked manifest is reused | reject at and after `revocation_epoch` |
| private-required task is assigned to public-only manifest | privacy matrix reject |
| task resource declaration exceeds governed ceilings | per-resource upper-bound checks |
| diversity exceeds all primary and standby slots | impossible-redundancy reject |
| diversity depends on unresolved standby meaning | typed pending verdict |

## Required evidence

Focused tests must include:

- compatible baseline;
- one-field root, profile, codec, and verifier-policy mutations;
- unsupported proof system;
- declared-security downgrade;
- each privacy matrix row;
- policy not-yet-valid and expired epochs;
- revocation immediately before, at, and after the boundary;
- one-over-limit input, cycle, and memory declarations;
- impossible and pending redundancy cases;
- stale, unknown, trailing, truncated, and oversized policy codec inputs;
- confirmation that compatible snapshots expose no payment or proof result.

Run:

```bash
cargo fmt --manifest-path zk/zrpf_protocol/Cargo.toml --all -- --check
cargo test --manifest-path zk/zrpf_protocol/Cargo.toml --locked --all-targets
cargo clippy --manifest-path zk/zrpf_protocol/Cargo.toml --locked --all-targets -- -D warnings
cargo test --manifest-path zk/zrpf_protocol/Cargo.toml --locked --doc
```

## Non-claims

This compatibility surface does not establish:

- governance authenticity or freshness of the supplied policy;
- authenticity of `assignment_epoch` or equality between `assignment_epoch`
  and the task's `epoch_id`;
- correctness of the policy's profile-to-codec or profile-to-verifier mapping;
- source-to-binary reproducibility or completeness of manifest declarations;
- that the declared security level is achieved;
- confidentiality from a privacy label;
- proof generation, proof verification, receipt authentication, or assignment
  to a specific prover;
- feasibility of standby diversity while its semantics remain pending;
- task input or data availability;
- bid, bond, reward, fee, payment, settlement, admission, finality, or production
  authority.

The task reward fields are intentionally outside compatibility. Existing V1
schemas define no governed reward-to-manifest relation for this evaluator to
enforce.

## Next boundary

A governed registry must authenticate the exact assignment policy and manifest
root. A scheduler must resolve pending redundancy semantics before assignment.
An authenticated verifier must later bind a verified receipt to the compatible
task and manifest. Payment and ledger admission remain separate atomic gates.
