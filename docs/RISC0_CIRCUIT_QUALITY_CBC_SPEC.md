# RISC0 Circuit Quality CBC Spec

Date: 2026-07-04
Status: design and implementation policy

## Claim Scope

This document defines the correct-by-construction quality contract for ZenoDEX
RISC0 circuits, journals, proof metadata, recursive aggregation, and verifier
admission. It is a design and implementation policy. It does not claim that
recursive RISC0 aggregation is already implemented.

The spec applies to:

- `zk/state_proof_risc0/**`;
- proof metadata and proof-profile code under `tools/**` and `src/integration/**`;
- ZenoLedger/Tau admission paths that consume RISC0 receipts or journals;
- future recursive proof aggregation work.

Related guidance:

- `AGENTS.md`
- `zk/AGENTS.md`
- `docs/research/RECURSIVE_STARK_SCALING_ARCHITECTURE_20260704.md`

## Core Law

Circuit quality is a statement-construction problem.

```text
TypedStatement
  -> deterministic witness builder
  -> guest verifies the witness
  -> canonical journal
  -> verifier checks receipt, image ID, journal hash, profile, and metadata roots
```

The prover may propose data. The guest and verifier decide what is trusted.

## Non-Claims

This spec does not claim:

- current RISC0 code already uses recursive composition;
- current proof profiles are production-ready;
- every ZenoDEX transition has a RISC0 leaf proof;
- data availability is solved by proof recursion;
- any RISC0 version-specific API is stable across upgrades;
- a successful local proof smoke is production evidence by itself.

## Disaster States

Every circuit and verifier change must name which disaster states it affects.

| Disaster state | Primary defense |
| --- | --- |
| proof from wrong program accepted | expected image ID in typed statement and receipt verify |
| proof paired with wrong journal | canonical journal hash checked by verifier |
| proof replayed across chain/config/domain | domain separator, chain ID, config hash, policy hash |
| production accepts dev proof | dev mode prohibited by production profile gate |
| host witness lies | guest recomputes or checks claim-relevant witness fields |
| child proof omitted in recursive root | child count/root and in-guest child receipt verification |
| child proof swapped | child journal digest and child verifier ID bound in root |
| stale verifier accepted | verifier ID membership in `verifier_set_root` |
| metadata stronger than proof | metadata roots must equal journal and block roots |
| unbalanced asset movement | typed delta rows and aggregate conservation check |
| unauthorized mint/burn/slash/reward | authority root membership and lane-specific policy |
| rejected proof mutates state | reject-is-no-op test and transition staging |
| data hidden behind a proof | data availability root plus DA policy verifier |
| ambiguous schema evolution | append-only schema, explicit version, reject unknown criticals |
| overflow or truncation | checked arithmetic, bounded counts, explicit widths |

## Typed Statement Contract

Every proof family must define a typed statement before implementing the guest.
The statement is the public contract. It must be hashable, canonical, bounded,
and versioned.

Minimum fields:

```text
Risc0StatementV1 {
  domain_separator
  schema_version
  chain_id
  config_hash
  epoch_or_height_range
  proof_profile
  expected_image_id
  verifier_set_root
  public_policy_hash
  feature_suite_hash
  dependency_lock_hash
  toolchain_lock_hash
  pre_state_root
  post_state_root
  tx_root
  evidence_root
  receipt_root
  data_availability_root
  max_witness_bytes
  max_public_rows
}
```

Recursive statements additionally require:

```text
RecursiveStatementV1 {
  child_verification_claims_root
  child_journals_root
  child_effect_summaries_root
  child_count
  max_child_journal_bytes
  max_total_child_journal_bytes
  max_recursion_depth
  conflict_schedule_hash
  carry_queue_pre_root
  carry_queue_post_root
}
```

The constructor must reject:

- missing required roots;
- all-zero image ID, verifier ID, or root where nonzero is required;
- unknown critical fields;
- ambiguous defaults;
- duplicate IDs;
- unsorted rows;
- row counts above configured bounds;
- profile/image/profile-kind mismatch;
- stale schema version;
- domain, chain, config, policy, feature, or toolchain mismatch.

If a field affects acceptance, ordering, conservation, authority, replay, or
public claims, it must be in the statement hash or in a root committed by the
statement hash.

## Witness Contract

Witnesses are private inputs. A witness field is admissible only if it falls
into one of these categories:

1. The guest checks it directly.
2. The guest recomputes a digest/root from it and commits that digest/root.
3. The guest verifies a proof or receipt that authorizes it.
4. A documented theorem shows it is irrelevant to the public statement.

Any other witness field is unconstrained and must be removed or rejected from
the production profile.

Witness builders must be deterministic:

- no wall clock;
- no randomness unless explicitly seeded and committed;
- no environment-dependent behavior;
- no unordered map/set iteration in canonical output;
- no hidden filesystem or network reads;
- no machine-specific paths in committed artifacts.

## Journal Contract

The journal is the public output ABI. It must be stable, canonical, and small.

Minimum fields:

```text
Risc0JournalV1 {
  journal_version
  domain_separator
  chain_id
  config_hash
  proof_profile
  risc0_image_id
  statement_hash
  pre_state_root
  post_state_root
  tx_root
  evidence_root
  receipt_root
  data_availability_root
  public_policy_hash
  feature_suite_hash
  dependency_lock_hash
  toolchain_lock_hash
}
```

Recursive journals additionally require:

```text
RecursiveJournalV1 {
  verifier_set_root
  child_verification_claims_root
  child_journals_root
  child_effect_summaries_root
  child_count
  conflict_schedule_hash
  carry_queue_pre_root
  carry_queue_post_root
  aggregate_asset_delta_root
}
```

The verifier must check:

```text
receipt.verify(expected_image_id)
journal.risc0_image_id == expected_image_id
hash(canonical_journal) == expected_journal_hash
statement_hash == expected_statement_hash
metadata roots == journal roots == block/header/body roots
proof_profile == expected_profile
```

Proof generation is never enough. A generated receipt must be verified against
the expected image ID and expected journal before it is used by a higher layer.

## RISC0 Receipt Profiles

Receipt kind must be explicit at every boundary.

```text
CompositeReceipt:
  purpose: local development and fastest proving
  claim: local proof artifact only unless explicitly accepted by profile

SuccinctReceipt:
  purpose: aggregation and constant-size STARK-style receipt lane
  claim: recursive composition candidate

Groth16Receipt:
  purpose: compact on-chain verifier target where supported
  claim: verifier-adapter-specific public proof
```

Production profiles must reject:

- implicit default prover options;
- dev-mode receipts;
- placeholder methods;
- all-zero image IDs;
- receipt kind missing from metadata;
- receipt kind different from declared profile;
- proof generated under one image ID and reported under another.

The CLI should expose the profile explicitly. Silent fallback between receipt
kinds is forbidden for production proof claims.

## Recursive Composition Contract

Recursive aggregation must verify child receipts in the guest.

Intended shape:

```text
host:
  build child receipts
  compute child journal bytes and verification-claim digests
  add child receipts as assumptions

guest:
  parse bounded child descriptors
  verify every child receipt assumption against child image ID and exact child
  journal bytes
  check child image ID is allowed by verifier_set_root
  decode child summary journal after verification
  compose EffectSummaryV1 values
  commit RecursiveJournalV1
```

Child journal bytes without in-guest receipt verification are data. They do not
carry proof authority.

RISC0 guest recursion verifies a claim of the form `(child_image_id,
child_journal_bytes)`. Exact serialized child receipt hashes are useful host
audit metadata, but they are not what the guest verifier checks. Recursive
journals therefore bind `child_verification_claims_root` and
`child_journals_root`, with any receipt-artifact root kept outside the guest
trust boundary.

The verifier set must not be a free host label. A child verifier ID must be
derived from `(child_image_id, child_profile)` and the recursive guest must
reject any descriptor whose `child_verifier_id` does not equal that derived ID.
The committed `verifier_set_root` is the sorted set of those derived IDs.

The `risc0.zenodex_recursive_summary_leaf.v1` method is a dedicated
summary-leaf image for recursive plumbing and smoke tests. It accepts only
`recursive_summary_leaf_test_v1`. It proves that a bounded summary was committed
by that image, with a 4096-byte postcard input cap and 128-byte caps on summary
text fields. It does not prove spot, perps, zUSD, oracle, or ledger transition
semantics. Production recursive leaves must use transition-specific images that
derive their `EffectSummaryV1` from the checked transition, or an adapter proof
that verifies the source receipt and proves the summary binding.

The `risc0.zenodex_recursive_spot_leaf.v1` method is the first
transition-specific recursive leaf. It accepts `SpotRecursiveLeafInputV1`,
executes the checked spot transition, requires `pre_app_hash` to be present,
requires the leaf `state_hash` to equal the checked post app root, and derives
`EffectSummaryV1` from the resulting `StateProofJournalV1`. Its
`receipt_root` is the native spot accepted-receipts root. Its recursive
accepted/rejected receipt ID sets, cross-shard message sets, and asset-delta rows
are empty in v1, so this profile proves local spot app-state transitions only.
It does not claim cross-shard asset movement or native ledger balance deltas.

Repeatable local smoke path:

```bash
cd zk/state_proof_risc0
RISC0_FORCE_BUILD=1 cargo check -p tau-state-proof-risc0-cli
SUMMARY_IMAGE_ID_HEX=<hex image ID from generated methods.rs>
cargo run -q -p tau-state-proof-risc0-cli --example recursive_summary_leaf_smoke -- \
  summary "$SUMMARY_IMAGE_ID_HEX" > /tmp/summary-leaf.request.json
RISC0_FORCE_BUILD=1 cargo run -q -p tau-state-proof-risc0-cli \
  < /tmp/summary-leaf.request.json > /tmp/summary-leaf.proof.json
cargo run -q -p tau-state-proof-risc0-cli --example recursive_summary_leaf_smoke -- \
  root /tmp/summary-leaf.proof.json > /tmp/recursive-root.request.json
RISC0_FORCE_BUILD=1 cargo run -q -p tau-state-proof-risc0-cli \
  < /tmp/recursive-root.request.json > /tmp/recursive-root.proof.json

SPOT_IMAGE_ID_HEX=<hex spot leaf image ID from generated methods.rs>
cargo run -q -p tau-state-proof-risc0-cli --example recursive_summary_leaf_smoke -- \
  spot "$SPOT_IMAGE_ID_HEX" > /tmp/spot-leaf.request.json
RISC0_FORCE_BUILD=1 cargo run -q -p tau-state-proof-risc0-cli \
  < /tmp/spot-leaf.request.json > /tmp/spot-leaf.proof.json
cargo run -q -p tau-state-proof-risc0-cli --example recursive_summary_leaf_smoke -- \
  root /tmp/spot-leaf.proof.json > /tmp/spot-recursive-root.request.json
RISC0_FORCE_BUILD=1 cargo run -q -p tau-state-proof-risc0-cli \
  < /tmp/spot-recursive-root.request.json > /tmp/spot-recursive-root.proof.json
```

The summary-leaf smoke proves recursive plumbing only. The spot-leaf smoke also
proves a checked local spot transition, then verifies that child receipt through
the recursive root. Neither smoke upgrades cross-shard or native-ledger
production claims.

Every child descriptor must bind:

```text
ChildDescriptorV1 {
  child_image_id
  child_verification_claim_hash
  child_journal_hash
  child_effect_summary_hash
  child_statement_hash
  child_verifier_id
  child_profile
}
```

The root guest must reject:

- child proof from the wrong chain;
- child proof from the wrong epoch or height range;
- child image ID absent from `verifier_set_root`;
- child receipt kind absent from allowed profile;
- duplicate child lane where uniqueness is required;
- missing child lane where the partition requires it;
- child journal digest mismatch;
- child effect summary hash mismatch;
- child policy, feature, dependency, or toolchain mismatch;
- unbalanced aggregate deltas;
- duplicated receipts or cross-shard messages;
- cross-shard messages that neither cancel nor carry forward exactly once.

## Effect Summary Contract

For recursive scaling, every leaf proof should commit a canonical
`EffectSummaryV1`.

```text
EffectSummaryV1 {
  summary_version
  lane_id
  lane_kind
  chain_id
  epoch_or_height_range
  proof_profile
  image_id
  statement_hash
  pre_state_root
  post_state_root
  tx_root
  evidence_root
  receipt_root
  accepted_receipts_root
  rejected_receipts_root
  asset_delta_root
  cross_shard_outbox_root
  cross_shard_inbox_root
  write_set_root
  public_policy_hash
  feature_suite_hash
  dependency_lock_hash
  toolchain_lock_hash
}
```

`EffectSummaryV1` is the composition object. It must have:

- canonical field order;
- append-only schema evolution;
- explicit zero-root semantics;
- sorted, unique leaf IDs;
- sorted, unique receipt IDs;
- sorted, unique message IDs;
- bounded row counts;
- no opaque host-only side conditions.

## Conservation And Authority

Use construction over cancellation when possible.

Preferred pattern:

```text
debit_atoms = sum(inputs consumed)
credit_atoms = deterministic output from transition
fee_atoms = deterministic residual with explicit recipient
```

Then verify:

```text
debit_atoms + authorized_mint_atoms
  = credit_atoms + authorized_burn_atoms
```

Mint, burn, slash, reward, or protocol-fee effects require an authority root and
lane-specific policy. Ordinary spot settlement should have zero mint and burn.

No circuit should hide value movement inside an untyped journal blob. Every
asset movement needs a row with units and authority.

## Reject-Is-No-Op

All verifier and admission rejects must be no-op at the committed state layer.

Implementation pattern:

```text
parse -> validate statement -> stage transition -> verify bindings -> commit
```

Rejects before commit return a typed reason and leave state unchanged.

Every new proof-admission path needs at least:

- one accept-invariant test;
- one reject-is-no-op test;
- one malformed-proof or malformed-journal test;
- one cross-domain replay test.

## Canonical Encoding And Schema Evolution

Canonical bytes are consensus-critical.

Rules:

- include a domain separator in every hash;
- sort rows by explicit stable keys;
- reject duplicate keys;
- reject unknown critical fields;
- keep schema evolution append-only;
- distinguish empty, absent, and zero root where semantics differ;
- never hash re-encoded ambiguous objects;
- use explicit integer widths and checked conversions;
- keep field names unit-bearing at boundaries, for example `_atoms`, `_bps`,
  `_hash`, `_epoch`, `_height`, `_image_id`.

Any field reorder, serialization change, or root-construction change requires a
version bump or an explicit compatibility theorem/test.

## Rust Implementation Rules

For `zk/state_proof_risc0/**`:

- use typed structs and enums for statements, journals, profiles, reject
  reasons, receipt kinds, and lane kinds;
- avoid stringly typed modes in production paths;
- prefer checked arithmetic for all amounts, counts, and offsets;
- avoid `unwrap` or `expect` in production verifier/guest/shared paths;
- return typed errors or stable reject strings where existing ABI requires
  strings;
- avoid implicit `Default` for critical statement fields;
- use `serde(default)` only for append-only compatibility fields with explicit
  validation;
- keep host-only helpers outside guest authority assumptions;
- keep shared semantics aligned with Python core through parity tests or
  explicit non-claims.

Guest functions should be small enough to audit locally. When a guest function
mixes parsing, validation, transition, and journal construction, split it into:

```text
parse_input
validate_statement
verify_witness
run_transition
build_journal
commit_journal
```

## Circuit Complexity Budget

These are review budgets, not automatic rejection rules:

| Surface | Budget |
| --- | --- |
| guest public entry | dispatch only plus one call per proof family |
| verifier helper | one invariant family per function |
| function length | prefer under 60 lines on critical paths |
| branching | prefer under 12 decision points per critical function |
| nesting | prefer depth at most 3 |
| verifier panic paths | none in host verifier or shared production logic |
| guest abort paths | explicit `risc0_zkvm::guest::abort` for invalid witness rejection |
| public roots | bounded and named |
| witness rows | bounded by statement |

Exceeding a budget requires an explanation in review and stronger focused
tests. It does not justify broad refactoring during unrelated work.

## Required Evidence Matrix

Every circuit, journal, verifier, or CLI parser behavior change needs evidence
from the relevant rows.

| Change type | Required evidence |
| --- | --- |
| statement schema | constructor reject tests, canonical hash fixture, unknown critical reject |
| journal schema | canonical journal hash fixture, metadata equality rejects |
| RISC0 image ID | wrong-image negative test, all-zero image ID reject |
| proof profile | wrong receipt kind reject, dev profile reject |
| guest witness check | mutation test that removes/inverts the check |
| asset deltas | conservation property or exhaustive bounded test |
| cross-shard messages | duplicate, missing, carry, and cancellation tests |
| recursive child verification | child substitution and child omission tests |
| CLI parser | malformed input, overflow, truncation, and unknown-mode tests |
| Python/Rust parity | shared fixture corpus or explicit non-claim |
| public claim update | claims registry or coverage matrix checker |

Use BDD-style scenario tests only for cross-layer user-visible behavior. For
proof correctness, prefer invariant-named unit/property/parity/mutation tests.

## Minimum Promotion Gate

Before a RISC0 circuit lane can be described as implemented, all of these must
hold:

1. Typed statement and journal are defined.
2. Production verifier rejects all-zero image IDs and placeholder methods.
3. Proof generation path verifies the produced receipt before emitting a report.
4. Admission verifier checks image ID, journal hash, proof profile, and metadata
   root equality.
5. Negative tests cover wrong image ID, wrong journal hash, wrong chain/config,
   wrong profile, stale verifier, malformed journal, and reject-is-no-op.
6. Python/Rust parity exists for any shared economic or settlement semantics.
7. Public docs name remaining gaps.

Before a recursive proof lane can be described as implemented, add:

1. Root guest verifies child receipts in guest.
2. Child verifier IDs are checked against `verifier_set_root`.
3. `EffectSummaryV1` composition checker exists outside the circuit.
4. Recursive root journal binds child verification-claim root, child journal
   root, and child summary root.
5. Negative tests cover omitted child, swapped child, duplicate receipt,
   duplicate message, unbalanced aggregate delta, missing DA root, and metadata
   drift.
6. At least one real proof smoke produces and verifies a root proof.

Before any production-ready claim, add:

1. Release manifest entry.
2. Claims registry update.
3. Public replay or smoke evidence with malformed-proof rejects.
4. Independent review of the circuit statement, journal, and verifier boundary.

## Implementation Workflow

Use this sequence for new RISC0 proof work:

1. Read `AGENTS.md`, `zk/AGENTS.md`, and this spec.
2. Define the typed statement, journal, reject reasons, and profile before guest
   code.
3. Implement a deterministic non-ZK checker for the statement.
4. Add constructor, canonicalization, and malformed-input tests.
5. Implement or update the guest.
6. Add real receipt verification in the host path.
7. Add proof metadata and admission checks.
8. Add negative tests and parity tests.
9. Run the narrow RISC0 gate:

```bash
cd zk/state_proof_risc0 && cargo test --all
cd zk/state_proof_risc0 && cargo clippy --all -- -D warnings
```

10. Run the relevant metadata or claims checker when public docs or proof
    profiles change.

## Review Checklist

Use this checklist before merging or promoting a circuit change:

- What is the exact typed statement?
- Which fields are public, private, committed, or irrelevant?
- Which private witness fields does the guest check?
- Which image ID is expected, and where is it bound?
- Which receipt profile is accepted?
- Which metadata roots must equal journal roots?
- What rejects are typed and stable?
- Is reject-is-no-op tested?
- Are all rows bounded?
- Are rows canonical, sorted, and duplicate-free?
- Is all arithmetic checked?
- Are public claims scoped to current evidence?
- Which disaster states remain possible, and what bounds them?

## Next Frontier

The highest-value implementation target is a deterministic
`EffectSummaryV1` / `RecursiveJournalV1` composition checker outside the circuit.
That checker should become the reference model for the future recursive guest.
