# FCIS M5-P4B5A B1B committed configuration authority: Revision 3.4

**Status:** `PROPOSED_REVIEW_ONLY_REVISION_3_4`

**Outcome:** `VALIDATE_CONFIGURATION_SEMANTICS_AND_SEPARATE_DECISION_PHASES`

**Authority:** This document authorizes no implementation, amendment, migration,
state binding, configuration update, receipt, proof, publication, or mount.
B1B-1 remains blocked until this revision passes independent review.

**Base:** Revision 3.3 at
`b86763850c1bc309a1cda1b67a6b3205ed22f758`.

Revision 3.4 is a normative amendment to Revision 3.3. Revision 3.3 remains in
force except where this document replaces the active-, proposed-, and
initial-configuration content pipelines; the candidate, decision, receipt, and
bundle dependency graph; rejection order; mutant inventory; pattern selection
record; and review gate. On conflict, Revision 3.4 controls.

## 1. Accepted Revision 3.3 findings

The focused ChatGPT review confirms that Revision 3.3 closes the three findings
it was written to address:

1. The authenticated configuration-update command commits the proposed
   configuration root.
2. Both publication branches consume the independently pinned deployment
   verifier, and mixed state/bundle families reject.
3. `TransitionCauseV2` contains no `decision_hash`.

The Revision 3.2 exact-pre-state header correction also remains closed.

The review found one remaining P1 content-validation gap and one P2 phase-DAG
contradiction.

### 1.1 Structurally admitted content is not semantically validated

Revision 3.3 performs:

```text
untrusted proposed content
  -> closed admission and fresh ownership
  -> canonical root recomputation
  -> authenticated command-root equality
  -> update laws
```

It does not require the admitted claim to pass the frozen B1A validator before
the root enters committed state.

The minimized witness is a structurally valid body with:

```text
algorithm_version = OTHER_ALGORITHM
```

An authenticated command can commit that body's exact canonical root. All
Revision 3.3 deployment, domain, version, activation, and root equations pass.
B1A rejects the claim with:

```text
ALGORITHM_VERSION_MISMATCH
```

Equivalent witnesses use the wrong accepted language, a mismatched policy root,
a mismatched embedded configuration root, or hostile mutation after validation.

### 1.2 Candidate and receipt form a cycle

Revision 3.3 places `receipt` inside `V2TransitionCandidate` while its dependency
graph derives the receipt from the complete candidate:

```text
receipt -> candidate -> receipt
```

The current FCIS V1 source uses the acyclic phase split:

```text
evaluation candidate without receipt
  -> controlled decision containing receipt
  -> commit bundle containing one decision
```

Both findings are accepted.

## 2. Preflight and authority map

### 2.1 Exact affected artifacts

This checkpoint changes documentation only:

```text
FCIS_M5_P4B5A_B1B_COMMITTED_CONFIGURATION_AUTHORITY_REVISION_3_4_20260729.md
FCIS_M5_P4B5A_B1B_REVISION_3_3_CHATGPT_ADJUDICATION_20260729.md
focused Revision 3.4 review packet
```

No Python, Rust, state, runtime, migration, command, receipt, proof, or shell
file changes.

### 2.2 Exact existing B1A boundary

The frozen B1A implementation separates:

```text
fcis_fee_distribution_configuration_admission.admit
  -> FeeDistributionConfigurationClaimV2

validate_fee_distribution_configuration_claim_v2
  -> FeeDistributionConfigurationVerificationRejectV2
   | ValidatedFeeDistributionConfigurationClaimV2

revalidate_fee_distribution_configuration_claim_v2
  -> bool
```

Admission owns exact source structure and canonical form. Validation enforces:

```text
algorithm_version =
  SRGD_ALGORITHM_VERSION_V1

accepted_language_version =
  PROVISIONAL_FEE_ACCEPTED_LANGUAGE_VERSION_V2

body.policy_root =
  canonical_fee_distribution_policy_root_v2(body.policy)

claim.configuration_root =
  canonical_fee_distribution_configuration_root_v2(body)
```

`ValidatedFeeDistributionConfigurationClaimV2` is controlled evidence of B1A
self-consistency. It explicitly carries no protocol authority.

### 2.3 Authority owners

| Fact | Independent source |
|---|---|
| Local deployment and expected migration manifest | Pinned deployment verifier |
| Current state and active configuration root | Store-current exact state |
| Proposed configuration root | Freshly reauthenticated update command |
| Initial migration configuration root | Pinned and verified migration manifest |
| Configuration semantic validity | Frozen B1A validator |
| Consensus facts | Independently authenticated publication context |
| Currentness and atomicity | Store-current publication operation |

The B1A validator decides whether a claim belongs to the frozen configuration
language. The state, command, or migration manifest decides which valid
configuration is authoritative for that transition.

### 2.4 Owned values and alias boundary

Every content path starts from untrusted bytes or an untrusted source
projection. It must:

1. decode with full input consumption;
2. pass the closed B1A admission registry;
3. construct fresh exact owned values;
4. pass B1A semantic validation;
5. pass point-of-use revalidation before any authority-bearing field read.

`frozen=True`, a private construction token, and a self-consistent root do not
individually establish ownership or authority. Publication repeats the complete
pipeline from independent sources.

### 2.5 Failure and commit model

Any decode, admission, B1A validation, root, source-binding, update-law, or
phase-DAG failure returns a typed rejection with:

```text
no successor
no patch
no effect
no receipt
no replay update
no outbox
no publication authority
```

Committed failure remains a distinct later variant with an explicit successor
and exact allowed authoritative changes.

Crash recovery, datastore linearizability, and external delivery remain outside
this review-only checkpoint.

## 3. Closed admit, validate, and bind pipeline

### 3.1 One semantic content function

Later checkpoints must implement one controlled semantic function with this
contract:

```text
admit_and_validate_fee_distribution_configuration_v2(
    untrusted_content_source:
      UntrustedConfigurationContentV2,
    validated_admission_limits:
      ValidatedAdmissionLimitsV1,
)
  -> ConfigurationContentRejectV2
   | ValidatedFeeDistributionConfigurationClaimV2
```

This name describes a required semantic phase. It does not authorize a second
validator. Its implementation must compose the frozen B1A admission and
validation functions.

Normative expansion:

```text
decoded_source =
  decode_canonical_configuration_claim_and_fully_consume_v2(
    untrusted_content_source
  )

admitted =
  fcis_fee_distribution_configuration_admission.admit(
    FEE_DISTRIBUTION_CONFIGURATION_SCHEMA_REVISION_V2,
    FEE_DISTRIBUTION_CONFIGURATION_CLAIM_SCHEMA_ID_V2,
    validated_admission_limits,
    decoded_source,
  )

require admitted is exact AdmitOk
require admitted.value is exact FeeDistributionConfigurationClaimV2

validated =
  validate_fee_distribution_configuration_claim_v2(
    admitted.value
  )

require validated is exact
  ValidatedFeeDistributionConfigurationClaimV2

require
  revalidate_fee_distribution_configuration_claim_v2(
    validated
  )
```

If the content source is already a bounded untrusted projection rather than
bytes, the byte-decoding phase belongs to the preceding canonical ingress
boundary. No source projection may bypass the same admission and validation
functions.

### 3.2 Root equality after semantic validation

For every validated configuration:

```text
recomputed_root =
  canonical_fee_distribution_configuration_root_v2(
    validated.body
  )

require validated.configuration_root = recomputed_root
```

This equality repeats the load-bearing B1A result at the authority boundary. A
consumer must not substitute a root copied from content metadata, a resolver,
the shell, or the bundle.

### 3.3 No admission-to-authority conversion

These values remain non-authoritative:

```text
decoded source
admission source
FeeDistributionConfigurationClaimV2
canonical body bytes
recomputed body root
ValidatedFeeDistributionConfigurationClaimV2 by itself
```

An admitted claim cannot be cast, wrapped, sealed, or copied into the validated
type. Only the B1A validator constructs the exact validated type.

The validated type becomes usable in an authority relation only after equality
with an independent expected root:

```text
active path:
  expected root from exact pre-state

proposed path:
  expected root from freshly authenticated command

initial migration path:
  expected root from pinned verified manifest
```

## 4. Active configuration path

For any V2 transition whose support profile declares an active
fee-configuration read:

```text
validated_active =
  admit_and_validate_fee_distribution_configuration_v2(
    active_content_source,
    validated_admission_limits,
  )

require
  revalidate_fee_distribution_configuration_claim_v2(
    validated_active
  )

active =
  bind_fee_configuration_to_state_v2(
    exact_pre_state,
    validated_active,
  )
```

The binder must freshly require:

```text
validated_active.configuration_root =
  canonical_fee_distribution_configuration_root_v2(
    validated_active.body
  )

validated_active.configuration_root =
  exact_pre_state.authority_header
    .fee_distribution_configuration_root

validated_active.body.chain_deployment_id =
  exact_pre_state.authority_header.chain_deployment_id

validated_active.body.activation_sequence <=
  exact_pre_state.authority_header.sequence
```

The resulting `StateBoundFeeDistributionConfigurationV2` means:

> This B1A-valid configuration is committed by this exact pre-state.

It does not mean that the pre-state is store-current. Every later
authority-bearing use rebinds from the same exact pre-state. Publication rebinds
from the store-current exact state.

## 5. Proposed configuration path

### 5.1 Source-bound update signature

The configuration-update relation retains Revision 3.3's source shape:

```text
derive_configuration_update_v2(
    exact_pre_state: FCISCommittedStateV2,
    reauthenticated_update_command:
      AuthenticatedConfigurationUpdateCommandV2,
    exact_consensus_context:
      AuthenticatedFCISConsensusContextV2,
    active_content_source:
      UntrustedConfigurationContentV2,
    proposed_content_source:
      UntrustedConfigurationContentV2,
)
  -> ConfigurationUpdateRejectV2
   | V2EvaluationCandidate
```

The command's canonical authenticated bytes contain:

```text
proposed_fee_distribution_configuration_root
```

No shell, bundle, resolver, archive, or content object supplies the expected
proposed root independently.

### 5.2 Active and proposed semantic validation

The core performs:

```text
validated_active =
  admit_and_validate_fee_distribution_configuration_v2(
    active_content_source,
    validated_admission_limits,
  )

active =
  bind_fee_configuration_to_state_v2(
    exact_pre_state,
    validated_active,
  )

validated_proposed =
  admit_and_validate_fee_distribution_configuration_v2(
    proposed_content_source,
    validated_admission_limits,
  )

require
  revalidate_fee_distribution_configuration_claim_v2(
    validated_proposed
  )

proposed_root =
  canonical_fee_distribution_configuration_root_v2(
    validated_proposed.body
  )
```

It then requires the three-way equality:

```text
validated_proposed.configuration_root
  = proposed_root

proposed_root
  = reauthenticated_update_command
      .proposed_fee_distribution_configuration_root
```

The update law reads only:

```text
active.validated_configuration_claim.body
validated_proposed.body
```

It must not read an admitted claim, decoded mapping, source object, resolver
metadata, or bundle copy.

### 5.3 Configuration-update laws

After semantic validation and root binding:

```text
pre_header = exact_pre_state.authority_header
active_body = active.validated_configuration_claim.body
proposed_body = validated_proposed.body

require pre_header.sequence < U256_MAX
require active_body.configuration_version < U256_MAX

require proposed_body.chain_deployment_id =
  pre_header.chain_deployment_id

require proposed_body.fee_distribution_domain_id =
  active_body.fee_distribution_domain_id

require proposed_body.configuration_version =
  checked_add_u256(active_body.configuration_version, 1)

require proposed_body.activation_sequence =
  checked_add_u256(pre_header.sequence, 1)
```

The complete successor derives:

```text
post_state.authority_header.chain_deployment_id =
  pre_header.chain_deployment_id

post_state.authority_header.sequence =
  checked_add_u256(pre_header.sequence, 1)

post_state.authority_header
  .fee_distribution_configuration_root =
  proposed_root
```

The update is configuration-only. It cannot compose with fee-bearing
settlement. Balances, pools, LP balances, nonces, vault, oracle,
fee-apportionment deficits, and perps remain byte- and value-identical.

Ordinary weight, destination, and policy rotation remains permitted. It
preserves the stable distribution-domain ID and exact fee-apportionment state.
Domain creation, domain-ID rotation, split, merge, retirement, and reuse remain
outside the initial V2 command language.

## 6. Initial migration configuration path

Migration publication retains the independently pinned verifier and
store-current exact V1 state from Revision 3.3.

Before migration laws can read the initial configuration:

```text
validated_initial =
  admit_and_validate_fee_distribution_configuration_v2(
    initial_configuration_content_source,
    validated_admission_limits,
  )

require
  revalidate_fee_distribution_configuration_claim_v2(
    validated_initial
  )

initial_root =
  canonical_fee_distribution_configuration_root_v2(
    validated_initial.body
  )

require validated_initial.configuration_root =
  initial_root

require initial_root =
  verified_manifest.expected_initial_configuration_root
```

The source-bound migration relation then requires:

```text
verified manifest root =
  pinned verifier expected manifest root

verified manifest deployment =
  pinned verifier expected deployment

validated initial deployment =
  verified manifest deployment

validated initial domain =
  verified manifest fee-distribution domain

validated initial version = 1
validated initial activation sequence = 0
initial V2 authority-header sequence = 0
```

The exact V1-to-V2 namespace projection from Revision 3.2 remains unchanged.
Merely admitted initial content cannot create a migration candidate.

## 7. Acyclic evaluation, decision, receipt, and bundle phases

### 7.1 Upstream transition cause

Revision 3.3's cause remains:

```text
TransitionCauseV2(
    pre_state_root,
    command_hash,
    consensus_context_hash,
    accepted_language_version,
    transition_kind,
)
```

Its fields derive from the exact pre-state, freshly authenticated command, and
independently authenticated consensus context before evaluation-candidate
construction.

The cause contains no candidate, post-state, decision, receipt, bundle, proof,
or hash whose projection includes the cause.

### 7.2 Receipt-free evaluation candidate

The complete non-migration core produces:

```text
V2EvaluationCandidate(
    post_state,
    canonical_patch,
    effects,
    replay_update,
    transition_cause,
)
```

The candidate contains no:

```text
receipt
receipt root
decision
decision root
bundle
bundle root
outbox plan
proof input
```

Its exact controlled constructor retains one immutable lineage from the exact
pre-state, command, context, required content, and deterministic outputs. The
same-lineage inputs may be retained in an enclosing evaluated-material value,
following `FCISEvaluatedMaterialV1`.

### 7.3 Receipt and decision

After the evaluation candidate is complete:

```text
receipt =
  derive_v2_receipt(
    evaluation_candidate,
    exact_receipt_inputs,
  )

decision =
  derive_v2_decision(
    evaluation_candidate,
    receipt,
  )
```

The accepted or committed-failure decision owns one exact candidate and one
exact receipt:

```text
V2Decision(
    evaluation_candidate,
    receipt,
)
```

Ordinary rejection has no evaluation candidate and no committable output. Its
later rejection receipt derives from typed rejection evidence and remains
non-committable unless the protocol defines a distinct committed-failure
variant.

The receipt preimage may include a hash of the receipt-free evaluation
candidate. It must exclude:

```text
the receipt itself
the receipt-bearing decision
the bundle
the outbox plan
proof outputs
any aggregate whose projection includes the receipt
```

The exact receipt schema, root domain, and projection remain later-checkpoint
obligations.

### 7.4 Commit bundle

The bundle retains one nested decision:

```text
V2CommitBundle(
    decision,
    outbox_plan,
)
```

It does not independently copy the candidate's post-state, patch, effects,
replay update, cause, receipt, or configuration lineage.

The outbox plan derives after the decision and receipt. The bundle builder
recomputes every root from the nested decision and exact outbox plan.

### 7.5 Complete dependency order

The normative order is:

```text
exact pre-state
freshly authenticated command
independently authenticated context
validated and source-bound required content
  -> transition cause
  -> deterministic transition outputs
  -> receipt-free evaluation candidate
  -> receipt
  -> decision
  -> outbox plan
  -> commit bundle
  -> proof input or publication equality target
```

Every edge points downstream. No root or hash may depend on an aggregate that
contains the value being hashed.

## 8. Publication rederivation

Revision 3.3's closed dispatch remains:

```text
store-current exact V1 + migration bundle
  -> eligible migration branch

store-current exact V2 + non-migration V2 bundle
  -> eligible V2 branch

every mixed or unknown family
  -> reject
```

### 8.1 Migration publication

Inside the atomic operation, publication:

1. loads the store-current exact V1 state;
2. validates the state/bundle family;
3. consumes the pinned deployment verifier;
4. admits and B1A-validates the initial configuration;
5. reruns the source-bound V1-to-V2 migration;
6. derives the migration receipt, decision, outbox, and bundle in their declared
   order;
7. requires complete equality with the submitted bundle;
8. commits the rederived tuple once.

A bundle-carried V1 state, expected manifest root, decoded anchor claim, or
merely admitted configuration is never an authority source.

### 8.2 Non-migration V2 publication

Inside the atomic operation, publication:

1. loads the store-current exact V2 state;
2. requires its deployment ID to equal the pinned deployment ID;
3. recomputes its current state root;
4. freshly reauthenticates command and consensus context;
5. derives the command-specific required-content profile;
6. admits and B1A-validates every required configuration;
7. rebinds active configuration content to the store-current exact state;
8. binds proposed content to the freshly authenticated command when applicable;
9. rederives the receipt-free evaluation candidate;
10. rederives the receipt, decision, outbox plan, and commit bundle;
11. requires complete equality with the submitted bundle;
12. commits the rederived tuple once.

The submitted bundle supplies equality targets and replayable content. It does
not supply current state, local deployment, expected roots, semantic validity,
command authentication, or consensus authority.

## 9. Rejection order

Revision 3.4 freezes the phase order, while stable public reject codes remain a
later checkpoint.

### 9.1 Configuration-content phase

```text
1. byte decoding and full consumption
2. closed structural admission
3. B1A semantic validation
   a. algorithm-version equality
   b. accepted-language-version equality
   c. policy-root equality
   d. configuration-root equality
4. point-of-use exact-type revalidation
5. authoritative expected-root comparison
6. deployment/domain/version/activation laws
```

### 9.2 Complete non-migration phase

```text
exact state/bundle family
  -> pinned deployment comparison
  -> current V2 root
  -> command and context authentication
  -> required-content profile
  -> configuration-content phase
  -> deterministic transition
  -> evaluation candidate
  -> receipt and decision
  -> outbox and bundle
  -> complete equality
  -> one atomic publication
```

### 9.3 Migration phase

```text
exact state/bundle family
  -> current V1 root
  -> pinned manifest and deployment comparison
  -> initial configuration-content phase
  -> migration laws and namespace projection
  -> migration evaluation candidate
  -> receipt and decision
  -> outbox and bundle
  -> complete equality
  -> one atomic publication
```

If several failures exist, the earliest phase wins. Within B1A semantic
validation, the existing implemented order controls:

```text
algorithm
accepted language
policy root
configuration root
```

## 10. Required architecture and mutation evidence

### 10.1 Semantic-validation mutants

Permanent mutants:

```text
command authenticates the root of a body using OTHER_ALGORITHM
command authenticates the root of a body using another accepted language
body embeds a wrong policy root and recomputes the outer configuration root
claim embeds H_MALLORY while its body recomputes to command-bound H_GOOD
update reads proposed body before B1A validation
admission result is treated as ValidatedFeeDistributionConfigurationClaimV2
validator call is deleted while command-root equality remains
validated proposed claim is mutated before update-law evaluation
active content is admitted but not B1A-validated
migration initial content is admitted but not B1A-validated
```

Each mutant preserves valid field types and recomputes unrelated outer hashes.
The semantic validator, revalidator, or independent expected-root comparison
must kill it.

### 10.2 Dependency-DAG mutants

Permanent mutants:

```text
evaluation candidate contains a receipt
evaluation candidate contains a receipt root
receipt projection includes the receipt-bearing decision
receipt projection includes the commit bundle
decision copies candidate fields outside its nested candidate
bundle copies candidate or receipt fields outside its nested decision
outbox plan is derived before the receipt it binds
transition cause regains a downstream decision or candidate hash
```

The DAG checker must reject cycles and independently swappable copies.

### 10.3 Retained source-binding mutants

All prior mutants remain:

```text
same authenticated command accepts two proposed roots
command commits H_GOOD while content hashes to H_MALLORY
shell or bundle supplies an expected proposed root
local pin B accepts store-current V2 state A
migration publication ignores the pin
migration publication uses bundle-carried V1 state
ordinary transition uses a loose pre-header
state-bound configuration is accepted without exact-state rebinding
mixed state/bundle families dispatch through an eligible branch
```

### 10.4 Required BDD scenarios

```text
Given an authenticated update command committing the exact root of a body
And the body uses OTHER_ALGORITHM
When the proposed content pipeline runs
Then B1A rejects before root authority or successor derivation

Given a body with a wrong policy root
And its outer configuration root is recomputed
When the proposed content pipeline runs
Then B1A rejects at policy-root equality

Given a B1A-valid proposed claim
When its nested policy is mutated before update-law evaluation
Then point-of-use revalidation rejects with no successor

Given a B1A-valid initial configuration matching the pinned manifest
When migration publication runs
Then the validated claim enters the source-bound migration relation

Given an admitted but B1A-invalid initial configuration
When migration publication runs
Then migration rejects before candidate derivation

Given one receipt-free evaluation candidate
When receipt, decision, outbox, and bundle are derived
Then the dependency graph is acyclic and every downstream aggregate retains one
nested lineage
```

### 10.5 Formal and bounded obligations

A later bounded model must include:

```text
admitted valid and admitted semantically invalid configurations
algorithm, language, policy-root, and configuration-root substitutions
post-validation mutation
active, proposed, and initial-migration content roles
receipt-free evaluation candidate
receipt, decision, outbox, and bundle dependency nodes
cycle search over every declared root projection
```

The model establishes determinism only after semantic validation, independent
root authority, source rebinding, and an acyclic phase DAG are included.

## 11. B1B-1 scope remains unchanged

The permitted B1B-1 scope remains:

```text
FCISAuthorityHeaderV2
DeploymentBootstrapAnchorClaimV2
V1ToV2MigrationManifestV2
closed schemas and field registries
canonical Python/Rust codecs and roots
shared positive and negative vectors
limited structural-checker coverage
```

B1B-1 must not implement:

```text
ConfigurationUpdateCommandClaimV2
AuthenticatedConfigurationUpdateCommandV2
PinnedDeploymentBootstrapVerifierV2
V1ToV2MigrationCandidateV2
FCISCommittedStateV2
StateBoundFeeDistributionConfigurationV2
TransitionCauseV2
V2EvaluationCandidate
V2Decision
V2CommitBundle
successor-producing transition
configuration update
receipt
outbox plan
proof input
publication
runtime mount
```

The B1B-1 checker must reject:

```text
any function advancing or updating a bare FCISAuthorityHeaderV2
any generic authority-header patch or write atom
any public conversion from an anchor claim to a pinned verifier
any premature command, validated-authority, state, transition, decision,
receipt, bundle, proof, publication, or mount type
```

The three B1B-1 carrier field sets do not change in Revision 3.4.

## 12. Pattern selection record

### 12.1 Domain schema and invariant relationship

The B1A validator owns configuration-language self-consistency. The exact
pre-state owns the active root. The authenticated update command owns the
proposed root. The pinned manifest owns the initial root. Publication composes
these independent facts with currentness.

The evaluation candidate owns deterministic transition outputs. The decision
introduces the receipt. The bundle introduces the outbox and atomic publication
envelope.

### 12.2 Selected construction

```text
closed source admission
+ controlled B1A semantic validation
+ independent expected-root binding
+ exact-state whole-transition derivation
+ receipt-free evaluation candidate
+ receipt-bearing controlled decision
+ one nested-decision commit bundle
+ closed pinned publication dispatch
```

### 12.3 Rejected alternatives

- Structural admission alone accepts unsupported algorithms and languages.
- Root equality alone proves content identity, not membership in the frozen
  semantic language.
- A validated claim alone proves self-consistency, not state or command
  authority.
- A receipt inside its own prerequisite candidate creates a dependency cycle.
- Copying candidate fields into the decision or bundle creates substitution
  checks and independently swappable lineage.
- A bundle-carried expected root or state proves only bundle
  self-consistency.

### 12.4 Mechanical guarantees

- Every active, proposed, and initial configuration belongs to the frozen B1A
  language before an authority relation reads it.
- The expected root comes from exactly one independent authority source for
  each content role.
- Hostile post-validation mutation is detected at every authority-bearing use.
- Unsupported configuration content cannot enter the successor header.
- The object and hash dependency graph is acyclic.
- The receipt is downstream of, and bound to, one receipt-free evaluation
  candidate.
- The bundle retains one decision lineage and publishes atomically.

### 12.5 Explicit non-guarantees

This construction does not determine governance authorization, bootstrap-pin
distribution, datastore linearizability, crash recovery, content availability,
proof-system soundness, or mounted runtime behavior.

### 12.6 Trusted constructors and boundaries

```text
B1A admission registry
B1A semantic validator
state binder that consumes exact pre-state
command authenticator that owns proposed root
pinned migration verifier
controlled evaluation-candidate builder
controlled decision/receipt builder
controlled bundle builder
atomic publication port
```

Public carrier, claim, canonical-byte, root, source, and content values are not
authority constructors.

### 12.7 Staleness, aliasing, concurrency, and crash witnesses

- A stale evaluation candidate fails store-current rederivation and root
  equality.
- A mutated validated claim fails point-of-use B1A revalidation.
- Competing configuration updates race on one pre-root and sequence.
- Missing content fails closed before semantic evaluation.
- Crash behavior remains a later atomic-shell obligation.

### 12.8 Python and Rust enforcement plan

Later implementations require exact dataclasses/newtypes, exact integer types,
closed field registries, controlled construction tokens, checked U256
arithmetic, transitively owned values, canonical bytes, and shared
Python/Rust vectors.

The Rust path must mirror B1A's exact semantic checks. Decoder and validator
parity must cover rejection phase and precedence, not only accepted bytes.

### 12.9 Serialization, replay, and migration implications

Every configuration-consuming published bundle retains the exact canonical
validated-claim bytes used during rederivation. The state header remains the
authoritative content pointer. An immutable content-addressed archive supplies
availability only.

The evaluation-candidate codec excludes receipts. Receipt, decision, and bundle
codecs each receive separate schemas and domain separators at their later
checkpoints.

### 12.10 Evidence hooks

Required evidence includes B1A semantic substitution tests, hostile-mutation
tests, Python/Rust rejection parity, dependency-DAG checks, requirement-linked
mutants, bounded state/bundle dispatch, store-current stateful tests, and
crash/CAS/outbox tests at their owning checkpoints.

## 13. Non-claims

Revision 3.4 does not claim:

- implementation of any relation in this document;
- completion of an exact configuration-content byte decoder;
- political, legal, or governance authorization for the bootstrap pin;
- governance authority over configuration updates;
- authenticated command-schema implementation;
- secure release distribution of the pinned verifier;
- security after verifier-code or datastore-implementation replacement;
- production datastore linearizability or crash recovery;
- content-cache availability;
- mounted migration, update, settlement, proof, or publication;
- whole-system Python/Rust parity;
- a machine-checked proof of the complete composition relation.

## 14. Review gate and next checkpoint

Revision 3.4 must receive focused independent approval before B1B-1 begins.

The exact approval verdict is:

```text
APPROVE_B1B1_REVISION_3_4_UNMOUNTED
```

After approval, B1B-1 remains limited to the unchanged untrusted authority
header, bootstrap-anchor-claim, and migration-manifest carriers; their schemas;
canonical Python/Rust codecs and roots; shared vectors; and limited structural
checker coverage.
