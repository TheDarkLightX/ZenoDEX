# FCIS M5-P4B5A B1B committed configuration authority: Revision 3.4

**Status:** `UNMOUNTED_IMPLEMENTATION_CANDIDATE_REVISION_3_4`

**Outcome:** `VALIDATE_BEFORE_ROOT_AUTHORITY_AND_SEPARATE_RECEIPT_PHASE`

**Base:** Revision 3.3 at
`b86763850c1bc309a1cda1b67a6b3205ed22f758`.

**Accepted review:**
`FCIS_M5_P4B5A_B1B_REVISION_3_3_CHATGPT_ADJUDICATION_20260729.md`.

**Authority:** This document and its B1B-1 implementation construct only
untrusted canonical carriers, codecs, audit roots, vectors, and structural
evidence. They authorize no pinned verifier, migration authority, committed V2
state, state-bound configuration, configuration update, value movement,
receipt, bundle, proof input, publication, datastore operation, or runtime
mount.

Revision 3.4 is a normative amendment to Revision 3.3. Revision 3.3 remains in
force except where this document replaces the active/proposed configuration
content pipeline, migration initial-content pipeline, rejection precedence,
candidate/receipt dependency graph, mutant inventory, and B1B-1 implementation
gate. On conflict, Revision 3.4 controls.

## 1. Result

Revision 3.3 closed command-to-content root substitution and publication
source continuity. It still allowed a command-authenticated root to become the
active state pointer after only structural admission of the corresponding
configuration body.

That is insufficient because B1A deliberately separates:

```text
structurally exact claim
  from
semantically validated configuration claim
```

A structurally exact claim may carry a wrong algorithm version, wrong
accepted-language version, wrong policy root, or wrong embedded configuration
root. Hashing that body and authenticating its hash does not make the body a
valid protocol configuration.

Revision 3.4 adopts one total deterministic content pipeline:

```text
untrusted canonical bytes
  -> full-consumption decoding
  -> closed structural admission
  -> B1A semantic validation
  -> defensive point-of-use revalidation
  -> exact root recomputation
  -> embedded-root equality
  -> independent authority-root equality
  -> transition-specific laws
```

It also separates the pre-receipt evaluation candidate from the receipt-bearing
decision. No canonical object contains a digest whose projection recursively
contains that object.

## 2. Authority-source map

| Fact | Independent source retained at use |
|---|---|
| Active configuration identity | Exact pre-state authority header |
| Proposed configuration identity | Freshly authenticated update command |
| Initial configuration identity | Point-of-use verified migration manifest |
| Configuration meaning | Exact admitted body accepted by B1A validation |
| Local deployment identity | Pinned deployment verifier |
| Current state | Exact state loaded inside atomic publication |
| Consensus context | Independently authenticated step/publication context |
| Receipt statement | Pre-receipt evaluation candidate and exact decision kind |

No shell, content resolver, archive, peer, file, cache, decoded claim, bundle,
or candidate may supply an expected semantic root independently.

## 3. Exact configuration-content pipeline

The same helper relation is used for active, proposed, and initial migration
content:

```text
admit_and_validate_fee_configuration_content_v2(
    canonical_content_bytes: ExactBytes,
)
  -> ConfigurationContentRejectV2
   | ValidatedFeeDistributionConfigurationClaimV2
```

The relation performs, in order:

```text
1. require exact bounded bytes
2. decode one complete canonical configuration-claim envelope
3. reject duplicate, unknown, missing, trailing, or noncanonical fields
4. closed structural admission into FeeDistributionConfigurationClaimV2
5. call validate_fee_distribution_configuration_claim_v2
6. require exact ValidatedFeeDistributionConfigurationClaimV2
7. call revalidate_fee_distribution_configuration_claim_v2
8. reconstruct one freshly owned policy, body, and claim field by field
9. recompute policy_root from the freshly owned policy
10. require embedded policy_root = recomputed policy_root
11. recompute configuration_root from the freshly owned body
12. require embedded claim.configuration_root = recomputed configuration_root
```

The controlled validated result remains non-authoritative by itself. Authority
arises only from a later equality with an independent expected root.

No transition may read `FeeDistributionConfigurationClaimV2.body` before step
6 succeeds. An admission result is never treated as a validated result through
a cast, alias, wrapper, Boolean flag, seal bit, or constructor token copied from
another value.

### 3.1 Defensive ownership

Python hostile in-process mutation remains in scope. Every authority use:

- reruns B1A semantic validation;
- reconstructs nested policy/body/claim values field by field;
- recomputes both roots;
- compares complete canonical bytes.

Rust uses private fields and owned values but performs the same semantic checks
and rejection precedence. Language privacy is a misuse barrier; semantic
recomputation is the authority check.

## 4. Active configuration binding

For an ordinary fee-bearing transition or configuration update:

```text
validated_active =
  admit_and_validate_fee_configuration_content_v2(
    untrusted_active_content_bytes
  )

state_bound_active =
  bind_fee_configuration_to_state_v2(
    exact_pre_state,
    validated_active,
  )
```

The binder freshly requires:

```text
validated_active.configuration_root =
  recomputed_configuration_root(validated_active.body)

validated_active.configuration_root =
  exact_pre_state.authority_header
    .fee_distribution_configuration_root

validated_active.body.chain_deployment_id =
  exact_pre_state.authority_header.chain_deployment_id

validated_active.body.activation_sequence <=
  exact_pre_state.authority_header.sequence
```

A body valid under another exact state, deployment, root, or activation point
cannot become active authority.

## 5. Proposed configuration update

The authenticated command owns:

```text
proposed_fee_distribution_configuration_root: Digest32
```

The exact pre-state owns the active root. Content sources provide bytes only.

The update relation is:

```text
derive_configuration_update_v2(
    exact_pre_state: FCISCommittedStateV2,
    reauthenticated_update_command:
      AuthenticatedConfigurationUpdateCommandV2,
    exact_consensus_context:
      AuthenticatedFCISConsensusContextV2,
    untrusted_active_content_bytes: ExactBytes,
    untrusted_proposed_content_bytes: ExactBytes,
)
  -> ConfigurationUpdateRejectV2
   | V2EvaluationCandidate
```

It derives:

```text
active =
  bind exact-pre-state authority to
  admit_and_validate_fee_configuration_content_v2(active bytes)

validated_proposed =
  admit_and_validate_fee_configuration_content_v2(proposed bytes)

proposed_root =
  recompute_configuration_root(validated_proposed.body)
```

and requires the exact three-way equality:

```text
validated_proposed.configuration_root
  = proposed_root
  = reauthenticated_update_command
      .proposed_fee_distribution_configuration_root
```

Only after all three values are equal may the core evaluate:

```text
pre_header = exact_pre_state.authority_header
active_body = active.validated_configuration_claim.body
proposed_body = validated_proposed.body

pre_header.sequence < U256_MAX
active_body.configuration_version < U256_MAX

proposed_body.chain_deployment_id =
  pre_header.chain_deployment_id

proposed_body.fee_distribution_domain_id =
  active_body.fee_distribution_domain_id

proposed_body.configuration_version =
  checked_add_u256(active_body.configuration_version, 1)

proposed_body.activation_sequence =
  checked_add_u256(pre_header.sequence, 1)
```

The successor root is not independently copied:

```text
post_state.authority_header
  .fee_distribution_configuration_root = proposed_root
```

The update is configuration-only. Balances, pools, LP balances, nonces, vault,
oracle, fee-apportionment state, and perps remain byte- and value-identical. It
cannot compose with a fee-bearing settlement.

One authenticated command root therefore identifies at most one canonical and
B1A-valid configuration body, assuming the SHA-256 collision-resistance premise.

## 6. Initial migration configuration

The V1-to-V2 migration branch uses the same content helper:

```text
validated_initial_configuration =
  admit_and_validate_fee_configuration_content_v2(
    submitted_bundle.untrusted_initial_configuration_bytes
  )
```

The source-bound migration relation then requires:

```text
validated_initial_configuration.configuration_root =
  verified_manifest.expected_initial_configuration_root

validated_initial_configuration.body.chain_deployment_id =
  verified_manifest.chain_deployment_id

validated_initial_configuration.body.fee_distribution_domain_id =
  verified_manifest.fee_distribution_domain_id

validated_initial_configuration.body.configuration_version = 1
validated_initial_configuration.body.activation_sequence = 0
```

A structurally exact but semantically invalid initial body cannot become the
first active V2 configuration even when its root appears in a caller-supplied
manifest. The independently pinned manifest root and B1A validation are both
required.

## 7. Stable rejection precedence

The content/update pipeline uses this closed phase order:

```text
1. CONTENT_BYTE_LIMIT
2. CONTENT_INVALID_UTF8
3. CONTENT_INVALID_CANONICAL_JSON
4. CONTENT_DUPLICATE_FIELD
5. CONTENT_UNKNOWN_OR_MISSING_FIELD
6. CONTENT_STRUCTURAL_ADMISSION_FAILED
7. ALGORITHM_VERSION_MISMATCH
8. ACCEPTED_LANGUAGE_VERSION_MISMATCH
9. POLICY_ROOT_MISMATCH
10. CONFIGURATION_ROOT_MISMATCH
11. EXPECTED_CONFIGURATION_ROOT_MISMATCH
12. ACTIVE_STATE_BINDING_FAILED
13. SEQUENCE_EXHAUSTED
14. CONFIGURATION_VERSION_EXHAUSTED
15. CONFIGURATION_UPDATE_LAW_FAILED
16. COMPLETE_CANDIDATE_RELATION_FAILED
```

The first applicable failure wins. No successor, patch, effect, replay update,
receipt, decision, bundle, proof input, outbox, or publication authority exists
after rejection.

When active and proposed content are both required, active content is admitted,
validated, and state-bound before proposed content is admitted and validated.
This makes a corrupted current authority visible before an unrelated proposed
body error.

## 8. Acyclic evaluation, receipt, decision, and bundle graph

Revision 3.4 uses four distinct phases.

### 8.1 Transition cause

```text
TransitionCauseV2(
    pre_state_root,
    command_hash,
    consensus_context_hash,
    accepted_language_version,
    transition_kind,
)
```

Every field derives before evaluation output. The cause contains no decision,
candidate, post-state, receipt, bundle, proof, or downstream hash.

### 8.2 Pre-receipt evaluation candidate

```text
V2EvaluationCandidate(
    post_state,
    canonical_patch,
    effects,
    replay_update,
    transition_cause,
)
```

`V2EvaluationCandidate` contains no receipt, decision, bundle, outbox, or any
root whose preimage contains the candidate itself.

Its root is:

```text
evaluation_candidate_root =
  sha256(
    domain_sep("fcis_v2_evaluation_candidate", version=2)
    || canonical_evaluation_candidate_envelope_v2
  )
```

### 8.3 Receipt and decision

The receipt binds the already-computed candidate root:

```text
V2AcceptanceReceipt(
    evaluation_candidate_root,
    pre_state_root,
    post_state_root,
    command_hash,
    consensus_context_hash,
    support_root,
    ... exact evidence roots ...
)
```

The controlled decision is then:

```text
V2Decision(
    kind = Accept | CommittedFailure,
    evaluation_candidate,
    receipt,
)
```

Ordinary rejection has a separate receipt-only shape and no candidate.

### 8.4 Commit bundle

```text
V2CommitBundle(
    decision,
    outbox_plan,
    expected_pre_root,
)
```

The dependency order is:

```text
pre-state + command + context + validated content
  -> transition cause
  -> evaluation candidate
  -> candidate root
  -> receipt
  -> decision
  -> commit bundle
```

No reverse edge exists. Candidate and receipt codecs must reject any projection
that recreates a cycle.

## 9. Publication refinement retained

Revision 3.3's closed publication dispatch remains:

```text
V1 state + migration bundle     -> pinned migration rederivation
V2 state + V2 transition bundle -> pinned deployment check and full rederivation
all mixed or unknown pairs      -> reject
```

Publication treats bundle content as equality targets only. It loads the exact
store-current state, uses the pinned verifier, reauthenticates command and
context, reruns the Revision 3.4 content pipeline, rederives the complete
pre-receipt candidate, reconstructs the receipt and decision, compares every
canonical field, and atomically publishes only the rederived tuple.

## 10. Required adversarial evidence

The permanent semantic mutation set includes:

```text
command authenticates a body using OTHER_ALGORITHM
command authenticates a body using another accepted language
body embeds a wrong policy_root while outer body root is recomputed
claim embeds a wrong configuration_root while command root matches the body
update reads admitted proposed body before B1A validation
admission result is cast to ValidatedFeeDistributionConfigurationClaimV2
B1A validator call is deleted while command-root equality remains
validated proposed claim is mutated before update-law evaluation
migration initial content is admitted but not B1A-validated
active content is root-matched but not B1A-validated
receipt is added to V2EvaluationCandidate
candidate root includes a receipt that includes the candidate root
TransitionCauseV2 regains decision_hash
```

Each semantic mutant recomputes every unrelated outer hash. A test passes only
when the missing semantic or dependency relation itself rejects the mutant.

### 10.1 Exhaustive bounded Boolean model

The checked model enumerates all `2^10 = 1,024` combinations of:

```text
structural exactness
algorithm equality
accepted-language equality
policy-root equality
embedded configuration-root equality
command-root equality
deployment equality
domain equality
version increment
activation boundary
```

Exactly one assignment accepts. The refuted admit-then-root model accepts
semantically invalid assignments and is retained as a negative control.

### 10.2 Dependency-DAG model

The model topologically sorts the intended candidate/receipt/decision/bundle
graph. Adding the edge `receipt -> evaluation_candidate` must create a detected
cycle.

## 11. B1B-1 implementation scope

Revision 3.4 includes one unmounted implementation candidate for:

```text
FCISAuthorityHeaderV2
DeploymentBootstrapAnchorClaimV2
V1ToV2MigrationManifestV2
```

and only:

```text
exact source carriers
closed field registries
strict full-consumption canonical decoding
canonical Python/Rust codecs
domain-separated anchor/manifest audit roots
shared Python/Rust golden vectors
structural contract checking
bounded adversarial models
```

The public carriers remain untrusted data. The migration manifest structurally
admits the complete declared U256 domains; fixed values `4 -> 5` and `0/1/0`
remain later migration semantics rather than carrier-constructor authority.

B1B-1 must not implement or export:

```text
ConfigurationUpdateCommandClaimV2
AuthenticatedConfigurationUpdateCommandV2
PinnedDeploymentBootstrapVerifierV2
VerifiedV1ToV2MigrationAuthorityV2
V1ToV2MigrationCandidateV2
FCISCommittedStateV2
StateBoundFeeDistributionConfigurationV2
TransitionCauseV2
V2EvaluationCandidate
receipt or decision types
successor-producing transitions
configuration update
commit bundle
proof input
publication
runtime mount
```

The structural checker rejects bare-header advance/update functions, generic
header patch atoms, anchor-claim-to-pin conversion, and all premature authority
outputs.

## 12. Cross-language carrier contract

Python and Rust share exact:

```text
schema IDs
field registries
exact text and digest rules
U256 domains
canonical UTF-8 JSON bytes
domain separators
SHA-256 roots
Unicode scalar behavior
```

Python rejects `bool` as an integer. Rust uses `BigUint` bounded to U256. The
shared fixture includes Unicode, zero, one, `U256_MAX`, roots, and a
structurally exact manifest with semantically wrong fixed constants that remains
explicitly carrier-only.

## 13. Evidence and stopping rule

B1B-1 promotion requires:

```text
all focused Python carrier tests green
shared fixture source-current
Rust shared-vector tests green
Revision 3.4 adversarial model green
Revision 3.4 structural mutation suite green
four inherited pre-mount checker profiles unchanged
final-mount not widened or suppressed
```

Passing B1B-1 authorizes review of the three untrusted carrier families only.
B1B-2 must separately freeze and implement the pinned verifier and source-bound
migration derivation. No later checkpoint may infer approval from carrier
bytes, roots, or passing B1B-1 tests.

## 14. Non-claims

Revision 3.4 does not establish:

- governance authorization of the deployment pin or update command;
- secure release distribution of pinned verifier data;
- production datastore linearizability or crash recovery;
- configuration-content availability;
- mounted V1-to-V2 migration;
- mounted configuration update or fee distribution;
- proof-system or guest refinement;
- whole-system Python/Rust parity;
- a cryptographic proof beyond the SHA-256 assumption;
- protection after arbitrary replacement of verifier code or datastore code.

The implementation remains unmounted and carries no protocol authority.
