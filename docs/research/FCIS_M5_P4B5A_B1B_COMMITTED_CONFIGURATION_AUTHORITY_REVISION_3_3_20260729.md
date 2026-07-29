# FCIS M5-P4B5A B1B committed configuration authority: Revision 3.3

**Status:** `PROPOSED_REVIEW_ONLY_REVISION_3_3`

**Outcome:** `BIND_UPDATE_CONTENT_AND_CLOSE_PUBLICATION_DISPATCH`

**Authority:** This document authorizes no implementation, amendment, migration,
state binding, configuration update, receipt, proof, publication, or mount.
B1B-1 remains blocked until this revision passes independent review.

**Base:** Revision 3.2 at
`27bfde2a5679250e949d397960d6dba09117c6bd`.

Revision 3.3 is a normative amendment to Revision 3.2. Revision 3.2 remains in
force except where this document replaces the configuration-update input
relation, transition-cause projection, publication relation,
header-transition evidence shape, mutant inventory, and review gate. On
conflict, Revision 3.3 controls.

## 1. Accepted Revision 3.2 findings

The focused ChatGPT review confirms that Revision 3.2 closes the loose
pre-header counterexample. It found two remaining P1 source gaps and one P2
dependency ambiguity.

### 1.1 Proposed configuration is not command-bound

Revision 3.2 receives:

```text
validated_proposed_configuration
exact_configuration_update_command
```

as distinct inputs. It checks the proposed deployment, domain, version,
activation sequence, and successor root. It does not prove that the
authenticated command selected that proposed configuration.

For one authenticated command `C`, both of these values can satisfy the written
transition:

```text
P_good:
  deployment = zenodex:B
  domain = protocol-fees
  version = active.version + 1
  activation = pre.sequence + 1
  policy = intended destinations and weights

P_mallory:
  deployment = zenodex:B
  domain = protocol-fees
  version = active.version + 1
  activation = pre.sequence + 1
  policy = 100 percent to Mallory
```

The resulting decisions may have different hashes. That records which decision
was produced. It does not prove which configuration `C` authorized.

### 1.2 Publication does not consume the deployment pin

Revision 3.2 includes `pinned_deployment_verifier` in the publication signature
without consuming it in the numbered relation.

This leaves migration publication without an explicit pinned rederivation and
allows a locally configured deployment `zenodex:B` to publish a valid
store-current V2 transition for `zenodex:A`.

### 1.3 Cause hashing is underspecified

Revision 3.2 puts `decision_hash` inside a cause that is nested inside the
decision lineage. Without a restricted projection, this can form a dependency
cycle.

All three findings are accepted.

## 2. Preflight and authority map

### 2.1 Exact affected artifacts

This checkpoint changes documentation only:

```text
FCIS_M5_P4B5A_B1B_COMMITTED_CONFIGURATION_AUTHORITY_REVISION_3_3_20260729.md
FCIS_M5_P4B5A_B1B_REVISION_3_2_CHATGPT_ADJUDICATION_20260729.md
focused Revision 3.3 review packet
```

No Python, Rust, state, runtime, migration, command, receipt, proof, or shell
file changes.

### 2.2 Owned invariants

The authenticated configuration-update command owns:

```text
the exact root of the proposed fee-distribution configuration
```

The exact pre-state owns:

```text
the active configuration root
the current authority header
the protocol sequence
```

The pinned deployment verifier owns:

```text
the local chain deployment ID
the expected V1-to-V2 migration-manifest root
```

The publication operation owns:

```text
currentness
closed state-family and bundle-family dispatch
complete store-current rederivation
one atomic publication
```

### 2.3 Independent source table

| Authority fact | Independent source retained at use |
|---|---|
| Current state and root | Exact state loaded from the store inside publication |
| Local deployment identity | `PinnedDeploymentBootstrapVerifierV2` |
| Migration manifest identity | Expected manifest root from the pinned verifier |
| Initial configuration identity | Point-of-use verified migration manifest |
| Active V2 configuration identity | Store-current exact V2 authority header |
| Proposed configuration identity | Freshly reauthenticated update command |
| Configuration content | Untrusted bytes admitted and root-checked by the core |
| Command identity | Fresh canonical command authentication |
| Consensus context | Independently authenticated publication context |
| Successor and effects | Complete deterministic transition rederivation |

No content resolver, bundle, shell argument, decoded claim, or candidate may
supply an expected semantic root independently.

### 2.4 Failure and commit model

Candidate derivation against an exact historical or caller-supplied state
creates state-bound evidence. It creates no currentness.

Publication loads one store-current state inside the atomic operation, derives
the version-specific root, checks deployment provenance, rederives the complete
candidate, compares every submitted field, and commits the rederived tuple
once.

Crash recovery, durable datastore linearizability, and external delivery remain
outside this review-only checkpoint.

## 3. Authenticated command binds the proposed configuration

### 3.1 Command claim

The later configuration-update command schema must contain:

```text
ConfigurationUpdateCommandClaimV2(
    proposed_fee_distribution_configuration_root: Digest32,
    ... exact authorization, replay, and language fields ...
)
```

`proposed_fee_distribution_configuration_root` is inside the canonical bytes
covered by command authentication. It is a lowercase canonical 32-byte digest
encoding under the repository's exact digest rules.

Authentication produces:

```text
AuthenticatedConfigurationUpdateCommandV2
```

whose owned command claim includes the same proposed root. A shell cannot add,
replace, or reinterpret the root after authentication.

This command type is outside B1B-1. Its exact authorization and governance
rules must be frozen in a later checkpoint before implementation.

### 3.2 Root-addressed untrusted content

The configuration-update transition has this source shape:

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
   | V2TransitionCandidate
```

The shell may retrieve content from a bundle, immutable archive, peer, file, or
cache. Those sources provide bytes only.

The core performs:

```text
active_claim =
  recursively_admit_and_own_configuration_v2(
    active_content_source
  )

active =
  bind_fee_configuration_to_state_v2(
    exact_pre_state,
    active_claim,
  )

proposed_claim =
  recursively_admit_and_own_configuration_v2(
    proposed_content_source
  )

proposed_root =
  recompute_fee_distribution_configuration_root_v2(
    proposed_claim
  )
```

It then requires:

```text
active.authority_header =
  exact_pre_state.authority_header

active.configuration_root =
  exact_pre_state.authority_header
    .fee_distribution_configuration_root

proposed_root =
  reauthenticated_update_command
    .proposed_fee_distribution_configuration_root
```

The expected active root comes only from the exact pre-state. The expected
proposed root comes only from the freshly authenticated command.

### 3.3 Update laws

After the source-binding checks:

```text
pre_header = exact_pre_state.authority_header
active_body = active.validated_configuration_claim.configuration_body
proposed_body = proposed_claim.configuration_body

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

The successor header is derived inside the complete state transition:

```text
post_state.authority_header.chain_deployment_id =
  pre_header.chain_deployment_id

post_state.authority_header.sequence =
  checked_add_u256(pre_header.sequence, 1)

post_state.authority_header
  .fee_distribution_configuration_root =
  reauthenticated_update_command
    .proposed_fee_distribution_configuration_root
```

The transition also requires:

```text
post_state.authority_header
  .fee_distribution_configuration_root =
  proposed_root
```

The update is configuration-only. It cannot compose with fee-bearing
settlement. Balances, pools, LP balances, nonces, vault, oracle,
fee-apportionment deficits, and perps remain byte- and value-identical.

One authenticated update command therefore admits at most one canonical
proposed configuration root. Content that hashes to another root rejects.

## 4. Complete non-migration V2 relation

The complete V2 transition remains source-bound:

```text
derive_complete_v2_transition(
    exact_pre_state: FCISCommittedStateV2,
    reauthenticated_command: AuthenticatedV2Command,
    exact_consensus_context:
      AuthenticatedFCISConsensusContextV2,
    required_untrusted_content:
      ExactRequiredUntrustedContentV2,
)
  -> V2TransitionReject
   | V2TransitionCandidate(
       post_state,
       canonical_patch,
       effects,
       receipt,
       replay_update,
       transition_cause,
     )
```

The relation derives the required content profile from the authenticated
command kind. The caller cannot omit a required active or proposed
configuration and cannot add content that changes the command language.

For a configuration update:

```text
active expected root   = exact_pre_state.authority_header root
proposed expected root = reauthenticated command root
```

For an ordinary fee-bearing transition:

```text
active expected root = exact_pre_state.authority_header root
```

For a transition whose support profile declares no configuration read:

```text
configuration content is neither required nor consulted
```

## 5. Closed publication dispatch

### 5.1 State and bundle families

The publication relation handles only this closed pairing:

```text
PublicationPairV2 =
    (
      FCISCommittedStateV1,
      V1ToV2MigrationBundleV2
    )
  | (
      FCISCommittedStateV2,
      V2TransitionBundleV2
    )
```

Every mixed or unknown state/bundle pair rejects before candidate derivation.
Legacy V1 ordinary publication remains on its existing mounted path and is not
redefined here.

### 5.2 Atomic operations

The closed dispatcher has two entry relations:

```text
publish_v1_to_v2_migration_bundle(
    submitted_bundle: V1ToV2MigrationBundleV2,
    store,
    pinned_deployment_verifier:
      PinnedDeploymentBootstrapVerifierV2,
)
  -> PublicationRejectV2
   | PublishedFCISV2Commit

publish_v2_transition_bundle(
    submitted_bundle: V2TransitionBundleV2,
    store,
    pinned_deployment_verifier:
      PinnedDeploymentBootstrapVerifierV2,
    exact_publication_context:
      AuthenticatedFCISConsensusContextV2,
)
  -> PublicationRejectV2
   | PublishedFCISV2Commit
```

Each relation loads the exact store-current state itself. The migration entry
requires V1. The non-migration entry requires V2. Calling the wrong entry for
the store-current state rejects.

Inside one atomic operation:

```text
1. current_exact_state = store.load_current_exact_state()
2. select the branch from the exact state family and exact bundle family
3. for V2, require current deployment ID = pinned deployment ID
4. derive the version-specific current root
5. require current root = submitted bundle expected pre-root
6. execute the branch-specific source-bound rederivation
7. require canonical equality with the submitted complete candidate
8. atomically publish the complete rederived tuple
```

The pinned verifier is mandatory in both branches.

### 5.3 V1-to-V2 migration branch

For:

```text
current_exact_state: FCISCommittedStateV1
submitted_bundle: V1ToV2MigrationBundleV2
```

publication reruns:

```text
fresh_migration =
  verify_and_derive_v1_to_v2_migration_v2(
    pinned_verifier =
      pinned_deployment_verifier,
    manifest_claim =
      recursively_admit_owned_manifest(
        submitted_bundle.untrusted_manifest_bytes
      ),
    exact_v1_pre_state =
      current_exact_state,
    initial_configuration_claim =
      recursively_admit_owned_configuration(
        submitted_bundle.untrusted_initial_configuration_bytes
      ),
  )
```

The derivation requires:

```text
recomputed manifest root =
  pinned_deployment_verifier.expected_migration_manifest_root

manifest chain deployment ID =
  pinned_deployment_verifier.expected_chain_deployment_id

snapshot_root_v4(current_exact_state) =
  manifest expected V1 pre-root
```

The initial configuration root comes from the point-of-use verified manifest.
The expected manifest root never comes from the bundle, manifest, content
resolver, or shell.

Publication requires complete canonical equality between `fresh_migration` and
the submitted migration candidate, including the exact V1 pre-root, complete
V2 successor, namespace projection, roots, receipt, replay data, and any
declared migration evidence.

### 5.4 V2 non-migration branch

For:

```text
current_exact_state: FCISCommittedStateV2
submitted_bundle: V2TransitionBundleV2
```

publication first requires:

```text
current_exact_state.authority_header.chain_deployment_id =
  pinned_deployment_verifier.expected_chain_deployment_id
```

It then:

```text
1. recursively reauthenticates submitted canonical command bytes
2. requires submitted context evidence to equal
   exact_publication_context
3. derives the required content roots from:
     current exact state
     freshly reauthenticated command
4. loads content bytes as untrusted input
5. rederives the complete V2 transition from:
     current exact state
     freshly reauthenticated command
     exact publication context
     required untrusted content
6. requires canonical equality with every submitted candidate field
```

For a configuration update, step 3 obtains:

```text
active root   from current_exact_state.authority_header
proposed root from the freshly reauthenticated command
```

No bundle-carried state, deployment ID, pre-header, command object, expected
content root, transition cause, state-bound configuration, or transition result
can substitute for these independent sources.

### 5.5 Mixed-family rejection

These pairs reject:

```text
V1 state + V2 non-migration bundle
V2 state + migration bundle
unknown state version + any bundle
known state + unknown bundle variant
```

No fallback, coercion, downgrade, or generic publication registry exists.

## 6. Acyclic transition-cause projection

Revision 3.3 removes `decision_hash` from the transition cause.

The non-migration cause is:

```text
TransitionCauseV2(
    pre_state_root,
    command_hash,
    consensus_context_hash,
    accepted_language_version,
    transition_kind,
)
```

All fields derive before candidate construction:

```text
exact pre-state
  -> pre-state root

canonical authenticated command bytes
  -> command hash

independently authenticated consensus context
  -> context hash

authenticated command kind and language admission
  -> transition kind and accepted language version

those five fields
  -> transition cause

transition cause + deterministic transition outputs
  -> complete candidate

complete candidate
  -> any later decision or candidate hash

candidate plus downstream evidence
  -> receipt and bundle
```

A transition cause never contains:

```text
decision hash
candidate hash
post-state root
receipt root
bundle root
proof root
any value whose projection includes the cause
```

Complete candidate equality at publication binds the cause to the decision.
A later checkpoint must freeze the exact cause schema, domain separator, and
canonical bytes before implementing a cause codec.

Migration uses its source-bound manifest, pinned verifier, V1 pre-root, and
migration candidate lineage. It is not coerced into
`TransitionCauseV2`.

## 7. Header transition is a derived projection

The authoritative header is only:

```text
post_state.authority_header
```

Revision 3.3 removes `authority_header_transition` as an independently stored
field of `V2TransitionCandidate`.

If a later receipt requires human-auditable header-transition evidence, it is
derived after the complete pre-state and post-state exist:

```text
derive_header_transition_evidence_v2(
    exact_pre_state.authority_header,
    post_state.authority_header,
    transition_kind,
)
```

That evidence is a projection. It cannot influence the successor, cannot be
applied, and cannot publish separately.

The closed semantic cases remain:

```text
MigrationHeaderV2
OrdinaryAdvanceV2
ConfigurationUpdateV2
```

They classify the already-derived pre/post pair. They are not free transition
inputs.

## 8. Rejection-order obligation

Revision 3.3 does not freeze public rejection codes. It freezes these
branch-specific phase orders:

```text
V1 migration:
  exact store state and state/bundle family
  -> current V1 root
  -> canonical manifest and initial-configuration admission
  -> manifest root and deployment comparison with the pin
  -> migration laws
  -> complete candidate equality
  -> one atomic publication

V2 non-migration:
  exact store state and state/bundle family
  -> deployment comparison with the pin
  -> current V2 root
  -> canonical command authentication
  -> expected-content-root derivation from authoritative sources
  -> untrusted content admission and root equality
  -> sequence/version/update laws
  -> complete candidate equality
  -> one atomic publication
```

Exact typed reject names and precedence within each phase must be frozen before
implementation.

Any rejection before publication produces no successor, effect, receipt,
replay update, or outbox authority.

## 9. Required architecture and mutation evidence

### 9.1 Permanent mutants

Revision 3.3 retains all prior source-binding mutants and adds:

```text
same authenticated update command accepts two proposed configuration roots
command commits H_GOOD while proposed content hashes to H_MALLORY
shell supplies expected proposed root separately from authenticated command
bundle supplies expected proposed root separately from authenticated command
command root is mutated while successor and unrelated hashes are retained

publication accepts migration without calling pinned verifier
publication deletes or ignores pinned verifier
local pin B accepts store-current V2 state A
migration publication uses bundle-carried V1 state
migration publication uses bundle-carried expected manifest root
V1 current state dispatches through ordinary V2 command path
V2 current state dispatches through migration path

cause contains a hash projection that includes cause
decision hash is restored inside cause
header-transition evidence influences or separately publishes state
```

Every mutant must recompute unrelated outer hashes and fields. The exact
authority-source or dependency check must kill it.

### 9.2 Required BDD scenarios

```text
Given one authenticated update command committing H_GOOD
When untrusted content hashes to H_MALLORY
Then the update rejects with no successor

Given one authenticated update command committing H_GOOD
When two different valid bodies are supplied
Then at most the body whose canonical root is H_GOOD can proceed

Given local pin zenodex:B
And store-current exact V2 state names zenodex:A
When a fully self-consistent A bundle is submitted
Then publication rejects before command evaluation

Given store-current exact V1 state
When a migration bundle is submitted
Then publication reruns migration with the pinned verifier and store-current V1
state

Given store-current exact V1 state
When a V2 non-migration bundle is submitted
Then publication rejects the family mismatch

Given a transition cause
When the dependency graph is constructed
Then every edge points from pre-state, command, and context toward the candidate
and no path returns to the cause
```

### 9.3 Formal and bounded obligations

A later bounded model must include:

```text
two proposed bodies under one command
two deployment IDs
V1 and V2 state families
migration and non-migration bundle families
all four family pairings
content-root substitution
cause dependency-cycle detection
```

The model must establish determinism only after command-to-content binding and
closed publication dispatch are included.

## 10. B1B-1 scope remains unchanged

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
successor-producing transition
configuration update
receipt
bundle
proof input
publication
runtime mount
```

The B1B-1 checker must also reject:

```text
any function advancing or updating a bare FCISAuthorityHeaderV2
any generic authority-header patch or write atom
any public conversion from an anchor claim to a pinned verifier
any command or publication type introduced early
```

The three B1B-1 carrier field sets do not change in Revision 3.3.

## 11. Pattern selection record

### Domain schema and relationship

The state header commits active configuration identity. The authenticated
update command commits proposed configuration identity. The deployment pin
commits local deployment and migration-manifest identity. Publication composes
these facts with the store-current exact state.

### Selected construction

```text
root-addressed untrusted content
+ source-bound whole-state transition
+ closed state/bundle publication dispatch
+ point-of-use deployment pin
+ acyclic upstream cause
+ one atomic complete-candidate commit
```

### Rejected alternatives

- A shell-selected proposed root gives the shell semantic policy authority.
- A bundle-selected expected root proves only bundle self-consistency.
- A migration candidate published without the pin loses bootstrap provenance.
- Implicit deployment descent leaves recovery and datastore-selection mistakes
  unchecked.
- A cause containing a downstream decision hash creates a cyclic projection.

### Mechanical guarantees

- One authenticated update command selects at most one canonical proposed root.
- Store-current V2 deployment must equal the independently pinned deployment.
- Migration publication repeats pinned source verification.
- Mixed state/bundle families fail closed.
- Cause construction is acyclic.
- Header state publishes only inside the complete successor.

### Explicit non-guarantees

The construction does not establish governance authorization, secure pin
distribution, datastore correctness, crash recovery, content availability,
mounted behavior, cryptographic strength beyond the hash assumption, or
machine-checked composition proof.

### Trusted constructors and boundaries

The pinned verifier is established before transaction processing. Command
authentication owns the proposed root. Exact state admission owns the current
header. The publication operation owns currentness and atomicity.

Public carriers and content remain untrusted even when self-consistent.

### Staleness, aliasing, concurrency, and crash witness

- Stale candidates fail the store-current root comparison.
- Fresh recursive ownership prevents retained content aliases.
- Competing updates race on one pre-root and one sequence.
- Crash semantics remain a later shell obligation.

### Python and Rust enforcement plan

Later implementations require exact digest strings, exact U256 values,
transitively owned immutable aggregates, checked arithmetic, exhaustive tagged
state/bundle families, canonical schemas, and shared byte vectors.

### Serialization, replay, and migration implications

The update command root enters authenticated canonical command bytes.
Migration retains its existing manifest root and carrier schema. The cause
schema is downstream and excluded from B1B-1.

### Evidence hooks

Architecture-conformance mutants, BDD scenarios, Python/Rust differential
vectors, bounded family-dispatch models, store-current stateful tests, and
crash/CAS tests are required at their owning checkpoints.

## 12. Non-claims

Revision 3.3 does not claim:

- implementation of any relation in this document;
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

## 13. Review gate and next checkpoint

Revision 3.3 must receive focused independent approval before B1B-1 begins.

The exact approval verdict is:

```text
APPROVE_B1B1_REVISION_3_3_UNMOUNTED
```

After approval, B1B-1 remains limited to the unchanged untrusted authority
header, bootstrap-anchor-claim, and migration-manifest carriers; their schemas;
canonical Python/Rust codecs and roots; shared vectors; and limited structural
checker coverage.
