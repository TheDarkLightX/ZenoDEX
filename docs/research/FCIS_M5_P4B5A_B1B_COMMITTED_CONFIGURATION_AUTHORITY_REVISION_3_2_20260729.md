# FCIS M5-P4B5A B1B committed configuration authority: Revision 3.2

**Status:** `PROPOSED_REVIEW_ONLY_REVISION_3_2`

**Outcome:** `SOURCE_BIND_HEADER_TRANSITIONS_TO_EXACT_STATE`

**Authority:** This document authorizes no implementation, amendment, migration,
state binding, configuration update, receipt, proof, publication, or mount.
B1B-1 remains blocked until this revision passes independent review.

**Base:** Revision 3.1 at
`fa22950b6691d646d04c49efb43e08c78b9ae4da`.

Revision 3.2 is a normative amendment to Revision 3.1. All Revision 3.1 text
remains in force except where this document replaces the ordinary-successor
source relation, authority-header transition algebra, publication relation,
mutant inventory, and B1B-1 structural rule. On conflict, Revision 3.2 controls.

## 1. Accepted Revision 3.1 counterexample

Revision 3.1 correctly removed loose authority from migration and configuration
binding. It retained a loose source at the header-transition boundary:

```text
ordinary successor -> exact pre-header + closed transition cause
```

Section 9 then defined:

```text
advance_ordinary_header_v2(pre: FCISAuthorityHeaderV2)
```

where `pre` was described as an exact header value. Exact data does not prove
that the header came from the authenticated pre-state.

### Minimal witness

Let the store-current exact V2 state contain:

```text
S_good.authority_header =
  Header(
    chain_deployment_id = "zenodex:B",
    sequence = N,
    fee_distribution_configuration_root = H_GOOD,
  )

R_good = snapshot_root_v5(S_good)
```

Construct exact untrusted data:

```text
H_fake =
  Header(
    chain_deployment_id = "zenodex:B",
    sequence = N,
    fee_distribution_configuration_root = H_MALLORY,
  )
```

The Revision 3.1 ordinary law admitted:

```text
advance_ordinary_header_v2(H_fake)
  =
  Header(
    chain_deployment_id = "zenodex:B",
    sequence = N + 1,
    fee_distribution_configuration_root = H_MALLORY,
  )
```

Every local equation holds, yet the successor preserves the root from
`H_fake`, not from `S_good.authority_header`. A bundle can retain `R_good` as
its expected pre-root while carrying the substituted successor. A root
comparison alone does not connect the loose `H_fake` input to `S_good`.

This is a concrete authority-provenance failure in the Revision 3.1 design.

## 2. Preflight and authority map

### Exact affected artifacts

This checkpoint changes documentation only:

```text
FCIS_M5_P4B5A_B1B_COMMITTED_CONFIGURATION_AUTHORITY_REVISION_3_2_20260729.md
FCIS_M5_P4B5A_B1B_REVISION_3_1_CHATGPT_ADJUDICATION_20260729.md
focused Revision 3.2 review packet
```

No Python, Rust, state, runtime, migration, receipt, proof, or shell file
changes.

### Invariant and owner

The whole-state V2 transition owns this invariant:

```text
Every successor authority header is derived from the authority header inside
the exact authenticated pre-state consumed by the same whole-state transition.
```

The commit verifier owns the refinement:

```text
PublishedSuccessor
  =
RecomputeCompleteTransition(
    store.current_exact_state,
    original_authenticated_command,
    exact_consensus_context,
    required_untrusted_content,
  )
```

### Trusted sources

| Authority fact | Independent source retained at use |
|---|---|
| Initial deployment and manifest | Pinned deployment verifier |
| Initial V1 state | Store-current exact V1 state |
| Active configuration | Exact V2 pre-state plus matching content |
| Ordinary successor header | Exact V2 pre-state |
| Configuration-update header | Exact V2 pre-state plus freshly rebound active configuration |
| Transition cause | Whole-state evaluation of the original command and context |
| Consensus context | Independently authenticated publication/step context |
| Publication currentness | Store-current exact state inside the atomic operation |

### Explicit non-guarantees

Frozen values, private constructors, canonical hashes, closed variants, and
compare-and-swap do not independently establish provenance. Arbitrary
replacement of verifier code, pinned release data, or datastore implementation
remains a trusted-computing-base assumption.

## 3. Revised global composition relation

Every non-migration V2 transition begins with the exact pre-state:

```text
derive_complete_v2_transition(
    exact_pre_state: FCISCommittedStateV2,
    original_authenticated_command: AuthenticatedV2Command,
    exact_consensus_context:
      AuthenticatedFCISConsensusContextV2,
    required_configuration_content: UntrustedConfigurationContentV2?,
)
  -> V2TransitionReject
   | V2TransitionCandidate(
       post_state,
       canonical_patch,
       effects,
       receipt,
       replay_update,
       authority_header_transition,
     )
```

The relation binds once:

```text
pre_header = exact_pre_state.authority_header
```

No caller, bundle, decoded value, configuration body, or shell argument may
supply a substitute `pre_header`.

The header transition is a nested evidence result of the complete transition.
It is never a caller-selected input and never independently applied.

Candidate computation against an exact historical or caller-supplied state
creates state-bound evidence only. It creates no currentness. Publication
authority arises only after the store-current rederivation in section 6.

## 4. Revised closed authority-header algebra

The closed result sum remains:

```text
AuthorityHeaderTransitionV2 =
    MigrationHeaderV2
  | OrdinaryAdvanceV2
  | ConfigurationUpdateV2
```

These values are controlled results nested in the complete candidate. They are
not commands, patch atoms, shell effects, or independently executable plans.

There is no authoritative function with this shape:

```text
forbidden:
  advance(pre_header: FCISAuthorityHeaderV2)
  update(pre_header: FCISAuthorityHeaderV2, ...)
```

### Migration

Migration remains owned by:

```text
verify_and_derive_v1_to_v2_migration_v2(
    pinned_verifier,
    manifest_claim,
    exact_v1_pre_state,
    initial_configuration_claim,
)
```

The returned initial header derives from the point-of-use verified manifest.

### Ordinary accept and committed failure

The source-bound helper is:

```text
derive_ordinary_header_successor_v2(
    exact_pre_state: FCISCommittedStateV2,
    exact_transition_cause:
        OrdinaryAcceptCauseV2
      | CommittedFailureCauseV2,
)
  -> HeaderTransitionRejectV2
   | OrdinaryAdvanceV2
```

Normatively:

```text
pre_header = exact_pre_state.authority_header

require pre_header.sequence < U256_MAX
require exact_transition_cause.pre_state_root =
  snapshot_root_v5(exact_pre_state)

next.chain_deployment_id =
  pre_header.chain_deployment_id

next.sequence =
  checked_add_u256(pre_header.sequence, 1)

next.fee_distribution_configuration_root =
  pre_header.fee_distribution_configuration_root
```

`exact_transition_cause` is produced by the same whole-state evaluation from
the original authenticated command and exact consensus context. It has no
public decoder or caller-controlled constructor. Commit-time publication
rederives the cause from the original command; it does not trust a
bundle-carried cause.

Ordinary rejection has no successor header.

### Configuration update

The source-bound update relation is:

```text
derive_configuration_update_v2(
    exact_pre_state: FCISCommittedStateV2,
    rebound_active_configuration:
      StateBoundFeeDistributionConfigurationV2,
    validated_proposed_configuration:
      ValidatedFeeDistributionConfigurationClaimV2,
    exact_configuration_update_command:
      AuthenticatedConfigurationUpdateCommandV2,
)
  -> ConfigurationUpdateRejectV2
   | V2TransitionCandidate
```

It first requires:

```text
fresh_active =
  bind_fee_configuration_to_state_v2(
    exact_pre_state,
    rebound_active_configuration.validated_configuration_claim,
  )

require fresh_active == rebound_active_configuration

pre_header = exact_pre_state.authority_header
active = fresh_active.validated_configuration_claim.configuration_body
proposed = recursively_revalidate_owned(
  validated_proposed_configuration
)
```

The relation then requires:

```text
pre_header.sequence < U256_MAX
active.configuration_version < U256_MAX

proposed.chain_deployment_id =
  pre_header.chain_deployment_id

proposed.fee_distribution_domain_id =
  active.fee_distribution_domain_id

proposed.configuration_version =
  checked_add_u256(active.configuration_version, 1)

proposed.activation_sequence =
  checked_add_u256(pre_header.sequence, 1)
```

The complete successor header is:

```text
next.chain_deployment_id =
  pre_header.chain_deployment_id

next.sequence =
  checked_add_u256(pre_header.sequence, 1)

next.fee_distribution_configuration_root =
  recomputed_root(proposed)
```

The update is configuration-only. It cannot compose with a fee-bearing
settlement. Balances, pools, LP balances, nonces, vault, oracle,
fee-apportionment deficits, and perps remain byte- and value-identical.

## 5. Transition-cause ownership

The complete transition derives its cause internally:

```text
AuthenticatedV2Command
  + exact_pre_state
  + exact_consensus_context
  -> Reject
   | OrdinaryAcceptCauseV2
   | CommittedFailureCauseV2
   | AuthenticatedConfigurationUpdateCommandV2
```

A cause binds:

```text
pre_state_root
command_hash
consensus_context_hash
accepted_language_version
transition_kind
decision_hash
```

The cause is nested once in the candidate lineage. A bundle cannot replace the
cause while retaining the successor. Commit-time rederivation starts from the
original authenticated command and context and requires canonical equality with
the submitted complete candidate.

## 6. Commit-time publication relation

Every V2 publication uses one atomic operation:

```text
publish_complete_v2_bundle(
    submitted_bundle,
    store,
    pinned_deployment_verifier,
    exact_publication_context:
      AuthenticatedFCISConsensusContextV2,
)
  -> PublicationRejectV2
   | PublishedV2Commit
```

Inside the atomic operation:

```text
1. current_exact_state = store.load_current_exact_state()
2. current_root = snapshot_root(current_exact_state)
3. require current_root = submitted_bundle.expected_pre_root
4. load required configuration bytes as untrusted content
5. recursively reauthenticate the submitted canonical command bytes
6. require submitted context evidence to equal exact_publication_context
7. rederive the complete transition from:
     current_exact_state
     the freshly reauthenticated command
     exact_publication_context
     required untrusted content
8. require canonical equality between the rederived complete candidate and:
     submitted decision
     submitted successor state
     submitted authority-header transition
     submitted patch and effects
     submitted receipt and replay update
     submitted post-root and all nested roots
9. atomically publish the complete rederived tuple
```

The operation never uses a bundle-carried pre-state, pre-header, cause, active
configuration, or transition result as the independent source. Bundle values
are equality targets only.

The authority header cannot be separately patched or published.

## 7. Exact migration projection retained

Revision 3.1's migration equalities remain:

```text
v2.balances    = v1.balances
v2.pools       = v1.pools
v2.lp_balances = v1.lp_balances
v2.nonces      = v1.nonces
v2.vault       = v1.vault
v2.oracle      = v1.oracle
v2.perps       = v1.perps

require v1.fee_accumulator.dust = 0
v2.fee_apportionment = canonical_empty_fee_apportionment_state_v2
```

No unnamed projection or hidden schema conversion is admitted.

## 8. Required architecture and mutation evidence

The permanent mutant set adds:

```text
ordinary advance accepts a directly constructed pre-header
ordinary advance reads bundle.pre_header
ordinary advance reads bundle.pre_state
committed failure uses a substituted pre-header
configuration update uses a substituted pre-header
configuration update uses active content not rebound to exact_pre_state
commit-time header validation reads bundle-carried state
store-current root is checked without full transition rederivation
transition cause changes while successor and outer hashes are retained
authority header is installed through a generic patch atom
authority header is published separately from the complete successor
```

Each mutant must recompute unrelated hashes. The test passes only when the
source-binding relation itself rejects the mutation.

Required BDD scenarios:

```text
Given a legitimate current state with H_GOOD
When an ordinary bundle carries a successor derived from loose H_MALLORY
Then commit-time rederivation from store.current_state rejects

Given a legitimate current state
When a committed-failure bundle substitutes its pre-header
Then candidate equality rejects with no publication

Given a configuration update
When active content is valid for another exact state
Then fresh exact-state rebinding rejects

Given a bundle with the correct current root
When its transition cause is changed and all outer hashes are recomputed
Then complete transition rederivation rejects
```

Formal or bounded models must treat the header as a projection of the global
state transition, not as a free transition input.

## 9. B1B-1 scope and structural rule

The permitted B1B-1 scope is unchanged:

```text
FCISAuthorityHeaderV2
DeploymentBootstrapAnchorClaimV2
V1ToV2MigrationManifestV2
closed schemas and field registries
canonical Python/Rust codecs and roots
shared positive and negative vectors
limited structural-checker coverage
```

B1B-1 must not implement a transition, successor, state-bound value, pinned
verifier, receipt, bundle, proof, publication, or mount.

The B1B-1 checker must enforce:

```text
FCISAuthorityHeaderV2 may appear in:
  exact value, schema, admission, codec, root, and vector modules

FCISAuthorityHeaderV2 must not appear in:
  generic state-write types
  generic patch atoms
  public authority builders
  stable currentness wrappers
  any function that advances or updates a bare header
```

Later checkpoints may introduce header-transition code only after a new
checker profile declares the exact whole-state source-bound entry points.

## 10. Rejection-order obligation

Revision 3.2 does not freeze new public rejection codes. A later checkpoint
must define the exact closed rejection vocabulary and precedence before
implementing these relations.

The required ordering constraint is:

```text
source acquisition and exact-state validation
  -> source-binding and reauthentication
  -> sequence/version bounds
  -> transition law
  -> complete candidate equality
  -> atomic publication
```

No successor, effect, receipt, replay update, or outbox authority may exist
after an earlier phase rejects. B1B-1 implements none of these rejects.

## 11. Non-claims

Revision 3.2 does not claim:

- implementation of any relation in this document;
- authenticated construction or secure release distribution of the pinned
  verifier;
- production datastore linearizability or crash recovery;
- content-cache availability;
- mounted migration, configuration update, settlement, proof, or publication;
- governance authority over configuration updates;
- Python/Rust parity beyond the already implemented B1A and apportionment
  substrates;
- a machine-checked proof of the whole-state composition relation.

## 12. Review gate and next checkpoint

Revision 3.2 must receive focused independent approval before B1B-1 begins.

The exact approval verdict is:

```text
APPROVE_B1B1_REVISION_3_2_UNMOUNTED
```

After approval, B1B-1 remains limited to untrusted carriers, schemas, canonical
Python/Rust codecs and roots, shared vectors, and limited structural-checker
coverage.
