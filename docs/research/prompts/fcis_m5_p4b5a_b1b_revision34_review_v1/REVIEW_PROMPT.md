# Independent review prompt: B1B Revision 3.4

Act as an adversarial functional-core authority reviewer. Work read-only. Do
not implement, amend, commit, push, open a pull request, or mount authority.

## Exact target

```text
repository: TheDarkLightX/ZenoDEX
target commit: a8b9d191b91a3258e3d7857784bbd6067a0463e1
refuted Revision 3.3: b86763850c1bc309a1cda1b67a6b3205ed22f758
refuted Revision 3.2: 27bfde2a5679250e949d397960d6dba09117c6bd
refuted Revision 3.1: fa22950b6691d646d04c49efb43e08c78b9ae4da
refuted Revision 3: 798f4ba862ff07cf1f92b54946c67e13e7a939b6
B1A implementation: 9fd7dd78ff410c72e9f40de7055da596f392a1d6
```

First verify `SOURCE_MANIFEST.sha256`. Stop with `NO_GO` on a missing,
modified, or uninspectable required file.

## Review question

Does Revision 3.4 preserve the accepted Revision 3.3 source-binding and
publication repairs while also:

1. requiring active, proposed, and initial-migration configuration content to
   pass the frozen B1A semantic validator after closed admission;
2. binding the exact controlled validated claim to the independent state,
   command, or manifest root at point of use; and
3. separating the receipt-free evaluation candidate from the receipt-bearing
   decision and nested-decision bundle in an acyclic dependency graph?

## Accepted Revision 3.3 repairs

Revision 3.3 correctly:

```text
places proposed configuration root inside the authenticated update command
uses the pinned verifier in both publication branches
closes state/bundle-family dispatch
removes decision_hash from TransitionCauseV2
retains exact-pre-state header provenance
```

Do not repeat those earlier findings as the only attack. Confirm they remain
closed, then test the distinct semantic-validation and phase-DAG relations.

## New Revision 3.4 relations

### Configuration content

```text
untrusted content
  -> canonical decode and full consumption
  -> closed B1A admission
  -> exact FeeDistributionConfigurationClaimV2
  -> B1A semantic validation
  -> exact ValidatedFeeDistributionConfigurationClaimV2
  -> point-of-use revalidation
  -> independent expected-root comparison
  -> update or migration laws
```

B1A semantic validation enforces:

```text
pinned SRGD algorithm
pinned accepted language
policy-root equality
configuration-root equality
```

### Proposed root authority

```text
validated claim configuration root
  = recomputed canonical body root
  = root inside freshly reauthenticated update command
```

For active content, the last root comes from the exact pre-state. For initial
migration content, it comes from the pinned verified manifest.

### Phase dependency

```text
pre-state + command + context + validated required content
  -> TransitionCauseV2
  -> receipt-free V2EvaluationCandidate
  -> receipt
  -> V2Decision
  -> outbox plan
  -> V2CommitBundle
  -> proof or publication equality target
```

## Mandatory falsification pass

### A. Admission versus B1A validation

Trace the exact current functions:

```text
fcis_fee_distribution_configuration_admission.admit
validate_fee_distribution_configuration_claim_v2
revalidate_fee_distribution_configuration_claim_v2
```

Confirm that admission constructs only
`FeeDistributionConfigurationClaimV2`, and only the validator constructs exact
`ValidatedFeeDistributionConfigurationClaimV2`.

Try to bypass the validator through a cast, wrapper, seal flag, copied token,
decoded claim, generic deep copy, or parallel validator.

### B. Proposed semantic substitutions

Construct command-authenticated, canonical-root-consistent proposed content for
each case:

```text
algorithm_version = OTHER_ALGORITHM
accepted_language_version = OTHER_LANGUAGE
wrong policy_root with recomputed outer configuration root
wrong embedded configuration_root
```

Each specimen should pass the relevant structural admission step and fail B1A
before expected-root authority or update-law evaluation.

Confirm the update reads only:

```text
validated_proposed.body
```

Any read from an admitted claim, decoded mapping, resolver, shell object, or
bundle copy is blocking.

### C. Active configuration source binding

Use:

```text
exact pre-state active root = H_GOOD
active content root = H_OTHER
```

Confirm the active content must first pass B1A, then bind to the exact pre-state
root and deployment. Retest coordinated mutation of the state-bound header and
claim while retaining the original pre-state root.

Every later authority-bearing use must rebind from the same exact pre-state.
Publication must rebind from the store-current exact state.

### D. Initial migration content

For the V1-to-V2 branch, confirm:

```text
pinned verifier
  -> verified manifest
  -> expected initial configuration root

untrusted initial content
  -> closed admission
  -> B1A validation
  -> exact root equality with verified manifest
  -> source-bound migration
```

Attempt migration with an admitted but B1A-invalid initial configuration.
Attempt to use a bundle-carried root, decoded anchor, or content-selected pin.

### E. Hostile post-validation mutation

Start with an exact validated proposed claim. Mutate its nested policy with
`object.__setattr__`, then recompute unrelated outer bundle or candidate hashes.

Confirm point-of-use revalidation rejects before any update-law field read.
Repeat for active and initial-migration content.

Private construction and `frozen=True` are misuse barriers. They cannot replace
fresh B1A revalidation from independent sources.

### F. Rejection phase and no-successor law

Confirm the declared order:

```text
decode and full consumption
closed admission
B1A algorithm check
B1A accepted-language check
B1A policy-root check
B1A configuration-root check
point-of-use exact-type revalidation
independent expected-root comparison
deployment/domain/version/activation laws
candidate
receipt and decision
bundle and publication
```

Exercise specimens failing more than one phase. Confirm the earliest phase wins
and no earlier failure creates a successor, patch, effect, receipt, replay
update, outbox, or publication authority.

### G. Evaluation-candidate and receipt DAG

Build the exact dependency graph.

Confirm `V2EvaluationCandidate` contains:

```text
post_state
canonical_patch
effects
replay_update
transition_cause
```

It must not contain a receipt, receipt root, decision, bundle, outbox plan,
proof input, or any downstream root.

Try:

```text
candidate contains receipt
candidate contains receipt root
receipt hashes the receipt-bearing decision
receipt hashes the bundle
cause regains a downstream hash
```

Require a named DAG or structural test to kill every cycle before those codecs
are implemented.

### H. Nested lineage and substitution

Confirm:

```text
V2Decision owns one evaluation candidate and one receipt
V2CommitBundle owns one decision and one outbox plan
```

Try copying the post-state, patch, effect, replay update, cause, receipt, or
configuration lineage into separately constructible decision or bundle fields.

Confirm downstream properties derive from the one nested lineage and every
duplicate independently swappable authority field is absent.

### I. Retained command and header provenance

Retest:

```text
one authenticated command + P_good + P_mallory
store-current state H_GOOD + loose pre-header H_MALLORY
ordinary accept changing the active root
committed failure changing the active root
configuration update using a substituted pre-header
```

The command must select at most one canonical proposed root. Every
non-migration header derives from `exact_pre_state.authority_header` inside the
whole-state transition.

### J. Publication source continuity

Exercise:

```text
V1 state + migration bundle
V1 state + V2 bundle
V2 state + migration bundle
V2 state + V2 bundle
```

Confirm only the two matching families are eligible. The migration branch must
rerun pinned migration with B1A-validated initial content. The V2 branch must
compare current deployment to the pin, reauthenticate command/context,
B1A-validate required content, rederive candidate, receipt, decision, outbox,
and bundle, then compare the complete submitted bundle.

The bundle supplies equality targets only.

### K. B1B-1 isolation and carrier feasibility

Confirm B1B-1 remains limited to:

```text
FCISAuthorityHeaderV2
DeploymentBootstrapAnchorClaimV2
V1ToV2MigrationManifestV2
closed schemas and field registries
canonical Python/Rust codecs and roots
shared positive and negative vectors
limited structural-checker coverage
```

It must not implement a content decoder, validated authority value, update
command, pin, migration candidate, committed V2 state, state-bound value,
transition cause, evaluation candidate, decision, receipt, bundle, outbox,
proof, publication, or mount.

Check exact types, Boolean/integer alias rejection, U256 bounds, identifier and
digest canonicality, unknown/missing fields, full-consumption decoding, domain
separation, and Python/Rust byte parity feasibility.

### L. Smaller safe construction

Try to remove or combine:

```text
closed admission
B1A semantic validation
point-of-use revalidation
independent expected-root comparison
receipt-free evaluation candidate
receipt-bearing decision
nested-decision bundle
store-current complete rederivation
```

Report any smaller construction with the same guarantees. In particular, assess
whether `StateBoundFeeDistributionConfigurationV2` can be eliminated in favor
of one larger exact evaluation lineage without losing exact-state rebinding.

## Automatic no-go conditions

Return `NO_GO` if:

- structurally admitted but B1A-invalid content can enter an active or initial
  configuration root;
- update or migration laws read configuration fields before B1A validation;
- an admission value can construct or masquerade as the controlled validated
  type;
- B1A validation does not enforce the pinned algorithm, accepted language,
  policy root, and configuration root;
- a shell, bundle, resolver, content object, or decoded claim supplies an
  authoritative expected root;
- post-validation mutation is not caught before authority-bearing use;
- migration accepts merely admitted initial content;
- an evaluation candidate contains a receipt or downstream receipt root;
- a receipt hash includes an aggregate that contains the receipt;
- a decision or bundle copies independently swappable candidate lineage fields;
- a prior command, exact-pre-state, pin, or closed-dispatch repair regresses;
- B1B-1 exports any authority-bearing or successor-producing value;
- Python and Rust cannot share exact canonical carrier bytes.

## Required report

Report:

1. exact target, packet commit, manifest digest, and ancestry;
2. files and commands inspected, plus anything unavailable;
3. one verdict;
4. findings ordered by severity with minimized witnesses;
5. a table disposing attacks A through L;
6. whether B1A semantic validation precedes every authority-bearing content use;
7. whether the three root values are exact and independently sourced;
8. whether hostile post-validation mutation is closed;
9. whether the candidate/receipt/decision/bundle graph is acyclic;
10. whether prior command, header, pin, and publication repairs remain closed;
11. exact B1B-1 permitted and forbidden outputs;
12. residual non-claims and smallest safe next checkpoint.

Use exactly one verdict:

```text
APPROVE_B1B1_REVISION_3_4_UNMOUNTED
REVISE_BEFORE_B1B1
NO_GO
```

Approval authorizes only the unchanged narrow unmounted B1B-1 carrier, codec,
root, vector, and structural-checker checkpoint.
