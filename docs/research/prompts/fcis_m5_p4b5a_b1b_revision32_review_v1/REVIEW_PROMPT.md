# Independent review prompt: B1B Revision 3.2

Act as an adversarial functional-core authority reviewer. Work read-only. Do
not implement, amend, commit, push, open a pull request, or mount authority.

## Exact target

```text
repository: TheDarkLightX/ZenoDEX
target commit: 27bfde2a5679250e949d397960d6dba09117c6bd
refuted Revision 3.1: fa22950b6691d646d04c49efb43e08c78b9ae4da
refuted Revision 3: 798f4ba862ff07cf1f92b54946c67e13e7a939b6
B1A implementation: 9fd7dd78ff410c72e9f40de7055da596f392a1d6
```

First verify `SOURCE_MANIFEST.sha256`. Stop with `NO_GO` on a missing,
modified, or uninspectable required file.

## Review question

Does Revision 3.2 ensure that every non-migration authority-header transition
is derived from the header inside the exact pre-state consumed by the same
whole-state transition, and that publication rederives the complete candidate
from the store's exact current state?

## Accepted Revision 3.1 counterexample

Revision 3.1 allowed a controlled relation shaped like:

```text
advance_ordinary_header_v2(
  pre: FCISAuthorityHeaderV2,
)
```

It required the successor to preserve `pre.configuration_root`, but did not
require:

```text
pre = exact_pre_state.authority_header
```

An attacker could construct:

```text
store.current_state.authority_header.configuration_root = H_GOOD
loose_pre_header.configuration_root = H_MALLORY
```

and derive a locally valid ordinary successor preserving `H_MALLORY`. The
bundle could retain the legitimate store-current pre-root. A current-root check
does not connect a loose header input to the state committed by that root.

Do not approve based only on a closed transition variant. Verify the source of
every transition input.

## Intended Revision 3.2 relation

```text
exact pre-state
  + original authenticated command
  + independently authenticated consensus context
  + required untrusted content
  -> complete whole-state transition
       -> internally extract pre_state.authority_header
       -> internally derive transition cause
       -> derive complete successor and nested header-transition evidence

store-current exact state
  + freshly reauthenticated command
  + independently authenticated publication context
  + required untrusted content
  -> rederive complete candidate
  -> compare all submitted candidate fields
  -> one atomic publication
```

`FCISAuthorityHeaderV2` remains public exact data for B1B-1 encoding. It must
never be an independently authoritative `pre` input.

## Mandatory falsification pass

### A. Exact-pre-state source binding

Try to invoke an ordinary or configuration-update header derivation with only
a directly constructed `FCISAuthorityHeaderV2`.

Confirm the authoritative relation receives `FCISCommittedStateV2` and binds:

```text
pre_header = exact_pre_state.authority_header
```

internally. Reject any public, generic, overloaded, subclassable, or
caller-selectable bare-header advance path.

### B. Candidate binding versus currentness

Construct a candidate from an exact historical, foreign, or caller-supplied
state. Confirm it creates state-bound evidence only.

Currentness must arise solely when publication rederives from the store's exact
current state and matches the expected pre-root.

### C. Ordinary accept

Attempt:

```text
legitimate current state carrying H_GOOD
bundle expected pre-root for that state
ordinary successor derived from loose H_MALLORY
all outer hashes recomputed
```

Confirm complete transition rederivation extracts `H_GOOD` from the
store-current state and rejects the submitted successor.

### D. Committed failure

Repeat attack C for a typed committed-failure transition. Confirm the same
exact-state source relation applies and that only the explicitly declared
committed-failure changes occur.

### E. Configuration update

Attempt all of:

```text
substituted pre-header
active configuration valid for another exact state
proposed configuration with a changed deployment ID
proposed configuration with a changed domain ID
version skip
activation at N rather than N+1
configuration update composed with fee settlement
deficit-state reset
```

Confirm the update consumes the exact pre-state, freshly rebinds the active
configuration to that state, extracts the pre-header internally, and returns
one complete candidate.

### F. Transition-cause provenance

Attempt to change:

```text
transition kind
ordinary accept versus committed failure
command hash
consensus-context hash
decision hash
```

while retaining the successor and recomputing outer hashes. Confirm the cause
is derived by the same whole-state evaluation from the original authenticated
command and exact context. Publication must rederive it rather than trust a
bundle-carried cause.

### G. Commit-time source continuity

Trace every source inside publication:

```text
store-current exact state
freshly reauthenticated command
independently authenticated publication context
required untrusted configuration content
pinned deployment verifier when migration requires it
```

Try to substitute a bundle-carried state, pre-header, cause, context, active
configuration, or transition result. A root comparison without complete
transition rederivation is a blocking failure.

### H. Header result containment

Confirm `AuthorityHeaderTransitionV2` is nested evidence inside one complete
candidate. It must not be:

```text
an input command
a generic patch atom
a shell effect
an independently executable plan
a separately publishable value
```

Try to apply or publish it separately.

### I. Migration source continuity

Confirm Revision 3.2 preserves the Revision 3.1 migration repair:

```text
pinned deployment verifier remains at derivation and publication use
manifest remains untrusted
exact store-current V1 state remains at commit-time rederivation
retained namespaces use explicit equality
legacy dust must be zero
```

### J. B1B-1 scope isolation

Confirm B1B-1 contains only:

```text
FCISAuthorityHeaderV2
DeploymentBootstrapAnchorClaimV2
V1ToV2MigrationManifestV2
closed schemas and field registries
canonical Python/Rust codecs and roots
shared positive and negative vectors
limited structural-checker coverage
```

It must not export any transition, pinned verifier, migration candidate,
committed V2 state, state-bound value, successor, update, receipt, bundle,
proof input, publication, or mount.

Confirm the structural rule forbids any function that advances or updates a
bare `FCISAuthorityHeaderV2`.

### K. Carrier and parity feasibility

Check exact types, Boolean/integer alias rejection, U256 bounds, identifiers,
digest canonicality, unknown/missing/duplicate fields, full-consumption
decoding, canonical envelopes, domain separation, and Python/Rust byte parity.

An admitted carrier remains untrusted data even when all hashes recompute.

### L. Smaller safe construction

Try to remove:

```text
exact pre-state input
fresh active-configuration rebinding
independently authenticated context
command reauthentication
complete transition rederivation
complete candidate equality
```

while preserving the same guarantees. Also consider eliminating the standalone
header-transition evidence and deriving the header only as a field of the
whole-state successor. Report whether this is materially smaller.

## Automatic no-go conditions

Return `NO_GO` if:

- any non-migration header transition accepts a bare pre-header as its
  authority-relevant source;
- a bundle-carried state, header, cause, context, or active configuration can
  replace the independent source;
- commit checks only the current root without rederiving the complete
  transition;
- command or context authentication is accepted only from bundle
  self-consistency;
- ordinary accept or committed failure can change deployment ID or
  configuration root relative to the store-current exact state;
- configuration update does not freshly bind active configuration to the same
  exact pre-state;
- header-transition evidence can be applied or published separately;
- migration loses the pinned verifier or exact store-current V1 state;
- B1B-1 exports any authority-bearing or successor-producing value;
- Python and Rust cannot share exact canonical carrier bytes.

## Required report

Report:

1. exact target, packet commit, and manifest digest;
2. files and commands inspected, plus anything unavailable;
3. one verdict;
4. findings ordered by severity with minimal witnesses;
5. a table disposing attacks A through L;
6. whether the loose-pre-header counterexample is closed for ordinary accept,
   committed failure, configuration update, and publication;
7. whether every independent source remains at point of use;
8. exact B1B-1 permitted and forbidden outputs;
9. residual non-claims;
10. the smallest safe next checkpoint.

Use exactly one verdict:

```text
APPROVE_B1B1_REVISION_3_2_UNMOUNTED
REVISE_BEFORE_B1B1
NO_GO
```

Approval authorizes only the narrow unmounted B1B-1 carrier, codec, root,
vector, and structural-checker checkpoint.

