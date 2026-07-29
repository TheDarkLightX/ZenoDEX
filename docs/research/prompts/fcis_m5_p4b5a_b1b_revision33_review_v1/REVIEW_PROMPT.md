# Independent review prompt: B1B Revision 3.3

Act as an adversarial functional-core authority reviewer. Work read-only. Do
not implement, amend, commit, push, open a pull request, or mount authority.

## Exact target

```text
repository: TheDarkLightX/ZenoDEX
target commit: b86763850c1bc309a1cda1b67a6b3205ed22f758
refuted Revision 3.2: 27bfde2a5679250e949d397960d6dba09117c6bd
refuted Revision 3.1: fa22950b6691d646d04c49efb43e08c78b9ae4da
refuted Revision 3: 798f4ba862ff07cf1f92b54946c67e13e7a939b6
B1A implementation: 9fd7dd78ff410c72e9f40de7055da596f392a1d6
```

First verify `SOURCE_MANIFEST.sha256`. Stop with `NO_GO` on a missing,
modified, or uninspectable required file.

## Review question

Does Revision 3.3 preserve exact-pre-state header provenance while also:

1. binding the canonical proposed configuration root inside the freshly
   authenticated update command;
2. using the independently pinned deployment verifier in closed V1-migration
   and V2-non-migration publication branches; and
3. making transition-cause hashing acyclic?

## Accepted Revision 3.2 findings

### Proposed-content substitution

Revision 3.2 supplied the authenticated update command and proposed content as
distinct inputs. The command did not commit the proposed root. One authenticated
command could therefore be paired with either intended content or a valid
same-domain, same-version policy paying Mallory.

### Unused publication pin

Revision 3.2 received a pinned deployment verifier without consuming it in its
publication steps. It did not define the V1 migration publication branch and
did not compare a store-current V2 deployment ID with the local pin.

### Cause cycle

Revision 3.2 placed `decision_hash` inside a cause nested in the decision
lineage without freezing an acyclic projection.

Do not repeat the loose-pre-header review as the only attack. Confirm that
Revision 3.2's exact-state correction remains, then test these distinct
authority sources.

## Intended Revision 3.3 relations

### Configuration update

```text
authenticated command owns proposed configuration root
exact pre-state owns active configuration root
untrusted content supplies bytes only

recompute proposed root from freshly admitted owned content
require proposed root = root inside freshly authenticated command
derive complete successor from the same exact pre-state and command
```

### Publication

```text
store-current exact V1 + migration bundle
  -> rerun pinned migration derivation

store-current exact V2 + V2 transition bundle
  -> require current deployment ID = pinned deployment ID
  -> reauthenticate command and context
  -> rederive complete V2 candidate

every mixed family
  -> reject
```

### Cause dependency

```text
pre-state + authenticated command + authenticated context
  -> transition cause without decision_hash
  -> complete candidate
  -> any later decision/candidate hash
  -> receipt and bundle
```

## Mandatory falsification pass

### A. Command-to-proposed-content binding

Use one exact authenticated configuration-update command with two valid
proposed bodies:

```text
P_good
P_mallory
```

Both should satisfy deployment, domain, version, and activation laws. Confirm
that the command contains
`proposed_fee_distribution_configuration_root` in its authenticated canonical
projection and that only content with that root can proceed.

Attempt to supply the expected proposed root through the shell, bundle,
resolver, or content object. Any such independent authority source is a
blocking failure.

### B. Untrusted content boundary

Trace active and proposed content from bytes to exact owned claims.

Confirm:

```text
active expected root   comes only from exact_pre_state.authority_header
proposed expected root comes only from freshly authenticated command
```

Try malformed-present fields, unknown fields, noncanonical bytes, nested
post-validation mutation, and content with a valid structure under the wrong
root.

### C. Exact-pre-state and header provenance

Retest the accepted Revision 3.1 counterexample:

```text
store-current state carries H_GOOD
loose exact header carries H_MALLORY
bundle retains legitimate current pre-root
```

Confirm every non-migration successor extracts the header from the exact
pre-state and that no bare-header transition API reappears.

### D. V1 migration publication

For store-current exact V1 state and a migration bundle, confirm publication
reruns:

```text
verify_and_derive_v1_to_v2_migration_v2(
  pinned deployment verifier,
  untrusted manifest,
  store-current exact V1 state,
  untrusted initial configuration,
)
```

Attempt:

```text
bundle-carried V1 state
bundle-carried expected manifest root
manifest-selected deployment pin
decoded anchor converted into a pin
pinned verifier argument deleted or ignored
```

Each must reject or fail the structural contract.

### E. V2 publication deployment pin

Set:

```text
local pinned deployment = zenodex:B
store-current exact V2 deployment = zenodex:A
```

Provide a fully self-consistent A transition and bundle. Confirm publication
rejects before command evaluation.

Check that the expected local deployment comes from the pre-established pinned
verifier, never from the state, command, bundle, content, environment, or
transaction-time file.

### F. Closed publication-family dispatch

Exercise all four pairings:

```text
V1 state + migration bundle      -> eligible branch
V1 state + V2 transition bundle  -> reject
V2 state + migration bundle      -> reject
V2 state + V2 transition bundle  -> eligible branch
```

Reject unknown versions and variants. Find any generic fallback, coercion,
downgrade, open registry, or caller-selected dispatch.

### G. Acyclic cause projection

Build the exact dependency graph.

Confirm `TransitionCauseV2` contains only:

```text
pre_state_root
command_hash
consensus_context_hash
accepted_language_version
transition_kind
```

It must not contain a decision, candidate, post-state, receipt, bundle, proof,
or any hash whose projection includes the cause.

Try restoring `decision_hash` inside the cause. Require a named structural or
dependency-DAG test to kill that mutation before cause codecs are implemented.

### H. Complete candidate equality and currentness

For both publication branches, replace every bundle-carried lineage field one
at a time and recompute unrelated hashes.

Confirm:

```text
store-current exact state is the independent state source
pinned verifier is the independent deployment/manifest source
reauthenticated command is the independent proposed-root source
authenticated publication context is the independent consensus source
submitted bundle fields are equality targets only
```

Publication must compare the complete rederived candidate and atomically commit
the rederived tuple.

### I. Header-result containment and simplification

Revision 3.3 removes `authority_header_transition` as an independently stored
candidate field.

Confirm the authoritative header exists only at:

```text
post_state.authority_header
```

Any later header-transition evidence must be a projection of exact pre-header,
post-header, and transition kind. Try to apply, patch, or publish the evidence.

### J. Migration and namespace continuity

Confirm the retained migration projection remains explicit:

```text
balances
pools
LP balances
nonces
vault
oracle
perps
zero legacy dust
canonical empty V2 fee-apportionment state
```

Confirm migration is not coerced into the ordinary non-migration cause or
command path.

### K. B1B-1 scope and carrier feasibility

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

It must not implement an update command, pin, migration candidate, committed
V2 state, state-bound value, cause, transition, update, receipt, bundle, proof,
publication, or mount.

Check exact types, Boolean/integer alias rejection, U256 bounds, identifier and
digest canonicality, unknown/missing fields, full-consumption decoding, domain
separation, and Python/Rust byte parity feasibility.

### L. Smaller safe construction

Try to remove:

```text
command-bound proposed root
store-current exact state
point-of-use deployment pin
closed state/bundle family dispatch
command/context reauthentication
complete candidate rederivation and equality
```

Report any smaller construction with the same authority guarantees. Also
review the removal of standalone header-transition evidence and whether any
other duplicated independently swappable field remains.

## Automatic no-go conditions

Return `NO_GO` if:

- proposed content identity comes from the shell, bundle, resolver, or content
  rather than the freshly authenticated command;
- one authenticated update command can accept two canonical proposed roots;
- publication receives but does not use the pinned verifier;
- migration publication does not rerun pinned derivation over store-current
  exact V1 state;
- V2 publication does not compare store-current deployment ID with the local
  pin;
- a mixed or unknown state/bundle family reaches candidate derivation;
- a cause contains a downstream hash whose projection includes the cause;
- a bare header or header-transition evidence can influence or publish state;
- a bundle-carried state, command object, expected root, context, or transition
  result replaces an independent source;
- B1B-1 exports any authority-bearing or successor-producing value;
- Python and Rust cannot share exact canonical carrier bytes.

## Required report

Report:

1. exact target, packet commit, manifest digest, and ancestry;
2. files and commands inspected, plus anything unavailable;
3. one verdict;
4. findings ordered by severity with minimized witnesses;
5. a table disposing attacks A through L;
6. whether command-to-proposed-content binding is exact;
7. whether both publication branches consume the pinned verifier;
8. whether publication dispatch is exhaustive;
9. whether the cause dependency graph is acyclic;
10. whether prior exact-pre-state provenance remains closed;
11. exact B1B-1 permitted and forbidden outputs;
12. residual non-claims and smallest safe next checkpoint.

Use exactly one verdict:

```text
APPROVE_B1B1_REVISION_3_3_UNMOUNTED
REVISE_BEFORE_B1B1
NO_GO
```

Approval authorizes only the unchanged narrow unmounted B1B-1 carrier, codec,
root, vector, and structural-checker checkpoint.
