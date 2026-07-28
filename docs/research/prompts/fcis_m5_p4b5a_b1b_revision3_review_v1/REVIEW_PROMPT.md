# Independent review prompt: B1B Revision 3

Act as an adversarial functional-core authority reviewer. Work read-only. Do
not implement, amend, commit, push, open a pull request, or mount authority.

## Exact target

```text
repository: TheDarkLightX/ZenoDEX
target commit: 798f4ba862ff07cf1f92b54946c67e13e7a939b6
prior refuted design: 14f5cb535250858cc1cf0ce00b8f6f6ebcd6e2d7
B1A implementation: 9fd7dd78ff410c72e9f40de7055da596f392a1d6
```

First verify `SOURCE_MANIFEST.sha256`. Stop with `NO_GO` on a missing,
modified, or uninspectable required file.

## Question

Can Revision 3 safely establish the first V2 deployment and fee-configuration
authority while retaining:

```text
configuration body outside state
deployment-scoped state header
one deterministic V1-to-V2 migration
state-bound configuration without durable currentness
one commit-time expected-pre-root CAS
closed Python/Rust canonical values
```

The design must prevent a caller-selected, self-consistent deployment,
migration manifest, configuration, state, or root from becoming local protocol
authority.

## Known counterexample that Revision 3 must close

The intended deployment is `zenodex:B`. A Revision 2 caller constructs a valid
configuration for `zenodex:A`, computes its root `H_A`, installs `H_A` in an
initial sequence-zero header, computes state root `R_A`, and binds the claim to
that state. Every Revision 2 check passes because no independent `zenodex:B`
value enters the relation.

Do not merely repeat that Revision 3 adds a deployment field. Determine whether
the field's first value has an independently trusted origin.

## Mandatory falsification pass

### A. Bootstrap-anchor substitution

Try to obtain `VerifiedV1ToV2MigrationAuthorityV2` when the anchor, manifest,
deployment ID, expected V1 root, initial configuration root, or domain ID all
come from the same untrusted caller. Determine whether decoding an anchor or
verified-authority projection can accidentally construct authority.

### B. Circular trust

Trace the origin of:

```text
DeploymentBootstrapAnchorV2.chain_deployment_id
DeploymentBootstrapAnchorV2.expected_migration_manifest_root
```

Reject any design in which the manifest authenticates its own anchor, the
candidate state authenticates its own deployment, or a transaction-time
environment/file lookup selects the expected value.

### C. Migration determinism

From one exact V1 pre-state, attempt to produce two accepted V2 roots by varying
sequence, configuration version, activation sequence, deployment, domain,
initial configuration root, snapshot versions, fee state, or retained economic
fields. Test second migration and V2-to-V1 downgrade.

### D. Currentness confusion

Construct a valid state-bound configuration from a historical or foreign state.
Confirm it remains labeled with that exact state/deployment and cannot become
local current authority until a deployment-specific verifier and the atomic
store comparison both accept.

### E. Header minimality and version removal

Determine whether removing configuration version from the header loses stale
update, activation, replay, or audit safety. Attempt to substitute a body with
another version under the same committed root without assuming a SHA-256
collision. Conversely, identify any remaining redundant independently
swappable authority field.

### F. Configuration update boundary

Test update at pre-sequence `N`:

```text
successor sequence = N + 1
new configuration version = old + 1
new activation sequence = N + 1
update transition has no fee-bearing settlement
first fee use occurs from pre-sequence N + 1
```

Try to apply the new policy during the update transition, skip a version,
change deployment/domain, or reset apportionment deficits.

### G. Overflow and rejection precedence

Exercise sequence and configuration version at `U256_MAX - 1` and `U256_MAX`,
including simultaneous exhaustion. Check Python/Rust feasibility and the
declared precedence.

### H. Rotation and topology

Confirm weight, destination, and ordinary policy rotation is allowed while
stable domain identity and deficits are preserved. Confirm domain creation,
ID rotation, split, merge, retirement, and reuse remain forbidden in the first
V2 language.

### I. Ownership and hostile mutation

Attempt nested `object.__setattr__` mutation after validation and state binding.
Check that field-by-field ownership plus point-of-use and commit-time
revalidation closes the path without generic copying, deep freezing, mutable
bases, or seal flags.

### J. Content availability and replay

Distinguish authority from availability. Confirm only transitions declaring a
configuration read block on missing content. Verify that a published bundle
retains the exact canonical claim bytes needed for historical replay and that
an archive cannot select policy authority.

### K. Cross-language canonical feasibility

Check that the proposed header, bootstrap anchor, migration manifest, verified
authority, initial V2 state, state root, state-bound value, update successor,
receipt, bundle, and rejection vectors can have one exact field registry and
byte-identical Python/Rust encoding. Canonical JSON key sorting must not be
confused with source or insertion order.

### L. Smaller safe construction

Try to remove a field, witness, or phase while preserving the same bootstrap,
cross-deployment, race, replay, migration, mutation, and canonical-byte
guarantees. Also test whether a deployment-scoped state-root domain would be
strictly smaller or safer than the selected header.

## Automatic no-go conditions

Return `NO_GO` if:

- the bootstrap anchor is transaction-selected or derived from the manifest it
  authenticates;
- one untrusted input family supplies deployment, manifest, pre-root, and
  configuration authority;
- a self-consistent wrong deployment can become local migration, receipt,
  bundle, proof, or publication authority;
- the same V1 state has multiple accepted initial V2 successors;
- a prior shell read creates stable current-authority evidence;
- configuration update can also settle fees;
- policy rotation resets or changes the stable deficit domain;
- a decoded or publicly constructed projection gains controlled authority;
- replay requires unavailable semantic content that no committed bundle
  retains;
- Python and Rust cannot share exact U256 and canonical-byte semantics.

## Required report

Report:

1. exact target and manifest digest;
2. files and commands inspected, plus anything unavailable;
3. one verdict;
4. findings ordered by severity, with a minimal witness;
5. a table disposing attacks A through L;
6. whether every prior blocking condition is closed;
7. required values, schemas, tests, and mutants for B1B-1;
8. residual non-claims;
9. the smallest safe next checkpoint.

Use exactly one verdict:

```text
APPROVE_B1B1_REVISION_3_UNMOUNTED
REVISE_BEFORE_B1B1
NO_GO
```

Approval authorizes only unmounted B1B-1 values, schemas, codecs, and vectors.
