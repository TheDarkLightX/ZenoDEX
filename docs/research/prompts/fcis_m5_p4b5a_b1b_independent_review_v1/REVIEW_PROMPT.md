# Independent review prompt: FCIS M5-P4B5A B1B

You are an independent adversarial architecture reviewer. Review exact ZenoDEX
commit `14f5cb535250858cc1cf0ce00b8f6f6ebcd6e2d7`. Work read-only. Do not
implement, commit, push, open a pull request, or mount authority.

Do not trust summaries or prior verdicts. Read the included source, tests,
contracts, and SRGD amendment. Record the exact model identity, review date,
target commit, and input-manifest hash in your answer.

## Question under review

Can B1B safely derive a fee-distribution configuration that is bound to exact
committed protocol state without letting a caller-selected, self-consistent
configuration acquire protocol authority?

The proposed construction is:

```text
untrusted FeeDistributionConfigurationClaimV2
  -> canonical admission and root recomputation
  -> ValidatedFeeDistributionConfigurationClaimV2
     (integrity and self-consistency only; no protocol authority)

FCISCommittedStateV2 contains:
  FCISAuthorityHeaderV2(
      sequence,
      fee_distribution_configuration_root,
      fee_distribution_configuration_version,
  )

exact admitted pre-state
+ validated configuration claim
+ expected pre-state root
  -> exact root/version/activation checks
  -> StateBoundFeeDistributionConfigurationV2
     (bound to one pre-state; still not independent commit authority)

publication:
  one expected-pre-root compare-and-swap
```

The complete configuration body remains a separate content-addressed input.
The state commits its root and version. Missing content must fail closed.

## Normative hierarchy

Use this order when sources conflict:

```text
1. FCIS semantic rule: explicit immutable inputs, pure transition,
   exact plan, shell-side atomic publication.
2. SRGD_V1_AMENDMENT.md, except where the B1B correction explicitly identifies
   and repairs its missing committed configuration identity and sequence.
3. B1A configuration-claim validation contract and exact implementation.
4. B1B committed-configuration authority correction under review.
5. Tests and generated vectors as evidence, never as a substitute for the
   normative relation.
```

The specification defines the denotation. Python and Rust code are executable
implementations that require refinement evidence.

## Required source reading

Read at minimum:

```text
docs/research/prompts/fcis_m5_p4b5a_dynamic_apportionment_architecture_v1/SRGD_V1_AMENDMENT.md
docs/research/FCIS_M5_P4B5A_CONFIGURATION_CLAIM_VALIDATION_CONTRACT_20260728.md
docs/research/FCIS_M5_P4B5A_B1B_COMMITTED_CONFIGURATION_AUTHORITY_CORRECTION_20260728.md

src/core/fcis_fee_distribution_configuration_values.py
src/core/fcis_fee_distribution_configuration_schema.py
src/core/fcis_fee_distribution_configuration_admission.py
src/core/fcis_fee_distribution_configuration_codec.py
src/core/fcis_fee_distribution_configuration_verification.py
rust-runtime/crates/zenodex-runtime-core/src/fcis_fee_distribution_configuration.rs

tests/core/test_fcis_fee_distribution_configuration.py
tests/core/test_fcis_fee_distribution_configuration_admission.py
tests/core/test_fcis_fee_distribution_configuration_golden.py
tests/fixtures/fcis_fee_distribution_configuration_v2_golden.json
tools/build_fcis_fee_distribution_configuration_v2_golden.py
tools/check_fcis_authority_snapshot_contract.py
tests/tools/test_check_fcis_authority_snapshot_contract.py
```

Also inspect every import or consumer of
`ValidatedFeeDistributionConfigurationClaimV2` and confirm whether mounted,
evaluator, decision, bundle, or commit paths can currently consume it.

## Mandatory falsification attempts

Attempt each attack. A prose assertion without tracing the exact construction
or comparison path is insufficient.

### A. Authority fabrication

Construct a Mallory-selected configuration body with attacker destinations,
recompute every embedded root and version consistently, pair it with a
caller-selected pre-state and expected root, and determine exactly which values
can be constructed. Distinguish:

```text
canonical
validated
state-bound
authenticated/current
commit-authoritative
```

Reject the architecture if any public or mounted path collapses these stages.

### B. Root and version substitution

Try:

- correct body with wrong configuration root;
- correct root with wrong configuration version;
- header from another deployment or domain;
- body from another pre-state with the same version;
- post-validation mutation of body, policy, header, or pre-state;
- a cached root accepted without recomputing its complete semantic preimage.

### C. Current-state and publication binding

Determine whether a state-bound value created from an arbitrary historical or
fabricated pre-state can itself authorize publication. Verify that only the
shell's atomic expected-pre-root comparison can establish currentness and that
the shell need not reconstruct fees, policy, successor state, or effects.

### D. Activation and sequence

Check:

```text
activation_sequence = sequence - 1
activation_sequence = sequence
activation_sequence = sequence + 1
sequence = 0
sequence = 2^256 - 1
```

Assess every Accept, Reject, and CommittedFailure rule. Look for off-by-one
activation, overflow, liveness ambiguity, or a path that commits without
advancing sequence.

### E. Configuration update race and ABA

Model a settlement planned under configuration A while an authorized update to
configuration B commits first. The settlement must become stale through the
single state-root CAS. Attempt configuration A -> B -> A, no-economic-change
commits, retries, and historical-header replay. State whether sequence is
sufficient for the exact ABA claim being made.

### F. Content addressing and availability

Determine whether committing only the configuration root and version preserves
all semantic inputs needed for replay. Identify any semantic field omitted from
the root preimage. Missing content must be an availability failure with no
fallback, no partial transition, and no caller-selected replacement.

### G. Migration and topology

Check V1-to-V2 migration, zero and nonzero legacy scalar dust, initial sequence,
initial configuration activation, deployment/domain preservation, forbidden
domain split/merge/reuse, and configuration-version monotonicity.

### H. Python/Rust canonical refinement

Determine whether B1B-1 can define exact Python/Rust bytes without host-width,
map-order, Unicode, integer, or schema ambiguity. Require stable field order,
schema identifiers, U256 encoding, digest format, rejection paths, and shared
golden vectors. State every field the header codec must bind.

### I. Composition and shell closure

Trace the intended composition:

```text
exact settlement replay
  -> provisional protocol-fee witnesses
  -> SRGD-v1 allocation
  -> one alias-aware canonical patch
  -> one three-way decision
  -> one receipt and atomic commit bundle
```

Identify any semantic choice left to the shell, including policy selection,
fee reconstruction, destination selection, retry classification, or effect
reconstruction.

### J. Smaller safe alternative

Try to find a construction with less committed state or a smaller trust surface
that preserves:

- caller-fabrication resistance;
- one-root atomic publication;
- deterministic activation;
- exact replay;
- content integrity;
- Python/Rust canonical parity.

Compare at least:

```text
full configuration body in state
root/version/sequence header in state
external configuration store with dual CAS
opaque shell witness without state commitment
```

## Automatic NO-GO conditions

Return `NO_GO` if any of these are required or representable:

- caller-controlled data constructs an authenticated or commit-authoritative
  configuration;
- configuration authority depends on a request, environment variable, file,
  cache, registry response, clock, or network result not committed as input;
- the configuration root omits a semantic field used by the transition;
- missing content falls back to another policy or configuration;
- state and configuration can race without changing the expected pre-root;
- the shell independently reconstructs state, fees, destinations, or effects;
- Python and Rust admit different values or emit different canonical bytes;
- V1 and V2 fee-state families coexist in one admitted state;
- sequence overflow wraps or a committed transition can reuse the same complete
  state root;
- review evidence applies to a different source commit.

## Required output

Return exactly these sections:

```text
1. VERDICT
2. EXECUTIVE REASON
3. SOURCE AND PROVENANCE CHECK
4. FINDINGS, highest severity first
5. FALSIFICATION ATTEMPTS A-J
6. PYTHON/RUST REFINEMENT ASSESSMENT
7. REQUIRED TESTS AND MUTANTS
8. RESIDUAL RISKS AND NON-CLAIMS
9. SMALLEST SAFE NEXT CHECKPOINT
```

Use one verdict:

```text
APPROVE_B1B1_UNMOUNTED
REVISE_BEFORE_B1B1
NO_GO
```

For every blocker provide:

```text
finding ID
severity
violated invariant
exact file, symbol, line, or document section
minimal counterexample
expected behavior
actual or representable behavior
smallest safe correction
regression evidence required
```

An approval permits only exact unmounted authority-header values and canonical
Python/Rust codecs. Do not imply approval for state-root integration,
state-bound construction, candidate integration, publication, or mounting.
