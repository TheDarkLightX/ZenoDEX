# FCIS M5-P4B5A B1B-1 Revision 3.4 implementation report

**Status:** `UNMOUNTED_IMPLEMENTATION_CANDIDATE`

**Base review packet:** `0511d71cca6b45df25e3c230e69bcce11d25d5a4`

**Authority mount:** prohibited

## Result

This checkpoint repairs the Revision 3.3 semantic-validation gap and implements
the narrow B1B-1 carrier surface.

The configuration-content relation is now explicitly:

```text
exact admitted claim
  -> B1A semantic validation
  -> fresh field-by-field ownership
  -> second semantic validation
  -> controlled non-authoritative validated claim
```

The normative Revision 3.4 design additionally requires canonical byte
decoding before admission and independently sourced expected-root equality
after semantic validation.

The receipt dependency is separated into:

```text
transition cause
  -> pre-receipt evaluation candidate
  -> candidate root
  -> receipt
  -> decision
  -> commit bundle
```

## Implemented unmounted values

```text
FCISAuthorityHeaderV2
DeploymentBootstrapAnchorClaimV2
V1ToV2MigrationManifestV2
```

Each has:

- exact Python value and source-carrier types;
- closed field registry;
- strict canonical byte decoding with duplicate/unknown/missing rejection;
- unique canonical JSON encoding;
- full U256 handling with Boolean rejection in Python;
- matching Rust owned values and canonical encoders;
- shared Unicode and boundary vectors.

The anchor-claim and migration-manifest roots use independent domain
separators.

## Explicitly absent

```text
pinned verifier
verified migration authority
migration candidate
committed V2 state
state-bound configuration
update command
transition cause implementation
successor-producing transition
receipt
decision
bundle
proof input
publication
runtime mount
```

## Adversarial evidence

The bounded model enumerates 1,024 combinations of structural and semantic
conditions. The repaired relation accepts exactly one combination. The refuted
admit-then-root relation accepts 15 semantically invalid combinations and is
retained as a negative control.

The dependency graph topologically sorts. Adding a receipt-to-candidate edge is
rejected as a cycle.

Structural mutations kill:

- deletion of B1A validation;
- receipt insertion into the evaluation candidate;
- downstream hashes in the transition cause;
- premature pinned-verifier or state-authority classes;
- bare-header advance/update functions;
- forbidden authority imports;
- missing Rust carrier definitions;
- registry and root-domain drift.

## Local gates

```text
B1B carriers and inherited B1A configuration tests: 45 passed
Revision 3.4 model and mutation-checker tests:          12 passed
Inherited P4B5A structural-checker tests:             18 passed
Total focused Python tests:                           75 passed
Revision 3.4 contract checker:                        green
Python compileall:                                    green
```

The bounded review environment did not contain a Rust toolchain. Rust shared
vector tests are included and must pass in repository CI before promotion.

## Promotion boundary

Passing this checkpoint permits review of the three untrusted carrier families
only. It does not establish deployment authority, migration authority,
configuration-update authority, publication currentness, or mounted behavior.
