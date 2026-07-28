# FCIS M5-P4B5A fee-configuration claim-validation contract

**Status:** `FROZEN_FOR_FRESH_UNMOUNTED_CHECKPOINT_B1A`

**Base implementation:** commit
`d434d29673692ef78f2db5f7a7cfae7a737fb2d6`

**Normative architecture:** reviewed
`docs/research/prompts/fcis_m5_p4b5a_dynamic_apportionment_architecture_v1/SRGD_V1_AMENDMENT.md`

**Authority mount:** prohibited

## 1. Purpose and boundary

Checkpoint B1A validates the canonical self-consistency of a fee-distribution
configuration claim before settlement lineage is added. It deliberately stops
before deployment authorization.

```text
decoded configuration claim
  -> closed structural admission
  -> canonical policy and configuration-root recomputation
  -> pinned algorithm and accepted-language comparison
  -> controlled validated claim with no protocol authority
```

The checkpoint does not implement:

```text
OwnedSettlementV2
provisional protocol-fee witnesses
balance or pool-reserve changes
fee-apportionment state changes
step candidates, receipts, support roots, state roots, or commit bundles
configuration storage, shell verification, or authority mounting
authenticated configuration construction
```

The validated value is an unmounted self-consistency result. A decoded claim,
validated claim, direct constructor attempt, canonical byte sequence, or
matching hash is not configuration authority. Only a later comparison against
configuration identity obtained from authenticated committed pre-state or an
equivalent shell witness may construct an authenticated configuration.

## 2. Constants and exact types

```text
algorithm_version =
  SUPPORT_RESPECTING_GREEDY_DEFICIT_V1

accepted_language_version =
  PROVISIONAL_FEES_NO_SAME_BATCH_FUNDING_V2
```

The canonical policy is the Checkpoint-A `FeeDistributionPolicyV2`.

```text
FeeDistributionConfigurationBodyV2(
    chain_deployment_id: ExactText,
    configuration_version: ExactU256Positive,
    fee_distribution_domain_id: ExactText,
    policy_root: Digest32,
    policy: FeeDistributionPolicyV2,
    activation_sequence: ExactU256,
    algorithm_version: ExactText,
    accepted_language_version: ExactText,
)

FeeDistributionConfigurationClaimV2(
    body: FeeDistributionConfigurationBodyV2,
    configuration_root: Digest32,
)

ValidatedFeeDistributionConfigurationClaimV2(
    body,
    configuration_root,
)
```

`Digest32` is a lowercase `0x`-prefixed 32-byte hexadecimal digest.

Only the validation function constructs
`ValidatedFeeDistributionConfigurationClaimV2`. Its constructor capability is
module-private and is registered with the FCIS structural checker. The type
name and contract explicitly deny protocol authority.

## 3. Canonical roots

Schema IDs:

```text
zenodex/fcis/fee-distribution/policy/v2
zenodex/fcis/fee-distribution/configuration-body/v2
zenodex/fcis/fee-distribution/configuration-claim/v2
zenodex/fcis/fee-distribution/validated-configuration-claim/v2
```

The configuration-body projection has this exact field set:

```text
chain_deployment_id
configuration_version
fee_distribution_domain_id
policy_root
policy
activation_sequence
algorithm_version
accepted_language_version
```

The claim and validated-claim projections have:

```text
body
configuration_root
```

Canonical bytes use the existing canonical JSON envelope:

```json
{"schema":"<schema-id>","value":<closed projection>}
```

Roots are:

```text
policy_root =
  sha256(
    domain_sep("fee_distribution_policy", version=2)
    || canonical_policy_envelope_v2
  )

configuration_root =
  sha256(
    domain_sep("fee_distribution_configuration", version=2)
    || canonical_configuration_body_envelope_v2
  )
```

`configuration_root` does not appear in the configuration-body preimage. A
future authenticated wrapper will additionally retain the expected version
observed from committed configuration for publication binding.

## 4. Verification relation

Verification applies this precedence:

1. top-level claim has the exact claim type;
2. body and nested policy revalidate structurally;
3. algorithm version equals the frozen SRGD version;
4. accepted-language version equals the frozen V2 language;
5. embedded `policy_root` equals a fresh recomputation;
6. `configuration_root` equals a fresh recomputation;

Success returns the controlled non-authoritative validated claim. Failure
returns one closed rejection with no validated claim:

```text
WRONG_EXACT_TYPE
INVALID_CLAIM
ALGORITHM_VERSION_MISMATCH
ACCEPTED_LANGUAGE_VERSION_MISMATCH
POLICY_ROOT_MISMATCH
CONFIGURATION_ROOT_MISMATCH
```

Every rejection carries a stable tuple path.

## 5. Admission and construction

Untrusted maps remain at the decode edge. The source-owned closed admission
profile registers:

```text
FeeDistributionPolicySourceV2
FeeDistributionConfigurationBodySourceV2
FeeDistributionConfigurationClaimSourceV2
```

The sole admission combinator enforces exact field sets, exact scalar types,
depth, node, collection, string, U256, and canonical-byte bounds.

Admission constructs a claim. It cannot construct the validated result or any
authenticated wrapper. The validator independently recomputes both roots after
admission.

## 6. Python/Rust refinement

Python and Rust implement the same validation relation:

```text
field order
schema IDs
canonical UTF-8 JSON bytes
domain separators
root computations
algorithm and accepted-language comparisons
rejection precedence
```

Rust uses `BigUint` for the U256 fields. Python rejects `bool` as an integer.
Both languages accept the complete U256 range.

A shared source-pinned fixture binds:

```text
policy bytes and root
configuration-body bytes and root
claim and validated-claim bytes
valid controlled non-authoritative result
each semantic root or algorithm substitution rejection
a self-consistent attacker-selected policy that remains validated-only
U256 maximum activation sequence
Unicode scalar identifiers
```

## 7. Structural isolation

Fresh configuration modules may import only canonical encoding, the closed
admission machinery, and the Checkpoint-A policy value/codec/schema.

They must not import:

```text
settlement or strong-settlement modules
balances, pools, or state transitions
step evaluator, decisions, receipts, commit bundle, outbox, or shell
legacy fee accumulator or rejected fee-custody experiments
mounted runtime paths
```

The mounted files remain byte-identical:

```text
src/core/dex.py
src/integration/dex_engine.py
src/core/route_settlement.py
src/state/legacy_state_snapshots.py
```

## 8. Required tests

1. Closed admission rejects unknown, missing, duplicate, broad, Boolean, and
   out-of-range fields.
2. A valid claim produces one controlled validated claim carrying no authority.
3. Policy-root, configuration-root, algorithm, and accepted-language
   substitutions each fail at their intended semantic check.
4. Hostile post-construction mutation is caught by verifier recomputation.
5. Direct validated construction fails, and B1A defines no authenticated type
   or builder.
6. Python and Rust consume the same canonical fixture.
7. Structural mutations kill private-token capture, mounted imports, omitted
   registry IDs, and premature authenticated-configuration authority.
8. The four pre-mount profiles remain green.
9. `final-mount` remains fail closed without suppression or allowlist widening.

## 9. Corrective authority evidence

The first uncommitted B1 implementation incorrectly constructed an
`AuthenticatedFeeDistributionConfigurationV2` after checking only values and
roots supplied by the same claim. The minimized deterministic reproducer chose:

```text
chain_deployment_id = attacker:deployment
fee_distribution_domain_id = attacker-domain
buyback destination = mallory
weights = (10_000, 0, 0)
```

It recomputed both roots and copied the body version into the claimed expected
version. The old verifier returned the authenticated type. This proved that
canonical self-consistency is insufficient to establish deployment authority.

The uncommitted implementation was corrected before staging. The Mallory case
now returns only `ValidatedFeeDistributionConfigurationClaimV2`. The structural
checker rejects reintroduction of the premature authenticated class, token, or
builder. Research Kernel run
`zenodex-fcis-m5-p4b5a-config-authority-20260728` records the counterexample,
corrected hypothesis, evidence, dependency, and refutation plan.

## 10. Promotion boundary

Passing B1A permits the later committed-configuration checkpoint to consume one
canonical validated claim. It does not permit the settlement evaluator to use
that claim as policy authority. B1B must compare it against chain/deployment ID,
configuration root, and version obtained from authenticated committed pre-state
or an equivalent shell witness before introducing
`AuthenticatedFeeDistributionConfigurationV2`. Settlement lineage, value
movement, publication, and mounting remain unauthorized.
