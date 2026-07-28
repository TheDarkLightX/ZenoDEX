# FCIS M5-P4B5A B1B committed-configuration authority correction

**Status:** `PROPOSED_REVIEW_ONLY`

**Exact source head inspected:**
`9fd7dd78ff410c72e9f40de7055da596f392a1d6`

**Research Kernel run:**
`zenodex-fcis-m5-p4b5a-config-authority-20260728`

**Authority mount:** prohibited

## 1. Result

The SRGD-v1 amendment does not yet specify an authority source from which B1B
can safely construct an active fee-distribution configuration.

Section 8 requires policy and domain authority to come from committed
deployment configuration. It also says that `FCISCommittedStateV2`, receipts,
patches, and commit bundles bind that configuration. Section 10 defines
`FCISCommittedStateV2` as the eight V1 state namespaces with only the scalar
fee accumulator replaced by V2 fee apportionment state. That field list has no
configuration identity and no authenticated sequence against which
`activation_sequence` can be checked.

Implementing the authenticated wrapper from the current text would repeat the
authority error corrected in B1A: caller-selected values could be made
self-consistent by recomputing their hashes.

## 2. Required correction

V2 must commit the active fee-distribution configuration and protocol sequence
inside the same state root as economic state.

```text
FCISCommittedStateV2(
    sequence,
    balances,
    pools,
    lp_balances,
    nonces,
    vault,
    oracle,
    fee_apportionment,
    perps,
    fee_distribution_configuration,
)
```

The normative field order above replaces the eight-field list in section 10.
The V1 scalar `fee_accumulator` and V2 `fee_apportionment` fields remain
mutually exclusive.

The configuration field contains the complete exact claim:

```text
FeeDistributionConfigurationClaimV2(
    body,
    configuration_root,
)
```

The V2 state admission profile recomputes `policy_root` and
`configuration_root`. Storing only an external lookup key or root is
insufficient because transition replay would then depend on an uncommitted
registry response.

## 3. Authority relation

The functional core derives one controlled state-bound value only from the
exact admitted pre-state:

```text
bind_active_fee_configuration_v2(pre_state, expected_pre_root)
  -> Reject(reason)
   | StateBoundFeeDistributionConfigurationV2(
         pre_state_root,
         pre_state_sequence,
         body,
         configuration_root,
     )
```

The binding relation must:

1. require exact `FCISCommittedStateV2`;
2. recursively revalidate all state fields;
3. recompute the snapshot-v5 bytes and pre-state root;
4. require the recomputed root to equal `expected_pre_root`;
5. revalidate the exact configuration claim and both roots;
6. require `body.activation_sequence <= pre_state.sequence`;
7. construct the state-bound value through a private capability;
8. expose the capability only to the exact V2 evaluator and commit verifier.

`StateBoundFeeDistributionConfigurationV2` is the core value. The term
`AuthenticatedFeeDistributionConfigurationV2` is reserved for a shell value
whose pre-root was observed as current at the publication boundary. A
state-bound value cannot independently authorize a commit.

## 4. Sequence law

For every committed accept or committed failure:

```text
next.sequence = pre.sequence + 1
```

For ordinary rejection:

```text
no successor exists
```

The transition rejects when `pre.sequence` is the maximum U256 value. The
sequence is part of canonical snapshot bytes and the snapshot root. This gives
every committed transition a distinct root even when all economic fields are
otherwise equal and closes the simple ABA shape in the reference model.

Configuration activation uses the pre-state sequence. A configuration with:

```text
activation_sequence > pre.sequence
```

is inactive and cannot authorize fee distribution.

## 5. Configuration update law

The first V2 migration installs one already-active configuration:

```text
configuration_version >= 1
activation_sequence <= initial_v2_sequence
```

A later configuration update must be a separately authorized protocol
transition. Its minimum laws are:

```text
new.configuration_version = old.configuration_version + 1
new.chain_deployment_id = old.chain_deployment_id
new.fee_distribution_domain_id = old.fee_distribution_domain_id
new.activation_sequence = update_successor.sequence
```

Domain split, merge, reuse, and ordinary rotation remain forbidden under the
SRGD-v1 domain topology. A new algorithm or accepted-language version requires
a separately reviewed migration.

## 6. Single-CAS publication

The state root commits:

```text
economic state
+ fee-apportionment state
+ active fee-distribution configuration
+ protocol sequence
```

Therefore the existing expected-pre-root comparison detects stale economic
state and stale configuration together. `CommitBundleV2` also carries the
expected configuration version as explicit audit evidence and checks that it
equals the version in the expected pre-state.

An external configuration store would require an independently proved atomic
comparison over both:

```text
(expected_pre_state_root, expected_configuration_version)
```

No such production transaction or authenticated anchor exists in the current
repository. B1B must not assume it.

## 7. Canonical schemas

The correction adds or amends these V2 schemas:

```text
zenodex/fcis/state/committed-dex-state/v2
zenodex/fcis/state/committed-dex-snapshot/v5
zenodex/fcis/fee-distribution/state-bound-configuration/v2
```

Snapshot-v5 canonical order follows the ten fields in section 2. The complete
configuration claim is encoded through its existing canonical V2 codec. The
state-bound wrapper binds:

```text
pre_state_root
pre_state_sequence
configuration_root
configuration_version
chain_deployment_id
fee_distribution_domain_id
policy_root
activation_sequence
algorithm_version
accepted_language_version
```

Python and Rust must emit identical bytes for every state, configuration, and
state-bound wrapper vector.

## 8. Required falsification evidence

Before implementation promotion, preserve these negative cases:

1. A self-consistent Mallory claim outside the committed pre-state cannot
   produce a state-bound value.
2. A claim with the correct root but wrong deployment ID rejects.
3. A claim from another pre-state with the same configuration rejects on the
   pre-root binding.
4. `activation_sequence = pre.sequence + 1` rejects.
5. `activation_sequence = pre.sequence` accepts.
6. Configuration version substitution rejects.
7. Post-admission mutation of any nested policy or state field rejects during
   revalidation.
8. A configuration change racing a planned settlement makes the settlement
   bundle stale under the single pre-root CAS.
9. A committed no-economic-change transition still advances sequence and
   changes the state root.
10. V1 migration rejects nonzero legacy scalar dust and never admits both fee
    state families.

The structural checker must reject:

```text
public construction of StateBoundFeeDistributionConfigurationV2
configuration authority derived from request context
configuration lookup inside the functional core
an external configuration-version check without the pre-root check
state schemas containing both fee_accumulator and fee_apportionment
```

## 9. Checkpoint sequence

```text
B1B-0  independent review of this correction
B1B-1  exact V2 state/configuration values and canonical codecs
B1B-2  state admission, root binding, and Python/Rust golden vectors
B1B-3  controlled state-bound configuration derivation and mutations
B1B-4  candidate, receipt, patch, and bundle bindings
B1B-5  reference commit sequence/configuration race evidence
```

No step mounts runtime authority. The production shell and datastore remain a
separate promotion gate.

## 10. Non-claims

This correction does not prove governance authorization, production datastore
linearizability, crash recovery, external delivery, or a mounted V2 state
migration. It does not authorize configuration construction from an API
request, environment variable, local file, or caller-supplied context.

The B1A claim-validation result at commit `9fd7dd78` remains valid. B1B adds the
missing provenance relation; it does not reinterpret self-consistency as
authority.
