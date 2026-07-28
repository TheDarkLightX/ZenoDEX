# FCIS M5-P4B5A B1B committed-configuration authority correction

**Status:** `PROPOSED_REVIEW_ONLY_REVISION_2`

**Exact source head inspected:**
`9fd7dd78ff410c72e9f40de7055da596f392a1d6`

**Research Kernel run:**
`zenodex-fcis-m5-p4b5a-config-authority-20260728`

**Authority mount:** prohibited

**Revision 2:** The first draft placed the full configuration claim in state.
The smaller reviewed candidate below commits only a configuration root and
version in an exact state header. The configuration body remains an explicit
content-addressed input whose integrity is checked against that header.
Revision 2 was prepared on documentation-only base
`c4b9fbd38c8ba758ebd99e815a2f9dccef7e679f`.

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

V2 must commit a compact fee-configuration anchor and protocol sequence inside
the same state root as economic state.

```text
FCISAuthorityHeaderV2(
    sequence,
    fee_distribution_configuration_root,
    fee_distribution_configuration_version,
)
```

```text
FCISCommittedStateV2(
    authority_header,
    balances,
    pools,
    lp_balances,
    nonces,
    vault,
    oracle,
    fee_apportionment,
    perps,
)
```

The normative state order above replaces the eight-field list in section 10.
The V1 scalar `fee_accumulator` and V2 `fee_apportionment` fields remain
mutually exclusive.

The complete exact configuration claim remains a separate explicit input:

```text
FeeDistributionConfigurationClaimV2(
    body,
    configuration_root,
)
```

The V2 state admission profile validates the exact header. Evaluation
recomputes `policy_root` and `configuration_root` from the separate claim and
requires exact equality with the root and version committed in the header.
Any registry, file, request, cache, or proof packet that supplies the claim is
an untrusted content source. A missing body fails closed; a substituted body
cannot match the committed root.

## 3. Authority relation

The functional core derives one controlled state-bound value only from the
exact admitted pre-state:

```text
bind_active_fee_configuration_v2(
    pre_state,
    validated_configuration_claim,
    expected_pre_root,
)
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
6. require the claim root to equal
   `pre_state.authority_header.fee_distribution_configuration_root`;
7. require the claim version to equal
   `pre_state.authority_header.fee_distribution_configuration_version`;
8. require `body.activation_sequence <= pre_state.authority_header.sequence`;
9. construct the state-bound value through a private capability;
10. expose the capability only to the exact V2 evaluator and commit verifier.

`StateBoundFeeDistributionConfigurationV2` is the core value. The term
`AuthenticatedFeeDistributionConfigurationV2` is reserved for a shell value
whose pre-root was observed as current at the publication boundary. A
state-bound value cannot independently authorize a commit.

## 4. Sequence law

For every committed accept or committed failure:

```text
next.authority_header.sequence = pre.authority_header.sequence + 1
```

For ordinary rejection:

```text
no successor exists
```

The transition rejects when `pre.authority_header.sequence` is the maximum
U256 value. The header is part of canonical snapshot bytes and the snapshot
root. This gives
every committed transition a distinct root even when all economic fields are
otherwise equal and closes the simple ABA shape in the reference model.

Configuration activation uses the pre-state sequence. A configuration with:

```text
activation_sequence > pre.authority_header.sequence
```

is inactive and cannot authorize fee distribution.

## 5. Configuration update law

The first V2 migration installs one already-active configuration:

```text
configuration_version >= 1
activation_sequence <= initial_v2_authority_header.sequence
```

A later configuration update must be a separately authorized protocol
transition. Its minimum laws are:

```text
new_configuration.body.configuration_version =
  active_configuration.body.configuration_version + 1
new_header.fee_distribution_configuration_version =
  new_configuration.body.configuration_version
new_header.fee_distribution_configuration_root =
  recomputed_root(new_configuration_body)
new_configuration.body.chain_deployment_id =
  active_configuration.body.chain_deployment_id
new_configuration.body.fee_distribution_domain_id =
  active_configuration.body.fee_distribution_domain_id
new_configuration.body.activation_sequence =
  update_successor.authority_header.sequence
```

Domain split, merge, reuse, and ordinary rotation remain forbidden under the
SRGD-v1 domain topology. A new algorithm or accepted-language version requires
a separately reviewed migration.

## 6. Single-CAS publication

The state root commits:

```text
economic state
+ fee-apportionment state
+ fee-configuration root and version
+ protocol sequence
```

Therefore the existing expected-pre-root comparison detects stale economic
state and stale configuration together. `CommitBundleV2` carries the expected
configuration root and version as explicit audit evidence and checks that both
equal the authority header in the expected pre-state.

An external configuration store would require an independently proved atomic
comparison over both:

```text
(expected_pre_state_root, expected_configuration_version)
```

No such production dual-key transaction or independently authenticated
external anchor exists in the current repository. The root-bound header avoids
that dependency.

## 7. Canonical schemas

The correction adds or amends these V2 schemas:

```text
zenodex/fcis/state/committed-dex-state/v2
zenodex/fcis/state/committed-dex-snapshot/v5
zenodex/fcis/state/authority-header/v2
zenodex/fcis/fee-distribution/state-bound-configuration/v2
```

Snapshot-v5 canonical order follows the nine fields in section 2. The complete
configuration claim is encoded through its existing canonical V2 codec and is
not duplicated inside state. The state-bound wrapper binds:

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

1. A self-consistent Mallory claim whose root is absent from the committed
   authority header cannot produce a state-bound value.
2. A claim with the correct root but wrong deployment ID rejects.
3. A claim from another pre-state with the same configuration rejects on the
   pre-root binding.
4. `activation_sequence = pre.authority_header.sequence + 1` rejects.
5. `activation_sequence = pre.authority_header.sequence` accepts.
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
state-bound construction without exact header root and version equality
```

## 9. Checkpoint sequence

```text
B1B-0  independent review of this correction
B1B-1  exact authority-header values and Python/Rust canonical codecs
B1B-2  state admission, root binding, and Python/Rust golden vectors
B1B-3  controlled state-bound configuration derivation and mutations
B1B-4  candidate, receipt, patch, and bundle bindings
B1B-5  reference commit sequence/configuration race evidence
```

No step mounts runtime authority. The production shell and datastore remain a
separate promotion gate.

## 10. Non-claims

This correction does not prove governance authorization, production datastore
linearizability, crash recovery, external delivery, content availability, or a
mounted V2 state migration. It does not authorize configuration construction
from an API request, environment variable, local file, or caller-supplied
context. The configuration root proves integrity and identity after matching
the state header; it does not prove that the body will remain available.

The B1A claim-validation result at commit `9fd7dd78` remains valid. B1B adds the
missing provenance relation; it does not reinterpret self-consistency as
authority.
