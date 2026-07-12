# ZRPF Value Node V4 Correct-by-Construction Specification

Status: implemented bounded leaf guest and temporary local Succinct receipt;
no ledger, release, or production authority
Date: 2026-07-11

## Purpose

Semantic Epoch V1 commits a canonical set of authenticated structural leaves.
Spot Represented Value V1 supplies the pure reference algebra for state
continuity, represented external-effect rows, issuance grants, residual flows,
and root closure. Value Node V4 defines the bounded public bytes that can carry
that semantic summary through a self-similar recursive tree.

This tranche establishes deterministic construction, strict decoding, one
verify-before-decode Spot value-leaf guest, and a sealed host receipt boundary.
A decoded V4 journal remains an untrusted protocol value. The fixed leaf lane
authenticates one exact retained adapter receipt under its pinned image, proves
the derived V4 journal, and binds the resulting receipt to the independently
derived expected bytes.

```text
untrusted bytes
  -> bounded sequence decoding
  -> exact adapter receipt verification inside the V4 guest
  -> semantic-witness interpretation and V3/V2/V4 self-consistency
  -> exact canonical NodeJournalV4
  -> Succinct V4 receipt
  -> host receipt, image, profile, manifest, record, and residual checks
  -> exact expected-journal typestate
  -> temporary local evidence only
```

Ledger-owned expectation, atomic admission, settlement, and release governance
remain later authority transitions.

## Compatibility

The implementation is additive under `zk/zrpf_protocol`. It does not change:

- `NodeJournalV3` fields or bytes;
- Semantic Epoch V1 proposal fields or bytes;
- existing RISC0 guest images or retained receipts;
- Spot Represented Value V1 hash domains;
- Firecracker replay or sandbox artifacts.

The V2 subtree root deliberately reuses the reference algebra's domains. An
independent temporary consumer reproduced the exact value-subtree root for an
ordinary debit/credit pair and a governed mint case.

## Bounds

```text
semantic subtree version             2
value node journal version            4
leaf records                          1..=64
asset-flow summaries                  0..=128
authority-use records                 0..=128
represented rows                      0..=128
immediate child journal hashes        0..=8
maximum SemanticSubtreeV2 bytes       60,000
maximum NodeJournalV4 bytes           65,536
```

The saturated test contains 64 leaf records, 128 asset flows, 128 authority
uses, and eight immediate child hashes. Its canonical subtree and V4 journal
remain within the declared byte caps.

## Semantic leaf record

Each `SemanticValueLeafRecordV2` commits:

```text
singleton partition
canonical Semantic Epoch V1 leaf hash
source-claim identity
semantic-source identity
task identity
PRE state-vector root
POST state-vector root
transaction root
effect root
asset-delta root
raw PRE state root
raw POST state root
```

The subtree constructor requires records to be dense in partition order. It
rejects duplicate source claims, semantic sources, tasks, and transaction
roots. Adjacent records satisfy:

```text
raw_post_state_root[i] == raw_pre_state_root[i + 1]
```

The first and final raw roots must equal the declared subtree endpoints.

## Residual represented flows

`SemanticAssetFlowV2` carries checked `u128` residual totals:

```text
asset_id
outflow_atoms
inflow_atoms
issued_atoms
destroyed_atoms
```

Flows are sorted and unique by exact 32-byte asset identity. An all-zero flow
rejects. Partial V4 nodes may remain imbalanced. The complete-root semantic
composer later enforces:

```text
outflow_atoms + issued_atoms
    == inflow_atoms + destroyed_atoms
```

`SemanticAuthorityUseV2` binds every represented issuance to:

```text
source_claim_id
leaf_ordinal
asset_id
atoms
legacy_authority_root
```

Authority uses are sorted by `(asset_id, leaf_ordinal, source_claim_id)`. Each
use must name the source claim at that exact ordinal. For every asset, checked
authority-use totals equal the residual `issued_atoms` total. Missing,
duplicated, reordered, out-of-partition, source-substituted, and overflowing
uses reject.

Grant caps remain an expected-policy and closed-root obligation. The codec
binds `authority_grants_root`; it does not decide which grant root is governed.

## SemanticSubtreeV2 commitments

Construction derives these values from bounded canonical records:

```text
semantic_leaf_records_root
ordered_transaction_roots_root
state_chain_root
asset_flows_root
authority_uses_root
value_subtree_root
```

`value_subtree_root` uses the existing Spot Represented Value V1/V2 hash law:

```text
H(
  value_profile_id,
  accounting_domain_id,
  atoms_unit_id,
  state_root_scheme_id,
  scope_hash,
  lane_id_hash,
  partition,
  raw endpoints,
  leaf and represented-row counts,
  semantic leaf root,
  ordered transaction root,
  state-chain root,
  authority-grants root,
  asset-flow root,
  authority-use root
)
```

Decoding recomputes every derived root. Caller-supplied matching roots cannot
skip record validation.

## Canonical semantic merge

`merge_semantic_subtrees_v2` accepts one through eight already validated child
subtrees in exact partition order. It requires equal profile, accounting,
unit, root-scheme, scope, lane, and authority-policy identities. Adjacent
partitions and raw state endpoints must be continuous.

The merge concatenates the bounded leaf records, sums each nonnegative asset
flow component with checked `u128` arithmetic, canonically orders authority
uses, and invokes the ordinary `SemanticSubtreeV2` constructor again. The final
constructor rechecks global source, semantic, task, and transaction uniqueness,
issued-atom equality with authority-use totals, all bounds, and every root.

For valid ordered children, the merge is associative wherever every invoked
merge stays within the one-to-eight child limit and cumulative semantic caps.
Its normalized state consists of:

```text
ordered leaf-record concatenation
per-asset component-wise addition
canonical authority-use ordering
checked represented-row addition
fixed shared metadata and outer endpoints
```

The tests compare direct, left-associated, and right-associated merges and
exercise the saturated eight-child, 64-leaf, 128-row, 128-flow boundary.
Receipt authentication remains outside this pure algebra.

Intermediate nodes derive a residual application statement as:

```text
H("zenodex.zrpf.spot_residual_application_statement.v4",
  semantic_subtree_canonical_hash)
```

The helper first requires the exact Spot value-profile, accounting-domain,
atoms-unit, and state-root-scheme identities. A self-consistent foreign-profile
subtree cannot receive the Spot residual domain label.

The ordinary two-leaf fixture has residual statement vector:

```text
a133121dac3163e6d107f9cd62d46ecf28f26382ff0f4e8ca0a3dd03aa016684
```

A final closed root instead carries the separately matched expected Spot
statement hash. The enclosing guest and outer verifier must enforce the node
role and expected-statement policy.

## NodeJournalV4

`NodeJournalV4` binds:

```text
journal_version = 4
exact validated NodeJournalV3 structural value
exact validated SemanticSubtreeV2
application_statement_hash
proof_profile_id
actual_program_id
proof_system_id
receipt_security_profile_id
verifier_parameters_root
derived verifier_id
derived semantic_statement_hash
program_manifest_root
ordered immediate child V4 journal hashes
derived child_semantic_journals_root
```

The semantic and structural values must have equal partitions, leaf counts,
and scope hashes. A V3 leaf requires zero child V4 hashes. A V3 aggregate
requires exactly its declared immediate child count. Duplicate child V4 hashes
reject.

The child list is retained alongside its root. This lets strict decoding
recompute the root and prevents an internally inconsistent journal from
crossing the codec boundary. A future guest must additionally authenticate
each exact child journal before using the list.

## Verifier identity

V4 corrects the narrower V3 verifier identity by deriving:

```text
verifier_id = H(
  actual_program_id,
  proof_profile_id,
  proof_system_id,
  receipt_security_profile_id,
  verifier_parameters_root,
  journal_version
)
```

Changing any component changes the verifier ID, semantic statement, and V4
journal hash. Decode-time relabeling rejects.

The semantic statement additionally binds:

```text
V3 structural journal hash
V2 semantic subtree hash
application statement hash
V4 proof and verifier identity
program manifest root
child semantic journal root
```

This keeps proof topology separate from the topology-independent value-subtree
root. Reordering child hashes preserves the semantic value root and changes
the V4 statement and journal hashes.

## Decoder boundary

Both exact decoders apply:

1. nonempty total-byte bounds;
2. per-sequence bounds during Serde visitation, before `Vec` allocation;
3. strict typed deserialization;
4. no trailing bytes;
5. complete self-consistency validation;
6. exact canonical re-encoding equality.

The bounded sequence visitors cover leaf records, asset flows, authority uses,
and child semantic journal hashes. Tests replace a canonical Postcard sequence
length with an excessive encoded count and require decode rejection.

## Disaster-state closures

| Disaster state | Current closure |
| --- | --- |
| duplicate semantic identity hidden across children | flattened record uniqueness, guarded construction |
| discontinuous raw state chain | adjacent endpoint equality, guarded construction |
| issuance without an authority-use record | exact per-asset issuance/use equality |
| child V4 omission or duplication | exact immediate count and duplicate rejection |
| structural scope or partition relabeling | V3/V2 equality checks |
| application statement hash relabeled after construction | semantic-statement and canonical-hash recomposition reject |
| child semantic metadata, order, or state chain differs | canonical merge rejects before parent construction |
| global identity duplicated across otherwise valid children | parent constructor rechecks flattened uniqueness |
| child flow sum overflows | checked component addition rejects |
| verifier backend or parameters relabeled | V4 verifier-ID derivation |
| stored derived root differs from records | decode-time root recomposition |
| hostile sequence length triggers large allocation | bounded sequence visitor |
| canonical bytes gain trailing or alternate encoding | exact re-encoding equality |

These are protocol-shape closures. Cryptographic child authentication remains
assigned to the future guest.

## Implemented evidence

The focused protocol suite covers:

- exact V2 and V4 round trips;
- every truncated prefix;
- trailing and nonminimal Postcard forms;
- oversized total bytes and oversized sequence lengths;
- state discontinuity and endpoint substitution;
- duplicate source, semantic, task, and transaction identities;
- flow and authority-use order, bounds, source binding, and issuance totals;
- V3/V2 partition, leaf-count, and scope equality;
- application-statement hash changes alter both derived V4 hashes;
- associative canonical merge, metadata/order/state failures, global duplicate
  rejection, checked overflow, and the saturated eight-child boundary;
- child count, child duplication, child order, and child-root binding;
- proof-system, receipt-security-profile, verifier-parameter, program,
  profile, and manifest relabeling;
- bounded byte mutation with the rule that any accepted mutation changes the
  canonical journal hash;
- independent mirror checks for V4 verifier, statement, and journal hashing;
- exact V1/V4 root parity for ordinary flows and governed mint authority uses;
- wrong-projection and off-origin subtree rejection before sealed matching;
- sealed expected-statement hash wiring into a pure V4 journal proposal;
- fixed hash vectors;
- a saturated maximum-size construction.

Current fixed vectors for the two-leaf fixture are:

```text
value_subtree_root
  d95434b68beecb47a87cb1875e4cbd1ba0ae17382ea0a0ed74c290e63794f30a
semantic_subtree_hash
  918e52100c997049adf8971bf5749a8d4a05dd1be616b71ab84a807e18e71f8f
verifier_id
  0d0ffc1ab18d49281d24178730b65efd5bf5e6f4c08098eaa9d2b3e2814422f1
semantic_statement_hash
  2e39deccf78b15d00e9a4bb093885d10a230e0fc9aa6b221c6be28de11780d75
node_journal_hash
  210af1ef25c1f027ec0e0823df534fd6a1932cf73e5df959139157b7f1e35028
```

## Explicit non-claims

This tranche does not establish:

- a release-governed or reproducibly built V4 image;
- proof regeneration for the retained Spot source or V1 adapter receipts;
- receipt-authenticated V4 aggregation beyond the one fixed residual leaf;
- a ledger-governed V4 program, policy, grant set, or expected statement;
- complete-root asset conservation or governed mint-cap enforcement;
- receipt, message, schedule, carry, or data-availability composition;
- durable atomic ledger admission;
- public replay, release, settlement, production, privacy, or throughput
  authority.

All corresponding authority claims remain false.

The fixed receipt proves a zero-row residual leaf with unchanged raw state. Its
application statement is deterministically rederived from the authenticated
subtree. A future complete-root verifier and atomic admission boundary must
compare the closed statement with a ledger-owned expectation before it gains
economic authority.

## Next executable step

The fixed ordinal-zero lane now derives `SemanticSubtreeV2` from an exact
retained Spot source and adapter receipt, recomputes the empty row root, proves
the V4 guest, crosses `ExactSpotValueLeafReceiptV4`, and rejects an exact
single-word Succinct seal mutation. The temporary receipt is 601,394 bytes with
SHA-256
`794a69746b3f833f56e15c968c16ab7d4ee9089f555eb210d38a1c0ea37d18c7`.

The next executable sequence is:

1. retain the fixed leaf receipt, replay, mutation, source closure, and exact
   claim boundary in a checker-governed evidence bundle;
2. define the V4 aggregate witness codec with the same bounded sequence
   discipline;
3. implement an aggregate guest that verifies every exact V4 child receipt
   before semantic merge;
4. close the complete root against the ledger-owned expected statement;
5. generate a nonempty ordinary-flow leaf, a governed-mint leaf, a multi-leaf
   aggregate receipt, and exact negative controls.
