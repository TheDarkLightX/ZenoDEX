# ZRPF Spot Represented Value V1 Specification

Status: implemented pure reference kernel, no value receipt evidence
Date: 2026-07-11

## Purpose

Semantic Epoch V1 authenticates a bounded ordered leaf sequence and rejects
duplicate source claims, semantic sources, and tasks. It commits each leaf's
state and asset roots without interpreting their contents. Spot Represented
Value V1 opens those commitments and checks one narrow value law.

The intended receipt-authenticated claim is:

> One ordered sequence of governed Spot adapter leaves opens to exact legacy
> external-effect rows, exact raw state endpoints, one lane, one atom unit, and
> ordered unique leaf transaction-root commitments. Partial recursive nodes carry checked
> per-asset residual totals. The closed root balances every represented asset
> and obeys the proposed, scope-bound Spot faucet-mint grant set.

The claim covers authenticated represented external-effect rows. It does not
establish complete internal balance coverage, external custody, complete token
supply, or settlement correctness.

## Implemented boundary

The implementation preserves Semantic Epoch V1 and NodeJournal V3 bytes,
hashes, image IDs, and retained receipts. Its public entry points are:

```text
propose_spot_value_subtree_v2
merge_spot_value_subtrees_v2
close_spot_represented_value_epoch_v1
compose_spot_represented_value_v1
```

`SpotValueSubtreeSummaryV2` is a sealed in-memory reference type. It carries
the bounded flattened witness needed to recompute a canonical summary during
merge. It is not a serialized journal ABI, authenticated receipt, or
ledger-admissible object.

## Bounds

```text
source kind                         Spot V1 only
leaves per partial summary          1..=64
leaves per closed V1 root           1..=8
operations per compatibility leaf  1
asset rows per leaf                 0..=16
asset rows per summary              0..=128
represented rows per closed root    1..=128
mint grants                         0..=128
lane ID bytes                       1..=128, restricted ASCII
state lanes                         exactly 1
state-root schemes                  exactly 1 pinned Spot scheme
asset encoding                      lowercase 0x plus 64 hex digits
atom unit                           one pinned Spot raw-u128 atom unit
supply effects                      governed Spot faucet mint only
```

An empty row vector is a valid opening for one no-effect leaf. A closed value
root must contain at least one represented row.

The exact asset-string byte bound is enforced before this kernel rehashes the
legacy row vector. A future guest must also bound the complete serialized input
before allocation and decoding.

## Authority progression

The future receipt-bearing guest must preserve this order:

```text
governed expected adapter identity
  -> verify exact child receipt security profile
  -> exact-decode authenticated NodeJournalV4 bytes
  -> reconstruct the governed Spot-only semantic leaf
  -> bind exact asset rows to NodeCommitmentsV3.asset_delta_root
  -> bind raw lane/pre/post openings to domain-separated state roots
  -> validate exact asset IDs and atom unit
  -> validate proposed mint grants and accumulate checked totals
  -> compose partial residual summaries
  -> enforce closure only at the governed complete root
  -> exact-compare the ledger-owned expected statement
  -> commit exact canonical output bytes
```

The current kernel begins after `ProposedSemanticLeafV1` values exist. Focused
tests cross the real Spot transition derivation for faucet and native-sync rows,
then use the existing V1 adapter projection. They do not authenticate RISC0
receipts.

## State law

The V1 adapter commits singleton state vectors under different domains:

```text
pre  = H(PRE_DOMAIN,  [(lane_id, raw_pre_state_root)])
post = H(POST_DOMAIN, [(lane_id, raw_post_state_root)])
```

The kernel recomputes both domain-specific commitments. It separately checks
raw continuity:

```text
for i in 0..n-1:
    raw_post_state_root[i] == raw_pre_state_root[i + 1]
```

Every leaf uses one exact bounded lane ID. A leaf with represented rows changes
its raw state root. Leaf transaction-root commitments are unique within the
summary. This does not open or deduplicate the individual transactions inside a
batch commitment. Partial summary merge additionally requires adjacent
partitions and matching raw endpoints.

The endpoints are:

```text
subtree_pre_state_root  = raw_pre_state_root[first]
subtree_post_state_root = raw_post_state_root[last]
```

Only a summary starting at ordinal zero may enter the V1 closed-root finalizer.
Ledger compare-and-swap remains a separate obligation.

## Asset identity and units

Legacy rows carry asset strings. This profile accepts one encoding:

```text
"0x" || 64 lowercase hexadecimal digits
```

The decoded 32 bytes form `asset_id`. Uppercase, symbolic, shortened, Unicode,
and otherwise aliased names reject even when the legacy leaf root authenticates
them.

All rows use:

```text
spot_atoms_unit_id_v1 = H("spot_raw_u128_atoms")
```

This profile excludes arbitrary legacy Spot asset names. The real-transition
faucet parity test uses a canonical 32-byte Spot asset name. A future asset
registry profile needs a governed mapping from each accepted legacy name to
`(asset_id, atoms_unit_id)`.

zUSD `_e8`, perps collateral units, and future unit conversions require new
profiles with explicit conversion and rounding laws.

## Composable represented-flow law

Legacy row columns map as follows:

```text
debit_atoms            -> outflow_atoms
credit_atoms           -> inflow_atoms
authorized_mint_atoms  -> issued_atoms
authorized_burn_atoms  -> destroyed_atoms
```

A partial subtree carries all four checked `u128` totals per asset. Merge is
component-wise checked addition:

```text
F(A || B) = F(A) + F(B)
```

The canonical flattened summary is associative:

```text
merge(merge(A, B), C) == merge(A, merge(B, C))
```

Partial subtrees may be imbalanced. The closed root alone enforces, for every
asset:

```text
outflow_atoms + issued_atoms
    == inflow_atoms + destroyed_atoms
```

All column accumulations and both side additions reject overflow. Arithmetic
never wraps and never uses field-modular equality.

Ordinary rows require zero mint, burn, and authority root. All-zero rows reject.
Rows remain sorted and unique under the exact legacy codec. Duplicate assets
across leaves are aggregated by canonical asset ID.

## Mint authorization

A Spot mint row has this exact shape:

```text
outflow_atoms   = 0
inflow_atoms    = issued_atoms > 0
destroyed_atoms = 0
```

The kernel recomputes the legacy authority root from:

```text
public_policy_hash
lane_kind = "spot"
canonical legacy asset name
effect = "mint"
```

The proposed policy supplies sorted unique grants:

```text
SpotMintAuthorityGrantV1 {
    asset_id,
    legacy_authority_root,
    max_atoms_per_value_root,
}
```

Each cap is positive. Aggregate use per asset cannot exceed the cap within one
closed value root. Every mint remains a distinct authority-use record.

The cap is not an epoch-global fact. Two independently accepted roots for the
same epoch can each consume the full cap. Durable admission must enforce one
governed complete root per `(domain, epoch, public_policy_hash)` or maintain an
equivalent atomic cumulative-use ledger.

The Spot V1 source has no authorized-burn path. Burn rows reject.

## Commitments

The reference kernel derives:

```text
base_semantic_epoch_root
value_profile_id
accounting_domain_id
atoms_unit_id
state_root_scheme_id
semantic_leaf_records_root
ordered_transaction_roots_root
state_chain_root
authority_grants_root
asset_flows_root
authority_uses_root
value_subtree_root
```

`value_subtree_root` binds the exact profile, units, state scheme, scope,
partition, lane, raw endpoints, counts, ordered leaf and leaf transaction roots,
state chain, proposed grants, residual flows, and authority uses. It hashes the
canonical flattened summary, so valid parenthesizations have the same root.

The tree-independent `semantic_value_root` binds the base semantic epoch root,
scope, lane, endpoints, counts, and complete value commitments. The separate
`proposal_hash` also includes the topology-sensitive base proposal hash.

Structural aggregate `asset_delta_root` values remain roots of child roots.
They are topology-dependent audit commitments and have no numeric-total
interpretation.

## Fixed vectors

The Rust tests independently mirror the profile hash framing and pin these
values:

```text
atoms_unit_id
  75b2937b0224d9accb8cf6d3c6f43dcf381dce412720afa5da982f797ce264fb
accounting_domain_id
  9486db0738818c3bd2d1009516d64861481d03de5d0e7f0b294b0eb41dcde316
state_root_scheme_id
  b01a20d7e5d1024289330875c2c6521632a57b82295ae7aa2eb3792c8bb7314a
value_profile_id
  20f73c0589af1ff8e8519c4cf522cb423a06589b19173b6deccfe7c386129c6d
```

The same test pins a two-leaf subtree root, semantic value root, and proposal
hash. Any intentional ABI change requires a version and domain review before
updating vectors.

## Outer expected statement

A future sealed verifier receives a governance or ledger-owned expected type
and exact-compares at least:

```text
expected_scope
expected_lane_id_hash
expected_state_root_scheme_id
expected_ordered_transaction_roots_root or schedule_root
expected_raw_pre_state_root
expected_raw_post_state_root
expected_authority_grants_root
expected_base_semantic_epoch_root
expected_semantic_value_root
```

The expected adapter program identity and receipt security profile come from
governed constants or a separately authenticated manifest. A journal cannot
select its own expected verifier identity. Caller-selected matching values have
no ledger authority.

## Self-similar recursion

`SpotValueSubtreeSummaryV2` demonstrates the required algebra. The future
serialized journal remains unfrozen. A candidate additive form is:

```text
NodeJournalV4 {
    structural: NodeJournalV3,
    semantic_subtree: SemanticSubtreeV2,
    child_semantic_journals_root,
}
```

Every parent verifies immediate child receipts, exact-decodes the child V4
journals, opens the bounded flattened semantic slice, checks that each slice
matches its child commitment, merges the slices, and derives the parent summary.
Hashing child semantic roots alone cannot establish cross-child uniqueness,
state continuity, mint-cap use, or represented-value conservation.

The child claim and child-journal roots must hash exact canonical V4 bytes.
Embedding `NodeJournalV3` preserves its fields and validation rules. Reusing a
complete V3 child-journal hash as the V4 child binding would leave the semantic
wrapper outside the authenticated recursive statement.

V4 domains and bytes remain unfrozen until the exact child summary codec,
bounds, and receipt guest are reviewed.

## Parallel composition

This profile is sequential. Current `write_set_root` values are opaque and do
not prove key-level disjointness.

A future parallel profile must define one explicit law:

1. Governed state-shard ownership with per-lane continuity, a complete lane
   set, and exact-once cross-lane messages.
2. Shared-root authenticated patches with read/write sets, old/new values,
   Merkle proofs, and rejection of all write/write and read/write conflicts.

Current commitments cannot be reinterpreted as either certificate.

## Implemented evidence

Focused Rust tests cover:

- partial debit and credit children with closure only at the complete root;
- nonzero-origin subtree construction and closed-root rejection;
- associative three-subtree regrouping and topology-independent value roots;
- raw state continuity, discontinuity, PRE/POST domain separation, and opening
  substitutions;
- exact legacy row-root binding, row mutation, row bounds, and asset codecs;
- checked flow, balance-side, and mint-use overflow;
- one-atom imbalance, zero rows, detached authorities, mint/burn shape errors,
  and nonchanging represented state;
- duplicate transaction roots, mixed lanes, base mismatch, and swapped
  openings;
- grant order, grant count, authority root, missing grant, per-root cap, and
  cumulative use;
- grant-policy substitution at both subtree merge and closed-root finalization;
- two same-epoch closed roots independently consuming a full cap, documenting
  the durable-admission blocker;
- real Spot faucet and native-sync transition derivation through the adapter;
- malformed real Spot faucet rejection;
- an independently mirrored profile hash and fixed root vectors.

## Explicit non-claims

This tranche does not establish:

- a RISC0 Spot value guest, receipt, image ID, or proof replay;
- receipt-authenticated origin for the pure proposal inputs;
- a canonical serialized V4 value journal;
- independently mergeable serialized child summaries;
- a ledger-owned expected statement or canonical schedule;
- individual transaction IDs, nonce-root continuity, or transaction exact-once replay protection;
- an epoch-global mint cap or one-root-per-epoch admission;
- complete internal Spot balance, custody, or token-supply coverage;
- arbitrary legacy Spot asset-name coverage;
- zUSD, perps, burn, liquidation, stability-pool, or proof-market coverage;
- parallel conflict freedom, schedule validity, or write-set authority;
- receipt, message, carry, or data-availability semantics;
- durable atomic ledger admission;
- release, settlement, production, privacy, or throughput authority.

All corresponding claim flags remain false.

## Next executable step

Define the exact bounded `SemanticSubtreeV2` and `NodeJournalV4` codecs from the
reference algebra. Add a sealed expected-statement type that pins lane, ordered
transactions or schedule, endpoints, grants, scheme, base root, and value root.
Then implement a guest that reaches this kernel only after governed child
receipt verification and exact V4 journal recomposition.

Fresh Spot source, adapter, semantic-node, and value-root Succinct receipts are
required after those boundaries pass adversarial review. Existing retained
Semantic Epoch V1 evidence cannot be promoted because its harness required
empty asset-row metadata.
