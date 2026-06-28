# ZenoDEX Sealed-Bid Apportionment Breakthrough - 2026-06-28

## Executive Result

The marginal bucket can be certified as largest-remainder apportionment with quota bounds and deterministic tie order, and the same certificate exposes a split-bid vulnerability when multiple commitments per bidder are admitted independently.

This is a research certificate and mechanism-design refuter. Runtime sealed-bid settlement is unchanged.

- Spec: `src/tau_specs/recommended/sealed_bid_marginal_bucket_certificate_v1.tau`
- Tau replay ok: `True`
- Tau version: `Tau Language Framework version 0.7.0-alpha (401d756b)`
- Certificate cases: `5`
- Mutation rejections: `4`

## Certificate Cases

| case | verified | clearing price | marginal supply | single-bidder scope | marginal fills |
| --- | --- | ---: | ---: | --- | --- |
| `quota_parity` | `True` | `110` | `5` | `True` | `[['alice', 'alice-commitment', 2], ['bob', 'bob-commitment', 3]]` |
| `same_remainder_tie_order` | `True` | `100` | `2` | `True` | `[['alice', 'a-commitment', 1], ['bob', 'b-commitment', 1]]` |
| `full_prefix_then_marginal` | `True` | `100` | `2` | `True` | `[['bob', 'bob-mid', 1], ['carol', 'carol-mid', 1]]` |
| `duplicate_occurrence_index` | `True` | `110` | `2` | `False` | `[['alice', 'same-commitment', 1], ['alice', 'same-commitment', 1]]` |
| `split_bid_witness` | `True` | `100` | `2` | `False` | `[['alice', 'a-commitment', 1], ['alice', 'b-commitment', 1]]` |

## Split-Bid Witness

- Base Alice fill: `1`
- Split Alice fill: `2`
- Owner-consolidated Alice fill: `1`

largest-remainder marginal buckets are not split-bid invariant when multiple commitments per bidder are admitted independently

Require one marginal-bucket reveal per bidder or apportion by bidder_id before distributing owner fills across commitments.

## Mutation Checks

| mutation | rejected | error |
| --- | --- | --- |
| `bad_domain_hash` | `True` | `domain hash mismatch` |
| `bad_quota_bound` | `True` | `marginal fill total mismatch` |
| `private_quantity_leak` | `True` | `public receipt rejected: private_field_leaked_quantity` |
| `unclassified_split_risk` | `True` | `split-bid risk not classified` |

## Non-Claims

- This artifact does not change sealed-bid runtime settlement semantics.
- The owner-consolidated mitigation is a design candidate, not an activated rule.
- Tau does not inspect private bids, compute apportionment, or authorize settlement.
- Privacy still depends on commitment nonce quality outside this certificate.

## Replay

```bash
python3 tools/zenodex_sealed_bid_apportionment_breakthrough_20260628.py
```
