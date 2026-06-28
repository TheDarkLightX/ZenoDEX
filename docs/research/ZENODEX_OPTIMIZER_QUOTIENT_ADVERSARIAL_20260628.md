# ZenoDEX Optimizer Quotient Adversarial Corpus - 2026-06-28

## Executive Result

The optimizer_quotient_certificate_v1 host-projected Tau envelope remains valid across a deterministic adversarial route-domain corpus covering original, split-heavy, two-hop-winner, sparse-direct, and asymmetric-reserve cases, while preserving bounded domain replay, mutation rejection, proof compression, and no-authority boundaries.

- Cases: `17`
- Families: `asymmetric_reserves, original_showcase, sparse_direct, split_heavy_near_cap, twohop_winner`
- Selected route prefixes: `direct, twohop`
- Label count range: `8` to `251`
- Compression range: `5.71x` to `196.63x`
- Tau replay ok: `True`

## Case Table

| case | family | labels | full bytes | cert bytes | compression | selected |
| --- | --- | ---: | ---: | ---: | ---: | --- |
| `original_baseline_route_amount42` | `original_showcase` | `45` | `16247` | `391` | `41.55x` | `twohop:p_ac>p_cb` |
| `original_wide_split_route_amount36` | `original_showcase` | `215` | `71697` | `404` | `177.47x` | `direct:p_ab_direct_3` |
| `original_twohop_route_amount48` | `original_showcase` | `53` | `19398` | `418` | `46.41x` | `twohop:p_ac_thin>p_cb_fee` |
| `wide_split_amount12` | `split_heavy_near_cap` | `71` | `21139` | `387` | `54.62x` | `direct:wide_ab0` |
| `wide_split_amount24` | `split_heavy_near_cap` | `143` | `43243` | `389` | `111.16x` | `direct:wide_ab0` |
| `wide_split_amount36` | `split_heavy_near_cap` | `215` | `65349` | `389` | `167.99x` | `direct:wide_ab3` |
| `wide_split_amount42` | `split_heavy_near_cap` | `251` | `76685` | `390` | `196.63x` | `direct:wide_ab3` |
| `twohop_winner_amount18` | `twohop_winner` | `58` | `19997` | `448` | `44.64x` | `twohop:twohop_ac_thin>twohop_cb_fee` |
| `twohop_winner_amount33` | `twohop_winner` | `103` | `36090` | `450` | `80.20x` | `twohop:twohop_ac_thin>twohop_cb_fee` |
| `twohop_winner_amount48` | `twohop_winner` | `148` | `52202` | `450` | `116.00x` | `twohop:twohop_ac_thin>twohop_cb_fee` |
| `twohop_winner_amount60` | `twohop_winner` | `184` | `65098` | `450` | `144.66x` | `twohop:twohop_ac_thin>twohop_cb_fee` |
| `sparse_direct_amount7` | `sparse_direct` | `8` | `2199` | `385` | `5.71x` | `direct:sparse_y` |
| `sparse_direct_amount19` | `sparse_direct` | `20` | `5884` | `387` | `15.20x` | `direct:sparse_y` |
| `sparse_direct_amount31` | `sparse_direct` | `32` | `9568` | `387` | `24.72x` | `direct:sparse_y` |
| `asymmetric_amount20` | `asymmetric_reserves` | `61` | `19901` | `402` | `49.50x` | `direct:asym_balanced` |
| `asymmetric_amount50` | `asymmetric_reserves` | `151` | `50188` | `404` | `124.23x` | `direct:asym_balanced` |
| `asymmetric_amount70` | `asymmetric_reserves` | `211` | `70380` | `404` | `174.21x` | `direct:asym_balanced` |

## Mutation Checks

| mutation | accepted | failed flags |
| --- | --- | --- |
| `bad_domain_hash` | `False` | `domain_commitment_ok` |
| `bad_selected_route` | `False` | `quotient_witness_ok`, `canonical_winner_ok` |
| `bad_selected_objective_key` | `False` | `canonical_winner_ok` |
| `bad_label_count` | `False` | `quotient_witness_ok`, `projection_cover_ok` |
| `bad_pruned_count` | `False` | `quotient_witness_ok`, `projection_cover_ok` |
| `cross_domain_transplant` | `False` | `domain_commitment_ok`, `quotient_witness_ok`, `canonical_winner_ok`, `replay_ok`, `projection_cover_ok` |

## Tau Boundary

`src/tau_specs/recommended/optimizer_quotient_certificate_v1.tau` remains a host-projected proof-surface gate. Host code owns route-domain enumeration, hashes, objective keys, arithmetic replay, and winner selection.

## Non-Claims

- The corpus is bounded to direct, two-hop, and two-way parallel exact-out route labels.
- The quotient certificate is only sound with host recomputation of the full route-label domain.
- Tau does not compute route labels, hashes, objective keys, CPMM arithmetic, DP states, or settlement.

## Replay

```bash
python3 tools/check_optimizer_quotient_adversarial.py
```
