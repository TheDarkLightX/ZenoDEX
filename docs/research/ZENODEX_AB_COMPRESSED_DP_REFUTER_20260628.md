# ZenoDEX AB Compressed-DP Refuter - 2026-06-28

## Executive Result

A one-record-per-subset Held-Karp DP is not sound for the current AB objective under integer CPMM semantics.
The existing full-state subset DP keeps reserves and sender balances in the state key.

## Witness

- Pool: reserve0 `85`, reserve1 `561`, fee_bps `5`
- `03e8`: sender `020202`, amount_in `32`, min_amount_out `32`
- `03e9`: sender `020202`, amount_in `119`, min_amount_out `81`
- `03ea`: sender `030303`, amount_in `96`, min_amount_out `130`

## Oracle Comparison

| solver | order | AB key |
| --- | --- | --- |
| `bruteforce` | `03e8, 03ea, 03e9` | `(247, 171, ('03e8', '03ea', '03e9'))` |
| `full_state_subset_dp` | `03e8, 03ea, 03e9` | `(247, 171, ('03e8', '03ea', '03e9'))` |
| `compressed_subset_only_dp` | `03ea, 03e9, 03e8` | `(215, 189, ('03ea', '03e9', '03e8'))` |

The unsafe compressed subset-only DP loses `32` units of primary AB amount while gaining surplus that the objective ranks second.

## Non-Claims

- This does not refute the existing full-state subset DP.
- This does not refute compressed-state results for different cross-pool routing models with separate conservation proofs.
- The witness is a bounded deterministic counterexample, not a distributional performance benchmark.

## Replay

```bash
python3 tools/zenodex_ab_compressed_dp_refuter_20260628.py
```
