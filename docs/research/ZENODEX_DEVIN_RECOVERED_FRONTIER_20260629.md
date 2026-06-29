# ZenoDEX Devin Recovered Frontier Inventory - 2026-06-29

## Executive Result

A bounded inventory of recovered Devin ACP event logs maps prior ZenoDEX research sessions to current repo artifacts and open candidate directions.

- Logs present: `5` / `5`
- Materialized candidates: `4`
- Highest-value next open candidate: `nc_bipartite_matching_for_cow`

## Signal Counts

- `discrete_argmax_proximity`: `418`
- `kpool_argmax_proximity`: `181`
- `tauspec_ebrm_frontier`: `323`
- `concavity_min_out_cap`: `937`
- `nc_bipartite_matching`: `5`
- `spectral_commutative_candidate`: `1`

## Candidates

### `discrete_argmax_proximity`

- Status: `materialized`
- Abstraction move: `R4 encode/compress plus C2 strengthen`
- Invariant: floor-rounded split value is within an epsilon band of the continuous optimum
- Value: Replaces the false discrete-concavity target with a provable argmax-proximity theorem.
- All artifacts present: `True`

### `kpool_argmax_proximity`

- Status: `materialized`
- Abstraction move: `D4 invariant-driven generalization`
- Invariant: floor error scales with pool count k under the abstract proximity theorem
- Value: Lifts the 2-pool proximity shape into a K-pool proof obligation.
- All artifacts present: `True`

### `tauspec_ebrm_frontier`

- Status: `materialized`
- Abstraction move: `R4 frontier compression plus C5 shadow-price ranking`
- Invariant: advisory selector cannot authorize settlement or state mutation
- Value: Keeps high-value Tau specification candidates visible in a bounded, replayable selector.
- All artifacts present: `True`

### `concavity_min_out_cap`

- Status: `materialized_research_only`
- Abstraction move: `C2 strengthen mechanism constraint`
- Invariant: filled users have no profitable lower-min-out deviation in the fixed-order model
- Value: Turns collusion mitigation into bounded no-gain and curvature-bound checks.
- All artifacts present: `True`

### `nc_bipartite_matching_for_cow`

- Status: `open_candidate_from_logs`
- Abstraction move: `R2 graphify plus R5 algebraic basis`
- Invariant: unverified hypothesis; pairwise CoW settlement may reduce to max-weight bipartite matching
- Value: Potential path from Hungarian-style exact matching to parallel matching certificates.
- All artifacts present: `False`

### `spectral_liquidity_commutative_consensus`

- Status: `open_candidate_from_logs`
- Abstraction move: `R5 spectral/change-basis`
- Invariant: unverified; session title only in recovered logs
- Value: Needs reconstruction before it can be treated as a research claim.
- All artifacts present: `False`

## Non-Claims

- The inventory does not treat Devin log text as proof.
- Open candidates require fresh replayable artifacts before promotion.
- Model-selector metadata is recorded only as source context, not as research evidence.
- No settlement, state-root, governance, production, routing, matching, or pool-mutation authority is derived.

## Replay

```bash
python3 tools/check_devin_recovered_frontier_20260629.py
```
