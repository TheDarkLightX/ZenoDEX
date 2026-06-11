# Mechanism Design Math Design Recommendations

No production code recommendations are emitted by the current Wave 1 arithmetic
evidence. Wave 2 records six sealed-bid deviation obligations across four
claim families; Wave 4 records six verification-market obligations across proof
mining and permissionless-hosting bounties. Each row names the claim, the
evidence, and the surface a separately reviewed change would touch. Replay for
the two strategic-deviation waves:

```bash
python3 -m pytest experiments/mechanism_design_math_v1/wave2_sealed_bid/ -q
python3 -m pytest experiments/mechanism_design_math_v1/wave4_verification_markets/ -q
```

Remedies named in the Recommendation column are candidate directions for the
cited open question (`OQ-*`), not tested results: Wave 2 evidence covers the
deviations in the implemented mechanism only. No remedy below has its own
deviation evidence yet; each would need that before adoption.

Settled so far:

| Obligation | Result | Recommendation |
|---|---|---|
| `O-SS-02` | ceil-rounded fees are superadditive under the bounded Wave 1 split model | no change; splitting does not reduce exact-in fee liability in this model |
| `O-SS-07` | fee dust-carry conserves value with `dust < 3` for the three-way split | no change; keep the dust-carry invariant covered by regression evidence |
| `O-SB-01` | claim "uniform pricing is incentive-compatible" FALSIFIED: demand reduction strictly profits (2-bidder 2-unit witness, gain 40 quote units at value 100) | decide OQ-SB-1 (highest-rejected-bid pricing and/or per-bidder quantity aggregation) before any production use of `src/core/sealed_bid_auction.py` beyond UX experiments |
| `O-SB-02` | pivotal single-unit winners pay their own bid; shading to runner-up + 1 strictly profits | same OQ-SB-1 decision; highest-rejected-bid (Vickrey-style) pricing is the classical candidate for the single-unit case — untested here, and known from auction theory to be insufficient against multi-unit demand reduction, so it is not claimed to remove `O-SB-01` |
| `O-SB-03` | claim "hash tie-break is neutral" FALSIFIED: T nonce trials buy win odds T/(T+m) against m rival commitments; each trial is one sha256 over a bidder-chosen nonce | adopt OQ-SB-2 (post-reveal salt in the tie-break hash, e.g. settlement-seed) if ties carry value at production sizes |
| `O-SB-04` | claim "bonds make reveal rational" FALSIFIED for q >= 2 (`MAX_BOND` < option value; exact threshold delta = MAX_BOND//q + 1); q = 1 is the covered in-domain boundary where `MAX_BOND` forces reveal | if non-reveal matters economically, scale the bond domain with committed quantity (e.g. bond >= q * max adverse width) or make reveal mandatory by construction; surface: `src/core/sealed_bid_bonds.py` |
| `O-SB-05` | conditional reveal is a free option exactly when q * support-width > bond (`conditional - always = q*w - b`) | same surface as `O-SB-04`; the bond floor must track q * expected price-support width, not a flat cap |
| `O-SB-06` | claim "decoy bids are neutral" FALSIFIED: a same-bidder decoy pins the clearing price (payoff 200 - 3d vs honest 20 in the witness) | per-bidder aggregation (one effective bid per bidder_id) or a seller reserve price; surface: `src/core/sealed_bid_auction.py` admission rules |
| `O-VM-01` | first-valid-wins collapses the deterministic speed-ranking model to one fastest entrant; slower lower-cost provers rationally exit | do not rely on first-valid-wins alone for prover decentralization; candidate directions are randomized admissible-winner selection, parallel per-class rewards, or latency-normalized queues; surface: `docs/PROOF_MINING.md` and any future proof-mining manager admission rule |
| `O-VM-02` | halving rewards stop participation before a pre-funded pool is exhausted (base 64, cost 9 leaves 888/1000 stranded in the witness) | specify a reward floor, cost-indexed schedule, or explicit rollover/sweep behavior before production use; surface: proof-mining reward schedule |
| `O-VM-03` | improvement ties are selectable through submitter-chosen `miner_id`, and route shape also affects the tiebreak key | replace user-controlled tie components with a post-round deterministic salt or canonical witness digest if equal-improvement ties carry value; surface: `tools/gpu_jobs/improvement_bounty_round_route_v1.py` |
| `O-VM-04` | per-round caps plus repeated base rewards make improvement withholding profitable (δ=80 pays 25 one-shot vs 40 split) | consider cumulative caps per job/miner or carry-over accounting for uncaptured improvement; surface: permissionless-hosting bounty payout formula |
| `O-VM-05` | flooding S slots is unprofitable exactly when `fee >= ceil(reward / S)` | size submission fees or stake locks against the active per-block/per-round cap and maximum payout, then test the chosen constants; surface: permissionless-hosting admission policy |
| `O-VM-06` | pool conservation holds in the tested claim-gate model when admissible claims pay and rejected claims are no-ops | keep admissibility as the payout authority and regression-test conservation across invalid and insufficient-budget claims before wiring a live payout path |

Future entries should name the falsified claim, the replay command, and the
specific production surface that would need a separately reviewed change.
