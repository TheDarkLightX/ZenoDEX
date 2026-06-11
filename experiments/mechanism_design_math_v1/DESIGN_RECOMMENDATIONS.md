# Mechanism Design Math Design Recommendations

No production code recommendations are emitted by the current Wave 1 arithmetic
evidence. Wave 2 records six sealed-bid deviation obligations across four
claim families; each row names the claim, the evidence, and the surface a
separately reviewed change would touch. Replay for every Wave 2 row:
`python3 -m pytest experiments/mechanism_design_math_v1/wave2_sealed_bid/ -q`.

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

Future entries should name the falsified claim, the replay command, and the
specific production surface that would need a separately reviewed change.
