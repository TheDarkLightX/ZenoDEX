# ZenoDEX Mechanism Design and Math (2026-06-10)

Companion to the AutoGovNEXT mechanism-design stream, which treats the
autonomous-governance mechanism. This document extends the same treatment to
ZenoDEX's *economic* mechanisms: the spot batch-clearing auction, the
sealed-bid auction family, perpetuals epoch timing and keeper incentives,
and the verification markets (proof mining and host compensation).

This is a design-and-analysis charter. It does **not** declare production
readiness, it does **not** authorize any production `src/` change, and it
does **not** weaken any promotion boundary. Falsified incentive claims
produce design recommendations
(`experiments/mechanism_design_math_v1/DESIGN_RECOMMENDATIONS.md`), never
direct fixes on the consensus path.

> ### Code-version grounding (read before citing any symbol)
>
> This document grounds against the working tree of branch
> `codex/zeno-ledger-public-testnet-20260514` as of 2026-06-10. Symbols are
> tagged:
>
> - **[implemented]** — exists in this working tree at the cited path;
> - **[existing]** — present before this program started (all mechanism
>   code cited here is [existing]; the tag distinguishes program artifacts);
> - **[open]** — a claim this program has not yet settled;
> - **[obligation]** — a property queued for evidence in
>   `experiments/mechanism_design_math_v1/` (hypothesis IDs `H-MD-*`).
>
> Every claim-bearing backticked repo path in this document is checked
> mechanically by
> `experiments/mechanism_design_math_v1/wave0_census/test_census.py` and
> `experiments/mechanism_design_math_v1/tools/check_charter_grounding.py`.
> Background streams that are not present on this clean-base branch are
> named in prose, but are not cited as repo-local evidence paths.

---

## Part I — Program statement

### 0. One-paragraph statement

ZenoDEX settles spot intents through a deterministic batch-clearing function
with an explicit optimization objective, sells inventory through a
commit-reveal sealed-bid auction, runs perpetuals on a phase-gated epoch
state machine with rule-derived funding, and pays for verification work
through first-valid-wins proof rewards and deterministic improvement
bounties. Each of these is, formally, a **mechanism**: it maps reported
types (intents, bids, action timing, witnesses) to an outcome (fills,
prices, funding flows, payouts). Prior programs proved these mechanisms
*safe* in the accounting sense (conservation, bounds, no-op on reject).
This program asks the *strategic* questions: is honest reporting a best
response, what does a deviation buy, which rule is the binding deterrent,
and what is the exact integer arithmetic of each answer.

### 1. Why a game-theoretic treatment, and why now

The accounting layer is already strong: settlement conservation, payout
caps, and phase-gate safety are machine-checked (see §Prior-art). But
several **stated-but-unproven incentive claims** ride on top of that layer:

- "AB-optimal ordering eliminates sandwich MEV" (batch clearing design
  intent) — proven for the *operator's* choice problem, not against
  *participant* strategy (min_out shading, intent splitting, tie-break
  selection, batch-cardinality manipulation).
- "Uniform pricing is incentive-compatible" (sealed-bid) — classically
  false for multi-unit demand (demand reduction); never tested against the
  implemented lowest-accepted-bid pricing rule.
- "Funding equilibrates timing-neutral exposure" — the phase gates block
  price-conditioned *entry*, but the residual *funding-conditioned timing*
  game is unanalyzed (queued as a "missing insight" by prior Codex review
  of the perp-incentives program).
- "First-valid-proof race incentivizes rapid proving" — true, and possibly
  monopoly-forming; participation equilibrium never modeled.

A falsified incentive claim is not an accounting bug: state stays
conserved while value migrates from honest participants to strategic ones.
That migration is invisible to conservation checks and visible only to a
game model. The house posture applies: hypotheses are falsifiable, numeric
deviations are measured before being claimed, and refutations are
first-class results.

### 2. Scope, exclusions, and lane discipline

In scope (four domains, one wave each):

| Domain | Mechanism surface | Wave |
|---|---|---|
| D1 spot settlement | `src/core/batch_clearing.py`, `src/core/fees.py`, `src/core/cpmm.py`, `src/core/routing.py` | 1 |
| D2 sealed-bid family | `src/core/sealed_bid_auction.py`, `src/core/sealed_bid_bonds.py` | 2 |
| D3 perps timing/keepers | `src/core/perp_v2/funding_rule.py`, `src/core/perp_v2/guards.py` | 3 |
| D4 verification markets | `docs/PROOF_MINING.md`, `docs/PERMISSIONLESS_HOSTING.md`, `tools/gpu_jobs/improvement_bounty_round_route_v1.py` | 4 |

Excluded, with reasons:

- **Autonomous governance** — owned by the AutoGovNEXT stream; its
  obligations O1–O8 stay in that stream.
- **zUSD buyback execution (Q-3/Q-4/Q-9)** — staged for review in
  the zUSD hybrid-economics lane; another lane, not raced here.
- **Settled prior art** — re-derivation of H-GT-001..020
  from the research-program lane, the perp-incentives principles, and zUSD
  economics I-1..I-18. New hypotheses must cite the prior result they
  extend when that source is present in the reviewed branch.
- **Production code changes** — none in this program. CBC discipline:
  research artifacts and design recommendations only.

### Prior-art floor (proven, cited, not re-derived)

- Batch ordering *quality*: `lean-mathlib/Proofs/BatchOptimality.lean`,
  `lean-mathlib/Proofs/BatchApproximation.lean`,
  `lean-mathlib/Proofs/BatchAuctionCanonical.lean`, and
  `lean-mathlib/Proofs/UniformBatchClearingV1.lean` — these bound how good
  the operator's ordering is; they say nothing about reporter strategy.
- Single-shot liquidation incentives:
  `lean-mathlib/Proofs/PerpGameTheory.lean` (`liquidation_dominant_strategy`,
  `liquidation_ic`, `no_profitable_self_liquidation`, LP individual
  rationality). The *race* among keepers and *timing* games are open.
- Funding arithmetic: `lean-mathlib/Proofs/PerpFundingRateSafety.lean`
  (rounding-gap bounds), `lean-mathlib/Proofs/FundingRateMarketSafety.lean`
  (clamps, conservation). The *when-to-hold* game is open.
- Cascade under isolated margin:
  `lean-mathlib/Proofs/PerpCascadeSafety.lean` — within-account isolation;
  the *price-mediated cross-account* channel is open.
- Proof-mining payout safety:
  `lean-mathlib/Proofs/ZenoDEXProofMiningClaimability.lean` and
  `src/kernels/dex/proof_mining_manager_v1.yaml` bind claimability and
  kernel conservation. The *participation equilibrium* is open.
- Game-theory infrastructure:
  `lean-mathlib/Proofs/PerpMechanismDesign.lean` (`Game`, Nash equilibrium,
  dominant strategies, incentive compatibility, individual rationality,
  budget balance). This program **extends** that file's definitions and
  never redefines them.
- PopperPad knowledge consulted 2026-06-10: domains `batch-auction`
  (snapshot-bound settlement equivocation defenses — the *operator-side*
  complement of D1's participant-side tie-break analysis), `amm-theory`
  (curve impossibility, buyback bounds), `perp-incentives` (floor-division
  funding-gap falsification; fees-in-pool recapture; unconditional-minimum
  exploitability). Domains `proof-market` and `mechanism-design` were empty
  at program start.

### 3. Method

Per domain: (i) write the game in normal terms — players, types, strategy
spaces, **integer** payoffs matching the implementation's floor/ceil
arithmetic exactly; (ii) state falsifiable hypotheses with numeric
predictions (`H-MD-*`, registry in
`experiments/mechanism_design_math_v1/HYPOTHESIS_REGISTRY.md`); (iii)
measure — pytest deviation tests, Morph counterexample miners with witness
minimization, bounded simulations; (iv) formalize what stabilizes — Lean
in `experiments/mechanism_design_math_v1/math_notes/lean_experimental/`
first (promotion to `lean-mathlib/Proofs/` is a Wave-5 reviewed decision),
ESSO bounded models under z3+cvc5 agreement; (v) record dead ends and
knowledge to PopperPad; (vi) per-wave Codex review gate.

Confidence labels used throughout: **[PROVEN]** (machine-checked),
**[NUMERICAL]** (measured, not proof), **[CONJECTURE]** (stated, untested),
**[REFUTED]** (counterexample held).

---

## Part II — D1: Spot settlement core

### II.1 The mechanism [existing]

`compute_settlement` in `src/core/batch_clearing.py` clears a batch of
intents against pools. For same-direction exact-in swap batches on one
pool, the operator chooses an execution order under
`swap_ordering` (default `greedy_ab_refined`), maximizing the lexicographic
objective:

```text
A = total executed input volume        (sum of amount_in filled)
B = total surplus                      (sum of amount_out − min_amount_out)
tie-break = lexicographically smallest tuple(intent_id, …)
```

Mode boundaries [implemented]:
`_MAX_SWAP_ORDERING_BRUTE_FORCE_N = 12` (above this,
`_order_swaps_optimal_ab_bounded` falls back to
`_order_swaps_limit_price`), `_MAX_SWAP_ORDERING_GLOBAL_REFINE_N = 24`,
`_MAX_SWAP_ORDERING_MCI_N = 18`. The greedy seed `_greedy_marginal_ab`
executes **tightest declared surplus first** ("lowest absolute surplus
(b), then highest A, then lowest id"), and `_order_swaps_greedy_ab`
guarantees its (A, B) is ≥ the `limit_price` ordering at reserve level,
else falls back. Fees: `compute_fee_total` in `src/core/cpmm.py` is
`ceil(gross_amount * fee_bps / 10_000)`; exact-in output floors. Fee
routing: `split_fee_with_dust_carry` in `src/core/fees.py` floor-splits
`fee + carried_dust` across `(buyback, treasury, rewards)` bps summing to
exactly `10_000`, carrying the remainder in `FeeAccumulatorState.dust`.

### II.2 The game in normal terms

- **Players.** Same-pool same-direction swappers `i = 1..n`; the operator
  (mechanical, plays the published ordering algorithm); LPs (passive
  payoff recipients); optionally a counter-intent supplier (CoW netting).
- **Types.** Trader i's true valuation is its honest acceptable output
  floor; its report is `(amount_in_i, min_amount_out_i, intent_id_i)` —
  three free choices per intent, plus the choice of *how many* intents to
  split into (affecting batch cardinality n).
- **Move order.** Reports are simultaneous (batch). The operator's
  ordering is a deterministic function of reports, so each trader can
  best-respond to the *algorithm*, not to others' private values.
- **Integer payoffs.** Trader i: `amount_out_i` filled at its execution
  position minus value of `amount_in_i`, all in kernel integer arithmetic
  (floor output, ceil fee). LPs: fee income + reserve drift. Rejected
  intent: payoff 0 (all-or-nothing; no pro-rata).

### II.3 Adversary taxonomy and what each rule denies

| Adversary move | Rule engaged | Status |
|---|---|---|
| Report `min_out` above true floor to gain greedy priority | `_greedy_marginal_ab` tightest-first selection | **[open]** — selection explicitly *rewards* tight reports (O-SS-01) |
| Split one intent into k to change fees | `compute_fee_total` ceil per order | **[NUMERICAL]** bounded pytest supports superadditivity (O-SS-02) |
| Split to change execution position | concavity vs priority interaction | **[open]** (O-SS-03) |
| Choose small `intent_id` to win ties | lexicographic tie-break | **[open]** — tie value strictly positive, id is free (O-SS-04) |
| Add a 13th dust intent to flip `optimal_ab_bounded → limit_price` | `_MAX_SWAP_ORDERING_BRUTE_FORCE_N` | **[open]** — cardinality cliff (O-SS-05) |
| Self-supply a counter-intent to net at zero fee | `cow_pair_netting_v1` | **[supported]** — LP fee/spread capture demonstrated (O-SS-06) |
| Drain value through repeated fee splits | dust-carry | **[NUMERICAL]** bounded pytest supports conservation + `dust < 3` (O-SS-07) |

The *operator-side* equivocation game (a forged settlement choosing which
of two competing parties wins) is already characterized in PopperPad
batch-auction knowledge (snapshot-anchor + must-fill defenses); D1 here is
the *participant-side* complement under an honest operator.

### II.4 Residual trust roots

The ordering algorithm itself is the trust root: traders best-respond to
*it*, and its published determinism is what makes shading computable. Any
change to `swap_ordering` defaults shifts the equilibrium; the obligations
below are stated per-mode.

---

## Part III — D2: Sealed-bid auction family

### III.1 The mechanism [existing]

`settle_uniform_price_sealed_bids` in `src/core/sealed_bid_auction.py`:
revealed bids `(bidder_id, commitment, quantity ∈ [1, MAX_UNITS],
limit_price ∈ [1, MAX_PRICE])` with `MAX_UNITS = MAX_PRICE = 0xFFFF` are
sorted by `(-limit_price, commitment, bidder_id)` and filled until
`units_for_sale` is exhausted; `clearing_price` is the **last filled
(lowest accepted) bid's** `limit_price`, and every fill pays it. The same
`bidder_id` may appear in multiple bids (no per-bidder aggregation).
Commitments are `sha256` over canonical JSON including a **bidder-chosen
nonce**. Non-reveal bonds: `settle_sealed_bid_non_reveal_bonds` in
`src/core/sealed_bid_bonds.py` refunds `bond_amount ∈ (0, MAX_BOND]`
(`MAX_BOND = 0xFFFF`) iff the commit was revealed, else slashes it.

### III.2 The game in normal terms

- **Players.** Bidders with multi-unit valuations; the seller is
  mechanical.
- **Types.** Marginal value per unit; report is a *set* of
  `(quantity, limit_price, nonce)` commitments, then a *reveal subset*
  decision after the commit window.
- **Move order.** Commit (simultaneous, hiding) → observe whatever leaks
  in the reveal window → choose which commits to reveal → deterministic
  settlement.
- **Integer payoffs.** `Σ filled_qty · (value − clearing_price)` minus
  slashed bonds. The clearing price is an exact selected `limit_price` —
  no rounding bridge needed for the price itself.

### III.3 Adversary taxonomy

| Adversary move | Rule engaged | Status |
|---|---|---|
| Under-report quantity so a lower rival sets the clearing price (demand reduction) | lowest-accepted uniform pricing | **[NUMERICAL]** witness held — reduction strictly profits for value 100 with rival prices 1..99 (O-SB-01) |
| Shade a pivotal single-unit bid (pays own bid when marginal) | clearing = last *accepted* bid | **[NUMERICAL]** witness held — optimal shade = runner-up + 1, strict gain (O-SB-02) |
| Grind `nonce` to get a small `commitment` and win price ties | sort key `(−price, commitment, bidder_id)` | **[NUMERICAL]** grinding flips settlement ties; win rate matches the exchangeability law T/(T+m) (O-SB-03) |
| Commit, then reveal only if favorable (free option) | non-reveal bond slash | **[NUMERICAL]** `MAX_BOND` beaten for every q ≥ 2 (threshold arithmetic exhaustive over 2..MAX_UNITS; payoffs bound to the real functions for 2..16); q = 1 is the in-domain boundary where `MAX_BOND` forces reveal (O-SB-04, O-SB-05) |
| Submit decoy + real bids under one `bidder_id` to pin the clearing price | repeated-bidder admission | **[NUMERICAL]** witness held — decoy pins the clearing price for its owner (O-SB-06) |

---

## Part IV — D3: Perps timing and keeper games

### IV.1 The mechanism [existing]

Epoch phases OPEN → PRICE_PUBLISHED → SETTLED (`EpochPhase` in
`src/core/perp_v2/types.py`). Phase guards in
`src/core/perp_v2/guards.py`: `guard_deposit_collateral`,
`guard_withdraw_collateral`, `guard_set_position` require OPEN;
`guard_apply_funding` allows OPEN or PRICE_PUBLISHED and at most once per
epoch (`funding_last_applied_epoch`); `guard_partial_liquidate` takes a
caller-chosen `fraction_bps`. The funding rate rule
`compute_funding_rate_bps` in `src/core/perp_v2/funding_rule.py`:

```text
basis_bps := (|mark − index| · 10_000) // index
rate_bps  := sign(mark − index) · min(basis_bps, funding_cap_bps)
```

Positive funding: longs pay shorts. Funding is *applied* as a discrete
per-epoch event, permissionlessly triggered.

### IV.2 The game in normal terms

- **Players.** Traders choosing position timing within and across epochs;
  keepers choosing whether/when to call `apply_funding` and liquidation;
  the protocol (mechanical guards).
- **Types.** Desired exposure windows; liquidation-eligibility
  observations.
- **Move order.** Within an epoch: any OPEN-phase action sequence;
  funding application is an *event whose timing is itself a strategic
  variable* because position changes are legal both before and after it
  in the same OPEN phase.
- **Integer payoffs.** PnL − funding paid − penalties, all in kernel
  arithmetic (`floor` on funding magnitudes via `//`).

### IV.3 Adversary taxonomy

| Adversary move | Rule engaged | Status |
|---|---|---|
| Hold exposure only in the funding-free part of each epoch (straddle) | once-per-epoch `apply_funding`, OPEN-phase `set_position` | **[open]** — residual bounded by `floor(notional·cap/10⁴)`/epoch (O-PT-01) |
| Condition entry on `funding_last_applied_epoch` | same | **[open]** (O-PT-01) |
| Condition position on the published clearing price | OPEN-only position guards | **[obligation]** airtightness to verify, not assume (O-PT-02) |
| Race other keepers for liquidation rewards | deterministic eligibility/selection | **[open]** — rent dissipation vs gas-auction baseline (O-PT-03) |
| Liquidate A to push the mark price into B's liquidation | per-account isolation (proven) + price impact (not modeled) | **[open]** — cross-account cascade depth bound (O-PT-04) |
| Over-liquidate via `fraction_bps` choice | `guard_partial_liquidate` bounds | **[open]** — value-transfer lever (O-PT-05) |

---

## Part V — D4: Verification markets

### V.1 The mechanism [existing]

**Proof mining** (`docs/PROOF_MINING.md` §6): first valid proof per
`proposal_hash` wins `reward(epoch) = base_reward · decay(epoch)` (halving
or exponential), paid from a pre-funded pool with conservation
`total_paid + reward_pool_balance == initial_pool` (bounded model
`src/kernels/dex/proof_mining_manager_v1.yaml`). **Host improvement
bounties** (`docs/PERMISSIONLESS_HOSTING.md`,
`tools/gpu_jobs/improvement_bounty_round_route_v1.py`): submissions are
replayed fail-closed; the winner is the maximum of
`(improvement_u64, −index)` where `index` is the submission's position
under `_route_tiebreak_key` = `(hop_count, pool_ids, intermediate_asset,
miner_id)`; payout `_compute_payout_amount` =
`min(max_reward, base_reward + improvement_u64 · improvement_reward_bps // 10_000)`
with `max_reward ≥ base_reward` enforced.

Note (grounding correction recorded at census time): the winner tie-break
is the **route key plus submitter-chosen `miner_id`**, not a witness hash.
This makes tie-breaking *costlessly* selectable by the submitter — no
grinding required — which sharpens, not weakens, the manipulability
question (O-VM-03).

### V.2 The game in normal terms

- **Players.** Provers with heterogeneous (cost, speed); bounty hunters
  with improvement inventories; sybil submitters; the round operator is
  mechanical (replay + total key).
- **Types.** Proving cost and latency; the size δ of a discovered
  improvement.
- **Move order.** Proof race: continuous, first-past-the-post per
  `proposal_hash`. Bounty rounds: per-round simultaneous submission,
  repeated across rounds — which makes *withholding* part of the strategy
  space.
- **Integer payoffs.** `reward · 1[win] − cost`; bounty payout per the cap
  formula above.

### V.3 Adversary taxonomy

| Adversary move | Rule engaged | Status |
|---|---|---|
| Fastest prover always wins → others exit (monopoly) | first-valid-wins | **[open]** — participation condition (O-VM-01) |
| Stop proving when `reward(epoch) < cost` with pool non-empty | decay schedule | **[open]** — depletion cliff `E_stop` (O-VM-02) |
| Choose `miner_id` to win improvement ties (route-shape variant untested) | `_route_tiebreak_key` | **[supported]** — costless `miner_id` tie selectability demonstrated (O-VM-03) |
| Split improvement δ across rounds to dodge `max_reward` and double `base_reward` | per-round cap formula | **[open]** (O-VM-04) |
| Flood submissions up to per-block caps | submission fee / rate limits | **[open]** — break-even fee floor (O-VM-05) |
| Drain the pool past conservation | pool accounting | **[obligation]** property-test binding to the documented invariant (O-VM-06) |

---

## §10. Provable obligations (hand-off to evidence and formal lanes)

Each row is decidable over a bounded integer model and lands as hypotheses
(`Evidence` column), then as Lean/ESSO artifacts where the result
stabilizes (`Artifact` column; `[exp]` = program-local
`math_notes/lean_experimental/`, promoted only after Wave-5 review). All
rows start **[obligation]**; rows flip to **[verified]** (with the verdict)
as waves complete.

| ID | Property | Statement (bounded, integer) | Denies / characterizes | Evidence | Artifact |
|---|---|---|---|---|---|
| O-SS-01 | min_out-priority characterization | in greedy modes, raising `min_amount_out` weakly raises execution priority; quantify the output gain at the rejection frontier | truthful-floor reporting is NOT dominant | H-MD-SS-001 | [exp] SpotBatchTiebreakGame.lean — [open] |
| O-SS-02 | ceil-fee superadditivity | for any partition of `gross`, `Σ ceil(gᵢ·f/10⁴) ≥ ceil(Σgᵢ·f/10⁴)` | fee-motivated order splitting | H-MD-SS-002 | bounded pytest evidence — [verified: 0..64 gross, all fee bps, all two-way splits] |
| O-SS-03 | split execution dominance + exception | sequential split output ≤ one-shot output (CPMM concavity), EXCEPT when O-SS-01 priority reorders rivals in between | naive "splitting is always bad" | H-MD-SS-003 | cites `lean-mathlib/Proofs` CPMM concavity — [open] |
| O-SS-04 | tie-break value | for identical-tying intents, first position gains an exactly computable output delta > 0; `intent_id` is a free choice | "ties are harmless" | H-MD-SS-004 | pytest-pinned integer — [open] |
| O-SS-05 | cardinality cliff | adding one intent across `_MAX_SWAP_ORDERING_BRUTE_FORCE_N` can strictly lower a victim's fill and the global (A,B) | settlement continuity in batch size | H-MD-SS-005, H-MD-SS-006 | miner witness + `esso/md_spot_cardinality_cliff_v1.yaml` — [open] |
| O-SS-06 | CoW self-netting capture | a self-supplied counter-intent nets at zero fee and captures fee+spread otherwise accruing to LPs | "netting is neutral for LPs" | H-MD-SS-007 | bounded pytest witness through the real `compute_settlement` (`_cow_pair_netting_exact_in_v1`) — [numeric: routing the pair {T, A} through the pool in ONE batch earns LPs the full fee 585 (300+285) + moves reserves; CoW-netting the same pair earns LPs 0 (`fee_paid` 0, `reserve_deltas==[]`) — universal LP capture, no per-party counterfactual. Party gains ASYMMETRIC: initiator T strictly gains (95_000 > 90_661 and > same-batch), but counter-supplier A beats only its ISOLATED quote (100_000 > 86_520) and is worse than same-batch pool (100_000 < 103_765); capture requires a min_out-feasible counter-intent]; research-only, netting-fee remedy untested |
| O-SS-07 | dust conservation, tight | `distributed + dust' = fee + dust` invariant; `dust' < 3` for the 3-way split (not merely < 10⁴) | stranded/created value across splits | H-MD-SS-008 | bounded pytest evidence — [verified: representative routes, fees, dust, and sequence carry] |
| O-SB-01 | demand reduction exists | a 2-bidder, 2-unit integer witness where reducing reported quantity strictly raises surplus | "uniform pricing is IC" | H-MD-SB-001 | bounded pytest witness — [numeric: strict gain, rival sweep 1..99 at value 100]; [exp] AuctionUniformPriceIC.lean still queued |
| O-SB-02 | single-unit non-truthfulness | pivotal winner pays own bid ⇒ shading to runner-up+1 strictly profits | "single-unit demand is truthful here" | H-MD-SB-002 | bounded pytest witness — [numeric: optimal shade = runner-up+1, strict gain]; derivation 06 still queued |
| O-SB-03 | tie grindability | win odds for T nonce trials against m rival commitments = T/(T+m); each trial costs one hash, and the fixed witness has positive tie value (trial-count distribution is heavy-tailed, so stated as a win-rate law, not an expected-trials claim) | "hash tie-break is neutral" | H-MD-SB-003 | pytest empirical — [numeric: grinding flips settlement ties; measured rate matches T/(T+m)]; derivation 08 still queued |
| O-SB-04 | bond < option value | for `q ≥ 2` there exist adverse moves Δ with `Δ·q > MAX_BOND` ⇒ no admissible bond forces reveal | "bonds make reveal rational" | H-MD-SB-004 | bounded pytest witness — [numeric: exact threshold Δ = MAX_BOND//q + 1; threshold arithmetic exhaustive over q in 2..MAX_UNITS, real-function payoff binding for q in 2..16; q = 1 boundary covered separately]; [exp] AuctionBondOptionBound.lean still queued |
| O-SB-05 | conditional-reveal straddle | commit-then-reveal-iff-favorable beats always-reveal when `q·support_width > bond` | costless-straddle denial | H-MD-SB-005 | bounded sim via real settle+bond functions — [numeric: conditional − always = q·w − b exactly on the grid] |
| O-SB-06 | self-competition pinning | one bidder, two commitments can lower its own average paid price | decoy-bid neutrality | H-MD-SB-006 | pytest witness — [numeric: decoy pins the clearing price; constructive witness made the planned miner unnecessary] |
| O-PT-01 | funding-straddle residual | intra-epoch round-trips around `apply_funding` pay 0 funding (under a once-per-epoch scheduled-snapshot keeper); avoided amount ≤ `floor(notional·cap/10⁴)` per epoch | "funding is timing-neutral" | H-MD-PT-001, H-MD-PT-005 | bounded pytest witness through the real `apply_funding` reducer — [numeric: holder debited `funding_magnitude`, straddler debited 0; avoided ≤ `floor(notional·cap/10⁴)`, tight at cap; base×cap sweep]; also confirmed through the real GUARDED `engine.step`: apply_funding debits a holder reached via the guarded `set_position`, but the gate REJECTS apply_funding on a flat account with the exact reason `apply_funding requires non-zero position` (`position_open_ok` the sole failing condition) — funding is gated on holding exposure at the funding moment. SCHEDULER SCOPE (model-honest): a rejected flat apply does not consume the epoch funding slot, so the realizable guarded trace `set_position(q)→set_position(0)→apply_funding(reject)→set_position(q)→apply_funding(accept,debits)` shows a re-entrant is re-exposed; the escape holds only under the standard once-per-snapshot scheduler (no per-account retry). Model-scope only, no keeper remedy claimed; [exp] PerpFundingStraddleBound.lean still queued |
| O-PT-02 | settlement-boundary airtightness | no reachable PRICE_PUBLISHED action sequence changes `position_base` conditioned on the published clearing price | free-look on clearing price | H-MD-PT-002 | **partially_falsified** — bounded verification through the real `engine.step` + guards. In-phase airtight: `set_position` guard-REJECTED in PRICE_PUBLISHED yet accepted+effective in OPEN (guards.py:150); every phase-preserving accepted action is position-invariant over a multi-state sweep; `settle_epoch` has no position param (identical state for 7777 vs 0). BUT the unconditional claim FAILS: `guard_advance_epoch` (guards.py:34) checks only the epoch bound, so `advance_epoch` from PRICE_PUBLISHED skips settlement → OPEN, and `publish→advance→set_position(0)` lets a long facing a 5% adverse clearing print AVOID exactly 50_000 of settlement loss (a reachable settlement-bypass). Airtightness is thus CONDITIONAL on settle-before-advance lifecycle discipline. SEVERITY BOUND (verified, not live-exploitable): driven through the real shell `apply_perp_ops`, advance-before-settle is REJECTED with `cannot advance epoch before settling current epoch` (`perp_runtime_risk_gate.py:180`) — the invariant lives in the shell, so the permissive `guard_advance_epoch` is a pure-core defense-in-depth gap only (remedy untested); [exp] `esso/md_perp_epoch_phase_gate_v1.yaml` inductive model still queued |
| O-PT-03 | keeper-race dissipation | deterministic selection ⇒ expended effort ε, vs ≈ full reward under an all-pay gas-auction baseline | "races are free" / monopolization-by-latency | H-MD-PT-003 | [exp] PerpKeeperRaceGame.lean — [open] |
| O-PT-04 | price-mediated cascade bound | cascade depth K ≤ f(insurance, penalty_bps, book depth, headroom spacing); K = 0 condition stated | unbounded cross-account contagion | H-MD-PT-004 | [exp] PerpPriceMediatedCascade.lean — [open] |
| O-PT-05 | fraction_bps lever | states exist where maximal `fraction_bps` is guard-legal but minimal restores margin with strictly less penalty transfer | "liquidation size choice is neutral" | H-MD-PT-006 | bounded pytest witness through the real `guard_partial_liquidate` + `apply_partial_liquidate` — [numeric: liquidatable long, auto-min fraction 1667 bps (tight: 1666 leaves collateral ≥0 but is guard-REJECTED for failing residual margin — guard enforces residual margin, lines 307-314) penalty 3_334 restores margin, full close 10_000 bps also guard-legal penalty 20_000; legal set is `[f_min, BPS_SCALE]`, oversizing extracts 16_666 extra, transferred liquidatee→fee_pool/insurance by conservation; exhaustive sweep confirms penalty non-decreasing across the whole legal range]; research-only, no minimal-fraction remedy claimed |
| O-VM-01 | participation collapse | prover i enters iff `cost_i ≤ reward · P(win_i)`; deterministic speed ranking ⇒ unique entrant | "open race ⇒ open market" | H-MD-VM-001 | [exp] VMktParticipationContest.lean — [open] |
| O-VM-02 | depletion cliff | under halving, participation stops at `E_stop = ⌊log₂(base/c)⌋ + 1` with pool remainder stranded | "pool depletes gracefully" | H-MD-VM-002 | derivation 14 — [open] |
| O-VM-03 | tie-break selectability | improvement ties resolve by `_route_tiebreak_key` incl. submitter-chosen `miner_id` ⇒ tie wins are costlessly selectable | "ties are rare/neutral" | H-MD-VM-003 | bounded pytest witness through the real `_route_tiebreak_key` + `_select_winner` (`tools/gpu_jobs/improvement_bounty_round_route_v1.py`) — [numeric: equal improvement on the same route ⇒ tie keys differ only in the `miner_id` slot, smaller `miner_id` wins order-independently; attacker ties then picks `'0'` < honest id to steal the win costlessly; strictly larger improvement (1001 vs 1000) wins regardless of a minimal `''` id, so the lever decides only genuine ties]; research-only, bonded-tiebreak remedy untested |
| O-VM-04 | improvement withholding | `2·min(M, b + ⌊bps·δ/2/10⁴⌋) > min(M, b + ⌊bps·δ/10⁴⌋)` for concrete (b, bps, M, δ) ⇒ splitting across rounds dominates | "submit-everything-now is optimal" | H-MD-VM-004 | [exp] VMktImprovementWithholding.lean — [open] |
| O-VM-05 | sybil fee floor | flooding to per-block caps is unprofitable iff `fee ≥ reward/max_slots` | underpriced submission spam | H-MD-VM-005 | sim — [open] |
| O-VM-06 | pool conservation binding | `total_paid + pool = initial` holds across all award combinations in the documented model | silent payout leak | H-MD-VM-006 | pytest property — [open] |

Cross-domain composition obligations (Wave 5): O-XD rows are added when
the single-domain results above settle; candidates are batch×funding
clearing-price bias, prover-settler tie-break compounding, commit-reveal ×
batch min_out conditioning, and funding-rounding × fee-dust composition
(`H-MD-XD-001..004`).

## §11. Open mechanism-design questions (flagged, not yet decided)

- **OQ-SS-1** — Should declared surplus (`amount_out − min_out`) buy
  priority at all? The B-objective rewards tight reports; an alternative is
  priority by submission order or uniform clearing. Decide only after
  O-SS-01 quantifies the gain.
- **OQ-SS-2** — Routing exact-out gate thresholds
  (`stress_threshold_bps = 4000`, `pressure_threshold_e4 = 16000` in
  `src/core/routing.py`) create policy-band edges; is there value in
  randomized or hysteresis bands? Deferred unless a measured edge-gaming
  witness appears.
- **OQ-SB-1** — If demand reduction confirms (O-SB-01), is the fix
  highest-rejected-bid (Vickrey-style) pricing, or per-bidder quantity
  aggregation, or both? Requires a revenue/complexity tradeoff note.
- **OQ-SB-2** — Should the tie-break hash the commitment with a
  *post-reveal* salt (e.g. settlement-seed) to kill grinding (O-SB-03)?
- **OQ-PT-1** — Is the funding straddle (O-PT-01) worth closing
  mechanically (funding accrual pro-rata to holding time within epoch), or
  is the residual small enough to document as accepted? Needs the bound
  first.
- **OQ-VM-1** — What decay schedule shape exhausts the pool without a
  participation cliff (O-VM-02)? Candidate: cost-indexed floor
  `reward(e) ≥ c_ref`.
- **OQ-VM-2** — Should bounty rounds carry-over uncaptured improvement
  (making withholding pointless) or cap per-identity cumulative payout
  (making splitting pointless)? Blocked on O-VM-04's measured gain.

## §12. Honesty boundary (what this program does and does not buy)

**Earned, per obligation, once its row flips to [verified]:**
- A measured, integer-exact answer to "what does this deviation buy" under
  the bounded model stated in the obligation — including refutations
  (deviation buys nothing) as first-class results.
- Machine-checked theorems only for the finite/bounded statements actually
  proved, in experimental Lean until promotion review.

**Not bought, ever, by this program:**
- Production-readiness or promotion claims for any surface. No `src/`
  behavior changes; design recommendations are inputs to separately
  reviewed work.
- Equilibrium claims over unbounded strategy spaces or real-valued limits;
  everything is finite-grid, integer, ε-stated.
- Rationality of real actors: results say what a payoff-maximizer *can*
  extract, not what anyone *will* do.
- Operator honesty: D1 analyzes participant strategy under an honest
  operator; the dishonest-operator game is the (already-characterized)
  snapshot-anchor lane in PopperPad batch-auction knowledge.
- Oracle truth, liveness, censorship resistance, or anything about the
  governance lane (see exclusions).

---

## Appendix A — Symbol map (grounding)

| Symbol | Where | Note |
|---|---|---|
| `compute_settlement` | `src/core/batch_clearing.py` | batch entry point; `swap_ordering` default `greedy_ab_refined` |
| `_MAX_SWAP_ORDERING_BRUTE_FORCE_N` | `src/core/batch_clearing.py` | = 12; AB brute-force cap, fallback `limit_price` |
| `_MAX_SWAP_ORDERING_GLOBAL_REFINE_N` | `src/core/batch_clearing.py` | = 24 |
| `_MAX_SWAP_ORDERING_MCI_N` | `src/core/batch_clearing.py` | = 18 |
| `_order_swaps_optimal_ab_bounded` | `src/core/batch_clearing.py` | (A,B)+tie-break objective; same-direction only |
| `_order_swaps_limit_price` | `src/core/batch_clearing.py` | sort `(−limit_price, intent_id)` |
| `_greedy_marginal_ab` | `src/core/batch_clearing.py` | tightest-surplus-first selection |
| `compute_fee_total` | `src/core/cpmm.py` | `ceil(gross·fee_bps/10_000)` |
| `split_fee_with_dust_carry` | `src/core/fees.py` | floor split + dust carry |
| `FeeAccumulatorState` | `src/core/fees.py` | carried dust |
| `stress_threshold_bps` | `src/core/routing.py` | default 4000 (exact-out 2-hop gate) |
| `pressure_threshold_e4` | `src/core/routing.py` | default 16000 |
| `settle_uniform_price_sealed_bids` | `src/core/sealed_bid_auction.py` | sort `(−limit_price, commitment, bidder_id)`; clearing = last filled price |
| `MAX_UNITS`, `MAX_PRICE` | `src/core/sealed_bid_auction.py` | both 0xFFFF |
| `settle_sealed_bid_non_reveal_bonds` | `src/core/sealed_bid_bonds.py` | refund iff revealed |
| `MAX_BOND` | `src/core/sealed_bid_bonds.py` | 0xFFFF |
| `compute_funding_rate_bps` | `src/core/perp_v2/funding_rule.py` | `sign·min((|Δ|·10⁴)//index, cap)` |
| `EpochPhase` | `src/core/perp_v2/types.py` | OPEN / PRICE_PUBLISHED / SETTLED |
| `guard_set_position` | `src/core/perp_v2/guards.py` | OPEN-only |
| `guard_apply_funding` | `src/core/perp_v2/guards.py` | OPEN or PRICE_PUBLISHED, once/epoch |
| `guard_partial_liquidate` | `src/core/perp_v2/guards.py` | caller-chosen `fraction_bps` |
| `proof_mining_manager_v1.yaml` | `src/kernels/dex/proof_mining_manager_v1.yaml` | `total_paid + reward_pool_balance == initial_pool` |
| `_compute_payout_amount` | `tools/gpu_jobs/improvement_bounty_round_route_v1.py` | `min(max_reward, base + δ·bps//10⁴)` |
| `_route_tiebreak_key` | `tools/gpu_jobs/improvement_bounty_round_route_v1.py` | `(hop_count, pool_ids, mid, miner_id)` |

Appendix B — program crosswalk:
`experiments/mechanism_design_math_v1/CROSSWALK.md` binds every `O-*` row
above to its `H-MD-*` evidence entries and artifact paths; consistency is
enforced by `experiments/mechanism_design_math_v1/tools/check_crosswalk.py`.
