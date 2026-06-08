# WS3 — Decentralized Proof Market (design)

> "Trust the MATH, not the hosts." The market makes proof *production* reliably
> available and correctly *paid* — it never makes a host, prover, or reputation an
> input to acceptance.

This is the economic layer that makes trustless hosting **permissionless + sustainable**:
who produces proofs, how proof supply meets demand, and how honest proving is the
dominant strategy — without ever letting payment substitute for verification.

Designed by a 15-agent workflow (understand → 3-lens design → 8-vector adversarial
incentive red-team → synthesis), grounded against the real proving/verifying path
(`zk/state_proof_risc0/cli/src/main.rs`), the existing (unwired) policy
(`src/core/proof_market_policy.py`, `lean-mathlib/Proofs/ProofMarketSafety.lean`), and
the hard-won perp-incentive rules.

## Status / scope (read first — this is a DESIGN, not a shipped market)

The economic rails (escrow, payment finalization, prover registry, bond, slash,
commit-reveal, submission fee, backstop prover) **do not exist in code**, and
`evaluate_proof_market_policy` is imported only by its own unit test. **The market MUST
remain disabled** until, at minimum:
- WS2's `ReceiptVerifierPort` + `RebindFn` are **real and parity-tested** (they are
  stubs today — paying real value on a stubbed verifier makes the lazy-prover attack a
  trivial unbounded-margin exploit), and
- the listed Lean/Kani incentive invariants are **proven**, and
- per-surface **prove-time benchmarks** exist (only ~31s CLOB / ~46–96s spot are known;
  perps-NP and zUSD are **unmeasured** — a hard precondition for pricing + SLA floors).

## The keystone — admission liveness is decoupled from proof purchase

Critical-path admission rests on **deterministic replay over public data**
(`HostIndependent := FailClosedBlocked OR (PublicDataAvailable AND (DeterministicReplay
OR ValidProof))`). The proof market sells **succinctness** (light-client admission +
asynchronous audit), **not** critical-path admission. Therefore no prover, cartel, or
late/withholding bonded prover can hold a full node hostage — admission never depended
on buying a proof. This is the load-bearing escape from the "bond ≥ unbounded exogenous
benefit V" trap: withholding is defeated by **structural non-pivotality**, not by a
value-indexed bond.

## Roles + trust status

| Role | Trust status | Responsibility |
|---|---|---|
| **Host / relay** | **Untrusted relay** (WS2 non-trust clause) | Relays ops/commitments/proof bundles/escrow msgs. Bandwidth + availability only. Can delay/censor (latency, absorbed by multiplicity), never forge an admission or payment. |
| **Client (verifier)** | **Trusted only in its own shipped code** (client-pinned registry + contract) | Refuse-by-default admission (WS2 `decide_admission`). For time-critical admission uses **deterministic replay**; a purchased proof is needed only where replay is unavailable. Recomputes verification for any payout it authorizes. The sole correctness boundary. |
| **Prover (keyless)** | **Incentivized, not trusted** | Runs the pinned prover; no key/identity/registration. Earns a reward by first-COMMITTING `H(receipt‖payout_addr)` then revealing a verifying, correctly-bound, non-vacuous proof. Cannot forge (STARK soundness + image-id pinning). |
| **Bonded prover (SLA)** | **Incentivized, not trusted, slashable** | Same binary + an isolated per-job **non-recapturable bond** for a latency SLA. The bond is the only slashable object. Runs *alongside* (never suppresses) the keyless race. |
| **Poster / demander** | **Self-interested; bears the right-statement obligation** | Commits `proposal_hash` (incl. post_state_root) + the **expected bindings** *before any proof exists*, funds escrow, posts an anti-grief bond. Its pre-committed bindings force the proof to certify the RIGHT statement. |
| **Governance (#51)** | **Trust-minimized (L2); never per-proof authority** | Sets parameters only (cost-oracle, fee floor, bond curve, burn sink, reward-pool funding, DoS cap, *recommended* pin). Cannot sign accept/reject; client pins its own image id independently. |

## Mechanism

- **Per-proposal bounty** (content-addressed to `proposal_hash`), not a standing order book.
- **Commit-reveal, first-COMMITTER-wins**: a prover commits `H(receipt‖payout_addr)`
  (marking the proposal claimed before the bytes are exposed) then reveals — defeating
  relay/mempool **receipt theft / free-riding**. (Alternatively bake the payout address
  into the proven journal so the receipt is non-transferable by construction.)
- **One verifier, two consumers**: the market's payout-authorizing `verifier_accepts`
  MUST be the *exact same* `receipt.verify`-against-client/validator-pinned-image used by
  WS2 `client_admission_decision.py` gate 3, and the binding check MUST equal WS2 gates
  5–9. A weaker market verifier would pay a proof clients refuse (wasted reward) or
  refuse one it paid (value leak).
- **Authority-recomputed**: every correctness boolean (`verifier_accepts`,
  `theorem_binding_matches`, `public_inputs_hash_matches`, `non_vacuity_witness`,
  `proposal_hash_unclaimed`, escrow/payment) is **recomputed by the consensus-grade
  authority** over the submitted bytes — never caller/host supplied, never the
  `SubprocessProofVerifier` stdout `ok`.
- **Who pays whom**: poster-escrow → prover (reward `R`); all penalties **BURNED** to a
  prover-disjoint sink; reward pool is **burn/genesis-funded** (never a prover-recapturable
  fee route). A **protocol-funded floor-price backstop prover** fills any at-floor bounty
  left unfilled (capping supply-side extraction — at the cost of a named centralization residual).
- **Pricing**: poster-set `R`, but must clear a governance floor `R·(1−α_max) ≥
  measured_prove_cost(surface)` — the **recapture-discounted** reward vs measured
  non-recapturable compute. The market never invents a number.
- **Admission ordering**: cheap structural checks (fee-paid, unclaimed/dedup, DoS cap)
  gate **before** the expensive `receipt.verify` (the live policy currently verifies first).

## Incentive invariants (load-bearing)

1. **Authority-recomputed verification** — a false proof is cryptographically unpayable.
2. **Non-recapturable-cost rule** — only sunk RISC0 compute + **burned** bonds/fees deter;
   pooled penalties cost `fee·(1−α)` → 0 as a sybil's share α→1, so no deterrent may be
   routed into any balance the penalized party can hold share of.
3. **Reward-source disjointness** — `reward_source ∩ prover_claimable = ∅` and
   `slash_destination ∩ prover_claimable = ∅` (machine-check pending).
4. **No unconditional minimum** — every minimum must be conditional on a non-recapturable
   cost; pay 0 when emission decays. (See finding F1: the live kernel ships `else:{const:1}`.)
5. **Producer-binding** — commit-reveal `H(receipt‖payout_addr)` in consensus-grade state
   before the receipt is exposed (a verifying receipt is otherwise a bearer instrument).
6. **Submission cost > verify cost** — a flat burned fee ≥ verify cost; junk submission is loss-making.
7. **Poster anti-grief bond** — non-recapturable, sized so poster griefing cost ≥ the prover compute it induces.
8. **Withholding non-pivotality** — the keystone; replay + a non-exclusive parallel race make withholders non-pivotal.
9. **Payment strictly downstream of correctness** — reputation is advisory and provably
   cannot substitute for verifier acceptance (`reputation_cannot_substitute_for_verifier`).
10. **Consensus-grade economic state** — escrow, claimed-set, payment, deadline are
    deterministic per-validator state, never a host flag.

## Slashing (all penalties BURNED — non-recapturable)

| Trigger | Penalty | Backed by |
|---|---|---|
| False proof | **None** — cryptographically unpayable; earns 0 automatically | STARK soundness + image-id pin |
| Keyless-lane bad/withheld/late | **None** — no identity/bond; loss = sunk compute + burned fee | Sunk RISC0 compute |
| SLA-lane withholding/lateness past the **consensus-grade deadline block** | Isolated per-job bond **burned** (compensates no one; admission already fell back to replay) | Prover's own burned bond |
| SLA-lane equivocation/commitment-breach | Bond **burned** (secondary to the structural race defense) | Bond + parallel race + replay |
| Poster griefing (unsatisfiable bindings / fail-to-finalize) | Anti-grief bond **burned** | Poster's own bond |

## Liveness

Permissionless keyless entry; **admission never depends on buying a proof** (replay
fast-path); a vanished prover is a non-event (proofs are deterministic + content-addressed,
any prover reproduces them); relay multiplicity; a refuse-by-default client that emits
`NO_PROOF` triggers a demand-pull bounty any prover fills, then re-runs `decide_admission`
over its **own** `receipt.verify`. Safe stall on total supply failure (fail-closed: no
payout without a valid proof; a light client correctly refuses).

## Unresolved adversarial gaps (8-vector red-team; 6 unclosed in *code*)

The design closes withholding/cartel/late **structurally** via the keystone, but the
red-team found that **no candidate** fully defends these in code today; the synthesis
specifies the required defense for each (all unbuilt):
- **Withholding-extortion** & **late-proof denial**: need a consensus-grade deadline
  block (not a host `before_deadline_ok` flag) + a real isolated burned bond with a
  deterministic slash trigger + the replay/parallel-race rescue. The bond can't dominate
  an unbounded exogenous V — non-pivotality (the keystone) is the actual defense.
- **Cartel pricing**: free entry alone is an *unproven economic assumption* (undermined by
  first-valid-wins race-loss risk); needs a bonded standing supply or the backstop prover
  (both add a centralization residual). A bounty *ceiling* is **not** a defense (it converts
  extraction into DoS).
- **Sybil-fee-recapture**: must implement + machine-check C-RWD-1 (reward-source disjoint)
  and C-LP-1 (remove the unconditional minimum; burned submission fee; price against
  recapture-discounted cost). None implemented or proven today.
- **Griefing-spam**: poster anti-grief bond + burned submission fee to a disjoint sink +
  per-block DoS cap + verify-after-structural-checks ordering.

## Open questions / preconditions

Verifier ports are stubs (hard precondition); per-surface prove-times unmeasured;
**right-statement/live-ledger binding** is the largest remaining audit obligation (verify
re-derives bindings from poster-supplied context — nothing forces the proven post_state_root
to equal the *ledger's* committed header; safety rests on the poster committing correctly);
no live wiring; `ProofMarketSafety.lean` proves only `payout ⇒ verifier-accepted` + non-vacuity
+ unclaimed + escrow + reputation-can't-substitute (no theorems yet on source-disjointness,
withholding/deadline non-pivotality, or authority-recomputed binding); backstop-prover
centralization; light-client time-critical liveness gap; no recursion/aggregation; governance
parameter-capture (L2 residual); deadline/equivocation observability.

## Non-claims

Does NOT guarantee critical-path admission via the market (replay does); does NOT make a
false or wrong-statement proof payable (but cannot detect a poster who commits *wrong*
bindings); does NOT trust any host field/reputation/bond-status/claimed-image as an
ACCEPT or PAYOUT input; does NOT slash for incorrectness (unpayable already) or in the
keyless lane; does NOT prove liveness/DA/ordering/oracle-honesty (the oracle is L2 — any
price-embedding surface inherits quorum trust); does NOT eliminate the toolchain/pin or
backstop-prover centralization residuals; **is NOT implemented**.

## Concrete, verified, actionable findings about EXISTING code

The design surfaced (and this doc verified) real, in-repo next steps:
- **F1 — exploitable unconditional minimum (C-LP-1):** `src/kernels/dex/proof_mining_manager_v1.yaml`
  ships `else: { const: 1 }` at lines **242 / 287 / 331 / 423** — a guaranteed 1-unit
  payout regardless of non-recapturable cost. Replace with `0` (or gate on
  `R·(1−α_max) ≥ measured_prove_cost`). **Needs an ESSO re-verification + review (kernel
  observables) — not changed here.**
- **F2 — verify-ordering:** `evaluate_proof_market_policy` runs `verifier_accepts` first
  (≈ line 42); reorder cheap structural checks (fee/unclaimed/cap) before the expensive verify.
- **F3 — policy unwired:** `proof_market_policy.py` + `ProofMarketSafety.lean` exist but are
  imported only by tests; the economic rails + the authority-recomputed-verification wiring
  are absent.
- **F4 — missing Lean/Kani invariants:** source/slash-destination disjointness, withholding
  & deadline non-pivotality, and the authority-recomputed-binding (the Lean theorem is silent
  if `verifierAccepts` is populated by a trusted flag) — all needed before promotion.
- **F5 — unmeasured prove-costs:** benchmark steady-state perps-NP / zUSD prove time before
  any pricing or SLA-deadline parameterization.
