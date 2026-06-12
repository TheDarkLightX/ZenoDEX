# AutoGovNEXT Game Theory and Mechanism Design (2026-06-10)

Companion to `docs/AUTOGOVNEXT_AND_ZENODEX_PRODUCTION_READINESS_PLAN_2026_06_10.md`.

The plan's **Mechanism Surface** section names the players, the attack query, and
the bounded model. This document supplies the layer underneath: *why* the
mechanism is safe, *what* an adversary can and cannot gain, *which* property each
gate prices out, and *which* theorems Phase 4 must discharge.

This is a design-and-analysis document. It does **not** declare production
readiness and it does **not** weaken any promotion boundary in the plan.

> ### Code-version grounding (read before citing any symbol)
>
> This document grounds against the committed Q-policy integration path plus
> the trajectory-runner work ported from `claude/autogov-trajectory-runner`.
> The current branch has committed-state context hashing, single-step
> expected-context checking, a multi-step trajectory runner/verifier, a
> cross-trajectory session verifier, and a single-live-head session store. The
> separate P1 admission hardening surface described in the production-readiness
> plan remains in-flight. Symbols are tagged below as one of:
>
> - **[P1-WIP]** — exists in the Phase-1 working tree, not yet committed to any
>   branch (`admit_autonomous_governance_surface_request_v1`,
>   `FORBIDDEN_SURFACE_ADMISSION_RESULT_FIELDS_V1`, and the extended `_safety_errors`
>   controls beyond freshness/divergence/volatility/liquidity-depth/cooldown —
>   i.e. confidence/concentration/churn/proof-health/validator/network-stress);
> - **[committed]** — present in the committed integration modules
>   (`_governance_surface_gate_report`, `_anti_oscillation_failures`,
>   `_trajectory_budget_failures`, `governance_surface_context_hash_v1`,
>   `_select_action`, `SURFACE_PARAMETER_NAMES_V1`, the surface evaluator,
>   `commit_…_surface_…_v1`, and
>   `run_autonomous_governance_surface_trajectory_v1`,
>   `verify_autonomous_governance_surface_trajectory_v1`, and
>   `admit_verified_autonomous_governance_surface_trajectory_v1`;
>   `continue_autonomous_governance_surface_trajectory_v1` and
>   `verify_autonomous_governance_surface_session_v1`;
>   `admit_autonomous_governance_session_continuation_v1` and
>   `verify_autonomous_governance_session_store_v1`;
>   `admit_autonomous_governance_session_file_continuation_v1` and
>   `verify_autonomous_governance_session_store_file_v1`;
>   `admit_autonomous_governance_live_session_file_update_v1`);
> - **[obligation]** — a proposed Phase-4 property, not yet code.
>
> Verify every citation against the module at the commit being promoted; the
> Phase-1 admission surface is under active hardening and its symbol names may
> move.

---

## 0. One-paragraph statement of the mechanism

AutoGovNEXT is a **proposer–disposer** mechanism. A frozen, hash-pinned policy
artifact (a layered integer lookup table) *proposes* a parameter revision by
ranking a finite action vocabulary against a binned oracle observation. A suite
of deterministic gates *disposes*: it accepts the proposal only if it survives
oracle-safety, per-parameter bounds and step limits, anti-oscillation,
trajectory-budget, cooldown, and the composed governance-surface guards. The
proposer has **zero authority**: its output is a hint over *search order*, never
a permission. Authority lives entirely in the disposer, which is a pure function
of committed state plus the request, recomputed by every node. The security goal
is that no profitable deviation exists for any player — the learned layer, the
node writer, the oracle reporter, or an external adversary — that moves a
governed parameter outside the envelope the disposer would independently allow.

---

## 1. Why a game-theoretic treatment at all

A parameter that a machine can change autonomously is an attack surface with an
*incentive gradient*. fee_bps, the fee-router split (buyburn/stakers/reserve/
hosts), mcr_bps/ccr_bps, the whale-defense `staker_bps`, and `funding_cap_bps`
all have parties who profit from moving them. "The gates are fail-closed" answers
the *static* question (one bad request is rejected). It does not answer the
*dynamic* and *strategic* questions:

- Can a sequence of individually-valid steps reach a state no single step could?
  (Ratchet / salami.)
- Can a player who controls one input (the oracle feed, the submission timing,
  the policy training data) steer the autonomous controller toward a state that
  benefits them, *without* ever tripping a gate?
- Is honest participation a best response, or merely *a* response?

Mechanism design is the right lens because the disposer is, formally, a
**mechanism**: it maps reported types (observations, committed state, timing) to
an outcome (a parameter delta or a no-op) and we want that mapping to be
*strategy-proof* — truthful, in-envelope behavior should weakly dominate every
deviation, for every player, given the others.

---

## 2. The game in normal terms

### 2.1 Players and their types

| Player | Controls | Private type / leverage | Wants |
|---|---|---|---|
| **Policy publisher** | the frozen artifact + its hash | the table contents (offline) | a table that ranks profitable actions first |
| **Node writer / submitter** | which requests reach the node, and when | submission timing, batching | to land a beneficial revision |
| **Oracle reporter(s)** | `observation` fields | the reported world-state, within signing/quorum limits | to bias the controller via the inputs it trusts |
| **Follower node** | independent replay | nothing privileged — it *verifies* | to detect any equivocation |
| **External adversary** | crafted requests | arbitrary bytes at the boundary | any accepted out-of-envelope transition |

The **governance authority** (`zeno_governance_authority.py`, Phase 3) is not a
player in the bounded-surface game; it is the *guard that removes a class of
moves from the game entirely* (authority-changing actions). See §9.

### 2.2 The move order (extensive form)

```
publisher: freeze artifact P, publish hash h(P)          [offline, reviewed]
   │
oracle:    emit observation o (signed / quorumed)        [bounded type report]
   │
writer:    submit request r = (h_expected, P, state s, o, epochs, traj_used)
   │
node:      DISPOSE:
             1. boundary-check r           (admit_…_request_v1)
             2. recompute selection on P,s,o   (proposer is re-run, not trusted)
             3. recompute every gate against committed s
             4. admit ⇒ apply δ ; reject ⇒ no-op (applied = committed)
             5. emit deterministic receipt + receipt_hash
   │
follower:  replay block body ⇒ MUST reach identical (state, root, receipt)
```

The single most important structural fact: **the proposer is re-executed inside
the disposer**. The node does not consume the publisher's or writer's *claimed*
selection; it recomputes the table lookup from `(P, s, o)` itself, and `P` is
admitted only if `h(P)` equals the request's `expected_policy_hash`. A claimed
action, score, receipt, or proposed state in the request is not an input to
authority — it is forbidden outright (§6.1).

### 2.3 Payoffs

- **Honest publisher/writer/reporter**: deterministic, in-envelope updates;
  positive expected utility from a well-tuned controller (the replay grids in
  `AUTONOMOUS_GOVERNANCE_Q_POLICY.md` measure this as frontier-regret ≈ 0).
- **Any deviator**: payoff is the value of a governed parameter landing outside
  the disposer's envelope, *times the probability the node accepts it*. The
  security claim is that this probability is zero, so the deviation payoff is
  zero minus the cost of trying — i.e. strictly dominated by honesty.

---

## 3. The two security properties, restated

The plan states them as existential queries; here they are the equilibrium
conditions the whole design exists to guarantee.

**P1 — Authority soundness (no proposer/forge profit).**

```
¬∃ request r :  NodeAccepts(r)  ∧  Disposer(committed_state(r), r) = REJECT
```

There is no request the live node admits that the deterministic gate suite,
recomputed against committed state, would reject. Equivalently: the node's accept
set equals the disposer's accept set. The proposer cannot enlarge it; a forged
result field cannot enlarge it.

**P2 — Replay equivalence (no equivocation profit).**

```
¬∃ body b :  WriterAccepts(b)  ∧  FollowerReplay(b) ≠ WriterPostState(b)
```

Every accepted governance body replays, on any follower, to the same post-state,
root, and receipt. No writer can present one outcome to the chain and a different
one to a verifier.

P1 is a property of a *single* node's decision function. P2 is a property of the
decision function being a *pure, deterministic* function shared by all nodes.
Both are decidable over the bounded model (§8), which is what makes Phase 4
formal evidence feasible rather than aspirational.

---

## 4. Adversary taxonomy and what the mechanism denies each one

Each row is a deviation and the specific gate/structure that makes its payoff
zero. Symbols are real functions in `autonomous_governance_q_policy.py`.

| # | Adversary move | What they hope for | Denied by | Residual |
|---|---|---|---|---|
| A1 | Submit a request asserting `approved`/`receipt`/`proposed_state`/`action_id`/`gate_recheck` | node trusts the claim | `FORBIDDEN_SURFACE_ADMISSION_RESULT_FIELDS_V1` → `direct_result_field_forbidden:*`, hard reject | none |
| A2 | Swap the policy artifact for a more permissive table | controller proposes their action | `expected_policy_hash` must equal `policy_content_hash_v1(P)`; mismatch rejects before evaluation | publisher trust → §9, Phase 3 |
| A3 | Feed a stale / diverged / volatile observation to dodge a guard | push a delta through a calm-only gate | `_safety_errors` core `[committed]`: `max_freshness_lag_epochs`, `max_divergence_bps`, `max_volatility_bps`, `min_liquidity_depth_bps`, cooldown (+ extended confidence/concentration/churn/stress controls `[P1-WIP]`) | oracle within-envelope bias → §7 |
| A4 | Move a single parameter far in one step | large jump to a profitable value | **surface path**: `_governance_surface_gate_report` + `gov_gate.py` bounds/step caps `[committed]`; older pointwise packet: `_revision_envelope_errors` (`*_next_out_of_bounds`, `*_step_exceeded`) | none (per-step bounded) |
| A5 | Oscillate a parameter up/down to pump a fee/funding cycle | extract on each flip | `_anti_oscillation_failures`: reversal vs `previous_approved_deltas` direction is skipped | none for budgeted params |
| A6 | Take many small valid steps to ratchet a parameter to an extreme | reach a state no single step allows | `_trajectory_budget_failures`: `used + |δ| > limit` per parameter | budget sizing → §8 |
| A7 | Re-submit at high frequency (griefing / churn) | constant pressure, or DoS the surface | `min_cooldown_epochs` (cooldown_not_elapsed) `[committed]`; `max_recent_governance_churn_bps` `[P1-WIP]` | churn ceiling lands with Phase 1 |
| A8 | Replay the same accepted tx twice | apply a delta twice | `tx_id` idempotency at the node (Phase 2 append report), pre/post epoch checks | node-wiring obligation §8 |
| A9 | Present a different outcome to a follower | equivocate on the root | determinism of the disposer + receipt hashing (P2) | node-wiring obligation §8 |
| A10 | Drive authority-changing parameters (verifier key, image id, signer set) | upgrade-oracle capture | these are **not in** `SURFACE_PARAMETER_NAMES_V1`; routed to the governance authority gate (Phase 3) | authority-gate completeness |
| A11 | Bias the *offline* training data so the frozen table prefers their action | controller ranks their move first | proposer has no authority: ranking only changes *search order*; the disposer still rejects out-of-envelope moves (P1) | a *worse controller*, never an *unsafe* one |

A11 is the keystone of the whole design and deserves emphasis: **even a fully
adversarial training pipeline cannot produce an unsafe runtime.** The worst a
poisoned table can do is propose bad-but-still-gated actions first, wasting
exact-gate checks (a *liveness/efficiency* degradation), or propose actions that
all get rejected (a no-op). It can never make the node admit something the gates
reject, because the gates are recomputed independently of the table's scores.
This is why the plan can let "Julia, EBRM, and other optimizers stay offline"
without those optimizers being in the trusted computing base.

---

## 5. The proposer–disposer separation as a mechanism-design principle

State the separation as an invariant on the authority function:

> **Authority independence.** The disposer's decision is a function of
> `(committed_state, observation, frozen_policy_bounds, timing)` only. The
> proposer's *scores and ranking* are **not** arguments to any accept/reject
> branch.

Two consequences:

1. **Strategy-proofness of the disposer with respect to the proposer.** Be
   precise about what the proposer *can* and *cannot* do. It **can** change
   *which* in-envelope action is selected and applied — a different frozen table
   may rank `hold` above `raise_fee_10` or vice-versa (`_select_action` /
   `_ranked_action_ids` pick the action whose deltas are then gated and, if
   admitted, applied). What it **cannot** do is cause an *out-of-envelope*
   acceptance: because the proposer's scores never enter an accept condition, no
   manipulation of the proposer (A11, A2-with-hash-break) can make the disposer
   admit an action the gates would reject. The precise invariant is therefore
   *the proposer cannot enlarge the disposer's accept set* — not the stronger,
   false claim that it never affects which admissible action is chosen. The
   learned layer is an advisory, non-binding signal over admissible options; the
   incentive to misreport it is bounded by §6.4/§8 (any selected action is still
   bounded and budgeted), so the worst a poisoned table buys is a worse choice
   *among already-safe actions*, never an unsafe one.

2. **The action vocabulary is finite and the bounds are total.** `_select_action`
   chooses one id from `policy["actions"]`; `_revision_envelope_errors` and
   `_safety_errors` are total over the surface parameter set
   `SURFACE_PARAMETER_NAMES_V1`. So the disposer's accept set is a finite,
   enumerable region of parameter space. "Safe" is not a vibe; it is a decidable
   predicate (§8).

A subtle but real requirement falls out of this: **the disposer must drive off
its own closed parameter set, not off the request's supplied map.** This is the
same class of bug WS2 fixed for proof bindings (drive gates off the closed
required-field set, never the attacker's map). Here it shows up as: bounds and
budget checks iterate `SURFACE_PARAMETER_NAMES_V1` / the policy's declared
`trajectory_budget` keys, and a parameter absent from the proposal is a
`*_next_missing` error — *not* a silently-skipped check. Phase 4 should pin this
as a non-vacuity obligation (§10, O5).

---

## 6. Per-gate incentive justification

Each gate is here because it prices out a specific deviation. A gate with no
deviation behind it is dead weight; a deviation with no gate is a hole.

### 6.1 Admission boundary — `admit_autonomous_governance_surface_request_v1` `[P1-WIP]`
Denies **A1**. The forbidden-field set makes "authority by assertion" impossible:
a caller cannot supply `approved`, `proposed_state`, `applied_state`, `receipt`,
`step`, `scores`, `action_id`, or `gate_recheck`. The node recomputes all of
them. `ok = step.ok AND admitted` means a *receipt-rejected no-op* is reported to
the caller as a rejected admission, not a success — closing the "valid receipt
for a no-op" misread. This is the autogovernance analogue of WS2's non-trust
clause: no field asserted by the requester is ever an accept input.

### 6.2 Policy-hash pin — `policy_content_hash_v1` vs `expected_policy_hash`
Denies **A2**. Binds the runtime to a reviewed artifact. Game-theoretically it
converts "which controller runs" from a live, manipulable choice into a
commitment made offline under review. The residual (who is allowed to publish a
new hash) is exactly the authority question Phase 3 answers.

### 6.3 Oracle safety gates — `_safety_errors`
Denies **A3**. These bound the *input* manipulation surface. The controller is
only allowed to act when the world is calm and observed freshly. The **committed**
core controls are: freshness lag, divergence, volatility, liquidity-depth floor,
cooldown, and `emergency_pause`. The **[P1-WIP]** extended controls — confidence
floor, liquidity-concentration ceiling, churn ceiling, proof-market-health floor,
validator- and network-stress ceilings — exist in the Phase-1 working tree but
are not yet committed; an analysis that relies on a parameter being gated along
one of *those* dimensions must confirm the control is present in the promoted
module (a report bad *only* along an extended dimension trips a gate **only**
once that control lands). The strategic reading: an
adversary who controls the oracle within its signing/quorum limits still cannot
trigger an action *during the conditions where a wrong action is most damaging*,
because those conditions trip a safety gate first. See §7 for the bounded-damage
model that makes this precise.

### 6.4 Bounds and step limits — two distinct paths, do not conflate them
Denies **A4**. There are two parameter families with two different enforcers, and
this is a real implementation distinction Phase 4 must respect:

- **Surface path** (`SURFACE_PARAMETER_NAMES_V1`: fee/router-split/MCR/CCR/whale/
  funding-cap) — the bounds and per-epoch step caps are enforced by
  `_governance_surface_gate_report` `[committed]`, which composes the
  `gov_gate.py` fee/router/collateral/whale/funding/master gates and the
  Tau-verified governance specs. The surface evaluator
  (`evaluate_autonomous_governance_surface_q_policy_v1`) **does not** call
  `_revision_envelope_errors`. This is the production AutoGovNEXT path.
- **Older pointwise packet** (`PARAMETER_NAMES_V1`: `fee`, `buyback`, tiers,
  weights) — `_revision_envelope_errors` `[committed]` enforces
  `minimum ≤ next ≤ maximum`, `|next − current| ≤ step`, width caps (U16/U32),
  and the ordering constraints (`tier1 < tier2`, `weight1 ≤ weight2 ≤ weight3`).
  The tier/weight ordering invariants live **here**, not on the surface params.

Either way the property is *single-step containment*: one accepted action moves
any parameter by at most its `step`, and never outside `[minimum, maximum]`.
Necessary but **not sufficient** — see §8. When O3/O4 (§10) are discharged for
the production path, prove them against `_governance_surface_gate_report` +
`gov_gate`, not the pointwise helper.

### 6.5 Anti-oscillation — `_anti_oscillation_failures`
Denies **A5**. For enabled parameters, a candidate whose direction reverses the
last approved nonzero delta is skipped before the exact gate. This removes the
up-down-up pump cycle: an attacker cannot harvest a fee on each direction flip
because the reversal candidate is never selected. Note it compares against
`previous_approved_deltas` (committed history), not the proposal, so it cannot be
spoofed by the request.

### 6.6 Trajectory budget — `_trajectory_budget_failures`
Denies **A6**. This is the **repeated-game** defense and the most important
single idea in the dynamic analysis; it gets its own section (§8).

### 6.7 Cooldown and churn — `min_cooldown_epochs` `[committed]`, `max_recent_governance_churn_bps` `[P1-WIP]`
Denies **A7**. Rate-limits the surface. `cooldown_not_elapsed` (committed) enforces
a minimum epoch gap between updates; the churn ceiling (Phase-1 WIP) refuses action
when recent governance activity is already high. Together they bound the
*frequency* of moves independently of their size, which is what a griefer or a
fast-pump attacker needs. Until the churn control lands, only the cooldown gap is
enforced — so an A7 analysis that leans on the churn ceiling must confirm it is
present in the promoted module.

### 6.8 Composed surface gates — `gov_gate.py` + Tau specs
The fee/router/collateral/whale/funding/master gates (reported as
`governance_surface_all_gates_ok`) enforce the cross-parameter invariants the
per-parameter bounds cannot see — e.g. the fee-router split must remain a
conserved partition, collateral ratios must stay coherent, and the whale-defense
`staker_bps` split cap holds (the load-bearing global defense identified in the
zUSD whale-recapture analysis; the exact numeric bound is enforced in
`gov_gate.py`, not in this module — confirm it there before citing a number).
These are the *joint* feasibility constraints; bounds are the *marginal* ones.

---

## 7. The oracle as residual trust root: bounded damage under bounded corruption

The mechanism does **not** claim oracle truth (`does_not_claim_oracle_truth` is a
hardcoded non-claim). The honest model is *bounded damage under bounded
corruption*:

> If the oracle is corrupted but its reports remain within the safety envelope
> (fresh enough, divergence/volatility/confidence within the configured bounds,
> signed by the required quorum), then any parameter move it can induce is itself
> within one `step` of the committed value and within the trajectory budget over
> any window. If the corruption pushes a report *outside* the envelope, the
> safety gate refuses to act at all.

So the oracle's influence is clamped on both ends: in-envelope reports can only
nudge parameters by bounded, budgeted amounts; out-of-envelope reports produce
no action. The adversary's best case is to walk a parameter toward a preferred
edge at the budget rate during genuinely calm, fresh, low-divergence conditions —
which is exactly the regime where a small parameter change is *least* damaging.
This is the design's answer to "garbage in": oracle reports inside tolerance can
only move parameters a little, and reports outside tolerance produce no move.

This bounded-damage statement is a candidate theorem (O3, §10). It also marks the
clean boundary with the Oracle workstream (Phase 5.6 / WS4): tightening the
*quorum and divergence bounds* shrinks the in-envelope manipulation set; that is
oracle work, not autogovernance work, and the two compose.

---

## 8. The trajectory budget is what makes single-step safety into multi-step safety

This is the part most easily missed, so it is stated as a lemma.

**Observation.** Per-step bounds (§6.4) are insufficient for dynamic safety. If
the only constraint were `|δ| ≤ step` and `min ≤ next ≤ max`, then a controller
(honestly or adversarially steered) could take `k` valid steps of size `step` in
one direction and reach `current ± k·step`, i.e. *any* point in `[min, max]`. The
per-step gate is memoryless; a patient adversary defeats every memoryless gate by
salami-slicing.

**Defense.** `_trajectory_budget_failures` `[committed]` checks a
per-parameter cumulative `trajectory_used` value as
`used + |δ| > limit ⇒ reject`. The multi-step owner is
`run_autonomous_governance_surface_trajectory_v1` `[committed]`: it advances
`trajectory_used` by `|applied − committed|` only on admitted state-changing
steps, preserves it on rejections and admitted holds, records
`trajectory_used_after` in each step record, and hashes the full trajectory
receipt. A follower runs
`verify_autonomous_governance_surface_trajectory_v1` to recompute the same
threading and refuse a receipt whose replay diverges.

**Runner custody is load-bearing.** The accumulator is only state *across* steps
if a runner/node feeds each previous `trajectory_used_after` into the next
commit call. The single-step commit cannot prove this history by itself; it
bounds *this* step against *the supplied* `trajectory_used`. A caller that
submits each step with an empty or reset `trajectory_used` gets per-step bounds
back (A4) but loses the cumulative bound (A6): every step looks fresh. The
bounded-drift lemma below is conditional on the committed runner or a deployed
node append path that threads the accumulator monotonically. The integration
runner now provides that custody; the deployed node path must make it mandatory.

**Session custody closes the receipt-boundary reset.** A trajectory receipt can
still end, so the reset question moves to the boundary between receipts.
`continue_autonomous_governance_surface_trajectory_v1` re-verifies the parent
receipt and derives the child carry-in only from the parent's verified finals:
`final_state`, `trajectory_used_final`, `previous_approved_deltas_final`,
`last_update_epoch_final`, `trajectory_budget`, and `chain_head`.
`verify_autonomous_governance_surface_session_v1` independently checks the
ordered session: fresh genesis, exact boundary carry, one policy hash, one
budget, strictly increasing boundary epochs, completed receipts, drift
conservation, and monotone session usage. This makes reset a visible verification
failure in the integration artifact path.

**Single-head custody closes fork and rollback admission through the API.**
`admit_autonomous_governance_session_continuation_v1` validates the current
store, advances only from the current pinned head, archives the new pin and
receipt on success, and returns the unchanged store on refusal. A fork branch
fails because the current head has already moved; a rollback replay fails the
same chain-head and boundary-epoch checks. The store hash and receipts-replayed
audit make corruption loud, but protecting and distributing exactly one live
store blob is still a deployment/ordering-layer responsibility.
`autonomous_governance_session_store_file.py` now provides the local deployment
repository for that blob: atomic JSON replacement, an exclusive lock sidecar,
and `expected_store_hash` compare-and-swap refusal. That closes stale local
writers that use this API. Global DA or node apply ordering remains a separate
requirement.

**Live apply admission binds committed state to store custody.**
`admit_autonomous_governance_live_session_file_update_v1` is the integration
boundary a node/apply layer can call before mutating governance surface
parameters. It requires the caller's committed surface state to equal the
persisted store head, requires an `expected_live_context_hash`, verifies the
trajectory from that head, advances the file-backed store, then returns the new
`applied_state`. A mismatched context, forged receipt, stale store hash, or
committed-state/head mismatch is a no-op result.

**Lemma (bounded drift).** Over any governance trajectory, the total absolute
movement of a budgeted parameter is at most its `limit`, regardless of the number
of steps, the action ranking, or the observation sequence — provided every step
passes through `commit_…_v1` and the accumulator is carried forward.

```
Σ_steps |applied_t − committed_t|  ≤  limit      (per budgeted parameter)
```

**Why it closes A6.** The ratchet attack's payoff was "reach an extreme via many
small valid steps." The budget makes the reachable set over the *entire*
trajectory equal to a ball of radius `limit` around the trajectory's start, not
the full `[min, max]` interval. The attacker's reachable advantage is now `limit`,
a *chosen, auditable* quantity, instead of unbounded drift.

**Design obligations this imposes (for Codex):**

- The accumulator must advance on **admitted state-changing** steps only, and
  must be the single source of truth carried between epochs. The committed
  trajectory runner implements this; a no-op or admitted hold must not consume
  budget.
- The budget reset policy is a **mechanism parameter with teeth**: whoever can
  reset `trajectory_used` can re-open the drift. The integration session verifier
  now treats a reset as a verification failure, and the session store refuses
  fork/rollback admission through its API. Renewing or replacing a session still
  needs an authority action or fixed era rule before live promotion.
- The bounded-drift lemma is the headline Phase 4 theorem (O2, §10). It is
  decidable over the bounded model: finite parameters, integer deltas, integer
  budgets.

---

## 9. Authority actions are removed from the game, not gated inside it

The bounded surface (`SURFACE_PARAMETER_NAMES_V1`) is deliberately *small* and
*non-authority*: fees, the router split, collateral ratios, whale-defense split,
funding cap. Parameters that change *what "valid" means* — verifier keys, image
ids, policy registries, threshold signer sets, deployment profiles — are **not in
the surface set at all**. Per the plan's Phase 3, those route to
`evaluate_governance_authority_v0` with timelock + threshold evidence, and proof
clients pin expected image ids / verifier keys client-side.

Mechanism-design reading: AutoGovNEXT is allowed to play only the *low-stakes*
game (tuning bounded economic parameters). The *high-stakes* game (who is allowed
to redefine the rules) is removed from the autonomous player's action set
entirely and handed to a human-or-threshold authority with delay. This is the
single most important scoping decision and the line the plan's promotion boundary
draws: AutoGovNEXT "cannot claim … upgrade-key correctness unless the governance
authority and client pinning lanes are also complete." The autonomous controller
must never become an upgrade oracle, and the way that is guaranteed is *exclusion
from the vocabulary*, not *a gate inside it*.

Obligation O4 (§10): a test/proof that no action in any admissible frozen
vocabulary touches a non-surface (authority) parameter — i.e. the autonomous path
is *type-confined* to `SURFACE_PARAMETER_NAMES_V1`.

---

## 10. Provable obligations for Phase 4 (hand-off to formal evidence)

The plan's Phase 4 asks for a Lean/ESSO/Tau safety-envelope artifact for
`Admit(request) → GatesAccept(request) ∧ CommitIsNoopOnReject(request)`. This
section refines that single line into the obligation set the mechanism actually
needs. Each is decidable over the bounded model (finite vocabulary, integer
parameters, integer budgets), so each is a candidate for ESSO/Tau (linear
integer) or Lean (the inductive budget argument).

| ID | Property | Statement | Denies |
|---|---|---|---|
| **O1** | Authority soundness (P1) | `NodeAccepts(r) → Disposer(committed(r), r) = ACCEPT` | A1, A2, A11 |
| **O2** | Bounded drift | over any trajectory, `Σ|applied−committed| ≤ limit` per budgeted parameter | A6 |
| **O2b** | Session continuity | over any accepted session, each child carry-in equals the verified parent finals and session-used is monotone | A6 boundary reset |
| **O2c** | Single-head admission | store admission either advances from the current head to a verified child or returns the unchanged store | fork / rollback admission |
| **O3** | Bounded damage | in-envelope observation ⇒ `|applied − committed| ≤ step` and budgeted; out-of-envelope ⇒ no-op | A3 |
| **O4** | Type confinement | no admissible action mutates a parameter ∉ `SURFACE_PARAMETER_NAMES_V1` | A10 |
| **O5** | Non-vacuous totality | every gate drives off the closed parameter set; a missing proposed parameter is an error, never a skipped check | silent-skip holes |
| **O6** | No-op faithfulness | `¬admitted → applied_state = committed_state` exactly (no partial mutation) | reject-with-side-effect |
| **O7** | Replay equivalence (P2) | the disposer is a pure function of `(committed, request)`; `receipt_hash`/`trajectory_used_after` bind the transition; follower replay matches | A8, A9 |
| **O8** | Idempotency | duplicate `tx_id` returns the prior append report without reapplying | A8 |

O1, O5, O6 are the literal refinement of the plan's Phase-4 line. O2 is the
dynamic-safety theorem the plan's bounded model gestures at but does not state.
O3 connects to the oracle workstream. O7/O8 are node-wiring properties (Phase 2)
that need writer/follower replay tests, not just unit tests.

**Suggested discipline (from the WS2 / governance-hardening campaigns):** for the
gate functions, build a *characterization corpus first* — capture the exact
`(accept, errors)` over a deterministic sweep of in- and out-of-envelope
requests, commit it, then prove the refactored/▶formal artifact reproduces it
byte-for-byte. A formal artifact that passes but whose corresponding test corpus
is vacuous (e.g. every case rejects for an unrelated reason) is the failure mode
to guard against; O5 is specifically there to catch it.

---

## 11. Open mechanism-design questions (for review, not yet decided)

These are genuine design choices the code does not yet pin down. Flagging them so
Codex and review can resolve them deliberately rather than by default.

- **Q1 — Budget reset / window policy.** Resolved for the integration artifact
  path by session continuity: a child receipt must carry the verified parent's
  `trajectory_used_final`, cooldown, oscillation history, budget, and chain
  head, or `verify_autonomous_governance_surface_session_v1` rejects it. The
  session store adds a single live head for API admission, so fork branches and
  rollback replays are refusals. Live promotion still needs an explicit renewal
  rule: either a governance-authority reset or a fixed era-length window.

- **Q2 — Cumulative cross-parameter envelope.** Budgets are per-parameter. Is
  there a *joint* move (e.g. fee up + reserve down) that is individually budgeted
  but jointly extractive? The composed master gate covers *static* joint
  feasibility; a *dynamic* joint budget (total economic movement) may be needed.
  Open.

- **Q3 — Oracle quorum vs in-envelope bias.** O3 bounds damage *given* the
  envelope. The tightness of that bound is set by the oracle's divergence/
  confidence configuration, which is WS4's lever. The two workstreams must agree
  on the numbers; document the assumed bounds where O3 is proved.

- **Q4 — Selection-order liveness under a poisoned table.** A11 shows the safety
  bound. A poisoned table can still raise the exact-gate check count
  (cost/latency) in `first_admissible` mode by ranking rejects first. Is
  there a DoS-via-ranking concern at the node (prover/gate work per request)?
  Likely bounded by the finite vocabulary, but worth a metering note (cf. the
  prover-cost/`max_cycles` gap flagged elsewhere).

- **Q5 — Tie-breaking determinism across languages.** P2 requires the
  action-list-order tie-break and integer score sums to be reproduced exactly by
  every replayer, including any future Rust follower. This is the same
  cross-language canonical-encoding discipline that bit the CLOB guest
  (label-drift); pin it with a cross-language fixture if a non-Python follower is
  in scope.

---

## 12. What this mechanism does and does not buy (honesty boundary)

Restating the plan's promotion boundary in game terms, so no reader over-reads
this analysis:

**Earned, once O1–O8 hold on a pinned candidate:**
- The autonomous player cannot move a governed parameter outside the disposer's
  envelope (P1/O1).
- Cumulative drift is bounded by a chosen, auditable budget (O2).
- A corrupted-but-in-tolerance oracle can only cause bounded, budgeted moves; an
  out-of-tolerance oracle causes none (O3).
- The autonomous path is confined to non-authority parameters (O4).
- Every node replays to the same root; no equivocation (P2/O7).

**Still requiring separate evidence:**
- Oracle *truth* (only bounded damage, not correctness).
- *Global economic optimality* of the chosen parameters (the replay grids measure
  *frontier regret against a finite vocabulary*, not real-world optimality).
- Safety of *arbitrary future action vocabularies* (O1–O4 are stated over the
  current bounded surface; a new vocabulary re-incurs the action-gate diagnostics
  and O4).
- *Authority/upgrade correctness* (Phase 3 + client pinning).
- *Settlement authorization* (explicitly disclaimed; `does_not_authorize_settlement`).

The autonomous controller is, by construction, a bounded economic-parameter
tuner whose worst case is worse tuning within the disposer envelope, provided
the budget reset (Q1) is gated and the vocabulary stays type-confined (O4). That
is the narrow claim this mechanism should carry.

---

## Appendix A — symbol map (grounding)

| Concept here | Code symbol (`autonomous_governance_q_policy.py`) | Status |
|---|---|---|
| admission boundary | `admit_autonomous_governance_surface_request_v1` | [P1-WIP] |
| commit / no-op-on-reject | `commit_autonomous_governance_surface_q_policy_v1` | [committed] |
| forbidden caller authority fields | `FORBIDDEN_SURFACE_ADMISSION_RESULT_FIELDS_V1` | [P1-WIP] |
| policy hash pin | `policy_content_hash_v1` | [committed] |
| committed-state context pin | `governance_surface_context_hash_v1`, `expected_committed_context_hash` | [committed] |
| bounded surface parameters | `SURFACE_PARAMETER_NAMES_V1` | [committed] |
| oracle safety gates (core) | `_safety_errors`, `_check_max`, `_check_min` | [committed] |
| oracle safety gates (extended: confidence/concentration/churn/proof-health/validator/network stress) | settings inside `_safety_errors` | [P1-WIP] |
| surface bounds + step caps | `_governance_surface_gate_report` + `gov_gate.py` | [committed] |
| pointwise-packet bounds + steps (tier/weight order) | `_revision_envelope_errors`, `BoundedParameter` | [committed] |
| anti-oscillation | `_anti_oscillation_failures` | [committed] |
| trajectory budget check | `_trajectory_budget_failures` | [committed] |
| trajectory accumulator custody | `run_autonomous_governance_surface_trajectory_v1` | [committed] |
| trajectory replay verification | `verify_autonomous_governance_surface_trajectory_v1` | [committed] |
| client-side trajectory refuse-loop | `admit_verified_autonomous_governance_surface_trajectory_v1` | [committed] |
| cross-trajectory continuation | `continue_autonomous_governance_surface_trajectory_v1` | [committed] |
| whole-session verification | `verify_autonomous_governance_surface_session_v1` | [committed] |
| policy pin lineage | `build_genesis_policy_pin_v1`, `rotate_policy_pin_v1` | [committed] |
| session-head pin lineage | `open_autonomous_governance_session_v1`, `advance_autonomous_governance_session_v1` | [committed] |
| single-live-head store admission | `initialize_autonomous_governance_session_store_v1`, `admit_autonomous_governance_session_continuation_v1` | [committed] |
| store receipts-replayed audit | `verify_autonomous_governance_session_store_v1` | [committed] |
| file-backed store admission | `initialize_autonomous_governance_session_store_file_v1`, `admit_autonomous_governance_session_file_continuation_v1` | [committed] |
| file-backed store audit/head read | `verify_autonomous_governance_session_store_file_v1`, `current_session_store_file_head_v1` | [committed] |
| live apply admission wrapper | `admit_autonomous_governance_live_session_file_update_v1`, `autonomous_governance_live_session_file_context_hash_v1` | [committed] |
| proposer (re-run inside disposer) | `_select_action`, `_ranked_action_ids`, `_bin_index` | [committed] |
| offline training only | `q_learning_update_fixed_point_v1` | [committed] |
| surface evaluator | `evaluate_autonomous_governance_surface_q_policy_v1` | [committed] |

Status is as of the branch carrying this document. **[P1-WIP]** symbols are
still working-tree admission hardening and must be reverified before promotion.
**[committed]** symbols are present in the integration modules on this branch.
The integration node/apply guard now requires these receipts and context hashes
before returning an applied state. A production node still has to route live
governance messages through that guard and provide a globally ordered store
custody rule before this becomes a live governance claim.
