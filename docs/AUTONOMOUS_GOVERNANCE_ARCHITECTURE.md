# Autonomous Governance Architecture (ZenoDEX)

How ZenoDEX can be governed **autonomously** — by a controller or a learned policy,
not only by human votes — while staying safe, by separating a (possibly heuristic /
ML) **proposer** from a formally-verified **bounded gate**. The project's north star
applied to governance: **trust the math, not the proposer.**

## Status & non-claims (read first)

This document mixes what is **built and verified** with what is **designed but not
built**. The distinction is load-bearing; do not let the vision blur it.

| Layer | Status |
|---|---|
| The **gate** — pointwise-revision spec suite (`src/tau_specs/governance/`) | **Built + merged** via PR #363. Reviews: Gemini A+, Codex Logic A / Correctness A-. |
| The existing **revision pipeline** it builds on (`docs/REVISION_PIPELINE.md` + the three `src/tau_specs/*_v1.tau` specs) | **Pre-existing** in the repo. |
| The **oracle** the autonomous loop would read | **L2** (trust-minimized), per `docs/ORACLE_TRUST_POSTURE.md`. Not trustless. |
| The **autonomous proposers** (PID controller, frozen Q-learning table) | **Reference implementation** — `src/tau_specs/governance/gov_proposers.py` (deterministic PI + frozen Q-table) for simulation/demonstration. NOT a production/live proposer. |
| The **frozen Q/EBRM artifact runtime** | **Built as an offline, verifier-preserving artifact path** — `src/integration/autonomous_governance_q_policy.py`, `src/integration/autonomous_governance_trajectory.py`, `tools/autonomous_governance_policy_factory.py`, `tools/autonomous_governance_q_policy.py`, and `docs/AUTONOMOUS_GOVERNANCE_Q_POLICY.md`. It ranks proposals, binds committed context hashes, runs/verifies multi-step trajectories, and emits receipts; exact gates still decide admission. |
| The **autonomous loop** (proposer → gate → apply/no-op) | **Reference implementation** — `src/tau_specs/governance/gov_loop.py`; the safety property (the gate bounds a poisoned proposer) and `curr`-binding are empirically tested (`tests/tau_specs/governance/test_gov_loop.py`). NOT wired to a live governance flow. |
| The **live autonomous loop** (the reference loop driving *committed on-chain* parameters from *attested* state) | **Partially built in integration code.** The Q-policy step can require a committed-context hash and the trajectory runner threads state across epochs. The deployed node/apply flow that requires those artifacts is still open **WS5** work. |

**No autonomous proposer is wired into any governance path today.** Default governance
authority is unchanged. Nothing here is deployed or promoted. The PID/Q-table sections
below are an architecture proposal, not a description of running code.

## 1. Thesis: separate the proposer from the gate

A governance update has two roles, deliberately separated:

| Role | Who | What it is |
|---|---|---|
| **Proposer** | staker vote, **PID controller**, or a frozen **Q-learning lookup table** | computes the *next* parameter value |
| **Gate** | the verified `gov_*_v1.tau` specs (+ `gov_gate.py` runtime mirror) | decides whether *next* is **admissible** |

The gate is **proposer-agnostic** (`src/tau_specs/governance/gov_action_bound_v1.tau`):
whatever computes `next` — a human vote, a PID loop on the oracle feed, or a hash-pinned
Q-table — the *same* verified gate admits it only if it is governance-approved, past the
timelock, within `[min, max]`, and within one bounded `step` of the current value.

So a mis-trained, poisoned, or oracle-manipulated proposer **can never escape the bounded
envelope** — the worst it can do is move a parameter by one `step` per revision inside
`[min, max]`. **The bound is the safety, not trust in the proposer.** This is what makes an
autonomous proposer safe to run at all: its trustworthiness is decoupled from protocol
safety (subject to the binding precondition in §5).

```text
   PROPOSER (untrusted, may be ML/heuristic)        GATE (verified, fail-closed)        STATE
   ┌──────────────────────────────────────┐        ┌─────────────────────────┐
   │ staker vote                           │        │ approved?               │
   │ PID/PI controller  ── reads oracle ──▶│ next   │ past timelock?          │  apply iff
   │ frozen Q-learning lookup table        │ ──────▶│ next ∈ [min,max]?        │ ─────────▶ committed
   └──────────────────────────────────────┘        │ |next − curr| ≤ step?   │   admit    parameter
                                                    └─────────────────────────┘            (registry)
                                          a bad proposer can move a param by ≤ 1 step/revision
```

## 2. The gate (built + verified)

### 2.1 The existing revision pipeline (prior art)

ZenoDEX already has a pointwise-revision pipeline (`docs/REVISION_PIPELINE.md`):

```text
proposal → governance vote → timelock → revision_policy → parameter_registry → settlement
```

- `src/tau_specs/governance_timelock_v1.tau` — proposals must be delayed by a minimum timelock.
- `src/tau_specs/revision_policy_v1.tau` — bounds + step limits on updatable parameters; requires
  approval + timelock when `exec_req = 1`.
- `src/tau_specs/parameter_registry_v1.tau` — applies *approved* updates, else keeps current values.

**Safety guarantee (existing):** as long as the settlement spec consumes parameters *only* from
the registry, an update cannot bypass the revision policy. **Immutable invariants** (conservation,
fail-closed rejection, the AMM curve, settlement/proof-binding) are *not* parameters and are never
touched by revision; only **parameters** (rates, caps, floors, thresholds, weights) change.

### 2.2 The pointwise-revision spec suite (`src/tau_specs/governance/`)

The new suite extends that pipeline with concrete, machine-verified per-surface gates and a
universal proposer-agnostic gate. Guardrail constants are **immutable** `{ #xHHHH }:bv[16]`
literals (changeable only by a spec-version bump, never by a pointwise revision); only `curr`/`next`
(and, for `action_bound`, the bounds) are inputs.

| Spec | Surface | Shape | Immutable guardrails |
|---|---|---|---|
| `gov_action_bound_v1.tau` | universal gate (any proposer) | factored bounds + step | bounds are inputs |
| `gov_fee_revision_v1.tau` | swap fee (bps) | bounds + step | `≤ 1000` (10% cap); `\|Δ\| ≤ 50`/rev |
| `gov_router_split_revision_v1.tau` | fee-router 4-way split (sum) | sum-budget | each `≤ 10000`; **sum = 10000** |
| _(router per-share drift)_ | fee-router split (anti-whiplash) | per-share `action_bound` | per-share `\|Δ\| ≤ 500` |
| `gov_collateral_ratio_revision_v1.tau` | zUSD MCR / CCR | ordered + bounds + step | `mcr ≥ 10000`, `ccr ≤ 30000`, **`mcr ≤ ccr`**, `\|Δ\| ≤ 1000` |
| `gov_whale_defense_revision_v1.tau` | `redeem.staker_bps` | ceiling + step | `≤ 7000`; `\|Δ\| ≤ 500` |
| `gov_funding_rate_revision_v1.tau` | perps funding-rate cap | bounds + step | cap `≤ 200` bps (2%/epoch); `\|Δ\| ≤ 25` |
| `gov_revision_master_v1.tau` | composite | factored AND of the 4 economic-core surfaces | union of fee/router/collateral/whale + `MIN_DELAY = 24` (funding is **not** composed here — it is standalone) |

**Wrap-safe timelock.** All gates use `current ≥ proposal AND current − proposal ≥ MIN_DELAY`
(subtraction-guard), not the naive `current ≥ proposal + MIN_DELAY`, which is bypassable by
`bv[16]` modular wrap when `proposal` is near `2^16`. `MIN_DELAY = 24` is in the runtime's own
time unit (epochs/blocks); `proposal_ts` and `current_ts` must be supplied in the same unit.

**Factoring is mandatory.** Coupling (not parameter count or bit width) is the cost driver: a
monolithic formula does not normalize, but a factored one (one output bit per concern, ANDed)
stays tractable. The fee-router is therefore two concerns — the sum-budget (`gov_router_split`)
and the per-share anti-whiplash drift, where each share's drift is the universal `gov_action_bound`
gate applied to that share. The composite master is verified **factored**: each `oN` bit in
isolation (with teeth) + the `o1` AND-composition, because the all-surfaces monolith does not
normalize on the current Tau build.

### 2.3 Verification (hybrid: Tau validates, Python computes)

- `src/tau_specs/governance/validate_governance_specs.py` drives Tau at the **Boolean-function
  layer** (`sat`/`unsat`), *not* the temporal `always` layer (a temporal `always` is vacuously
  satisfied by the empty trace, so `sat`/`unsat` on it prove nothing). For each spec it checks:
  it compiles; it is **non-vacuous** (`sat` — admits some revision); and **every guardrail has
  teeth** (`unsat` — a violating revision provably cannot be admitted).
- `src/tau_specs/governance/gov_gate.py` is the Python runtime mirror, strictly **fail-closed**:
  it hard-rejects out-of-domain values *and* non-`bool` control flags (stricter than the `bv[16]`
  core, never weaker).
- `tests/tau_specs/governance/test_gov_parity.py` is a **Tau↔Python differential** over a shared
  boundary table (`src/tau_specs/governance/gov_parity_cases.py`): each case is evaluated by both
  the Tau spec (ground `sat`) and `gov_gate.py`, and a disagreement fails the test.
  `tests/tau_specs/governance/test_gov_gate.py` reproduces the teeth in pytest.

Last observed locally: the harness reports `ALL PASS`; `test_gov_gate.py` and `test_gov_parity.py`
pass. These are existence-of-a-passing-run statements, not a committed CI artifact. A committed,
replayable Tau proof artifact (a recorded verifier transcript) is **not** part of the suite yet.

## 3. The proposers (reference implementation)

The gate is proposer-agnostic; these are the candidate proposer populations.
`src/tau_specs/governance/gov_proposers.py` provides **deterministic reference implementations** of
the PI controller and the frozen Q-table (pure integer / fixed-point — no floats or randomness,
because a real on-chain proposer must be replayable); `src/tau_specs/governance/gov_loop.py` composes
a proposer's candidate with the gate. These are for **simulation/demonstration** — they are not
production proposers and are not wired to a live governance flow. The staker-vote proposer below is
not modeled (a live vote is non-deterministic / not replayable).

### 3.1 Staker vote (manual baseline)
Humans choose `next`; the gate bounds it. **Non-deterministic** — a live vote cannot be replayed,
so any offline replay/verification guarantee does *not* extend to it. Risks: sybil/whale capture,
bribery. This is the status-quo authority; the gate simply ensures even a captured vote is bounded.

### 3.2 PID / PI controller (continuous target-tracking — design)
For a **single continuous monetary target with a monotone response** — the canonical case being the
zUSD peg. Proven DeFi precedent: **RAI/Reflexer**, whose controller adjusts a redemption rate from
the market-vs-redemption price deviation, with no human votes. Engineering notes:
- Use **PI, not full PID** — the derivative term amplifies oracle noise into erratic parameter swings
  (RAI is effectively PI). Drop or heavily filter D.
- **Anti-windup** on the integral (a sustained depeg otherwise saturates it and overshoots on recovery).
- A **deadband** so noise / small deviations don't drive churn.
- The per-revision **`step` is the rate-limit** — already enforced by the gate.
- **Not** for discrete/structural choices.

The reference `gov_proposers.py` implements PI in **velocity form** (the committed parameter is the
accumulator; `Δ = Kp·(e − e_prev) + Ki·e`), which has inherent anti-windup and no positional-form
steady-state runaway. Being integer fixed-point, it has a steady-state **deadzone** bounded by the
gain denominator (an error smaller than `ki_den` floor-divides to 0) — an honest limitation of
on-chain-friendly integer control, not a bug.

### 3.3 Frozen Q-learning lookup table (deterministic multi-factor rules — design)
For **discrete, multi-factor** policies (e.g. `(volatility_bin, utilization_bin, peg_dev_bin) →
fee_action`). Train offline (RL or any optimizer), then **freeze** as a hash-pinned artifact. The
live runtime must be a **pure function**: `state → deterministic integer/fixed-point binning →
table lookup → action → hash-bound receipt`. No learning, floats, or nondeterminism at execution
time, so it is consensus-safe and client-verifiable (anyone re-derives the action from the public
state + the pinned table hash). Design constraints:
- **Layered / factored tables** — bin each dimension independently and compose; a monolithic joint
  table over the product of all bins blows up (the same factoring lesson as the spec suite).
- **Updating the table is itself a governed action** — pin it by hash; swapping it goes through the
  timelock + the bounded gate; the client refuses any action not derivable from the pinned table.
- **Determinism is load-bearing** — any float or non-canonical encoding breaks consensus. A
  deterministic, hash-bound decision runtime of this kind is **not implemented** in this repo today
  (the reference proposers below are simulation-grade, not consensus-bound).

### 3.3.1 Layered (hierarchical) Q-tables (reference implemented)
`gov_proposers.layered_q_propose` makes the "layered/factored" constraint concrete: a **regime
layer** (slow/coarse signal, e.g. volatility bin) selects a sub-policy id, and the selected
sub-policy's **action table** (fast signals, e.g. utilization × peg-deviation bins) yields the
action. Cost is `|regime table| + Σ|per-regime action tables|` instead of the joint product. The
WHOLE hierarchy is **one** hash-pinned artifact (`layered_table_hash`) — swapping any layer changes
the pin and is a governed action. Every layer miss (regime bin, dangling sub-policy id, action bin)
is **fail-closed** (propose `curr`, `hit=False`). Validation, digest, and both lookups act on one
private snapshot taken before any caller-controlled iteration runs (the pin/use-TOCTOU discipline).

### 3.3.1.1 Frozen artifact runtime and selection-aware ranking

`src/integration/autonomous_governance_q_policy.py` is the frozen artifact
evaluator for governance-surface updates. It turns observations into integer
bins, sums deterministic Q/EBRM lookup-table layers, ranks a finite action set,
proposes a candidate surface state, and calls the exact `gov_gate.py` functions
before anything can be admitted. The runtime is an ordering engine; the gate is
the admission authority.

The current artifact path uses `first_admissible` selection. The raw ranked
action list is adjusted by deterministic sequence-context blockers before exact
gate scanning:

- anti-oscillation blockers prevent immediate fee/funding reversals;
- trajectory-budget blockers prevent standing-approval walks from spending
  beyond their configured movement budget;
- blocked raw candidates receive a fixed selection penalty and are reported as
  `selection_penalized_candidates`;
- exact gate failures remain separate from selection blockers.

This matters for efficiency and auditability. In the generated evidence,
long-horizon replay keeps frontier utility at `11,380 / 11,380` with zero
regret and zero invalid accepts, while candidate work drops from 164 scanned
candidates to 116. The 48 raw candidates that sequence rules would have blocked
are penalized before the first-admissible scan. The exact gates still receive
116 candidate checks and remain the only admission authority.

Developer entry points:

- `docs/AUTONOMOUS_GOVERNANCE_Q_POLICY.md`: artifact format, metrics, commands,
  and replay interpretation.
- `tools/autonomous_governance_policy_factory.py`: offline policy factory,
  residual EBRM lookup layer, replay reports, and artifact/promotion checks.
- `tools/autonomous_governance_q_policy.py`: sample/evaluate/step plus
  trajectory-run/verify CLI for the frozen policy artifact.
- `src/integration/autonomous_governance_trajectory.py`: deterministic
  multi-step runner, receipt hash chain, and independent replay verifier.
- `tests/integration/test_autonomous_governance_q_policy.py`: runtime behavior,
  exact-gate boundary, and selection-aware ranking tests.
- `tests/integration/test_autonomous_governance_trajectory.py`: trajectory
  threading, invariant tripwires, tamper matrix, and CLI verification tests.
- `tests/tools/test_autonomous_governance_q_table_optimizer.py`: full factory,
  replay, artifact, and promotion-gate regression test.

### 3.3.2 Frozen energy model (energy-based reasoning — reference implemented)
`gov_proposers.energy_propose` is energy-based reasoning in its consensus-safe form: a frozen,
hash-pinned **integer energy function** `E(c) = w_track·(c − target)² + w_move·|c − curr|` is
scored over the **exactly-bounded revision band** `[curr−step, curr+step] ∩ [lo, hi]`, and the
proposer returns the argmin (ties break toward the smallest candidate — a total, replay-stable
order). The trade-off the model "reasons" about is explicit: tracking error toward a per-state
target vs. movement cost (parameter churn). The artifact (`{targets, w_track, w_move}`) is one pin
(`energy_model_hash`); a degenerate both-weights-zero model is rejected at validation. The proposer
is in-envelope **by construction** (it only enumerates the band) — and the gate still independently
verifies bounds, approval, and timelock: a poisoned target or a lying band cannot escape
(empirically tested: the gate no-ops a 9000 proposal under a 1000-cap/50-step fee gate).

### 3.4 Which proposer for which parameter

| Proposer | Best for | Avoid for | Determinism |
|---|---|---|---|
| Staker vote | structural / one-off / contested choices | high-frequency tuning | no (not replayable) |
| PID / PI | one continuous peg-class target (zUSD peg) | discrete or non-monotone params | yes |
| Frozen Q-table | discrete multi-factor rules (fees vs regime) | targets with no clear binning | yes (if frozen + canonical) |

All three flow through the **same** verified bounded gate.

## 4. Safety composition (blast radius)

The gate (`gov_gate.py` docstring) states the safety property: a mis-trained / poisoned /
oracle-manipulated proposer can only move a parameter by `step` per revision inside `[min,max]`.

**This worst-case bound is conditional on the binding precondition in §5.** If an attacker also
controls the `curr` value or the epoch inputs, the step and timelock gates are vacuous and the
envelope is *unbounded*. The `step`-per-revision bound holds **only when `curr` and the epochs are
bound to attested committed state.**

Given that precondition, the composition is: a bad proposer's reachable set per revision is the
bounded band; over N revisions (each timelocked) it can compound only at `≤ N · step`, with each
step independently approval-gated. That is what makes autonomy tolerable — the guardrails, not the
proposer, are the defense.

**The trajectory tier closes the standing-approval gap.** The `≤ N · step` compounding bound
above leans on *per-revision* approval — but real autonomy replaces that approval with a STANDING
grant, and per-step safety is not trajectory safety: under standing approval a poisoned proposer
could walk a parameter from min to max at one legal step per revision. The trajectory tier (§6.1)
bounds the walk itself: at most `DRIFT_BUDGET_BPS[s]` of |delta| per surface per
`DRIFT_WINDOW_EPOCHS` (reference: 3 steps per 720 epochs), at least `GOV_COOLDOWN_EPOCHS` between
applied revisions of a surface, at most `EPOCH_MOVEMENT_BUDGET` aggregate |delta| per applied
multi-surface revision (a coordinated one-legal-step-everywhere regime walk rejects), and the
standing approval itself EXPIRES (charter dead-man) and is revocable/vetoable at any moment.

## 5. Trust posture

### 5.1 Oracle trust is inherited
An autonomous proposer that reads the price oracle **inherits the oracle's trust level.** Per
`docs/ORACLE_TRUST_POSTURE.md`, the ZenoDEX oracle is **L2** (`quorum_attested_honest_scope`):
quorum-attested (no single signer moves the price), fail-closed, replay-bound, and *explicit about
not claiming* the price is the true market price or the source honest. It is trust-**minimized**,
not trustless (L3 proof-carrying provenance is an unbuilt research gap). Therefore an autonomous
proposer is **not** trustless either; it is at most as trustworthy as L2.

The gate **caps** oracle-manipulation damage to the bounded band per epoch — but does not remove
the dependence. The **guardrails are the manipulation defense, not the proposer.** A PID/Q-table
proposer should use the most manipulation-resistant signal available and a deadband; and per the
oracle posture's own rule, **no surface may describe the oracle (or a proposer reading it) as
trustless or proven** until an L3 path ships.

### 5.2 The binding precondition (`curr` and epochs must be attested)
The step-limit `|next − curr| ≤ step` is sound **only if `curr` is the true committed value**, and
the timelock is sound **only if the epochs are attested.** In the gate, `curr` and the epochs are
*inputs*, not read from chain by the spec. A proposer (or relay) that supplies its own `curr`/epoch
can make an arbitrary jump look like a one-step move, or defeat the timelock.

So the live runtime **MUST** bind `curr` and `current/proposal/last-update` epochs to the committed
ledger state alongside the proposal — exactly the repo's **WS2 "right-statement-binding" / non-trust
clause** (no proposer-asserted field is an accept input). **The spec bounds the delta; the runtime
owns the anchor.** The integration runtime now exposes
`governance_surface_context_hash_v1` and optional
`expected_committed_context_hash` checking on the surface evaluator/commit path.
That closes the local artifact boundary when the expected hash comes from an
attested committed-state source. The deployed node still has to make that source
authoritative and mandatory.

## 6. The full autonomous loop (design)

The payoff, when all pieces exist:

```text
attested oracle/ledger snapshot (curr params + epochs, bound to committed state)
  → verified proposer (a PID or frozen Q-table that can itself be a verified/replayable function)
  → verified bounded gate (gov_*_v1.tau + gov_gate.py)
  → parameter_registry (the only parameter source for settlement)
  → committed parameter + cooldown (next revision must clear the timelock again)
```

Every step is intended to be machine-checkable — the proposer's action re-derivable from public
state, the gate's decision replayable, the registry the sole source consumed by settlement. That is
"trust the math" applied to governance. Today the **gate**, the **registry/pipeline**, and a
**reference proposer + loop** (deterministic; simulation; the safety property and `curr`-binding
empirically tested in `gov_loop.py` / `test_gov_loop.py`) are built; the **production** proposer
(tuned/trained on real signals) and the **live** binding/apply wiring — sourcing `curr` and the
epochs from attested committed on-chain state (§5.2) — are open.

### 6.1 The epoch machine: charter, veto, freeze, and the trajectory tier (built + reference)

`gov_epoch.py` is the reference machine that makes standing-approval autonomy concrete. Every
transition is a total function `(state, inputs) -> (state', GovReceipt)` in the CBC shape —
validate before mutate, reject leaves params unchanged (receipts carry canonical params digests,
so no-op-on-reject is checkable: `digest_before == digest_after` on every reject), stable reject
codes with a FIXED documented precedence (`APPLY_PRECEDENCE`).

| Piece | What it is | Why |
|---|---|---|
| **Charter** (`renew_charter`/`revoke_charter`, `gov_charter_v1.tau`) | the autonomous lane's `approved` source: a governed, revocable, **expiring** grant (`ttl ≤ CHARTER_TTL_MAX = 4096`, constitutional — no perpetual charter), pinned to a policy artifact hash | real autonomy cannot use per-revision votes; expiry without renewal halts the lane to HOLD — a **dead-man switch**, autonomy fails closed |
| **Timelock + veto window** (`propose_revision`/`veto_pending`) | a pending action matures `MIN_DELAY` epochs; during that window a guardian can **cancel** (never propose) — veto works even frozen/unchartered | asymmetric authority: stopping is always safe, so the stop is never gated |
| **Freeze** (`set_frozen`) | a committed disaster flag halts propose/apply (veto still works); the machine OBEYS the flag, upstream disaster tripwires decide it | governance must park during oracle divergence / depeg / vault-floor events |
| **Cooldown** (`gov_cooldown_v1.tau`) | ≥ `GOV_COOLDOWN_EPOCHS = 48` between applied revisions per surface (wrap-safe subtraction-guard) | anti-thrash hysteresis, distinct from the timelock |
| **Drift budget** (`gov_drift_budget_v1.tau`) | per-surface Σ\|Δ\| ≤ `DRIFT_BUDGET_BPS[s]` (= 3 steps) per `DRIFT_WINDOW_EPOCHS = 720`, magnitude not direction (oscillation is movement) | per-step-legal walks halt at 3 steps/window — the trajectory bound |
| **Epoch budget** (`gov_epoch_budget_v1.tau`) | aggregate Σ\|Δ\| ≤ `EPOCH_MOVEMENT_BUDGET = 2000` per applied revision across all touched surfaces | the largest single-group action fits exactly; a coordinated every-surface step (4575) rejects |
| **Observables** (`gov_observables.py`) | staleness-guarded deterministic binning feeding the proposers' state keys (binning is consensus-side, import-bound to `gov_proposers.bin_index`) | a stale or future-dated sensor yields NO key → the lane holds; autonomy never acts on dead sensors |

Trust posture matches the multi-surface loop: every gate the machine consults is **import-bound
at module load** (`_MULTI_STEP`, `_COOLDOWN_OK`, `_DRIFT_OK`, `_CHARTER_OK`, `_EPOCH_BUDGET_OK`)
— a forged-gate monkeypatch of gov_gate/gov_loop does not bite (empirically tested, with a
call-counter proving the fake is never consulted). No self-amendment: the trajectory constants
and the charter cap are constitution-tier (version bump only), and an action targeting an
unknown surface (e.g. `charter_ttl`) hard-rejects.

The machine's per-surface core is **inductively verified** in ESSO
(`src/kernels/dex/gov_epoch_machine_v1.yaml`, z3 + cvc5 agree, badge `Inductive(k=1)`,
10/10 queries): param bounds, `drift_used ≤ budget`, pending well-formedness, and four
**guard-presence tripwires** — `apply` copies the pre-state of each guarded condition
(frozen / unchartered / immature / in-cooldown) into an `applied_*` variable that the
invariants pin at 0, so DELETING any guard conjunct is a machine-detected invariant
violation, not a silent hole. The bv[16] wrap-safety of the absolute-epoch comparisons is
verified at the Tau layer (the four trajectory specs carry wrap probes in their teeth),
and the cross-window composition (m windows of budget B ⇒ displacement ≤ m·B, with the
bound attained at a concrete m=3, B=150 instance) is proved in Lean
(`lean-mathlib/Proofs/GovTrajectoryBound.lean`).

## 7. What is verified today vs open

| Item | Status |
|---|---|
| Pointwise-revision gate suite (7 specs + composite) compiles, non-vacuous, every guardrail has teeth | **Done** (harness `ALL PASS` locally) |
| `gov_gate.py` Python mirror, fail-closed on out-of-domain + non-bool flags | **Done** (`test_gov_gate.py`) |
| Tau↔Python differential parity | **Done** (`test_gov_parity.py`) |
| Reviews | **Gemini A+, Codex Logic A / Correctness A−** (gate suite) |
| Existing revision pipeline (timelock → policy → registry) | **Pre-existing** |
| Committed/replayable Tau proof artifact (recorded verifier transcript) | **Open** |
| `curr`/epoch binding to committed ledger state (the §5.2 precondition) | **Partially done** for the integration artifact path (`governance_surface_context_hash_v1`, `expected_committed_context_hash`, trajectory runner threading); deployed ledger-source wiring remains **Open** (WS5) |
| PID + frozen-Q proposer **reference impls** (deterministic, no floats) | **Done** (`gov_proposers.py`) — simulation only |
| **Layered (hierarchical) Q-tables** — regime layer → per-regime action table, one pin over the whole hierarchy, fail-closed at every layer | **Done** (`layered_q_propose`) — reference/simulation only |
| **Frozen energy model** — pinned integer `E(c)` argmin over the bounded band, explicit tracking-vs-churn trade-off | **Done** (`energy_propose`) — reference/simulation only |
| Reference **loop** + safety property (gate bounds a poisoned PI/Q-table/layered/energy proposer) + `curr`-binding | **Done** (`gov_loop.py`, `test_gov_loop.py`, `test_gov_proposers.py` — empirical) |
| **Multi-surface revision step** — all-or-nothing across every touched surface (fee/funding/whale scalars, router shares as a unit, MCR/CCR as a unit); gates import-bound (no forged-wrapper surface); consumes the policy-factory action shape (`{surface: delta}`) directly — every action in the frozen `q_policy.v1` sample is gate-admissible and the factory's negative controls all reject (differential fixture) | **Done** (`gov_loop.multi_surface_revision_step`) — reference; live `curr`/epoch binding still **Open** (WS5) |
| Q-table **hash-pinning** primitive (`table_hash` / `layered_table_hash` / `energy_model_hash`) | **Done** (reference); a live consensus-bound, hash-pinned decision runtime is **Open** |
| Frozen Q/EBRM artifact evaluator, factory, CLI, replay reports, selection-aware first-admissible ranking, context-hash binding, and multi-step trajectory runner/verifier | **Done** (`src/integration/autonomous_governance_q_policy.py`, `src/integration/autonomous_governance_trajectory.py`, `tools/autonomous_governance_policy_factory.py`, `tools/autonomous_governance_q_policy.py`, `docs/AUTONOMOUS_GOVERNANCE_Q_POLICY.md`) — offline/integration artifact path; deployed apply wiring still **Open** (WS5) |
| **Trajectory-tier Tau specs** — `gov_drift_budget_v1` / `gov_cooldown_v1` / `gov_charter_v1` / `gov_epoch_budget_v1` (compile + non-vacuity + teeth incl. wrap probes, via the same bf-layer harness) | **Done** (`validate_governance_specs.py` `PURE_SPECS`) |
| Trajectory-tier Python mirrors + Tau↔Python↔Rust differential parity (one shared boundary table, byte-pinned fixture) | **Done** (`gov_gate.py`, `test_gov_parity.py`) |
| **Epoch machine** — charter (dead-man standing approval) / veto / freeze / cooldown / drift budgets / aggregate budget, stable receipt codes + params-digest no-op proofs, import-bound gates, no self-amendment | **Done** (`gov_epoch.py`, `test_gov_epoch.py`) — reference; live `now_epoch`/state binding still **Open** (WS5) |
| **ESSO inductive verification** of the epoch machine's per-surface core (z3 + cvc5 agree, `Inductive(k=1)`, 10/10 queries, guard-presence tripwires) | **Done** (`src/kernels/dex/gov_epoch_machine_v1.yaml`) |
| **Lean trajectory composition** — per-window budget B over m windows ⇒ end-to-end displacement ≤ m·B; achievement witness at m=3, B=150 (the always-max walk attains m·B; the construction scales) | **Done** (`lean-mathlib/Proofs/GovTrajectoryBound.lean`, 0 sorry; verify from a dep-complete checkout: `cd lean-mathlib && lake env lean Proofs/GovTrajectoryBound.lean` — `external/mathlib4` is git-ignored and absent in bare worktrees) |
| **Observables/sensor layer** — staleness-guarded deterministic binning (stale/future ⇒ hold) | **Done** (`gov_observables.py`) — reference; real committed metrics are **Open** (WS5) |
| **Production** proposer (tuned/audited PID or trained+frozen Q-table on real signals) | **Open** |
| Live wiring: a deployed governance flow that *requires* this gate before applying any change | **Open** (WS5) |
| Client-side refuse-loop that rejects an unbounded/unproven revision | **Open** (WS5) |
| Rust port of the gate kernel — `rust-runtime/crates/zenodex-governance-gate`: all gates + trajectory bits + the canonical params digest (contract-equal to `gov_epoch.params_digest`), 3-way parity over the shared byte-pinned fixture, clippy-clean checked arithmetic, Kani 7/7 full-domain accept⇒invariant | **Done** (reference/shadow; authority stays `gov_gate.py`; promotion via the CBC matrix)
| Rust port of the EPOCH MACHINE — `epoch` module: Surface enum + fixed arrays make the hostile-object tier unrepresentable; digest-free core proved by Kani over the FULL symbolic state space (reject-is-no-op, pending kept-vs-cleared, accept⇒bookkeeping/band/charter invariants, precedence dominance, stop-authority field isolation — 15/15 harnesses); bound to `gov_epoch.py` by a 53-transition replay fixture generated from the Python machine itself (all 17 receipt codes, byte-pinned) | **Done** (reference/shadow; `gov_epoch.py` stays the authority machine) |

## 8. References

- Gate suite: `src/tau_specs/governance/` — `gov_action_bound_v1.tau`, `gov_fee_revision_v1.tau`,
  `gov_router_split_revision_v1.tau`, `gov_collateral_ratio_revision_v1.tau`,
  `gov_whale_defense_revision_v1.tau`, `gov_funding_rate_revision_v1.tau`,
  `gov_revision_master_v1.tau`, `gov_gate.py`, `gov_parity_cases.py`,
  `validate_governance_specs.py`, `README.md`
- Trajectory tier + epoch machine: `gov_drift_budget_v1.tau`, `gov_cooldown_v1.tau`,
  `gov_charter_v1.tau`, `gov_epoch_budget_v1.tau`, `gov_epoch.py`, `gov_observables.py`;
  tests `tests/tau_specs/governance/test_gov_epoch.py`, `test_gov_observables.py`;
  ESSO model `src/kernels/dex/gov_epoch_machine_v1.yaml` (verify-multi z3,cvc5 → VERIFIED)
- Gate tests: `tests/tau_specs/governance/test_gov_gate.py`, `tests/tau_specs/governance/test_gov_parity.py`
- Reference proposers + loop: `src/tau_specs/governance/gov_proposers.py` (deterministic PI, frozen
  Q-table, layered/hierarchical Q-tables, frozen energy model), `src/tau_specs/governance/gov_loop.py`
  (proposer→gate→apply/no-op); tests
  `tests/tau_specs/governance/test_gov_proposers.py`, `tests/tau_specs/governance/test_gov_loop.py`
- Frozen Q/EBRM artifact runtime: `docs/AUTONOMOUS_GOVERNANCE_Q_POLICY.md`,
  `src/integration/autonomous_governance_q_policy.py`,
  `tools/autonomous_governance_policy_factory.py`,
  `tools/autonomous_governance_q_policy.py`,
  `tools/autonomous_governance_q_table_optimize.jl`,
  `tests/integration/test_autonomous_governance_q_policy.py`,
  `tests/tools/test_autonomous_governance_q_table_optimizer.py`
- Existing pipeline: `docs/REVISION_PIPELINE.md`, `src/tau_specs/revision_policy_v1.tau`,
  `src/tau_specs/governance_timelock_v1.tau`, `src/tau_specs/parameter_registry_v1.tau`
- Oracle trust: `docs/ORACLE_TRUST_POSTURE.md` (WS4 doc — lives on branch
  `claude/prod-promotion-phase5-proof-receipt`, unmerged; not on this branch yet) and the
  modules it cites: `src/integration/zeno_oracle_authority.py`, `src/core/oracle.py`
- Merged source branch: `claude/governance-pointwise-revision` (gate suite; PR #363)
