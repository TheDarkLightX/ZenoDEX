# ZenoDEX Governance — Pointwise-Revision Spec Suite (WS5)

Machine-verified governance gates for ZenoDEX. Stakers (or an autonomous proposer)
update DEX parameters; these Tau specs are the **immutable, fail-closed envelope** that
decides whether a proposed update is admissible. The thesis is the project's north star
applied to governance: **trust the math, not the proposer.**

## The proposer / gate split

A governance update has two roles, deliberately separated:

| Role | Who | What it is |
|---|---|---|
| **Proposer** | staker vote, **PID controller**, or a frozen **Q-learning lookup table** | computes the *next* parameter value |
| **Gate** | these Tau specs (+ `gov_gate.py` runtime) | decides whether *next* is **admissible** |

The gate is **proposer-agnostic**. Whatever computes `next` — a human vote, a PID loop
on the oracle feed, or a hash-pinned Q-table — the *same* verified gate admits it only if
it is governance-approved, past the timelock, within `[min, max]`, and within one bounded
`step` of the current value. So a mis-trained, poisoned, or oracle-manipulated proposer
**can never escape the bounded envelope**: the worst it can do is move a parameter by
`step` per revision inside `[min, max]`. **The bound is the safety, not trust in the
proposer.** (This is why an autonomous PID/Q-table proposer is safe to run at all: it
inherits the oracle's trust level, and the gate caps the blast radius of any oracle
manipulation to the bounded band.)

`gov_action_bound_v1.tau` is that universal gate, with bounds passed as inputs.

## What is governable (and what is not)

Only **parameters** — rates, caps, floors, thresholds, weights — are revisable.
**Immutable invariants** (value conservation, fail-closed rejection, the AMM curve,
settlement and proof-binding logic) are *not* parameters and live outside this surface;
they can change only by a spec-version bump with new proofs, never by a pointwise
revision. That boundary is what makes "stakers update behavior" safe.

## The specs

| Spec | Surface | Shape | Immutable guardrails |
|---|---|---|---|
| `gov_action_bound_v1.tau` | universal gate (any proposer) | factored bounds + step | bounds are inputs |
| `gov_fee_revision_v1.tau` | swap fee (bps) | factored bounds + step | `next ≤ 1000` (10% cap); `\|Δ\| ≤ 50` /rev |
| `gov_router_split_revision_v1.tau` | fee-router split (sum-budget) | sum-budget | each ≤ 10000; **sum = 10000** (no leak/mint) |
| _(router per-share drift)_ | fee-router split (anti-whiplash) | per-share step = `action_bound` | per-share `\|Δ\| ≤ 500` (5pp) — see below |
| `gov_collateral_ratio_revision_v1.tau` | zUSD MCR / CCR | ordered + bounds + step | `mcr ≥ 10000`, `ccr ≤ 30000`, **`mcr ≤ ccr`**, `\|Δ\| ≤ 1000` |
| `gov_whale_defense_revision_v1.tau` | `redeem.staker_bps` | factored ceiling + step | `next ≤ 7000` (whale-defense ceiling); `\|Δ\| ≤ 500` |
| `gov_funding_rate_revision_v1.tau` | perps funding-rate cap | factored bounds + step | cap `≤ 200` bps (2%/epoch); `\|Δ\| ≤ 25` |
| `gov_revision_master_v1.tau` | composite | **factored** AND of the 4 economic-core surfaces | union of fee/router/collateral/whale + shared `MIN_DELAY = 24` |

Guardrail constants are encoded as immutable bv[16] literals (`{ #xHHHH }:bv[16]`); only
`curr`/`next` (and, for `action_bound`, the bounds) are inputs. `MIN_DELAY = 24` is expressed
in the **runtime's own time unit** (epochs / blocks); the spec is unit-agnostic — `proposal_ts`
and `current_ts` must be supplied in the same unit. The fee-router is **two** factored concerns:
the sum-budget (`gov_router_split`) and the anti-whiplash **per-share drift**, where each share's
drift is just the universal `gov_action_bound` gate (lo=0, hi=10000, step=500) applied to that
share. A router revision is admissible iff the sum-budget **and** every per-share `action_bound`
accept (composed by `router_revision_ok`, and by the master's `o3` ∧ `o6` bits). Factoring is
forced *and* fortuitous: sum + four step ladders in one Tau formula normalizes in ~180s (too
heavy/flaky to gate on), but the sum-budget spec, each per-share `action_bound`, and the combined
master `o6` bit are each tractable — so the step is verified two independent ways (per-share via
the universal gate, combined via `o6`) without a heavy standalone spec. The master composes the
four economic-core surfaces; perps funding has its own `gov_funding_rate` gate, verified
standalone like `action_bound`.

### Why these shapes are cheap (no BDD blowup)

The empirical envelope (`experiments/pointwise_revision_envelope/`) showed that the cost
driver is **coupling** (BDD state-space explosion on monolithic formulas), not parameter
count or bit width: a *monolithic* formulation blows up, but a **factored** one (one
independent output bit per knob, ANDed) stays ~linear. Concretely on the current Tau build:
the per-surface `sat`/`unsat` bf checks run from well under a second up to a few seconds; the
full-temporal *normalize* of the most-coupled single spec (collateral, two nested step
ladders) takes ~tens of seconds (~49 s); and the all-surfaces *monolith* (the master as one
formula) does **not** terminate — which is exactly why the master is verified factored, not
as a single formula. The whale-defense ceiling, the router sum, and `mcr ≤ ccr` all factor
cleanly.

## Verification

Run the harness (drives the built Tau binary):

```bash
python3 src/tau_specs/governance/validate_governance_specs.py            # table
python3 src/tau_specs/governance/validate_governance_specs.py --json     # machine summary
```

For each spec it runs three classes of check, all at Tau's **Boolean-function layer**
(`sat`/`unsat`/`valid`), never the temporal `always` layer — a temporal `always` is
vacuously satisfied by the empty trace, so `sat`/`unsat` on it prove nothing. The bf
relation is obtained from the temporal spec by a deterministic transform (drop comment
lines, the leading `always`, every `[t]`, the trailing `.`), so the verified Boolean
structure is exactly the runtime spec's:

1. **Compile** — the temporal spec normalizes with 0 errors.
2. **Non-vacuity** (`sat`) — the gate admits a concrete, fully-valid revision
   (`output = 1`). Proves it is not vacuously always-reject.
3. **Teeth** (`unsat`) — for each guardrail, it is *unsatisfiable* to have `output = 1`
   while that guardrail is violated and execution is requested. Proves it is not
   vacuously always-accept, and that each guardrail genuinely rejects.

(`unsat → %N: T` means *provably unsatisfiable* = the teeth hold.)

### Hybrid model: Tau validates, Python computes

`gov_gate.py` is the runtime ("computes") side, encoding each spec's Boolean gate. The two
implementations are **not** trusted relative to each other:
`tests/tau_specs/governance/test_gov_parity.py` drives a shared boundary-scenario table
(`gov_parity_cases.py`) through BOTH the Tau spec (ground `sat`) and `gov_gate.py`, and
asserts both agree with the expected verdict on every case — a dual-checker; a disagreement
fails the test. `test_gov_gate.py` additionally reproduces the teeth in pytest (admit valid;
reject each guardrail violation; honor the `exec_req = 0` escape; hard-reject out-of-domain
inputs). The Python shell is **stricter** than the bv[16] core: it hard-rejects any input
outside `[0, 0xFFFF]` rather than silently wrapping it, so the composed decision is fail-closed.

### How the master is verified (factored, not monolithic)

`sat`/`unsat` on the full 4-surface master bf does not terminate on the current Tau build
(the coupling/envelope limit). The master is therefore verified **factored**: each `oN`
biconditional is extracted and verified in isolation (one concern each, tractable), where
**every guardrail of every bit** gets its own teeth (`o3`: all four share caps + the exact sum;
`o6`: each per-share drift; `o4`: MCR floor, CCR ceiling, ordering, and both steps; etc.) plus
non-vacuity; and the composition bit is verified separately — `o1 = 1` requires every
`oN = 1` (`o2,o3,o6,o4,o5`) under the shared gate (`requires_all_bits`, `requires_approval`, `requires_timelock`)
and admits when all hold (`admits_all_good`). The master's correctness is then the *logical*
conjunction of these machine-checked facts (each guardrail bit bites + `o1` is exactly their
gated AND), not a single monolithic solver result — an honest distinction, stated so a
reviewer can audit the chaining.

### How to add a new governable surface

To keep a spec from being written but silently omitted from the gate or the proof, touch all
of these (the verification harness fails closed if any step is skipped):

1. **`gov_<surface>_revision_v1.tau`** — the new gate, following the factored pattern
   (immutable `{ #xHHHH }:bv[16]` guardrails; only `curr`/`next` as inputs; the wrap-safe
   subtraction-guard timelock).
2. **`gov_gate.py`** — the mirror gate function (domain-validate every field first, then the
   `exec_req` escape, then the guardrails) and its constants.
3. **`validate_governance_specs.py`** — add a `PER_SURFACE` entry (non-vacuity + a teeth case
   for **every** guardrail).
4. **`gov_parity_cases.py`** — add the `SURFACE_TAU` mapping + boundary `CASES` (≥1 accept,
   ≥1 reject per guardrail); register the gate in `test_gov_parity.py`'s `PY_GATE`.
5. **`test_gov_gate.py`** — Python teeth tests.
6. *(If composing it into the master)* add an `oN` bit to `gov_revision_master_v1.tau`, a conjunct
   to `o1`, the `MasterRevision` fields, and a `MASTER_BITS` entry.

## A bug this process caught

The naive timelock `current_ts ≥ proposal_ts + MIN_DELAY` is **bypassable by modular
wrap**: with `proposal_ts` near `2^16`, `proposal_ts + MIN_DELAY` wraps below `current_ts`
and the delay is skipped. The harness probe demonstrated the bypass (an accept it should
have rejected). All specs now use the wrap-safe **subtraction-guard** form
`current_ts ≥ proposal_ts AND current_ts − proposal_ts ≥ MIN_DELAY` (bv[16] is unsigned,
verified). `gov_gate.py` mirrors it; `test_timelock_wrap_bypass_rejected` pins it.

## Honest boundaries

- These are **gates, not proposers.** They do not choose `next`; they bound it. Pairing
  with an autonomous proposer (PID / Q-table) is a separate, opt-in design — and that
  proposer inherits the **oracle's trust level** (currently L2, attested — see
  `docs/ORACLE_TRUST_POSTURE.md`). The gate caps, but does not remove, that dependence.
- **The step-limit assumes `curr` is the true committed value.** `curr` is a *gate input*,
  not read from state by the spec. If the calling runtime lets a proposer supply a stale or
  self-serving `curr`, the proposer can jump freely within a *fake* step. The runtime MUST
  bind `curr` to the committed on-chain parameter before calling the gate — exactly the WS2
  non-trust clause (no proposer-asserted field is an accept input). The spec bounds the
  *delta*; the runtime owns the *anchor*.
- bv[16] arithmetic is **modular**; every guardrail bounds its value well below `2^16`,
  and the Python shell hard-rejects out-of-domain inputs, so wrap cannot admit a bogus
  revision.
- This is the **WS5** governance-pinning building block (the second trust assumption).
  Wiring a deployed governance flow to *require* this gate before applying any parameter
  change — and a client-side refuse-loop that rejects an unbounded revision — is the
  remaining integration step.
```
