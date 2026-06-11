# ZenoOracle Mechanism & Math Analysis

Status: analysis + checked Lean strengthenings + metamorphic runtime binding
(2026-06-11).

The oracle is the root dependency of every solvency claim in the system:
perp epoch safety, funded liquidation, zUSD MCR, and redemption all
condition on the aggregated price. This document maps what the oracle
actually does (verified in code), pins its robustness algebra in Lean, and
identifies the mechanism gaps in priority order.

Companion artifacts shipped with this analysis:

- `lean-mathlib/Proofs/OracleMedianRobustness.lean` — breakdown-point
  theorems for the median-3 aggregator and the defense-in-depth
  composition with the runtime clamp.
- `lean-mathlib/Proofs/EconomicSecurityEnvelope.lean` (extended) —
  coalition deterrence: `coalition_deterrence`,
  `median3_coalition_bond_floor`, `witness_unilateral_sizing_insufficient`.
- `tests/core/test_metamorphic_lean_identities.py` — binds the LIVE
  aggregator (`tools/zenodex_oracle_admitted_median3.py::_median3`) and the
  LIVE settle clamp (`src/core/perp_v2/math.py::_settle_price_python`) to
  the proven relations under hypothesis-generated inputs, including
  arbitrarily corrupt values.

---

## 1) Verified mechanism map

| Surface | What the code does | Where |
|---|---|---|
| Aggregation | median of exactly 3 equal-weighted admitted reports; duplicates rejected; `< 3` reports ⇒ NO price (fail-closed) | `tools/zenodex_oracle_admitted_median3.py:126-135, 318-320, 448-449` |
| Deviation gate | confidence = max |vᵢ − median|; reject aggregate when `ceil(confidence·10⁴/median) > max_deviation_bps` (default 200) | same file, `:497-498` |
| Reporter economics | register / bond / report / dispute / slash / withdraw exist as a **lifecycle trace verifier**; bonds and slashing are NOT kernel state | `tools/zenodex_oracle_reporter_lifecycle.py:82-339` |
| Freshness | `(now − last_update) ≤ max_staleness_epochs`; stale ⇒ zUSD risky ops blocked, perp settle guard fails | `src/core/zusd.py:50-56`, `src/core/perp_v2/math.py:145-160` |
| zUSD commit | two-step: `oracle_report` lowers `price_pending` (NON-INCREASING only), `oracle_commit` promotes pending→active, but is BLOCKED if the vault would be under MCR at pending | `src/core/zusd.py:528-559` |
| Perp path | index price consumed from oracle authorization receipt UNclamped; the `max_oracle_move_bps` clamp applies to clearing-vs-index at settlement | `src/integration/perp_engine.py:220,814`, `perp_v2/math.py:163-229` |
| Timing | plaintext signed reports, no commit-reveal; sequenced per reporter | `tools/zenodex_oracle_signed_report.py:210-221` |

Model-mapping note for the Lean epoch-safety lemmas: in the runtime, the
clamp is clearing-vs-index and PnL is `pos·(settle − index)` with margin
re-measured at the current index each epoch — i.e. `P := index`,
`P' := settle` in `PerpEpochSafety`. The hypotheses of the solvency lemmas
are therefore discharged by the runtime even when the index itself jumps
between epochs.

## 2) The robustness algebra (now machine-checked)

Write `k = 3`, honest values `h₁, h₂`, deviation cap `D` bps.

**Integrity breakdown point = 2.** One arbitrarily corrupt reporter cannot
move the median outside `[min(h₁,h₂), max(h₁,h₂)]` — proven for all three
corrupt positions (`median3_robust_corrupt_first/second/third`), and
re-checked against the live `_median3` under hypothesis with corrupt values
up to `10¹⁸`. Two corrupt reporters control the median completely
(`witness_two_corrupt_unbounded`).

**Availability breakdown point = 1.** This is the asymmetry the deviation
gate buys: a single admitted reporter posting any value with
`|v − median| > D·median/10⁴` trips the gate and the aggregate is REJECTED
— no price. One reporter can therefore veto every price update
indefinitely. Fail-closed is the right default, but the consequence chain
is the freeze family: no price → freshness decay → zUSD risky-ops freeze +
perp settle halt. The mechanism converts *manipulation* into *denial of
service*, and DoS is currently free for an admitted reporter because
slashing is doc-only (§3).

**Last-mover power (no commit-reveal) is bounded but real.** A reporter
who sees the other two reports before submitting can place the median
anywhere inside the honest interval, subject to the gate:

```
last-mover shift ≤ min( |h₁ − h₂| ,  D·median/10⁴ )
```

(first term: `median3_shift_bounded_by_honest_disagreement`; second: the
deviation gate). With honest reporters reading the same venues, `|h₁ − h₂|`
is small, so this is a second-order channel — commit-reveal is worth doing
but is NOT the binding weakness.

## 3) The binding weakness: the economics are not wired to the kernel

The economic security envelope (`ZENO_ORACLE_ECONOMIC_SECURITY_V1.md`)
specifies bonds (250e9), slash fraction (50%), deterrence margins (20%) —
and the lifecycle tool can *verify a trace* of bond/slash events. But no
kernel state collects bonds or executes slashes. Three consequences, in
order of severity:

1. **The deterrence laws have no enforcement substrate.** Every deterrence
   inequality (now in Lean) is about slash amounts that nothing can
   currently take.
2. **The availability veto (§2) is unpriced.** Gate-tripping garbage is
   objectively attributable — when two reports agree within `D` and the
   third is outside, the outlier is identified by the data itself — yet
   carries no penalty.
3. **Coalition sizing is absent.** Even the doc-level law is unilateral.
   The binding adversary at `k = 3` is the **2-coalition**, and the correct
   bond floor is (`median3_coalition_bond_floor`):

```
2 · (slash_fraction · Bond)  ≥  (1 + margin) · G_coalition
```

where `G_coalition` is the COALITION-extractable value, not a per-reporter
share. `witness_unilateral_sizing_insufficient` pins the failure mode: a
slash of 12 deters a unilateral gain of 10 at 20% margin, while the
2-coalition pooling a gain of 100 nets +76 under the same slash.

**Sizing `G_coalition` from the proven envelopes.** A 2-coalition that
controls the median (and hence the gate) can hold the price wrong for at
most `L_detect` epochs (staleness window / dispute latency). Per epoch the
proven damage bounds are: perp side ≤ `OI · m/10⁴` (settle clamp), zUSD
side ≤ `freeDebt · D/10⁴` (redemption at a gate-bounded wrong price,
assuming the fee floor of R6 is still zero). Hence the bond floor:

```
slash_fraction · Bond ≥ (1 + margin) · L_detect · (OI·m + freeDebt·D) / (2·10⁴)
```

Bond requirements must scale with open interest — a static 250e9 is only
correct for a static OI cap, and the inequality above is the checkable
form to enforce at parameter admission (same proof-carrying-parameter
pattern as FUNDED-LIQ).

## 4) Defense-in-depth: why one corrupted epoch cannot kill the system

Now machine-checked end-to-end (`corrupt_report_damage_bounded`,
`corrupt_report_cannot_insolve_in_one_epoch`, and the metamorphic clamp
test under arbitrary corrupt clearing inputs):

- even a FULLY corrupted aggregate moves the applied settle price at most
  `m` bps for the epoch — the clamp lemma holds for every raw input;
- a maintenance-safe account therefore survives ANY single corrupted
  update;
- with (FUNDED-LIQ) holding, the liquidation triggered by a corrupted
  update is still fully funded.

So oracle corruption is lethal only through **persistence** — repeated
epochs of bounded damage inside the clamp band. Persistence is governed by
exactly three controls: the staleness window (implemented), the dispute
lane (doc-only), and coalition bonds (doc-only). That is why §3 is the
priority: the arithmetic layer is already sound; the persistence layer has
no teeth.

## 5) zUSD oracle state machine findings (verified)

1. **Monotone-down ratchet with no recovery path.** `oracle_report`
   requires `p ≤ price_pending` (`zusd.py:534-535`) and commit promotes
   pending→active, so the committed collateral price can NEVER rise after
   bootstrap. Conservative for solvency, but: (a) mint capacity never
   recovers after a dip; (b) combined with the zero default redemption fee
   (mechanism doc R6), `price_active ≤ p_true` eventually holds with
   certainty, making redemption arbitrage *guaranteed* rather than
   conditional — the redeemer receives `z/p_active ≥ z/p_true` in true
   value, draining vault collateral whenever the true price has risen.
   Recommendation R-O3: add an upward path with asymmetric friction
   (up-commits delayed by ≥ the dispute window and bounded per epoch),
   keeping pessimism short-run without making it permanent.
2. **Commit-blocked-under-MCR forces liquidation-first ordering.**
   `oracle_commit` refuses while the vault would be under MCR at pending
   (`zusd.py:545-551`); risky ops are frozen while pending ≠ active;
   liquidation runs on the pending price. This is coherent — the bad price
   must be acted on (liquidation) before it becomes the active price — but
   it composes with the SP-empty liquidation refusal (`zusd.py:774-775`)
   into a **permanent module freeze**: bad pending + empty SP ⇒ commit
   blocked forever, mint/withdraw/redeem blocked forever. This strengthens
   the priority of R7 (SP cooldown + partial absorption).
3. **`auth_ok` is a caller-supplied flag** (`zusd.py:531-532`): the kernel
   trusts the boolean; authorization is an upstream obligation. Standard
   for this kernel style, but it belongs on the runtime-binding obligation
   list next to the rebalancer's anti-abuse flags.

## 6) Recommendations, priority-ordered

| # | Action | Effect | Cost |
|---|---|---|---|
| R-O1 | Implement bonds/slashing as kernel state; size by the **coalition** law of §3, scaled to OI (proof-carrying parameter) | deterrence laws become real; persistence channel priced | kernel feature + admission rule |
| R-O2 | Outlier attribution on gate trips: two reports within `D` of each other + third outside ⇒ emit price from the agreeing pair, slash the outlier | availability breakdown restored from 1 to 2; veto becomes self-slashing | aggregator rule + R-O1 |
| R-O3 | Asymmetric upward price path for zUSD (delayed, per-epoch-bounded up-commits) | removes the guaranteed-redemption-arb endgame and permanent mint-capacity loss | state-machine change |
| R-O4 | Redemption fee floor ≥ `D` + staleness drift budget (sharpens R6: under honest majority the price error is gate-bounded by `D`) | prices the residual oracle error into the redemption path | parameter default |
| R-O5 | Gate-trip and `liq_penalty_capped`-binding telemetry as monitored disaster axes | the two cheapest early-warning signals for oracle attack and unfunded liquidation | effects + monitor |
| R-O6 | Commit-reveal for reports | removes last-mover channel (already bounded by §2) | protocol change, lower priority |

## 7) What this does not claim

The Lean results cover aggregation algebra, clamp composition, and
deterrence arithmetic. They do not prove reporter honesty, network
delivery, dispute adjudication correctness, or that the runtime wires the
median output into the consumers (the metamorphic tests bind the
*functions*, not the end-to-end pipeline). The lifecycle verifier checks
traces; it does not custody bonds. Every claim above marked "doc-only"
remains doc-only until R-O1 lands.
