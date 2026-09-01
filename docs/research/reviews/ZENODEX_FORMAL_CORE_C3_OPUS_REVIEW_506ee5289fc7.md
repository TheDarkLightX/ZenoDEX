# Opus review receipt: candidate C3 at P6 = 506ee5289fc71877710439c77f80188cd514497b

Reviewer: Opus 5 (independent reviewer, read-only, detached worktree `/tmp/zenodex-formal-core-review-p-506ee5289`).
Date: 2026-09-01. Subject: P6 = 506ee5289fc71877710439c77f80188cd514497b (tree be188f65b65ca320b4fc472c5c89d9e702af7e14), S6 = dced526513a6a6e75d1f861c03f1a36cc2f6d8b2, parent 9056dac69044772aab9316637a68ec94265fe885.
Verdict: Grade A- (accept with two P2 repairs; no P0/P1). Disposition: P2-1 (the notes sentence about accepted transitions implying the four bindings) and P2-2 (no negative coverage of ESSO_ACTIONS_DRIFT) are repaired in candidate C1''' (source commit fee3b08a1). The grade is advisory and grants no authority.

Verbatim report follows.

---

# Opus 5 independent review — Candidate C3 (O-008 formal cycle)

- **Subject worktree**: `/tmp/zenodex-formal-core-review-p-506ee5289` (detached, read-only review)
- **P6 (packet commit)**: `506ee5289fc71877710439c77f80188cd514497b`, tree `be188f65b65ca320b4fc472c5c89d9e702af7e14`
- **S6 (source commit)**: `dced526513a6a6e75d1f861c03f1a36cc2f6d8b2`, tree `70f7adb241d2b953654dfd884c675d104b459c06`
- **S6 parent (C1'' packet)**: `9056dac69044772aab9316637a68ec94265fe885`
- **Reviewer**: Opus 5, advisory only. This review grants no authority.
- **Date**: 2026-09-01

---

## 1. Grade: **A-**

C3 does what a formal-model candidate should do and very little else. The five safety
invariants and both claimant actions (`open_claim`, `drain_claim`) are **byte-identical**
to their C1'' forms — I verified this structurally, not by trusting diff hunk boundaries —
so no invariant was weakened and no claim action was touched. The additions are a genuinely
inert reserve column, an operational `deposit_reserve` witness, a real named mutant, and a
completed observable surface (all 21 state vars are now observable; nothing is hidden). Every
mechanical value reproduced exactly: `ir_hash sha256:08fce65c…`, fingerprint `256b0dcb…`
identical across both determinism trials, four queries `unsat` under both Z3 and CVC5, three
hand-recomputed pins matching, all 22 v7 hygiene pins matching S6 bytes, and all 54 `killed_by`
node ids resolving to real collected tests. I independently reproduced the
`reserve_masking_open_claim` mutant and its attribution run, and the counterexample is
precisely the claimed disaster: `custody_d0` stays at 7 while `allocation_bob_d0` grows to 8
and `reserve_d0` absorbs the atom — a reserve standing in for missing custody, caught by
`inv_exact_custody_partition_d0` alone. I also falsified the most likely way the new ir-hash
test could have been vacuous: a YAML round-trip with no modification preserves the `ir_hash`,
so the test's sensitivity is real. Claim discipline holds — `claim_ceiling`, `completion_scope`
and `nonclaims` are unchanged, and "Exact reserve reconciliation remains open" survives and
stays lexically pinned. Two things keep this off a full A. First, the pinned model notes now
carry a sentence that is false when read model-globally ("The journal makes every accepted
transition imply all four bindings") — `deposit_reserve` emits `accepted: true` from GENESIS
with all four binding flags false, which I reproduced; claim precision in a pinned artifact is
exactly what this campaign exists to protect. Second, `ESSO_ACTIONS_DRIFT` — the admission-core
guard that C3 itself widened from two actions to three — has zero negative-test coverage
anywhere in the repository; I proved it still fires, but nothing in the repo pins that.

**No P0 and no P1 findings.** Nothing here is unsound, and nothing blocks on correctness.

---

## 2. Findings

### P0 — none

No finding at this severity. No unsoundness, no invariant weakening, no claim inflation, no
chain defect.

### P1 — none

No finding at this severity. Both P2 items below are real and should be repaired, but neither
makes a verified statement false, and neither affects any invariant, query, or authority claim.

---

### P2-1 — Pinned model notes assert a property C3 falsified

**File**: `src/kernels/dex/global_claimant_custody_certificate_v1.yaml:32`

**Exact statement**: the notes retain

> `The journal makes every accepted transition imply all four bindings.`

Before C3 this was true model-globally: the only actions were `open_claim` and `drain_claim`,
both set `g_decision` to `OPENED`/`DRAINED`, and `inv_accept_requires_exact_bound_evidence`
forces all four `g_*` binding flags true in any such post-state — so a step with a false
binding param is rejected. C3 adds a third action that emits `accepted: true` while leaving
`g_decision` at `GENESIS` and all four flags `false`. The sentence sits inside a paragraph
opening "open_claim and drain_claim model only an accepted exact relation update", so a
charitable scoped reading survives; read as a statement about the model, it is now false.
`observables.effects` declares `accepted` as part of the observation surface, so an auditor
has good reason to read it model-globally.

**Reproducing command** (from the worktree):

```bash
PYTHONPATH=/home/trevormoc/Downloads/ESSO /usr/bin/python3 - <<'PY'
import yaml
from ESSO.ir.schema import CandidateIR
from ESSO.kernel.interpreter import step, Command, eval_expr
ir = CandidateIR.from_json_dict(yaml.safe_load(
    open('src/kernels/dex/global_claimant_custody_certificate_v1.yaml'))).canonicalized()
s0 = {}
for a in ir.init:
    s0[a.var] = eval_expr(a.expr, state={}, params={}, ir=ir, expected=None)
r = step(s0, Command(tag="deposit_reserve", args={"domain":"D0","amount":1}), ir)
print("effects:", r.effects)
print("pre flags:", {k:s0[k] for k in s0 if k.startswith('g_')})
PY
```

**Observed**:

```
effects: {'accepted': True, 'decision': 'GENESIS'}
pre flags: {'g_decision': 'GENESIS', 'g_global_root_bound': False,
            'g_lane_projection_root_bound': False, 'g_header_bound': False,
            'g_terminal_projection_exact': False}
```

**Required repair**: scope the sentence to the claim actions, e.g. replace with
`The journal makes every accepted claim transition (open_claim, drain_claim) imply all four
bindings; deposit_reserve is accepted without bindings because it establishes no claim.`
Changing the notes changes the model bytes, so this requires a re-cut of S/P with new
`RECORDED_SOURCE_SHA256` / `RECORDED_IR_HASH` / `RECORDED_FINGERPRINT`, a refreshed v8 hygiene
packet, and a fresh two-solver replay. Consider adding the new phrasing to the lexical surface
test's pinned phrase list so the scoping cannot silently regress.

---

### P2-2 — `ESSO_ACTIONS_DRIFT`, the guard C3 widened, has no negative test

**File**: `tools/o008_formal_cycle_admission_v1.py:1781` (emission site);
`tools/o008_formal_cycle_admission_v1.py:387` (`ESSO_ACTIONS_V1`, changed by C3)

**Exact statement**: C3 changes the action allowlist from
`("open_claim", "drain_claim")` to `("open_claim", "drain_claim", "deposit_reserve")`.
`ESSO_ACTIONS_DRIFT` is the only guard enforcing that allowlist against the model, and it
appears **nowhere in the repository except its own emission site**. By contrast
`ESSO_MODEL_ID_DRIFT`, `ESSO_INVARIANTS_DRIFT`, `ESSO_GATE_MUTANTS_DRIFT`,
`ESSO_IR_HASH_DRIFT` and `ESSO_CODE_COMMIT_DRIFT` all have assertions in
`tests/test_check_o008_formal_cycle_v1.py`. `ESSO_GATE_SOURCE_PIN_DRIFT` and
`ESSO_GATE_INVARIANTS_DRIFT` are likewise untested, but C3 did not widen those.

**Reproducing command**:

```bash
grep -rn "ESSO_ACTIONS_DRIFT" --include=*.py --include=*.json --include=*.md . | grep -v '\.git/'
# -> tools/o008_formal_cycle_admission_v1.py:1781 only
```

I confirmed the guard is live, not dead code, with an independent probe
(`/tmp/opus-c3-work/probe_actions_drift.py`): renaming `deposit_reserve` to
`deposit_reserve_x` in the model blob yields `ESSO_ACTIONS_DRIFT`, and deleting the action
from the model also yields `ESSO_ACTIONS_DRIFT`.

**Required repair**: add a parametrized case to `tests/test_check_o008_formal_cycle_v1.py`
alongside the existing `ESSO_INVARIANTS_DRIFT` case, asserting
`_project_code(_edit(snapshot, core.ESSO_MODEL_PATH_V1, '- id: "deposit_reserve"',
'- id: "deposit_reserve_x"')) == "ESSO_ACTIONS_DRIFT"`. This is a test-only change; it does
not require re-cutting the model.

---

### P3-1 — `deposit_reserve` effects are indistinguishable from `open_claim` effects

**File**: `src/kernels/dex/global_claimant_custody_certificate_v1.yaml:607-608`
(`accepted: { bool: true }`, `decision: { var: "g_decision" }`)

From an `OPENED` state, `deposit_reserve` emits `{'accepted': True, 'decision': 'OPENED'}` —
byte-identical to what `open_claim` emits. The declared effect surface therefore cannot
distinguish a reserve deposit from a claim opening. The **state** observation does distinguish
them (`reserve_d1` changes), and all 21 state vars are observable, so the combined observation
surface is adequate; only an effect-trace-only consumer is fooled.

**Reproducing command**: the script in §3, run E.

**Required repair**: none required — the design choice is a direct consequence of keeping V1
wire names byte-stable (a distinct `Decision` symbol would change the enum ABI), and the state
surface disambiguates. Worth one sentence in the notes if the effect stream is ever consumed
standalone.

---

### P3-2 — Mutant harness accepts a non-unique needle

**File**: `tests/formal/test_esso_global_claimant_custody_certificate_v1.py:488`

`assert source.count(needle) >= 1` followed by `source.replace(needle, replacement, 1)`. If a
future edit introduces a second occurrence, the mutant silently targets the first and the test
still passes while testing something else. For the `reserve_masking_open_claim` needle I
verified `count == 1`, at line 297, inside `open_claim`.

**Required repair**: tighten to `== 1`. Test-only change; low risk.

---

### P3-3 — The ir-hash sensitivity test omits its own control

**File**: `tests/formal/test_esso_global_claimant_custody_certificate_v1.py:264-275`

`test_ir_hash_binds_the_observable_surface` writes a `yaml.safe_dump` round-trip with one
observable removed and asserts the resulting `ir_hash != RECORDED_IR_HASH`. It would pass
vacuously if the round-trip alone perturbed the hash. It does not — I checked directly: the
unmodified round-trip is byte-different from the original file yet yields the identical
`sha256:08fce65c…`, while the observable-dropped variant yields `sha256:29dbe725…`. The test
is sound, but relies on an unstated fact.

**Required repair**: none required. Optionally assert the control in the same test
(round-trip unmodified `== RECORDED_IR_HASH`) so non-vacuity is self-evident.

---

### P3-4 — Inertness check does not cover `g_*` reads in the `deposit_reserve` guard

**File**: `tests/formal/test_esso_global_claimant_custody_certificate_v1.py:255-257`

The `deposit_reserve` branch asserts the update set is exactly `{reserve_d0, reserve_d1}` and
that guard+updates text contains no `custody_`, `allocation_`, `liability_`, `open_`. It does
not exclude `g_decision` or the four `g_*_bound` flags. I probed seven escape hatches against
a replay of the test's assertion logic; it caught six, and missed only
"`deposit_reserve` guard reads `g_global_root_bound`". This is not a soundness hole — the
update set assertion still forbids writing anything but reserves, so invariants are untouched;
it would only couple reserve movement to evidence bindings.

**Required repair**: none required. Optionally extend the forbidden-substring check to `g_`.

---

### P3-5 — The new reject-code precedence is untested

**File**: `tools/o008_formal_cycle_admission_v1.py:2206-2207`

C3 hoists `source_pins = _project_source_pins(snapshot)` above
`esso_evidence = _project_esso(snapshot)`. This is a real behavioral change, confirmed
empirically against both cores: with a non-ESSO pinned path removed *and* the ESSO action set
drifted, the pre-C3 core reported `ESSO_ACTIONS_DRIFT` and the C3 core reports
`SOURCE_PIN_MISSING_IN_SUBJECT`.

**This is not a regression.** Both outcomes are rejects, so fail-closed behavior is preserved;
the new order reports a missing file before a content-level finding derived from the same
snapshot, which is strictly more useful. The ESSO model and gate are themselves source pins
(indices 14 and 15 of 28), so a missing ESSO model reports the same code under both orders.
Nothing pins the new order, so a future refactor could flip it back silently.

**Required repair**: none required for correctness. Optionally add an ordering test.

---

### P3-6 — Packet markdown omits actions and queries

**File**: `docs/research/ZENODEX_O008_FORMAL_CYCLE_V1.md:130-136`

The rendered "ESSO evidence" section lists model, `ir_hash`, fingerprint, invariants and named
mutants — but not `actions` or `queries`, both of which the JSON carries. A reader of the
markdown alone learns that a `reserve_masking_open_claim` mutant exists but never learns the
model has a third action. This is pre-existing template behavior, not introduced by C3, but C3
is the change that makes the omission material.

**Required repair**: none required. Optionally add actions/queries rows to the renderer.

---

### P3-7 — "invariant under reserve movements" over-generalizes the modeled transition

**File**: `src/kernels/dex/global_claimant_custody_certificate_v1.yaml:20-23`

The model has `deposit_reserve` only — no withdrawal, no reserve→custody transfer; reserves
are monotone non-decreasing and capped at 8. The claim is nevertheless *true*, because the
justification in the same sentence ("inert named atoms that no invariant reads") carries the
full generality, and Lean states exactly that as `Iff.rfl`. The operational witness covers
deposits only.

**Required repair**: none required. If P2-1 is repaired, "reserve deposits" would read more
precisely than "reserve movements".

---

### P3-8 — Naming hazard between the Lean and ESSO deposit operations

**Files**: `lean-mathlib/Proofs/GlobalClaimantCustodyRelationV1.lean:273` (`deposit`);
`src/kernels/dex/global_claimant_custody_certificate_v1.yaml:577` (`deposit_reserve`)

Lean's `deposit` is a **claimant** deposit: it grows custody, liability and the open terminal,
and copies the reserve column unchanged (`reserves := state.reserves`). ESSO's
`deposit_reserve` is a **reserve** deposit: it grows reserves and touches nothing else. They
are near mirror images with confusingly similar names, and both surface in the same packet
(`deposit_preserves_reserves` next to `inductive_deposit_reserve`).

**Required repair**: none required in this candidate — the Lean file is pinned unchanged and
renaming it is out of scope. Worth noting for any future Lean revision.

---

## 3. Verification record

Environment: `PY="/home/trevormoc/Downloads/Autonomous Tau DEX/.venv/bin/python"`,
ESSO via `PYTHONPATH=/home/trevormoc/Downloads/ESSO ZENO_ESSO_PYTHON=/usr/bin/python3`.
All commands run from `/tmp/zenodex-formal-core-review-p-506ee5289`. Cargo skipped (C3 touches
no Rust). No file inside the repository was created, modified, staged or committed; scratch
work lives in `/tmp/opus-c3-work/`; nothing was written under `/dev/shm`.

### Mandated commands

| # | Command | Exit | Key output |
|---|---------|------|------------|
| 1 | `git status --porcelain \| grep -v '^??'` | 1 (no match) | empty — no tracked modifications |
| 2 | `git diff-tree --no-commit-id --name-status -r HEAD^ HEAD` | 0 | exactly `M docs/research/ZENODEX_O008_FORMAL_CYCLE_V1.json`, `M …_V1.md` |
| 3 | `git diff --stat HEAD^^ HEAD^` | 0 | 6 files, 843 insertions, 22 deletions |
| 4 | `"$PY" tools/check_o008_formal_cycle_v1.py --root "$PWD"` | 0 | `"ok":true,"packet_admitted":true,"subject_commit":"dced5265…","head_commit":"506ee5289…","errors":[]`, `proof_replay:{"status":"NOT_RUN"}` |
| 5 | `… -m ESSO validate <model>` | 0 | `"ir_hash": "sha256:08fce65c258f145667cdf0df33e1c8464d6ca24f572fd39e4c21bf25778f9158", "ok": true` |
| 6 | `… -m ESSO verify-multi <model> --solvers z3,cvc5 --determinism-trials 2 --timeout-ms 10000` | 0 | `"verdict": "VERIFIED"`, `total_queries: 4`, `passed_queries: 4`, `failed_queries: 0`, `inconclusive_queries: 0`, `solvers_agreed: true`, fingerprints `["256b0dcb…","256b0dcb…"]`, `esso_code_hash 7f80c6216be85c827e8d1cc2fa08ee3107a74588`, badge `Inductive(k=1)` |
| 7 | `… pytest -q tests/formal/test_esso_*.py tests/formal/test_lean_*.py` | 0 | `26 passed in 33.97s` (20 ESSO + 6 Lean) |
| 8 | `"$PY" -m pytest -q tests/test_check_o008_formal_cycle_v1.py` | 0 | `244 passed in 82.10s` |
| 9 | `"$PY" tools/check_test_hygiene_v1.py --base-ref fd409ba6… --json` | 0 | `selected_evidence_ids` includes `THV1-20260901-o008-formal-cycle-admission-v7` |
| 10 | `"$PY" -m ruff check tools/o008_formal_cycle_admission_v1.py tests/formal/test_esso_*.py` | 0 | `All checks passed!` |

### Hand-recomputed pins

| Path | `git cat-file blob HEAD^:<path> \| sha256sum` | Packet `source_pins` | Match |
|---|---|---|---|
| `src/kernels/dex/global_claimant_custody_certificate_v1.yaml` | `e3c841e25db8051c1fe1903cc441db5b2f378f87d997d5d31c528dba3ced39f9` | same | YES |
| `tests/formal/test_esso_global_claimant_custody_certificate_v1.py` | `a8cac9d5cf356d4098fc22f3e73a0cbf9591a006cd9408ddbf911f9a5f2d45e5` | same | YES |
| `tests/formal/test_lean_global_claimant_custody_relation_v1.py` (third, extra) | `4a18288432029b8a057aade8308650d96651050bb1a942b8f9d8d2281a344388` | same | YES |

Both mandated pins also equal the worktree file bytes and the recorded test constants
(`RECORDED_SOURCE_SHA256 = e3c841e2…`).

### Independent adversarial runs

| Probe | Command / script | Result |
|---|---|---|
| Invariants and claimant actions unchanged | canonical-JSON compare of `HEAD^^` vs `HEAD^` model | 5/5 invariants identical; `open_claim` identical; `drain_claim` identical; `types` identical |
| No invariant reads reserves | dump of all 5 invariant expressions | confirmed — `reserve_` absent from every invariant |
| Mutant reproduction | `verify-multi /tmp/opus-c3-work/mutant_reserve_masking.yaml` | exit 1, `verdict FAILED`, `failed_queries 1`, only `inductive_open_claim` sat, both solvers sat with models |
| Mutant attribution | `verify-multi /tmp/opus-c3-work/mutant_attrib.yaml` (only `inv_exact_custody_partition_d0` retained) | exit 1, `failed_queries 1`, `inductive_open_claim` sat — attribution confirmed |
| Counterexample shape | z3 model from the attribution run | pre `custody_d0=7 = 0+7`; `open_claim(BOB,D0,1)` → `custody_d0_post=7`, `allocation_bob_d0_post=8`, `reserve_d0_post=1`; partition broken exactly as claimed |
| Mutant needle uniqueness | `src.count(needle)` | `1`, byte offset 12419, line 297, enclosing action `open_claim` |
| ir-hash non-vacuity (control) | `validate` of unmodified `yaml.safe_dump` round-trip | bytes differ from original, `ir_hash` **identical** `sha256:08fce65c…` |
| ir-hash sensitivity (treatment) | `validate` with `allocation_alice_d0` dropped from observables | `sha256:29dbe725dec4907befce762421299d0037c48f9d7c02c1328f26958a9abf2db0` — differs |
| Effect evaluation order | `ESSO/kernel/interpreter.py:153` | `_eval_effects(act, post, …)` — post-state; `deposit_reserve` never updates `g_decision`, so pre == post |
| Frame / inertness | 148 accepted `deposit_reserve` steps over a spread of invariant-satisfying pre-states | **0** frame violations (only `reserve_*` ever changed), **0** effect surprises; 144 `GuardFalse` rejections (the cap at 8) |
| Non-vacuity of `inductive_deposit_reserve` | same run | 148 concrete accepted steps — the query is not vacuously unsat |
| Effect ambiguity (P3-1) | step `open_claim` then `deposit_reserve` | both emit `{'accepted': True, 'decision': 'OPENED'}` — identical |
| Escape-hatch test strength | replay of the test's assertion logic against 7 doctored documents | 6/7 caught (reserve in invariants, reserve in `open_claim` guard, reserve in `open_claim` updates, `deposit_reserve` writing custody, allocations hidden, reserves hidden); missed only `g_*` read in the `deposit_reserve` guard |
| `ESSO_ACTIONS_DRIFT` reachable | `/tmp/opus-c3-work/probe_actions_drift.py` | rename → `ESSO_ACTIONS_DRIFT`; delete action → `ESSO_ACTIONS_DRIFT`; baseline → admitted |
| Precedence, C3 core | same probe, drop non-ESSO pin + drift ESSO actions | `SOURCE_PIN_MISSING_IN_SUBJECT` |
| Precedence, pre-C3 core | `/tmp/opus-c3-work/probe_old.py` against the `HEAD^^` tree | `ESSO_ACTIONS_DRIFT` — change confirmed, both fail closed |
| Observable completeness | model state_vars vs observables | 21 state vars, 21 observable, **nothing hidden**; no `g_pre_*`, no `unclassified_*`; all emitted effects declared |
| v7 hygiene pins | all 22 `source_pins` vs `git cat-file blob HEAD^:<path>` | 22 checked, **0 mismatches** |
| v7 `killed_by` liveness | 54 ids vs `pytest --collect-only` (264 collected) | 54 ids, **0 dangling** |
| v7 new-surface coverage | mutations mentioning reserve/deposit | 2 — `reserve_masking_open_claim` mutant and the `deposit_reserve` inertness check, both with live `killed_by` |
| Executing checker bytes == S6 | sha256 of 3 admission tools vs S6 blobs | `check_o008…` `3b148d47…`, `o008…admission…` `d5fa4e0b…`, `o008…shell…` `4f5360d2…` — all MATCH |
| Chain shape | `git rev-list --parents -n1` | P6 has exactly one parent S6; S6 has exactly one parent `9056dac69…` |
| Subject tree | `git rev-parse HEAD^^{tree}` vs packet | both `70f7adb241d2b953654dfd884c675d104b459c06` |
| Packet claim drift | structural diff of packet JSON P6 vs its parent | `claim_ceiling`, `completion_scope`, `nonclaims` **unchanged**; only ESSO evidence values, hygiene selection v6→v7, source pins, subject triple |
| Expected symlinks | `ls -ld` | `external/ESSO`, `external/mathlib4`, `lean-mathlib/.lake/packages/*` present as symlinks; gitignored via `.gitignore:2`, hence absent from `git status` rather than listed as `??` |

### Recorded values (all reproduced fresh)

| Constant | Recorded | Fresh | Match |
|---|---|---|---|
| `RECORDED_SOURCE_SHA256` | `e3c841e25db8051c1fe1903cc441db5b2f378f87d997d5d31c528dba3ced39f9` | sha256 of the yaml at S6 | YES |
| `RECORDED_IR_HASH` | `sha256:08fce65c258f145667cdf0df33e1c8464d6ca24f572fd39e4c21bf25778f9158` | `ESSO validate` | YES |
| `RECORDED_FINGERPRINT` | `256b0dcbb7c25c9581d6b16db8f2a5b44512d18c9cadf420477d6c63e38dfc86` | `verify-multi` (both trials) | YES |
| `RECORDED_ESSO_CODE_HASH` | `7f80c6216be85c827e8d1cc2fa08ee3107a74588` | unchanged in the diff; `verify-multi` reports the same | YES |
| Queries | `{init_implies_inv, inductive_open_claim, inductive_drain_claim, inductive_deposit_reserve}` | identical set | YES |
| `total_queries == passed_queries` | 4 | 4 | YES |

---

## 4. Answers to the six review questions

**1. Semantics of the model change.** The five invariants are byte-identical and no invariant
reads `reserve_*`, so preservation under `deposit_reserve` is structural, not incidental —
confirmed by both solvers (`inductive_deposit_reserve` unsat) and by 148 executed steps with
zero frame violations. `deposit_reserve` is genuinely inert: its update set is exactly
`{reserve_d0, reserve_d1}` and its guard reads only a reserve coordinate and its own `amount`.
The var-valued effect behaves as intended — ESSO evaluates effects in the **post** state
(`ESSO/kernel/interpreter.py:153`), and since `deposit_reserve` never updates `g_decision`,
post equals pre and the decision is genuinely re-emitted unchanged. The mutant claim is
accurate: `reserve_masking_open_claim` routes `open_claim`'s `custody_d0` increment into
`reserve_d0`, and the two-solver counterexample shows the claimant's allocation growing to 8
while custody stays at 7 and the reserve absorbs the atom — a reserve standing in for missing
custody, caught by `inv_exact_custody_partition_d0` in isolation. I reproduced both the mutant
and the attribution independently.

**2. Observables.** The `ir_hash` really binds observables: an unmodified round-trip preserves
it, dropping one observable changes it. Making the allocation coordinates observable is
consistent with the notes calling them "verifier-derived evidence bound to the exact
global-state root" — evidence that a verifier derives and a consumer must be able to read
should be on the observation surface. Nothing is now observable that should not be, and
nothing that matters is hidden: all 21 state vars are observable, there are no `g_pre_*`
variables, and every emitted effect is declared.

**3. Bounded target contract, or a smuggled reserve claim?** Still a bounded exact-partition
target contract. No reserve reconciliation claim was smuggled. The added claim is a *negative*
one — reserves are inert and cannot substitute for custody — and it is backed by an inductive
query and a named mutant. "Exact reserve reconciliation remains open and is not a claimed
invariant here" survives verbatim and is lexically pinned. `esso_evidence` gained only the
action, query and mutant names plus refreshed hashes; `completion_scope`, `nonclaims` and
`claim_ceiling` are unchanged, and `nonclaims` still disclaims the reserve reconciliation
certificate.

**4. Recorded values.** All verified — see the table in §3. Four queries, `total_queries ==
passed_queries == 4`, ESSO code hash unchanged.

**5. Consistency with the Lean model — stated honestly.** There is **no proved correspondence**
between the ESSO and Lean models, and — importantly — **no document claims one**. The Lean file
never mentions ESSO and the model YAML never mentions Lean. ESSO's `deposit_reserve` has **no
Lean counterpart**: no Lean function increments reserves. Lean's `deposit` is a *claimant*
deposit (grows custody, liability, open terminal; copies reserves unchanged) and is the
analogue of ESSO's `open_claim`, not of `deposit_reserve`. Lean handles reserves by the dual
route: `necessaryRelation_independent_of_reserves` and
`exactCurrentProfileCustody_independent_of_reserves` state that replacing the *entire* reserve
column by any other column leaves the relations unchanged, proved by `Iff.rfl` because the
predicates never mention reserves. That is strictly more general than ESSO's bounded query,
but it is definitional, and the packet discloses exactly that with "reserve independence
(definitional, disclosed)". The accurate characterization: two independent, mutually consistent
formalizations of one design intent — Lean states the definitional exclusion, ESSO supplies a
bounded operational witness plus a mutation showing the partition catches reserve masking.
Neither is derived from the other, and nothing claims otherwise.

**6. Admission-core precedence.** Not a regression. Confirmed behaviorally against both cores;
both orders reject, so fail-closed holds, and the new order surfaces a missing pinned path
before a content finding derived from the same snapshot. The ESSO model and gate are themselves
source pins, so a missing ESSO file reports identically under both orders.
`tests/test_check_o008_formal_cycle_v1.py` contains no ordering expectation between
`SOURCE_PIN_MISSING_IN_SUBJECT` and the `ESSO_*` family, and all 244 tests pass. The one line
C3 changed in that file is a robustness improvement — the `esso_zero_queries` case now derives
its literal from `len(core.ESSO_QUERIES_V1)` instead of hardcoding `3`, so the case cannot
silently stop matching when the query set changes.

**7. S/P chain.** P6 has exactly one parent (S6) and changes exactly the two packet paths.
S6's parent is the C1'' packet commit `9056dac69…`. Pins are Git blobs at S6; three
hand-recomputed. Executing checker bytes equal S6 for all three admission tools. The v7 packet
pins exactly S6 bytes (22/22) and all 54 `killed_by` node ids resolve.

---

## 5. Nonclaims and residual risks

**What this review did not establish:**

- I did not build Lean or run `lake build`; the Lean evidence is reviewed as source text and
  by its pinned hashes, not recompiled. `proof_replay` is `NOT_RUN` in the admitted packet, and
  the packet discloses this.
- I did not run cargo or any Rust gate (out of scope; C3 touches no Rust).
- I did not verify the RISC0, Tau, publisher, or runtime surfaces.
- My frame/inertness result is a bounded execution over 148 accepted steps from a spread of
  invariant-satisfying pre-states plus a structural argument, not an exhaustive proof over the
  full 2^56.3 state space. The structural argument (no invariant mentions reserves; the update
  set is exactly the two reserve vars) is what carries the generality.
- I did not re-derive the twelve-lane audit or the sidecar contract.
- I did not assess whether the bounded model is an adequate abstraction of the real
  GlobalSettlementABI V1 — the packet explicitly disclaims refinement.

**Residual risks:**

- The bounded model is one asset, two domains, two claimants, ≤8 atoms per cell, and
  `Inductive(k=1)`. Nothing here speaks to larger instances or multi-step trajectories beyond
  what one-step induction gives.
- Reserves are monotone non-decreasing in this model (deposit only, capped at 8). A withdrawal
  or a reserve→custody transfer is not modeled and would be the natural next adversarial surface.
- `ESSO_ACTIONS_DRIFT` protects the widened action allowlist with no test (P2-2); a future
  action addition could pass review on the strength of a guard nobody has exercised.
- The reject-code ordering C3 introduced is untested and could regress silently (P3-5).
- The effect surface alone cannot distinguish a reserve deposit from a claim (P3-1).
- The `RECORDED_FINGERPRINT` is a determinism witness only, as the packet's
  `fingerprint_role: DETERMINISM_WITNESS_NOT_MODEL_BINDING` correctly states; `ir_hash` is the
  binding value and is only verified under replay.

---

## 6. Do the user's decisions hold?

Yes, on every point I checked.

| Decision | Status | Evidence |
|---|---|---|
| Reserves are the claimant-free term of `controlled_atoms` | **Honored** | No invariant reads `reserve_*`; `deposit_reserve` writes exactly `{reserve_d0, reserve_d1}` and touches no claimant, custody, liability or terminal coordinate; 148 executed steps with 0 frame violations |
| Control-domain vocabulary in new code, V1 wire names byte-stable | **Honored** | `claim_boundary` reads "two-control-domain"; `completion_scope` uses "control-domain" throughout; the `Domain`/`Decision` enums and all V1 wire names are unchanged — the enums are byte-identical to C1'' |
| O-008A unattested | **Honored** | No O-008A attestation anywhere in the packet; `o008_status` stays `OPEN_EXACT_ALL_12_RECONCILIATION_MISSING` |
| UP-01..UP-20 unresolved, never fixture-selected | **Honored** | No `UP-` identifier appears in any file C3 touches; the v7 hygiene selection names only the three `THV1-20260901-*` evidence ids |
| Authority NONE | **Honored** | `claim_ceiling` byte-identical: all seven authority fields `NONE`, `whole_value_movement_safe: false`, `value_movement_gates_closed: 0` of `12` |
| `formal_core_complete` false | **Honored** | unchanged `false` |

The candidate also honors the campaign's artifact-only discipline: P6 is a direct child of S6
touching exactly the two packet paths, and the commit message states plainly that the committed
packet is stale at S6 by construction until the next artifact-only child.

---

## 7. Recommendation

Advisory: **A-**, accept with the two P2 repairs.

P2-2 (the missing `ESSO_ACTIONS_DRIFT` negative test) is a test-only change and can land
without re-cutting the model. P2-1 (the notes sentence) changes model bytes and therefore
requires a fresh S/P pair with new recorded hashes, a v8 hygiene packet and a fresh two-solver
replay — so it is naturally batched with whatever the next source commit turns out to be rather
than cut on its own. Neither finding undermines any verified statement in this candidate.
