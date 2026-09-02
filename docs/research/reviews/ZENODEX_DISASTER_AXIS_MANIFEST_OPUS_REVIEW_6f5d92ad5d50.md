# Adversarial review — disaster-axis status manifest

- **Subject**: commit `85d674efe1d30e1116727c023ec106381a835171`, branch `codex/disaster-axis-manifest-20260902`
- **Reviewer worktree**: `/tmp/zenodex-opus-disaster-review` (detached at 85d674efe; subject worktree not modified)
- **Date**: 2026-09-02
- **Verdict**: **C+** — the totality half is sound and well-tested; the binding half does not bind; three of the twelve promoted `inductive_esso` rows overstate what their models prove.

---

## Summary

| Claimed property | Result |
|---|---|
| 1. TOTALITY (one row per live axis, fail-closed on unmapped/dead/duplicate) | **CONFIRMED** |
| 2. BINDING (model + receipt sha-pinned, two-solver VERIFIED checked) | **BROKEN** — P1-1, P1-2 |
| 3. HONESTY (bounded_replay claims only bounded evidence; no overstatement) | **PARTIAL** — P2-1..P2-5 |
| 4. RECEIPT FRESHNESS (regenerate and compare) | **CONFIRMED, 12/12** (stronger than the 2 requested) |
| 5. CHECKER (fail-closed, no traversal, closed vocabulary, axis pinning) | **MIXED** — axis pinning works; traversal and hostile-shape handling do not |

Baseline reproduced green before any mutation: checker `ok: true`, `axis_count: 125`, `{bounded_replay: 113, inductive_esso: 12}`; `build --check` clean; `pytest tests/tools/test_check_disaster_axis_status_manifest.py` 9 passed; `ruff` and `mypy` clean on both tools.

---

## P1 findings (unsound acceptance)

### P1-1 — The receipt is never bound to the model it certifies; all 12 rows can rest on one proof

`tools/check_disaster_axis_status_manifest.py:61-89`

The checker verifies, independently, that `model_path` hashes to `model_sha256` and that `receipt_path` hashes to `receipt_sha256`, then opens the receipt and reads `report.verdict` etc. Nothing ties the three together. The receipt itself carries `model.path`, `model.ir_hash`, and `report.model_id` — none are read. Nothing ties either artifact to the row's `axis_id` either; the axis→model map lives only in the *builder* (`INDUCTIVE_MODEL_BY_AXIS`, `tools/build_disaster_axis_status_manifest.py:29-42`), and the builder's `--check` mode is not exercised by any test and not wired into CI.

Consequence: the manifest can claim 12 inductive axes while only one model was ever verified.

Minimal repro (accepted, `ok: true`):

```python
# rewrite every inductive row's model/receipt pins to the FIRST inductive row's
ind = [r for r in manifest["rows"] if r["status"] == "inductive_esso"]
for r in ind[1:]:
    for k in ("model_path", "model_sha256", "receipt_path", "receipt_sha256"):
        r[k] = ind[0][k]
check_manifest(root, manifest_path)   # -> {"ok": true, ... "inductive_esso": 12}
```

The three weaker variants requested all pass as well: swapping model+receipt between two rows, swapping only the model (leaving a receipt that describes a different model), and pointing two rows at one receipt.

**Fix (3 lines)**: after loading the receipt, require
`receipt["model"]["path"] == row["model_path"]`, `receipt["report"]["model_id"] == Path(row["model_path"]).stem`, and `receipt["model"]["ir_hash"]` equal to the ir_hash recomputed from (or pinned alongside) the model.

### P1-2 — A hand-forged four-key receipt is accepted as a two-solver VERIFIED proof

`tools/check_disaster_axis_status_manifest.py:81-89`

The receipt gate reads exactly four fields plus `ok`. It never checks that the run used two solvers, never checks that any query was discharged, and never checks provenance. This receipt is accepted:

```json
{"ok": true, "report": {"verdict": "VERIFIED", "solvers_agreed": true,
                        "failed_queries": 0, "inconclusive_queries": 0}}
```

Two narrower forms also pass:
- **single-solver receipt** — set `solvers: ["z3"]`, `report.cvc5_available: false`, `cvc5_passed: false`, strip every `queries.*.cvc5` block, leave `solvers_agreed: true`. Accepted. "Two-solver agreement" is asserted by a field the producer controls and the checker does not corroborate.
- **zero-query receipt** — `queries: {}`, `total_queries: 0`, `passed_queries: 0`. Accepted. `solvers_agreed: true` over zero queries is vacuous.

Correctly rejected: a receipt with the `report` key deleted (caught by the `ok`/verdict/agreement conjunction).

**Fix**: also require `receipt["solvers"] == ["z3", "cvc5"]` (or a superset check), `report.z3_passed and report.cvc5_passed and report.cvc5_available`, `report.total_queries >= 1`, `report.passed_queries == report.total_queries`, and `report.disagreements == []`.

---

## P2 findings (false or unsupported claim)

### P2-1 — `zusd_oracle_recovery_split_brain`: every oracle freshness/quorum guard is inert

`experiments/disaster_inductive_promotion/models/disaster_zusd_oracle_recovery_split_brain_inductive_v1.yaml`

The axis's disaster is *"oracle recovery region admits a risky zUSD state transition under split-brain oracle inputs."* The model builds a two-source quorum (`o1_epoch`, `o2_epoch`, `max_stale`, `commit_epoch`/`region_epoch`/`selector_epoch`) and 15 guard clauses that encode freshness, quorum agreement, and snapshot alignment.

**All 15 can be deleted at once and the model still verifies** (`VERIFIED 6/6`, z3+cvc5). Deleting the `drift_oracle` action — the model's own "split-brain window generator" — also leaves it `VERIFIED 5/5`. **No invariant references `o1_epoch`, `o2_epoch`, or `max_stale`** (checked mechanically: zero hits across `inv_solvent`, `inv_snapshot_aligned`, `inv_bounds`).

What actually carries the proof:
- `inv_solvent` (`collateral*price_e >= debt*mcr`) is preserved because `risky_borrow`'s last guard clause *is* the post-state invariant restated (`collateral*price_e >= (debt+borrow_amt)*mcr`), and likewise for `risky_redeem` and `commit_oracle_snapshot`. The model header (lines 55-58) states this openly but attributes it to "under a coherent view"; coherence is provably not required.
- `inv_snapshot_aligned` (`commit==region==selector`) is preserved because `commit_oracle_snapshot` assigns all three to `now_epoch` in one simultaneous update, and no other action writes them. It is definitional, not guarded.

Additionally the NON-VACUITY block (lines 70-73) claims *"`inv_coherent_snapshot` is genuinely violable: drift_oracle makes region_epoch/commit_epoch != now, so risky ops become disabled rather than the invariant being trivially true."* **There is no invariant named `inv_coherent_snapshot`** in the file, and the invariant that does exist (`inv_snapshot_aligned`) is untouched by `drift_oracle`, which writes only `now_epoch`, `o1_epoch`, `o2_epoch`. The stated non-vacuity argument does not apply to any invariant in the model.

Repro:
```bash
# delete every guard clause mentioning o1_epoch/o2_epoch/max_stale/commit_epoch/
# region_epoch/selector_epoch from commit_oracle_snapshot, risky_borrow, risky_redeem
PYTHONPATH=/home/trevormoc/Downloads/ESSO ZENO_ESSO_PYTHON=/usr/bin/python3 \
  /usr/bin/python3 -m ESSO verify-multi <stripped>.yaml --solvers z3,cvc5
# -> verdict VERIFIED, passed 6/6
```

The row's `inductive_esso` status therefore does not certify anything about split-brain admission.

### P2-2 — `settlement_proof_recompute_gate`: the root-match half of the disaster invariant is not enforced

`experiments/disaster_inductive_promotion/models/disaster_settlement_proof_recompute_gate_inductive_v1.yaml:156-173, 312-320`

`inv_apply_implies_recompute_match_and_strong` is documented (lines 156-160) as forbidding *"a settlement applied on a stale, divergent (root mismatch), or weak proof — exactly the 'proof-verifier wrapper accepts stale or weak settlement proof' disaster."*

Removing the pre-state root-match guard `recomputed_root == claimed_root` from `apply_settlement` leaves the model **`VERIFIED 4/4`**. The reason is at line 315: `apply_settlement` *overwrites* `claimed_root` with the new post-state root ("keep claimed_root pinned to the new recomputed root"). The root-match conjunct therefore holds by construction of the update, not because the gate refused a mismatched claim. Confirming the direction: removing the overwrite while keeping the guard yields `FAILED 3/4`.

The **strength** conjunct *is* load-bearing (removing `validator_strength >= required_strength` yields `FAILED 3/4`), so roughly half the disaster is genuinely certified. A real verifier cannot rewrite the prover's claim; the model should keep `claimed_root` adversary-fixed and instead weaken `inv_applied_root_is_poststate`.

### P2-3 — `state_accounting_size_boundary`: the canonical-size guard is dead code

`experiments/disaster_inductive_promotion/models/disaster_state_accounting_size_boundary_inductive_v1.yaml`

Deleting the entire "Canonical-size guard BEFORE apply" clause from `accrue` leaves the model **`VERIFIED 2/2`**. `ser_size` is recomputed as `width(sum_balances) + width(fee_accumulator)` over a `[0,999]` range, so its maximum reachable value is `3+3 = 6`, while `MAX_CANONICAL = 30`. Tightening the invariant to `ser_size <= 5` yields `FAILED 1/2`, pinning the reachable maximum at 6.

The model header claims *"inv_canonical_size and inv_no_overflow are then the disaster negations: they hold because the guard refuses any accrual that would breach either bound."* That is true for the overflow bounds (removing the `sum_balances` overflow guard yields `FAILED 1/2`) and false for the canonical-size bound: no accrual can breach it, so the guard never fires. Axis disaster (b), *"serialized canonical state root exceeds MAX_CANONICAL → oversized/noncanonical persistent root,"* is proved unreachable for range-calibration reasons that carry no information about `src/state/canonical.py::bounded_json_utf8_size`. Setting `MAX_CANONICAL` to 4 or 5 would make the guard load-bearing.

The other three invariants in this model are genuine: breaking the conservation update (`total_supply` drops the fee term) and freezing `ser_size` both flip to `FAILED`.

### P2-4 — `dex_settlement_recovery_proof_unit_boundary` is bound to a model covering roughly one third of its axis

The axis's disaster template is *"recovery-valid DEX settlement or proof-mining state replays stale proof or claimability context,"* with three mutation families all about the settlement grammar, the **proof-verifier unit**, **proof-mining claimability**, and **Tau Testnet recovery** validating *different* recovered states.

`disaster_dex_settlement_recovery_v1.yaml` models `vault / acct_a / acct_b / fee_acct / staged_amt / staged_fee / applied_seq / expected_seq / phase` and proves conservation plus no-double-apply across `begin_settle → abort_settle → recover_settle`. It contains **no proof root, no claimability state, and no manager root** — the multi-validator disagreement that defines the axis is not representable in it. This is also the only one of the twelve models not named `*_inductive_v1`.

The manifest has no field to record partial axis coverage: a model covering 1 of 3 mutation families gets the same `inductive_esso` badge as one covering 3 of 3.

### P2-5 — `bounded_replay` is assigned by default, never by evidence; `open` is unreachable by construction

`tools/build_disaster_axis_status_manifest.py:62,71-76`

```python
model_name = INDUCTIVE_MODEL_BY_AXIS.get(axis_id)
if model_name is not None:
    ...  # inductive_esso, with pins
else:
    row["status"] = "bounded_replay"
```

The `else` branch is unconditional. No replay receipt is read, hashed, or required. The declared vocabulary contains `open`, but no code path can ever emit it — a newly added axis with zero evidence is silently labelled `bounded_replay`, and the checker accepts it. The totality claim "every one of the 125 live axes has exactly one certified status row" is therefore satisfied by fiat for 113 of 125 rows.

Mitigating: the `evidence_note` is honest ("receipt is a local git-ignored artifact and is not CI-enforced"), and `docs/DISASTER_STATE_COVERAGE.md` does record a 125/125 green replay — but that receipt is dated **2026-04-25**, is git-ignored, and nothing in this commit re-establishes or pins it.

---

## P3 findings (gaps)

1. **No coverage ratchet.** `check_disaster_axis_status_manifest.py` accepts arbitrary status downgrades. Demoting an `inductive_esso` row to `bounded_replay` (dropping all four pins) → `ok: true`. Setting **all 125 rows to `out_of_scope`** and dropping every pin → `ok: true`. The manifest is the artifact that records coverage, and the checker cannot detect coverage regression. Only `build --check` would, and it is untested/unwired.

2. **Path traversal and absolute paths.** `check_disaster_axis_status_manifest.py:68` — `target = root / rel` with no confinement. `model_path: "/tmp/anything.yaml"` is accepted (Python's `/` operator discards `root` for an absolute right operand), and a `../`-relative path at the correct depth also escapes. Impact is limited (an attacker who can edit the manifest can edit the checker), but the checker cannot be pointed at an untrusted manifest, which its fail-closed docstring implies it can.

3. **`check_manifest` raises instead of returning `{"ok": False}`** on hostile shapes. All four crash: receipt is a JSON list (`:81`, `AttributeError`), `report` is a string (`:81`), `axis_count` is non-numeric (`:93`, `ValueError`), a `rows` entry is a string or `rows` is a dict (`:46`, `AttributeError`). The CLI still exits non-zero, so it is fail-closed as a process, but the library contract in the docstring is violated and the test suite asserts on the returned dict.

4. **`nonclaims` is unpinned decoration.** Deleting the entire `nonclaims` array and adding `"production_authority": "granted"` to the manifest → `ok: true`. The honesty of the artifact rests on text the checker does not enforce; only `schema` and `status_vocabulary` are pinned.

5. **Acceptance criterion 8 is not actually closed.** `docs/ZENO_DISASTER_STATE_MINIMIZATION_GOAL.md:45-50` asks for a table separating five categories: guaranteed unreachable / bounded-no-counterexample / backlog inventory / **external assumptions** / out-of-scope. The manifest's vocabulary has no bucket for *external assumptions*, and no `open` row exists to represent backlog. No document in the commit references the manifest — the goal doc, `DISASTER_STATE_COVERAGE.md`, and the README are unchanged — so the "public coverage table" the criterion names still does not point at this artifact.

6. **Guard-clause redundancy census.** Across the 12 models, **72 top-level guard clauses can each be individually deleted with the model still `VERIFIED`**. Individual redundancy is mostly *not* a defect here — I ran the joint-deletion test (delete the whole semantic family at once) on the two models where it mattered most and both held up:

   | Model | Family deleted jointly | Result |
   |---|---|---|
   | `dex_engine_sequence_anomaly_surface` | 8 receipt-freshness / nonce-ordering clauses (`issued_receipt_live`, `issued_receipt_epoch == now_epoch`, nonce ordering) across 4 actions | **`FAILED 3/5`** — jointly load-bearing |
   | `perp_funding_liquidation_oracle_window` | 3 oracle-staleness clauses (`oracle_seen`, `oracle_last_update_epoch`, `max_stale`) across `open_position`/`apply_funding`/`liquidate` | **`FAILED 4/6`** — jointly load-bearing |
   | `zusd_oracle_recovery_split_brain` | 15 freshness/quorum clauses across 3 actions | **`VERIFIED 6/6`** — inert (P2-1) |

   So the redundancy is benign in the two comparable models and the zusd model is the outlier, not the norm. The remaining nine models were not joint-tested; the individual census is recorded above as a screening signal, not a finding against them.

---

## Confirmed-good

**Totality (property 1) — sound.** Dropping a row names the unmapped axis; renaming a live axis produces both `row names a dead axis` and `live axis has no status row`; a duplicate `axis_id` is caught; an unknown status is caught. All nine shipped tests pass and each kills the mutation it names.

**Axis-definition pinning (property 5) — genuinely works.** This was tested with *real* axis edits, not just sha tampering. Mutating `what_if`, `priority_score`, `commands`, or `surface_ids` on a live axis dict each produce `axis definition drift: <axis_id>`; `_axis_definition_sha` hashes the full canonical JSON, so every field is covered.

**Receipt freshness (property 4) — confirmed at 12/12.** All twelve models were re-run with `verify-multi --solvers z3,cvc5` and compared field-by-field against the committed receipts with only `timestamp` and `time_ms` scrubbed. **Zero mismatches.** Every `model.ir_hash` matched, every `verdict` is `VERIFIED`, `solvers: ["z3","cvc5"]`, `z3 4.15.4` + `cvc5 1.1.2`, `failed_queries: 0`, `inconclusive_queries: 0`, `passed == total` (2 to 7 queries per model, 55 total). The receipts are real, current, and reproducible on this machine.

**Nine of twelve models are well-aligned to their axes** and carry explicit `MODEL<->CODE GAP` sections naming what is abstracted and omitted: `batch_refinement_mci_parity_boundary` (lex-monotone refinement), `batch_settler_greedy_adapter_boundary` (greedy-vs-adapter envelope lockstep), `dex_engine_sequence_anomaly_surface`, `perp_funding_liquidation_oracle_window` (`inv_no_window_disagreement` matches the axis's window-disagreement template closely), `reciprocal_netting_pair_forgery` (four legs, `weak_would_admit` vs `pairing_ok` — a genuine strong-vs-weak-gate separation), `settlement_proof_recompute_gate` (strength half), `vault_reward_carry_spendability`, `zusd_native_accounting_gate_boundary`, and the conservation half of `state_accounting_size_boundary`.

**The `quote_receipt_gate_decomposition_consistency` model discriminates.** It is a self-consistency check between two hand-written expressions rather than an extraction from `src/core/quote_receipts.py`, and its own comments say so. But it is not a tautology: introducing a cross-gate "repair" into the composed driver flips it to `FAILED 1/2`, so `inv_no_cross_repair` does distinguish a safe driver from an unsafe one. It covers mutation family 2 of 3.

**Tooling quality is clean.** `ruff check` and `mypy` both pass on the two tools; the checker is a pure function with an imperative CLI shell; `--root` is threaded properly for artifact resolution (though the axis source is always imported from the checker's own repo, not `--root` — worth documenting).

---

## Recommended minimum before this is treated as a keystone

1. Bind receipt → model → axis (P1-1) and corroborate solver provenance (P1-2). Both are small, local edits to `check_disaster_axis_status_manifest.py:74-89`, plus two new mutation-killer tests.
2. Add a test that runs `build_disaster_axis_status_manifest.py --check` — today nothing enforces the axis→model map.
3. Re-model or re-badge `zusd_oracle_recovery_split_brain` (P2-1); it currently proves a solvency arithmetic identity, not split-brain safety. Run the same joint-deletion test on `dex_engine_sequence_anomaly_surface` and `perp_funding_liquidation_oracle_window` before trusting them.
4. Stop `apply_settlement` from rewriting `claimed_root` (P2-2), and tighten `MAX_CANONICAL` (P2-3), so the guards that encode the real gates become load-bearing.
5. Give the manifest an `open` path and a per-row coverage field (which mutation families the model covers), so `bounded_replay` stops meaning "not inductive" and `inductive_esso` stops meaning "some part of this axis".
6. Confine artifact paths to `root`, return `{"ok": False}` instead of raising on hostile shapes, and pin `nonclaims`.

---

## Commands used

```bash
git worktree add --detach /tmp/zenodex-opus-disaster-review 85d674efe
cd /tmp/zenodex-opus-disaster-review
/usr/bin/python3 tools/check_disaster_axis_status_manifest.py          # ok: true, 125, 113/12
/usr/bin/python3 tools/build_disaster_axis_status_manifest.py --check  # ok: true
"$VENV/python" -m pytest tests/tools/test_check_disaster_axis_status_manifest.py -q   # 9 passed
"$VENV/python" -m ruff check tools/{build,check}_disaster_axis_status_manifest.py     # clean
"$VENV/python" -m mypy      tools/{build,check}_disaster_axis_status_manifest.py      # clean
PYTHONPATH=/home/trevormoc/Downloads/ESSO ZENO_ESSO_PYTHON=/usr/bin/python3 \
  /usr/bin/python3 -m ESSO verify-multi <model>.yaml --solvers z3,cvc5   # x12, all reproduced
```

Mutation harnesses (18 manifest attacks, 5 axis-drift probes, 12-model re-verify, 72-clause dead-guard sweep, decisive joint-deletion tests) are under `/tmp/claude/dz/`: `attack.py`, `attack2.py`, `reverify.py`, `mutate_models.py`, `mut2.py`, `deadguard.py`, `decisive.py`, `decisive2.py`, `joint.py`.

---

# Addendum — re-verification at `98a601ffe` (2026-09-02)

- **Subject**: commit `98a601ffe7ce2a48a3ddcf417a0487de75375494` ("fix: bind disaster receipts to their models and reject forged verdicts")
- **Reviewer worktree**: fresh detached `/tmp/zenodex-opus-disaster-review2`; subject worktree not modified (`git status --porcelain` empty)
- **Updated grade: B** (was C+)

## 1. Both P1 exploit classes are closed

The full 18-attack battery from round 1 was re-run unchanged against the new checker (`/tmp/claude/dz/attack_v2.py`). Every P1 exploit now fails closed:

| Round-1 exploit | Then | Now |
|---|---|---|
| 1. swap model+receipt between two axes | accepted | **rejected** — `model_path does not name the registered model` |
| 2. swap model only (receipt describes a different model) | accepted | **rejected** — `receipt certifies a different model path` |
| 3. two rows share one receipt | accepted | **rejected** — `duplicate receipt_path shared across proof rows` |
| 4. all 12 rows → one model+receipt | accepted | **rejected** (3 distinct errors) |
| 8. single-solver receipt (cvc5 stripped) | accepted | **rejected** — `solvers are not exactly z3+cvc5` + per-query `lacks an unsat cvc5 result` |
| 9. zero-query vacuous receipt | accepted | **rejected** — `receipt carries no queries` |
| 10. fully forged 4-field receipt | accepted | **rejected** (3 distinct errors) |

Two round-1 P3s closed as a side effect: **11. relative traversal** and **12. absolute `model_path`** are now both rejected, because `endswith(f"/{expected_model}.yaml")` plus the `receipt.model.path` equality leaves no room to relocate an artifact. A traversal path crafted to still end with the registered model name (new exploit R8) is also rejected.

Baseline at the new head: checker `ok: true`, `axis_count: 125`, `{bounded_replay: 114, inductive_esso: 11}`; `build --check` clean; **14/14 tests pass**; `ruff` and `mypy` clean. All **12 committed receipts still reproduce byte-identically** under a fresh `verify-multi --solvers z3,cvc5` (timestamps and `time_ms` scrubbed), including the now-unreferenced zusd receipt — zero mismatches.

## 2. Do the five new tests kill the exploit classes? — Partly

I mutated each new guard out of the checker individually and ran the suite. **Four of the eight guards have no mutation killer:**

| Guard | Lines | Mutation result |
|---|---|---|
| G1 registered-model-name | `:63-67` | **KILLED** by `test_swapped_model_receipt_pair_is_rejected` |
| G2 `receipt.model.path` equality | `:97-98` | **KILLED** by `test_receipt_certifying_a_different_model_is_rejected` |
| G3 `report.model_id` equality | `:99-101` | **SURVIVED** — deleting it leaves 14/14 green |
| G4 `solvers == ["z3","cvc5"]` | `:104-105` | **SURVIVED** — 14/14 green |
| G5 queries non-empty | `:106-108` | **KILLED** by `test_hand_written_verified_receipt_is_rejected` |
| G6 per-query `agreed` + unsat from both solvers | `:110-117` | **SURVIVED** — 14/14 green |
| G7 counts == `len(queries)` | `:118-119` | **SURVIVED** — 14/14 green |
| G8 model/receipt path uniqueness | `:120-124` | **KILLED** by `test_swapped_model_receipt_pair_is_rejected` |

G6 is the *core* of the P1-2 repair — it is the only thing that actually reads the two-solver evidence — and nothing pins it.

Root cause for G4/G6: `test_single_solver_receipt_is_rejected` asserts
`any("not exactly z3+cvc5" in e or "lacks an unsat cvc5 result" in e for e in errors)`.
The `or` pins only the *disjunction*. Confirmed: removing G4 and G6 **together** does fail that test (`1 failed, 13 passed`), removing either alone does not. Splitting that assertion into two `assert any(...)` lines kills G4 and G6 separately, at zero cost.

## 3. Residual bypasses of the repair (new, P2/P3 — not P1)

Harness: `/tmp/claude/dz/attack3.py`.

**R1/R2 (P2) — the model file's *content* is still unbound; only its *name* is bound.** `:97-101` compare the receipt's `model.path` string and `report.model_id` string against the row's `model_path` string. Every real receipt carries `model.ir_hash` (e.g. `sha256:21fd0d3970e5567f…`) and it is never compared against anything derived from the model file. So:
- **R2**: overwrite a model with `"this is not an ESSO model at all"`, update the row's `model_sha256` → **accepted**.
- **R1**: swap the *contents* of two models, keep both filenames, update both `model_sha256` → **accepted**; each receipt still "certifies" a file it never saw.

The commit message says the receipt "must certify the row's own model." It certifies the row's own model *path*. That is a real improvement over round 1, but it is one level weaker than the claim.

**R3/R4 (P2) — the query set is checked for shape, not for correspondence to the model.** `:106-119` require a non-empty query dict whose counts match `len(queries)` — nothing ties the query *names* to the model's proof obligations.
- **R4**: take the real receipt for a 3-query model, delete 2 queries, set `passed_queries = total_queries = 1` → **accepted**. A receipt can silently drop `init_implies_inv` and every inductive check but one.
- **R3**: hand-forge a receipt with one fabricated query named `totally_made_up`, `agreed: true`, `unsat` from both solvers, matching counts → **accepted**.

**This is mechanically fixable and closes R1–R4 at once.** The expected query set is derivable from the model YAML: the declared `checks:` ids when present, otherwise `{init_implies_inv} ∪ {inductive_<action> for each action}`. I verified this against every committed pair: **11/11 exact matches** (2 to 7 queries each). Requiring `set(receipt["queries"]) == derived_set(model_yaml)` binds the receipt to the model's *content*, not just its name, and rejects garbage models (no derivable actions), swapped models (wrong action names), stripped receipts, and fabricated query names.

**R5 (P3) — the axis→model registry is enforced one-way.** `:62-67` only checks "proof status ⟹ registered". Nothing checks "registered ⟹ proof status", so any of the 11 inductive certificates can still be silently demoted to `bounded_replay` (pins dropped) with `ok: true`. Round-1 exploits 16 (demote) and 18 (all 125 → `out_of_scope`) both still succeed. The one-line fix is the converse check; `build --check` would also catch it, which makes its absence from the test suite and CI more load-bearing than it was in round 1 — **still untested and still unwired** (verified by grep over `tests/`, `.github/`, `Makefile*`, `scripts/`).

**R6 (P3) — one new hostile-shape crash site.** `receipt["model"]` set to a string raises `AttributeError` at `:97`. The round-1 crash sites (`:47`, `:87`, `:128`, and receipt-is-a-list) are all still present. `receipt.queries` as a list is handled correctly (`:107` `isinstance` check) — that pattern applied at `:87`/`:97` closes the class.

## 4. Are the remaining open P2s honestly represented? — Yes

- **zusd downgrade is real and accurate.** `INDUCTIVE_MODEL_BY_AXIS` no longer registers the axis; the row is `bounded_replay` with an `evidence_note` that states the finding correctly ("oracle freshness/quorum guards are jointly deletable with VERIFIED preserved, so the inductive certificate does not certify this axis's semantics; bounded 240s replay lane only until the model is strengthened"). Counts moved to 11 + 114, and a test pins both the status and the note. The builder carries an explanatory comment at the registry. This is the right disposition: the axis was demoted rather than the finding argued away.
- **The three model-work P2s are left visibly open**, not papered over — `settlement_proof_recompute_gate` (root-match guard non-load-bearing because `apply_settlement` rewrites `claimed_root`), `state_accounting_size_boundary` (dead canonical-size guard), and `dex_settlement_recovery_proof_unit_boundary` (model covers ~1 of 3 mutation families). All three still carry `inductive_esso`. Given that the manifest has no field for partial axis coverage, that is defensible for the first two (a real, if partial, certificate) and weakest for the third, where the model contains no proof, claimability, or manager-root state at all. I would not block on it, but it is the next one to either re-model or downgrade.
- **The orphaned zusd model and receipt remain committed** and unreferenced by any row. Harmless, and arguably right — they are the evidence for the downgrade note — but nothing now checks them, so they will rot silently.

## 5. Updated grade: B

The two P1s are genuinely closed against every exploit I could build, including three I only invented for this round; two round-1 traversal P3s closed as a bonus; the zusd downgrade is honest and test-pinned; receipts still reproduce 12/12; tooling stays clean. Held below B+ by two things, both cheap: the receipt is bound to the model's *name* rather than its *content* (R1–R4), which is one level weaker than the commit message claims; and four of the repair's own eight guards — including G6, the two-solver evidence check that is the whole substance of the P1-2 fix — have no mutation killer.

**To reach A:** (a) require `set(receipt["queries"])` to equal the set derived from the model YAML — verified 11/11 derivable, and it closes R1–R4 together; (b) split the `or` in `test_single_solver_receipt_is_rejected` and add killers for G3, G6, G7; (c) add the converse registry check and a `build --check` test (closes R5 and the ratchet); (d) `isinstance` guards at `:87`/`:97` and a `try/except` at `:128` so `check_manifest` returns `{"ok": False}` instead of raising.

---

# Addendum 2 — final re-verification at `07129479a` (2026-09-02)

- **Subject**: commit `07129479a91f765f3fc5b7645473a60e2f256cf3` ("fix: bind receipts to model content and pin every guard individually")
- **Reviewer worktree**: fresh detached `/tmp/zenodex-opus-disaster-review3`; subject worktree not modified
- **Final grade: A−**

## 1. Every exploit class I built is now closed

Full battery re-run unchanged (`attack_v3.py`, `attack2_v3.py`, `attack3_v3.py`), plus five new probes (`attack4.py`).

| Exploit | Round 1 | Round 2 | Round 3 |
|---|---|---|---|
| 1-4 swap / share / all-rows-one-artifact | accepted | rejected | **rejected** |
| 8-10 single-solver / zero-query / forged receipt | accepted | rejected | **rejected** |
| 11-12 relative + absolute traversal | accepted | rejected | **rejected** |
| R1 model content swapped (shas resynced) | — | accepted | **rejected** — `query set does not match the model's declared checks` |
| R2 model gutted to garbage (sha resynced) | — | accepted | **rejected** — `model does not parse as an ESSO model` |
| R3 forged receipt, invented query name | — | accepted | **rejected** |
| R4 real receipt stripped to 1 of N queries | — | accepted | **rejected** |
| R6 `receipt.model` is a string | — | crash | **rejected** (no crash) |
| R8 traversal ending in the registered model name | — | rejected | **rejected** |
| T4 query result `sat` with `agreed: true` | — | — | **rejected** |
| T5 model with empty `checks` and empty `actions` | — | — | **rejected** |

`expected_queries_for_model` is the fix I proposed and it lands correctly: declared `checks` win, otherwise `init_implies_inv` plus `inductive_<action>` per action, and the receipt's query set must equal it. That single derivation closes R1–R4 together, exactly as predicted.

Baseline: `ok: true`, 125 axes, **10 inductive_esso + 115 bounded_replay**, `build --check` clean, **23/23 tests pass**, ruff clean. All **12 committed receipts still reproduce byte-identically** under fresh `verify-multi --solvers z3,cvc5` — zero mismatches, including the two now-orphaned ones.

## 2. Guard pinning — complete for the repairs, 18/28 overall

I swept every `errors.append` site in the checker (28 of them), neutralising each individually and running the suite (`guardsweep3.py`).

**All twelve guards added in rounds 2 and 3 are now individually pinned**, including the four that survived in round 2:

| Guard | Round 2 | Round 3 |
|---|---|---|
| G3 `report.model_id` | SURVIVED | **KILLED** by `test_receipt_model_id_drift_is_rejected` |
| G4 `solvers == ["z3","cvc5"]` | SURVIVED | **KILLED** — the `or` was split into two conjunctive asserts |
| G6 per-query unsat from both solvers | SURVIVED | **KILLED** by `test_dropping_cvc5_from_one_query_is_rejected` |
| G7 counts == `len(queries)` | SURVIVED | **KILLED** by `test_query_count_drift_is_rejected` |

**Ten sites remain unpinned — all pre-existing, none from the repairs**: schema drift (`:67`), vocabulary drift (`:69`), unregistered-axis proof status (`:93`), pin missing (`:100`), receipt not JSON (`:113`), `ok is not true` (`:117`), `solvers_agreed` false (`:121`), failed/inconclusive queries (`:123`), per-query `agreed` false (`:141`), and `axis_count` drift (`:173`).

I confirmed each of these **functions correctly** — they are untested, not broken. I drove all ten directly (`unpinned.py`) and every one rejects. Ten small tests would take the suite to 28/28.

## 3. Residuals

**T2 (P3) — joint model+receipt weakening.** Delete an action from a real model *and* its corresponding query from the real receipt, resync both shas → **accepted**. The derivation follows the mutated model, so consistency is preserved under joint weakening: a transition silently stops being checked for inductiveness. This is inherent to any consistency check that does not re-run the solver. The real defense is that both artifacts are committed, so the weakening is visible in `git diff` — which makes manifest-diff review the control, and that is a reasonable place to leave it.

**T1 (P3) — the stated floor.** A model gutted to `ir_version` + `checks: [{id: q}]` with a forged one-query receipt is **accepted**. Self-declared `checks` are trusted by construction. Closing this requires re-running ESSO to recompute the ir_hash; it is the boundary of what a pure-Python checker can do, not a defect, but it is worth stating in the checker docstring so nobody reads `inductive_esso` as solver-backed without a CI re-run.

**T3 (P3, cheap to close) — `ir_hash` is still never checked.** Falsifying `receipt.model.ir_hash` and `report.ir_hash` (model bytes untouched) is **accepted**. Pinning `model_ir_hash` in the row from the receipt and requiring a match would make the receipt's self-description tamper-evident and give CI a concrete value to recompute against ESSO. It does not stop T2, but it costs two lines.

**NEW REGRESSION (P3) — mypy is no longer clean.** `import yaml` at `check_disaster_axis_status_manifest.py:18` has no stubs:

```
tools/check_disaster_axis_status_manifest.py:18: error: Library stubs not installed
for "yaml"  [import-untyped]
```

Confirmed with `--no-incremental` both alone and alongside the builder (an earlier "Success" was a stale-cache artifact). Both files were mypy-clean at `98a601ffe`. Given the repo's typing ratchet this should not merge as-is: add `types-PyYAML`, or `import yaml  # type: ignore[import-untyped]`.

**Still open from round 1** (unchanged, correctly so): `check_manifest` raises rather than returning `{"ok": False}` on four hostile shapes (receipt-is-a-list `:113`-adjacent, `report` as a string, non-numeric `axis_count`, non-dict row); the checker itself still accepts a demoted certificate (R5 — now defended by `test_builder_check_mode_catches_a_demoted_certificate`, which is a legitimate defense, though `build --check` is still not in CI); `nonclaims` is unpinned; and criterion 8's "external assumptions" category still has no bucket.

## 4. Are the downgrades and the remaining model-work P2s honest? — Yes, with one gap

**Both downgrades are accurate and specific.** `zusd_oracle_recovery_split_brain` and `dex_settlement_recovery_proof_unit_boundary` are deregistered, `bounded_replay`, and each carries a note stating the actual finding ("oracle freshness/quorum guards are jointly deletable with VERIFIED preserved"; "carries no proof, claimability, or manager-root state, covering about one of the axis's three mutation families"). Both are test-pinned. Counts moved 12 → 11 → 10 across the two rounds, in the honest direction each time: **the count went down because evidence was re-examined, not up because more was claimed.** That is the behaviour I would want from this artifact.

**One gap remains.** `settlement_proof_recompute_gate` and `state_accounting_size_boundary` are still `inductive_esso` and carry **no field recording their known partial certification** — I confirmed their rows have only the seven standard keys. Both P2s stand exactly as filed (the models and receipts are byte-identical to `85d674efe`; `git diff --stat 85d674efe 07129479a -- experiments/` is empty): the root-match guard in the proof gate is still non-load-bearing because `apply_settlement` rewrites `claimed_root`, and the canonical-size guard in the accounting model is still dead. The generic nonclaim covers them technically, but the two downgraded rows got detailed notes while these two known-weak retained rows got nothing. A one-line `caveat` field on each would make the manifest self-describing rather than requiring a reader to find this report.

## 5. Final grade: A−

Three rounds in, every P1 and every residual exploit class I could construct is closed; the fix for R1–R4 is the minimal one and generalises correctly; all twelve repaired guards are individually mutation-pinned; and twice the response to a finding was to *downgrade a claim* rather than defend it. Receipts have reproduced 12/12 in all three rounds. The remaining items are small and mostly pre-existing.

Held from A by three things, each a few lines: the **mypy regression** (a previously green gate is now red), the four **hostile-shape crashes** that still raise instead of returning `{"ok": False}`, and the two **known-weak retained rows carrying no caveat**. Adding the ten tests for the pre-existing guards and the `model_ir_hash` pin (T3) would leave nothing material outstanding on the tooling; what would remain is model work — re-authoring the proof-gate and accounting models so their guards are load-bearing.

---

# Addendum 3 — final verification at `6f5d92ad5` (2026-09-02)

- **Subject**: commit `6f5d92ad5d500c743dc793d5b3d97b0c734cb582` ("fix: make the manifest self-describing and the checker total")
- **Reviewer worktree**: fresh detached `/tmp/zenodex-opus-disaster-review4`; subject worktree not modified
- **Final grade: A**

All three A-blockers from Addendum 2 are fixed and verified. Baseline: `ok: true`, 125 axes, 10 inductive + 115 bounded, `build --check` clean, **26/26 tests**, ruff clean, and **all 12 receipts still reproduce byte-identically** (fourth consecutive round).

## 1. Hostile shapes — total, via both the wrapper and the CLI

Eleven hostile shapes driven through `check_manifest`, `check_manifest_total`, and the CLI:

| Shape | `check_manifest` | `check_manifest_total` | CLI |
|---|---|---|---|
| receipt is a JSON list | raises `AttributeError` | **`ok: false`** | exit 1, no traceback |
| `report` is a string | raises `AttributeError` | **`ok: false`** | exit 1, no traceback |
| `axis_count` non-numeric | raises `ValueError` | **`ok: false`** | exit 1, no traceback |
| row entry is a string | **`ok: false`** (early guard) | `ok: false` | exit 1 |
| `rows` is a dict | **`ok: false`** (early guard) | `ok: false` | exit 1 |
| manifest root is a list / a scalar / not JSON | **`ok: false`** | `ok: false` | exit 1 |
| a row is `null` / `status_vocabulary` is a dict / a query is `null` | **`ok: false`** | `ok: false` | exit 1 |

Every one is now a clean rejection at the CLI with a non-zero exit and no traceback. The design is right — early `isinstance` guards for the common cases, a `try/except Exception` totality boundary for the rest, and `BaseException` deliberately not caught so `KeyboardInterrupt`/`SystemExit` still propagate. One note for callers: `check_manifest` itself still raises on three of these; totality lives in `check_manifest_total`, which is what the CLI uses. Worth a line in the module docstring naming `check_manifest_total` as the entry point.

## 2. The ir_hash pin kills the T3 probe — with its scope correctly stated

Six probes: falsifying `model.ir_hash` alone, `report.ir_hash` alone, deleting either, and stripping the `sha256:` prefix are **all rejected** (`receipt ir_hash fields are absent or inconsistent`). The guard is individually pinned by `test_inconsistent_ir_hash_fields_are_rejected`.

Falsifying **both fields consistently** is still accepted — which is exactly what "the receipt's two ir_hash fields must agree" claims, and the scoping is honest. It is also inert: the model bytes are untouched and the derived query set still matches, so nothing false can be claimed through it. The ir_hash pin buys tamper-evidence on the receipt's self-description; the model-content binding is carried by `expected_queries_for_model`, which is the stronger mechanism and already lands.

Side benefit: the ir_hash pin raised the forgery floor. My round-3 T1 probe (gutted model self-declaring `checks` plus a matching forged receipt) now **fails**, because the forged receipt lacked a consistent ir_hash pair. Adding one (`T1'`) makes it pass again — so the floor is unchanged in principle, just harder to hit by accident. Closing it genuinely requires re-running ESSO; see §5.

## 3. mypy is clean under my invocation

```
$ rm -rf .mypy_cache && mypy --no-incremental tools/build_... tools/check_...
Success: no issues found in 2 source files
$ rm -rf .mypy_cache && mypy --no-incremental tools/check_...
Success: no issues found in 1 source file
```
The `# type: ignore[import-untyped]` on the yaml import is the right minimal fix. Regression closed.

## 4. Caveat wording — accurate to my findings

Both retained partial certifications now carry a `caveat` field, pinned by `test_partial_certifications_carry_their_caveats`:

- `settlement_proof_recompute_gate`: *"the root-match guard is removable with VERIFIED preserved because apply_settlement overwrites claimed_root; the strength half is enforced"* — matches P2-2 exactly, **including the nuance that the strength half is genuinely load-bearing**. Not overstating the defect is as important as recording it, and this gets it right.
- `state_accounting_size_boundary`: *"the canonical-size guard is dead in-domain (max reachable ser_size 6 vs MAX_CANONICAL 30)"* — matches P2-3, carrying the exact numbers I measured.

Both downgrade notes and both caveats are test-pinned. The manifest now describes its own limits without a reader needing this report. That closes the last honesty gap I filed.

## 5. Guard pinning and the three carried residuals

**19/29 guard sites individually pinned** (up from 18/28; the new ir_hash guard is pinned). The ten unpinned sites are the same pre-existing ones, all previously confirmed functioning.

On whether the three carried residuals should block — **two no, one I would raise in priority**:

- **10 pre-existing unpinned guards — does not block.** All verified functioning by direct drive. Test debt, not defect.
- **T2 joint model+receipt weakening — does not block.** Inherent to any consistency check that does not re-run the solver, and visible in `git diff` since both artifacts are committed.
- **CI — I would raise this above "follow-up", and it is broader than `build --check`.** `tests/tools/test_check_disaster_axis_status_manifest.py` is referenced by **no workflow and no gate script** (verified by grep across `.github/`, `tools/*.sh`). `ci.yml` has no bare `pytest`; `run_critical_quality_gate.sh` runs a 66-file allowlist that does not include it. So **nothing in CI runs this checker or any of its 26 tests** — every guard verified across these four rounds is currently enforced only by a developer running pytest locally. The repo already has the right slot: `run_release_gate.sh` names individual `tests/tools/test_check_*.py` files. Adding this one is a one-line change and it is what converts this work from a local artifact into an enforced gate.

**The single highest-value addition** would be a CI step that re-runs `verify-multi` for the 10 referenced models and diffs against the committed receipts. I have now done exactly that four times; it takes **under 10 seconds for all 12 models**. It closes T1', T2, and the ir_hash-to-model-bytes question in one move, because it re-establishes the solver result from the model bytes rather than trusting any recorded field.

## 6. Final grade: A

Across four rounds every finding was either fixed with a minimal, correctly-scoped, individually-tested guard, or answered by **downgrading the claim** — the inductive count went 12 → 11 → 10, always downward, always because evidence was re-examined. Both P1s, all four round-2 residuals, and all three round-3 A-blockers are closed and verified against my own harnesses rather than against restated tests. The receipts have reproduced byte-identically in all four rounds. The manifest now states its own partial certifications in its own data.

What remains is honest and documented: a forgery floor that only re-running ESSO can lower, ten untested pre-existing guards that all work, joint-weakening visible in review, and the CI enrollment above. None of it undermines a claim the artifact makes.

---

# Addendum 4 — closure confirmation at `d176335c1` (2026-09-02)

Single-pass confirmation of the post-review hardening at `d176335c14d79747b42bfb2da69e28c1436df330`. **The A stands, and the branch head is stronger than the graded hash.**

**Enrollment is the pattern I pointed at.** `run_release_gate.sh` (which runs under `set -euo pipefail`, so any failure aborts the gate) now carries a `== release: disaster-axis status manifest ==` stanza running the checker with `--root` plus its pytest file — the same two-line shape as the neighbouring `check_*` gates. That closes the finding that nothing in CI ran this checker.

**The replay test is what I meant, and it fails closed.** It re-runs `ESSO verify-multi --solvers z3,cvc5` for all 10 inductive models with `check=True`, and requires the fresh `ir_hash`, `verdict`, `solvers_agreed`, and query-set to match the committed receipt. I exercised it three ways rather than reading it:

- **Without `external/ESSO`** (absent in a clean worktree, since `external/` is git-ignored): **FAILS** at the assert — it does not skip. That is the right call; note the operational consequence that the release gate now hard-requires ESSO to be provisioned wherever it runs.
- **With `external/ESSO` present**: **27/27 pass in 21.8s**, the replay portion matching the ~10s I measured.
- **With a one-constant model edit** (`MAX_CANONICAL` 30 → 31): **FAILS in 4.5s.** The gate has teeth.

That last result is the important one. Because the fresh `ir_hash` is derived from the model bytes, this gate closes the two residuals I had accepted as inherent: **T2** (joint model+receipt weakening with resynced shas) and **T1'** (a gutted model plus a fully consistent forged receipt) both now produce a divergent fresh `ir_hash` — or an ESSO failure under `check=True` — and fail the gate. It also settles the ir_hash-to-model-bytes question that the internal-consistency pin could not. I had estimated this single addition would close all three; it does.

**The other two items land as described.** The module docstring now names `check_manifest_total` as the entry point. The review receipt at `docs/research/reviews/ZENODEX_DISASTER_AXIS_MANIFEST_OPUS_REVIEW_6f5d92ad5d50.md` hashes to `df1e42d4b1ede6f3660fa9dce5706c1192bcfd13ce9f08ea7dfc2af7450909f2` — byte-identical to my four-round report at the graded commit.

**Remaining, unchanged and non-blocking:** the ten pre-existing unpinned guard sites (all verified functioning by direct drive) and the model work itself — re-authoring the proof-gate and accounting models so their guards become load-bearing, which the two `caveat` fields now record in the manifest's own data.

**Final: A at `6f5d92ad5`, and A at `d176335c1` with the strongest residuals closed.**
