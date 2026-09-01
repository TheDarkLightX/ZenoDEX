# Opus review receipt: candidate C2 at P2 = 3feaa62247f4baf581c45303119cac2293e16d4c

Reviewer: Opus 5 (independent reviewer, read-only, detached worktree `/tmp/zenodex-formal-core-review-p-3feaa6224`).
Date: 2026-09-01. Subject: P2 = 3feaa62247f4baf581c45303119cac2293e16d4c (tree f524f54f1f87979ee7e5d42c02a46e44a54e0dae), S2 = 85c45bd629f6793e06d995a335ec92fc8a5926e6, parent P1 = 3b3528bacc13c65bc386dacff7e3ee6943605ca1.
Verdict: Grade B+. Disposition: findings P1-1, P1-2, P2-1, P2-2, P2-3, P3-1, P3-2 are repaired by candidate C2' (the next source commit after this receipt); P3-3 was addressed by C1' (newest-matching hygiene selection). The grade is advisory and grants no authority.

Verbatim report follows (the probe scripts it names lived under /tmp/opus-c2-probe and are not part of the repository).

---

# C2 Review — Opus 5, read-only at P2 = `3feaa62247f4baf581c45303119cac2293e16d4c`

Worktree: `/tmp/zenodex-formal-core-review-p-3feaa6224` (left untouched, tracked changes 0; `/tmp/zenodex-opus-c2-cargo-target` deleted). Adversarial scripts live outside the repo at `/tmp/opus-c2-probe/`.

## 1. Grade: B+

The mechanism is A-grade work. `ClaimantBackingViewV1` makes reserve/balance masking unrepresentable at the type level rather than by convention; the reject set is a closed three-code enum with byte-identical messages across languages; every fold uses checked u128 and rejects before any inequality is evaluated; the view root is a genuine cross-language commitment (Python sorts dict keys in `_canonical_value`, Rust's `serde_json` `Map` is a `BTreeMap` with `preserve_order` off, and `arbitrary_precision` reproduces u128 digits exactly — so the 27-vector root parity is real differential evidence, not a same-code replay). The S2/P2 chain is exactly as specified, both hand-recomputed pins match, the manifest bump is justified by exactly one new call site, the THV1 re-pins are structurally honest, and every command exits 0.

What holds it below A- is claim discipline, which is precisely what this campaign exists to enforce. The evidence package asserts one **false impossibility** (declared-unreachable custody overflow — I constructed a valid `GlobalEconomicStateV1` that reaches it), and the composed guard's **reject precedence changed** relative to the reviewed C1 head while being described as "unchanged semantics." A packet at `risk_class: critical` carrying an unsupported bounded refutation is the exact defect the repo's own credibility rule targets. Neither defect is a safety hole — both directions are fail-closed — so this is a repair, not a rejection.

## 2. Findings

### P0 — none
No state makes Python and Rust disagree on code, message, view bytes, or view root; no reject path mutates state or returns partial results; no reserve or balance row can enter the view.

### P1-1 — The declared-unreachable custody fold overflow is reachable
`tools/render_global_claimant_backing_guard_v1_golden.py:354-360`, restated at `tests/evidence/test_hygiene/THV1-20260901-claimant-backing-guard-golden-v1.json` `nonclaims[1]`.

Exact statement: *"supply = custody + reserves + balances is validated as u128 at state construction, so custody rows of one asset cannot sum past u128 in a valid GlobalEconomicStateV1; the custody fold's checked addition is retained as defence in depth."*

False. `GlobalEconomicStateV1.__post_init__` (`src/core/global_settlement_types_v1.py:1391-1447`) validates per-row u128 bounds, token shape, ordering and uniqueness — it contains **no** supply/owned equality check. That equality is enforced only by `_require_conservation_refinement_v1` (`src/core/global_economic_state_effect_refinement_v1.py:494`), and in `_refine_snapshot_v1` the backing guard runs at lines **554-555** while conservation runs at line **562**, so the overflow fires first even end-to-end. Reproduced:

```
=== PROBE 2: custody fold overflow from a VALID GlobalEconomicStateV1 ===
  state constructed OK; custody rows: [('a1', 2**127), ('a2', 2**127)]
  state_root: 0xded0942ddf7e5267 ...
  derive: ValueError: economic refinement claimant backing total overflows
  classified code: ClaimantBackingRejectCodeV1.CLAIMANT_BACKING_TOTAL_OVERFLOW
=== PROBE 3: 4096-row custody overflow (bounded table) ===
  rows: 4096  derive: ValueError: economic refinement claimant backing total overflows
```
Repro command: `"$PY" /tmp/opus-c2-probe/probe.py`

Honest calibration: removing `checked_add` from the **custody** fold is not an R1 soundness hole. A wrap requires a true sum >= 2^128, and entitlements are folded with checked arithmetic so they are <= 2^128-1 < true custody; the resulting accept would be semantically correct. In Rust it is still a debug-build panic (CBC-forbidden) and it changes the observable reject code. The defect is the *claim*, not the guard.

Required repair: delete the `unreachable_mutations` entry and the THV1 nonclaim; add a `rejects_custody_aggregate_overflow` vector (custody `[("a1","USD","d",MAX),("a2","USD","d",1)]` with an explicit `supplies` override) mirroring the existing `rejects_entitlement_aggregate_overflow`; re-render. If the intent was that the fixture *builder* derives supplies (it does, `render_..._golden.py:104-108`), say that the builder cannot express it — do not attribute the invariant to the type.

### P1-2 — `_require_state_only_necessary_claimant_backing_v1` semantics changed; "unchanged semantics" is false
`src/core/global_economic_state_effect_refinement_v1.py:430-441` vs the P1 body at `git show HEAD^^:src/core/global_economic_state_effect_refinement_v1.py` lines 242-310.

Old code folded custody + liabilities, **checked R1**, then folded OPEN terminals. New code folds all four tables inside `derive_claimant_backing_view_v1` (`:373`) **before** `require_claimant_backing_v1` (`:407`) evaluates any inequality. On a state where R1 fails *and* the OPEN-terminal fold overflows, the reported reject flips:

```
=== PROBE 1: precedence divergence old(P1) vs new(S2) ===
  old: ValueError: economic refinement liabilities exceed same-domain custody backing
  new: ValueError: economic refinement claimant backing total overflows
```
Repro command: `"$PY" /tmp/opus-c2-probe/probe.py`

The change is deliberate and pinned — `precedence_terminal_overflow_before_domain` is exactly that state, and the contract doc's `reject_precedence` lists overflow first. What is missing is that no artifact says the precedence **changed**; the THV1 packet carries only `change_kind: "behavior_change"` with no statement of what behavior. CLAUDE.md declares reject precedence part of the consensus contract.

Required repair: one sentence in the THV1 `claim_scope` or the contract doc naming the change — "the composed guard now reports a fold overflow before R1 in states where the OPEN-terminal fold overflows; prior to S2 the R1 inequality was evaluated before the terminal fold." Drop "unchanged semantics" from the candidate description.

### P2-1 — Evidence packet names a terminal status that does not exist
`tests/evidence/test_hygiene/THV1-20260901-claimant-backing-guard-golden-v1.json:161` (`"SETTLED excluded"`) and `:208` (`"count SETTLED or TOMBSTONED terminals as open"`).

`TerminalObligationStatusV1` is `{OPEN, DRAINED, TOMBSTONED}` in both languages (`global_settlement_types_v1.py`; `zk/global_settlement_abi_v1/src/state.rs:339-344`). The real vectors are `ignores_drained_terminal_amount` / `ignores_tombstoned_terminal_amount`. The boundary dimension claims coverage of a status the ABI cannot represent, and one declared mutation names it.
Repro: `grep -n SETTLED tests/evidence/test_hygiene/THV1-20260901-claimant-backing-guard-golden-v1.json`
Required repair: replace both occurrences with `DRAINED`.

### P2-2 — Test name overclaims its body; it is the `killed_by` node for 5 declared mutations
`tests/core/test_global_claimant_backing_guard_v1_golden.py:89-92`:
```python
def test_mutation_killers_name_recorded_vectors_with_the_expected_polarity() -> None:
    fixture = _fixture()
    for mutation, vector_name in fixture["mutation_killers"].items():
        assert vector_name in fixture["vectors"], mutation
```
Polarity is never checked — only membership. Five of the ten `mutations` entries in the THV1 packet cite this node as `killed_by`. The Rust counterpart (`zk/global_settlement_abi_v1/tests/claimant_backing_guard_golden.rs:163-174`) is honestly named. This is the docstring-alignment defect from the repo's own quality gates.
Required repair: assert the expected outcome per killer (map `mutation_killers` to `{vector, expected_code}`), or rename to `test_mutation_killers_name_recorded_vectors`.

### P2-3 — The O-008 packet does not pin C2's headline evidence
`docs/research/ZENODEX_O008_FORMAL_CYCLE_V1.json` `source_pins` (20 entries). `"claimant_backing" in json.dumps(packet)` is **False**: the golden fixture, its renderer, and both golden test files are unpinned, so hand-editing `tests/data/global_claimant_backing_guard_v1_golden.json` produces no `current_source_drift` from `tools/check_o008_formal_cycle_v1.py`. Mitigated — `test_fixture_is_the_renderer_output` and the Rust replay both fail on a hand edit — so this is an admission-checker gap, not an unguarded surface. Note `completion_scope` did not grow either, which makes the re-pin honest but leaves the new artifact outside the admitted evidence set.
Required repair: add the fixture, renderer, and two golden test files to `source_pins` with a `claimant_backing_guard_golden` role, or state in the packet why they are deliberately out of scope.

### P3-1 — Stage 3 of the lifecycle test is vacuous
`tests/test_check_o008_formal_cycle_v1.py:797-803`. `assert report["current_applicable"] is (report["packet_admitted"] and report["current_source_drift"] == [])` restates `AdmissionOutcomeV1.current_applicable` (`tools/o008_formal_cycle_admission_v1.py:1756-1757`) verbatim; `assert report["ok"] is consistent` restates `render_report_v1`'s definition of `ok` (`:2062-2064`). Both are "return h."

It is a weakening only in the newly reachable branch — the old form would have *falsely failed* at a source commit after P, so this is a real fix badly implemented. At this HEAD stage 2 ran (`head_commit == packet_commit`), which is strictly stronger than before (it adds `current_source_drift == []`). Drift detection is covered elsewhere with synthetic fixtures (`:433`, `:444`, `:744`), which caps severity.
Required repair: assert the fail-closed direction — if any pinned blob at HEAD differs from the packet pin, then `ok is False` and that path appears in `current_source_drift`.

### P3-2 — Rust view is not validated by construction; Python's is
`zk/global_settlement_abi_v1/src/global_economic_state_effect_refinement.rs:189-207`. `BackingTotalV1 = (String, String, u128)` and `ClaimantBackingViewV1` has public fields with no constructor. Python's `__post_init__` enforces exact row type, token shape, and canonical sorted-unique keys (`:307-314`, `:325-330`). A crate consumer can hand-build a Rust view with duplicate keys — `exceeds_backing_v1` (`:278`) collects into a `BTreeMap` and silently keeps the last — or an arbitrary `schema` string, changing `view_root`. Python rejects both. Not reachable through `derive_`, so it is an API-surface asymmetry only.
Required repair: make the fields private behind a checked `ClaimantBackingViewV1::new`, or drop `schema` from the struct and inject it at serialization as Python does.

### P3-3 — Whole-packet re-pin per candidate
`THV1-...-admission-v2 -> v3`, `semantic-restage-v1 -> v2`. This round's diff is clean (identical key set, no pins added or removed, exactly 5 hashes updated, `claim_scope` prefixed with the reason), so it is honest. But every candidate touching a pinned source forces a full ~29 KB packet copy and the directory now holds five near-duplicate files. Design note, not a blocker: consider a `re-pin` delta packet referencing its predecessor by hash.

## 3. Verification record

| Command | Exit | Key output |
|---|---|---|
| `git status --porcelain \| grep -v '^??'` | 1 (empty) | 0 tracked changes; untracked symlinks `external/ESSO`, `external/mathlib4` present as expected |
| `git diff-tree --no-commit-id --name-status -r HEAD^ HEAD` | 0 | `M docs/research/ZENODEX_O008_FORMAL_CYCLE_V1.json`, `M ...V1.md` — **exactly the two packet paths** |
| `git diff --stat HEAD^^ HEAD^` | 0 | 19 files changed, +6893 / -140 |
| `"$PY" tools/check_o008_formal_cycle_v1.py --root "$PWD"` | **0** | `ok:true, packet_admitted:true, current_applicable:true, current_source_drift:[], head_commit==packet_commit==3feaa622…, subject_commit=85c45bd6…, formal_core_complete:false, all authorities NONE, value_movement_gates_closed 0/12, proof_replay NOT_RUN` |
| `"$PY" tools/render_global_claimant_backing_guard_v1_golden.py --check` | **0** | `{"ok": true, "mode": "check"}` |
| `"$PY" -m pytest -q -p no:cacheprovider` (5 files) | **0** | `264 passed in 36.64s` |
| `pytest --collect-only tests/core/test_global_claimant_backing_guard_v1_golden.py` | 0 | `34 tests collected` (claim confirmed) |
| `pytest --collect-only tests/test_accounting_source_classification_contract_v1.py` | 0 | `5 tests collected` |
| `cargo test --offline --locked --test claimant_backing_guard_golden` | **0** | `3 passed` |
| `cargo test --offline --locked --test global_economic_state_effect_refinement` | **0** | `41 passed` |
| `cargo clippy --offline --locked --all-targets -- -D warnings` | **0** | clean, no warnings |
| `"$PY" tools/check_test_hygiene_v1.py --base-ref "$(git rev-parse HEAD^)" --json` | **0** | `ok:true, changed_path_count:2, critical_path_count:0` (weak at P2 by construction — P2 touches only docs) |
| `"$PY" /tmp/opus-c2-probe/probe.py` | 0 | probes 1-6, see findings |
| `"$PY" /tmp/opus-c2-probe/escape.py` | 0 | JSON escaping of printable-ASCII tokens |

Hand-recomputed pins, `git cat-file blob HEAD^:<path> | sha256sum`:

| Path | Recomputed | Recorded in packet | Match |
|---|---|---|---|
| `src/core/global_economic_state_effect_refinement_v1.py` | `abf60faacdcd45def5163e618494a2202c9c1ab7e11bde1f44b7b29cd0057697` | identical | YES |
| `zk/global_settlement_abi_v1/src/global_economic_state_effect_refinement.rs` | `0a63e93e58f0a1b8c2f897005839d6151f02a924ed706530d604ffc7150d6c10` | identical | YES |

Both `git_blob` values (`b1e99b88…`, `11b36dae…`) also match the S2 diff index lines. Third pin cross-check: `ZENODEX_WHOLE_VALUE_MOVEMENT_FORMAL_SAFETY_CLAIM_V1.md` = `32985ee88b0b15a0b6ef1408e60ac1767f93e20eade434090011e144ecd56990`, matching the contract's `normative_source`; the cited lines 84-96 (vocabulary) and 170-173 (partition) are accurate.

Manifest bump (item 5): justified. `hash_global_v1(` occurrences in `src/**/*.py` go 215 -> 216 raw (import line included); the one new call site is `global_economic_state_effect_refinement_v1.py:354` (`view_root`). `EXPECTED_CALL_FILE_COUNT_V1` correctly stays 92 since the new call lands in an already-counted file.

THV1 v2->v3 re-pin honesty (item 6): identical key set, `source_pins` and `test_pins` paths added=[] removed=[], exactly 5 hash-only changes (`global_economic_state_effect_refinement_v1.py`, `global_economic_state_effect_refinement.rs`, `o008_formal_cycle_admission_v1.py`, `test_lean_global_claimant_custody_relation_v1.py`, `test_check_o008_formal_cycle_v1.py`) — exactly the pinned files S2 touched. `claim_scope` prefixed "Append-only re-pin after candidate C2 changed the two pinned refinement sources". Append-only confirmed: v1/v2 predecessors retained, `removed_paths` empty in all three packets, zero deletions in S2.

Adversarial questions:
- (a) Python/Rust divergence — **no**. Both encoders emit compact `,`/`:` JSON with sorted object keys (Python `canonical_json_bytes` uses `sort_keys=True`, `separators=(",",":")`; Rust `Value::Object` is a `BTreeMap`, `preserve_order` off). Tokens are restricted to `0x21..0x7E` in both (`_require_token` / `validate_token_v1`), so code-point order == byte order and JSON escaping is identical (`"`->`\"`, `\`->`\\`, `/` unescaped by both — verified empirically). `serde_json = "=1.0.148"` with `arbitrary_precision` round-trips u128 exactly, confirmed by `accepts_u128_backing_boundary` passing on both sides. Empty tables -> `[]` both sides. Duplicate rows and unicode tokens are unrepresentable in a validated state. No `SETTLED` status exists; `DRAINED`/`TOMBSTONED` filtering has two vectors.
- (b) Fold order irrelevant to which overflow code fires — **yes**. Both languages fold in the same order (Python kwarg evaluation, Rust struct-literal field order), and all three fold sites map to the single `CLAIMANT_BACKING_TOTAL_OVERFLOW`.
- (c) Reserve or balance row in the view — **no**. `derive_` reads only `state.custody`, `state.liabilities`, `state.terminal_obligations`. Probe 5: R1 still rejects with 1000-atom reserves and balances present, and `custody_by_control_domain` shows only the custody row. Enforced structurally by `test_view_has_no_reserve_or_balance_column`.
- (d) Unreachable custody overflow — **false**, see P1-1.
- (e) Reject mutates state or returns partial results — **no**. Frozen slotted dataclasses; Rust takes `&state`. Probe 4: `state_root` unchanged across a reject.
- (f) Contract-doc overclaim — the doc is clean. `ZENODEX_ACCOUNTING_SOURCE_CLASSIFICATION_CONTRACT_V1.json` scopes itself `RESEARCH_CONTRACT`, its nonclaims correctly limit the guard to "two state-visible necessary inequalities", and `reject_precedence` matches the enum. The overclaims are in the THV1 packet and the fixture, not the contract.
- (g) Chain holds — **yes**. `subject_commit` = S2 `85c45bd6…`, `subject_parent` = P1 `3b3528ba…`, `subject_tree` = `fa6a306c434990f0a16ffcce1aba29f8377d437f` = `git rev-parse HEAD^^{tree}`, `packet_commit_parent` = S2, `packet_write_set` = exactly the two packet paths. All three THV1 packets are acyclic (none pins the O-008 packet or itself). The O-008 packet -> v3 packet -> admission tool -> *path-only* reference back to v3 is well-founded, not a hash cycle.

Corrections to the brief's own claims: the fixture has **one** history (`deposit_deposit_drain_overdrain`) of five states, not four histories — the four are its `history_N_*` steps. And the brief's "SETTLED/TOMBSTONED" phrasing inherited the P2-1 error from the packet.

## 4. Nonclaims and residual risks

- I verified the guard, the fixture, the parity, the pins, and the chain. I did **not** re-run the Lean or ESSO proofs (`proof_replay.status` is `NOT_RUN`, correctly reported), did not read `GlobalClaimantCustodyRelationV1.lean`, and did not audit the 12-lane reconciliation.
- The Python golden test replays through `renderer.evaluate_v1` — the same function that produced the fixture. The Python side is self-consistent, not independent; **the differential content lives entirely in the Rust replay**, which re-derives from the recorded canonical state through its own implementation. Sound, but a Python-only mutation to `evaluate_v1` would be invisible on the Python side alone.
- `derive_claimant_backing_view_v1` is `pub` in Rust and callable on a state that never had `validate()` run — the golden test does exactly this. Python's equivalent input is validated by construction. States with non-ASCII tokens are unreachable in Python and would sort by UTF-8 bytes in Rust; no shared valid input distinguishes them, but the two entry points are not equally defended.
- The guard proves two necessary inequalities only. It cannot bind an opaque lane root to its private claimant projection, nor recover a terminal obligation's omitted control domain and principal. Both docstrings say so accurately.

## 5. User decisions — honored

All six hold. Reserves are the claimant-free term and never enter the view (verified structurally and by probe). New code uses control-domain vocabulary while every V1 wire name stays byte-stable (`v1_alias_table` maps `custody_domain -> control_domain` with `byte_stable: true` on all nine rows; no wire field renamed). O-008A remains unattested. UP-01..UP-20 appear only in `blocked_pending_policy` as named blockers — no policy value is selected anywhere in the fixture; vectors use arbitrary small integers and u128 boundaries, never a fee split or ratio. `claim_ceiling` reports every authority `NONE` and `formal_core_complete: false`.

Grade is advisory and grants no authority. Recommendation: repair P1-1 and P1-2 (both are one-line claim corrections plus one new golden vector), fix the two `SETTLED` strings and the test name, and this reaches A-.
