# Fable independent second review — candidate C9a' (P30)

| Field | Value |
|---|---|
| **Subject** | `S30 = fe5a6de6fa994704cc3387b582525650417c2ad3` ("security: repair the Opus P28 review findings", direct child of P29 `e5f8cd4231821dda1e9a44ae87c9cd5fc66076a8`) |
| **Artifact** | `P30 = 31e677feb640bf1b577bf38750c1b8b5e8e3cd92` ("docs: freeze the O-008 formal-cycle packet at C9a'", direct child of S30; diff limited to `docs/research/ZENODEX_O008_FORMAL_CYCLE_V1.{json,md}`; packet sha256 `2eb993461e232dcd6ef64ff8f4aca5c7e297645042d2f098816855acbfdf3a50`) |
| **Subject tree** | `4b37128696d8fd1f7d61d13c79605873c035bdbe` |
| **Worktree** | `/tmp/zenodex-formal-core-fable-review-c9ap` (detached at P30; `git status --short` empty before and after review; `external/ESSO` and `lean-mathlib/.lake/packages/*` symlinked) |
| **Reviewer** | Fable 5.1, fresh context, maximum effort. **Independence caveat:** the author is also a Fable 5.1 session. I share a model family with the author but no transcript, worktree, scratchpad, or notes; I did not read `/tmp/claude-1000` author state and did not touch the Opus or the C8-p11 review worktrees. This review cannot certify the author's work. ACCEPT is advisory. Authority stays NONE. The claim ceiling must not move. |
| **Date** | 2026-09-02 |
| **Toolchain (from replay)** | Python 3.12.3, Lean 4.27.0, cargo/rustc 1.87.0 (`17067e9a`), ESSO code hash `7f80c6216be85c827e8d1cc2fa08ee3107a74588` |

---

## Verdict

**Grade: B+. Recommendation: REVISE (narrow).** 0 P1, 2 P2, 5 P3.

The HIGH from the Opus P28 review is closed as claimed and I could not reopen it. Both Opus PoCs are refused at construction; every forgery I planted inside `accepted` (subclassed rows, tuple-subclass containers, int-subclass amounts, exact-class foreign custody rows, a foreign Enum lane id, a bool epoch, a journal subclass with a foreign `pre_lane_root` and a recomputed `receipt_root`, a `__class__` swap, and cross-pairing a real witness with a different real accepted) is refused by the snapshot or the journal-root equality before the producer runs. All 15 declared mutation killers kill (17 arms). Every pin across all five THV1 packets matches the worktree bytes, all 603 pinned node ids collect, the claim ceiling is byte-identical to P29, the packet rebuild with replay reproduces the committed packet byte-for-byte on a clean tree, and the registry still keeps ASSET_TRANSFER at NO_PRODUCER with no consumer of the witness in `src/`, `tools/`, or `zk/`.

It is not higher because (P2-1) three of the seven construction-closure gates the packet declares under `C9A-ROOT-BEARING-NESTED-VALUES-EXACT-TYPED-AT-CONSTRUCTION` have no behavioural evidence anywhere in the repository (reverting each to `isinstance` leaves 209 tests green), and one of them, the accepted `effects` gate, is load-bearing at construction in exactly the F1 shape; and (P2-2) under the candidate's own forgery threat model, a caller-owned entitlement row reaches a minted `VerifiedLaneAllocationFragmentV1` un-rebuilt, producing a witness that reports two different totals and cannot be hashed. Neither falsifies a packet invariant (all are scoped to `accepted`, and entitlements are a declared nonclaim), and neither contradicts the receipt. Both are small repairs.

---

## Replays (exact commands, exits, output hashes)

All commands run from `/tmp/zenodex-formal-core-fable-review-c9ap` with `PY="/home/trevormoc/Downloads/Autonomous Tau DEX/.venv/bin/python"`, `PYTHONDONTWRITEBYTECODE=1`. Lean-bearing commands (replays 2, 3, 12, 13) were run strictly serially, each started only after `pgrep -af "lake env lean" | grep -v "pgrep\|bash -c"` printed nothing (the `grep -v` excludes the reviewer's own bash wrapper, which `pgrep -f` otherwise matches on its own command text; the team lead's later correction recommends `pgrep -x lean` / `pgrep -x lake` instead). No wait was needed at any of the four starts.

| # | Command | Exit | Result | Output sha256 |
|---|---|---|---|---|
| 1 | `"$PY" tools/check_o008_formal_cycle_v1.py --root "$PWD" --packet-commit 31e677feb640bf1b577bf38750c1b8b5e8e3cd92` | 0 | `ok true`, `packet_admitted true`, `current_source_drift []`, `errors []`, `proof_replay.status NOT_RUN`, stderr empty | `e6c51a52090cb94cf4e2d50863f7d813d52541f3827727c586a9f386134ba313` |
| 2 | same `--replay --esso-python /usr/bin/python3 --esso-pythonpath /home/trevormoc/Downloads/ESSO` | 0 | `proof_replay.status EXECUTED_PASS`, 29 runs, 0 non-pass (lean_version … rust_producer_gate), stderr empty, 5m01s | `b83e98c8a4179753b284c0a5f89d6d11dc623f227f6347ebe97847560edd7cf5` |
| 3 | `"$PY" tools/build_o008_formal_cycle_v1.py --root "$PWD" --subject-commit fe5a6de6f… --created-date 2026-09-02 --check --replay --esso-python /usr/bin/python3 --esso-pythonpath /home/trevormoc/Downloads/ESSO --output-json docs/research/ZENODEX_O008_FORMAL_CYCLE_V1.json --output-md docs/research/ZENODEX_O008_FORMAL_CYCLE_V1.md` | 0 | `{"drift":[],"mode":"check","ok":true,...}`; **`git status --short` empty afterwards; packet sha unchanged `2eb99346…`** (byte-for-byte reproducible), 3m54s | `742428b6ba5275963c7fb67b2a007b17bf6c6d46623d6b1a8e013316b9f5ee97` |
| 4 | `cargo fmt --all -- --check` (zk/global_settlement_abi_v1, `CARGO_TARGET_DIR=/tmp/zenodex-fable-review-c9ap-cargo CARGO_INCREMENTAL=0`) | 0 | clean | (combined) `e887d7f8cffc190e6c4d92112e548d8e93d5d7bd3bae3e4181757c976bf44bf8` |
| 5 | `cargo clippy --locked --all-targets -- -D warnings` | 0 | clean | same file |
| 6 | `cargo test --locked` | 0 | **527 passed, 0 failed** across 54 test binaries | same file |
| 7 | `pytest tests/core/test_asset_transfer_receipt_admission_v1.py -q` | 0 | **20 passed** | `bd35917cfd345444b36192831380ea050c36d273611fc64ebbc30fcec482e584` |
| 8 | `pytest tests/core/test_global_accounting_lane_producers_v1.py tests/core/test_asset_transfer_lane_module_v1.py tests/core/test_global_settlement_abi_v1.py tests/core/test_global_settlement_canonical_admission_v1.py tests/test_check_global_settlement_canonical_manifest_v1.py -q` | 0 | **126 passed** | `176bc7ffb4a64223ebdaa3eaad12c2eb598930ac904c804ec961e3fbb20eff0c` |
| 9 | `pytest tests/test_check_o008_formal_cycle_v1.py -q` | 0 | **389 passed** (4m40s) | `ee23ba20ceffd2e7d9cc9adb64b132f055c2d880a04095961f32ae505fab6f8f` |
| 10 | `"$PY" tools/check_test_hygiene_v1.py --json` | 0 | `ok true`, 153 packets, stderr empty | `b7095270b1ef41ece8fe636605534f6bf23b168b83d8dcf3f76c55840f46de7d` |
| 11 | `"$PY" tools/check_test_hygiene_v1.py --base-ref e5f8cd4231821dda1e9a44ae87c9cd5fc66076a8 --json` | 0 | `ok true`, 16 changed paths, 9/9 critical paths covered, 460 node ids, selected: formal-cycle-admission-v26, canonical-exact-admission-v2, receipt-admission-v2 | `536de3007640c5652955c0f8b24562c386277eac36d9861adbc747120d88956b` |
| 12 | `pytest tests/formal/test_lean_global_accounting_allocation_certificate_v1.py -q` (serial) | 0 | 6 passed (2m31s) | `a2155506cccdba832e679cdd869cfcd957d19b51770309211e95c8bd5d3df5fb` |
| 13 | `pytest tests/formal/test_lean_global_claimant_custody_relation_v1.py -q` (serial) | 0 | 6 passed | `c0e4a88eb02346cbb411b1612540b08bca75217e31aee5292fda39ab958e503a` |
| 14 | `PYTHONPATH=. "$PY" /tmp/zenodex-opus-c9a-poc.py` | 1 | `TypeError: asset lane port post-state must be the exact typed value` at `asset_lane_projection_v1.py:213` (refused at `SpoofedPort(...)` construction) | — |
| 15 | `PYTHONPATH=. "$PY" /tmp/zenodex-opus-c9a-poc2.py` | 1 | `TypeError: asset transfer lane module private port must be the exact typed value` at `asset_transfer_lane_module_v1.py:217` (refused at `AssetTransferLaneModuleAcceptedV1(...)` construction) | — |

`tests/core/test_zusd_liquidation_partition.py` excluded (pre-existing unrelated collection error). `--base-ref 42ccb6624` not re-run (known red on the resource-bounds test, Opus P29 NEW-25, out of scope). The review cargo target dir was deleted after the gates; the replay shell used and cleaned its own temp target; no in-tree `target/` exists.

### Envelope and chain

* S30 is the direct child of P29; P30 is the direct child of S30 (`git rev-parse` verified). P30's complete diff is the two packet files (2 files, +45/−45). The branch carries one later artifact-only receipt commit (`2e6894f33`, the Opus C8-p11 receipt); this review is of P30 exactly.
* S30 touches 14 files: five `src/core` modules, one test, one count test, five THV1 packets, the canonical-manifest checker digest, and doc comments in the Rust producer (the `.rs` diff is comment-only; `cargo test` confirms no behavioural change).

### Packet integrity

* **Formal-cycle packet P29→P30**: top-level key set identical; changed keys exactly `subject_commit`, `subject_parent`, `subject_tree`, `packet_commit_parent`, `source_pins` (only the Python and Rust producer pins moved, `26be354b→0ad3e2b1`, `4c92915c→99c2c136`, matching the docstring-only diffs), and `hygiene_selection` (same 44 paths; attribution moved from admission-v25/receipt-admission-v1 to v26/v2, and `global_settlement_types_v1.py` to canonical-exact-admission-v2). **`claim_ceiling` is byte-identical to P29**; `nonclaims`, `completion_scope`, `lean_evidence`, `esso_evidence`, `v1_information_loss` unchanged. The Markdown companion diff mirrors the JSON exactly.
* **THV1 pins**: receipt-admission-v2 (6 source + 1 test pin), formal-cycle-admission-v26 (40), certificate-v13 (26), backing-guard-v20 (12), canonical-exact-admission-v2 (5): **all 89 pins match the worktree bytes**; `removed_paths` empty everywhere. **All 603 pinned node ids collect** (`pytest --collect-only` over the 13 pinned test files; 0 missing).
* Packet bumps are honest: v1→v2 receipt-admission adds the three F1/F3/F4 invariants, two failure modes, nine mutations, two nonclaims, and re-pins the five touched sources; v25→v26 and v19→v20 are pure re-pins of the producer docstrings / manifest digest; v12→v13 adds one mutation and the admission test file; canonical-exact v1→v2 records the 104+35 count.
* Incidental (pre-existing, not a C9a' defect): certificate-v12 at P29 pinned `src/core/managed_asset_lifecycle_types_v1.py` at `d6867627…` while the P29 file was `f85ffc59…` (changed by `a18699202`). v12 was not in the P29 hygiene selection, so nothing flagged it; v13 re-pins it correctly.

### Mutation killers (applied, named test run, restored; tree clean afterwards)

| # | Declared mutation | Applied as | Named killer | Result |
|---|---|---|---|---|
| M1 | admit from caller-forged accepted (foreign journal) | delete the journal-root block (`admission:195-201`) | `test_foreign_accepted_value_is_rejected_at_the_journal_root` | KILLED |
| M2 | construct witness outside verifier | token check → `pass` (`admission:124-125`) | `test_witness_token_is_verifier_only` | KILLED |
| M3 | non-witness through the type gate | delete `admission:181-182` | `test_admission_requires_the_module_witness_type` | KILLED |
| M4 | subclassed port at construction | `lane_module:216` → `isinstance` | `test_subclassed_private_port_with_a_spoofed_root_is_refused_at_construction` | KILLED |
| M5 | drop the snapshot | `owned = accepted` (`admission:185`) | `test_planted_subclass_port_is_refused_by_the_admission_snapshot` | KILLED |
| M6 | projection gates → isinstance | `projection:210-213` | `test_subclassed_projection_is_refused_by_the_port_gate` | KILLED |
| M7 | journal gate → isinstance | `types_v1:226` | `test_subclassed_journal_with_a_spoofed_journal_root_is_refused` | KILLED — **by `ValueError: wrong post-state root`, not by the gate** (see P3-3) |
| M8 | skip re-validation | `owned = accepted` | `test_validation_bypassed_accepted_is_refused_by_the_snapshot` | KILLED |
| M9a/b/c | delete kind / statement / occurrence check | each block deleted | `test_defensive_witness_checks_have_forgery_witnesses[kind/statement_root/occurrence]` | KILLED ×3 (each arm fails only its own param) |
| M10 | delete binding-root check | `admission:221-227` | `test_binding_root_drift_is_producer_drift_protection` | KILLED |
| M11 | foreign controlled rows | `producer:341` owner → `"attacker"` | `test_admitted_controlled_rows_are_the_receipt_proved_custody_rows` | KILLED |
| M12 | swallow/transform producer reject | `admission:219-220` returns a witness reject | `test_producer_rejects_pass_through_unchanged` | KILLED |
| M13 | grow reject family | add `WITNESS_EXTRA` | `test_witness_reject_family_is_closed_and_ordered` | KILLED |
| M14 | mutate input on reject | `object.__setattr__(witness, "_fields", …)` before the journal-root reject | `test_witness_reject_is_a_no_op_value` | KILLED |
| M15 | change claimant coverage semantics | fold key gains `claimant` (`producer:324`) | `test_claimant_identity_is_not_bound_by_the_receipt_until_c9b` | KILLED |

Extra mutations of my own (see P2-1): **X1** `types_v1:220` post_state gate → isinstance: **SURVIVED** (20/20 admission tests, then 209/209 across 7 suites). **X2** `types_v1:222` effects gate → isinstance: **SURVIVED** (20, 209). **X3** `projection:165` source gate → isinstance: **SURVIVED** (20, 209). **X4** (proposed fix) `producer:242` `isinstance(…, tuple)` → `type(…) is not tuple`: neutral, 20 passed.

---

## The candidate's claims, adversarially

### F1 — the exact-typed snapshot as check (0) — **holds; the class is closed for `accepted`**

`verify_asset_transfer_fragment_receipt_v1` (`src/core/asset_transfer_receipt_admission_v1.py:181-186`) gates `witness` and `lane_root` by exact type and then calls `_snapshot_asset_transfer_lane_module_accepted_v1` (`src/core/asset_transfer_lane_module_v1.py:250-273`, pre-existing, previously used only by the mint's recompute). I traced the rebuild field by field: exact class on `accepted`, `post_state`, `effects`, `module_journal`, `private_port`; exact `str` statement root; exact scalars on the journal (`_require_exact_dataclass_scalars_v1`, `global_economic_refinement_snapshot_v1.py:33-59`, admitting only `str`/`int`/`bool` and an Enum for `lane_id`); every row tuple re-checked as exact `tuple` with exact-class rows and exact-primitive scalars and rebuilt with `replace` (`:74-83`); the port rebuilt with five exact strings and two rebuilt projections (`asset_lane_projection_v1.py:268-290`); and the rebuilt `AssetTransferLaneModuleAcceptedV1.__post_init__` re-runs every cross-equality, so `private_port_root` is compared against a `port_root` recomputed from the rebuilt content. The journal root therefore binds, through the rebuilt value, `statement_root` (via `receipt_root`), `post_state` (via `post_lane_root`), `effects` (via `effect_plan_root`), the journal fields themselves, and both projections including custody (via `private_port_root`). The producer reads custody only from `owned.private_port.post_state.custody`.

Probes (all refused; `probes_out.txt`): planted str-subclass statement root → `TypeError` (snapshot); planted `EconomicAmountV1` subclass custody row with `__eq__` override → `TypeError`; planted tuple-subclass custody container → `TypeError`; planted **exact-class** foreign custody row → `ValueError: private-port root mismatch` (root recomputed); planted int-subclass amount inside a custody row → `TypeError`; planted foreign Enum `lane_id` → `TypeError` (journal `validate`); planted `bool` epoch → `ValueError`; journal subclass overriding `journal_root` with foreign `pre_lane_root` and a **recomputed** `receipt_root` (the field the existing cross-checks do not pin) → `TypeError` at construction and at the snapshot; `__class__` swap of a spoofed port to the exact class → refused by CPython (slots layout differs); real witness A + real accepted B → `WITNESS_JOURNAL_ROOT_DRIFT`. `_canonical_value` (`global_settlement_types_v1.py:167-201`) independently refuses scalar/sequence/dataclass subclasses, so nothing subclassed can even be hashed.

**Raising at the type boundary**: consistent with the path's stated contract. The producer raises `TypeError` on non-exact arguments (`producer:236-245`), the mint raises `ValueError` on recompute mismatch, and the admission docstring says so explicitly (`admission:176-178`). The one design tension is recorded as P3-4.

### F2 — nonclaim pin — **honest**

`test_claimant_identity_is_not_bound_by_the_receipt_until_c9b` (`test:424-444`) admits both `custodian` and `attacker` for the same `(USD, vault, 100)` total and asserts the controlled rows stay the receipt-proved custodian row. The nonclaim appears in the THV1 packet, the module docstring (`admission:27-30`), both producer docstrings, and the Rust doc comment. M15 confirms the pin inverts when coverage semantics change.

### F3/F4 — defensive-code witnesses and check (4) relabel — **hold**

Each of `WITNESS_KIND_DRIFT`, `WITNESS_STATEMENT_ROOT_DRIFT`, `WITNESS_OCCURRENCE_DRIFT` now has a forged-witness arm (M9a/b/c each kill exactly their own arm) and the docstrings say a forged witness is the only route (accurate: the mint derives every witness scalar from the recomputed journal, `lane_module_receipt_verification_v1.py:374-410`). `WITNESS_BINDING_ROOT_DRIFT` is labelled producer-drift protection with a monkeypatched-producer witness (M10 kills). The docstring's "the witness carries no receipt root" is correct (`VerifiedLaneModuleTransitionV1` exposes `receipt_digest`, not a receipt root). Pass-through is exercised for three producer codes (`LANE_DISABLED`, `MODULE_RELEASE_DRIFT`, `JOURNAL_ROOT_DRIFT`).

### F5 — docstrings and Rust gap — **hold**

Both producer docstrings and the Rust doc comment are present tense and the Rust twin gap is a declared nonclaim and open gap. Rust `cargo test` 527 passed with the comment-only diff.

### Count-test repair — **honest**

`GLOBAL_SETTLEMENT_CANONICAL_SERIALIZER_TYPES_V1` has 104 entries and the enum tuple 35 at P30 (imported directly). The P29 version of the test, run against the unchanged manifest, fails with `assert 104 == 92`. The manifest last grew at `31671bab8` (2026-09-01 22:33, "add the receipt-backed ASSET_TRANSFER fragment producer (C8, wave B)"), consistent with "red since C8 S17 grew the manifest (2026-09-01)". Membership and the closure digest remain owned by `tools/check_global_settlement_canonical_manifest_v1.py` (re-pinned; its test passes in replay 8).

### Containment — **holds**

`LANE_ALLOCATION_PRODUCER_REGISTRY_V1[ASSET_TRANSFER] = (NO_PRODUCER, …)` unchanged (`certificate:99`); `_check_lane_bindings` rejects a RECEIPT_BACKED asset-transfer fragment at `PRODUCER_KIND_DRIFT` and, failing that, `BINDING_ROOT_DRIFT` (`certificate:634-655`). `grep` for the admission module, the witness class, or the admission function over `src/`, `tools/`, `zk/` hits only docstrings in the two producers.

---

## Findings

### P2-1 — Three declared construction-closure gates have no behavioural evidence; the `effects` gate is load-bearing in the F1 shape

**Where.** `src/core/asset_transfer_types_v1.py:220` (`post_state` exact gate), `:222` (`effects` exact gate); `src/core/asset_lane_projection_v1.py:165` and `:183` (projection-source exact gates). All four were introduced by S30 under the packet invariant `C9A-ROOT-BEARING-NESTED-VALUES-EXACT-TYPED-AT-CONSTRUCTION` and the claim_scope sentence "the same class is closed at construction by exact-type gates on the private port, its projections, the projection sources, and the accepted state, effects, and journal".

**Evidence.** Reverting each of X1/X2/X3 to `isinstance` leaves the 20 admission tests and 209 tests across `test_asset_transfer_lane_module_v1`, `test_global_settlement_abi_v1`, `test_global_accounting_lane_producers_v1`, `test_global_accounting_allocation_certificate_v1_golden`, `test_asset_transfer_receipt_admission_v1`, `test_asset_transfer_module_v1`, `test_asset_transfer_module_v2` green. The certificate-v13 packet's only F1 mutation ("loosen a root-bearing nested-value gate on the accepted path back to isinstance") names the private-port test as killer, so it evidences the port gate alone. Only the port, projection (via the port), and journal gates carry killers.

**Why it matters.** With X2 reverted, an ordinary `GlobalEconomicEffectPlanV1` subclass whose `effect_plan_root` property returns the genuine root over foreign rows constructs both `AssetTransferAcceptedV1` and `AssetTransferLaneModuleAcceptedV1` (`x2_demo.py`: every cross-equality — journal `effect_plan_root`, port `module_effect_plan_root`, recomputed `receipt_root` — reads the spoofed root and passes). At P30 the exact gate refuses it with `TypeError`, and the admission snapshot refuses the planted variant regardless, so the **admission path is protected either way**; but the declared construction closure is asserted, not evidenced, for three of its seven gates, which is the same evidence gap Opus F3 named for reject codes.

**Reproduction.** In the worktree: change `types_v1:222` to `if not isinstance(self.effects, GlobalEconomicEffectPlanV1):`, run `PYTHONPATH=. "$PY" <scratch>/x2_demo.py` → both constructors print `CONSTRUCTED`; run the seven suites → 209 passed. Restore with `git checkout -- src/core/asset_transfer_types_v1.py`.

**Minimal fix.** One parametrized test in `tests/core/test_asset_transfer_receipt_admission_v1.py` (or the types test) that constructs (a) an effects subclass overriding `effect_plan_root`, (b) a state subclass overriding `state_root`, (c) a state subclass passed to `project_asset_transfer_state_v1`, and asserts `TypeError` with `match="exact typed value"` at `AssetTransferAcceptedV1` / `AssetTransferLaneModuleAcceptedV1` / the projector; then add one mutation row per gate to receipt-admission-v3 and certificate-v14 naming that test. ~40 lines of test, no source change.

### P2-2 — A caller-owned entitlement row reaches the minted witness un-rebuilt (poison witness under the candidate's own forgery model)

**Where.** `src/core/asset_transfer_receipt_admission_v1.py:216-217` passes `claimant_entitlements` straight to the producer; `src/core/global_accounting_lane_producers_v1.py:242-245` checks only the container (`isinstance(…, tuple)`) and row class; `:323-330` folds `entitlement.amount_atoms` and `:356` stores the caller's rows in the fragment; `LaneAllocationFragmentV1.__post_init__` (`certificate:373-390`) re-checks row class and order, never row scalars.

**Evidence** (`probes_out.txt`, P-B). A `ClaimantEntitlementRowV1` with `amount_atoms` planted to an `int` subclass whose `__radd__`/`__add__` return 100 but whose value is 10^30 (planted with the candidate's own `_plant` helper, i.e. `object.__setattr__`) passes the coverage fold and **mints a `VerifiedLaneAllocationFragmentV1`** whose row reports `int(amount_atoms) = 1000000000000000000000000000000`, `sum(...) = 100`, and whose `fragment.fragment_root` raises `TypeError: canonical scalar subclasses are unsupported`. The receipt-proved controlled rows are untouched (the receipt is not contradicted), but the authority-bearing value is internally inconsistent and unhashable.

**Why P2 and not P3.** The candidate defines its threat model to include `object.__new__`/`object.__setattr__` forgery (that is what "validation-bypassed object" means in `test_validation_bypassed_accepted_is_refused_by_the_snapshot` and `test_planted_subclass_port_is_refused_by_the_admission_snapshot`) and states as the module's boundary principle that "the snapshot refuses … every scalar that is not an exact primitive" (`admission:20-22`). That holds for `accepted` only; the residual for the other caller inputs is neither closed nor declared. Not a falsification: no packet invariant names entitlements, and the nonclaim already says the rows are caller-chosen — but the nonclaim's own residual claim ("covered per `(asset, control_domain)` total") is what the forged row defeats.

**Reproduction.** `PYTHONPATH=. "$PY" <scratch>/probes.py` from the worktree; see the `P-B` line.

**Minimal fix** (~6 lines). In the admission, before the producer call: `rows = _snapshot_dataclass_tuple_v1(claimant_entitlements, ClaimantEntitlementRowV1, "claimant entitlements")` and pass `rows`; in the producer replace `isinstance(claimant_entitlements, tuple)` with `type(claimant_entitlements) is not tuple` (X4 verified neutral). Add a negative test that a planted int-subclass amount raises `TypeError` at the admission boundary, and a mutation row. Alternatively, declare the residual explicitly in the packet nonclaims — but the snapshot is cheaper than the sentence.

### P3-1 — A forged prior fragment bypasses chain continuity (`STALE_JOURNAL`)

**Where.** `admission:216-217` passes `prior_fragment` un-rebuilt; `producer:283-286` compares `journal.pre_lane_root != prior_fragment.lane_state_root`.

**Evidence** (P-D). A `LaneAllocationFragmentV1` prior with `lane_state_root` planted to a `str` subclass whose `__eq__`/`__ne__` lie is admitted and a witness is minted although `journal.pre_lane_root` (`0xd57148…`) differs from the prior's value (`0x7777…`); the honest mismatch (P-D') rejects `STALE_JOURNAL "pre root"`. The witness carries no prior root, so its content equals an honest admission's; only the producer's continuity check is lost. Same threat model and same fix family as P2-2 (snapshot the prior's scalars, or `replace(prior_fragment)` after `_require_exact_dataclass_scalars_v1`), or declare the residual.

### P3-2 — `isinstance(claimant_entitlements, tuple)` admits a tuple subclass through the public API and makes `FRAGMENT_INVALID` reachable

**Where.** `producer:242`; producer docstring `:217-220` calls `FRAGMENT_INVALID` "unreachable in intent".

**Evidence** (P-A, P-A'). A plain `tuple` subclass carrying honest rows (no forgery) passes the producer's gate, every check, and is refused only by `_require_tuple` inside the fragment constructor, surfacing as the `FRAGMENT_INVALID` reject value. Fail-closed as a value, so no security impact, but it is the one remaining `isinstance` gate on the C9a input surface that the F1 audit did not convert, and it contradicts the docstring. A stateful `__iter__` can also make the fold and the constructor see different rows (still rejected). **Fix:** `type(claimant_entitlements) is not tuple` → `TypeError` (X4: 20 passed), and drop "unreachable in intent" or keep it true.

### P3-3 — The spoofed-journal regression test varies a cross-checked field, so the journal type gate is not what refuses it

**Where.** `test:275-305`, `fields["post_lane_root"] = FOREIGN_ROOT`.

**Evidence.** Under M7 (journal gate → `isinstance`) the test is killed by `ValueError: asset transfer journal has the wrong post-state root` from `types_v1:232`, not by the type gate — `post_lane_root` was never admissible with or without the gate. The load-bearing case is a journal field no cross-equality pins (`pre_lane_root`, `chain_id`, `deployment_root`, `profile_root`, `writer_epoch`) combined with a recomputed `receipt_root`; my P-L probe shows P30 refuses exactly that variant by the exact gate (`TypeError`) at construction and at the snapshot. **Fix:** in the test set `pre_lane_root = FOREIGN_ROOT`, recompute `receipt_root` with `_receipt_root(...)`, and keep the `TypeError` assertion; the docstring's story then matches the refusing check.

### P3-4 — Check (0) raises `ValueError` where the Rust producer returns `ACCEPTED_INVALID`; Python's `ACCEPTED_INVALID` stays unreachable

**Where.** `admission:185` (snapshot raises); `producer:120,195-199` (`ACCEPTED_INVALID` declared, documented as check 0, no code path emits it; P-O confirms a planted foreign-custody accepted passes straight through the producer when called directly, which its nonclaim permits); Rust `asset_transfer_lane_module.rs` validates and returns `ACCEPTED_INVALID` as a value.

**Assessment.** Raising for *type-boundary* failures is consistent with the path (producer and mint raise). But a **semantically** inconsistent exact-typed value (P-H: exact classes, foreign custody, `ValueError: private-port root mismatch`) is precisely the input class Rust names with a stable reject code, and the reject-code family is part of the consensus contract. This is covered in spirit by the declared "no Rust twin" gap but not named. **Recommendation** for C9b, decide one of: map snapshot `ValueError` (not `TypeError`) to `ReceiptBackedProducerRejectedV1(ACCEPTED_INVALID, …)` in the admission so the eleven-code family is reachable and twins agree; or add the divergence to the nonclaims.

### P3-5 (INFO) — Commit message claim about the V2 twin is inaccurate (safe direction)

The S30 commit message and the review brief say "the V2 types twin (asset_transfer_types_v2) keeps isinstance". `src/core/asset_transfer_types_v2.py` contains no `isinstance` at all; it already uses `type(...) is not` gates throughout (lines 73-573). Harmless, but a factual statement in a security commit message should be true. Fix: drop or correct the sentence in the next packet's claim_scope.

### Observations (no finding)

* `AssetLaneCompositionAcceptedV1` / `AssetLaneCompositionRejectedV1` (`projection:375-401`) and `AssetTransferRejectedV1` (`types_v1:250,256`) still use `isinstance`; they are on the coordinator/reject paths, not the C9a accepted path, and are out of this candidate's declared scope.
* Under forgery of `lane_root` scalars the reject constructors raise (`TypeError: … committed lane root must be a string`) rather than returning a value (P-C, P-P); fail-closed, and outside the threat the packet declares for `lane_root`.
* The pre-existing stale certificate-v12 pin (see Packet integrity) is fixed incidentally by v13.

---

## What I could not falsify

* No `VerifiedLaneAllocationFragmentV1` whose **controlled rows** contradict the receipt, through public constructors, subclassing of any nested value, planting inside `accepted`, `__class__` reassignment, or cross-pairing real witnesses and real accepted values.
* No route to the witness through `copy`/`pickle`/foreign token (unchanged from Opus P28, re-confirmed by M2/M3).
* No drift in the claim ceiling, the producer registry, the formal-cycle packet's nonclaims, or any pinned source; the packet reproduces byte-for-byte under replay on a clean tree.
* No behavioural change in the Rust crate (comment-only diff; 527 tests pass).

## Recommendation

**REVISE (narrow), grade B+.** Repairs: P2-1 (one parametrized gate test + mutation rows), P2-2/P3-1/P3-2 (snapshot `claimant_entitlements` and `prior_fragment`, exact-tuple gate, one negative test), P3-3 (vary `pre_lane_root` in the journal test), P3-4 (decide the `ACCEPTED_INVALID` mapping or declare it), P3-5 (fix the sentence). Then re-cut S/P and re-pin receipt-admission-v3 / certificate-v14. Authority remains NONE; the claim ceiling did not move and must not move on this candidate.

## Artifacts

Scratch outputs (session-local): `probes.py`, `probes_out.txt`, `mutations_out.txt`, `mutations_x_out.txt`, `x2_demo.py`, and all replay logs under `/tmp/claude-1000/-home-trevormoc-Downloads-Autonomous-Tau-DEX/e5cec494-0621-4e74-acda-a1f19abfcad5/scratchpad/`. Worktree left clean at P30; `/tmp/zenodex-fable-review-c9ap-cargo` deleted.
