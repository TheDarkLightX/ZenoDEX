# Opus review receipt: candidate C1'''' at P = 7896065ef1daf9f0d027da2c3489acb475d8a6e4

Reviewer: Opus 5 (`Agent(model: "opus")`, read-only, detached worktree `/tmp/zenodex-formal-core-review-p-7896065ef`; adversarial copies under `/tmp/opus-c1qprime-*`, deleted by the reviewer).
Date: 2026-09-01. Subject: P = 7896065ef1daf9f0d027da2c3489acb475d8a6e4 (tree e5b05f49f252dae65400c9de0f3085c73795f7be), S = 2bce28475075e57fb972a0a1d0790e736903c4db, parent R8 = c6760e9c1ddb8d3945e79beae1c08ad4c0606fe2.
Verdict: Grade C, REVISE. All nine Codex C1'' and Opus C1''' findings are recorded CLOSED by re-mounting; two new P1s (a second macro_rules definition shadows the pinned container deserialiser macro; a notation command inside an elided Lean proof region rewrites a pinned statement's meaning) and two P2s (static_closure/statement_binding wording; golden-v4 mutation[3] attribution) are repaired by candidate C1''''' (the next source commit after this receipt, cut on top of C4a S9/P9 = b3a816a7b4c963e523e99eaa1705589f1a82f207/c9131d74d9dca10ae16dd56162ba7c769331ad24). Codex's parallel audit of the same commit terminated on its usage limit before producing a report (log in the session scratchpad; credit returns 2026-09-06) and is not a receipt. The grade is advisory and grants no authority.

Verbatim report follows (sha256 of the reviewer's file: 32d49843f913420731ad0efd71c71f15836f3b363b5c1bc51a5b26f5783e5b87).

---

# Opus review receipt: candidate C1'''' at P8 = 7896065ef1daf9f0d027da2c3489acb475d8a6e4

- **Reviewer**: Opus 5, independent reviewer. Read-only, detached worktree `/tmp/zenodex-formal-core-review-p-7896065ef`.
- **Date**: 2026-09-01. Branch `codex/formal-core-fable-20260901`.
- **P8 (packet commit)**: `7896065ef1daf9f0d027da2c3489acb475d8a6e4`.
- **S8 (source commit)**: `2bce28475075e57fb972a0a1d0790e736903c4db`, tree `0facc820f9d9fb6b80a11d71cf0240c3adf76538`, parent `c6760e9c1ddb8d3945e79beae1c08ad4c0606fe2` (the Opus C1''' receipt).
- **This review is advisory and grants no authority.**

Worktree left untouched: `git status --porcelain` empty (tracked and untracked) before and after; HEAD still `7896065ef`; no `target/` anywhere under the worktree or the primary repository. Nothing written under `/dev/shm`. Adversarial work lives in `/tmp/opus-c1qprime-exp` (in-process probe harness `harness.py`, `repin.py`, `p1.py`…`p7.py`, `LeanWeakened.lean`), `/tmp/opus-c1qprime-cargo` (standalone crate copy), `/tmp/opus-c1qprime-mutrepo` (mutation sandbox, deleted), `/tmp/opus-c1qprime-work` (logs). `CARGO_TARGET_DIR=/tmp/opus-c1qprime-cargo-target` deleted at the end.

---

## 1. Grade: **C — REVISE**

**This is a genuinely strong repair round, and I verified every closure by re-mounting it rather than reading it.** All nine findings carried from the two prior receipts are **CLOSED**, including the two exact survivor chains Codex left mounted on disk. Codex's `S' = 6c8499030` (imported widening deserialiser behind a block-local macro decoy, no-op gate bodies) is rejected at three independent layers, and the same class re-cut fresh against S8 is rejected at four. Codex's `S'' = d40c9ac30` (`noUnclassified_premise_is_necessary : True`) is `LEAN_STATEMENT_DRIFT`, and so is the same mutation re-cut fresh. Every Opus C1''' vehicle is dead: all seven attribute spellings before a `use` (including two the previous reviewer did not try, `#[allow(nested([deep]))]` and `#[a([b([c])])]`), the crate-root `mod bounded_vec` rebinding in four spellings plus `#[path]` and inline-module variants, all nine Python dynamic-store spellings, `serde::de::Deserialize`, the Rust gate's string literals, and the `bounded_vec.rs` `#[cfg(test)]` module. Every prescribed command passes: checker exit 0 `NOT_RUN`; checker `--replay` `EXECUTED_PASS` with **17/17** runs at exit 0; builder `--check --replay` `{"drift":[],"ok":true}`; **373 tests passed** (299 + 6 + 20 + 13 + 35, exactly as predicted); hygiene checker `ok:true`; ruff and `mypy --strict` clean. All 28 packet `source_pins`, all 26 v9 pins and all 12 golden-v4 pins equal the S8 blob bytes; all 87 `killed_by` ids resolve against 362 collected tests. I hand-recomputed the admission core pin, the Lean file pin, the definition-surface hash, `RUST_GATE_NORMALIZED_SHA256_V1`, `BOUNDED_VEC_FILE_NORMALIZED_SHA256_V1` and one load-bearing theorem-statement hash from S8 blobs; all six match.

**The grade is held at C because the two headline claims of the commit — that the compiled container decoder is bound to the pinned macro, and that theorem statements are bound to their meaning — are both falsified end to end, each by a new route I mounted completely.**

1. **Rust (P1-1).** `rust_container_deserializer_closure_v1` validates the body of the **first** `macro_rules! bounded_state_vec_deserializer_v1` (`re.search`). Rust's textual macro scoping means a **second** definition of the same name shadows it for every later invocation. Adding one such definition immediately before the terminal invocation — plus a plain `fn` in the same file, which nothing forbids — is **ACCEPTED** by a full attacker re-pin, compiles, keeps the exact recorded replay counts **7 / 41 / 3 / 9**, survives `cargo clippy --all-targets -- -D warnings`, and makes the compiled `GlobalEconomicStateV1` accept a terminal row carrying `zz_shadow` that the pristine crate rejects with ``unknown field `zz_shadow` ``. One file changed, 34 lines.

2. **Lean (P1-2).** `lean_definition_surface_v1` elides everything between a theorem's statement end and the next **column-zero item whose keyword is in `_LEAN_ITEM_START_RE`**. That list omits `notation`, `macro_rules`, `syntax`, `local`/`scoped notation`, `export`, `partial def` and `initialize`. A `notation` placed in an elided proof region re-binds a token that a **later, byte-identical statement** uses. I mounted this on the real file: `necessaryRelation_nonvacuous` — the pinned non-vacuity witness — now proves `True`, while the definition-surface hash is **`cd1e010a3f82e159…`, identical to the pinned constant**, and **all 25 theorem statement hashes are unchanged**. The file compiles under `lake env lean -DwarningAsError=true` with **exit 0 and empty output**, exactly what `lean_direct_check` requires, and the projection is **ACCEPTED**. This defeats the centrepiece repair of this round on its own terms.

Both routes assume the attacker re-pins (the correct threat model here, and the one the task sets); my harness performs full re-pinning of the Lean gate table and every hygiene packet to a fixpoint. The packet's `static_closure` sentence again carries a clause the routes falsify, and `lean_evidence.statement_binding` overstates what elision leaves free (**P2-1**). One golden-v4 `killed_by` row is still mis-attributed (**P2-2**).

### Per-finding disposition

**Codex C1'' (grade D)**

| Finding | Status | Evidence |
|---|---|---|
| **P1 Rust projection closure / gate non-vacuity** | **CLOSED for the named class; class OPEN by a new route** | Verbatim `S'` blobs → `RUST_STATE_IMPORT_DRIFT`, `RUST_CRATE_MODULE_SET_DRIFT`, `RUST_GATE_CONTENT_DRIFT`. Fresh re-cuts R1–R5 → `RUST_CONTAINER_DESERIALIZER_DRIFT` (0 item-position invocations), `RUST_STATE_IMPORT_DRIFT`, `RUST_CRATE_MODULE_SET_DRIFT`, `RUST_GATE_CONTENT_DRIFT`. New route: **P1-1** below. |
| **P1 Lean statements self-pinned** | **CLOSED for the named class; class OPEN by a new route** | Verbatim `S''` and a fresh `True` re-cut both → `LEAN_STATEMENT_DRIFT`. `LEAN_STATEMENT_SHA256_V1` (25 entries) and `LEAN_DEFINITION_SURFACE_SHA256_V1` are embedded in the reviewed core. New route: **P1-2** below. |
| **P2 false `killed_by` rows** | **PARTIALLY CLOSED** | golden-v4 mutation[2] now names the behavioural vector and I confirmed it: under the reserve mutation `…[excludes_reserves_from_backing]` **fails** while the old field-name attribution `test_view_has_no_reserve_or_balance_column` **passes**. Four further declared mutations executed; three killed by the named node. mutation[3] is still mis-attributed — **P2-2**. |
| **P2 cargo replay inherits host configuration** | **CLOSED** | `_replay_env` builds from a fixed dict, never `os.environ`. Empty `HOME`/`TMPDIR`, registry-only `CARGO_HOME` with no config, rebuilt `PATH`. `rust_compiler_version` records `rustc -vV` release/commit-hash/host, `_validate_toolchain` compares it on fresh replay. `test_replay_environment_is_sanitized` and `[rustc_vv_nightly]` collect and pass. |

**Opus C1''' (grade C)**

| Finding | Status | Evidence |
|---|---|---|
| **P1-1 attribute-prefixed `use`** | **CLOSED** | `_strip_rust_attributes_v1` blanks attributes before the scan and `]` was added to the boundary set — belt and braces. A1–A9 (7 attribute spellings incl. 3-deep nesting, glob, serde redirect) all rejected; B1–B8 boundary probes (doc comment, block comment, unit struct, `fn` body, attribute strings/raw strings, inner attribute) all rejected. |
| **P1-2 crate-root `mod bounded_vec` rebinding** | **CLOSED** | `RUST_CRATE_PINNED_MODULES_V1`, `RUST_CRATE_RESERVED_NAMES_V1`, `RUST_CRATE_MODULES_V1`. L1–L8 → `RUST_STATE_MODULE_DECLARATION_DRIFT`, `RUST_CRATE_ROOT_REBINDING`, `RUST_GLOB_IMPORT_FORBIDDEN`, `RUST_PATH_ATTRIBUTE_FORBIDDEN`, `RUST_CRATE_MODULE_SET_DRIFT`. |
| **P2-1 Python attribute stores** | **CLOSED** | All five previously-accepted spellings plus four more (annotated store, augmented store, `__dict__` subscript, `exec`) → `PYTHON_DYNAMIC_BINDING_FORBIDDEN`. |
| **P2-2 false `static_closure` clause** | **NOT CLOSED** | The clause now reads "…the local macro whose body and implementation file are whole-file pinned"; **P1-1** falsifies it. Nonclaim[6] correctly discloses the unpinned modules. See **P2-1**. |
| **P3-1 raw gate hash** | **CLOSED** | Hash is now `_normalized(rust_raw)`. Both string-literal weakenings → `RUST_GATE_CONTENT_DRIFT`. |
| **P3-2 `bounded_vec.rs` cfg(test)** | **CLOSED** | `BOUNDED_VEC_FILE_NORMALIZED_SHA256_V1` covers the whole file; inserting an item into the test module → `RUST_BOUNDED_VEC_DRIFT`. `rust_bounded_vec_unit_gate` is replay command 17 (9 unit tests). |
| **P3-3 `serde::de` prelude** | **CLOSED** | Rule is now `full_path == f"serde::{leaf}"`; `use serde::de::Deserialize;` → `RUST_SERDE_IMPORT_DRIFT`. |
| **P3-4 raw identifiers** | Carried, fail-closed | Unchanged by design; `r#use` → `RUST_SOURCE_UNPARSEABLE`. |
| **P3-5 bookkeeping** | Resolved | Both receipts are in P8's ancestry this time. |

---

## 2. Findings

### P0 — none

No authority escalation, value movement, production promotion, or `formal_core_complete = true` path exists. `claim_ceiling` was byte-identical under every one of the ~60 hostile mutations I mounted: seven authorities `NONE`, `formal_core_complete: false`, `whole_value_movement_safe: false`, `value_movement_gates_closed: 0` of 12, `o008_status: OPEN_EXACT_ALL_12_RECONCILIATION_MISSING`. No reject path mutates state. Reserves remain the claimant-free term.

---

### P1-1 — A second `macro_rules!` with the pinned name shadows the pinned macro; the compiled container is widened and every replay count stays exact

**Files:** `tools/o008_formal_cycle_admission_v1.py:1856` (`macro = re.search(r"\bmacro_rules!\s*" + BOUNDED_VEC_MACRO_NAME_V1 + r"\s*\{", code)`), `:1859` (body compared to `BOUNDED_VEC_MACRO_BODY_V1`), `:1683` (`definitions = {m.group(1): m.start() …}` — last definition wins), `:1696` (`macro_rules` token-tree check uses `_RUST_ITEM_KEYWORD_RE`, which does **not** include `fn`); `zk/global_settlement_abi_v1/src/state.rs:167`.

**Exact statement.** `rust_container_deserializer_closure_v1` locates the macro definition with `re.search`, so it validates the **first** definition only. `macro_rules!` in Rust is textually scoped and a later definition of the same name shadows the earlier one for all subsequent invocations, so the macro that actually expands at the terminal-container invocation need not be the one whose body was compared to `BOUNDED_VEC_MACRO_BODY_V1`. Two supporting gaps make the shadow useful: the second definition's token tree passes `rust_lexical_closure_v1` because `_RUST_ITEM_KEYWORD_RE` covers `struct|enum|union|trait|impl|type|mod|use|extern` but not `fn`; and nothing in the closure forbids `state.rs` from defining additional plain `fn`, `struct`, `impl` or nested `mod` items (probes M3/M4/M5, all `[ACCEPTED]`). `serde_json` is a first-class dependency of the crate, so the widening body needs no new import — a fully-qualified path suffices, and `rust_state_import_closure_v1` constrains only `use`.

**Weaponised.** Insert, immediately before the `deserialize_terminal_obligations_v1` invocation (so the pinned macro is still used by the earlier containers and no `unused_macros` warning appears):

```rust
macro_rules! bounded_state_vec_deserializer_v1 {
    ($function:ident, $row:ty, $maximum:expr, $label:literal) => {
        fn $function<'de, D>(deserializer: D) -> Result<Vec<$row>, D::Error>
        where D: Deserializer<'de>,
        { evil_widen_rows_v1::<D, $row, $maximum>(deserializer, $label) }
    };
}
```

and append a plain `fn evil_widen_rows_v1<'de, D, T, const MAXIMUM: usize>(…)` that decodes `Vec<serde_json::Value>`, keeps the `MAXIMUM` bound, removes `"zz_shadow"` from each object, and then `serde_json::from_value::<T>`. `state.rs` is the only file touched.

**Results (all mounted, not inferred):**

| Property | Result |
|---|---|
| `project_packet_v1`, full attacker re-pin (`p4.py` M1) | **ACCEPTED** |
| Controls M2–M5 (second macro under another name; extra `fn`; extra `struct`+`impl`; nested `mod`) | **ACCEPTED** (each is a separate, independently sufficient gap) |
| Files changed | **1** (`src/state.rs`, 34 lines); `bounded_vec.rs`, `lib.rs`, the gate byte-identical |
| `cargo test --test v1_projection_gate` | **7 passed** (exact recorded) |
| `cargo test --test global_economic_state_effect_refinement` | **41 passed** (exact) |
| `cargo test --test claimant_backing_guard_golden` | **3 passed** (exact) |
| `cargo test --lib` (the new `rust_bounded_vec_unit_gate`) | **9 passed** (exact) |
| `cargo clippy --offline --locked --all-targets -- -D warnings` | **exit 0** |
| Compiled `GlobalEconomicStateV1`, terminal row with `zz_shadow` | **`DIVERGENCE: widened terminal row ACCEPTED; rows=1`** |
| Same input, pristine `state.rs` (control) | ``CONTROL: rejected: unknown field `zz_shadow`, expected one of `obligation_id`, `lane_id`, `claimant`, `asset`, `amount_atoms`, `status` `` |

The seeded property test cannot catch it: `TERMINAL_FORBIDDEN`/`OUTBOX_FORBIDDEN` are enumerated in the pinned, attacker-readable gate and the generated keys have the form `k_%016x`, so a filter keyed on any other name survives all seven gate tests. The consequence is a wire-schema widening — two distinct V1 encodings decode to the same Rust state while Python rejects one — directly under `v1_information_loss`.

**Reproduce:**
```bash
PY="/home/trevormoc/Downloads/Autonomous Tau DEX/.venv/bin/python"
cd /tmp/opus-c1qprime-exp && "$PY" p4.py     # M1..M5 all [ACCEPTED]
cd /tmp/opus-c1qprime-cargo/zk/global_settlement_abi_v1
export CARGO_TARGET_DIR=/tmp/opus-c1qprime-cargo-target CARGO_INCREMENTAL=0
cargo test --offline --locked --test opus_probe -- --nocapture
#   DIVERGENCE: widened terminal row ACCEPTED; rows=1
cp /tmp/zenodex-formal-core-review-p-7896065ef/zk/global_settlement_abi_v1/src/state.rs src/state.rs
cargo test --offline --locked --test opus_probe -- --nocapture
#   CONTROL: rejected: unknown field `zz_shadow`, ...
```
(The mutated `state.rs` is saved at `/tmp/opus-c1qprime-work/state.rs.mutated`.)

**Required repair.** Require **exactly one** `macro_rules!` definition of `BOUNDED_VEC_MACRO_NAME_V1` in `state.rs` (`len(re.findall(...)) == 1`) and validate *that* body — the same "declared once" discipline the crate root already applies to `mod state;` and `mod bounded_vec;`. Independently, close the item surface of `state.rs`: pin the set of top-level `fn`/`struct`/`impl`/`mod` items the file may declare, or add `fn` to `_RUST_ITEM_KEYWORD_RE` for macro token trees and reject nested modules in the pinned modules. Add this exact survivor as a negative regression (`second_macro_definition_shadows_pinned_body`).

---

### P1-2 — A `notation` in an elided proof region vacuates a pinned non-vacuity witness with the statement and definition-surface hashes byte-identical

**Files:** `tools/o008_formal_cycle_admission_v1.py:1166-1172` (`_LEAN_ITEM_START_RE`), `:1174-1193` (`lean_definition_surface_v1`), `:2188-2192` (the two comparisons); `lean-mathlib/Proofs/GlobalClaimantCustodyRelationV1.lean:204`.

**Exact statement.** `lean_definition_surface_v1` keeps `code[cursor:statement_end]` for each theorem and then jumps `cursor` to the next match of `_LEAN_ITEM_START_RE`, deleting everything in between. That regex enumerates `theorem|lemma|def|abbrev|structure|inductive|instance|class|axiom|opaque|example|namespace|end|open|section|variable|universe|set_option|attribute|deriving|import|#…` after optional `@[…]` and `private|protected|noncomputable|nonrec`. Lean 4 has many more column-zero commands. I confirmed that each of `partial def`, `notation`, `macro_rules`, `local notation`, `scoped notation`, `export`, `syntax` and `initialize` inserted at column zero inside an elided region leaves the surface hash **unchanged** and is **ACCEPTED** under a full attacker re-pin (`p4.py` N2, N3, N4, N6, N8, N11, N12), against controls N9 (`def`, → `LEAN_DEFINITION_SURFACE_DRIFT`) and N1 (`unsafe def`, → `LEAN_PLACEHOLDER_PRESENT`). A `notation` whose atom is an existing identifier adds that atom to the token table, so a **later statement that is textually unchanged elaborates to a different proposition**.

**Lean semantics, verified directly** (`lake env lean`, worktree toolchain):

```lean
def OpusFoo : Prop := False
notation "OpusFoo" => True
theorem opus_probe : OpusFoo := by trivial     -- exit 0
```
Control without the `notation` line: `error: Tactic 'assumption' failed`, exit 1. The applied form (`notation:max "Rel" => (fun _ : St => True)` shadowing `def Rel (s : St) : Prop := s.n = 0`) also compiles, exit 0.

**Weaponised on the real file.** Insert, at column zero inside the elided proof region of `exactAllocation_noUnclassified_implies_exactCurrentProfileRelation` (immediately before `def balancedState`):

```lean
notation:max "NecessaryRelation" => (fun _ : State => True)
```

and rewrite three proof bodies (all elided, therefore free): `necessaryRelation_nonvacuous` becomes `trivial`; the two `*_preserves_necessaryRelation` proofs consume their now-`True` hypotheses; the two `*_preserves_exactCurrentProfileRelation` proofs inline the original arguments, because `def ExactCurrentProfileRelation` was elaborated before the notation and still projects the real `NecessaryRelation`.

**Results (all mounted):**

| Property | Result |
|---|---|
| `lean_definition_surface_v1` hash | **`cd1e010a3f82e159…` — identical to `LEAN_DEFINITION_SURFACE_SHA256_V1`** |
| Theorem statement hashes | **25/25 unchanged; 0 mismatches against `LEAN_STATEMENT_SHA256_V1`** |
| `project_packet_v1`, full attacker re-pin (`p5.py` W1) | **ACCEPTED** |
| `lake env lean -DwarningAsError=true` on the weakened file | **exit 0, empty output** (what `lean_direct_check` requires) |
| Same invocation on the pristine file (control) | exit 0 |
| `example : (…necessaryRelation_nonvacuous : True) = True.intro := rfl` | **compiles — the pinned non-vacuity witness now proves `True`** |

`lean_axioms_probe` cannot see this: a theorem of type `True` proved by `trivial` depends on no axioms, so `theorems_probed=25` stays green. `lean_binding_gate` pins the file's sha256, which the attacker re-pins.

**Reproduce:**
```bash
PY="/home/trevormoc/Downloads/Autonomous Tau DEX/.venv/bin/python"
cd /tmp/opus-c1qprime-exp && "$PY" p4.py     # N2/N3/N4/N6/N8/N11/N12 [ACCEPTED], N9 rejected
"$PY" p5.py                                   # W1 [ACCEPTED]
cd /tmp/zenodex-formal-core-review-p-7896065ef/lean-mathlib
lake env lean -DwarningAsError=true /tmp/opus-c1qprime-exp/LeanWeakened.lean   # exit 0, no output
lake env lean /tmp/opus-c1qprime-exp/LeanVacuity.lean                          # exit 0: witness is `True`
```

**Required repair.** The elided region must be a *proof*, not "whatever is not a recognised item". Two sound options: (a) require the elided text to contain no line whose first non-whitespace character starts at column zero — a Lean 4 proof body is always indented, so any column-zero token in the region is a new command and must either be part of the surface or be rejected outright (`LEAN_UNRECOGNISED_ITEM`); or (b) keep the whitelist but invert it — reject any column-zero identifier in an elided region that is not in `_LEAN_ITEM_START_RE`, rather than silently eliding it. Additionally forbid `notation`, `macro`, `macro_rules`, `syntax`, `elab`, `declare_syntax_cat`, `infix*`, `prefix`, `postfix` and `export` anywhere in the pinned proof file (add rules to `tools/scan_lean_proof_placeholders_v1.py` alongside `lean_unsafe_declaration`), since none is needed and each can re-bind a pinned statement's tokens. Add this survivor as `test_weakened_statement_is_rejected_on_fresh_projection[notation_shadowed_statement]`.

---

### P2-1 — The `static_closure` sentence again carries a clause the mounted route falsifies, and `statement_binding` overstates the Lean binding

**Files:** `tools/o008_formal_cycle_admission_v1.py:553-566` (`INFORMATION_LOSS_BINDING_V1["static_closure"]`), surfaced at `docs/research/ZENODEX_O008_FORMAL_CYCLE_V1.json` → `v1_information_loss.binding.static_closure` and `…_V1.md`; `lean_evidence.statement_binding`.

**Exact statement.** Two published sentences are false as written:

1. `static_closure` asserts "each record container carries only deserialize_with naming a function produced by exactly one item-position invocation of **the local macro whose body and implementation file are whole-file pinned**". **P1-1** shows the macro that expands at the invocation need not be the macro whose body was pinned. This is the third consecutive candidate in which the sentence names a property the checker does not enforce (Codex C1'' P2-3 → Opus C1''' P2-2 → here).
2. `lean_evidence.statement_binding` reads "theorem statements and the definitional surface are compared against hashes embedded in the admission core at S; proof terms are free text checked only by replay". The first half is literally true of the *text*, but the sentence is read as a meaning-binding claim and **P1-2** falsifies that reading; and the elided region is **not** restricted to "proof terms" — it admits arbitrary Lean commands.

Nonclaim[6] ("canonical.rs, release.rs, and the lane modules are compiled unpinned…") is a real improvement and correctly closes the disclosure half of Opus C1''' P2-2. What is missing is any statement that the pinned modules' own item surface beyond the scanned constructs is unconstrained, and that elided Lean regions are not restricted to proofs.

**Reproduce:** `"$PY" -c "import json;print(json.load(open('docs/research/ZENODEX_O008_FORMAL_CYCLE_V1.json'))['v1_information_loss']['binding']['static_closure'])"` alongside `p4.py` and `p5.py`.

**Required repair.** Take the **P1-1** repair (declared-once macro) so the clause becomes true, and take the **P1-2** repair so `statement_binding` becomes true. If either is deferred, cut the clause back to what is checked and add nonclaims naming (i) that `state.rs` may declare unscanned items and a shadowing macro, and (ii) that the Lean elided region may carry commands other than proof terms.

---

### P2-2 — golden-v4 mutation[3] names a killer that cannot fail on the mutation it declares

**Files:** `tests/evidence/test_hygiene/THV1-20260901-claimant-backing-guard-golden-v4.json` → `mutations[3]`; `tests/core/test_global_claimant_backing_guard_v1_golden.py:116-126`.

**Exact statement.** mutation[3] is "swap R1/R2 precedence or report overflow after R1", `killed_by` `…::test_precedence_is_overflow_then_domain_then_claimant`. That test executes nothing: it reads `_fixture()["vectors"]` and asserts three recorded `expected_outcome.code` values. With the R1/R2 order swapped in `require_claimant_backing_v1` (`src/core/global_economic_state_effect_refinement_v1.py:407-418`) the named node **passes**. The mutation *is* killed — by `…::test_vector_replays_state_view_root_and_outcome[precedence_domain_before_claimant]`, which fails, and by the renderer's own polarity guard (`tools/render_global_claimant_backing_guard_v1_golden.py:435` raises `mutation killer polarity drift: swap the R1/R2 precedence: precedence_domain_before_claimant yields OPEN_TERMINAL_EXCEEDS_CLAIMANT_ENTITLEMENTS, declared LIABILITIES_EXCEED_SAME_CONTROL_DOMAIN_BACKING`, so `test_fixture_is_the_renderer_output` fails too). So the defence is real and this is a bookkeeping defect, not a survivor — but it is the same class Codex graded at P2, and the commit message claims the false rows are corrected.

The other four rows I executed are correctly attributed: mutation[0] (drop R1) → `[one_atom_short_rejects]` **fails**; mutation[2] (reserves as backing) → `[excludes_reserves_from_backing]` **fails** while the old field-name attribution passes, confirming both Codex's finding and its repair; mutation[6] (count DRAINED as open) → `[ignores_drained_terminal_amount]` **fails**; mutation[9] (fold across control domains) → `[rejects_cross_domain_backing]` **fails**.

**Reproduce:** in a writable copy, swap the two `if _exceeds_backing_v1(...)` blocks, then
```bash
"$PY" -m pytest -q tests/core/test_global_claimant_backing_guard_v1_golden.py::test_precedence_is_overflow_then_domain_then_claimant   # passes
"$PY" -m pytest -q 'tests/core/test_global_claimant_backing_guard_v1_golden.py::test_vector_replays_state_view_root_and_outcome[precedence_domain_before_claimant]'  # fails
```

**Required repair.** Re-point mutation[3]'s `killed_by` at `[precedence_domain_before_claimant]` (and split the "or report overflow after R1" half into its own row with its own vector), or extend `test_precedence_is_overflow_then_domain_then_claimant` to execute the guard rather than assert fixture constants.

---

### P3-1 — `state.rs` may declare arbitrary additional items

**File:** `tools/o008_formal_cycle_admission_v1.py:1650-1712`. Probes M3/M4/M5: an extra top-level `fn`, an extra `struct` + `impl`, and a nested `mod` inside `state.rs` are each `[ACCEPTED]`. Alone these move nothing — the container attribute must still name a macro-produced function and the record shapes are pinned — but they are the ingredient that makes **P1-1** ergonomic. Recorded separately so the repair is not scoped only to the macro.

### P3-2 — Statement hashes are whitespace-normalised, so whitespace inside a pinned statement is free once the gate is re-pinned

**File:** `tools/o008_formal_cycle_admission_v1.py:1155` (`statement = " ".join(code[…].split())`). A whitespace-only edit inside a pinned statement leaves `LEAN_STATEMENT_SHA256_V1` satisfied; it is caught only by `LEAN_GATE_PIN_DRIFT`, which an attacker re-pins. In Lean a statement's whitespace is not semantically load-bearing in any way I could exploit, so this is a completeness note, not a survivor. Bounded negative result.

### P3-3 — A module-level `__getattr__` in the pinned Python types module is accepted

**File:** `tools/o008_formal_cycle_admission_v1.py:1346-1360`. `def __getattr__(name): return int` appended to `src/core/global_settlement_types_v1.py` is `[ACCEPTED]` under full re-pin (`p7.py` H1). It is **not** exploitable: PEP 562 module `__getattr__` fires only for names absent from the module dict, and `TerminalObligationV1` is defined, so the Python gate's `from … import` still binds the real class. Recorded for completeness; a duplicate class definition is correctly `PYTHON_CLASS_AMBIGUOUS`.

### P3-4 — Raw identifiers remain a misleading hard failure

Unchanged from Opus C1''' P3-4 and correctly left alone: `const _OPUS: u8 = { let r#use = 1u8; r#use };` in `state.rs` → `RUST_SOURCE_UNPARSEABLE: unterminated raw string`. Fail-closed, so not a soundness defect.

---

## 3. Verification record

`PY="/home/trevormoc/Downloads/Autonomous Tau DEX/.venv/bin/python"`, cwd `/tmp/zenodex-formal-core-review-p-7896065ef` unless noted; ESSO via `PYTHONPATH=/home/trevormoc/Downloads/ESSO ZENO_ESSO_PYTHON=/usr/bin/python3`; cargo under `CARGO_TARGET_DIR=/tmp/opus-c1qprime-cargo-target CARGO_INCREMENTAL=0` (deleted at the end).

| # | Command | Exit | Key output |
|---|---|---|---|
| 1 | `git status --porcelain` | 0 | **empty** (tracked and untracked), before and after; HEAD still `7896065ef`; no `target/` under the worktree |
| 2 | `git rev-list --parents -n 1 HEAD` | 0 | `7896065ef… 2bce28475…` — **one parent** |
| 3 | `git diff --stat HEAD~1 HEAD` | 0 | exactly `docs/research/ZENODEX_O008_FORMAL_CYCLE_V1.json` (+1/−1) and `…_V1.md` (+37/−36) |
| 4 | `check_o008_formal_cycle_v1.py --root "$PWD"` | **0** | `ok:true, packet_admitted:true, current_applicable:true, current_source_drift:[], errors:[]`; `subject_commit=2bce28475…`; replay `NOT_RUN`; schema `…/v3` |
| 5 | `check_o008_formal_cycle_v1.py … --replay …` | **0** | `EXECUTED_PASS`, **17 runs, all exit 0**: lean_version, lean_direct_check, lean_axioms_probe, lean_binding_gate, esso_validate, esso_verify_multi, esso_gate, prior_restage_gate, python_version, python_projection_gate, rust_projection_gate, rust_version, **rust_compiler_version**, rust_refinement_gate, python_golden_gate, rust_golden_gate, **rust_bounded_vec_unit_gate** |
| 6 | `build_o008_formal_cycle_v1.py … --subject-commit 2bce28475… --created-date 2026-09-01 --check --replay …` | **0** | `{"drift":[],"mode":"check","ok":true,"subject_commit":"2bce28475…"}` |
| 7 | `pytest -q -p no:cacheprovider` × 5 files | **0** | **373 passed in 134.52 s** (299 + 6 + 20 + 13 + 35 — exactly the predicted split) |
| 8 | `check_test_hygiene_v1.py --base-ref 2bce28475… --json` | **0** | `ok:true`, `changed_path_count: 2`, `evidence_packet_count: 90` |
| 9 | `ruff check` (4 tools modules) | 0 | `All checks passed!` |
| 10 | `mypy --strict` (4 tools modules) | 0 | `Success: no issues found in 4 source files` |
| 11 | `p1.py` — Codex survivor re-mount | 0 | verbatim `S'` blobs and 5 fresh re-cuts **all rejected**; verbatim `S''` and a fresh `True` re-cut → `LEAN_STATEMENT_DRIFT` |
| 12 | `p2.py` — Opus C1''' re-mount | 0 | 9 attribute/glob/serde routes, 8 crate-root routes, 9 Python store routes — **all rejected** |
| 13 | `p3.py`/`p4.py` — new routes | 0 | Lean N2/N3/N4/N6/N8/N11/N12 and Rust M1–M5 **ACCEPTED**; controls N1, N9 rejected |
| 14 | `p5.py` — Lean survivor | 0 | **W1 ACCEPTED**; surface hash and all 25 statement hashes unchanged |
| 15 | `p6.py` — residual closures | 0 | B1–B8, C1, D1, E1, E2, F1 **all rejected** |
| 16 | `p7.py` — Python hooks | 0 | H1/H2/H3 accepted (not exploitable, **P3-3**); H4 → `PYTHON_CLASS_AMBIGUOUS` |
| 17 | Mutated crate: `--test v1_projection_gate` / `…refinement` / `…golden` / `--lib` | 0 | **7 / 41 / 3 / 9 passed** — every recorded count exact |
| 18 | Mutated crate: `cargo clippy --all-targets -- -D warnings` | **0** | no diagnostics |
| 19 | Mutated crate: `--test opus_probe` | 0 | **`DIVERGENCE: widened terminal row ACCEPTED; rows=1`** |
| 20 | Pristine crate: `--test opus_probe` (control) | 0 | ``CONTROL: rejected: unknown field `zz_shadow`, …`` |
| 21 | `lake env lean -DwarningAsError=true LeanWeakened.lean` | **0** | **empty output** |
| 22 | `lake env lean LeanVacuity.lean` | **0** | witness `necessaryRelation_nonvacuous` has type `True` |
| 23 | `lake env lean` notation probe / control | 0 / 1 | shadowing compiles; control `Tactic 'assumption' failed` |
| 24 | Declared-mutation execution (5 rows) | — | golden[0], [2], [6], [9] killed by the **named** node; golden[3] **not** (**P2-2**) |
| 25 | `killed_by` resolution | 0 | **87 ids, 0 unresolved** against 362 collected tests |

### Hand-recomputed pins (all from S8 blobs, independently of the checker)

```
tools/o008_formal_cycle_admission_v1.py   9d6d92fed2dc43051d23618de91ef25efdb562b7fc5eec81e27fba5a73377a7b  MATCH (source_pins + executing_tools)
lean-mathlib/…/GlobalClaimantCustodyRelationV1.lean
                                          687a18bb663fbbbf0b565da137ecee8defb790126e1249303ba2773fb694d005  MATCH (source_pins + LEAN gate PINNED_SOURCES)
sha256(normalise(v1_projection_gate.rs))  38db418dee30744ae1e9cbf242ad07dd8dd7b7c32c93ebe6d6ba80334cdcfa51  == RUST_GATE_NORMALIZED_SHA256_V1
sha256(normalise(bounded_vec.rs))         eb70f210499100de84e3669756d18beece43ee5b1a90ee9be7758f0397ac3943  == BOUNDED_VEC_FILE_NORMALIZED_SHA256_V1
lean_definition_surface_v1 hash           cd1e010a3f82e1595c4cefa7fc7354bc8d972e77c669ed026d177bb8cf275b11  == LEAN_DEFINITION_SURFACE_SHA256_V1
statement "noUnclassified_premise_is_necessary" (hand-extracted, hand-normalised)
                                          9079528f9f9ed075fe76de725096ffb7ba5c569afba6368d8aa29b2822195ab3  == LEAN_STATEMENT_SHA256_V1[…]
```

### Bulk verification

- All **28** packet `source_pins` equal the S8 blob bytes (0 mismatches).
- All **26** THV1-admission-v9 and all **12** golden-v4 pins equal the S8 blob bytes (0 mismatches).
- `subject_tree == 0facc820f9d9fb6b80a11d71cf0240c3adf76538` (= S8's tree); `subject_parent == c6760e9c1…`; `packet_write_set` = exactly the two packet paths; P8 has one parent, S8 has one parent.
- `LEAN_STATEMENT_SHA256_V1` has 25 entries, matching the 25-theorem inventory.

---

## 4. Nonclaims and residual risks

1. **I did not re-verify the Lean proofs' mathematical content.** I compiled the file (pristine and weakened) and confirmed one witness's type; I did not re-audit the 25 theorems. Codex C1'' verified the necessity theorem directly.
2. **P1-2's harm is scoped to what a `notation` can re-bind.** I mounted one instance (`NecessaryRelation` → `fun _ => True`, vacuating the pinned non-vacuity witness). I did not enumerate which other pinned statements are reachable this way, and I did not attempt a `macro_rules`- or `syntax`-based variant end to end — only their admission-level invisibility is executed.
3. **Both P1 routes assume an attacker who re-pins.** That is the standard this task sets; `repin.py` rewrites every pin of a changed blob in every source blob and hygiene packet to a fixpoint. An attacker who cannot re-pin is stopped at the first changed byte by `THV1_PIN_DRIFT`.
4. **The checker's own source is the trust anchor and is outside the threat model I applied.** `LEAN_STATEMENT_SHA256_V1`, `LEAN_DEFINITION_SURFACE_SHA256_V1`, `RUST_GATE_NORMALIZED_SHA256_V1`, `BOUNDED_VEC_FILE_NORMALIZED_SHA256_V1` and `RUST_CRATE_MODULES_V1` live in `tools/o008_formal_cycle_admission_v1.py`, which the attacker re-pins like any other file. Their force comes entirely from the fact that editing them is a visible diff in the reviewed tool. That is the correct design given the task's stated standard, but it should be stated as such somewhere in the packet.
5. **`Cargo.lock` content, the dependency name set, and the host crate registry cache remain host-trusted**, as C1'' recorded. `prepare_replay_environment_v1` symlinks `$CARGO_HOME/registry` (or `~/.cargo/registry`) into the sanitized home; a tampered extracted `src/` in that cache is not re-verified by `--locked --offline`. Unchanged by this candidate.
6. **`PATH` for replay is derived from `shutil.which` over the invoking `PATH`**, and `RUSTUP_HOME`/`ELAN_HOME`/`PYTHONUSERBASE` are deliberate passthroughs. `rustc -vV` (release, commit-hash, host) and the Lean version now bind the toolchain *identity* but not the binary's bytes; `PYTHONUSERBASE` can shadow the ESSO solver bindings. All of this is disclosed in `REPLAY_ENV_POLICY_V1`; I read the policy against the implementation and found no undisclosed leak — `_replay_env` builds from a fixed dict and never reads `os.environ`.
7. **P3-3 is reasoned, not executed end to end.** I did not build a mutated repository copy to watch the Python gate resolve `TerminalObligationV1` past a module `__getattr__`; I inferred it from PEP 562. The admission acceptance itself *is* executed.
8. **Audit-procedure incident.** My first `build_o008_formal_cycle_v1.py --check --replay` returned `REPLAY_EXECUTED_FAIL: REPLAY_EXIT_CODE at lean_binding_gate: exit 1`. This was caused by my own concurrent `lake env lean` invocation in the same `lean-mathlib` directory, not by the candidate. I re-ran it with no concurrent Lean activity and it returned `{"drift":[],"ok":true}`, exit 0. Row 6 records the clean run. Nothing was written inside either repository; `git status --porcelain` is empty in both.
9. **Disk pressure.** The host was at 97–98 % full throughout. `/tmp/opus-c1qprime-cargo-target` and `/tmp/opus-c1qprime-mutrepo` were deleted at the end; no result above was affected.
10. **I did not re-verify the ESSO layer independently.** The ESSO evidence rests on replay commands 5–7 executed by the checker. Opus C1''' re-derived the ir-hash and fingerprint outside the checker; C1'''' did not touch the ESSO model (`d7b547e327…` unchanged).

---

## 5. Do the user's decisions hold?

Yes, on all six.

- **Authority NONE everywhere.** Held. All seven authority fields are `NONE` in every projection I ran, including under ~60 hostile mutations.
- **`formal_core_complete` false.** Held, with `whole_value_movement_safe: false` and `value_movement_gates_closed: 0` of 12.
- **O-008 open.** Held. `o008_status: OPEN_EXACT_ALL_12_RECONCILIATION_MISSING`; `formal_cycle_status: FORMAL_CYCLE_COMPLETE_O008_OPEN`; nonclaim[0] states plainly that the completed formal cycle does not complete O-008.
- **Reserves are the claimant-free term.** Held. `derive_claimant_backing_view_v1` folds only `state.custody` and `state.liabilities`; no reserve column enters the claimant-backing view, and the golden vector `excludes_reserves_from_backing` is now the *named* killer for the reserve mutation — which I executed and confirmed fails.
- **Control-domain vocabulary with V1 wire names byte-stable.** Held. `TERMINAL_FIELDS_RUST_V1`/`OUTBOX_FIELDS_RUST_V1` are unchanged and pinned in both gates; the new prose uses "control domain" while the wire names stay as they were.
- **O-008A unattested; no UP-xx fixture-selected.** Held. Nonclaim[1] states the exact all-twelve certificate is not implemented or mounted; no `UP-` identifier appears anywhere in the packet.

---

## 6. Disposition

**Grade C — REVISE.** The candidate is exactly chained, claim-limited, and passes every prescribed verification with the predicted numbers; nine carried findings are genuinely closed and I confirmed each by re-mounting it, including both of Codex's exact survivor chains. It cannot rise above C because the two claims the commit is built on are each falsified end to end by a route I mounted completely — a second `macro_rules!` definition that shadows the pinned container decoder and produces a compiled wire-schema widening with every recorded replay count exact (**P1-1**), and a `notation` in an elided proof region that vacuates a pinned non-vacuity witness while the definition-surface hash and all 25 statement hashes stay byte-identical and the file compiles warning-free (**P1-2**) — and because the packet again publishes a `static_closure` clause those routes make false (**P2-1**).

The two smallest changes that close the most ground: require **exactly one** `macro_rules! bounded_state_vec_deserializer_v1` in `state.rs` and validate that one (mirroring the crate root's existing declared-once discipline), and make the Lean elided region reject any column-zero command rather than silently eliding what `_LEAN_ITEM_START_RE` does not name.

This grade is advisory and grants no authority.
