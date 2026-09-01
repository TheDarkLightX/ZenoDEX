# Opus review receipt: candidate C1'' at P5 = 9056dac69044772aab9316637a68ec94265fe885

Reviewer: Opus 5 (independent reviewer, read-only, detached worktree `/tmp/zenodex-formal-core-review-p-9056dac69`).
Date: 2026-09-01. Subject: P5 = 9056dac69044772aab9316637a68ec94265fe885 (tree dcdd90fd38a72622eb7bd8d8724de9899d495fba), S5 = 6358da52f5a4235f6928dda0bf1bdee92d862dd2, parent fd59705426b50787e813d62b7c6bd30a371f08df.
Verdict: Grade C, REVISE. All ten C1-residual and C2' findings closed; the C1' P1-A instance is dead; two new mounted P1s (brace-group use statements skipped by the use scan; bounded_vec.rs pinned only by substrings) and three P2s (gate bodies unconstrained; attribute-level rebinding; unenforced packet statement). Disposition: repaired by candidate C1'''. The grade is advisory and grants no authority.

Verbatim report follows (probe crates it names lived under /tmp/opus-c1dprime-* and are not part of the repository).

---

# Opus review receipt: candidate C1'' at P5 = 9056dac69044772aab9316637a68ec94265fe885

Reviewer: Opus 5 (independent reviewer, read-only, detached worktree `/tmp/zenodex-formal-core-review-p-9056dac69`).
Date: 2026-09-01.
Subject: P5 = `9056dac69044772aab9316637a68ec94265fe885` (tree `dcdd90fd38a72622eb7bd8d8724de9899d495fba`),
S5 = `6358da52f5a4235f6928dda0bf1bdee92d862dd2` (tree `f218d3ad743075ef8bb04bde5365ca0f5b6cfa6d`),
S5 parent = `fd59705426b50787e813d62b7c6bd30a371f08df` (Opus C2' receipt commit).

Worktree left untouched: 0 tracked changes, HEAD still `9056dac69`. Nothing written under `/dev/shm`, nothing written inside the worktree or the primary repository. `CARGO_TARGET_DIR=/tmp/zenodex-opus-c1dprime-cargo-target` deleted (1.7 G reclaimed). Adversarial work was done in `/tmp/opus-c1dprime-exp` (probe harness), `/tmp/opus-c1dprime-cargo` (a standalone crate copy with its own `Cargo.lock`), and `/tmp/opus-c1dprime-repo` (a standalone shallow clone with its own `.git`, built by `git init` + `git fetch --depth=1 file://…`).

---

## 1. Grade: C — REVISE

**The exact subject is clean, exactly chained, claim-limited, and passes every prescribed verification.** 298 tests pass; three Rust test binaries pass at exactly the recorded counts (41/3/7); ruff, mypy `--strict`, and clippy `-D warnings` are clean; Lean compiles with `-DwarningAsError=true`; the checker admits with and without `--replay`, and `--replay` now runs **15** commands including a Rust toolchain identity, the Rust refinement suite, and both golden replays. Both hand-recomputed pins match the packet exactly, all 28 source pins equal S5 bytes, all 26 hygiene-packet pins equal S5 bytes, and all four executing-tool hashes equal S5 blobs.

**Most of the repair work is real and verified adversarially.** Every one of the ten C1 residuals and C2' findings is closed, and I confirmed each by running it rather than reading it: the homoglyph bypass is closed twice over (NFKC folding *and* a hard printable-ASCII rule on every packet string); the ESSO grade now rejects a zero-query VERIFIED report (`REPLAY_ESSO_QUERY_COUNT_DRIFT`) and a wrong query-id set (`REPLAY_ESSO_QUERY_SET_DRIFT`); `->` no longer swallows fields; the Lean necessity theorem now states and genuinely derives `¬ ∀ (s : State) (_ : ExactAllocationWitness s), ExactCurrentProfileRelation s`; `--check` without `--replay` reports `CHECK_MODE_MISMATCH`; the lifecycle stage-3 test drives a real synthetic child commit; and **all six** implementation mutations in golden-v3 are killed by the node they name (I mutated the guard six ways and every declared node failed). The C1' P1-A instance is dead: both of my C1' counterexamples are now rejected with `RUST_CONTAINER_DESERIALIZER_DRIFT`, and eight further variants I built against the container closure (second local macro, `mod` shim, commented-out invocation, foreign-const macro argument, extra field attribute, cross-named deserializer, `fn` re-alias) are all rejected with specific codes. Macro locality is genuinely closed: invocation-before-definition and item-defining macro bodies are both rejected.

**What holds the grade at C is that the headline claim of the commit — binding the V1 projection to its compiled decoding path — again does not hold adversarially, and this time I mounted the counterexample end to end.** The `use`-statement scanner (`_RUST_USE_RE`, `tools/o008_formal_cycle_admission_v1.py:614`) cannot match a braced `use`. It therefore sees **exactly one of the four `use` statements in `state.rs`**, and the two it is meant to constrain — `use serde::{Deserialize, Deserializer, Serialize};` and, once rewritten in brace form, `use crate::bounded_vec::deserialize_bounded_vec_v1;` — are invisible to it. Adding two brace characters to `state.rs` line 3 redirects the pinned macro's target to `crate::canonical`, one of 82 unpinned `src/*.rs` modules in the same crate. With a faithful copy of the pinned visitor there plus one added `object.remove("zz_shadow")`, the crate compiles, **all 52 test binaries pass**, `cargo clippy --all-targets -- -D warnings` is clean, all three Rust replay suites report their exact recorded counts (41/3/7), `bounded_vec.rs` is byte-identical to the pinned file, `project_packet_v1` accepts — and the compiled `GlobalEconomicStateV1` accepts a terminal row carrying an extra key that the pristine crate rejects. A second, independent bypass edits `bounded_vec.rs` *inside* its own pinned fragments (the three pinned fragments are substring-containment checks over a visitor body that is otherwise free), with the same result.

Separately, the C1' P1-B repair is real but partial: the gates' *tables and test names* are now pinned, so a wholesale replacement is rejected — but the *bodies* are not. Seven Rust tests with the pinned names and empty bodies, and seven Python tests with the pinned names, the pinned constants, and `pass` bodies, are both accepted by admission **and** report the expected `7 passed` / `13 passed` under replay. I ran both.

This is a materially stronger candidate than C1': the container-deserialiser class that was wide open is now narrow, hermeticity and toolchain identity are real, and every evidence-metadata defect is closed. But the defect class Codex graded C1 at C for, and that I graded C1' at C for, is reachable a third time by a construct simpler than either predecessor — a two-character edit — so the grade cannot rise.

### Per-finding disposition

**Opus C1' findings (grade C):**

| Finding | Claim | Status | Evidence |
|---|---|---|---|
| **P1-A** | `deserialize_with` hook on the container defeats the compiled gate | **CLOSED for the named class; the defect class is OPEN by a new route** | Both C1' counterexamples rejected (`RUST_CONTAINER_DESERIALIZER_DRIFT`); 8 new container variants rejected. But see **P1-1** and **P1-2** below — the same compiled divergence is reachable through the bounded-vec import and through the bounded-vec visitor body. |
| **P1-B** | Gate content unconstrained; gates can be made vacuous | **PARTIALLY CLOSED** | Names + four arrays now pinned (`RUST_GATE_CONTENT_DRIFT` / `PYTHON_GATE_CONTENT_DRIFT`); an extra test name, a shrunk `TERMINAL_FORBIDDEN`, and `#[ignore]` are all rejected. **Bodies are still free**: empty-bodied gates admit and report 7/13 passed. See **P2-1**. |
| **P2-1** | No Rust compiler identity; not hermetic | **CLOSED (with stated residuals)** | `rust_version` (`cargo --version`) is replay command 12; `toolchain.rust = "1.87.0"` is compared on fresh replay; `Cargo.lock` is source pin 12; `.cargo/config{,.toml}` at three levels rejected at S, HEAD and worktree (`CARGO_CONFIG_PRESENT`); `[workspace]`/`[features]`/`[profile]`/`auto*`/non-exact versions rejected. Residuals in §4. |
| **P2-2** | Macro locality order-blind; foreign path macros reachable | **CLOSED** | `crate::evil_items!()` → `RUST_FOREIGN_ITEM_MACRO`; unqualified invocation before its definition → `RUST_FOREIGN_ITEM_MACRO`; item-defining local macro → `RUST_MACRO_DEFINES_ITEM`; benign local macro accepted. |
| **P2-3** | Python container class not closed | **CLOSED for the named routes; one route remains** | `exec(...)` → `PYTHON_DYNAMIC_BINDING_FORBIDDEN`; `globals()[...] = ` → same; `GlobalEconomicStateV1` rebind → `PYTHON_CLASS_REBOUND`; metaclass → `PYTHON_CLASS_BASES_FORBIDDEN`; extra decorator → `PYTHON_CLASS_DECORATORS_DRIFT`; `setattr` via `importlib` → `PYTHON_DYNAMIC_BINDING_FORBIDDEN`. **`object.__setattr__(sys.modules[__name__], …)` is still accepted** (see **P2-2** below). |
| **P2-4** | Hygiene selection validates pins only, undocumented | **CLOSED** | `nonclaims[8]`: "Selected test-hygiene packets are bound by pin only; their evidence families and mutation tables are validated by tools/check_test_hygiene_v1.py, which this checker does not run." |
| **P3-1** | Line-anchored `use` scan; `extern crate` unconstrained | **PARTIALLY CLOSED** | `extern crate` → `RUST_EXTERN_CRATE_FORBIDDEN`; mid-line `use` now caught (`RUST_SERDE_IMPORT_DRIFT`). **Braced `use` still escapes entirely** — this is the vehicle for **P1-1**. |
| **P3-2** | Two author-record values free absent `--replay` | **CLOSED** | `nonclaims[7]` names exactly the python/rust versions and the Lean probe hash. |
| **P3-3** | `--check` without `--replay` reports opaque drift | **CLOSED** | `{"error":{"code":"CHECK_MODE_MISMATCH",…}}`, exit 1; `test_builder_check_mode_mismatch_is_named` asserts the code. |
| **P3-4** | Lifecycle stage 3 definitional/unreachable | **CLOSED** | `test_cli_source_commit_after_p_is_fail_closed` clones the synthetic chain, commits a real edit to a pinned path after P, and asserts exit 1 + `packet_admitted True` + `current_applicable False` + exact `current_source_drift`. |
| **P3-5** | `declared_order` bespoke parser | **CLOSED** | Replaced by a string-and-nesting-aware tokenizer, with an in-test assertion over `{"a":{"x":[1,2],"y":"b,c"},"b":"q\\"z","c":3}` → `["a","b","c"]`. |

**Opus C1 residuals:**

| Finding | Status | Evidence |
|---|---|---|
| **P2-1** Unicode-homoglyph promotion-token defeat | **CLOSED (twice)** | `check_nonclaims_v1` NFKC-folds (catches U+FF4F fullwidth o → `PROMOTION_TOKEN_PRESENT`); `_validate_json_value` rejects any non-printable-ASCII packet string (`PACKET_NON_ASCII`), which catches U+2011 and U+2010, which NFKC alone does not. |
| **P2-2** `noUnclassified_premise_is_necessary` states no necessity | **CLOSED** | Conclusion is now `¬ ∀ (s : State) (_ : ExactAllocationWitness s), ExactCurrentProfileRelation s`; the proof is `intro universal; exact overCollateralised_isBacked_notExact.2 (universal overCollateralisedState overCollateralisedAllocation).2` — a real derivation, not `rfl`+`omega` on a literal. Docstring matches. `lake env lean -DwarningAsError=true` exit 0. |
| **P2-3** Rust rejection behaviour asserted but not executed | **CLOSED** | `rust_refinement_gate` (41 passed) and `rust_golden_gate` (3 passed) are replay commands 13 and 15. |
| **P2-4** ESSO replay never verifies a query ran | **CLOSED** | Synthetic zero-query VERIFIED report → `REPLAY_ESSO_QUERY_COUNT_DRIFT (0/0)`; three wrong ids → `REPLAY_ESSO_QUERY_SET_DRIFT (a,b,c)`. |
| **P3-1** `->` treated as a closing delimiter | **CLOSED** | `_split_depth_zero_commas("pub a: u8, pub cb: fn(u8) -> u8, pub b: u8")` → three fields; generics still nest correctly. |
| **P3-3** Four definitional theorems inside `theorem_count: 25` | **CLOSED** | `lean_evidence.definitional_theorems` lists the four; `substantive_theorem_count: 21`, `theorem_count: 25`; `completion_scope[4]` says "reserve independence (definitional, disclosed)". |

**Opus C2' findings:**

| Finding | Status | Evidence |
|---|---|---|
| **P2-1** Six false `killed_by` attributions | **CLOSED — verified on six of six** | golden-v3 now names vector-replay nodes. I applied each implementation mutation in a standalone clone and confirmed the declared node fails: drop R1 → `[one_atom_short_rejects]` FAILED; drop R2 → `[open_terminal_one_atom_over_rejects]` FAILED; unchecked fold → `[rejects_entitlement_aggregate_overflow]` FAILED; same edit → `[rejects_custody_aggregate_overflow]` FAILED; drop the OPEN filter → `[ignores_drained_terminal_amount]` FAILED; fold entitlements across domains → `[rejects_cross_domain_backing]` FAILED. |
| **P2-2** `completion_scope` grew without a replay command | **CLOSED** | `python_golden_gate` (35 passed) and `rust_golden_gate` (3 passed) added; `proof_replay.commands` is 15. |
| **P3-1** Two mutations named one source location | **CLOSED** | Reworded to "use unchecked addition in the shared fold helper" and "skip the checked fold for the custody table", pointing at two distinct vectors. |
| **P3-2** Stage 3 not reached at a packet commit | **CLOSED** | Synthetic-chain test, above. |
| **P3-3** Bare `assert` in the renderer | **CLOSED** | `grep -c 'assert isinstance' tools/render_global_claimant_backing_guard_v1_golden.py` → 0. |
| **P3-4** Python golden replay self-referential | Carried forward, correctly scoped | Unchanged; the Rust replay supplies the independence. |

---

## 2. Findings

### P0 — none

No authority escalation, value movement, production promotion, or `formal_core_complete = true` path. `claim_ceiling` is emitted from module constants and was identical under every mutation I mounted: all seven authorities `NONE`, `formal_core_complete: false`, `whole_value_movement_safe: false`, `value_movement_gates_closed: 0` of 12, `o008_status: OPEN_EXACT_ALL_12_RECONCILIATION_MISSING`. No reject path mutates state; no reserve or balance column can enter the claimant-backing view.

---

### P1-1 — A braced `use` in `state.rs` redirects the pinned deserialiser to an unpinned sibling module; the compiled container is widened and every replay command stays green

**Files:** `tools/o008_formal_cycle_admission_v1.py:614` (`_RUST_USE_RE`), `:1543-1551` (the two `use` rules inside `rust_lexical_closure_v1`, defined at `:1488`); `zk/global_settlement_abi_v1/src/state.rs:1` and `:3`.

**Exact statement.** The scanner's `use` regex is

```python
_RUST_USE_RE: Final = re.compile(r"(?:^|[;{}])\s*(?:pub(?:\([^)]*\))?\s+)?use\s+([^;{}]+);")
```

The capture class `[^;{}]` excludes braces, so a `use` whose path contains a brace group matches nothing. `state.rs` has four `use` statements; the scanner sees **one**:

```
source lines : use serde::{Deserialize, Deserializer, Serialize};
               use crate::bounded_vec::deserialize_bounded_vec_v1;
               use crate::canonical::{ …
               use crate::release::{ …
regex sees   : ['crate::bounded_vec::deserialize_bounded_vec_v1']
```

Both rules at `:1545` (`RUST_SERDE_IMPORT_DRIFT`) and `:1549` (`RUST_BOUNDED_VEC_IMPORT_DRIFT`) are therefore defeated by rewriting the import in brace form. The serde rule has in fact **never fired on the line it exists to constrain**, because that line is braced as shipped.

Weaponised: change `state.rs:3` from
`use crate::bounded_vec::deserialize_bounded_vec_v1;` to
`use crate::canonical::{deserialize_bounded_vec_v1};`
(the equivalent `use crate::{canonical::deserialize_bounded_vec_v1};` also passes), and put a `deserialize_bounded_vec_v1` in `src/canonical.rs`. `canonical.rs` is one of the crate's 86 `src/*.rs` modules and is **not** among the 28 pinned paths; `rust_crate_root_closure_v1` constrains only `mod state;`. The pinned macro body — which is checked byte-for-byte — expands to `deserialize_bounded_vec_v1::<D, $row, $maximum>(deserializer, $label)`, and *which* function that names is decided entirely by the import the scanner cannot see.

The hostile module is a faithful copy of the pinned visitor (same `size_hint` guard, same `MAXIMUM` loop, same `IgnoredAny` excess check, same error strings) with one added line: `object.remove("zz_shadow")` before `T::deserialize(row)`.

**Results (all mounted, not inferred):**

| Property | Result |
|---|---|
| `project_packet_v1` on the edited `state.rs`, with full attacker re-pinning | **ACCEPTED** (probes U2, U3) |
| `bounded_vec.rs` vs the pinned file | **byte-identical** (`diff -q` → identical) |
| Diff to pinned files | **one line**, two brace characters |
| `cargo test --offline --locked` (whole crate) | **52 test binaries, 0 failures** |
| `cargo test … --test v1_projection_gate` | **7 passed** (the exact recorded count) |
| `cargo test … --test global_economic_state_effect_refinement` | **41 passed** (exact) |
| `cargo test … --test claimant_backing_guard_golden` | **3 passed** (exact) |
| `cargo clippy --offline --locked --all-targets -- -D warnings` | **exit 0** |
| Compiled `GlobalEconomicStateV1` on a recorded state whose terminal row carries `zz_shadow` | **`DIVERGENCE: widened terminal row ACCEPTED; rows=1`** |
| Same input on the pristine crate (control) | ``CONTROL: rejected: unknown field `zz_shadow`, expected one of `obligation_id`, `lane_id`, `claimant`, `asset`, `amount_atoms`, `status` `` |

The seeded property test does **not** catch this: its generated keys have the form `k_%016x`, and the four `TERMINAL_FORBIDDEN` / `OUTBOX_FORBIDDEN` names are enumerated in the pinned, attacker-readable gate file, so a filter keyed on any other name survives all seven tests. The consequence is a wire-schema widening: two distinct V1 encodings decode to the same state in Rust, while Python rejects one of them — a canonicalisation and cross-language parity break directly under the packet's `v1_information_loss` claim.

**Reproduce:**
```bash
PY="/home/trevormoc/Downloads/Autonomous Tau DEX/.venv/bin/python"
# 1. admission accepts the braced redirect (in-process, full attacker re-pinning)
"$PY" /tmp/opus-c1dprime-exp/p5.py
#   [ACCEPTED] U2 bounded-vec import redirected, braced
#   [rejected] U2b bounded-vec import redirected, unbraced (control) -> RUST_BOUNDED_VEC_IMPORT_DRIFT
#   [ACCEPTED] U1 serde import redirected, braced
#   [rejected] U1b serde import redirected, unbraced (control)       -> RUST_SERDE_IMPORT_DRIFT
# 2. compiled behaviour (crate copy; nothing written in the worktree)
cd /tmp/opus-c1dprime-cargo/zk/global_settlement_abi_v1
export CARGO_TARGET_DIR=/tmp/opus-c1dprime-target CARGO_INCREMENTAL=0
cargo test --offline --locked                      # 52 binaries, 0 failures
cargo test --offline --locked --test opus_probe -- --nocapture
#   DIVERGENCE: widened terminal row ACCEPTED; rows=1
diff -q src/bounded_vec.rs "/tmp/zenodex-formal-core-review-p-9056dac69/zk/global_settlement_abi_v1/src/bounded_vec.rs"   # identical
diff "/tmp/zenodex-formal-core-review-p-9056dac69/zk/global_settlement_abi_v1/src/state.rs" src/state.rs
#   3c3 < use crate::bounded_vec::deserialize_bounded_vec_v1;
#       > use crate::canonical::{deserialize_bounded_vec_v1};
```

**Required repair.** Two independent changes, both cheap:
1. Tokenise `use` items from the stripped code instead of line-matching them: read from `use` to the terminating `;` at brace depth zero, expand brace groups into their full paths, and apply both rules to every expanded path. Assert as a self-test that the scan sees **all four** of `state.rs`'s imports (today it sees one).
2. Do not let an unpinned module decide the decoder. Either pin the deserialiser by absolute path in the macro body (`crate::bounded_vec::deserialize_bounded_vec_v1::<…>`, so no import can redirect it), or add every `src/*.rs` in the crate to the pinned set, or state honestly in `v1_information_loss` that the closure covers five files out of ~85 in the crate and that the compiled binding is only as strong as the two projection gates.

---

### P1-2 — The bounded-vec visitor body outside the three pinned fragments is free; the same widening is reachable without touching `state.rs`

**Files:** `tools/o008_formal_cycle_admission_v1.py:520-527` (`BOUNDED_VEC_REQUIRED_FRAGMENTS_V1`), `:1651` (`rust_bounded_vec_closure_v1`); `zk/global_settlement_abi_v1/src/bounded_vec.rs:35` (`visit_seq`).

**Exact statement.** `rust_bounded_vec_closure_v1` requires that three whitespace-normalised fragments be **contained** in the library text, that there be exactly one `impl` block, and that no `Deserialize` impl exist. It does not pin the file. `deserialize_bounded_vec_v1` is fully pinned (the whole function is one fragment), but the `Visitor` impl is pinned only at its header (`… { type Value = Vec<T>;`) and at the element loop (`match sequence.next_element()? { Some(value) => values.push(value), None => return Ok(values), }`). Everything else inside the impl is free, and `serde_json` is already a non-dev dependency of the crate, so `serde_json::Value` is available as a generic intermediate. The pinned loop can be kept verbatim inside an `if false { … }` block while a live loop buffers each element as a `Value`, strips a chosen key, and only then calls `T::deserialize`.

**Result:** the mutated `bounded_vec.rs` is **ACCEPTED** by `project_packet_v1` (probe B1), the crate compiles, all 9 library unit tests pass (including `oversized_exact_size_sequence_rejects_before_first_element`), all 7 `v1_projection_gate` tests pass, and the compiled container reports `DIVERGENCE: widened terminal row ACCEPTED; rows=1`.

**Reproduce:**
```bash
"$PY" /tmp/opus-c1dprime-exp/p2.py
#   [ACCEPTED] B1 hostile JsonValue pre-filter inside the pinned visitor
```
(the compiled half was run first, in the crate copy, with `--test opus_probe --test v1_projection_gate --lib`.)

**Required repair.** Pin `bounded_vec.rs` the way the macro body is pinned: compare the whole library portion (after stripping `#[cfg(test)] mod tests`) against a normalised template constant, not against three substrings. If a whole-file template is too brittle, at minimum require that the *only* `next_element` turbofish in the file be `next_element::<IgnoredAny>()`, that no other type be named in a `next_element` call, and that the file contain no `serde_json` reference and no other `use` beyond a pinned import list.

---

### P2-1 — Both projection gates can still be made vacuous while keeping the pinned names and tables, and both then report the expected pass counts

**Files:** `tools/o008_formal_cycle_admission_v1.py:1928` (`_check_projection_gates`), `:528` (`RUST_GATE_TESTS_V1`), `:537` (`PYTHON_GATE_TESTS_V1`), `:582-583` (`PYTHON_GATE_EXPECTED_PASSED_V1 = 13`, `RUST_GATE_EXPECTED_PASSED_V1 = 7`), `:1918` (`_rust_str_array`).

**Exact statement.** The C1' P1-B repair extracts and pins the gates' test-name tuples and four constant arrays. It does not look at the test **bodies**, and nothing requires the pinned arrays to be *used*. A Rust gate consisting of the four `const` arrays plus seven `#[test] fn <pinned name>() {}` is accepted, and reports `7 passed`. A Python gate consisting of the four constants plus the seven pinned function names — keeping the two `@pytest.mark.parametrize` decorators so the node count stays 13 — with `pass` bodies is accepted, and reports `13 passed`. Both therefore survive admission **and** replay. Unused `const` arrays are a Rust warning, not an error, and `cargo test` does not deny warnings.

The pinning is not worthless: an extra or renamed test is rejected (`RUST_GATE_CONTENT_DRIFT`), a shrunk forbidden-field table is rejected, and `#[ignore]` is rejected (incidentally — it breaks the `#[test]`/`fn` adjacency the name regex requires). A module-level `pytest.skip(..., allow_module_level=True)` is accepted by the scan but caught at replay by the pass count. Only the empty-body form defeats both layers.

**Reproduce:**
```bash
"$PY" /tmp/opus-c1dprime-exp/p3.py
#   [ACCEPTED] G1 Rust gate: pinned names+arrays, EMPTY bodies
#   [ACCEPTED] G3 Python gate: pinned names+constants, `pass` bodies
#   [rejected] G2 extra test name           -> RUST_GATE_CONTENT_DRIFT
#   [rejected] G4 shrunk TERMINAL_FORBIDDEN -> RUST_GATE_CONTENT_DRIFT
#   [rejected] G5 #[ignore]                 -> RUST_GATE_CONTENT_DRIFT
"$PY" -m pytest -q /tmp/.../test_vacuous_gate.py       # 13 passed
cargo test --offline --locked --test v1_projection_gate  # 7 passed (empty bodies)
```

**Required repair.** Require each pinned gate test to reference its table and to contain an assertion. A cheap, sound version: from the Rust gate require that each of the four `const` names appear at least once inside a `#[test] fn` body, and that the body contain `assert` or the shared `assert_unknown_field` helper; from the Python gate require (via AST) that each `test_` function body contain at least one `assert` or `pytest.raises`. A stronger version is a negative self-test: a gate that is compiled against a deliberately-widened shim type and is required to **fail**.

---

### P2-2 — `object.__setattr__` on the module rebinds a record class past the Python AST closure

**File:** `tools/o008_formal_cycle_admission_v1.py:1195-1215` (`_PYTHON_DYNAMIC_CALLS_V1`, `python_dynamic_binding_scan_v1`).

**Exact statement.** The scan rejects a `Call` whose `func` is a bare `Name` in `{exec, eval, compile, __import__, globals, locals, vars, setattr, delattr}`, and `Store`/`Del` subscripts on `*.modules`, `globals()`, `locals()`, `vars()`. `object.__setattr__(...)` is an `ast.Attribute` call, so it is matched by neither rule. Appending

```python
import sys as _s
object.__setattr__(_s.modules[__name__], 'TerminalObligationV1', int)
```

to `src/core/global_settlement_types_v1.py` is **ACCEPTED** (probe P13), while the equivalent `setattr(...)`, `globals()[...] =`, `exec(...)`, and plain rebinding are all rejected with specific codes. `type.__setattr__`, `builtins.setattr`, and `__dict__` mutation via a module reference are the same shape.

**Honest scope.** This is defence-in-depth, not an end-to-end bypass on its own: under `--replay` the Python gate's `test_state_containers_hold_exactly_the_record_types` and `test_terminal_record_runtime_fields_and_canonical_keys_are_exact` fail against a rebound name. It becomes real only in combination with **P2-1** (a vacuous gate), and it holds unconditionally for the default non-replay invocation, which still returns `ok=true, packet_admitted=true` with `proof_replay.status = NOT_RUN`.

**Reproduce:** `"$PY" /tmp/opus-c1dprime-exp/p4.py` → `[ACCEPTED] P13 object.__setattr__ on the module`.

**Required repair.** Reject any `Call` whose unparsed `func` ends in `__setattr__`, `__delattr__`, or `setdefault`/`update` on a module-valued expression, and any `Store` to an `ast.Attribute` whose base resolves to `sys.modules[...]`. Or state in the packet that the Python binding closure is AST-syntactic and that dynamic module mutation is caught by the runtime gate alone.

---

### P2-3 — The packet publishes a closure property (`serde imported only from serde`) that the checker does not enforce

**File:** `tools/o008_formal_cycle_admission_v1.py:550` (`INFORMATION_LOSS_BINDING_V1["static_closure"]`), surfaced verbatim in `docs/research/ZENODEX_O008_FORMAL_CYCLE_V1.json` at `v1_information_loss.binding.static_closure`.

**Exact statement.** The packet asserts as its static closure: *"…no field attributes; serde imported only from serde; crate root declares mod state once; manifest keeps default targets and registry dependencies"*. Per **P1-1**, "serde imported only from serde" is not enforced for the braced form, which is the form `state.rs` actually uses — the rule has never once fired on that line. "No field attributes" is also true only of the two record structs; the container carries `#[serde(deserialize_with = …)]` on ten fields, which is legitimate and separately constrained, but the sentence as written reads as covering the scanned surface.

This is the campaign's own discipline — a claim in an evidence packet must be true — applied to the closure description rather than to a `killed_by` field.

**Reproduce:** `"$PY" /tmp/opus-c1dprime-exp/p7.py` → the `_RUST_USE_RE` coverage table above.

**Required repair.** Fix the scanner (P1-1) so the sentence becomes true; if that is deferred, reword to "record structs carry no field attributes; the record containers carry only the closed `deserialize_with` attribute; unbraced serde imports are checked" and add a nonclaim naming the unpinned modules of the crate.

---

### P3-1 — `use crate::x as bounded_state_vec_deserializer_v1;` is accepted by the scan; it is neutralised only by a Rust name-resolution rule the closure never states

**File:** `tools/o008_formal_cycle_admission_v1.py:1543` (the `use` loop); probe N2.

**Exact statement.** Importing a foreign macro under the pinned macro's own name is accepted by admission. I compiled it: the local `macro_rules! bounded_state_vec_deserializer_v1` (whose body is pinned) wins, because a textual-scope `macro_rules!` definition takes precedence over a path-imported macro for the invocations that follow it, and `rust_lexical_closure_v1` independently requires depth-zero item macros to be defined before they are invoked. So the closure holds — but by an unstated fact about `rustc`, not by the checker. `cargo build` exit 0; the compiled container rejected `zz_shadow` as the pristine crate does.

**Required repair.** None strictly. If the macro-locality argument is to be self-contained, reject any `use` that binds a name equal to a `macro_rules!` name defined in the same file, and record the precedence rule in the closure docstring.

---

### P3-2 — A manual `Deserialize` impl for a record type in `state.rs` is accepted by the scan

**File:** `tools/o008_formal_cycle_admission_v1.py:1610` (`rust_container_deserializer_closure_v1`); probe N4.

**Exact statement.** Appending `impl<'de> Deserialize<'de> for OutboxStateV1 { … }` to `state.rs` is **ACCEPTED** by `project_packet_v1`. `rust_bounded_vec_closure_v1` has exactly this guard for `bounded_vec.rs` (`manual_deserialize`, `:1668`) and `state.rs` does not. It is closed by `rustc` — the derive already provides the impl, so a manual one is `error[E0119]` — but admission without `--replay` accepts source that does not compile, and the closure docstring claims the derive is the single decoding path.

**Required repair.** Apply the same `impl … Deserialize … for <record>` rejection to `state.rs` that `bounded_vec.rs` already has. One line.

---

### P3-3 — `mod` blocks inside `state.rs` are outside the depth-zero macro rule

**File:** `tools/o008_formal_cycle_admission_v1.py:1533` (`_brace_depth_at(code, match.start()) == 0`); probe M5.

`mod nested_evil { foreign!{ struct Hidden { a: u8 } } }` is accepted, because the invocation sits at depth 1. It is not weaponisable against the record names (an inner module cannot shadow a depth-zero item, and a `use` re-export of a colliding name is `E0255`), and the `fn <deserialiser>` regex scans the whole file including inner modules. Recorded for completeness; the closure docstring's "a `pub struct` at brace depth zero is the single definition Rust compiles for that name" remains true.

**Required repair.** None. Optionally reject `mod <name> { … }` in `state.rs` outright, as `rust_crate_root_closure_v1` already does for `mod state`.

---

### P3-4 — `Cargo.lock` content and the crate-selection surface are unconstrained by admission

**File:** `tools/o008_formal_cycle_admission_v1.py:1651-1712` (`rust_manifest_closure_v1`); probes L1, L2, L3.

`Cargo.lock` is pinned by hash but its content is never parsed: a zeroed serde checksum (L1) and a `source = "registry+https://evil.example/index"` (L2) both project cleanly. `rust_manifest_closure_v1` constrains dependency *form* (exact `=` versions, no `path`/`git`/`registry`/`package` keys) but not dependency *identity*: `evil-derive = "=0.1.0"` is accepted (L3), which is the one construct that could turn the braced-serde-import of P1-1 into a hostile `#[derive(Deserialize)]`. All three are closed at replay by `cargo --offline --locked` (a checksum mismatch or an uncached crate is a hard error), not by admission — so the guarantee is "the reviewer's cargo cache", not "the pinned bytes". `[profile.test]` is correctly rejected; `.cargo/config{,.toml}` at all three levels is correctly rejected at S, at HEAD, and in the worktree.

**Required repair.** None required. If cheap: parse `Cargo.lock` and require every `source` to be exactly `registry+https://github.com/rust-lang/crates.io-index`, and pin the allowed dependency name set alongside the version constraint. Add a nonclaim that `CARGO_HOME`, `RUSTUP_HOME`, and `RUSTUP_TOOLCHAIN` are passed through from the replaying host (`tools/o008_formal_cycle_shell_v1.py:38`), so registry cache contents are host-trusted; note that `RUSTUP_TOOLCHAIN` is bounded by the `rust_version` comparison to `1.87.0`, and `RUSTC` is *not* passed through.

---

## 3. Verification record

`PY="/home/trevormoc/Downloads/Autonomous Tau DEX/.venv/bin/python"`, cwd `/tmp/zenodex-formal-core-review-p-9056dac69` unless noted, cargo under `CARGO_TARGET_DIR=/tmp/zenodex-opus-c1dprime-cargo-target CARGO_INCREMENTAL=0` (deleted, 1.7 G reclaimed).

| # | Command | Exit | Key output |
|---|---|---|---|
| 1 | `git status --porcelain \| grep -v '^??'` | 1 (grep, empty) | **0 tracked changes**, before and after; 0 untracked shown; HEAD still `9056dac69` |
| 2 | `git diff-tree --no-commit-id --name-status -r HEAD^ HEAD` | 0 | exactly `M docs/research/ZENODEX_O008_FORMAL_CYCLE_V1.json`, `M …_V1.md` |
| 3 | `git diff --stat HEAD^^ HEAD^` | 0 | 12 files, **+1690 / −102**; 2 added (THV1 admission-v6, golden-v3), 10 modified, 0 deleted |
| 4 | `check_o008_formal_cycle_v1.py --root "$PWD"` | 0 | `ok:true, packet_admitted:true, current_applicable:true, current_source_drift:[], errors:[]`, `head==packet==9056dac69…`, `subject=6358da52f…`, replay `NOT_RUN` |
| 5 | `check_o008_formal_cycle_v1.py … --replay …` | 0 | `EXECUTED_PASS`, **15 runs, all exit 0**: lean_version 4.27.0; lean_direct_check `e3b0c442…`; lean_axioms_probe `theorems_probed=25`; lean_binding_gate 6; esso_validate `sha256:a4d1d07f6c9d…`; esso_verify_multi VERIFIED z3 4.15.4/cvc5 1.1.2 `esso_code_hash=7f80c6216be8…`; esso_gate 18; prior_restage_gate 136; python_version 3.12.3; **python_projection_gate 13; rust_projection_gate 7; rust_version cargo 1.87.0; rust_refinement_gate 41; python_golden_gate 35; rust_golden_gate 3** |
| 6a | `build_o008_formal_cycle_v1.py … --check --replay …` | 0 | `{"drift":[],"mode":"check","ok":true,"subject_commit":"6358da52f…"}` |
| 6b | `build_o008_formal_cycle_v1.py … --check` (no `--replay`) | 1 | `{"error":{"code":"CHECK_MODE_MISMATCH","detail":"committed author record is EXECUTED; this check runs NOT_RUN (use --replay accordingly)"},"ok":false}` — C1' P3-3 closed |
| 7 | `pytest -q` (4 files: checker, python gate, golden, lean gate) | 0 | **298 passed in 94.86 s** |
| 8 | `cargo test --offline --locked --test v1_projection_gate --test claimant_backing_guard_golden --test global_economic_state_effect_refinement` | 0 | **41 passed; 3 passed; 7 passed** |
| 9 | `cargo clippy --offline --locked --all-targets -- -D warnings` | 0 | clean |
| 10 | `lake env lean -DwarningAsError=true Proofs/GlobalClaimantCustodyRelationV1.lean` | 0 | no output |
| 11 | `check_test_hygiene_v1.py --base-ref fd409ba6f7… --json` | 0 | `ok:true, changed_path_count:39, critical_path_count:13, covered_critical_paths:13, evidence_packet_count:86, pytest_node_ids:343`, `selected_evidence_ids: [claimant-backing-guard-golden-v3, semantic-restage-v3, o008-formal-cycle-admission-v6]` |
| 12 | `ruff check` (4 tools) | 0 | `All checks passed!` |
| 13 | `mypy --strict` (4 tools) | 0 | `Success: no issues found in 4 source files` |

### Hand-recomputed pins at S5

`git cat-file blob HEAD^:<path> | sha256sum`, against the values in `docs/research/ZENODEX_O008_FORMAL_CYCLE_V1.json`:

| Path | Recomputed sha256 | In packet | Git blob recomputed / in packet | Match |
|---|---|---|---|---|
| `zk/global_settlement_abi_v1/src/bounded_vec.rs` | `eb4539f793405c0120c7e95424c51daea6c78b7c5b9584b7bfdbbcf63a0b3be6` | identical | `82b7dc7d766b54781bc57429821eb24e638ed0c3` / identical | **YES** |
| `tools/o008_formal_cycle_admission_v1.py` | `41927fd161cf6e8e7f7aa7ea7fb943813b822194983aedad3a582a73f68df49d` | identical | `d787c6fe4a93681673ae4c69ffae764b058ecd3e` / identical | **YES** |

All **28** source pins recomputed from S5 blobs: **0 mismatches**. All **26** pins in `THV1-20260901-o008-formal-cycle-admission-v6.json` and all **12** in `THV1-20260901-claimant-backing-guard-golden-v3.json`: **0 mismatches**. Neither packet pins either O-008 packet path, so the reference remains well-founded.

**Executing checker bytes equal S5** — all four recomputed from `HEAD^` blobs and identical to `report.executing_tools`:
`tools/check_o008_formal_cycle_v1.py 3b148d47c6…`, `tools/o008_formal_cycle_admission_v1.py 41927fd161…`, `tools/o008_formal_cycle_shell_v1.py 4f5360d2c1…`, `tools/scan_lean_proof_placeholders_v1.py 44a7c67142…`.

### Chain and topology

`git rev-list --parents -n1 HEAD` → `9056dac69… 6358da52f…` (exactly one parent). `git rev-list --parents -n1 HEAD^` → `6358da52f… fd59705426…` (S5's parent is the C2' receipt commit). `packet.subject_commit = 6358da52f…`, `subject_parent = fd59705426…`, `subject_tree = f218d3ad74… = git rev-parse HEAD^^{tree}`, `packet_commit_parent = 6358da52f…`, `packet_write_set` = exactly the two packet paths. All exact. Schema `zenodex/o008-formal-cycle-evidence/v3`; `hygiene_selection` is 25 rows, all naming `admission-v6`.

### `killed_by` verification (C2' P2-1), in `/tmp/opus-c1dprime-repo`

Six implementation mutations applied to `src/core/global_economic_state_effect_refinement_v1.py`; each declared node run alone:

| Mutation | Declared node | Result |
|---|---|---|
| drop the R1 branch | `…[one_atom_short_rejects]` | **1 failed** |
| drop the R2 branch | `…[open_terminal_one_atom_over_rejects]` | **1 failed** |
| `if total > MAX_ATOMS_V1:` → `if False:` | `…[rejects_entitlement_aggregate_overflow]` | **1 failed** |
| same edit | `…[rejects_custody_aggregate_overflow]` | **1 failed** |
| `status is OPEN` → `status is not None` | `…[ignores_drained_terminal_amount]` | **1 failed** |
| fold entitlements on a constant domain | `…[rejects_cross_domain_backing]` | **1 failed** |

### Adversarial probe matrix (39 probes)

Controls: unmutated snapshot accepted with and without the re-pin round-trip.

**Rejected as designed (24):** `RUST_CONTAINER_DESERIALIZER_DRIFT` ×6 (both C1' counterexamples, second local macro, `mod` shim, commented-out invocation, foreign-const macro argument, `use`-renamed fn), `RUST_CONTAINER_ATTRIBUTE_DRIFT` ×2 (extra `#[serde(default)]`, cross-named deserialiser), `RUST_FOREIGN_ITEM_MACRO` ×2, `RUST_MACRO_DEFINES_ITEM`, `RUST_SERDE_IMPORT_DRIFT` ×2, `RUST_EXTERN_CRATE_FORBIDDEN`, `RUST_GATE_CONTENT_DRIFT` ×3, `RUST_INCLUDE_FORBIDDEN` ×2, `CARGO_TARGET_OVERRIDE_FORBIDDEN`, `CARGO_CONFIG_PRESENT`, `PYTHON_DYNAMIC_BINDING_FORBIDDEN` ×3, `PYTHON_CLASS_REBOUND`, `PYTHON_CLASS_BASES_FORBIDDEN`, `PYTHON_CLASS_DECORATORS_DRIFT`, plus `PACKET_NON_ASCII` ×3, `PROMOTION_TOKEN_PRESENT` ×2, `REPLAY_ESSO_QUERY_COUNT_DRIFT`, `REPLAY_ESSO_QUERY_SET_DRIFT`.

**Accepted (survivors):** U1/U2/U3 braced `use` (**P1-1**, mounted end to end), B1 bounded-vec visitor pre-filter (**P1-2**, mounted end to end), G1/G3 vacuous gates (**P2-1**, mounted at both admission and replay), P13 `object.__setattr__` (**P2-2**), N2 macro `use`-alias (**P3-1**, compiler-neutralised — verified by compiling), N4 manual `Deserialize` impl (**P3-2**, compiler-neutralised by `E0119`), M5 nested-`mod` foreign macro (**P3-3**, not weaponisable), L1/L2/L3 lockfile and dependency-identity (**P3-4**, cargo-closed at replay), P8/P11 inert Python hooks (not findings).

---

## 4. Nonclaims and residual risks

- **P1-1 is mounted, not merely inferred.** I ran `project_packet_v1` under full attacker re-pinning, compiled the crate, ran its entire test suite and clippy, ran the three Rust replay targets at their exact recorded counts, and observed the compiled divergence against a pristine control. What I did **not** build is the Git S′/P′ chain and a rebuilt packet. Since admission is projection + topology + pin equality, and re-pinning simulates the topology/pin half exactly, I judge the chain to follow — but that step is inference.
- I did **not** attempt to weaponise the braced **serde** import (U1), which would need a hostile `#[derive(Deserialize)]` from an added proc-macro crate. The manifest closure permits any exact-version registry crate (L3), but `--offline --locked` replay would fail unless the crate is already in the replaying host's cargo cache. I did not test that path; the bounded-vec redirect needs no new dependency and is sufficient.
- **The pinned Rust surface is 4 of the crate's 86 `src/*.rs` modules.** Pinned: `state.rs`, `lib.rs`, `bounded_vec.rs`, `global_economic_state_effect_refinement.rs` (plus `Cargo.toml`, `Cargo.lock`, and the two `tests/*.rs` gates). Unpinned: `canonical.rs`, `release.rs`, and 80 others. `check_current_applicability_v1`'s worktree-equals-S guarantee covers only the 28 pinned paths. Nothing in the packet says this.
- The Rust seeded property test draws its seed from `SystemTime` ⊕ pid, so the replay's `7 passed` is not a bit-deterministic artifact of fixed inputs. This is the right design for a property test and the seed is printed, but it is worth stating that one replay command is non-deterministic by construction.
- Replay passes through `PATH, HOME, ELAN_HOME, TMPDIR, CARGO_HOME, RUSTUP_HOME, RUSTUP_TOOLCHAIN` from the replaying host. `RUSTC` is not passed through and the toolchain version is compared, so the exposure is the contents of the host's cargo registry cache and elan/rustup trees — host trust, correctly outside the packet's reach, but currently unstated.
- `EXECUTED_PASS` still does not run the 298 admission-checker tests or `tools/check_test_hygiene_v1.py`; both remain source-pinned only. The circularity argument against replaying the checker's own suite stands.
- I did **not** re-audit the claimant-backing guard's arithmetic, the twelve-lane reconciliation, the sidecar contract, or `ZENODEX_O008A_DEPENDENCY_POLICY_BLOCKER_V1.json`. I took the C1, C1' and C2' receipts as the specification and independently re-derived every finding I report.
- O-008 remains open at 0/12 value-movement gates; the all-lane allocation certificate is unimplemented and unmounted; ESSO remains a bounded one-asset/two-domain/two-claimant model; Lean establishes no finite-width runtime parity, cryptographic binding, or settlement authority. The packet's own nonclaims state all of this accurately.
- My grade is advisory and grants no authority.

---

## 5. User decisions — honored

All six hold, and I checked each rather than assuming.

1. **Reserves are the claimant-free term.** `derive_claimant_backing_view_v1` reads only `state.custody`, `state.liabilities`, `state.terminal_obligations`; the view's five columns are `schema`, `custody_by_control_domain`, `entitlements_by_control_domain`, `entitlements_by_claimant`, `open_terminals_by_claimant`. The golden-v3 mutation "count reserves or balances as claimant backing" is killed by `test_view_has_no_reserve_or_balance_column`. Lean's `necessaryRelation_independent_of_reserves` and `exactCurrentProfileCustody_independent_of_reserves` are declared definitional and counted separately.
2. **Control-domain vocabulary in new code; V1 wire names byte-stable.** S5 touches no V1 wire field. `state.rs` and `src/core/global_settlement_types_v1.py` are unchanged by S5 (`git diff --stat HEAD^^ HEAD^` lists neither); the new code — `rust_container_deserializer_closure_v1`, `rust_bounded_vec_closure_v1`, `_check_projection_gates`, the two gate files — uses control-domain vocabulary throughout, while `TERMINAL_FORBIDDEN_FIELDS_V1` still enumerates the legacy `custody_domain`/`custody_principal` names as *forbidden wire keys*, which is the correct direction.
3. **O-008A unattested.** `ZENODEX_O008A_DEPENDENCY_POLICY_BLOCKER_V1.json` is untouched by S5/P5 and is not referenced from the O-008 packet.
4. **UP-01..UP-20 unresolved and never fixture-selected.** `grep -o 'UP-[0-9]*'` over the packet JSON returns nothing.
5. **Authority NONE.** All seven authority fields are `"NONE"`; `whole_value_movement_safe: false`; `value_movement_gates_closed: 0` of 12. Identical under every mutation I mounted.
6. **`formal_core_complete` false.** Confirmed in the checker report and the committed packet; `o008_status: "OPEN_EXACT_ALL_12_RECONCILIATION_MISSING"`. The commit message states plainly that the committed packet is stale at S5 by construction.

---

## 6. Recommendation

Do not land as the closing candidate of this lane. Three edits get it to A-, and none is large:

1. **Tokenise `use`** (P1-1, ~15 lines) and add a self-test asserting the scan sees all four of `state.rs`'s imports. Then either qualify the deserialiser path inside the pinned macro body or pin the whole crate `src/` tree — the first is one token.
2. **Pin `bounded_vec.rs` as a whole normalised template** rather than three substrings (P1-2, a constant plus one comparison).
3. **Require the gate tests to assert** (P2-1): each pinned Rust test body must name its `const` table and contain an `assert`; each pinned Python test body must contain an `assert` or `pytest.raises`.

P2-2 (`__setattr__`) and P3-2 (manual `Deserialize` impl in `state.rs`) are one line each and worth taking in the same pass. P2-3 resolves itself once P1-1 is fixed. With those closed I would expect this to reach A-: the evidence discipline in C1'' — 15 replay commands, exact toolchain identity, verified `killed_by` attributions, a real necessity theorem, honest nonclaims for every shape-checked value — is already at that level, and the remaining defects are all in one place: the lexical scanner's coverage of its own claims.

Artefacts kept: `/tmp/opus-c1dprime-exp/` (harness + probes p0–p7), `/tmp/opus-c1dprime-cargo/` (the compiling P1-1 counterexample crate, ~3.4 M), `/tmp/opus-c1dprime-repo/` (shallow clone used for the `killed_by` mutations, 133 M), `/tmp/opus-c1dprime-out/` (checker JSON, pytest and hygiene output). Cargo target dir deleted.
