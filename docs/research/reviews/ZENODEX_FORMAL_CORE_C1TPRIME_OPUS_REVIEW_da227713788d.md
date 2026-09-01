# Opus review receipt: candidate C1''' at P = da227713788dac83853f92177892b14268433d6a

Reviewer: Opus 5 (`Agent(model: "opus")`, read-only, detached worktree `/tmp/zenodex-formal-core-review-p-da2277137`; adversarial copies under `/tmp/opus-c1tprime-*`).
Date: 2026-09-01. Subject: P = da227713788dac83853f92177892b14268433d6a (tree 5bb7890a80e6c18b5ad6b35d1e5b8fd697bd5e0e), S = fee3b08a1f8511ad250cff5bacc77dae24d222c7, parent R5 = 8d822a5b126f592e97fb6a626208a08dabeccb31.
Verdict: Grade C, REVISE. Disposition: P1-1 (attribute-prefixed use statements), P1-2 (crate-root module rebinding), P2-1 (structural Python store closure), P2-2 (static_closure sentence and nonclaim), P3-1 (raw gate hash), P3-2 (bounded_vec whole-file pin and unit-test replay), and P3-3 (serde prelude exactness) are repaired by candidate C1'''' (the next source commit after this receipt), together with the Codex C1'' findings recorded in `ZENODEX_FORMAL_CORE_C1DPRIME_CODEX_REVIEW_9056dac69044.md`. The grade is advisory and grants no authority.

Verbatim report follows (sha256 of the reviewer's file: 50c22b1d95d1e16bf4eaa1a7f6e197cd1e176c0fc9aa49855b6d8a5623b1542f; the adversarial copies it names are not part of the repository).

---

# Opus review receipt: candidate C1''' at P7 = da227713788dac83853f92177892b14268433d6a

- **Reviewer**: Opus 5, independent reviewer. Read-only, detached worktree `/tmp/zenodex-formal-core-review-p-da2277137`.
- **Date**: 2026-09-01.
- **P7 (packet commit)**: `da227713788dac83853f92177892b14268433d6a`, tree `5bb7890a80e6c18b5ad6b35d1e5b8fd697bd5e0e`.
- **S7 (source commit)**: `fee3b08a1f8511ad250cff5bacc77dae24d222c7`, tree `37708bf5752d409f3f2d2d60fe78740d85ee25f4`.
- **S7 parent**: `8d822a5b126f592e97fb6a626208a08dabeccb31` (Opus C1'' receipt, grade C), preceded by `506ee5289fc71877710439c77f80188cd514497b` (C3 packet).
- **This review is advisory and grants no authority.**

Worktree left untouched: `git status --porcelain` empty (tracked **and** untracked), HEAD still `da2277137`, no `target/` directory anywhere under the worktree. Nothing written under `/dev/shm`; nothing written inside the worktree or the primary repository. `CARGO_TARGET_DIR=/tmp/zenodex-opus-c1tprime-cargo-target` deleted (1.6 G reclaimed). Adversarial work lives in `/tmp/opus-c1tprime-exp` (in-process probe harness `harness.py` + `p0.py`…`p5.py`) and `/tmp/opus-c1tprime-cargo` (a standalone crate copy). The C3 review receipt is not in P7's ancestry — it is at `3fe6a21bd`, a child of P7 — so I read it with `git show 3fe6a21bd:docs/research/reviews/ZENODEX_FORMAL_CORE_C3_OPUS_REVIEW_506ee5289fc7.md`.

---

## 1. Grade: **C — REVISE**

**Everything mechanical about this candidate is correct, and most of the repair work is real and verified adversarially.** The chain is exact (P7 has one parent, S7; S7 has one parent, the C1'' receipt; P7's diff is exactly the two packet paths). Both hand-recomputed pins match; all 28 packet source pins and all 26 THV1-v8 pins equal S7 bytes; all 60 `killed_by` node ids resolve to collected tests; the executing checker hash equals the S7 blob. 296 Python tests pass (276 + 20), cargo `v1_projection_gate` reports 7, clippy `-D warnings` is clean from a cleaned package, ruff and `mypy --strict` are clean, the checker admits with and without `--replay`, the builder `--check --replay` reports `{"drift":[],"ok":true}`, and all fifteen replay commands are `EXECUTED_PASS` with the recorded values (`ir_hash sha256:91852626…`, fingerprint `256b0dcb…`, ESSO gate 20, z3 4.15.4 / cvc5 1.1.2 `VERIFIED`). I reproduced the ESSO ir-hash and fingerprint independently, outside the checker.

**Four of the five C1'' findings and both C3 findings are genuinely closed, and I confirmed each by running it.** The `use` scan now sees **all four** of `state.rs`'s statements and **all six** of `bounded_vec.rs`'s (it saw one before); every C1'' P1-1 named vehicle — braced, nested-braced, aliased, `pub(crate)`, `self::`, `super::`, `as _`, leading `::` — is now rejected with a specific code, as are `use` statements inside `mod` blocks and function bodies. `bounded_vec.rs` is a whole-template pin: the exact C1'' P1-2 vehicle (a `serde_json::Value` pre-filter kept beside the pinned loop under `if false`) is now `RUST_BOUNDED_VEC_DRIFT`, and I could not defeat the `#[cfg(test)] mod tests` exclusion (a second module, an uncfg'd module, code after the module, and braces inside strings are all rejected). Both gate content hashes recompute exactly from the S7 blobs; the emptied-body gates that C1'' P2-1 mounted are now `RUST_GATE_CONTENT_DRIFT`; a comment-only edit correctly falls through to `THV1_PIN_DRIFT`. The C3 P2-1 notes sentence is now scoped **and true** — I re-ran the ESSO kernel and confirmed `deposit_reserve` accepts from GENESIS with all four binding flags false while `open_claim` with any one flag false is a `StepError` — and C3 P2-2's `ESSO_ACTIONS_DRIFT` now has two negative cases that collect and pass.

**What holds the grade at C is that the headline claim of the commit — binding the V1 projection to its compiled decoding path — again does not hold adversarially, and this time it fails by two independent routes, both of which I mounted end to end.** (1) `_RUST_USE_RE`'s statement boundary is `^` (MULTILINE) or a lookbehind on `[;{}]`. A `]` is not a boundary, so **any attribute on the same line as a `use`** hides that statement from the scan completely — `#[allow(unused_imports)] use crate::canonical::deserialize_bounded_vec_v1;` is accepted, and so are `#[rustfmt::skip]`, `#[deprecated]` and `#[doc = "x"]` prefixes, and the same trick smuggles a glob import into `state.rs` past `RUST_GLOB_IMPORT_FORBIDDEN`. (2) Independently of the regex, **nothing pins `mod bounded_vec;` in the crate root**: `rust_crate_root_closure_v1` counts only `mod state;`, and `pub use <module>::*` is explicitly permitted there, so replacing `mod bounded_vec;` with `mod evil_shim; use evil_shim::bounded_vec;` rebinds what `crate::bounded_vec` means while `state.rs` **and** `bounded_vec.rs` stay byte-identical. Both routes compile, pass all 52 test binaries, report the exact recorded replay counts 7/41/3, survive `cargo clippy --all-targets -- -D warnings`, and make the compiled `GlobalEconomicStateV1` accept a terminal row carrying an extra key that the pristine crate rejects with `unknown field 'zz_shadow'`.

The second route matters more than the first: it is not a regex bug. It says the closure's unit of trust is a set of five files inside an ~85-module crate whose module graph is unconstrained, and it means the C1''' repair direction (fix the scanner) is necessary but not sufficient. The packet's `static_closure` sentence is correspondingly still false, and C1''' *added* a false clause to it ("record containers decode only through the pinned local macro and the whole-template-pinned bounded_vec.rs") — so C1'' P2-3 is not closed. C1'' P2-2 is closed only for the spellings it names: a plain `sys.modules[__name__].TerminalObligationV1 = int` is still accepted.

This is a materially better candidate than C1'': two of the three mounted C1'' defects are dead, the gates are no longer vacuous-able, and the model claim is now accurate. But the defect class Codex graded C1 at C for, and that I graded C1' and C1'' at C for, is reachable a fourth and fifth time — once by a one-line edit, once with no edit at all to either pinned Rust source — so the grade cannot rise.

### Per-finding disposition

**Opus C1'' findings (grade C):**

| Finding | Claim | Status | Evidence |
|---|---|---|---|
| **P1-1** | Braced `use` invisible to the scan; redirects the deserialiser | **CLOSED for the named class; the defect class is OPEN by a new route** | Scan now sees 4/4 state.rs and 6/6 bounded_vec.rs statements; U1/U2/U3 and 11 further forms all rejected with specific codes. But an attribute on the same line still hides the statement entirely — see **P1-1** below, mounted end to end. |
| **P1-2** | bounded_vec.rs pinned only by three substrings | **CLOSED** | `BOUNDED_VEC_LIBRARY_TEMPLATE_V1` is a whole normalised-template equality. The exact C1'' vehicle → `RUST_BOUNDED_VEC_DRIFT`; the `#[cfg(test)] mod tests` exclusion resisted four attacks. Residuals: string literals and the test module's own contents are free (**P3-2**, **P3-3**). |
| **P2-1** | Gate bodies unconstrained; emptied gates admit and pass | **CLOSED** | `RUST_GATE_NORMALIZED_SHA256_V1` / `PYTHON_GATE_AST_SHA256_V1`; both recomputed by hand from S7 and matching. Emptied-body Rust gate → `RUST_GATE_CONTENT_DRIFT`; a one-assertion-removed Python gate → `PYTHON_GATE_CONTENT_DRIFT`; comment-only edits fall through to `THV1_PIN_DRIFT`. Residual: the Rust hash is computed on stripped code, so string literals are free (**P3-1**). |
| **P2-2** | `object.__setattr__` rebinds a record class past the AST closure | **PARTIALLY CLOSED** | `object.__setattr__`, `type(m).__setattr__`, `m.__dict__.update`, `vars(m)[…]` all → `PYTHON_DYNAMIC_BINDING_FORBIDDEN`. **`sys.modules[__name__].X = int`, a two-step attribute store, `importlib.import_module(__name__).X = int`, `getattr(m,'__dict__')[…] = int` and `del m.X` are still accepted** — see **P2-1** below. |
| **P2-3** | Packet publishes a closure property the checker does not enforce | **NOT CLOSED** | The sentence was rewritten and lengthened, but it is still false for attribute-prefixed `use` statements, and the newly added clause "record containers decode only through the pinned local macro and the whole-template-pinned bounded_vec.rs" is falsified by **P1-2** below. See **P2-2**. |

**Opus C3 findings (grade A-):**

| Finding | Claim | Status | Evidence |
|---|---|---|---|
| **P2-1** | Pinned model notes assert a property C3 falsified | **CLOSED** | Notes now read "…every accepted claimant transition (open_claim, drain_claim) imply all four bindings; deposit_reserve accepts without bindings because it reads and writes no claimant, custody, or terminal coordinate." I verified both halves against the ESSO kernel and against the action's `updates` (it writes only `reserve_d0`/`reserve_d1`). The phrase "deposit_reserve accepts without bindings" is pinned in the lexical-surface test. Model sha `d7b547e3…`, ir_hash `sha256:91852626…`, both re-derived. |
| **P2-2** | `ESSO_ACTIONS_DRIFT` has no negative test | **CLOSED** | `test_subject_mutations_reject_projection[extra_esso_action]` and `[renamed_esso_action]` collect and pass. |
| **P3-1** | `deposit_reserve` effects indistinguishable from `open_claim` | Carried, correctly scoped | Unchanged by design (V1 wire names byte-stable — a user decision). The state surface disambiguates. |
| **P3-2** | Mutant harness accepts a non-unique needle | Carried (no repair required) | Unchanged; `count >= 1` still. |
| **P3-3** | ir-hash sensitivity test omits its own control | Carried (no repair required) | Unchanged. |

---

## 2. Findings

### P0 — none

**No finding at this severity.** No authority escalation, value movement, production promotion, or `formal_core_complete = true` path exists in this candidate. `claim_ceiling` is emitted from module constants and was identical under every mutation I mounted: all seven authorities `NONE`, `formal_core_complete: false`, `whole_value_movement_safe: false`, `value_movement_gates_closed: 0` of 12, `o008_status: OPEN_EXACT_ALL_12_RECONCILIATION_MISSING`. No reject path mutates state. Reserves remain the claimant-free term and cannot enter the claimant-backing view.

---

### P1-1 — An attribute on the same line as a `use` hides the statement from the import scan entirely; the compiled container is widened and every replay command stays green

**Files:** `tools/o008_formal_cycle_admission_v1.py:623` (`_RUST_USE_RE`), `:1560-1572` (the `use` loop inside `rust_lexical_closure_v1`); `zk/global_settlement_abi_v1/src/state.rs:3`.

**Exact statement.** The statement boundary is

```python
_RUST_USE_RE: Final = re.compile(r"(?:^|(?<=[;{}]))\s*(?:pub(?:\([^)]*\))?\s+)?use\s+([^;]+);", re.MULTILINE)
```

The boundary alternatives are a line start (MULTILINE `^`) or a lookbehind on `;`, `{`, `}`. A `use` preceded on the **same line** by an attribute is preceded by `]`, which is neither — so the statement is not matched, and *every* rule in the loop (`RUST_SERDE_IMPORT_DRIFT`, `RUST_BOUNDED_VEC_IMPORT_DRIFT`, `RUST_GLOB_IMPORT_FORBIDDEN`) is defeated at once. `strip_rust_noncode_v1` blanks comments and strings but leaves attributes intact, so this is not a comment artefact. Four attribute spellings work (`#[allow(...)]`, `#[rustfmt::skip]`, `#[deprecated]`, `#[doc = "x"]`); `#[cfg(...)]` is correctly rejected elsewhere.

The C1''' repair fixed the *consuming*-boundary half of C1'' P1-1 (consecutive statements) and the brace-group half. It did not make the boundary set complete.

**Weaponised.** Change `state.rs:3` from
`use crate::bounded_vec::deserialize_bounded_vec_v1;` to
`#[allow(unused_imports)] use crate::canonical::deserialize_bounded_vec_v1;`
and put a faithful copy of the pinned visitor in `src/canonical.rs` (one of the crate's ~85 unpinned `src/*.rs` modules) with one added line, `object.remove("zz_shadow")`, before `T::deserialize(row)`. The pinned macro body — checked byte-for-byte — expands to `deserialize_bounded_vec_v1::<D, $row, $maximum>(deserializer, $label)`; *which* function that names is decided entirely by the import the scanner cannot see.

**Results (all mounted, not inferred):**

| Property | Result |
|---|---|
| `project_packet_v1` on the edited `state.rs`, full attacker re-pinning | **ACCEPTED** (`p1.py` probe A1) |
| Control: the same attribute on its own line | **rejected** — `RUST_BOUNDED_VEC_IMPORT_DRIFT` (probe A1c) |
| Diff to the pinned `state.rs` | **one line**; `bounded_vec.rs`, `lib.rs` byte-identical |
| `cargo test --offline --locked` (whole crate) | **52 test binaries, 0 failures** |
| `cargo test … --test v1_projection_gate` | **7 passed** (exact recorded count) |
| `cargo test … --test global_economic_state_effect_refinement` | **41 passed** (exact) |
| `cargo test … --test claimant_backing_guard_golden` | **3 passed** (exact) |
| `cargo clippy --offline --locked --all-targets -- -D warnings` | **exit 0** |
| Compiled `GlobalEconomicStateV1` on a recorded state whose terminal row carries `zz_shadow` | **`DIVERGENCE: widened terminal row ACCEPTED; rows=1`** |
| Same input, pristine crate (control) | ``CONTROL: rejected: unknown field `zz_shadow`, expected one of `obligation_id`, `lane_id`, `claimant`, `asset`, `amount_atoms`, `status` `` |

The seeded property test cannot catch it: its generated keys have the form `k_%016x`, and the four `TERMINAL_FORBIDDEN`/`OUTBOX_FORBIDDEN` names are enumerated in the pinned, attacker-readable gate, so a filter keyed on any other name survives all seven tests. The consequence is a wire-schema widening: two distinct V1 encodings decode to the same state in Rust while Python rejects one of them — a canonicalisation and cross-language parity break directly under `v1_information_loss`.

**Reproduce:**
```bash
PY="/home/trevormoc/Downloads/Autonomous Tau DEX/.venv/bin/python"
cd /tmp/opus-c1tprime-exp && "$PY" p1.py
#   [ACCEPTED] A1 #[allow(unused_imports)] use crate::canonical::deserialize_bounded_vec_v1;  (ONE line)
#   [rejected] A1c control: same attribute on its own line
#   [ACCEPTED] A2 same trick on the serde import
#   [ACCEPTED] A5 same trick hides a glob import in state.rs
#   [rejected] A5c control: glob on its own line
#   [ACCEPTED] A8 #[rustfmt::skip] / A9 #[deprecated] / A10 #[doc = "x"]
# compiled half (crate copy; nothing written in the worktree):
cd /tmp/opus-c1tprime-cargo/zk/global_settlement_abi_v1
export CARGO_TARGET_DIR=/tmp/opus-c1tprime-target CARGO_INCREMENTAL=0
sed -i '3s|.*|#[allow(unused_imports)] use crate::canonical::deserialize_bounded_vec_v1;|' src/state.rs
cargo test --offline --locked            # 52 binaries, 0 failures
cargo test --offline --locked --test opus_probe -- --nocapture
#   DIVERGENCE: widened terminal row ACCEPTED; rows=1
```

**Required repair.** Do not rely on a regex boundary. Tokenise item positions from the stripped code: scan forward from every `use` keyword token whose preceding non-whitespace context is a statement boundary **or an attribute group**, and read to the terminating `;` at brace depth zero. Cheapest sound form: strip attribute groups (`#[...]`, `#![...]`) to blanks *before* the `use` scan, exactly as comments are stripped, so the boundary before a `use` is always `^`, `;`, `{` or `}`. Add a self-test asserting that `state.rs`'s statement count equals its `\buse\s` token count under an attribute-prefixed variant, not only under the shipped file. Note that this repair alone does **not** close **P1-2**.

---

### P1-2 — `mod bounded_vec;` is not pinned in the crate root: `crate::bounded_vec` can be rebound to an unpinned module while both pinned Rust sources stay byte-identical

**Files:** `tools/o008_formal_cycle_admission_v1.py:1732-1741` (`rust_crate_root_closure_v1`), `:1565-1567` (the crate-root glob exception); `zk/global_settlement_abi_v1/src/lib.rs:13`.

**Exact statement.** `rust_crate_root_closure_v1` constrains exactly two things: that `mod state;` appears once, and that there is no inline `mod state { … }`. Every other module declaration in the crate root — including `mod bounded_vec;` — is unconstrained, and `pub use <ident>::*;` is explicitly allowed there (needed because `lib.rs` ships 70 such globs). `state.rs`'s pinned import `use crate::bounded_vec::deserialize_bounded_vec_v1;` therefore resolves through a crate-root name that the closure never fixes. Rewriting

```
mod bounded_vec;
```
as
```
mod evil_shim;
use evil_shim::bounded_vec;
```

with `src/evil_shim.rs` declaring `pub(crate) mod bounded_vec { pub(crate) fn deserialize_bounded_vec_v1<…> … }` makes `crate::bounded_vec` name the hostile module. (A private `use` at the crate root is visible to all descendant modules, so `state` resolves it.) The pinned `bounded_vec.rs` becomes an orphan file that is never compiled — and it still hashes exactly, because the closure checks its bytes, not its reachability.

**Results (all mounted):**

| Property | Result |
|---|---|
| `project_packet_v1` on the edited `lib.rs` | **ACCEPTED** (`p5.py` probes L1, L2, L4; L3 — bare deletion — also accepted) |
| Diff to `state.rs`, `bounded_vec.rs`, `canonical.rs` | **byte-identical, all three** |
| Diff to `lib.rs` | **two lines** (one replaced, one added) plus one new unpinned file |
| `cargo test --offline --locked` | **52 test binaries, 0 failures** |
| `v1_projection_gate` / `global_economic_state_effect_refinement` / `claimant_backing_guard_golden` | **7 / 41 / 3 passed** (all exact) |
| `cargo clippy --offline --locked --all-targets -- -D warnings` | **exit 0** |
| Compiled `GlobalEconomicStateV1` with `zz_shadow` on a terminal row | **`DIVERGENCE: widened terminal row ACCEPTED; rows=1`** |

This route is independent of **P1-1**: it survives any repair to the `use` regex, because the offending `use` (`use evil_shim::bounded_vec;`) binds a *module* name, which no rule inspects.

**Reproduce:**
```bash
cd /tmp/opus-c1tprime-exp && "$PY" p5.py
#   [ACCEPTED] L1 drop `mod bounded_vec;`, bind the name from an unpinned module
#   [ACCEPTED] L2 same via `pub use`   [ACCEPTED] L3 delete outright   [ACCEPTED] L4 glob re-export
# compiled half: /tmp/opus-c1tprime-cargo/zk/global_settlement_abi_v1/src/{lib.rs,evil_shim.rs}
```

**Required repair.** Pick one:
1. Fix the binding at the use site rather than the import: change the pinned macro body to call `crate::bounded_vec::deserialize_bounded_vec_v1::<D, $row, $maximum>(…)` by absolute path, and additionally require in the crate root exactly one `mod bounded_vec;` declaration with no crate-root binding of that name (mirroring the existing `mod state` rule). This is the smallest change that closes both **P1-1** and **P1-2** at once, because it removes the import from the trust path entirely.
2. Or pin the crate-root module graph: require that every path segment named in a pinned module's `use` resolves to a `mod <name>;` declaration in the crate root, and reject any crate-root `use` or glob that binds a name equal to a pinned module.
3. If neither is taken now, the packet must say plainly that the static closure covers five files of ~85 in the crate, that the crate-root module graph is unconstrained, and that the compiled binding rests on the two projection gates alone.

---

### P2-1 — A plain attribute store on the module still rebinds a pinned record class past the Python AST closure

**File:** `tools/o008_formal_cycle_admission_v1.py:1209-1212` (`_PYTHON_DYNAMIC_ATTRIBUTES_V1`), `:1224` (the new rule).

**Exact statement.** The new rule rejects any `ast.Attribute` whose `.attr` is in `{__setattr__, __delattr__, __dict__, __class__, __builtins__, __loader__, __spec__}`. That is a rule about the *spelling of the accessor*, not about the *target of the store*. An assignment whose target is an `ast.Attribute` with an ordinary `.attr` is matched by nothing: the `ast.Subscript` rule at `:1226` fires only when the subscript itself carries `Store`/`Del` context, and in `sys.modules[__name__].X = int` the subscript is in `Load` context. Appending any of the following to `src/core/global_settlement_types_v1.py` is **ACCEPTED**:

```python
import sys as _s
_s.modules[__name__].TerminalObligationV1 = int          # accepted
```
```python
import sys as _s
_m = _s.modules[__name__]; _m.TerminalObligationV1 = int  # accepted
```
```python
import importlib as _i
_i.import_module(__name__).TerminalObligationV1 = int     # accepted
```
```python
import sys as _s
getattr(_s.modules[__name__], '__dict__')['TerminalObligationV1'] = int   # accepted
```
```python
import sys as _s
del _s.modules[__name__].TerminalObligationV1             # accepted
```

while `object.__setattr__(…)`, `type(m).__setattr__(…)`, `m.__dict__.update(…)`, `vars(m)[…] = …`, `setattr`, `globals()[…] = …` and `exec` are all rejected with `PYTHON_DYNAMIC_BINDING_FORBIDDEN`.

**Honest scope.** This is defence-in-depth, not an end-to-end bypass on its own, and the scope is unchanged from C1'' P2-2: a module-level rebind executed at import time is caught under `--replay` by the Python gate, whose `from src.core.global_settlement_types_v1 import TerminalObligationV1` binds the rebound object and whose `dataclasses.fields(...)`, defining-module and container-annotation assertions then fail. It holds unconditionally for the default non-replay invocation, which still returns `ok=true, packet_admitted=true` with `proof_replay.status = NOT_RUN`. I reasoned this runtime consequence from Python import semantics rather than executing the gate against a mutated repository copy — that is a nonclaim, recorded in §4.

**Reproduce:** `cd /tmp/opus-c1tprime-exp && "$PY" p4.py`.

**Required repair.** Reject stores and deletes whose target is an `ast.Attribute` — i.e. add `isinstance(node, (ast.Assign, ast.AugAssign, ast.AnnAssign, ast.Delete))` handling that walks the targets and rejects any `ast.Attribute` target whose base is not `self` — or, more simply for these modules, reject **every** `ast.Attribute` in `Store`/`Del` context at module scope. Also add `getattr`/`setattr` to the forbidden call set for the pinned type modules (the gate exemption at `:1216` already carves out what the gate needs). If the class is deliberately left open, say so in a nonclaim: "the Python binding closure is AST-syntactic; dynamic module mutation is caught by the runtime gate alone."

---

### P2-2 — The packet's `static_closure` sentence is still not enforced, and C1''' added a clause to it that is false

**File:** `tools/o008_formal_cycle_admission_v1.py:553-565` (`INFORMATION_LOSS_BINDING_V1["static_closure"]`), surfaced verbatim at `docs/research/ZENODEX_O008_FORMAL_CYCLE_V1.json` → `v1_information_loss.binding.static_closure` and at `docs/research/ZENODEX_O008_FORMAL_CYCLE_V1.md:95`.

**Exact statement.** The sentence now reads, in part:

> "… use statements expanded through brace groups and aliases with serde names bound only from serde and the bounded-vec deserialiser bound only from crate::bounded_vec; no glob imports in the scanned modules; record containers decode only through the pinned local macro and the whole-template-pinned bounded_vec.rs; crate root declares mod state once …"

Three problems:
1. "serde names bound only from serde", "the bounded-vec deserialiser bound only from crate::bounded_vec" and "no glob imports in the scanned modules" are all false for an attribute-prefixed `use` (**P1-1**). The C1'' P2-3 finding is therefore restated in longer form, not closed.
2. "record containers decode only through the pinned local macro and the whole-template-pinned bounded_vec.rs" is a **new** clause introduced by C1''' and is falsified by **P1-2**: the containers can decode entirely through an unpinned module while `bounded_vec.rs` hashes exactly. Adding a false clause to a claim sentence is the failure mode this campaign exists to prevent.
3. No `nonclaims` entry discloses that the Rust closure covers five files of an ~85-module crate, or that the crate-root module graph outside `mod state` is unconstrained. (I read all ten nonclaims; none mentions the crate's unpinned modules.)

The "crate root declares mod state once" clause is true and enforced — it is the presence of that clause, and the absence of any analogue for `bounded_vec`, that makes **P1-2** reachable.

**Reproduce:** `"$PY" -c "import json;print(json.load(open('docs/research/ZENODEX_O008_FORMAL_CYCLE_V1.json'))['v1_information_loss']['binding']['static_closure'])"` alongside `p1.py` and `p5.py`.

**Required repair.** Make the sentence true by taking the **P1-2** repair (option 1 closes both clauses at once), and delete or requalify the decode-path clause until it is. If the repairs are deferred, the sentence must be cut back to what is actually checked and a nonclaim added naming the unpinned modules and the unconstrained crate-root module graph.

---

### P3-1 — The Rust gate's normalised content hash is computed on stripped code, so every string literal in the gate is free

**File:** `tools/o008_formal_cycle_admission_v1.py:1996` (`sha256_hex_v1(_normalized(rust_code)…)`); `rust_code` is the return of `rust_lexical_closure_v1`, i.e. `strip_rust_noncode_v1` output with all string, raw-string and char literals blanked.

**Exact statement.** `RUST_GATE_NORMALIZED_SHA256_V1` pins token structure but not string content. The four `const [&str; N]` tables are separately pinned from the **raw** source by `_rust_str_array`, so those are safe; everything else is not. Accepted mutations include weakening `error.to_string().contains("unknown field")` to `contains("")`, collapsing the seeded key space from `format!("k_{value:016x}")` to a single constant key, and rewriting the `json!` fixture payload values. The Python gate does not have this gap: `ast.dump` includes `Constant` values, so its string literals are covered.

**Honest scope.** I could **not** turn any of these into a widening. `assert_unknown_field` still requires `from_value::<T>(value).err()` to be `Some`, and `terminal_record_serialises_fields_in_declared_order` still requires the base fixture to decode, so the record- and container-level rejection assertions remain live even with the substring check neutered. The realisable harm is a reduction in the seeded property test's coverage — which, as C1'' established, was already unable to catch a filter keyed on a name outside the pinned tables.

**Reproduce:** `cd /tmp/opus-c1tprime-exp && "$PY" p3.py` → `[ACCEPTED] S1`, `[ACCEPTED] S2`.

**Required repair.** None strictly required, given the scope above. If cheap: hash `_normalized(text)` of the **raw** decoded source for the gate (strings included) instead of the stripped code — the gate file has no reason to tolerate a string edit — or add the two remaining semantic strings (`"unknown field"`, the seeded-key format) to the pinned-constant set the way the four tables already are.

---

### P3-2 — `bounded_vec.rs`'s `#[cfg(test)] mod tests` is both unpinned and never executed by any replay command

**Files:** `tools/o008_formal_cycle_admission_v1.py:1725-1729` (the exclusion); `zk/global_settlement_abi_v1/src/bounded_vec.rs:63`.

**Exact statement.** The template pin deliberately excludes the `#[cfg(test)] mod tests { … }` block, so its nine unit tests (including `oversized_exact_size_sequence_rejects_before_first_element`, which is what makes the `size_hint` guard meaningful) can be edited or emptied freely — I confirmed that inserting an arbitrary item into that module is `[ACCEPTED]`. Separately, the fifteen replay commands contain no `cargo test --lib` and no unfiltered `cargo test`; the three cargo commands are `--test v1_projection_gate`, `--test global_economic_state_effect_refinement` and `--test claimant_backing_guard_golden`, all integration targets, which compile the library **without** `cfg(test)`. So the file's own unit tests are neither pinned nor run. The exclusion itself is sound — a second `#[cfg(test)] mod tests` is a duplicate-name compile error and also fails the template; an uncfg'd `mod tests_extra`, code after the block, and braces smuggled through a string are all rejected.

**Reproduce:** `"$PY" p2.py` → `[ACCEPTED] B10`; command list via `"$PY" -c "import json;[print(c['command_id'],c['argv']) for c in json.load(open('docs/research/ZENODEX_O008_FORMAL_CYCLE_V1.json'))['proof_replay']['commands']]"`.

**Required repair.** None required for soundness — the excluded region cannot affect the library's compiled behaviour for the integration gates. If the unit tests are meant to be evidence, either add `cargo test --offline --locked --lib` as a sixteenth replay command with its exact pass count, or add a nonclaim saying the bounded-vec unit tests are not part of the replayed evidence.

---

### P3-3 — `use serde::de::Deserialize;` is accepted; the serde rule is "any path under `serde::`", not "the serde prelude item"

**File:** `tools/o008_formal_cycle_admission_v1.py:1568-1570`.

**Exact statement.** The rule is `full_path.startswith("serde::") and bound_name == leaf`. `use serde::de::Deserialize;` satisfies both and is accepted. It is harmless here — `serde::de::Deserialize` is the same trait, and importing it instead of `serde::Deserialize` would leave `#[derive(Deserialize)]` unresolved in the macro namespace, so the crate would not compile — but the rule as written would also accept any future `serde::<submodule>::Deserialize` that is not a re-export. Recorded for completeness; the docstring's claim that serde names are "bound only from serde" is true as stated.

**Required repair.** None. If tightened: require `full_path == f"serde::{leaf}"` for the four prelude names.

---

### P3-4 — A raw identifier anywhere in a pinned Rust file is a hard `RUST_SOURCE_UNPARSEABLE`

**File:** `tools/o008_formal_cycle_admission_v1.py:1338` (raw-string scanner), reached from `strip_rust_noncode_v1`.

**Exact statement.** `_rust_literal_start` treats `r#` as the beginning of a raw string, so a raw identifier such as `r#use` or `r#type` is misparsed and the file is rejected with `RUST_SOURCE_UNPARSEABLE: unterminated string literal`. This is **fail-closed** and therefore not a soundness defect; it is a maintainability trap, because a legitimate future edit using a raw identifier would be rejected with a misleading code.

**Reproduce:** append `const _X: u8 = { let r#use = 1u8; r#use };` to `state.rs` and project.

**Required repair.** None required. If cheap: require `r#` to be followed by `"` or another `#` before treating it as a raw string, and emit a distinct code otherwise.

---

### P3-5 — Two review-receipt bookkeeping observations

The C3 review receipt (`ZENODEX_FORMAL_CORE_C3_OPUS_REVIEW_506ee5289fc7.md`) is **not** an ancestor of P7 — it was committed at `3fe6a21bd` as a *child* of P7, so the C1''' source commit S7 does not contain the review it repairs. That is a chain-hygiene observation, not a defect: S7's message names the two C3 findings explicitly and both are closed. Second, `tests/test_check_o008_formal_cycle_v1.py` collects exactly 257 tests, matching the commit message.

**Required repair.** None.

---

## 3. Verification record

`PY="/home/trevormoc/Downloads/Autonomous Tau DEX/.venv/bin/python"`, cwd `/tmp/zenodex-formal-core-review-p-da2277137` unless noted; ESSO via `PYTHONPATH=/home/trevormoc/Downloads/ESSO ZENO_ESSO_PYTHON=/usr/bin/python3`; cargo under `CARGO_TARGET_DIR=/tmp/zenodex-opus-c1tprime-cargo-target CARGO_INCREMENTAL=0` (deleted at the end, 1.6 G reclaimed).

| # | Command | Exit | Key output |
|---|---|---|---|
| 1 | `git status --porcelain \| grep -v '^??'` | 1 (grep, empty) | **0 tracked changes**, before and after; 0 untracked; HEAD still `da2277137`; no `target/` under the worktree |
| 2 | `git diff-tree --no-commit-id --name-status -r HEAD^ HEAD` | 0 | exactly `M docs/research/ZENODEX_O008_FORMAL_CYCLE_V1.json`, `M …_V1.md` |
| 3 | `git diff --stat HEAD^^ HEAD^` | 0 | 6 files, **+896 / −34**; 1 added (THV1 admission-v8, 769 lines), 5 modified, 0 deleted |
| 4 | `check_o008_formal_cycle_v1.py --root "$PWD"` | 0 | `ok:true, packet_admitted:true, current_applicable:true, current_source_drift:[], errors:[]`; head==packet==`da2277137`; `subject=fee3b08a1`; replay `NOT_RUN`; `executing_tools[o008_formal_cycle_admission_v1.py] = 975a4e05…` |
| 5 | `check_o008_formal_cycle_v1.py … --replay …` | 0 | `EXECUTED_PASS`, **15 runs, all exit 0**: lean_version 4.27.0; lean_direct_check `e3b0c442…`; lean_axioms_probe `theorems_probed=25`; lean_binding_gate 6; **esso_validate `sha256:918526261e71b37c7bf6af05a73a836c72fba86e008258e525b4970fcb75f04c`**; **esso_verify_multi VERIFIED z3 4.15.4/cvc5 1.1.2, fingerprint `256b0dcbb7c25c9581d6b16db8f2a5b44512d18c9cadf420477d6c63e38dfc86`, esso_code_hash `7f80c6216be8…`**; **esso_gate 20**; prior_restage_gate 136; python_version 3.12.3; python_projection_gate 13; rust_projection_gate 7; rust_version cargo 1.87.0; rust_refinement_gate 41; python_golden_gate 35; rust_golden_gate 3 |
| 6 | `build_o008_formal_cycle_v1.py … --subject-commit fee3b08a1 --created-date 2026-09-01 --check --replay …` | 0 | `{"drift":[],"mode":"check","ok":true,"subject_commit":"fee3b08a1f8511ad250cff5bacc77dae24d222c7"}` |
| 7 | `pytest -q -p no:cacheprovider tests/test_check_o008_formal_cycle_v1.py tests/test_o008_v1_projection_runtime_gate.py tests/formal/test_lean_global_claimant_custody_relation_v1.py` | 0 | **276 passed in 100.72 s** (257 + 13 + 6) |
| 8 | `PYTHONPATH=… ZENO_ESSO_PYTHON=… pytest -q … tests/formal/test_esso_global_claimant_custody_certificate_v1.py` | 0 | **20 passed in 21.12 s** |
| 9 | `cd zk/global_settlement_abi_v1 && cargo test --offline --locked --test v1_projection_gate` | 0 | **7 passed** |
| 10 | `cargo clippy --offline --locked --all-targets -- -D warnings` (after `cargo clean -p zenodex-global-settlement-abi-v1`) | 0 | `Checking zenodex-global-settlement-abi-v1 … Finished in 18.13s`, no diagnostics |
| 11 | `check_test_hygiene_v1.py --base-ref fd409ba6f7da8f0ec3e0220a04b7406d69a8cb85 --json` | 0 | `changed_path_count: 44`; 14 covered critical paths |
| 12 | `ruff check` (4 tools) | 0 | `All checks passed!` |
| 13 | `mypy --strict` (4 tools) | 0 | `Success: no issues found in 4 source files` |
| 14 | `PYTHONPATH=… /usr/bin/python3 -m ESSO validate <model>` (independent) | 0 | `ir_hash sha256:918526261e71b37c…`, `ok:true`, `errors:[]` |
| 15 | `PYTHONPATH=… /usr/bin/python3 -m ESSO verify-multi <model> --solvers z3,cvc5` (independent) | 0 | `verdict VERIFIED`, `solvers_agreed true`, `total_queries 4` all `unsat` under both solvers (`init_implies_inv`, `inductive_open_claim`, `inductive_drain_claim`, `inductive_deposit_reserve`), `fingerprints == [256b0dcb…, 256b0dcb…]` across both determinism trials |
| 16 | ESSO-kernel probe of the corrected notes sentence | 0 | `deposit_reserve` from GENESIS → `{'accepted': True, 'decision': 'GENESIS'}` with all four `g_*` flags false; `open_claim` with any one binding false → `StepError` |
| 17 | `p0.py` — `use`-scan coverage | 0 | state.rs **4/4**, bounded_vec.rs **6/6**, lib.rs **77/77**, v1_projection_gate.rs **3/3** statements seen |
| 18 | `p1.py` — import-scan escapes | 0 | U1/U2/U3 rejected; **A1/A2/A5/A8/A9/A10 ACCEPTED**; A1c/A5c controls rejected |
| 19 | `p2.py` — bounded_vec template | 0 | C1'' P1-2 vehicle and 5 exclusion attacks rejected; B4/B5/B10 accepted (residuals) |
| 20 | `p3.py` — gate hashes | 0 | both hashes recomputed from S7 blobs and **matching**; G1 emptied bodies rejected; comment-only edits without re-pin → **`THV1_PIN_DRIFT`**; S1/S2 accepted (residual) |
| 21 | `p4.py` — Python attribute rebinding | 0 | 3 spellings rejected, **5 accepted** |
| 22 | `p5.py` — crate-root module redirect | 0 | **L1/L2/L3/L4 all ACCEPTED** |
| 23 | Hostile crate copy, route P1-1 | 0 | `cargo test` 52 binaries 0 failures; 7/41/3 exact; clippy 0; probe `DIVERGENCE`; control `CONTROL: rejected: unknown field 'zz_shadow'` |
| 24 | Hostile crate copy, route P1-2 | 0 | `cargo test` 52 binaries 0 failures; 7/41/3 exact; clippy 0; probe `DIVERGENCE`; `state.rs`/`bounded_vec.rs`/`canonical.rs` byte-identical to the pinned files |

### Hand-recomputed pins

```
$ git cat-file blob HEAD^:tools/o008_formal_cycle_admission_v1.py | sha256sum
975a4e059e453246e94b12d05f085767d612f9f1cb17f5d389e3c51cf65e8a1d
   packet source_pins[21]  = 975a4e059e453246e94b12d05f085767d612f9f1cb17f5d389e3c51cf65e8a1d   MATCH
   report executing_tools  = 975a4e059e453246e94b12d05f085767d612f9f1cb17f5d389e3c51cf65e8a1d   MATCH

$ git cat-file blob HEAD^:src/kernels/dex/global_claimant_custody_certificate_v1.yaml | sha256sum
d7b547e32790828c149fb0e3bdd6b32e11a235bbb67b6cf02eaaff4db2681252
   packet source_pins[14]                     = d7b547e327…   MATCH
   tests/formal/…_certificate_v1.py RECORDED_SOURCE_SHA256 = d7b547e327…   MATCH
   tests/formal/test_lean_…_v1.py PINNED_SOURCES[ESSO_MODEL] = d7b547e327…   MATCH
```

### Bulk pin verification

- All **28** packet `source_pins` equal the S7 blob bytes (0 mismatches).
- All **26** `THV1-20260901-o008-formal-cycle-admission-v8.json` `source_pins`/`test_pins` equal the S7 blob bytes (0 mismatches).
- All **60** `killed_by` node ids resolve against the 277 tests collected from `tests/test_check_o008_formal_cycle_v1.py` + `tests/formal/test_esso_global_claimant_custody_certificate_v1.py` (0 missing).
- `subject_commit == fee3b08a1…`, `subject_tree == 37708bf5…` (= S7's tree), `subject_parent == 8d822a5b1…`, `packet_commit_parent == fee3b08a1…`, `packet_write_set` = exactly the two packet paths.
- P7 has **one** parent; S7 has **one** parent.
- Both gate content hashes recomputed from the S7 blobs by me, independently of the checker, and matching (`8afc35b7…`, `c84dbf97…`).

---

## 4. Nonclaims and residual risks

1. **I did not re-verify the Lean layer.** No `lake` invocation of mine ran; the Lean evidence rests on replay commands 1–4 executed by the checker (`lean_direct_check` exit 0 with `-DwarningAsError=true`, `theorems_probed=25`, binding gate 6 passed). The C1'' review verified the necessity theorem's statement and proof directly; I did not re-do that.
2. **The P2-1 runtime consequence is reasoned, not executed.** I did not build a mutated repository copy to watch the Python gate fail against `sys.modules[__name__].X = int`; I inferred it from the gate's `from … import` binding and its `dataclasses.fields` / defining-module assertions. The admission acceptance itself *is* executed.
3. **Both mounted P1 routes assume an attacker who re-pins.** That is the correct threat model for this checker (the packet's hashes are regenerated by the builder), and my harness performs full attacker re-pinning of the Lean gate table and the v8 hygiene packet. An attacker who cannot re-pin is stopped by `THV1_PIN_DRIFT` at the first byte changed.
4. **`Cargo.lock` content, the dependency name set, and the registry cache remain host-trusted**, exactly as C1'' recorded (its P3-4). I did not re-mount those probes; nothing in C1''' changed that surface.
5. **The `#[cfg(test)]` region of `bounded_vec.rs` and the string literals of the Rust gate are outside every pin.** I searched for a widening through both and did not find one; that is a bounded negative result, not a proof of safety.
6. **I did not audit the 82 unpinned `src/*.rs` modules** for existing constructs that would make P1-2 easier or harder; I supplied my own hostile module.
7. **Disk pressure.** The host was at 97–98 % full throughout. Both cargo builds completed cleanly and the 1.6 G target directory has been removed; no result in §3 was affected.
8. **I did not re-verify the six C2' `killed_by` attributions or the golden-v3 mutation table**, which C1'' verified six-of-six; C1''' did not touch them.

---

## 5. Do the user's decisions hold?

Yes, on all six.

- **Reserves are the claimant-free term.** Held. `deposit_reserve` writes only `reserve_d0`/`reserve_d1` (I read the action's `updates` directly), the ESSO invariants and both claimant actions are unchanged from C1''/C3, and no reserve column enters the claimant-backing view. The corrected notes sentence states exactly this and is now true.
- **Control-domain vocabulary with V1 wire names byte-stable.** Held. `TERMINAL_FIELDS`/`OUTBOX_FIELDS` are unchanged and pinned in both gates; `completion_scope[7]` still speaks of "the control-domain vocabulary"; the C3 P3-1 effect-surface ambiguity is retained rather than "fixed" by an enum change, which is the correct consequence of this decision.
- **O-008A unattested.** Held. `o008_status: OPEN_EXACT_ALL_12_RECONCILIATION_MISSING`; `nonclaims[1]` states the exact all-twelve certificate is not implemented or mounted.
- **UP-01..UP-20 unresolved and never fixture-selected.** Held. No `UP-` identifier appears in the packet, and the hygiene selection is 25 pinned paths with no UP fixture.
- **Authority NONE.** Held. All seven authority fields are `NONE` in every projection I ran, including under all 40+ hostile mutations.
- **`formal_core_complete` false.** Held, with `whole_value_movement_safe: false` and `value_movement_gates_closed: 0` of 12.

I also confirm C1''' does not relitigate any of these: the six user decisions are load-bearing in the packet text and were not weakened by the repair.

---

## 6. Disposition

**Grade C — REVISE.** The candidate is clean, exactly chained, claim-limited and passes every prescribed verification; four of five C1'' findings and both C3 findings are closed and I verified each by running it. It cannot rise above C because the compiled-binding claim is falsified end to end by two independent routes (**P1-1**, an attribute-prefixed `use`; **P1-2**, the unpinned crate-root `mod bounded_vec;`), and because the packet's own `static_closure` sentence now carries a clause that those routes make false (**P2-2**).

The single change that closes the most ground is to take the deserialiser out of the import path entirely: pin the macro body to call `crate::bounded_vec::deserialize_bounded_vec_v1::<…>` by absolute path, and add a `mod bounded_vec;`-once rule to the crate root alongside the existing `mod state;` rule. That closes P1-2 outright and removes P1-1's leverage over the decode path; the `use`-scan boundary should still be repaired (strip attribute groups before the scan) so that the serde and glob rules mean what the packet says they mean.

This grade is advisory and grants no authority.
