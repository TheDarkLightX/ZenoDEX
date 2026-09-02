# Opus independent review of record — C7 (S16/P16)

ZenoDEX formal functional core closure campaign, branch `codex/formal-core-fable-20260901`.
Reviewed in the clean detached worktree `/tmp/zenodex-formal-core-review-p-06a3591f7`
(HEAD `06a3591f776038024460e88a3c09b5ab89554fcb`, `git status --porcelain` empty at start
and at end). No file in the worktree was edited. Every mutation experiment ran on in-memory
copies or on copies written under the scratchpad.

**Grade: C7 = A-.**
**Findings: 0 x P1, 0 x P2, 1 x P3** (plus two INFO observations).

C7 exists solely to close the seven Opus P15 findings (2 P1, 2 P2, 3 P3). **All seven are
closed and independently verified adversarially here.** The envelope is clean, the full
`--check --replay` round-trip is byte-identical on the builder side, and a full checker
`--replay` returns `EXECUTED_PASS` over all 28 gates with the worktree left clean. No new
P1/P2 defect. The single P3 is a non-exploitable defense-in-depth completeness note.

---

## 1. Envelope + round trip (duty 1) — PASS

| Check | Result |
|---|---|
| `git rev-list --count S16..P16` | 1 |
| P16 is a single-parent child of S16 | `06a3591f7^` = `ebe802f81` (S16) |
| P16 touches only the two packet files | `M …ZENODEX_O008_FORMAL_CYCLE_V1.{json,md}` |
| S16 parent | `1929ca1b7` (P15 review receipt) |
| packet `subject_commit` == S16 | `ebe802f819e9a75cd9120c691f57892573c1ae41` |
| packet schema | `zenodex/o008-formal-cycle-evidence/v12` |
| `packet_write_set` | the two packet files only |

Chain: `1073c5347` (P15) -> `1929ca1b7` (P15 review receipt) -> `ebe802f81` (S16, the C7
repair) -> `06a3591f7` (P16, re-freeze).

**Admission checker at HEAD, NOT_RUN** (`tools/check_o008_formal_cycle_v1.py --root .
--packet-commit 06a3591f7`): `exit_code=0`, `ok=true`, `packet_admitted=true`,
`current_applicable=true`, `head==packet==06a3591f7`, `subject==ebe802f81`,
`proof_replay=NOT_RUN`, `errors=[]`, stderr empty.

**Builder projection round-trip under full replay.**
`tools/build_o008_formal_cycle_v1.py --check --replay` (project venv; `/usr/bin/python3`
as the ESSO interpreter; `PYTHONPATH=…/ESSO`):

```
{"drift":[],"mode":"check","ok":true,"subject_commit":"ebe802f819e9a75cd9120c691f57892573c1ae41"}
```

stderr empty; worktree clean afterwards. All 28 recorded proof commands executed and the
rebuilt projection — including the `EXECUTED` author record — is byte-identical to the
committed packet. The builder's post-replay `_require_worktree_equals_subject(...,
code="REPLAY_WORKTREE_MUTATED")` (the P1-1 escalation, `build_o008_formal_cycle_v1.py:79`)
therefore passed against a clean worktree.

**Checker full replay.** `tools/check_o008_formal_cycle_v1.py --replay --packet-commit
06a3591f7`: `exit_code=0`, `ok=true`, `packet_admitted=true`, `current_applicable=true`,
`proof_replay.status=EXECUTED_PASS`, 28 runs, `errors=[]`, stderr empty, worktree clean
afterwards. This exercises the checker's own escalation path
(`replay_worktree_mutation_errors_v1`) end-to-end and confirms it does **not** false-positive
on a clean run. This is the strongest form of duty 1 and it passes.

---

## 2. P15 P1 findings — both CLOSED

### P1-1 — mid-line `#` command / arbitrary IO during replay — CLOSED

**What C7 changed.**
* `o008_formal_cycle_admission_v1.py:1656` — the `#` ban is now un-anchored:
  `re.search(r"#", _lean_code(text, path))` (was `re.search(r"^\s*#", …, re.MULTILINE)`).
  Any `#` in the comment/string-stripped code of a pinned Lean file is rejected
  (`LEAN_COMMAND_FORBIDDEN`).
* `:1047` — `run_cmd`, `run_elab` joined `_LEAN_FORBIDDEN_WORDS_V1`.
* Escalation: a post-replay worktree re-verification in **both** the builder
  (`build_…:79`, `REPLAY_WORKTREE_MUTATED` against the subject blobs) and the checker
  (`check_…:71-84` -> `replay_worktree_mutation_errors_v1`, `admission_…:3966`, forcing
  `EXECUTED_FAIL` over the packet's source pins + selected hygiene packets).
* `LEAN_STATEMENT_BINDING_V1` (`:604`) rewritten to state exactly the enforced property.

**Verification.**
* The P15 vehicle (`  Iff.rfl #eval (IO.FS.writeFile (String.ofList ['…']) … : IO Unit)`,
  injected after the elided proof line of `necessaryRelation_independent_of_reserves`) is
  now `REJECT LEAN_COMMAND_FORBIDDEN: # command at line 128` at `literal_closure`, while the
  surface hash still MATCHes — confirming the surface hash is (as P15 diagnosed) blind to the
  elided region, and the un-anchored `#` ban is now the barrier that catches it.
* **No residual `#`-free IO path.** Every Lean 4 mechanism that runs `IO` at
  `lake env lean` elaboration requires one of: a `#`-command (`#eval`/`#eval!`/…, all begin
  with `#` — banned anywhere), `initialize`/`builtin_initialize` (forbidden words),
  `run_cmd`/`run_elab` (now forbidden), `native_decide` (banned by the placeholder scanner,
  `scan_lean_proof_placeholders_v1.py` `lean_native_decide`), or a custom command/elaborator
  via `macro`/`elab`/`syntax`/`notation`/`declare_syntax_cat` (all forbidden). `deriving`
  invokes only registered handlers (no custom handler can be registered without the banned
  words); defining `def x : IO Unit := …` never executes it. So no elaboration-time IO can be
  expressed.
* **Comment/string lexer divergence closed.** The only historical way to hide a command from
  the stripper while Lean elaborates it was a lexer desync (P10 quote-in-char, P13
  guillemet-comment). With `"` and `«`/`»` banned on the *raw* bytes before stripping
  (`:1652-1655`), the stripper's string state is unreachable and its comment boundaries
  (`--`, nested `/- -/`) agree with Lean's; a `#` inside a char literal `'#'` stays in the
  stripped code and is rejected (fail-closed, as the code comment notes). `_lean_code` catches
  `ScanError` -> `LEAN_SOURCE_UNPARSEABLE`, so a malformed strip cannot skip the ban.
* **Only the two pinned proof files elaborate during replay.** Both binding-gate tests
  (`test_lean_global_claimant_custody_relation_v1.py:113`,
  `test_lean_global_accounting_allocation_certificate_v1.py:103`) run `lake env lean` on the
  single pinned `PROOF` file and a derived `#print axioms` probe only — never `lake build` of
  the whole library — so no non-pinned `.lean` file (including the pinned-but-unclosed
  `Proofs.lean` root) is elaborated. The axioms-probe files are shell-generated from the
  closure-checked proof + read-only `#print axioms`; not attacker-controlled.
* **Escalation is sound and cannot be forged.** `replay_worktree_mutation_errors_v1` compares
  the current worktree sha of every applicability path against `replay_expected_sha_by_path_v1`
  (source pins + selected hygiene). I verified in-memory: 43 applicability paths, 43 expected
  entries, **0 paths without an expected sha** (fail-closed), baseline → 0 errors, a mutated
  or deleted path → `REPLAY_WORKTREE_MUTATED`. The expected shas cannot be forged: the packet's
  `source_pins[*].sha256` are bound to S by `check_source_pins_v1` -> `_check_pin_row`
  (`row["sha256"] != blob.sha256` rejects) **and** the whole packet is compared against the
  S-derived projection by `check_projection_v1(packet, _expected_projection(packet, snapshot))`.
  The `EXECUTED_FAIL` status propagates to `ok=false`/`exit 1` via `render_report_v1:4140`.
* **No IO window.** `run_proof_replay_v1` runs each command with `subprocess.run(..., timeout=)`
  synchronously and returns only after the last command's process has exited; the checker
  computes the re-read shas immediately after, with no concurrent replay process. (A
  double-forked daemon would need code execution during replay — closed above — and could
  only cause a *future* run to fail-closed on the pre-replay drift check, never launder the
  current one.)

**Statement-binding accuracy.** The rewritten `LEAN_STATEMENT_BINDING_V1` — "no double quote
or guillemet and no # character anywhere in its stripped code … no notation, macro, syntax,
instance, attribute, scope, open, run_cmd, or run_elab command; each elided region is
indented, #-free, forbidden-word-free proof text with no declaration" — matches exactly what
is enforced. The false clauses P15 flagged ("no # command" while only anchored; "only how a
theorem is proved is left to replay") are gone.

**Verdict: CLOSED.**

### P1-2 — module-hook binding by nested def/class or `import *` — CLOSED

**What C7 changed.** `python_dynamic_binding_scan_v1` now calls a recursive
`_scan_hook_definitions_v1(module, path, under_class=False)` (`:1854`) that walks every
descendant; a `def`/`async def`/`class` named `__getattr__`/`__dir__` is rejected unless it
has a `ClassDef` ancestor (ancestry, not `module.body` membership). `from x import *` is
banned (`:1904`).

**Verification.** Every P15 surviving vehicle now rejects — `def` inside
`if`/`try`/`for`/`while`/`with`/`match`/`else`, `async def`, decorated `def`, `class`
named after a hook, arbitrarily deep nesting, and `from os import *`. The class-ancestor
negative case is genuinely harmless: a `def __getattr__` in a class body is `C.__getattr__`,
not the module global; a `def __getattr__` local to a method is a local; neither is a module
hook. I further confirmed the only ways to route a class-made hook into the module namespace
are all caught by the existing `ast.walk` binding pass: `global __getattr__` inside a class
method, `__getattr__ = …` (Name Store), tuple-unpack / `for` / `with as` targets, walrus
(module + comprehension), annotated assignment, `from m import y as __getattr__`,
`sys.modules[__name__].__getattr__ = …` (attribute store), and `globals()/vars()/setattr()`
(forbidden dynamic calls). All → `PYTHON_DYNAMIC_BINDING_FORBIDDEN`.

**Verdict: CLOSED.**

---

## 3. P15 P2 findings — both CLOSED

### P2-1 — `binding_root` unvalidated — CLOSED

`_check_lane_bindings` (`global_accounting_allocation_certificate_v1.py:648-651`) now rejects
`fragment.binding_root != fragment.lane_state_root` with `BINDING_ROOT_DRIFT` for every
fragment (16 codes; Rust twin at `.rs:129`). This directly kills P15's counterexamples (b)
forged `binding_root` and (c) zero `binding_root`, both previously accepted. A recorded vector
`rejects_forged_binding_root` produces `BINDING_ROOT_DRIFT` / detail `ASSET_TRANSFER`, and the
mutation killer "trust the fragment's binding root" is declared. **Precedence:** it is the
last check in `_check_lane_bindings`, after `REGISTERED_EMPTY_ROOT_DRIFT` — check-major, so it
adds value exactly when the earlier lane-root comparison passes but the binding field is
forged. **C9 documented:** the code comment states C9's receipt admission replaces this rule
for `RECEIPT_BACKED` lanes with the receipt root.

**Verdict: CLOSED.**

### P2-2 — Python/Rust fold-label divergence — CLOSED

Python `_fold` now **requires** `label` (no default, `:654`); the five call sites carry
`{lane} controlled` (`:670`), `{lane} assignments` (`:676`), `reserves` (`:699`),
`terminal totals` (`:772`), `custody` (`:789`) — matching the Rust labels
(`.rs:818/837/913/1081/1132`). The fixture pins `fold_overflow_labels`
(`["{lane} controlled","{lane} assignments","reserves","terminal totals","custody"]`,
`fixture_schema …/v2`). Direct-call parity tests on both sides
(`test_…_golden.py:202 test_fold_overflow_details_match_the_shared_labels`;
`.rs:1401 fold_overflow_details_match_the_shared_labels`) drive each of the five folds via
`_check_exactly_once` / `_check_reserve_rows` / `_check_terminal_totals` /
`_check_lane_aggregates` with `u128::MAX` rows and assert each reject detail equals the
corresponding fixture label — binding the **actual** call sites. The claim that the folds are
unreachable through the registry gate holds: with no receipt-backed producer, a lane carrying
rows is rejected earlier by `DISABLED_LANE_NOT_EMPTY` / `BLOCKED_LANE_PRODUCER_MISSING`
(both precede the fold-bearing checks in `CERTIFICATE_CHECK_ORDER_V1`), which is why the
overflow detail cannot be pinned by a whole-certificate recorded vector.

**Verdict: CLOSED.**

---

## 4. P15 P3 findings — all CLOSED

* **P3-1 (vector count).** The completion-scope sentence is now an f-string over
  `CERTIFICATE_FIXTURE_VECTORS_V1 = 28` (`:276`); the fixture holds exactly 28 vectors and the
  count is enforced at `:2982` (`len(vectors) != CERTIFICATE_FIXTURE_VECTORS_V1 ->
  CERTIFICATE_FIXTURE_DRIFT`) and again at `:3533`. Both count and binding fixed (P15's
  "twenty-five" prose was wrong and unbound).
* **P3 statement-binding accuracy** — see P1-1; the sentence now claims exactly what is
  checked.
* **P3-2 (Rust producer swallowed error).** `global_accounting_lane_producers.rs:81-89` now
  `match`es `registered_empty_lane_root_v1(...)` and maps `Ok(None) | Err(_)` to
  `REGISTERED_EMPTY_ROOT_DRIFT` (was `.ok().flatten()` -> `None` -> `LANE_NOT_REGISTERED_EMPTY`).
  New unit test `registered_empty_lane_roots_are_available` (`.rs:115`) pins both
  registered-empty lanes compute a root (the 4th Rust unit test; the packet's expected count
  moved 3 -> 4).
* **P3-3 (ESSO pre-check fail-open).** `test_esso_global_accounting_allocation_certificate_v1.py:243`
  is now `assert _evaluate(expr, values, enums, "") is True` (was `is not False`), so a model
  omitting a variable an assumed invariant needs fails closed instead of vacuously passing.

---

## 5. Nonclaims + authority ceiling (duty 5) — INTACT

`claim_ceiling`: all seven authority fields (`migration/production/publication/release/
settlement/value_movement/verifier`) = `NONE`; `formal_core_complete=false`;
`whole_value_movement_safe=false`; `o008_status=OPEN_EXACT_ALL_12_RECONCILIATION_MISSING`;
`value_movement_gates_closed=0` of `12`;
`supported_claim=O008_RELATION_NECESSARY_CHECKS_AND_INFORMATION_LOSS_PROVED`;
`formal_cycle_status=FORMAL_CYCLE_COMPLETE_O008_OPEN`. The 11 nonclaims correctly disclaim
O-008 completion, no receipt-backed producer / not mounted, no refinement to any running
execution, no cryptographic binding / runtime parity / settlement authority / value safety,
the fingerprint-vs-ir_hash distinction, the detached-sidecar evidence-only ceiling, the
unpinned Rust modules, the author record being an observation only, the pin-only hygiene
packets, and all authority. The claim ceiling is emitted from module constants; no packet
content can raise it (`render_report_v1` uses `CLAIM_CEILING_V1`). No overclaiming sentence
found (the P15-flagged statement-binding and vector-count sentences are both corrected).

---

## 6. Finding (P3) and observations

### P3-1 (this review) — the replay re-verification set is the pinned+hygiene closure, not every file a replay gate reads (defense-in-depth)

`replay_worktree_mutation_errors_v1` / the builder's `_require_worktree_equals_subject`
re-verify only the source pins and selected hygiene packets. Several files a later replay gate
reads are **not** in that set — e.g. `tests/test_o008_v1_projection_runtime_gate.py`
(command 16) and the `src/` modules pytest imports transitively. This is by design (the
escalation's charter is "a replayed command must not rewrite the *pinned* bytes the remaining
commands replay"), and it is **not exploitable today**: there is no `#`-free / forbidden-word-
free IO path to mutate anything during the Lean replay (§P1-1), and the pinned test/source
files that *do* run code are themselves gate-checked and re-verified. But the completeness of
the backstop rests entirely on the direct-IO closure being total; if a future `#`-free IO
vector were ever found, a gate reading a non-pinned file could be laundered without tripping
`REPLAY_WORKTREE_MUTATED`. **Direction:** either re-verify the full transitive read set of the
replay commands, or run the replay against an ephemeral read-only copy of the worktree so no
replayed command can write the live tree at all. Severity P3 (theoretical, defense-in-depth).

### INFO-a — `python_dynamic_binding_scan_v1` coverage

The scan is applied to the gate, types, and certificate modules (`:2924`, `:2944`, `:3024`),
not to the producers or refinement modules. This is consistent with its purpose (protecting
the checker's *static shape extraction* of exactly the parsed files, which the admission
decision trusts); the checker does not import the runtime modules, so a fabricated name in an
unscanned module does not fool the admission decision. Noted for completeness, not a
demonstrated defect.

### INFO-b — `_scan_hook_definitions_v1` over-rejection

A `def __getattr__`/`__dir__` local to a module-level *function* (no `ClassDef` ancestor) is
rejected even though a function-local name is not a module hook. This is a fail-closed
over-rejection with no security impact; the pinned modules do not trip it.

---

## 7. Grade — C7 = A-

C7 is a focused repair whose sole charter is to close the seven Opus P15 findings, and it
closes **all seven**, each verified adversarially here:

| P15 finding | Verdict |
|---|---|
| P1-1 mid-line `#` / no post-replay re-verification | **CLOSED** — un-anchored `#` ban + dual-side, S-bound post-replay re-verification; no residual `#`-free IO path |
| P1-2 nested def/class hook binding + `import *` | **CLOSED** — recursive ancestry scan defeats a full battery of vehicles; `import *` banned |
| P2-1 unvalidated `binding_root` | **CLOSED** — `BINDING_ROOT_DRIFT` per fragment, recorded vector + killer, C9 documented |
| P2-2 fold-label divergence | **CLOSED** — labels unified, fixture-pinned (schema v2), direct-call parity on both real call sites |
| P3-1 vector count | **CLOSED** — f-string over the enforced `= 28` constant |
| P3 statement-binding accuracy | **CLOSED** — sentence now matches enforcement |
| P3-2 Rust producer swallowed error | **CLOSED** — maps to `REGISTERED_EMPTY_ROOT_DRIFT` + unit test |
| P3-3 ESSO pre-check fail-open | **CLOSED** — `is True` |

The envelope is clean; the builder `--check --replay` round-trip is byte-identical; the
checker `--replay` returns `EXECUTED_PASS` over all 28 gates with the worktree left clean and
the new escalation path not false-positiving; the authority ceiling is `NONE` and the
nonclaims are intact. The P1-1 escalation is a genuinely strong construction — an un-anchored
lexical ban plus a builder- and checker-side re-read that is cryptographically bound to S and
correctly wired to `EXECUTED_FAIL` -> `exit 1`. There is **no open P1 or P2**.

Held one notch below A by the single P3: the re-verification set is the pinned+hygiene
closure rather than the full transitive read set of the replay, so the escalation is
belt-and-suspenders only for pinned evidence and rests on the direct-IO closure being total.
That closure holds today, so the residual is non-exploitable — hence A-, not lower. Not A
because a strictly airtight escalation would re-verify (or sandbox to read-only) everything
the replay touches, closing the completeness gap by construction rather than by argument.

**Promotable.** Recommend proceeding; the P3 is a hardening item for a later commit
(ephemeral read-only replay tree, or full-read-set re-verification), not a blocker.

---

## Appendix — commands run

```
git rev-list --count ebe802f81..06a3591f7            -> 1
git rev-parse 06a3591f7^                              -> ebe802f81 (S16)
git diff --name-status S16 P16                        -> only the two packet files
tools/check_o008_formal_cycle_v1.py --root . --packet-commit 06a3591f7          -> exit 0, ok, admitted, NOT_RUN
tools/build_o008_formal_cycle_v1.py --root . --subject-commit S16 --check --replay
                                                     -> {"drift":[],"ok":true}, worktree clean
tools/check_o008_formal_cycle_v1.py --replay --packet-commit 06a3591f7
                                                     -> exit 0, ok, EXECUTED_PASS, 28 runs, errors [], worktree clean
in-memory: run_static() on both pinned Lean files    -> ALL_STATIC_PASS (pristine); P15 #eval vehicle -> REJECT LEAN_COMMAND_FORBIDDEN
in-memory: python_dynamic_binding_scan_v1 on ~30 hook vehicles -> all REJECT; class-body/local negatives -> PASS (harmless)
in-memory: replay_worktree_mutation_errors_v1        -> 43 apaths / 43 expected / 0 missing; mutate/delete -> REPLAY_WORKTREE_MUTATED; baseline -> 0
fixture: 28 vectors, rejects_forged_binding_root -> BINDING_ROOT_DRIFT, fold_overflow_labels (5), killer present
```

Artifacts under
`/tmp/claude-1000/-home-trevormoc-Downloads-Autonomous-Tau-DEX/37cec583-0c57-4fc0-844c-9f17c86c9adf/scratchpad/opus_p16/`:
`builder_replay.json`, `builder_replay.err`, `checker_replay.json`, `checker_replay.err`,
`checker_norun.err`, `lean_harness.py`, `mut_p15_eval.lean`.
