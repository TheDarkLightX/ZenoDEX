# Opus review receipt: candidate C1' at P3' = 52d81ff352296c570a4cf01e6cb4fd0bde1d4d59

Reviewer: Opus 5 (independent reviewer, read-only, detached worktree `/tmp/zenodex-formal-core-review-p-52d81ff35`).
Date: 2026-09-01. Subject: P3' = 52d81ff352296c570a4cf01e6cb4fd0bde1d4d59 (tree 5da848dfd54b0897ff7e6196e18d15dc3f876a07), S3' = d7b3a528bd9a16f5165c7776a045c9b967a9686f, parent bfadf58bbb7cf8abc5885ccb9cc0683f032edb32 (Codex C1 receipt).
Verdict: Grade C, REVISE. Codex P2 closed; Codex P1 closed for the named instance only (the class survives via a `deserialize_with` hook on the container field and via unconstrained gate-file content). Disposition: P1-A, P1-B, P2-1, P2-2, P2-3, P2-4, P3-1, P3-3, P3-5 are repaired by candidate C1''; P3-2 is recorded as a packet nonclaim; P3-4 was repaired by C2' (independent Git-derived drift) and gains a synthetic-chain test in C1''. The grade is advisory and grants no authority.

Verbatim report follows (probe scripts and counterexample crates it names lived under /tmp/opus-c1prime-* and are not part of the repository).

---

# Grade: C — REVISE

The exact subject is clean, correctly chained, claim-limited, and passes every prescribed verification; 211 admission tests pass; ruff/mypy/clippy are clean; the two hand-recomputed pins match; the new THV1 v4 packet pins exactly the S3' bytes and all 38 `killed_by` node ids exist. The Codex P2 repair is thorough and I could not break it: closed per-command comparable schemas, an exact 4-key toolchain block, toolchain comparison on fresh replay, and a builder that derives the toolchain only from replayed tools. The Codex P1 repair is genuine but incomplete: the named `#[cfg(any())]`-decoy-plus-macro-live-struct is now rejected with a specific code (`RUST_CFG_FORBIDDEN`), yet the headline claim of the commit — "Compiled binding under replay" — does not hold adversarially. A `#[serde(deserialize_with = "...")]` hook on the state container, written as an ordinary `fn` (no cfg, no macro, no `include!`), passes the whole lexical closure, passes `project_packet_v1`, compiles, and passes all five `v1_projection_gate` tests while the compiled `GlobalEconomicStateV1` accepts a widened terminal row. Separately, the two new gate files' *content* is constrained by nothing but a sha256 and a pass count, so both gates can be replaced by vacuous tests and still project and admit. This is the same defect class Codex graded C1 at C for, reached by a construct simpler and less conspicuous than the one that was repaired, so the grade cannot rise. It is a materially stronger C than C1's: P2 is fully closed, the cfg/macro class is closed, replay now genuinely compiles Rust, and the test matrix grew 136 → 211.

Codex P1: **NOT closed** (specific instance closed, class open). Codex P2: **closed** (narrow residual, P3-2 below).

---

# Findings

## P0 — None
No authority escalation, value movement, production promotion, or `formal_core_complete=true` path. The claim ceiling is emitted from module constants and every mutation I mounted left it identical.

## P1-A — A `deserialize_with` hook defeats the compiled projection gate while the textual scan and all five gate tests pass

Files: `/tmp/zenodex-formal-core-review-p-52d81ff35/tools/o008_formal_cycle_admission_v1.py:1403` (`rust_container_field_types_v1`), `:1408` (`allow_attributes=True`), `:1650` (`_check_container_bindings`), `/tmp/zenodex-formal-core-review-p-52d81ff35/zk/global_settlement_abi_v1/tests/v1_projection_gate.rs:95`, `:116`, `:134`.

Exact statement: the container scan checks only the *declared type* of `GlobalEconomicStateV1.terminal_obligations` / `.outbox` and explicitly permits field attributes, so a `#[serde(deserialize_with = "…")]` hook is unconstrained; the hook's body is a plain `fn`, and `fn` is absent from `_RUST_ITEM_KEYWORD_RE` (`:527`), so the lexical closure never inspects it. The compiled gate is the only defence, and it is a two-key point test: `state_container_rejects_unknown_terminal_field_through_the_compiled_type` injects exactly `liability_domain`, and `terminal_record_rejects_unknown_fields` exactly `liability_domain`/`custody_principal`. Because the gate file is pinned bytes the attacker can read, a deserializer that rejects those two names and drops every *other* unknown key passes all five tests. Two independent variants confirmed:

* **Outbox** (no container test exists at all — the gate covers the terminal container only): a lenient `fn deserialize_outbox_v1` replacing the macro invocation. Scan accepted, 5/5 gate tests green, container accepted a row carrying `liability_domain` and `custody_principal`.
* **Terminal** (defeats the very test added to close Codex P1): a `fn deserialize_terminal_obligations_v1` that returns "unknown field" for `liability_domain`/`custody_principal` and silently drops anything else. Scan accepted, 5/5 gate tests green, container accepted a row carrying `custody_domain_shadow`.

Control: the unmodified crate rejects the same input with `unknown field 'custody_principal', expected one of 'effect_id', 'destination_id', 'payload_hash', 'commit_id', 'status'`.

Reproduce (temporary copies only; nothing was written in the worktree):
```bash
# scan acceptance, in-process against SubjectSnapshotV1 with full attacker re-pinning
"$PY" /tmp/opus-c1prime-exp/probe3.py
#   [ACCEPTED] T1 selective terminal deserialize_with (full projection)
#   [ACCEPTED] T2 lenient outbox deserialize_with (full projection)

# compiled behaviour
cd /tmp/opus-c1prime-cargo-terminal/zk/global_settlement_abi_v1
export CARGO_TARGET_DIR=/tmp/zenodex-opus-c1prime-cargo-target CARGO_INCREMENTAL=0
cargo test --offline --locked --test v1_projection_gate          # 5 passed
cargo test --offline --locked --test opus_terminal_probe -- --nocapture
#   DIVERGENCE: widened terminal row ACCEPTED; rows=1
```
(`/tmp/opus-c1prime-cargo` holds the outbox variant; the pristine control was `/tmp/opus-c1prime-cargo-control`, since deleted.)

Required repair: make the record-level property universal rather than exemplary. Either (a) forbid `deserialize_with`/`with`/`default`/`flatten` field attributes on the two container fields that hold V1 records — i.e. call `_rust_fields(..., allow_attributes=False)` for `CONTAINER_RECORD_FIELDS_V1` and allow attributes only on the remaining container fields — or (b) make the gate property-based: round-trip every field name plus a set of generated unknown keys (including randomly generated ones derived from a seed the gate prints), asserting rejection for *all* of them. (a) alone is the cheap, closing fix; (b) is the one that survives the next unforeseen hook.

## P1-B — The two new replay gates' content is unconstrained by admission, so the compiled/runtime binding can be neutered wholesale

Files: `tools/o008_formal_cycle_admission_v1.py:94-95` (the two gate rows in `SOURCE_PIN_ROLES_V1`), `:503-504` (`PYTHON_GATE_EXPECTED_PASSED_V1 = 8`, `RUST_GATE_EXPECTED_PASSED_V1 = 5`).

Exact statement: `tests/test_o008_v1_projection_runtime_gate.py` and `zk/global_settlement_abi_v1/tests/v1_projection_gate.rs` enter the packet only as `{path, role, mode, git_blob, sha256, size}` and enter replay only as a pass count. The core knows how to constrain gate content — it does exactly that for the Lean gate (`_check_lean_gate`, `:1548`: `THEOREMS`, `PINNED_SOURCES`, `ALLOWED_STANDARD_AXIOMS`) and the ESSO gate (`_project_esso`, `:1514-1524`: model sha pin, `EXPECTED_INVARIANTS`, named mutant param ids, `RECORDED_IR_HASH`, `RECORDED_ESSO_CODE_HASH`) — and does not do it for the two gates whose whole purpose is to bind the compiled artefact. Replacing the Rust gate with five `#[test] fn a() { assert!(true); }` and the Python gate with eight `def test_x(): assert True` is accepted by `project_packet_v1`, and both would report the expected 5 and 8 at replay.

Reproduce: `"$PY" /tmp/opus-c1prime-exp/probe_gate.py` → `[ACCEPTED] G1 …vacuous…`, `[ACCEPTED] G2 …vacuous…`. (G3 confirms the lexical layer still catches a directly widened field list, so the scan — not the gate — is doing all the adversarial work today.)

Required repair: extract and pin the gate content the way the Lean/ESSO gates are handled. Minimum: from the `.rs`, the two `const … FIELDS` arrays must equal `TERMINAL_FIELDS_RUST_V1`/`OUTBOX_FIELDS_RUST_V1` names and the tested unknown-key set must be non-empty and recorded in the packet; from the `.py`, `TERMINAL_FIELDS`/`OUTBOX_FIELDS` and the `@pytest.mark.parametrize` ids must match the projection (`pytest_param_ids_v1` already exists at `:1111`).

## P2-1 — The cargo replay records no compiler identity and is not hermetic

Files: `tools/o008_formal_cycle_admission_v1.py:1743` (`AUTHOR_TOOLCHAIN_KEYS_V1` = esso_code_hash, lean, python, solvers), `:777-781` (the `rust_projection_gate` command), `:1422` (`rust_manifest_closure_v1`), `tools/o008_formal_cycle_shell_v1.py:286` (`REPLAY_ENV_PASSTHROUGH_V1`).

Exact statement: replay gained a Rust compile but the toolchain block gained no Rust entry, and there is no `rust_version` command paralleling `lean_version`/`python_version` — `grep -n "rustc\|cargo_version\|rust_version" tools/o008_formal_cycle_admission_v1.py` returns nothing. The packet therefore records a compiled result with no record of what compiled it. The manifest closure covers `Cargo.toml` only: `Cargo.lock` is unpinned (`--locked` asserts only internal consistency), `.cargo/config.toml` is neither pinned nor consulted (it can set `[source] replace-with`, `rustflags`, or `rustc-wrapper` from the crate dir, `zk/`, the repo root, or `$CARGO_HOME`), `CARGO_HOME`/`RUSTUP_TOOLCHAIN`/`PATH` are passed through from the reviewer's environment, and every crate source other than `state.rs`/`lib.rs` (`bounded_vec.rs`, `canonical.rs`, `release.rs`, …) is outside the pinned set, so `check_current_applicability_v1`'s worktree-equals-S guarantee covers only the 22 pinned paths. `[workspace]`, `[features]`, `autotests`, and a loosened `serde = "1"` all pass the manifest closure (probes M10/M11/M12, all `[ACCEPTED]`).

Required repair: add a `rust_version` replay command (`cargo --version` / `rustc --version`) and a `rust` key in the closed toolchain block; pin `Cargo.lock`; reject the presence of any `.cargo/config.toml` at the crate dir, `zk/`, or the repo root; and reject `[workspace]`/`autotests` in the crate manifest.

## P2-2 — `rust_lexical_closure_v1`'s local-macro set is order-blind, so a foreign item-defining macro is reachable at depth zero

File: `tools/o008_formal_cycle_admission_v1.py:1359`.

Exact statement: `local_macros = set(re.findall(r"\bmacro_rules!\s*(…)", code))` is computed over the whole file with no regard to definition order or to path-qualified invocation. `crate::evil_items!();` at brace depth zero followed later in the file by `macro_rules! evil_items { () => {}; }` is accepted (probe M4, `[ACCEPTED]`): the scanner sees a "local" macro whose dummy body defines nothing, while `rustc` resolves the path-qualified invocation to a `#[macro_export]` macro in an unpinned module whose expansion may define `struct`, `impl`, `mod`, or `use`. This directly falsifies the docstring at `:1345-1351` ("Without … item-defining or nested-invoking local macros, and foreign item-position macros, a `pub struct` at brace depth zero is the single definition Rust compiles for that name"). I did not mount a schema divergence through it — a second definition of the record name would collide — but the stated closure argument is unsound, and it gives P1-A a way to hide the hostile `fn` outside the pinned bytes.

Required repair: treat a macro as local only if its `macro_rules!` definition precedes the invocation textually, and reject any path-qualified (`::`-bearing) macro invocation at depth zero outright.

## P2-3 — The Python container class is not closed; only replay catches a rebind

File: `tools/o008_formal_cycle_admission_v1.py:1055` (`python_container_field_annotations_v1`).

Exact statement: the record classes go through `_top_level_class` (`:983`) with its no-rebind, no-bases, single-literal-`@dataclass` closure, but `GlobalEconomicStateV1` goes through a bare `found = [n for n in module.body …]` with none of it. Appending `class _Other: pass` + `GlobalEconomicStateV1 = _Other` to `src/core/global_settlement_types_v1.py` is accepted by the scan (probe P5, `[ACCEPTED]`). Likewise `exec('TerminalObligation' + 'V1 = int')` and `globals()['TerminalObligationV1'] = int` defeat `_binds_name` (`:971`), which is AST-syntactic (probes P3/P6, `[ACCEPTED]`; the literal `TerminalObligationV1 = int` is correctly rejected as `PYTHON_CLASS_REBOUND`). Module-level `__getattr__` and `sys.modules` writes are inert here and are not findings.

Honest scope: all three rebinds should be caught by `tests/test_o008_v1_projection_runtime_gate.py` under `--replay` (`dataclasses.fields(int)` raises; `cls.__module__` fails), so this is a defence-in-depth gap rather than an end-to-end bypass — *unless* the gate is neutered per P1-B, and it does not hold at all for the default non-replay invocation, which still returns `ok=true, packet_admitted=true` with `proof_replay.status = NOT_RUN`. `exec` and `globals()[…] =` are outside the pinned surface in the sense that no AST rule can see through them; the honest fix is to reject `exec`/`eval`/`globals()` assignment at module level in the pinned types module, or to stop claiming the AST layer closes the binding.

Required repair: route `GlobalEconomicStateV1` through the same closure as the records, and reject module-level `exec`/`eval`/`globals()` subscript assignment in `PYTHON_TYPES_PATH_V1`.

## P2-4 — Hygiene selection validates pins only; the selected packet's content is unvalidated and the division is undocumented

File: `tools/o008_formal_cycle_admission_v1.py:1710` (`_select_hygiene_packets`), `:1693` (`_hygiene_pins`).

Exact statement: selection takes the lexicographically newest packet whose pin equals the subject blob and checks only `schema`, `evidence_id == filename stem`, that `source_pins`/`test_pins` are lists of objects, and non-circularity. Adding `THV1-20260901-o008-formal-cycle-admission-v9.json` with v4's pins verbatim but `"mutations": []` and `"evidence_families": []` is selected and admitted (probe H1, `[ACCEPTED]`, selected = …v9.json). The circularity guard does work (probe H2 → `THV1_PINS_PACKET_CIRCULAR`). The division of labour is defensible — `tools/check_test_hygiene_v1.py` owns families and mutation tables — but it is **not** honest as currently documented: that gate is not one of the eleven replay commands, and the packet's eight `nonclaims` do not mention hygiene at all, while the Markdown section is headed "Hygiene selection (newest packet pinning each required path at the subject commit)", which a reader will take as an assurance about the packet rather than about its pins.

Required repair: no code change is strictly required, but add a nonclaim — "the selected test-hygiene packets are bound by pin only; their evidence families and mutation tables are validated by `tools/check_test_hygiene_v1.py`, which this checker does not run" — or add that gate as a twelfth replay command.

## P3-1 — The serde-import check is line-anchored and `extern crate` is unconstrained
`tools/o008_formal_cycle_admission_v1.py:1373`: `re.finditer(r"^\s*(?:pub…)?use\s+([^;]+);", code, re.MULTILINE)` cannot match a `use` that shares a line with preceding code, so `const _X: u8 = 0; use crate::evil::Deserialize as _E;` escapes the check entirely (probe M2, `[ACCEPTED]`). `extern crate hex as serde;` at depth zero is matched by no rule at all (probe M3, `[ACCEPTED]`). Neither is weaponisable here — a hostile derive needs a proc-macro crate, and `path`/`git` dependency specs are rejected — so this is P3, not P2. Repair: tokenise `use`/`extern crate` from the stripped code rather than line-anchoring, and reject `extern crate` in the two scanned files.

## P3-2 — Two author-record values remain free absent `--replay`
`tools/o008_formal_cycle_admission_v1.py:1800` (`_validate_toolchain`), `:1755` (`COMPARABLE_SCHEMA_V1`). `toolchain.python` is only shape-checked (`semver`, and must equal the `python_version` run) and `lean_axioms_probe.probe_sha256` is only `hex64`. A self-consistent forged `python = "9.9.9"` and an arbitrary probe hash are both accepted (probes A10/A11, `[ACCEPTED]`), while every value Codex named — `lean=999.0.0`, forged solver versions, an extra authority-shaped key at either level, a dropped run, reordered runs, `passed=1`, `verdict=UNKNOWN`, a forged ESSO fingerprint, `passed=True` — is now rejected with a specific code (A1–A9, A12, A13). Fresh replay refutes both residuals via `compare_author_record_v1`. No repair required; state it as a nonclaim, since the packet's existing nonclaim says only that replay is "NOT_RUN unless the checker executed the recorded tools", not which author values survive that state.

## P3-3 — `build … --check` without `--replay` reports opaque drift
`tools/build_o008_formal_cycle_v1.py:60`. The prescribed command in my brief omitted `--replay`; because the committed packet carries an `EXECUTED` author record and `_author_record` returns `{"status": "NOT_RUN"}` without the flag, the projections differ and the tool reports `{"drift":["…json","…md"],"ok":false}` with exit 1 — a byte-drift message for a mode mismatch. With `--replay` it is `{"drift":[],"ok":true}`, exit 0. Repair: reject `--check` against a packet whose `author_record.status` differs from the mode implied by the flags, with a distinct code.

## P3-4 — The lifecycle test's third stage is definitional and unreachable at P3'
`tests/test_check_o008_formal_cycle_v1.py:1050`, stage 3 at `:1069-1073`. `consistent = report["errors"] == [] and report["current_source_drift"] == []` then `assert report["ok"] is consistent` restates `render_report_v1`'s own construction of `ok` (`tools/o008_formal_cycle_admission_v1.py:2513-2519`); the same is true of the `current_applicable` assertion. **It is not a weakening** — `git show HEAD^^:tests/test_check_o008_formal_cycle_v1.py` shows the stage is byte-identical to C1 apart from `PACKET_SCHEMA_V2` → `V3` — but at P3' `head_commit == packet_commit`, so only stage 2 executes and stage 3 asserts nothing about the fail-closed behaviour its docstring claims. Repair: drive the stage from a synthetic commit in the existing temporary-clone fixture layer instead of from the live repository.

## P3-5 — `declared_order` is a bespoke parser sound only for the current field types
`zk/global_settlement_abi_v1/tests/v1_projection_gate.rs:53`. It skips each value by scanning to the next `,`, so it desynchronises on any value containing a comma (nested object, array, or a string with a comma) and on an escaped quote. It is sound *as written* — every field is a `String`, a unit-variant enum, a `RootV1`, or a `u128`, and the fixture values contain no commas — but it will silently misreport the moment a record gains a structured field, which is exactly when the order check matters. Repair: compare `serde_json::to_value(&record)` keys against a `serde_json::Map` built by an ordered `Deserialize`, or use `serde_json::Value` with `preserve_order`.

---

# Verification record

All commands run in `/tmp/zenodex-formal-core-review-p-52d81ff35`, `PY="/home/trevormoc/Downloads/Autonomous Tau DEX/.venv/bin/python"`, cargo under `CARGO_TARGET_DIR=/tmp/zenodex-opus-c1prime-cargo-target CARGO_INCREMENTAL=0` (deleted after use, 259M reclaimed). Nothing written under `/dev/shm`; nothing written inside the worktree — `git status --porcelain` is empty for tracked *and* untracked at the end, and `HEAD` is still `52d81ff352296c570a4cf01e6cb4fd0bde1d4d59`.

| # | Command | Exit | Key output |
|---|---|---|---|
| 1 | `git status --porcelain \| grep -v '^??'` | 1 (grep, empty) | no tracked changes |
| 2 | `git diff-tree --no-commit-id --name-status -r HEAD^ HEAD` | 0 | exactly `M docs/research/ZENODEX_O008_FORMAL_CYCLE_V1.json`, `M …_V1.md` |
| 3 | `git diff --stat HEAD^^ HEAD^` | 0 | 8 files, 1679 insertions(+), 127 deletions(−); 3 added (THV1 v4, python gate, rust gate), 5 modified; **no Lean, no `state.rs`, no `lib.rs`, no `Cargo.toml`, no `src/core`** |
| 4 | checker, no replay | 0 | `ok=true`, `packet_admitted=true`, `current_applicable=true`, `current_source_drift=[]`, `errors=[]`, `head_commit == packet_commit == 52d81ff35…`, `subject_commit=d7b3a528b…`, replay `NOT_RUN` |
| 5 | checker `--replay` | 0 | `EXECUTED_PASS`, 11 runs all exit 0: lean_version 4.27.0; lean_direct_check stdout+stderr empty (`e3b0c442…`); lean_axioms_probe `theorems_probed=25`; lean_binding_gate 6; esso_validate `ir_hash=sha256:a4d1d07f6c9d…`; esso_verify_multi `VERIFIED`, z3 4.15.4 / cvc5 1.1.2, `esso_code_hash=7f80c6216be8…`; esso_gate 18; prior_restage_gate 136; python_version 3.12.3; **python_projection_gate 8; rust_projection_gate 5** |
| 6a | `build … --check` (no `--replay`, as prescribed) | **1** | `{"drift":["…json","…md"],"ok":false}` — mode mismatch, see P3-3 |
| 6b | `build … --check --replay` | 0 | `{"drift":[],"mode":"check","ok":true,"subject_commit":"d7b3a528b…"}` |
| 7 | `pytest -q tests/test_check_o008_formal_cycle_v1.py tests/test_o008_v1_projection_runtime_gate.py` | 0 | `211 passed in 58.17s` |
| 8 | `cargo test --offline --locked --test v1_projection_gate` | 0 | `5 passed; 0 failed` |
| 9 | `cargo clippy --offline --locked --all-targets -- -D warnings` | 0 | clean, no output |
| 10 | `check_test_hygiene_v1.py --base-ref fd409ba6f7da… --json` | 0 | `"ok": true`, `changed_path_count=30`, `critical_path_count=13`, `evidence_packet_count=81`; covered critical paths include both new gate files |
| 11 | `ruff check` (4 tools) | 0 | `All checks passed!` |
| 12 | `mypy --strict` (4 tools) | 0 | `Success: no issues found in 4 source files` |

Hand-recomputed pins at S3' (`git cat-file blob HEAD^:<path> \| sha256sum`):

```
tools/o008_formal_cycle_admission_v1.py    92b9f843e3826d85ca1f993ae188cc9e42802ec0d04e3c4bcb10dda2bf15cb04
zk/global_settlement_abi_v1/src/state.rs   44f6874589e72c7fefdcac8b6c220fb311c6dc0f1e53bb3b962e32a6d593b98c
tools/check_o008_formal_cycle_v1.py        3b148d47c647edc9af1f9232e234f7d54d23e9502d7fd9470476060d2c91ae2e
```
All three equal the packet's `source_pins` rows; the third also equals the report's `executing_tools` entry, so the executing checker bytes are S3' bytes. The other three executing tools match too: core `92b9f843…`, shell `f1ae83b46a1d…`, scanner `44a7c67142955…`.

Topology and chain: `P3'` has exactly one parent `d7b3a528bd9a16f5165c7776a045c9b967a9686f`; `packet.subject_commit == packet.packet_commit_parent == d7b3a528b…`; `packet.subject_parent == bfadf58bb…` (the Codex receipt commit, whose parent is the C2 packet `3feaa6224`); tree `5da848dfd…`; schema `zenodex/o008-formal-cycle-evidence/v3`.

Hygiene packet `tests/evidence/test_hygiene/THV1-20260901-o008-formal-cycle-admission-v4.json`: schema and `evidence_id` match the filename; all **20** pins (16 `source_pins` + 4 `test_pins`) equal the S3' blobs exactly (recomputed independently); it pins neither packet path; 38 mutations with 38 distinct `killed_by` node ids, **all present** in `pytest --collect-only` across the four gate files (235 nodes collected, 0 missing). It is the packet selected for all required paths.

Mutation matrix I ran against the pure core with full attacker re-pinning of the Lean gate `PINNED_SOURCES` and the THV1 v4 pins (`/tmp/opus-c1prime-exp/probe2.py`, `probe3.py`, `probe_gate.py`, `probe_hyg.py`, `probe_record.py`): 3 positive controls rejected with the right codes (`TERMINAL_FORBIDDEN_FIELD_PRESENT`, `RUST_DENY_UNKNOWN_FIELDS_MISSING`, `RUST_CFG_FORBIDDEN` — the last is Codex's exact P1 payload); 13 of 23 adversarial probes `[ACCEPTED]`, of which 4 (T1, T2, G1, G2) are load-bearing for the P1 findings and the rest are the P2/P3 gaps above.

---

# Nonclaims and residual risks

* I did **not** build a complete adversarial S′/P′ Git chain for P1-A. I demonstrated the three components separately and decisively — the pure core's `project_packet_v1` accepts the mutated `state.rs` after attacker re-pinning; the crate compiles; the five pinned gate tests pass; the compiled container accepts a widened row, with a pristine control that rejects it. Because admission is projection + topology + pin equality, and re-pinning simulates exactly the topology/pin half, I judge the chain to follow, but it is inference, not a mounted end-to-end run. Codex mounted its C1 chain; I did not mount mine.
* P2-2 (order-blind macro locality) is a soundness gap in the stated closure argument. I did **not** mount a schema divergence through it.
* P2-3's Python rebinds should be caught by the runtime gate under `--replay`; I reasoned this from the gate's assertions rather than executing a mutated import, and it is void if P1-B is exercised.
* The exact C1' subject's own `state.rs`, `lib.rs`, and `Cargo.toml` are unchanged from C1 and are correct: the records do carry `deny_unknown_fields`, the container is strict, and the control run confirms it. Every P1/P2 finding is an admission-gate survivor, not a mounted defect in the shipped code.
* `EXECUTED_PASS` still does not run the 211 admission-checker tests or `tools/check_test_hygiene_v1.py`; it now does run Cargo, which is a real improvement over C1.
* O-008 remains open at 0/12 value-movement gates; the all-lane allocation certificate is unimplemented, unattested, unmounted; ESSO remains a bounded one-asset/two-domain/two-claimant model; Lean establishes no finite-width runtime parity, cryptographic binding, or settlement authority.
* This grade is advisory and grants no authority.

# User decisions

All five honored, and I checked rather than assumed. S3' touches no Lean file, no `state.rs`, no `lib.rs`, no `Cargo.toml`, and nothing under `src/` — it is tooling, tests, and the two new gates — so the **claimant-free reserve partition** and **V1 wire-name byte stability** are untouched by construction, and the new code uses control-domain vocabulary throughout. **O-008A** appears nowhere as attested. **UP-01..UP-20**: `grep -o "UP-[0-9]*"` over the packet JSON returns nothing, so none is referenced, let alone fixture-selected. The packet's `claim_ceiling` is every authority `NONE`, `formal_core_complete: false`, `value_movement_gates_closed: 0` of 12, `o008_status: OPEN_EXACT_ALL_12_RECONCILIATION_MISSING` — identical under every mutation I mounted, since it is emitted from module constants.

Artefacts kept for you: `/tmp/opus-c1prime-exp/` (five probe scripts), `/tmp/opus-c1prime-cargo/` and `/tmp/opus-c1prime-cargo-terminal/` (the two compiling counterexample crates, 2.8M each). Cargo target dir deleted.
