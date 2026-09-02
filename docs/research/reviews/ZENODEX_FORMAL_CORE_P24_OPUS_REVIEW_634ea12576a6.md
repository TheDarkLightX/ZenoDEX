# Opus independent review — candidate C8''''''' (repair of P23 / receipt R20)

- Reviewer: Opus, independent. Authority granted by this review: **NONE**.
- Branch: `codex/formal-core-fable-20260901`
- Subject S24: `5c4b523251260a9a3584e626cfd8d53c1db00221`
- Artifact P24: `634ea12576a65038209894426706105ae311f774`
- Prior receipt R20: `6f1fc91082b18a357dfd4648d141b2bfe3bc0b7c` (A-; 0 P1, 0 P2, 1 P3 = NEW-11)
- Review worktree: `/tmp/zenodex-formal-core-opus-c8p7` (detached at P24; `git status --porcelain`
  empty at every checkpoint, including the last)
- Date: 2026-09-02

## Grade: A

**0 P1, 0 P2, 1 P3.** NEW-11 is **CLOSED**. The repair is exactly the one line I verified in
P23, and it is exactly right: on the real `canonical.rs` the widened regex returns the
identical 24 ordered name/expression pairs, and all five survivors I named — plus
`NonZeroUsize`, plus sixteen more mutants I constructed this round including tabs and a
newline between every token — now fail the key-set equality. `mutations[6]`'s stated class
("a different integer type **or spacing**") has no surviving member I could construct in 22
attempts. The v4 evidence packet is honestly scoped, all eleven of its pins verify, and it
is genuinely live: the hygiene gate selects it by pin match and runs 107 tests green.

The grade moves to A rather than being held by NEW-12, the one new P3 I found, and I want
to be explicit about why, because the P3 *count* is unchanged from P23. In P23 I set a
severity bar and used it to justify holding at A-: the NEW-11 residual mattered because the
type-alias form was **rustfmt-stable and reachable by an ordinary refactor** (the crate
already declares two `pub type`s). NEW-12 is strictly below that bar — it is pre-existing
(bit-identical on the P23 tree), it is not a single-edit member of any declared mutation
row, and it requires an author to write a deliberately misleading comment into a file that
the same evidence packet sha256-pins. Holding A- on a defect *less* reachable than the one
I said "should take the next round to A" would be a ratchet, not a standard.

The claim ceiling did not move.

---

## 1. Topology, admission, and replay

`git log --oneline` confirms a single-parent chain with an artifact-only leaf:

```
634ea1257 (P24) -> 5c4b52325 (S24) -> 6f1fc9108 (R20 receipt) -> f1c9c8490 (P23)
```

**S24 changes exactly two files** (7 lines changed in one, 240 inserted in the other):

| File | Change |
| --- | --- |
| `tests/core/test_global_settlement_abi_v1_resource_bounds.py` | one regex line + a three-line docstring rewrap |
| `tests/evidence/test_hygiene/THV1-20260901-global-settlement-v1-resource-bounds-v4.json` | new (240 lines) |

**P24 changes exactly the two packet files.** By `git diff --word-diff` the *only* changed
tokens in `ZENODEX_O008_FORMAL_CYCLE_V1.json` are `packet_commit_parent`, `subject_commit`,
`subject_parent`, and `subject_tree`; the `.md` changes the same three hashes. Nothing else
— no claim, no scope, no gate count.

### Checker, non-replay mode

```
$PY tools/check_o008_formal_cycle_v1.py --root /tmp/zenodex-formal-core-opus-c8p7 \
    --packet-commit 634ea12576a65038209894426706105ae311f774
```

exit 0 — `ok: true`, `packet_admitted: true`, `errors: []`, `current_source_drift: []`,
`current_applicable: true`, `proof_replay.status: NOT_RUN`. stderr empty (0 bytes). The
author record again correctly did not self-upgrade the replay status.

### Checker, replay mode — EXECUTED_PASS, 28/28, 0 non-zero exits

```
$PY tools/check_o008_formal_cycle_v1.py --root /tmp/zenodex-formal-core-opus-c8p7 \
    --packet-commit 634ea12576a65038209894426706105ae311f774 --replay \
    --python "$PY" --esso-python /home/trevormoc/Downloads/ESSO/.venv/bin/python \
    --esso-pythonpath /home/trevormoc/Downloads/ESSO
```

exit 0, stderr empty (0 bytes), `proof_replay.status: EXECUTED_PASS`, 28 runs, **0 non-zero
exits**. Every observed value is identical to my P23 replay:

| command_id | observed | command_id | observed |
| --- | --- | --- | --- |
| lean_version | 4.27.0 | prior_restage_gate | 136 passed |
| lean_direct_check | empty stdout | python_version | 3.12.3 |
| lean_axioms_probe | 25 theorems | python_projection_gate | 13 passed |
| lean_binding_gate | 6 passed | rust_projection_gate | 7 passed |
| lean_certificate_direct_check | empty stdout | rust_version | cargo 1.87.0 |
| lean_certificate_axioms_probe | 16 theorems | rust_compiler_version | rustc 1.87.0 |
| lean_certificate_binding_gate | 6 passed | rust_refinement_gate | 41 passed |
| esso_validate | ir_hash ok | python_golden_gate | 35 passed |
| esso_verify_multi | z3 4.15.4 + cvc5 1.1.2 VERIFIED | rust_golden_gate | 3 passed |
| esso_gate | 20 passed | rust_bounded_vec_unit_gate | 1 passed |
| esso_certificate_validate | ir_hash ok | python_certificate_golden_gate | 37 passed |
| esso_certificate_verify_multi | z3 4.15.4 + cvc5 1.1.2 VERIFIED | rust_certificate_golden_gate | 3 passed |
| esso_certificate_gate | 24 passed | rust_certificate_unit_gate | 4 passed |
| | | python_producer_gate | 30 passed |
| | | rust_producer_gate | 7 passed |

The two Lean gates and the cargo gates were executed by the checker strictly serially. I ran
**nothing** concurrently while the replay was in flight — no Lean invocation of any kind
occurred outside the checker, and the cargo battery below was started only after the replay
process had exited.

### Claim ceiling — unchanged, and byte-identical to P23

```
formal_core_complete        false
formal_cycle_status         FORMAL_CYCLE_COMPLETE_O008_OPEN
o008_status                 OPEN_EXACT_ALL_12_RECONCILIATION_MISSING
supported_claim             O008_RELATION_NECESSARY_CHECKS_AND_INFORMATION_LOSS_PROVED
migration/production/publication/release/settlement/value_movement/verifier  NONE
value_movement_gates_closed 0 of 12
whole_value_movement_safe   false
```

Compared as parsed dicts between the P24 packet and the P23 packet (`f1c9c8490`):
`P24 ceiling == P23 ceiling: True`, differences: **none**. Also equal between the checker's
non-replay and replay reports. Nothing raised it.

### Independent batteries

| Battery | Command | Result |
| --- | --- | --- |
| Full cargo | `cargo test --offline --locked` in `zk/global_settlement_abi_v1` | **53 suites, 523 passed, 0 failed, 0 ignored, 0 warnings** |
| cargo all-targets | `cargo test --all-targets` | 52 suites, 522 passed, 0 failed (delta = the 1 doc-test) |
| Repair test file | `pytest tests/core/test_global_settlement_abi_v1_resource_bounds.py` | **19 passed** (unchanged from P23) |
| Module suites | transfer module + transfer lane module + managed lifecycle + `test_global_settlement_abi_v1.py` + checker gate + repair file | **531 passed** |
| Closure digest | `tools/check_global_settlement_canonical_manifest_v1.py` | **PASS** |
| Test hygiene | `tools/check_test_hygiene_v1.py --base-ref 6f1fc9108 --json` | **ok: true**, 4 changed paths, 1 critical path, 86 node ids, 136 packets |
| Hygiene gate (executes) | `tools/run_test_hygiene_gate_v1.py` on the two S24 paths | **ok: true**, **107 passed** |
| ruff (configured) | `ruff check` on the source + test file | **All checks passed** |
| ruff E303 preview | `ruff check --select E303 --preview --no-cache` | **All checks passed** |

The cargo count matches P23 exactly (523/53). I deleted `/tmp/zenodex-opus-c8p7-cargo`
(1.8 GB) immediately after the battery, as asked; root went from 98% back to 98% with 9.0 GB
free.

### Pin integrity

All eleven pins in `resource-bounds-v4` recomputed against the tree at P24: **0 mismatches**
(8 source pins, 3 test pins, 86 node ids). In particular
`tests/core/test_global_settlement_abi_v1_resource_bounds.py` pins to
`a10085318fa612812871e15cd1a12196079f914a449a97943a7658cbaad235b3`, which is the file's
actual hash after the repair.

I checked the obvious hazard — that the changed test file would leave a *stale* pin in an
older packet. `resource-bounds` v1/v2/v3 do pin the historical hashes
(`f7705ca9…`, `8fa0cc4b…`, `3c9841f8…`), but that is this campaign's established versioning
convention (v3 sat beside v1/v2 the same way last round), and the gate is changed-path
driven: it selected **only** `resource-bounds-v4`. No admission packet pins this test file,
so nothing else went stale. `v4` is not orphaned — it is the packet the gate chooses.

---

## 2. The P23 finding — verdict: **CLOSED**

### 2.1 The repair is exactly the verified line

`tests/core/test_global_settlement_abi_v1_resource_bounds.py:225`
(sha256 `a10085318fa612812871e15cd1a12196079f914a449a97943a7658cbaad235b3`):

```python
r"pub\s+const\s+(MAX_[A-Z0-9_]+)\s*:\s*[A-Za-z0-9_:]+\s*=\s*([^;]+);",
```

This is byte-for-byte the pattern I proposed and verified in P23. `pub` and `const` are now
separate tokens with `\s+` between them and before the name; the type class admits `_`,
uppercase and `::`.

### 2.2 Zero-diff on the real `canonical.rs` — re-verified independently

`zk/global_settlement_abi_v1/src/canonical.rs`
(sha256 `6cce2178582ae4f38ff95fade6f544ae54b0d7568b7599dfa6214a56515cd46a`, matching the v4
source pin):

```
old pairs: 24   new pairs: 24
IDENTICAL ordered pair list: True
IDENTICAL as dicts:          True
duplicate names in new:      []
```

The widening is behaviour-preserving on the shipped file — the same 24 pairs in the same
order, with no name collapsed by the dict comprehension. The `>= 24` floor at `:241` remains
tight.

### 2.3 Mutation battery — 22 mutants, all killed, baseline green

Run against the real in-repo test through a mirror root (`/tmp/c8p7-mut`) whose `src/` is a
symlink into the worktree and whose test file and `canonical.rs` are copies (a *symlinked*
test file would defeat the harness, because `Path(__file__).resolve()` follows symlinks).
The worktree itself was never modified — `git status --porcelain` empty afterwards.
Harness: `/tmp/c8p7_mutants.sh`.

| Mutant | P23 result | P24 result |
| --- | --- | --- |
| M0 baseline | 1 passed | **1 passed** |
| `pub const  MAX_X: usize` (2 spaces const→name) | **survived** | **1 failed** ✓ killed |
| `pub  const MAX_X: usize` (2 spaces pub→const) | **survived** | **1 failed** ✓ killed |
| `pub const\n    MAX_X: usize` | **survived** | **1 failed** ✓ killed |
| `pub const MAX_X: RowCountV1` (CamelCase alias) | **survived** | **1 failed** ✓ killed |
| `pub const MAX_X: core::primitive::usize` | **survived** | **1 failed** ✓ killed |
| `pub const MAX_X: NonZeroUsize` | (named, untested) | **1 failed** ✓ killed |
| `u32` / `i64` / `u16` / `u8` / `isize` / `i128` / `usize` | killed | **1 failed** ✓ still killed |
| newline after `=` / before `=` / before `:` | killed | **1 failed** ✓ still killed |
| `MAX_X  :  usize  =  77;` (multi-space) | killed | **1 failed** ✓ still killed |
| **X1 tabs between every token** | not tested | **1 failed** ✓ killed |
| **X2 newline between every token** | not tested | **1 failed** ✓ killed |
| **X3 `crate::MyAlias`** | not tested | **1 failed** ✓ killed |
| **X4 `u_size` (underscore type)** | not tested | **1 failed** ✓ killed |
| **X5 space before `;`** | not tested | **1 failed** ✓ killed |
| C1 value drift `4_096` → `8_192` | killed | **1 failed** ✓ still killed |
| C2 delete `MAX_ASSET_CUSTODY_ROWS_V1` | killed | **1 failed** ✓ still killed |

All six of the survivors the lead asked me to re-run are captured and fail the key-set
equality. C1/C2 pass through as controls proving the mirror is live (a stale mirror reading
the worktree's `canonical.rs` would show them passing).

### 2.4 `mutations[6]`'s class is empty

`tests/evidence/test_hygiene/THV1-20260901-global-settlement-v1-resource-bounds-v4.json`
(sha256 `a631b5153d6b94122e0763c40cd31d0f1c8cb01594e0b146c80b6076f4646812`). Numbering is
worth stating once, because the packet's prose and my P23 report use 0-based indices:

```
mutations[6]  (the 7th row): "declare a canonical bound with a different integer type
                              or spacing (Opus P22 NEW-7)"
              killed_by:     test_every_canonical_rust_bound_has_a_python_twin
```

Its class is **integer types** ∪ **spacing**. Every integer primitive (`i8`…`i128`,
`u8`…`u128`, `isize`, `usize`) is killed, and every inter-token whitespace form I could
construct — single/multiple spaces, tabs, and newlines at each of the four positions,
including a newline between *every* token — is killed. I could not construct a surviving
member. **The row is honest.**

The claim strings are also now true as written for every spelling I identified as
realistic. The v4 `claim_scope` is scoped rather than absolute — "admits any type spelling
(primitive, CamelCase alias, path-qualified)" — and so is the docstring at `:192-197`. That
closed enumeration is exactly what I asked for as the alternative to the widening, and the
author did both.

---

## 3. New findings

### NEW-12 (P3) — a trailing comment repeating a bound masks a real value drift, in *both* parity tests

**Where.**
- `tests/core/test_global_settlement_abi_v1_resource_bounds.py:225` (total-parity regex) and
  `:183` (frozen-equality regex). Neither strips comments, and both feed `re.findall` into a
  **dict comprehension**, so on a duplicated name the *last* occurrence in the file wins.

**Minimal repro** (mirror root as in §2.3; `MAX_EFFECT_PLAN_ROWS_V1` is a shipped bound
covered by *both* tests):

```bash
sed -i 's/pub const MAX_EFFECT_PLAN_ROWS_V1: usize = 4_096;/pub const MAX_EFFECT_PLAN_ROWS_V1: usize = 8_192;/' \
    zk/global_settlement_abi_v1/src/canonical.rs
pytest -q tests/core/test_global_settlement_abi_v1_resource_bounds.py::test_every_canonical_rust_bound_has_a_python_twin
# => 1 failed        (correct: the drift is caught)

printf '\n// pub const MAX_EFFECT_PLAN_ROWS_V1: usize = 4_096;\n' >> \
    zk/global_settlement_abi_v1/src/canonical.rs
pytest -q tests/core/test_global_settlement_abi_v1_resource_bounds.py::test_every_canonical_rust_bound_has_a_python_twin
# => 1 passed        (the drift is now masked)
pytest -q tests/core/test_global_settlement_abi_v1_resource_bounds.py::test_python_and_rust_v1_collection_limits_are_frozen_and_equal
# => 1 passed        (also masked)
```

Rust now enforces 4 096 → 8 192 while both parity tests report agreement with Python's
4 096. The docstring's universal — "Every `pub const MAX_...` declaration in canonical.rs …
must resolve through this single mapping **with an equal value**" — is false under an input
the test accepts, and `admission-v24`'s "parity over canonical.rs is TOTAL (… with an equal
value)" is false with it.

**Provenance — this is not a regression.** I re-ran the identical sequence against the P23
tree (`/tmp/zenodex-formal-core-opus-c8p6`, pre-repair narrow regex): baseline passed, drift
alone failed, drift + comment passed, frozen test passed. Bit-identical behaviour. The
widening neither introduced nor worsened it, and it predates my P21/P22/P23 reviews, all of
which missed it — mine included.

**Why it does not hold the grade.** It is a two-edit evasion, not a single-edit surviving
mutant of any declared row (`mutations[2]`'s own mutant — change one constant — *is* killed,
as C1 and the first command above show). It is unreachable by refactor or `cargo fmt`; it
requires an author to write a comment whose only purpose is to deceive the parser. And the
same v4 packet sha256-pins `canonical.rs`, so any edit to that file — masked or not — breaks
the pin and forces a new evidence packet through review. Against the accidental-drift threat
model these tests actually serve, they work.

**Suggested repair (not applied), one line.** Make duplicate capture loud rather than
silent, at `:230-236`:

```python
matches = re.findall(r"pub\s+const\s+(MAX_[A-Z0-9_]+)\s*:\s*[A-Za-z0-9_:]+\s*=\s*([^;]+);",
                     rust_source, re.S)
rust_bounds = {name: evaluate(expression) for name, expression in matches}
assert len(matches) == len(rust_bounds), "duplicate MAX_ capture in canonical.rs"
```

I verified this assertion is satisfied by the real file today (24 matches, 24 distinct
names), so adding it is zero-diff on the shipped tree. Stripping `//` and `/* */` before
matching would be the stronger fix; the duplicate assertion is the cheaper one and catches
the mask directly.

---

## 4. Observations (not findings)

1. **Residual regex escapes are all outside the claimed class and none is realistic.** Four
   spellings still escape: `Wrapping<usize>` and `[usize; 1]` (angle/square brackets are
   outside `[A-Za-z0-9_:]`), `core :: primitive :: usize` (spaces inside the path), and
   `pub(crate) const MAX_…` (`\s+` cannot match `(`). I checked realism the same way I did in
   P23, and unlike the `RowCountV1` case none of these clears the bar: the crate has **zero**
   generic- or array-typed consts and **zero** `pub(crate) const` (it uses `pub(crate)` 119
   times, but never on a const), and the spaced-path form is not `rustfmt`-stable. The v4
   `claim_scope` and the docstring both enumerate the admitted spellings rather than saying
   "any type", so they do not over-claim these. `admission-v24`'s older unqualified "every
   pub const MAX_ bound" phrasing does, technically, but the two rustfmt-stable spellings I
   cited against it in NEW-11 are now both killed. If the next round wants the phrasing to be
   literally exhaustive, `pub(?:\([a-z]+\))?\s+const` plus a lazy `[A-Za-z0-9_:<>\[\]; ]+?`
   type class covers all four. I ran it: it returns the **identical 24 ordered pairs** on the
   shipped `canonical.rs` and captures all four residual spellings above.

2. **The "total" parity is total over one *file*, and 13 more bounds sit outside it.** The
   test scans only `zk/global_settlement_abi_v1/src/canonical.rs`. The crate declares 41
   `MAX_` consts in total; 13 of the ones outside that file are `pub`, and **all 13 have a
   Python `Final` twin that is actually enforced** (`MAX_ASSET_TRANSFER_POLICIES_V1`,
   `MAX_COMMAND_AUTHORIZATIONS_V1`, `MAX_COMMAND_SIGNATURE_BYTES_V1`,
   `MAX_COMMAND_SIGNATURE_VERIFIER_ARTIFACT_BYTES_V1`,
   `MAX_COMMAND_SIGNATURE_VERIFIER_RELEASES_V1`, `MAX_DECIMAL_SCALE_STEP_V1`,
   `MAX_FRAGMENT_ROWS_V1`, `MAX_INITIAL_STATE_ATOM_ROWS_V1`,
   `MAX_INITIAL_STATE_OUTBOX_ROWS_V1`, `MAX_MANAGED_ASSET_POLICIES_V1`,
   `MAX_PERPS_MARGIN_ACCOUNTS_V1`, `MAX_ZDEX_PROJECTION_BUCKETS_V1`,
   `MAX_ZDEX_TOKENOMICS_FEE_ASSETS_V1`). The wording does say "over canonical.rs", so this is
   not an over-claim — but it is the highest-value cheap win available: **I checked all 13
   cross-language pairs and every one is currently in parity, 0 drift**, so extending the
   same regex over `zk/global_settlement_abi_v1/src/**.rs` and resolving twins across modules
   would take coverage from 24 to 37 bounds and be green on the first run.

3. **The parity test is deliberately one-directional** (every Rust bound has a Python twin;
   a Python-only `MAX_` is not caught except for the one hardcoded lane-module name). The
   test's name says so, and the frozen test covers 12 names in both directions. Noting it
   only so it is not mistaken for symmetry.

4. **`evaluate()` remains fail-closed.** I re-checked every path: anything it cannot parse
   (`0x1000`, `4_096usize`, `4_096 + 1`, a trailing comment inside the expression) raises
   through `int()` and errors the test loudly. There is no silent-skip path.

5. **Cosmetic.** The docstring rewrap at `:192-196` left one short unwrapped line
   ("resolve through this single" / "mapping with an equal value"). Harmless; it just reads
   as a mechanical edit that was not re-flowed.

6. `resource-bounds-v4`'s `boundary_dimensions` still lists the same three dimensions as
   v2/v3; the two transition-ceiling boundaries are still carried by `mutations[5]` and
   `mutations[7]` rather than by dimensions of their own. Repeated from P23, unchanged, not
   an over-claim.

7. **Disk.** Root was at 98–99% throughout (8.7–9.1 GB free). I freed my 1.8 GB
   `CARGO_TARGET_DIR` immediately after the battery. Sibling review target dirs belonging to
   other agents remain; I did not touch them. Same flag as P23: a full root will eventually
   make a replay fail in a way that looks like an evidence failure.

---

## 5. Verdict

C8''''''' does one thing and does it correctly. The single line I specified in P23 is the
single line that shipped, its zero-diff property holds on the real `canonical.rs` (24
identical ordered pairs), and every survivor I named is now killed along with sixteen more
mutants I built this round. `mutations[6]`'s stated class is empty as far as I can construct
it. The new v4 packet scopes its claim to what the regex actually enforces, pins eleven
files that all verify, and is the packet the hygiene gate really selects — it ran 107 tests
green. Full replay is EXECUTED_PASS at 28/28 with every observed value identical to the
previous round, cargo is 523 passed across 53 suites with zero warnings, Python is 19 + 531
passed, ruff is clean, the closure digest passes, and the claim ceiling is byte-identical to
P23.

NEW-12 is a real defect and the next round should fix it — a value drift on a shipped
consensus bound can be hidden from both parity tests by one trailing comment. But it is
pre-existing, orthogonal to this repair, not a member of any declared mutation row under
single-edit semantics, and gated behind a sha256 pin on the very file it would have to
modify. It is a smaller problem than the one this round closed, and I am not going to hold a
grade on a defect I twice failed to find myself while the assigned repair came back exact.

**Grade: A. 0 P1, 0 P2, 1 P3 (NEW-12). NEW-11: CLOSED.**

Authority granted: **NONE**. `formal_core_complete` remains **false**, `o008_status` remains
`OPEN_EXACT_ALL_12_RECONCILIATION_MISSING`, and value-movement gates remain 0 of 12. The
claim ceiling did not move and must not move on the strength of this review.

---

## Appendix — sha256 of every file quoted

```
24e43906cc390581611896a099cf2710a9d42c4ab93a00f0e82cbb8cd4d5267e  docs/research/ZENODEX_O008_FORMAL_CYCLE_V1.json
ba7c15c94c7182f9e73c7930443657bb23848ceaaf6d1ae2fb633ee989a7df73  docs/research/ZENODEX_O008_FORMAL_CYCLE_V1.md
a10085318fa612812871e15cd1a12196079f914a449a97943a7658cbaad235b3  tests/core/test_global_settlement_abi_v1_resource_bounds.py
a631b5153d6b94122e0763c40cd31d0f1c8cb01594e0b146c80b6076f4646812  tests/evidence/test_hygiene/THV1-20260901-global-settlement-v1-resource-bounds-v4.json
372a8444a833e466fbd7cfa850ac664e15d5ac2f83089619dbae8f6b5cac8835  tests/evidence/test_hygiene/THV1-20260901-global-settlement-v1-resource-bounds-v3.json
474ec652969657453bd68615b3e3eba71f009577a23b9397680a9e52febc5b89  tests/evidence/test_hygiene/THV1-20260901-o008-formal-cycle-admission-v24.json
6cce2178582ae4f38ff95fade6f544ae54b0d7568b7599dfa6214a56515cd46a  zk/global_settlement_abi_v1/src/canonical.rs
854a65b68a0c76a3af3afc62b53eb48c333b9e87f854e8f10fd54a851ff27ac4  src/core/global_settlement_types_v1.py
2d0d7116faecde2090a00ca38dad91e9bbb3e7f0597045750ceeed8725bd938c  src/core/asset_transfer_module_v1.py
613ae04adb22bc15bde4a1641c892d7292dd6f24ad03f240e6dd424c66e297fd  src/core/managed_asset_lifecycle_module_v1.py
```

Harnesses used (outside the worktree): `/tmp/c8p7_mutants.sh`, `/tmp/c8p7_probe.sh`,
mirror roots `/tmp/c8p7-mut` and `/tmp/c8p7-mut-old`.
