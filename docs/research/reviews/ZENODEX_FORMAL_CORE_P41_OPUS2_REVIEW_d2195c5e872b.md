# ZenoDEX Formal Functional Core Closure — C9c-4 (P41) second independent review

| field | value |
|---|---|
| subject | S41 `f111ec292f01dbaede9cf0cdfee8d1594989f456` — "fix: make the evidence standard real, and say what UNDETERMINED actually means" |
| artifact | P41 `d2195c5e872bd89c098fa9b5abd5ff3db9820674` (artifact-only child; `docs/research/ZENODEX_O008_FORMAL_CYCLE_V1.{json,md}`) |
| packet json sha256 | `c269a5f2b19a4627ea0aad25cfd06d85e776aeab277b71352ea72a50d9598456` (matches the expected value) |
| worktree | `/tmp/zenodex-formal-core-opus2-c9c4` (detached at P41; `git status --short` empty at start and at end) |
| reviewer | second reviewer, fresh-context Opus 5 session |
| date | 2026-09-03 |
| verdict | **B−** — 2 P1, 5 P2, 6 P3. REVISE (advisory). Authority stays NONE; the claim ceiling did not move. |

## Independence caveat (stated as required)

This campaign's second reviewer is normally a fresh-context Fable 5.1 session. Fable is out of usage
credit until 2026-09-06, so **both of this round's reviewers are fresh-context Opus 5 sessions and the
independence is weaker than the campaign standard**: the two reviewers and the author share a model
family. I had no access to the primary reviewer's worktree, report, or session, and did not attempt to
infer their findings. Read this report as one of two same-family reviews, not as an independent
cross-model check.

---

## 1. Replays executed here

Environment: `PY=/home/trevormoc/Downloads/Autonomous Tau DEX/.venv/bin/python`,
`PYTHONDONTWRITEBYTECODE=1`, `CARGO_INCREMENTAL=0`. Every Lean-bearing command ran under
`flock -w 7200 /tmp/zenodex-lean.lock`. Worktree preparation needed two symlinks the review prompt
omits — `lean-mathlib/.lake/packages/mathlib` and `external/mathlib4`, both to
`/home/trevormoc/deps/mathlib4` — because `lean-mathlib/lakefile.lean:7` does
`require mathlib from "../external/mathlib4"`. That is a review-environment fact, not a defect.

| command | result |
|---|---|
| `check_o008_formal_cycle_v1.py --root $PWD --packet-commit d2195c5e8` | exit 0; `ok true`, `packet_admitted true`, `current_source_drift []`, `proof_replay NOT_RUN`. Result sha256 `50a9e71cef73f09b16678577fc4054aa299efe4aa96022f7437f81b9787fadbb` |
| same `--replay --esso-python /usr/bin/python3 --esso-pythonpath …/ESSO` | exit 0; **`EXECUTED_PASS`, 38 runs**, `ok true`, `errors []`, `current_source_drift []`. Result sha256 `92a35aed13c6b2b920027761b40d6a7d2ea15f9ce8b7c4850949cc5fe20a9da0` |
| — the six ledger runs inside it | `ledger_projection_rows` 24, `ledger_tool_rows` 18, `ledger_admission_rows` 31, `ledger_ownership_rows` 21, `ledger_certificate_rows` 2, `ledger_lineage_rows` 1 = **97 killed, 0 survived, 0 errors**, each exit 0 — exactly the declared figures |
| `build_o008_formal_cycle_v1.py … --check --replay --output-json/-md` | exit 0; `ok true`, **`drift []`**; `git status --short` empty after; the packet regenerates byte-identically to `c269a5f2…` |
| `cargo fmt --all -- --check` (`zk/global_settlement_abi_v1`) | exit 0 |
| `cargo clippy --locked --all-targets -- -D warnings` | exit 0 |
| `cargo test --locked` | exit 0; 54 summaries, **536 passed**, 0 failed — matches the declared figure |
| `tests/core/test_global_accounting_allocation_projection_v1.py` | **79 passed** (declared `PROJECTION_GATE_EXPECTED_PASSED_V1 = 79`) |
| `tests/formal/test_lean_asset_transfer_refinement_v1.py` (under the lock) | exit 0; **40 passed** (declared 40) |
| `tests/core/test_transition_resource_bound_totality_v1.py` | 10 passed |
| `tests/core/test_global_settlement_abi_v1_resource_bounds.py` | 17 passed |
| `tests/core/test_global_settlement_abi_v1.py` | 75 passed |
| `tests/test_check_o008_formal_cycle_v1.py` | 398 passed (236 s) |
| `tests/test_check_global_settlement_canonical_manifest_v1.py` | 8 passed |
| `check_test_hygiene_v1.py --json` | exit 0; `ok true`, **231 packets**, `changed_path_count 0` |
| `--base-ref ad91dbae4 --json` (parent of S41) | exit 0; `ok true`, 231 packets, 17 changed |
| `--base-ref fd409ba6f7d… --json` (campaign base) | exit 0; `ok true`, 231 packets, 414 changed — **the campaign base is green** |

`tests/core/test_zusd_liquidation_partition.py` excluded as instructed.

### Pin audit

* O-008 packet: **58** `source_pins`, all byte-exact on `sha256`, `git hash-object` **and** `size`;
  0 mismatches. **38** replay commands as declared. `hygiene_selection`: 55 rows, every
  `packet_sha256` and `pin_sha256` byte-exact, 0 mismatches.
* The five THV1 packets cut by this candidate: **87** `source_pins` + `test_pins`, **0 bad**;
  **707** pinned pytest node ids, **0 orphans** (each resolves to a real `def` in its pinned file).
* `subject_tree` `1e82e689c5412ab5a3cbdd3ee6d1a2c3955b6ee8` equals `git rev-parse f111ec292^{tree}`;
  `subject_parent` = `ad91dbae4`, `packet_commit_parent` = `f111ec292`. P41's complete diff is the two
  packet files.
* Claim ceiling: `migration/production/publication/release/settlement/value_movement/verifier_authority`
  all `NONE`; `formal_core_complete false`; `o008_status OPEN_EXACT_ALL_12_RECONCILIATION_MISSING`;
  `value_movement_gates_closed 0 / 12`. **The ceiling did not move.**
* Required nonclaims present: no Rust twin (THV1 v4 nonclaim 6), fixture partition is not a general
  property (9), a refusal does not say the state is invalid (10), nothing consumes it (2).

### Independent mutation execution (not via the packet's own runner)

I extracted `src/ tests/ tools/` from HEAD into `/tmp/opus2c9c4-mut` and, for every declared row,
applied the mutant, ran only the row's named killer, and restored:

* `THV1-…-global-accounting-allocation-projection-v4`: **24/24 killed**, no needle-count anomalies.
* `THV1-…-thv1-mutation-ledger-v5`: **18/18 killed**. `THV1-…-lineage-ordering-v5`: **1/1 killed**.
* Deduplication audit: `set(v5 triples) == set(v4 triples)` for both deduplicated packets, with
  0 dropped and 0 added — the lowered gate numbers (22→18, 2→1) removed repeats only, no distinct
  work was lost. The commit's "92 distinct before, 97 after" reconciles exactly.

---

## 2. One verdict per claim

### C1. The evidence standard is executed, not declared — **CLOSED**

Reproduced the primary reviewer's falsification without touching the worktree, with a pytest plugin
that rebinds `_no_certificate_reconciles` after collection:

```bash
cat > $SCRATCH/mutplugin.py <<'EOF'
import sys
def pytest_collection_finish(session):
    for n in [n for n in sys.modules if "test_global_accounting_allocation_projection_v1" in n]:
        m = sys.modules[n]
        if hasattr(m, "_no_certificate_reconciles"):
            def boom(*a, **k): raise AssertionError("MUTANT")
            m._no_certificate_reconciles = boom
EOF
PYTHONPATH=$SCRATCH:$PWD "$PY" -m pytest -q tests/core/test_global_accounting_allocation_projection_v1.py \
  -p no:randomly -p mutplugin | tail -1
#   -> 8 failed, 71 passed        (at P40: 53 passed, unchanged)
```

The helper is called for all eight UNRECONCILABLE row cases. I also verified the candidate's specific
claim about the omitted terminal checks by re-implementing the P40 four-check version and running both
over the same eight cases: the old helper returns `ACCEPTED` for exactly **4** of them ("one terminal
over-claiming its entitlement", "two terminals over-claiming together", "a claimant with no entitlement
at all", "an OPEN obligation naming another lane") and the new one returns `TERMINAL_BINDING_DRIFT`.
The "four of those cases would have passed" statement is accurate.

What it establishes is narrower than the claim in two places — see **P2-1**.

### C2. UNDETERMINED no longer claims two ACCEPTED certificates — **PARTIAL** (P1-1, P1-2)

The exhibition is real. `test_an_undetermined_state_admits_two_row_checked_certificates_with_different_roots`
(`tests/core/…_projection_v1.py:825-861`) builds two candidates over one state with
`source_principal` `pool-a` / `pool-b`, both passing `_check_exactly_once`, `_check_entitlement_rows`,
`_check_external_obligations` and `_check_lane_aggregates`, with two distinct `allocation_root`s, and
the full checker refuses both with `RECEIPT_WITNESS_REQUIRED`. I reproduced this independently.

`grep -rni "accepted certificate"` over the module, the test file and the THV1 packet finds **no
surviving assertion** of the false form in the module docstring, the enum docstring or the test
docstring — every occurrence there is the corrected negation.

But the hunt the brief asked for turns up the sentence in **three** of the six named places, all of them
inside the pinned artifact (**P1-1**), and the *replacement* definition is itself false for reachable
sub-cases of both its codes (**P1-2**).

### C3. Which row cases the entry point reaches is pinned — **CLOSED**

Ran each of the twelve `_ROW_CASES` through `project_allocation_certificate_v1` myself. Exactly two
reach their own code — "entitlements exceeding custody" → `PROJECTION_NEGATIVE_RESIDUAL` and
"controlled atoms no obligation can absorb" → `PROJECTION_UNASSIGNED_CONTROLLED_ATOMS` — and the other
ten are masked by `PROJECTION_ROWS_BEYOND_PRODUCER`. That is exactly the set fixed at
`tests/core/…_projection_v1.py:883` (`reaches_entry`).

The primary reviewer's Falsification B is closed. The `SPOT_LIQUIDITY`/`NO_PRODUCER` probe that
returned `PROJECTION_TERMINAL_EXCEEDS_ENTITLEMENT` at P40 now returns
`PROJECTION_ENABLED_LANE_WITHOUT_PRODUCER`. Note for the record: the gate that closes it,
`_state_level_refusals_v1` (`src/core/…_projection_v1.py:277-311`), is **new in C9c-4**, not carried
from C9c-3 as the review brief states.

### C4. The headline guard has a mechanical row — **CLOSED**

Row 21 of the projection packet mutates `                if beyond:` and is killed by
`test_which_row_cases_the_entry_point_reaches_is_pinned[one-terminal-over-claiming-its-entitlement]`
(verified: exit 1). I then looked for any guard added in C9c-3 or C9c-4 that still has none, and found
none: the three other new branches all carry rows that kill — row 22 (`if not principals:` →
`PROJECTION_TERMINAL_WITHOUT_BACKING`), rows 23 and 24 (the two state-level gates). All 24 kill.

### C5. The Rust guard is tested by something that calls it — **CLOSED**

I rebuilt the crate in a faithful copy (`/tmp/opus2c9c4-proberepo`, with `tests/data/` and
`tests/fixtures/` present, because `fixture_value()` at
`zk/global_settlement_abi_v1/src/global_accounting_allocation_certificate.rs:1523-1527` reads
`$CARGO_MANIFEST_DIR/../../tests/data/…`; a bare crate copy fails for that reason and not for the
mutation's, which cost me one wrong result before I caught it).

Baseline: `cargo test --locked --no-fail-fast` → 536 passed, 0 failed; `--lib` → 16 passed.
With the guard body replaced by `let _ = controlled;` (the packet's declared mutant, byte-exact):

```
cargo test --offline --locked --lib -- global_accounting_allocation_certificate::tests::the_source_principal_guard_refuses_and_the_check_is_what_refuses
  -> test result: FAILED. 0 passed; 1 failed; 15 filtered out
cargo test --offline --locked --no-fail-fast
  -> exit 101; 54 summaries; one FAILED (15 passed, 1 failed); the other 53 ok
```

**535 passed at P40 with the guard deleted; the crate now fails.** The attack on the new killer form is
**P2-2**: it does not qualify a mutant nothing exercises, but it binds neither the declared file nor a
named test.

### C6. The ledger grader refuses three more shapes — **CLOSED, with the stated limits verified**

`tools/o008_formal_cycle_admission_v1.py:4137-4159`. Non-digest digests and non-portable paths are
refused; `seen` rejects a repeated `(path, needle_sha256, replacement_sha256)` triple. Five negative
tests plus a positive complement at `tests/test_check_o008_formal_cycle_v1.py:1248-1295`.

(a) The distinctness rule's catch of the author's own packets is **honest**: verified above that the
deduplication removed repeats only. Lowering the gate numbers rather than weakening the rule was the
right call and the disclosure ("inflated counts, not false evidence") is accurate.

(b) The `_grade_ledger` docstring's statement of what it cannot check **is accurate**:
`tools/test_hygiene_evidence_v1.py:289` does enforce `mutant path is not a pinned source path`, and
`check_test_hygiene_v1.py` is not run by this checker (nonclaim 14). Verified by reading both.

Two residues: three of the six `REPLAY_LEDGER_*` codes still have no test (**P2-5**), and the test
helper's own docstring claims a guard that was withdrawn (**P3-1**).

Other packets with duplicate mechanical rows: I hashed every row of all **231** packets. Three declare
duplicates — `THV1-20260903-thv1-mutation-ledger-v3` (19 rows / 18 distinct), `…-v4` (22 / 18) and
`THV1-20260902-test-hygiene-lineage-ordering-v4` (2 / 1). All three are superseded predecessors of the
two this candidate deduplicated, and none is ledger-gated now. No other packet in the tree has a repeat.
The distinctness rule lives only in `_grade_ledger`, not in the packet validator, so all three still
pass `check_test_hygiene_v1.py`.

### C7. A terminal with zero candidate principals is UNRECONCILABLE — **PARTIAL** (P2-3)

`PROJECTION_TERMINAL_WITHOUT_BACKING` exists, is raised before the `!= 1` test, is in the
`unreconcilable` kind, and has a killing mechanical row. The classification is right.

I confirmed the unreachability claim rather than accepting it, and **half of it is false** — see
**P2-3**. The entry-point half holds; the row-harness half does not.

### C8. The family is 16 codes in three kinds, held as data — **PARTIAL** (P1-2)

`ALLOCATION_PROJECTION_REFUSAL_KINDS_V1` (`src/core/…_projection_v1.py:164-185`) is exhaustive,
disjoint and pinned by `test_the_three_refusal_kinds_partition_the_family` (`:487-506`), which also
scans the enum docstring for every member. That is the *exhaustiveness* question and it is closed.

The *membership* question — is any code in the wrong kind — is **P1-2**: both codes in `undetermined`
have reachable sub-cases where exactly one row-checked certificate exists.

### C9. Known-open items — **both still open, one disclosed only in the commit trail**

* Opus P40 P2-4: `THV1-20260902-global-settlement-v1-canonical-exact-admission-v10` and
  `THV1-20260901-claimant-backing-guard-golden-v29` are each referenced by nothing but their own file
  (`grep -rl` over the repo). **Still open**, stated as not addressed.
* opus2 P40 P2-7: **still open and still live.** Reproduced: take `_witnessed(with_rows=True)`, add one
  atom to the single custody row and the matching liability, keep the lane and binding roots —

  ```
  projection DERIVED a certificate
    with the minted witness -> RECEIPT_WITNESS_FRAGMENT_DRIFT
    with empty witness slots -> RECEIPT_WITNESS_REQUIRED
  ```

  The commit message says it is not addressed. The **artifact** does not: module claim 2
  (`src/core/…_projection_v1.py:36-47`) states "Where NO certificate over the state can be accepted, the
  projection refuses rather than deriving an object the checker must reject" with two "includes" and no
  exception, and no THV1 nonclaim carries one. See **P2-4**.

### C10. The P3s from both P40 reviews

| P40 finding | status here |
|---|---|
| Opus P3-1 (two-kind split omits 3 of 13 codes) | **closed in the module**, still open in the packet (part of P1-1) |
| Opus P3-2 (append the module's exception to nonclaim 5) | **closed** — nonclaim 5 now carries the two lane-configuration codes |
| Opus P3-3 ("the two branches are disjoint" is about states) | **closed** — the word is gone; the claim is now "a partition of all sixteen codes" |
| Opus P3-4 (`_derive_rows` reads `lane_roots[0]`) | **open**, undisclosed — `tests/core/…_projection_v1.py:106` unchanged (P3-3) |
| opus2 P3-1 (taxonomy omits three codes) | as Opus P3-1 |
| opus2 P3-2 (check order omits the producer-capability gate) | **open** — the docstring gained "(1b)" for the state-level gates; `PROJECTION_ROWS_BEYOND_PRODUCER`, which runs between (2) and (3), is still absent (P3-4) |
| opus2 P3-3 (2 of 6 ledger-gated packets not in `hygiene_selection`) | **open**, undisclosed — still `certificate-v23` and `lineage-ordering-v5` (P3-2) |
| opus2 P3-4 ("the generator now stamps…" names no tool) | **repeated, not fixed** — "the generator now drops a repeat before writing" (P3-5) |
| opus2 P3-5 (v22 `claim_scope` repeats a sentence) | **worse** — v23 has three verbatim-repeated sentences (P3-6) |
| opus2 P3-6 (`test_reject_codes_are_closed_and_ordered` scans the file) | **open**, unchanged |

Two of the ten were answered in prose rather than in code (Opus P3-3, and the packet half of P3-1);
three are simply still open and two of those three are not listed as not-addressed.

### C11. The packet — **CLOSED**

58 pin roles, 38 replay commands, authority NONE, `formal_core_complete false`, the four required
nonclaims present and correct. The one packet-level defect is the text of nonclaim 5 (P1-1).

---

## 3. Findings

### P1-1 — The artifact under review still asserts, in three pinned places, the sentence both P40 reviews' P1 falsified

P41's whole diff is the two packet files, and the packet still says it.

**(a) `tools/o008_formal_cycle_admission_v1.py:559,561` → O-008 packet nonclaim 5** (rendered into
`docs/research/ZENODEX_O008_FORMAL_CYCLE_V1.{json,md}`, the artifact):

> "**Two kinds** of refusal share that family … **UNDETERMINED means more than one acceptable
> certificate exists** (a domainless terminal with two entitlement domains, two principals controlling a
> cell, several ways to split a residual across pending obligations); UNRECONCILABLE means none exists
> (entitlements exceeding custody, unassignable controlled atoms, an obligation with no controlled
> location, an over-claiming terminal, a claimant with no entitlement, a fold that would overflow, rows
> with no enabled lane, more than one enabled lane, an enabled lane whose registry entry has no
> producer, and a registered-empty lane committed at a foreign root)."

Three defects in one paragraph, all of them the subject of a P40 finding: "Two kinds" where the module
now says **three**; "more than one **acceptable** certificate" — the exact wording of opus2 P40 P1-1,
which the commit message says was replaced in six places; and an UNRECONCILABLE enumeration of ten that
omits `PROJECTION_ROWS_BEYOND_PRODUCER` (both reviews' P3-1, the headline guard of the previous
candidate) and `PROJECTION_TERMINAL_WITHOUT_BACKING` (this candidate's own new code).

This is not an oversight of an untouched string. **The author edited this exact nonclaim in this
commit** — `git diff 4b42d63c3 d2195c5e8` on the packet shows nonclaim 5 changed, extending the
UNRECONCILABLE list with the two lane-configuration codes — and left the falsified sentence and the
stale "Two kinds" standing two clauses earlier.

**(b) `tests/evidence/test_hygiene/THV1-20260903-global-accounting-allocation-projection-v4.json:509`,
nonclaim 7:**

> "…so a cell controlled by two principals admits **two accepted certificates** over one state with
> different allocation roots. The projection refuses such a state rather than choosing; **the checker
> would take either**."

Both halves are false, and the second is refuted by the test the same commit adds: the full checker
refuses both certificates with `RECEIPT_WITNESS_REQUIRED`
(`tests/core/…_projection_v1.py:858`, and I reproduced it).

**(c) same file:510, nonclaim 8:**

> "Under the current registry the reserve, external and terminal derivation **is unreachable through the
> public entry point**…"

That is Opus P40 P1-2's sentence, and the candidate's own new test
`test_which_row_cases_the_entry_point_reaches_is_pinned` pins two cases that reach the external
derivation through the entry point.

**Reproduction.**

```bash
cd /tmp/zenodex-formal-core-opus2-c9c4
"$PY" - <<'EOF'
import json, subprocess
def nc(rev): return json.loads(subprocess.run(["git","show",f"{rev}:docs/research/ZENODEX_O008_FORMAL_CYCLE_V1.json"],capture_output=True,text=True).stdout)["nonclaims"]
print("nonclaim 5 changed P40->P41:", nc("4b42d63c3")[4] != nc("d2195c5e8")[4])
print("still says:", "UNDETERMINED means more than one acceptable certificate exists" in nc("d2195c5e8")[4])
p = json.load(open("tests/evidence/test_hygiene/THV1-20260903-global-accounting-allocation-projection-v4.json"))
old = json.loads(subprocess.run(["git","show","f111ec292^:tests/evidence/test_hygiene/THV1-20260903-global-accounting-allocation-projection-v3.json"],capture_output=True,text=True).stdout)
print("all ten THV1 nonclaims byte-identical to v3:", p["nonclaims"] == old["nonclaims"])
EOF
#   nonclaim 5 changed P40->P41: True
#   still says: True
#   all ten THV1 nonclaims byte-identical to v3: True
```

**Why P1.** The candidate exists to repair two P1s about written claims the code falsifies. It repaired
them in the module, the test file and the `claim_scope`, and left them in the two places that are
*pinned by sha256 as evidence* — one of them the top-level packet that **is** artifact P41, edited in
the same commit. The projection packet's own `claim_scope` says "Six places now say 'passes every row,
partition and aggregate check'"; its nonclaim 7, in the same file, is a seventh that does not.

**Minimal fix.** In `NONCLAIMS_V1` nonclaim 5: "Two kinds" → "Three kinds"; "more than one acceptable
certificate exists" → "more than one certificate that passes every row, partition and aggregate check
exists"; add `..._ROWS_BEYOND_PRODUCER` and `..._TERMINAL_WITHOUT_BACKING` to the UNRECONCILABLE
enumeration. In the THV1 packet: nonclaim 7 → "two certificates that pass every row, partition and
aggregate check … the checker refuses both, for the structural reason"; nonclaim 8 → the sentence the
candidate's own test pins ("unreachable for the ten cases that need a reserve, a PENDING entry or an
OPEN terminal; reachable for the two that need none"). Re-cut both packets.

### P1-2 — The replacement definition of UNDETERMINED is false for reachable sub-cases of **both** its codes

`src/core/global_accounting_allocation_projection_v1.py:113-117` (enum docstring) and `:169-172`
(the `undetermined` tuple of `ALLOCATION_PROJECTION_REFUSAL_KINDS_V1`, whose comment at `:160-163`
says "Membership is a claim about WHY a code is raised"):

> "UNDETERMINED — V1 state leaves **more than one** certificate open that passes every row, partition
> and aggregate check, so deriving one would be a guess: `..._EXTERNAL_RESIDUAL_AMBIGUOUS`,
> `..._TERMINAL_DOMAIN_AMBIGUOUS`."

Repeated at `tests/core/…_projection_v1.py:13-15`.

**Counterexample A — `..._EXTERNAL_RESIDUAL_AMBIGUOUS` over a state with exactly one such certificate.**
One PENDING outbox entry and custody fully assigned, so there are zero open residual cells:

```bash
"$PY" - <<'EOF'
import sys; sys.path.insert(0, ".")
from dataclasses import replace
from src.core import global_accounting_allocation_certificate_v1 as cert
import tests.core.test_global_accounting_allocation_projection_v1 as T
state = T._backed_state((), custody=(("pool-a","USD","spot-pool",10),),
    liabilities=(("alice","USD","spot-pool",10),),
    outbox=((T.renderer._root(9_001),"dest-1",T.renderer._root(9_002),T.renderer._root(9_003),"PENDING"),))
print("row harness ->", T._derive_rows(state)[0].value)
EOF
#   -> PROJECTION_EXTERNAL_RESIDUAL_AMBIGUOUS      detail "1 pending rows for 0 residual cells"
```

The pending row's `amount_atoms` is forced to 0 by `_check_lane_aggregates` (custody 10 = entitlements
10 + reserves 0 + pending), and `_require_atoms_u128`
(`src/core/global_settlement_types_v1.py:71-76`) admits 0. Its `effect_id`, `destination_id` and
`commitment_root` come from the outbox entry; its `asset`, `control_domain` and `source_principal` are
forced by `_check_external_obligations` to bind to a controlled location, and there is exactly one.
So the certificate is fully determined. I built both candidates:

```
no pending row       : rows=[exactly_once PASS, entitlement PASS, external EXTERNAL_OBLIGATION_BINDING_DRIFT, terminal PASS, aggregates PASS]
zero-atom pending row: rows=[exactly_once PASS, entitlement PASS, external PASS, terminal PASS, aggregates PASS]  root 0x5399614b7ff5
```

Exactly one certificate passes every row, partition and aggregate check. The state determines the
answer; the projection reports UNDETERMINED.

**Counterexample B — `..._TERMINAL_DOMAIN_AMBIGUOUS` likewise.** A claimant entitled in two domains where
only one can host the row:

```bash
state = T._backed_state((T._terminal("terminal-1", 5),),
    custody=(("pool-a","USD","spot-pool",10),("pool-b","USD","vault",1)),
    liabilities=(("alice","USD","spot-pool",10),("alice","USD","vault",1)))
#   row harness -> PROJECTION_TERMINAL_DOMAIN_AMBIGUOUS   "terminal-1: 2 entitlement domains"
#   terminal row in spot-pool -> all six checks PASS   root 0x23bc573ba138
#   terminal row in vault     -> terminal TERMINAL_BINDING_DRIFT, term_totals TERMINAL_BINDING_DRIFT
```

`vault` cannot host it (`entitled` 1 < 5), so again exactly one certificate passes. Both counterexamples
run through `_derive_rows`, the same harness the suite uses for ten of its twelve row cases.

**Why P1.** This is the third wording of the candidate's headline claim and the third falsifiable one:
P39 said the certificate is a function of the state; P40 said UNDETERMINED means two ACCEPTED
certificates; C9c-4 says it means more than one row-checked certificate, and a twenty-line probe
refutes that for both codes it names. The new test pins the kinds as *exhaustive and disjoint* and never
tests *membership*, which is the property the docstring asserts — so the repair's own gate cannot see
this. The claim is carried in the enum docstring, a module-level constant, the test module header, and
(in its older form) the two pinned packets of P1-1.

**Minimal fix.** State what is true of the codes: *"the state does not determine the row content, so the
projection refuses rather than choosing. It does not follow that more than one row-checked certificate
exists: `..._EXTERNAL_RESIDUAL_AMBIGUOUS` also fires when there are fewer open residual cells than
PENDING entries, and `..._TERMINAL_DOMAIN_AMBIGUOUS` when only one of the candidate domains can carry
the amount — in both, exactly one certificate passes the row checks and the projection is incomplete
rather than the state undetermined."* Then add the two states above as `_ROW_CASES` entries so the
sentence has a test. (Making the projection actually derive them is a larger change and not required to
make the claim true.)

### P2-1 — The one place the candidate points to for its stated scope limit gives a reason that is false, and the false reason contradicts the same commit's headline repair

`tests/core/test_global_accounting_allocation_projection_v1.py:125-128`, the docstring of
`_state_consistent_candidate`:

> "WHAT THIS DOES NOT COVER … **it builds no terminal binding rows**, so for a state with an OPEN
> terminal obligation it is one candidate among more than one…"

The function builds terminal binding rows: `:152-190` loops `state.terminal_obligations`, constructs a
`cert.TerminalBindingRowV1` for every OPEN one, and installs them. The commit message and the THV1
`claim_scope` both say so — *"it builds the terminal rows and runs the terminal checks it used to
omit"*. The same false reason is repeated at `:810-811` ("the builder omits terminal rows, so other
candidates exist").

The limitation itself is real; the reason is not. The true reason is at `:154-181`: for an OPEN terminal
the builder picks `domains[0]`, `principals[0]`, or a `fallback`/`"unbound"` placeholder — an arbitrary
choice from a set that may have more than one member — so it is one candidate among several.

The brief asks whether that limit is carried everywhere the claim appears. It is carried in three places
(this docstring, the parametrised test's docstring, the THV1 `claim_scope`) and **omitted** from two:
the enum docstring's "For each row case in the UNRECONCILABLE kind a test BUILDS the certificate the
state implies and shows the checker refusing it" (`src/core/…_projection_v1.py:128-131`) and the test
module header (`tests/core/…_projection_v1.py:19-21`). And in two of the three where it appears, the
reason given is wrong.

**Reproduction.** `sed -n '125,190p' tests/core/test_global_accounting_allocation_projection_v1.py` —
the docstring and the `terminal_rows` loop are eleven lines apart.

**Minimal fix.** Replace "it builds no terminal binding rows" with "for a state with an OPEN terminal it
chooses one control domain and one controlling principal from a set the state may leave open, so it is
one candidate among several" in both places, and add the same sentence to the enum docstring and the
test module header.

### P2-2 — The new `<crate>/src/<file>.rs::<filter>` killer form binds neither the declared file nor a named test

`tools/thv1_mutation_ledger_v1.py:174-180` and `:187-190`; `tools/test_hygiene_evidence_v1.py:297-320`.

For the `--test` form the declared path determines the cargo target, so the run is scoped to the named
integration file. For the new `--lib` form the path is used **only** for `crate_dir`
(`:149-153`) and the pin-drift check; selection is `cargo test --lib -- <filter>`, a substring match
across every unit test in the crate. `_validate_killer` checks only that the path is a pinned `.rs`
under `/src/` or `/tests/` and that the filter is non-empty and whitespace-free — it never resolves the
filter to a test, unlike the pytest form, whose node ids all resolve to a real `def` (707/707 verified
above).

**Reproduction.** All four of these are accepted, and three produce a run identical to or a superset of
the declared one:

```bash
"$PY" - <<'EOF'
import sys, json; sys.path.insert(0, ".")
from tools.thv1_mutation_ledger_v1 import parse_killer_v1, cargo_argv_v1
from tools import test_hygiene_evidence_v1 as thv
pkt = json.load(open("tests/evidence/test_hygiene/THV1-20260901-global-accounting-allocation-certificate-v23.json"))
rust = frozenset(p["path"] for p in pkt["source_pins"] if p["path"].endswith(".rs"))
for kb in ["zk/global_settlement_abi_v1/src/lib.rs::global_accounting_allocation_certificate::tests::the_source_principal_guard_refuses_and_the_check_is_what_refuses",
           "zk/global_settlement_abi_v1/src/asset_transfer_lane_module.rs::tests::"]:
    thv._validate_killer(kb, packet_context="c", pinned_nodes=frozenset(), rust_test_paths=rust, legacy=False)
    print("ACCEPTED |", " ".join(cargo_argv_v1(parse_killer_v1(kb))))
EOF
#   ACCEPTED | cargo test --offline --locked --lib -- global_accounting_allocation_certificate::tests::the_source_principal…
#   ACCEPTED | cargo test --offline --locked --lib -- tests::
```

and the second qualifies:

```
control  (unmutated): cargo test --lib -- tests::   ->  test result: ok. 16 passed
mutant   (guard deleted): same command             ->  test result: FAILED. 15 passed; 1 failed   -> KILLED
```

So a row may declare `zk/global_settlement_abi_v1/src/asset_transfer_lane_module.rs::tests::` — a file
containing neither the guard nor the test, and a filter naming no test — and be graded a mechanical kill
for the source-principal guard.

**To the brief's exact question:** no, a filter cannot qualify a mutant it does not exercise.
`control_error_v1` (`:220-239`) requires ≥1 green selected test and `mutant_verdict_v1` (`:254-263`)
requires a cargo summary with `failed > 0`, so some selected test must fail under the mutant; a
compile-breaking mutant yields `UNVIABLE`, not `KILLED`. The defect is **attribution**, not soundness:
the form certifies "some unit test in this crate matching this substring notices this mutation", while
the row and the packet read as "this named test in this file kills it".

**Minimal fix.** In `_validate_killer`, for a `/src/` path require the filter to appear in that file's
text (`filter.rsplit("::", 1)[-1]` as a `fn` name), and in `_execute_mechanical_row` require the killer's
control run to select exactly one cargo test (`sum(passed) == 1`).

### P2-3 — "It cannot be reached … through the row harness" is false for `PROJECTION_TERMINAL_WITHOUT_BACKING`

`tests/core/test_global_accounting_allocation_projection_v1.py:467-470`:

> "The branch is DEFENSIVE: it cannot be reached through the entry point **or through the row harness**,
> because a state entitling a claimant in a domain it controls nowhere fails the negative-residual check
> first, and that check runs before the terminal rows."

The negative-residual check fires only for a **positive** entitlement in an uncontrolled domain. A
zero-amount entitlement row is constructible, and then the residual is zero, `_external_rows_v1` returns
`()`, and `_terminal_rows_v1` reaches the branch:

```bash
"$PY" - <<'EOF'
import sys, dataclasses; sys.path.insert(0, ".")
import tests.core.test_global_accounting_allocation_projection_v1 as T
from src.core import global_accounting_allocation_projection_v1 as proj
st = T._one_enabled_state(custody=[("pool-a","USD","vault",10)],
                          liabilities=[("alice","USD","spot-pool",0)],
                          reserves=[("pool-a","USD","vault",10)])
st = dataclasses.replace(st, terminal_obligations=(T._terminal("terminal-1", 5),))
print("row harness ->", T._derive_rows(st))
print("entry point ->", proj.project_allocation_certificate_v1(st, T._root_of(st)).code.value)
EOF
#   row harness -> (PROJECTION_TERMINAL_WITHOUT_BACKING, 'terminal-1: no controlled location in spot-pool')
#   entry point -> PROJECTION_ROWS_BEYOND_PRODUCER
```

The entry-point half of the claim holds. The row-harness half does not, and the claim is the stated
justification for testing the branch by a direct call instead of adding a `_ROW_CASES` entry — which,
given this state, was available. This is the same shape as the P1-2 the candidate repairs: a written
unreachability claim refuted by a short probe, one candidate later, inside the repair for it. It is P2
rather than P1 because it lives in a test docstring, not in a pinned nonclaim, and the code is correct.

**Minimal fix.** Add the state above as a `_ROW_CASES` entry for
`PROJECTION_TERMINAL_WITHOUT_BACKING`, and restate the docstring as "unreachable through the public
entry point, and reachable in the row harness only with a zero-amount entitlement row".

### P2-4 — Module claim 2 is universal and the witnessed-lane row-*content* exception is nowhere in the artifact

`src/core/global_accounting_allocation_projection_v1.py:36-47`. The claim — "Where NO certificate over
the state can be accepted, the projection refuses rather than deriving an object the checker must
reject" — is followed by two "That includes…" clauses and no exception. opus2 P40 P2-7 showed a third
case, and it is still live (reproduced in §C9). The commit message says it is not addressed; the module
and all ten THV1 nonclaims say nothing, and `grep -rn "row contents"` over both returns nothing.

Disclosure in a commit message is not disclosure in the artifact: P41 is the packet, and the packet is
what a later reader is pinned to.

**Minimal fix.** Add to claim 2 and to the THV1 nonclaims: *"a witnessed lane's controlled and
entitlement rows must also equal the ones the committed lane root's receipt admitted; the projection
cannot check that and will derive a certificate the witness check refuses."*

### P2-5 — Three of the six `REPLAY_LEDGER_*` codes still have no test

`tools/o008_formal_cycle_admission_v1.py:4112`, `:4123` and `:4126` against
`tests/test_check_o008_formal_cycle_v1.py`. The five new parametrised cases cover
`REPLAY_LEDGER_ROW_PATH_UNPORTABLE`, `REPLAY_LEDGER_ROW_NOT_DISTINCT` and
`REPLAY_LEDGER_ROW_WITHOUT_MUTATION`. `REPLAY_LEDGER_ROW_NOT_KILLED`,
`REPLAY_LEDGER_KILLED_COUNT_DRIFT` and `REPLAY_LEDGER_REPORT_UNPARSEABLE` are asserted nowhere:

```bash
grep -rn "REPLAY_LEDGER_ROW_NOT_KILLED\|REPLAY_LEDGER_KILLED_COUNT_DRIFT\|REPLAY_LEDGER_REPORT_UNPARSEABLE" tests/
#   (no output)
```

opus2 P40 P2-8 asked for three rows and named `survived: 1` → `REPLAY_LEDGER_ROW_NOT_KILLED`
explicitly; that one is the one that did not land. **Minimal fix:** three more `pytest.param` lines on
the existing table (`survived: 1`; `killed` off by one; stdout that is not JSON).

### P3-1 — The ledger test helper's docstring claims a guard the grader deliberately does not have

`tests/test_check_o008_formal_cycle_v1.py:1063-1070`: "The mutation path must be one the formal-cycle
packet pins, because the grader now refuses a mutation applied to a file this packet does not bind
(Opus P40 P2-1)." The grader checks portability only; the pinning version was tried and withdrawn, as
`_grade_ledger`'s own docstring and the commit message both say. Verified:

```bash
"$PY" -c "import sys;sys.path.insert(0,'.');from tools.o008_formal_cycle_admission_v1 import _portable_repo_path_v1 as f;print(f('src/core/x.py'))"
#   True
```
and `_grade_ledger` accepts a full report whose every row names the unpinned, non-existent
`src/core/x.py`. **Fix:** say "must be a portable repository-relative path".

### P3-2 — opus2 P40 P3-3 still open: 2 of the 6 ledger-gated packets are not pinned by the packet that claims the gate

`THV1-20260901-global-accounting-allocation-certificate-v23` and
`THV1-20260902-test-hygiene-lineage-ordering-v5` are in `LEDGER_GATED_PACKETS_V1` and not among the
seven in `hygiene_selection`. The version numbers moved; the gap did not. Not listed as not-addressed.
**Fix:** add both to `hygiene_selection`.

### P3-3 — Opus P40 P3-4 still open: the row harness selects `lane_roots[0]`, the entry point selects the enabled lane

`tests/core/test_global_accounting_allocation_projection_v1.py:106` unchanged against
`src/core/…_projection_v1.py:591-593`. Not listed as not-addressed. **Fix:** select the enabled lane.

### P3-4 — opus2 P40 P3-2 still open: the documented check order omits the producer-capability gate

`src/core/global_accounting_allocation_projection_v1.py:508-518` now lists (0), (1), **(1b)**, (2), (3),
(4). The `PROJECTION_ROWS_BEYOND_PRODUCER` gate, which runs between (2) and (3) and is the code ten of
the twelve row cases receive, is still absent. **Fix:** insert it as (2b).

### P3-5 — "the generator now drops a repeat before writing" names no code in the tree

The commit attributes the deduplication to a generator change. S41 touches no packet generator: its
fifteen files are the projection module, three test files, five THV1 packets, three tools and two Rust
files. The `seen` set added in `_grade_ledger` **refuses** a repeat at grading time; nothing **drops**
one at authoring time, and `grep -rn "dedup" tools/*.py` finds only unrelated hits. This is the same
shape as opus2 P40 P3-4 ("the generator now stamps every packet it writes"), reported and repeated.
The outcome is verified correct (§1), so only the mechanism claim is wrong. **Fix:** say the packets
were deduplicated by hand and the grader now refuses a repeat.

### P3-6 — opus2 P40 P3-5 is worse: the v23 `claim_scope` now repeats three sentences verbatim

`THV1-20260901-global-accounting-allocation-certificate-v23.json` `claim_scope` contains "Earlier: v20
re-pin (C9c-1): …", "Earlier: Candidate C8''' (Opus P19 repairs): …" and "The asset-lane projection
joins the pinned surface" twice each (one repeat at v22). The prepend-and-carry construction is still
un-deduplicated. **Fix:** de-duplicate on carry.

---

## 4. INFO

**INFO-1 — Review-brief drift.** The brief says the NO_PRODUCER falsification "should be closed by
C9c-3's state-level gate". `_state_level_refusals_v1` is added by **C9c-4** (`git show f111ec292` on
`src/core/global_accounting_allocation_projection_v1.py`); C9c-3 had no such gate, which is why the
probe worked at P40. The conclusion is unchanged — it is closed — but by this candidate.

**INFO-2 — A wrong result I discarded.** My first Rust deletion test ran in a bare copy of
`zk/global_settlement_abi_v1`, where `fixture_value()` cannot resolve
`$CARGO_MANIFEST_DIR/../../tests/data/…`. Both the new unit test and the unrelated
`fold_overflow_details_match_the_shared_labels` failed for that reason and not for the mutation's. The
result in §C5 is from a corrected layout with a green baseline. Recording it because a reviewer reading
only the first run would have credited the guard with a kill it had not earned.

**INFO-3 — Shared ledger staging directory (my environment, not the candidate's).** I did not set
`TMPDIR`, so `_default_workdir()` (`tools/thv1_mutation_ledger_v1.py:424-425`) resolved to the shared
`/tmp/thv1-ledger`, which the other reviewer's replay of the same packet names also uses, and
`run_ledger_v1` (`:523-524`) `rmtree`s an existing `packet_dir` before staging. Concurrent runs would
therefore have collided. They could not: every Lean-bearing command on both sides ran under
`flock -w 7200 /tmp/zenodex-lean.lock`, my `--replay` waited about fifty minutes for the lock (I observed
the other session holding it: `fuser` showed its `flock` and `python`, with a live `lean`) and then held
it for its whole run. A collision would also have surfaced as `PIN_DRIFT`, `NEEDLE_COUNT` or a missing
file, i.e. `survived`/`errors` > 0 and `EXECUTED_FAIL`; the run returned 97 killed, 0 survived, 0 errors.
Independently, I re-executed all 43 declared pytest mutation rows in my own extract and the Rust row in
my own crate copy, outside any shared staging, and they match the replay exactly, as does the builder's
separate 38-command replay. No result here depends on the shared directory. Future reviewers should
still set `TMPDIR` per the campaign guidance.

**INFO-4 — Carried, unchanged.** The row derivation still runs outside the refusal boundary
(`src/core/…_projection_v1.py:612-621`, after the `except _Reject` at `:610`), recorded at P38, P39 and P40. Unreachable today; the module
docstring's "Every refusal is a value carrying the unchanged state root" still has no exception attached.

---

## 5. Worktree hygiene

`/tmp/zenodex-formal-core-opus2-c9c4` is at `d2195c5e872bd89c098fa9b5abd5ff3db9820674` with
`git status --short` empty at the end of the review. Nothing was committed to any branch. All mutation
testing ran in `/tmp/opus2c9c4-mut` (a `git archive` extract of `src/ tests/ tools/`) and
`/tmp/opus2c9c4-proberepo` (a copy of the crate plus `tests/data` and `tests/fixtures`); both were
deleted, as were the cargo target directories. No other worktree was read or written.

---

## 6. Bottom line

**REVISE (advisory). Grade B−.** Authority stays NONE, `formal_core_complete` stays false, the claim
ceiling did not move, and nothing consumes the projection.

More landed here than in either predecessor, and I verified each piece by execution rather than by
reading: the evidence standard is genuinely called and the falsification now fails the suite; the Rust
guard's deletion now breaks the crate where 535 tests once stayed green; every one of the 24 projection
mutations, 18 ledger mutations and 1 lineage mutation kills; the deduplication removed repeats and
nothing else; the two state-level gates close the NO_PRODUCER falsification; all 58 packet pins, 87 THV1
pins and 707 node ids are byte-exact; the full 38-command replay is `EXECUTED_PASS`.

It is B− because the campaign's named failure mode is present in the artifact under review rather than
around it. P41's entire diff is the packet, and the packet's nonclaim 5 — edited in this very commit —
still says "Two kinds" and "UNDETERMINED means more than one acceptable certificate exists", and the
pinned THV1 nonclaims are byte-identical to the ones both P40 P1s falsified. The replacement definition
that the module *does* carry is itself refuted by a twenty-line probe for both codes it names, and the
new test that pins the kinds checks exhaustiveness and disjointness but never membership — the one
property the docstring asserts. The pattern to break is not "fix the code": the code was fixed. It is
"re-cut every text that carries the claim, and give the claim a test that could fail."
