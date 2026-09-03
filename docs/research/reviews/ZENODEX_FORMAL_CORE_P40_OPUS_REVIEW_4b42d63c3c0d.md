# ZenoDEX Formal Functional Core Closure — C9c-3 (P40) independent review

| field | value |
|---|---|
| subject | S40 `42c2e40704181dc45d219634758d8b1fdd129fbf` — "fix: say which of the two things is true when the projection refuses" |
| artifact | P40 `4b42d63c3c0de6b93bc0644817e1ab82d05c3b2f` (artifact-only child; `docs/research/ZENODEX_O008_FORMAL_CYCLE_V1.{json,md}`) |
| packet json sha256 | `59073e535075aadcb745ffaa0b781c6ac8a06add020b7f13014d69f39cc2eafc` (matches the expected value) |
| worktree | `/tmp/zenodex-formal-core-opus-c9c3` (detached at P40; `git status --short` empty at start and at end) |
| reviewer | independent Opus 5 session, fresh context |
| date | 2026-09-03 |
| verdict | **B−** — 2 P1, 4 P2, 4 P3. ACCEPT is **not** advised without the P1 repairs. Authority stays NONE; the claim ceiling did not move. |

---

## 1. Replays

Every Lean-bearing command ran under `flock -w 7200 /tmp/zenodex-lean.lock`. Environment:
`PY=/home/trevormoc/Downloads/Autonomous Tau DEX/.venv/bin/python`, `PYTHONDONTWRITEBYTECODE=1`,
`CARGO_TARGET_DIR=/tmp/zenodex-opus-c9c3-cargo`, `CARGO_INCREMENTAL=0`.

| command | result |
|---|---|
| `check_o008_formal_cycle_v1.py --root $PWD --packet-commit 4b42d63c3` | exit 0; `ok true`, `packet_admitted true`, `current_source_drift []`, `proof_replay NOT_RUN`. Result sha256 `16b916573afa0a480ca353eead8590a35570628313625c752a064ef3e6fce294` |
| same `--replay --esso-python /usr/bin/python3 --esso-pythonpath …/ESSO` | exit 0; **`EXECUTED_PASS`, 38 runs**, `ok true`, `errors []`, `current_source_drift []`. Result sha256 `0cbf9f6deba3708eed2e84ff8c31af4b9c5a54463b5ed99c852cf0acbfb4256c` |
| — the six ledger runs inside it | `ledger_projection_rows` 20, `ledger_tool_rows` 22, `ledger_admission_rows` 31, `ledger_ownership_rows` 21, `ledger_certificate_rows` 1, `ledger_lineage_rows` 2 = **97 killed, 0 survived, 0 errors**, each exit 0 — exactly the declared figures |
| `build_o008_formal_cycle_v1.py … --check --replay --output-json/-md` | exit 0; `ok true`, **`drift []`**; `git status --short` empty after; the packet regenerates to the identical `59073e53…` |
| `cargo fmt --all -- --check` (`zk/global_settlement_abi_v1`) | exit 0 |
| `cargo clippy --locked --all-targets -- -D warnings` | exit 0 |
| `cargo test --locked` | exit 0; 54 `test result: ok` summaries, **535 passed**, 0 failed — matches the declared figure exactly |
| `tests/core/test_global_accounting_allocation_projection_v1.py` | **53 passed** (declared 53) |
| `tests/formal/test_lean_asset_transfer_refinement_v1.py` (under the lock) | exit 0; **40 passed** (declared 40) |
| `tests/core/test_transition_resource_bound_totality_v1.py` | 10 passed |
| `tests/core/test_global_settlement_abi_v1_resource_bounds.py` | 17 passed |
| `tests/core/test_global_settlement_abi_v1.py` | 75 passed |
| `tests/test_check_o008_formal_cycle_v1.py` | 392 passed (238 s) |
| `tests/test_check_global_settlement_canonical_manifest_v1.py` | 8 passed |
| `check_test_hygiene_v1.py --json` | exit 0; `ok true`, `evidence_packet_count 226`, `changed_path_count 0` |
| `--base-ref 2928191bb --json` (parent of S40) | exit 0; `ok true`, 226 packets, 18 changed / 5 critical |
| `--base-ref fd409ba6f7d… --json` (campaign base) | exit 0; `ok true`, 226 packets, 407 changed / 68 critical — **the campaign base is green** |

`tests/core/test_zusd_liquidation_partition.py` excluded as instructed (pre-existing unrelated collection error).

**Setup note (mine, not the candidate's).** My first `--replay` returned `EXECUTED_FAIL` with eight
`REPLAY_EXIT_CODE` errors on the Lean commands, starting with `lean_version`. The cause was my own
worktree preparation: the symlink list in the review prompt omits `mathlib` itself, and
`lean-mathlib/lakefile.lean:7` does `require mathlib from "../external/mathlib4"`. After adding
`lean-mathlib/.lake/packages/mathlib -> /home/trevormoc/deps/mathlib4` and
`external/mathlib4 -> /home/trevormoc/deps/mathlib4` the Lean commands resolve. **This is an artifact of
the review environment, not a defect in the candidate**, and it is recorded here only so the failed first
run is not mistaken for evidence against P40.

A second environment artifact: my first `build_… --check --replay` was SIGTERM'd (exit 143) at exactly
20 minutes by the review harness, not by the tool. Re-run fully detached it completed in 10 minutes with
`ok true` and `drift []`. Neither of these two incidents is a finding against the candidate.

### Pin audit

* O-008 packet: **58** `source_pins`, all byte-exact on `sha256`, `git_blob` (`git hash-object`) **and**
  `size`; 0 mismatches. **38** replay commands as declared. `hygiene_selection`: 55 rows, every
  `packet_sha256` and `pin_sha256` byte-exact, 0 mismatches.
* The ten named THV1 packets: **135** `source_pins` + `test_pins`, 0 bad; **812** pinned pytest node ids,
  **0 orphans** (every one resolves to a real `def` in the pinned file).
* `subject_tree` `003c129592ad03b976008279209601c0e1d2b6ab` equals `git rev-parse 42c2e4070^{tree}` — the
  packet is bound to the exact S40 tree. `subject_parent` = `2928191bb`, `packet_commit_parent` =
  `42c2e4070`, both correct.
* Claim ceiling: `migration/production/publication/release/settlement/value_movement/verifier_authority`
  all `NONE`; `formal_core_complete false`; `o008_status OPEN_EXACT_ALL_12_RECONCILIATION_MISSING`;
  `value_movement_gates_closed 0 / 12`. **The ceiling did not move.**
* Required nonclaims are present, in the THV1 projection packet rather than the O-008 packet (whose
  nonclaim 5 explicitly defers: "the THV1 projection packet carries the current list"): no Rust twin
  (nonclaim 6), fixture partition is not a general property (9), a refusal does not say the state is
  invalid (10), nothing consumes it (2). Verified — not a finding.

---

## 2. One verdict per claim

### C1. The false claim is withdrawn — **CLOSED**

`src/core/global_accounting_allocation_projection_v1.py:17-27` no longer says the certificate is a
function of the state. It now says the checker binds a pending row's source principal and a terminal
row's controlling principal to *some* controlled location, "so a cell controlled by two principals still
admits two accepted certificates with different allocation roots. The projection refuses such a state;
the checker would take either."

I tried to falsify the new wording by building the second admitting certificate, as instructed. State:
custody `(pool-a, USD, spot-pool, 6)` and `(pool-b, USD, spot-pool, 4)`, no liabilities, one PENDING
outbox entry. Two certificates differing only in `source_principal`:

```
source_principal=pool-a: exactly_once:PASS external:PASS reserves:PASS aggregates:PASS
  allocation_root=0x611cd6ed0b43c02af68ae0f8…
source_principal=pool-b: exactly_once:PASS external:PASS reserves:PASS aggregates:PASS
  allocation_root=0xb4fecce221699c583fdf5555…
```

Two distinct allocation roots, both passing every row and aggregate check. That is exactly what the new
docstring predicts, so the new wording **survives** the attack that killed the old one. (The full checker
returns `RECEIPT_WITNESS_REQUIRED` for both, because the enabled lane is receipt-backed and no witness is
supplied; the docstring's claim is about the binding, and it is stated at that level.) Nothing else in the
docstring is falsified by a second admitting certificate.

### C2. A refusal says which of two disjoint things is true — **PARTIAL**

What holds: the family is **closed** — 17 `_fail` sites use exactly the 13 declared codes, and
`ALLOCATION_PROJECTION_REJECT_CODES_V1` is derived from the enum, so a code cannot be raised outside it.
The `PROJECTION_NEGATIVE_RESIDUAL` reordering is real and is the substantive repair of P39 P1-1: the
residual is classified at line 247, before the pending count is consulted at 255, so `custody 3 /
liabilities 5 / empty outbox` now returns `PROJECTION_NEGATIVE_RESIDUAL` **through the entry point**
(previously unreachable without an outbox entry). Both declared mutants for these two guards kill when
applied by hand (see §4).

What does not hold: the reachability claim attached to the taxonomy is false (**P1-2**); the headline
branch has no declared mutation row (**P2-2**); a zero-candidate terminal binding is still reported with
an UNDETERMINED code (**P2-3**); the two branches are not disjoint as predicates over states (**P3-3**);
and the enum docstring's own two-kind split enumerates only 10 of the 13 codes (**P3-1**).

### C3. Unreconcilability is proved through the checker, not asserted — **NOT CLOSED**

`_no_certificate_reconciles` is **dead code**. It is never called (**P1-1**). Every UNRECONCILABLE case in
`_ROW_CASES` asserts only `observed is code` — the projection's own classification, i.e. precisely the
"author's say-so" standard the candidate says it replaced.

### C4. The row-builder harness does not pretend to be the entry point — **CLOSED** (with C2's caveat)

`_derive_rows` (`tests/…/test_global_accounting_allocation_projection_v1.py:66-78`) does say plainly that
it calls the helpers directly, and I found **no** place where a result obtained through that harness is
stated as a property of `project_allocation_certificate_v1`. THV1 nonclaim 8 and the packet `claim_scope`
both scope those paths as "the contract a future producer would have to meet, not behaviour any registered
lane exhibits today". The claim this section makes is honoured; the *reason* the harness gives for
existing is what is false, and that is P1-2, not this claim.

### C5. The ledger gate covers every mechanical packet — **PARTIAL**

`LEDGER_GATED_PACKETS_V1` (`tools/o008_formal_cycle_admission_v1.py:95-102`) does now name all six packets
with pinned kill counts totalling **97** (20 + 22 + 31 + 21 + 1 + 2), executed as six of the 38 replay
commands — the P39 P2-4 repair is real. `_grade_ledger` does now inspect rows rather than four totals — the
P39 P3-2/P3-3 repair is real. But the grader is defeatable (**P2-1**) and the headline guard has no
declared row (**P2-2**).

### C6. Known-opens

* **Second reviewer's P39 P2-5 — still open, as flagged.** The carve-out is now in the module docstring
  (`…projection_v1.py:32-35`: "Two state-level gates are outside this remit and are reported by the
  checker rather than refused here"). It is **not** in the packet: O-008 nonclaim 5 states the refusal
  property with no exception, and `BLOCKED_LANE_PRODUCER_MISSING` appears in the packet only at
  `required_sidecar.implementation.reject_codes[4]`, never as a claim about the projection.
  `REGISTERED_EMPTY_ROOT_DRIFT` likewise. Confirmed open (P3-2).
* **Second reviewer's P39 P3-2 — MOOT.** `test_one_pending_obligation_takes_the_residual_and_the_checker_accepts_the_rows`
  is gone. Its replacement, `test_row_derivation_accepts_the_determined_shapes` (line 512), claims only
  that the rows "are derived and ordered" and asserts exactly that. The overclaim did **not** move to a new
  name. I checked every new test name and docstring in the file against its body; the only
  name/body mismatches I found are P1-1 and P1-2, which are separate findings.

### C7. Process disclosure — **acceptable, with one reservation**

I can verify the parts that leave evidence, and they check out: `subject_tree` equals the S40 tree exactly,
`git status --short` is empty in a fresh worktree at P40, no partial packet write survives, and the packet
JSON hashes to the expected value. The claim that the pinned battery ran at 15:29Z against a
byte-identical tree is consistent with that, but it is not independently verifiable from the artifact —
it rests on the author's record. The disclosure that two earlier chain attempts died because the author
amended a running chain script is the right thing to have written down, and nothing from those attempts is
in the tree.

My reservation is narrower than the process: **the cargo gate was run at P, after the battery**, and the
battery is what the packet's `author_record` is built from. That ordering is disclosed, and I re-ran the
cargo gate myself and got the declared numbers, so the gap is closed by replay rather than by trust. I do
not raise it as a finding.

### C8. The packet — **CLOSED**

58 pin roles, 38 replay commands, nonclaims intact (§1), authority NONE, `formal_core_complete false`.

---

## 3. Findings

### P1-1 — The candidate's stated standard of evidence is not implemented in either direction; the helper that would implement it is dead code

**Where.** `tests/core/test_global_accounting_allocation_projection_v1.py:97` defines
`_no_certificate_reconciles(state)`. It is never called.

**The claims it is supposed to discharge**, all three written in this candidate:

1. S40 commit message: "An UNRECONCILABLE refusal is now shown by building the certificate the state
   itself implies and having the checker refuse it, the method the reviewer used to falsify the old claim.
   The AMBIGUOUS one is shown by exhibiting two certificates the checker accepts. Neither is asserted from
   the projection's own answer."
2. `tests/evidence/test_hygiene/THV1-20260903-global-accounting-allocation-projection-v3.json`,
   `claim_scope` (pinned, byte-exact): "the suite's standard changed: an UNRECONCILABLE refusal is shown
   by BUILDING the state-consistent certificate and having the checker refuse it, while the AMBIGUOUS one
   is shown by exhibiting two certificates the checker accepts."
3. `src/core/global_accounting_allocation_projection_v1.py:101-103` (the reject-family docstring): "The
   tests assert the second kind by BUILDING the state-consistent certificate and showing the checker
   refuses it, rather than by asserting the classification."

**Reproduction.**

```bash
cd /tmp/zenodex-formal-core-opus-c9c3
grep -rn "_no_certificate_reconciles" . --include=*.py --include=*.json --include=*.md
#   -> exactly one hit: the def at tests/core/…_projection_v1.py:97
"$PY" - <<'EOF'
import ast, pathlib
t = ast.parse(pathlib.Path("tests/core/test_global_accounting_allocation_projection_v1.py").read_text())
print(sum(1 for n in ast.walk(t) if isinstance(n, ast.Name) and n.id == "_no_certificate_reconciles"))
EOF
#   -> 0   (not even a bare name reference)
# and the decisive one — make the helper explode and the suite does not notice:
sed -i 's/^def _no_certificate_reconciles(state) -> str:$/&\n    raise AssertionError("MUTANT")/' \
    tests/core/test_global_accounting_allocation_projection_v1.py
"$PY" -m pytest -q tests/core/test_global_accounting_allocation_projection_v1.py -p no:randomly | tail -1
#   -> 53 passed          (unchanged)
git checkout -- tests/core/test_global_accounting_allocation_projection_v1.py
```

The AMBIGUOUS half is missing outright: no test anywhere exhibits two certificates the checker accepts.
`grep -n "check_global_accounting_allocation_certificate_v1\|_check_exactly_once" ` on the test file
returns 11 hits; lines 127 and 132 are inside the dead helper, and the remaining nine all assert that the
projection's *own* certificate is accepted — never that a second, different one is.

What the tests actually do for every UNRECONCILABLE case is line 508: `assert observed is code`. That is
the projection classifying itself.

**Why this is P1 and not P2.** The P39 P1 that this candidate exists to repair was a claim the author had
made to the user in writing that the code falsified. This is the same defect, in the repair, about the
repair's own headline method — and it is now additionally pinned into an evidence packet by sha256.

**Second, independent weakness in the same helper** (it matters for the fix, not only for the fact that it
is uncalled): even if it were called, `_no_certificate_reconciles` would not support the word "no". It
builds exactly **one** candidate — the registered-empty fragment with custody/liabilities/reserves
substituted (lines 102-121) — and it omits `pending_external_obligations` and `terminal_bindings`
entirely, so for any state carrying a PENDING outbox entry it refuses a candidate that a *different*
certificate would not have. It then runs four of the eleven checks (`_check_exactly_once`,
`_check_entitlement_rows`, `_check_external_obligations`, `_check_lane_aggregates`), skipping
`_check_reserve_rows` — which is the check that actually forecloses "absorb the residual with an extra
reserve row", the most obvious escape from `PROJECTION_UNASSIGNED_CONTROLLED_ATOMS`. It can therefore
return `"ACCEPTED"` for a certificate the real checker rejects, and its returned code need not be the code
`check_global_accounting_allocation_certificate_v1` would return, because `CHECK_ORDER_V1`
(`…certificate_v1.py:1005-1019`) is not the order the helper uses.

**Minimal fix.** Either (a) implement the claim: call the helper from every UNRECONCILABLE case in
`_ROW_CASES` and assert the *checker's* reject code, rebuild the candidate to include the external and
terminal rows the state implies, run the full `check_global_accounting_allocation_certificate_v1` rather
than four hand-picked checks, and add the missing AMBIGUOUS test (two accepted certificates over one
state — this is about twenty lines; my C1 probe above is a working sketch); or (b) withdraw all three
claim texts and say the suite asserts the classification, which is what it does. Do not ship (2) and (3)
unchanged with an uncalled helper.

### P1-2 — The pinned nonclaim "unreachable through the public entry point" is false, in two independent ways

**Where.** THV1 packet nonclaim 8 (pinned, byte-exact): "Under the current registry the reserve, external
and terminal derivation is unreachable through the public entry point, because the only receipt-backed
producer emits neither and the entry refuses first". Repeated in the same packet's `claim_scope` ("the
whole reserve, external and terminal derivation is unreachable through the entry point"), in the S40
commit message, in `_derive_rows`'s docstring
(`tests/core/…_projection_v1.py:74`: "they are not reachable through the public entry today") and in the
`_ROW_CASES` test docstring (line 499: "rather than the entry point because the entry refuses earlier").

**Falsification A — two of the twelve `_ROW_CASES` fixtures reach their code through the entry point,
unchanged.** `PROJECTION_NEGATIVE_RESIDUAL` and `PROJECTION_UNASSIGNED_CONTROLLED_ATOMS` need no reserve,
no outbox entry and no open terminal, so `PROJECTION_ROWS_BEYOND_PRODUCER` never fires for them:

```bash
"$PY" - <<'EOF'
import sys; sys.path.insert(0, ".")
from tests.core.test_global_accounting_allocation_projection_v1 import _backed_state, _terminal, _root_of, _ROW_CASES
from src.core.global_accounting_allocation_projection_v1 import project_allocation_certificate_v1, AllocationProjectionRejectedV1
for label, tables, terminals, code, _ in _ROW_CASES:
    st = _backed_state(tuple(_terminal(t[0], t[1], **(t[2] if len(t) > 2 else {})) for t in terminals), **tables)
    r = project_allocation_certificate_v1(st, _root_of(st))
    got = r.code.value if isinstance(r, AllocationProjectionRejectedV1) else "ACCEPTED"
    print(f"{'SAME' if got == code.value else 'diff'}  {label[:46]:48} {got}")
EOF
```

```
SAME  entitlements exceeding custody                   PROJECTION_NEGATIVE_RESIDUAL
SAME  controlled atoms no obligation can absorb        PROJECTION_UNASSIGNED_CONTROLLED_ATOMS
```

(the other ten are masked by `PROJECTION_ROWS_BEYOND_PRODUCER`, as the docstring says). So the blanket
justification for routing all twelve through the harness is false for two of them, and those two are
exactly the two codes the P39 P1-1 repair introduced — the cases where an entry-point test would carry the
most weight.

**Falsification B — enabling a `NO_PRODUCER` lane reaches the "unreachable" derivation through the entry
point.** Nothing prevents `SPOT_LIQUIDITY` from being enabled, and `PROJECTION_ROWS_BEYOND_PRODUCER` is
guarded on `RECEIPT_BACKED` (`…projection_v1.py:464-480`), so it does not fire:

```bash
"$PY" - <<'EOF'
import sys, dataclasses; sys.path.insert(0, ".")
from tests.core.test_global_accounting_allocation_projection_v1 import _backed_state, _terminal
from src.core.global_accounting_allocation_projection_v1 import project_allocation_certificate_v1, AllocationProjectionRejectedV1
from src.core.global_settlement_types_v1 import LaneIdV1
b = _backed_state((_terminal("terminal-1", 99),))
roots = tuple(dataclasses.replace(l, enabled=(l.lane_id is LaneIdV1.SPOT_LIQUIDITY)) for l in b.lane_roots)
st = dataclasses.replace(b, lane_roots=roots,
        terminal_obligations=(_terminal("terminal-1", 99, lane=LaneIdV1.SPOT_LIQUIDITY),))
print(project_allocation_certificate_v1(st, ()).code.value)
EOF
```

```
PROJECTION_TERMINAL_EXCEEDS_ENTITLEMENT
```

This is not a novel state shape: it is the same shape the second P39 reviewer used in their own P2-5 probe
("a state with `SECOND_ENABLED` (SPOT_LIQUIDITY, `NO_PRODUCER`) projects to a certificate"), which the
author read and answered in this candidate. The commit message even anticipates it — "rather than hidden
behind a lane whose registry entry would make every such state trivially unreconcilable" — which is a
sound methodological reason to prefer the harness, but it is a reason **not to test that way**, not a
basis for the sentence "unreachable through the public entry point", which the next probe falsifies.

**Why P1.** The failure mode this candidate exists to repair is a written claim the code falsifies, and
this one is pinned by sha256 into an evidence packet, restated in three other places, and refuted by three
lines of Python.

**Minimal fix.** Move the two Falsification-A cases to the entry point (they need no new fixture — the
same `_backed_state` call and `_root_of(state)`). Restate nonclaim 8, `claim_scope`, `_derive_rows:74` and
the `_ROW_CASES` docstring as what is true: *on the only receipt-backed lane the entry point refuses
reserve/external/terminal-bearing states before the row derivation runs, so those paths are exercised
through the helpers; they remain reachable through the entry point on a lane with no registered producer,
which the checker rejects for an unrelated reason.*

### P2-1 — `_grade_ledger` accepts a report in which one mutation is reported N times, with digests that are not digests

**Where.** `tools/o008_formal_cycle_admission_v1.py:4108-4122`. The strengthening is described as "every
mechanical row must name the mutation that produced its verdict … with distinct needle and replacement
digests". "Distinct" is enforced only *within* a row (line 4118: `needle_sha256 == replacement_sha256`).
There is no check that the digests are 64-hex, that `path` is a repository file, or that the
`(path, needle_sha256, replacement_sha256)` triples differ *between* rows.

**Reproduction.**

```bash
"$PY" - <<'EOF'
import sys, json, inspect; sys.path.insert(0, ".")
from tools.o008_formal_cycle_admission_v1 import _grade_ledger, ReplayObservationV1
row = {"verdict": "KILLED", "description": "row",
       "mutation": {"path": "/etc/passwd", "needle_sha256": "a", "replacement_sha256": "b"}}
payload = {"killed": 20, "survived": 0, "errors": 0, "mechanical": 20, "rows": [dict(row) for _ in range(20)]}
obs = ReplayObservationV1(command_id="ledger_projection_rows", exit_code=0,
                          stdout=json.dumps(payload).encode(), stderr=b"", timed_out=False, probe_sha256="")
print(_grade_ledger(obs, 20))
EOF
```

```
{'killed': 20, 'mechanical': 20, 'survived': 0, 'errors': 0}      # accepted
```

Twenty KILLED rows, one mutation between them, a path outside the repo, and digests `"a"`/`"b"`. The gate
cannot distinguish that from twenty real mutants. In mitigation, `tools/thv1_mutation_ledger_v1.py` is
pinned by content hash, so an honest run produces honest rows and this is defence-in-depth rather than the
only barrier — which is why it is P2 and not P1.

**Minimal fix.** In the row loop: require `re.fullmatch(r"[0-9a-f]{64}", …)` on both digests; require
`mutation["path"]` to be one of the packet's declared mutant paths; and collect the triples into a set,
rejecting if `len(set) != killed`.

### P2-2 — The candidate's headline guard has no declared mutation row, so the ledger's 97 rows do not cover it

**Where.** The `PROJECTION_ROWS_BEYOND_PRODUCER` guard,
`src/core/global_accounting_allocation_projection_v1.py:474` (`if beyond:`), is the change the candidate
leads with. `THV1-20260903-global-accounting-allocation-projection-v3` declares 20 mutations; none names
`test_a_witnessed_lane_carrying_rows_no_producer_emits_is_refused` (line 537), and the string `beyond`
occurs **0** times in the packet. The pinned count `("ledger_projection_rows", …, 20)` therefore certifies
twenty guards, none of them this one.

**Reproduction.**

```bash
"$PY" -c "
import json,collections
d=json.load(open('tests/evidence/test_hygiene/THV1-20260903-global-accounting-allocation-projection-v3.json'))
print(json.dumps(d).count('beyond'))
print(collections.Counter(m['killed_by'].split('::')[-1].split('[')[0] for m in d['mutations']))"
```
`0`, and `test_a_witnessed_lane_carrying_rows_no_producer_emits_is_refused` is absent from the counter.

**Scope, stated so this is not read as worse than it is.** The guard *is* covered by the suite. Neutering
it fails exactly one test:

```bash
sed -i 's/^                if beyond:$/                if beyond and False:/' src/core/global_accounting_allocation_projection_v1.py
"$PY" -m pytest -q tests/core/test_global_accounting_allocation_projection_v1.py -p no:randomly | tail -1
#   -> 1 failed, 52 passed
git checkout -- src/core/global_accounting_allocation_projection_v1.py
```

So this is a gap in the *declared mechanical evidence*, not in coverage.

**Minimal fix.** Add the 21st row (`needle "                if beyond:"` → `"                if beyond and False:"`,
`killed_by` the test at line 537) and bump `LEDGER_GATED_PACKETS_V1` to 21 / 98.

### P2-3 — A terminal binding with *zero* candidate principals is reported with an UNDETERMINED code

**Where.** `src/core/global_accounting_allocation_projection_v1.py:351-355`: `if len(principals) != 1:`
raises `PROJECTION_TERMINAL_DOMAIN_AMBIGUOUS`. `len(principals) == 0` means no controlled location can
bind the row at all — *no* certificate exists, which is the UNRECONCILABLE kind, not "more than one
acceptable certificate exists". This is the same misclassification the primary P39 P1-1 flagged
(unassignable atoms reported as an ambiguity), surviving inside the repair for it.

**Reproduction** — the branch exists and produces the wrong kind of code:

```bash
"$PY" - <<'EOF'
import sys; sys.path.insert(0, ".")
import src.core.global_accounting_allocation_projection_v1 as proj
from tests.core.test_global_accounting_allocation_projection_v1 import _backed_state, _terminal
st = _backed_state((_terminal("terminal-1", 1),))
ctrl = (proj.ControlledLocationRowV1("USD", "pool-a", "vault", 10),)
ents = (proj.ClaimantEntitlementRowV1("USD", "alice", "spot-pool", 10),)
try:
    proj._terminal_rows_v1(st, st.lane_roots[0].lane_id, st.lane_roots[0].state_root, ctrl, ents)
except proj._Reject as r:
    print(r.code.value, "|", r.detail)
EOF
```

```
PROJECTION_TERMINAL_DOMAIN_AMBIGUOUS | terminal-1: 0 principals
```

The detail string names the zero. It is unreachable from a whole state **only** because
`_external_rows_v1` runs first and an entitlement in a domain with no custody forces
`PROJECTION_NEGATIVE_RESIDUAL` (I confirmed this: the same shape routed through `_derive_rows` returns
`PROJECTION_NEGATIVE_RESIDUAL`). The correct classification therefore depends on a check-ordering accident
between two functions, is not asserted anywhere, and `_ROW_CASES` covers the two-principal case but never
the zero-principal one.

**Minimal fix.** Split the zero case: `if not principals: _fail(…TERMINAL_WITHOUT_ENTITLEMENT or a new
unreconcilable code, …)` before the `!= 1` test, and add the `_ROW_CASES` entry. Failing that, add a test
that pins the pre-emption so a future reordering cannot silently reintroduce a P39-P1-class
misclassification.

### P2-4 — Two of the ten named THV1 packets are bound by nothing in this candidate

`THV1-20260902-global-settlement-v1-canonical-exact-admission-v10` and
`THV1-20260901-claimant-backing-guard-golden-v29` appear in the review's list of ten, but
`grep -rl` over the repo finds each referenced only by its own file: neither is in the O-008 packet's
`hygiene_selection` (which pins 7 distinct packets), nor in `LEDGER_GATED_PACKETS_V1`, nor anywhere in
`tools/`. Their only gate is the generic 226-packet `check_test_hygiene_v1.py` sweep, which nonclaim 14
already scopes as "bound by pin only". Their own pins and node ids are byte-exact (§1), so nothing is
wrong with them; the finding is that the candidate's evidence set is two packets smaller than the review
brief implies.

**Minimal fix.** Either add them to `hygiene_selection` or say in the packet which of the ten are pinned
and which are covered only by the sweep.

### P3-1 — The reject-family docstring's two-kind split omits 3 of its 13 codes

`src/core/global_accounting_allocation_projection_v1.py:91-103` says "Two kinds of refusal share this
family", then lists two `..._AMBIGUOUS` codes and eight UNRECONCILABLE ones — ten. `ROWS_BEYOND_PRODUCER`
(the candidate's headline, and per module claim 2 genuinely unreconcilable), `BINDING_ROOT_MISSING` and
`BINDING_ROOT_UNEXPECTED` are placed in neither kind. The last two are arguably caller-input refusals
rather than statements about the state, but the docstring does not say so. **Fix:** add
`ROWS_BEYOND_PRODUCER` to the UNRECONCILABLE list and one sentence putting the two binding-root codes
outside the split.

### P3-2 — Second reviewer's P39 P2-5 is closed in the module and still open in the packet

Confirmed open, as the review brief anticipated. The carve-out now appears at
`…projection_v1.py:32-35`, but O-008 nonclaim 5 still states the refusal property without exception, and
neither `BLOCKED_LANE_PRODUCER_MISSING` nor `REGISTERED_EMPTY_ROOT_DRIFT` appears in any claim text (the
former occurs once in the packet, at `required_sidecar.implementation.reject_codes[4]`, which is a
different subject). **Fix:** append the module's exception sentence to nonclaim 5.

### P3-3 — The two branches are disjoint as codes, not as states

A state can satisfy both branches, and the code returned is decided by check order, not by the state:

```
negative residual only                                      -> PROJECTION_NEGATIVE_RESIDUAL
negative residual AND a reserve on the receipt-backed lane  -> PROJECTION_ROWS_BEYOND_PRODUCER
```

That is fine behaviour (a refusal carries one code) but "the two branches are disjoint" is a claim about
states, and it is not true of them. **Fix:** say the family is a partition of *refusals*, and that
`ROWS_BEYOND_PRODUCER` pre-empts the residual codes.

### P3-4 — `_derive_rows` reads `state.lane_roots[0]` rather than the enabled lane

`tests/core/…_projection_v1.py:88` takes `lane_root = state.lane_roots[0]` and passes its id and root to
`_terminal_rows_v1`, whereas the entry point passes the *enabled* lane
(`…projection_v1.py:458`). For every fixture in `_ROW_CASES` lane 0 is the enabled lane, so the two
agree today, but the harness that stands in for the entry point does not reproduce the entry point's lane
selection, and the `PROJECTION_NO_LANE_FOR_ROWS` case ("an OPEN obligation naming another lane") is
precisely a lane-identity test. **Fix:** select the enabled lane in the harness the way the entry point
does.

---

## 4. Mutation spot-checks (applied, run, restored)

| declared row | needle → replacement | named test | observed |
|---|---|---|---|
| #12 "derive an external row when entitlements and reserves exceed custody" | `if negative:` → `if negative and False:` | `test_row_derivation_refuses_every_shape…` | **1 failed**, 11 passed — kills |
| #13 "report unassignable controlled atoms as an ambiguity" | `if len(open_cells) > len(pending):` → `… and False:` | same | **2 failed**, 10 passed — kills |
| (undeclared, mine) `ROWS_BEYOND_PRODUCER` guard | `if beyond:` → `if beyond and False:` | whole file | 1 failed, 52 passed — covered but undeclared (P2-2) |

`git status --short` empty after each restore.

---

## 5. Bottom line

The two substantive repairs are real and I verified them independently: the `PROJECTION_NEGATIVE_RESIDUAL`
reordering makes that code reachable through the entry point for the first time, and the withdrawn
"function of the state" wording now survives the second-admitting-certificate attack that killed it twice.
The ledger gate genuinely grew from two packets to six and from four integers to per-row mutation
identity. Pins, node ids, the claim ceiling and every replayable gate I could run are exact.

What stops this from being an ACCEPT is that the candidate repairs a "claimed more than shipped" P1 by
claiming more than shipped, twice, in the same artifact: the UNRECONCILABLE/AMBIGUOUS evidence standard is
announced in a commit message, a module docstring and a sha256-pinned evidence packet, and is implemented
by a function nothing calls (P1-1); and the reachability sentence that justifies routing the whole row
contract through a test harness is refuted by three lines of Python, using a state shape the previous
reviewer had already put in front of the author (P1-2). Both are cheap to fix — P1-1 by calling the helper
and adding the twenty-line AMBIGUOUS test, P1-2 by moving two cases to the entry point and restating one
sentence — and neither touches the design, which I think is right.

**Grade B−. Authority NONE. `formal_core_complete` false. The claim ceiling must not move on this
candidate.**
