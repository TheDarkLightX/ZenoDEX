# ZenoDEX Formal Functional Core Closure — C9c-5 (P42) second independent review

| field | value |
|---|---|
| subject | S42 `06897ef74d5885dd1a5c7323c8dc111adcdeb7ea` — "fix: repair the claims in the artifact, not only in the code" |
| artifact | P42 `d33598ec4c79274c5a325d5cc655074a951d8847` (artifact-only child; `docs/research/ZENODEX_O008_FORMAL_CYCLE_V1.{json,md}`) |
| packet json sha256 | `8cfe379a0011c00f1b6f625fc22873672df7de8bf5ef4032881c1209f226a073` (matches the expected value) |
| worktree | `/tmp/zenodex-formal-core-opus2-c9c5` (detached at P42; `git status --short` empty at start and at end) |
| reviewer | second reviewer, fresh-context Opus 5 session |
| date | 2026-09-03 |
| verdict | **B−** — 2 P1, 5 P2, 7 P3, 3 INFO. REVISE (advisory). Authority stays NONE; the claim ceiling did not move. |

## Independence caveat (stated as required)

This campaign's second reviewer is normally a fresh-context Fable 5.1 session. Fable is out of usage
credit until 2026-09-06, so **both of this round's reviewers are fresh-context Opus 5 sessions and the
independence is weaker than the campaign standard**: the two reviewers and the author share a model
family. I had no access to the primary reviewer's worktree, report, or session, did not read the
author's scratchpad, and did not attempt to infer the other reviewer's findings. Read this as one of
two same-family reviews, not as an independent cross-model check.

---

## 1. Replays executed here

Environment: `PY=/home/trevormoc/Downloads/Autonomous Tau DEX/.venv/bin/python`,
`PYTHONDONTWRITEBYTECODE=1`, `TMPDIR=/tmp/zenodex-opus2-c9c5-tmp` (created by me),
`CARGO_TARGET_DIR=/tmp/zenodex-opus2-c9c5-cargo`, `CARGO_INCREMENTAL=0`. Every Lean-bearing command
ran under `flock -w 7200 /tmp/zenodex-lean.lock`. The nine `lean-mathlib/.lake/packages` symlinks
plus `external/ESSO` and `external/mathlib4` were already in place.

| command | result |
|---|---|
| `check_o008_formal_cycle_v1.py --root $PWD --packet-commit d33598ec4` | exit 0; `ok true`, `packet_admitted true`, `current_source_drift []`, `proof_replay NOT_RUN`. Result sha256 `83339e63475620a80b9dcb81a5a9d1332386422220bdfc9abab913c624706b32` |
| same `--replay --esso-python /usr/bin/python3 --esso-pythonpath …/ESSO` (2nd run) | exit 0; **`EXECUTED_PASS`, 39 runs**, `ok true`, `errors []`, `current_source_drift []`. Result sha256 `f4b28decb0de4dcecf542532c7105ac3ea10da66b658ed45813f769a5ac6de46` |
| — the **seven** ledger runs inside it | `projection 29`, `tool 21`, `checker 3`, `admission 31`, `ownership 21`, `certificate 2`, `lineage 1` = **108 killed, 0 survived, 0 errors**, every one exit 0 — exactly the declared figures |
| — first `--replay` attempt (cold worktree) | exit 1, `EXECUTED_FAIL`; the ONLY failing run was `lean_version` (`lake env lean --version`, `timeout_seconds 300`), `exit -1 timed_out=True`. Every other one of the 39 was green with identical comparables. See **INFO-1**: this is an environment/cold-start artifact, not a candidate defect, but the declared 300 s budget does not cover a cold `lake env` in a fresh worktree |
| `build_o008_formal_cycle_v1.py … --check --replay --output-json/-md` | see §1a |
| `cargo fmt --all -- --check` (`zk/global_settlement_abi_v1`) | exit 0 |
| `cargo clippy --locked --all-targets -- -D warnings` | exit 0 |
| `cargo test --locked` | exit 0; 54 summaries, **536 passed**, 0 failed — matches the declared figure |
| `tests/core/test_global_accounting_allocation_projection_v1.py` | **87 passed** (declared `PROJECTION_GATE_EXPECTED_PASSED_V1 = 87`) |
| `tests/formal/test_lean_asset_transfer_refinement_v1.py` | covered by the replay's `transfer_refinement_gate`: **40 passed** (declared 40) |
| `tests/core/test_transition_resource_bound_totality_v1.py` | 10 passed |
| `tests/core/test_global_settlement_abi_v1_resource_bounds.py` | 17 passed |
| `tests/core/test_global_settlement_abi_v1.py` | 75 passed |
| `tests/test_check_o008_formal_cycle_v1.py` | **404 passed** (261 s) |
| `tests/test_check_global_settlement_canonical_manifest_v1.py` | 8 passed |
| `tests/test_thv1_mutation_ledger_v1.py` | 19 passed |
| `check_test_hygiene_v1.py --json` | exit 0; `ok true`, **234 packets**, `changed_path_count 0` |
| `--base-ref e68a9e764 --json` (receipts head) | exit 0; `ok true`, 0 changed |
| `--base-ref f686e66ca --json` (S42's parent) | exit 0; `ok true`, 11 changed |
| `--base-ref fd409ba6f7d… --json` (campaign base) | exit 0; `ok true`, 419 changed — **the campaign base is green** |

`tests/core/test_zusd_liquidation_partition.py` excluded as instructed.

### Pin and node-id audit — clean

* O-008 packet: **58** `source_pins`, all byte-exact on `sha256`, `git hash-object` **and** `size`;
  0 mismatches. **39** replay commands as declared (7 of them ledger runs — the brief's "38 / six
  ledger runs" describes the predecessor; see INFO-2). `hygiene_selection`: 55 rows over 7 distinct
  packets, every `packet_sha256`, `packet_git_blob` and `pin_sha256` byte-exact, 0 mismatches.
* The five THV1 packets in scope: **87** `source_pins` + `test_pins`, **0 bad** on sha/size/blob;
  **953** pytest node ids appearing anywhere in them, **0 orphans** (each resolves to a real `def`
  in its pinned file); **232** pytest mutation killers, 0 unresolved.
* Claim ceiling: `migration/production/publication/release/settlement/value_movement/verifier_authority`
  all `NONE`; `formal_core_complete false`; `o008_status OPEN_EXACT_ALL_12_RECONCILIATION_MISSING`;
  `value_movement_gates_closed 0 / 12`. **The ceiling did not move.**

### Independent mutation execution (not through the packet's own runner)

`git archive HEAD` into `/tmp/opus2c9c5-mut` (src/tests/tools) and `/tmp/opus2c9c5-full` (whole tree);
for each spot-checked row I applied the mutant, ran only that row's named killer, and restored.
Twelve rows checked, chosen to cover everything this candidate added:

```
projection-v5 [ 1] KILLED  if len(hosting) != 1:
projection-v5 [20] KILLED  if beyond:
projection-v5 [24] KILLED  if witness.fragment != fragment:
projection-v5 [25] KILLED  if lane_witnesses and len(lane_witnesses) != len(ALL_LANE_IDS_V1):
projection-v5 [26] KILLED  hosting = [domain for domain in domains if capacity.get(...)…]
projection-v5 [27] KILLED  if not hosting:
projection-v5 [28] KILLED  if len(cells) == 1 and len(controlling) == 1:
ledger-v6     [18] KILLED  if not rest.startswith(f"{module}::"):
ledger-v6     [19] KILLED  if killer.lib:
admission-v38 [105] KILLED if _SHA256_HEX_RE_V1.fullmatch(mutation[digest_field]) is None:
admission-v38 [106] KILLED if not _portable_repo_path_v1(mutation["path"]):
admission-v38 [107] KILLED if identity in seen:
```

Note on method: the v38 rows first came back NOT-KILLED in the `src/tests/tools`-only extract, because
`tests/test_check_o008_formal_cycle_v1.py` needs the rest of the tree and its **control** run already
failed. Re-run in a full-tree copy they kill. Recording it because a reviewer reading only the first
run would have reported three false survivors.

---

## 1a. Builder `--check --replay`

`build_o008_formal_cycle_v1.py --root $PWD --subject-commit 06897ef74d5885dd1a5c7323c8dc111adcdeb7ea
--created-date 2026-09-03 --check --replay --esso-python /usr/bin/python3 --esso-pythonpath …/ESSO
--output-json docs/research/ZENODEX_O008_FORMAL_CYCLE_V1.json --output-md …V1.md`

* exit **0**; `{"mode": "check", "ok": true, "subject_commit": "06897ef74…"}`, **`drift []`**.
* Result sha256 `82c56257d57baf190cb2d61ac835466cba8dcea4d68958ab00f9f16f3310e8f5`.
* `git status --short` empty immediately after, and
  `sha256sum docs/research/ZENODEX_O008_FORMAL_CYCLE_V1.json` is still
  `8cfe379a0011c00f1b6f625fc22873672df7de8bf5ef4032881c1209f226a073` — **the packet regenerates
  byte-identically from the subject commit**, so the artifact is a function of S42 and the builder,
  not of anything typed into the file afterwards. (That is what makes P1-1 a defect in
  `NONCLAIMS_V1` rather than in the rendered JSON.)

---

## 2. One verdict per claim

### C1. The falsified sentences are gone from the artifact — **CLOSED for the three named sentences, and three NEW false claims took their place (P1-1)**

The three the brief names are genuinely repaired, and I checked the text rather than the commit
message:

* **O-008 nonclaim 5** (`tools/o008_formal_cycle_admission_v1.py:559-579`, rendered into the artifact):
  "Two kinds" → "THREE kinds"; "more than one **acceptable** certificate" → "more than one certificate
  that passes every row, partition and aggregate check"; and it now says why it is not "accepted"
  ("under the current registry no accepted certificate can carry an external, reserve or terminal row
  at all"). ✔
* **Projection packet nonclaim 7** (`THV1-20260903-…-projection-v5.json`) now reads "two certificates
  that pass every row, partition and aggregate check … NOT two ACCEPTED certificates: under the current
  registry the full checker refuses both (`RECEIPT_WITNESS_REQUIRED`)". Both halves of the old sentence
  are gone, and the replacement is the one the candidate's own test asserts. ✔
* **Nonclaim 8** now reads "TEN of the twelve row cases are masked … and TWO reach their own code
  through the public entry point", replacing "unreachable through the public entry point". ✔

Tree-wide grep for the three phrases over `src/`, `tests/`, `tools/` and the artifact: the only
surviving occurrences of "two accepted certificates", "the checker would take either" and "unreachable
through the public entry point" are in **superseded predecessor packets** (`…-projection-v3.json`,
`…-v4.json`), which are historical records, and in the module's own *negations*
(`src/core/…_projection_v1.py:25,35,129`). That is the right outcome.

But the brief asks the harder question — "is anything now claimed that a probe falsifies?" — and the
answer is yes, in **three** new places, all of them counts, and all three in sentences this commit
edited. That is **P1-1**, and the shape is the campaign's named failure mode a fifth time.

### C2. UNDETERMINED is defined by what the STATE does — **PARTIAL (P1-2)**

Both of opus2 P41 P1-2's counterexamples are genuinely closed, and I re-ran both:

```bash
# A: 1 PENDING entry over 0 residual cells  ->  PROJECTION_ZERO_RESIDUAL_ROW_UNSUPPORTED
#    detail "1 pending rows over no residual cells"    (was: ..._EXTERNAL_RESIDUAL_AMBIGUOUS)
# B: terminal entitled in two domains, only one with capacity  ->  DERIVES
#    TerminalBindingRowV1(..., control_domain='spot-pool', controlling_principal='pool-a')
#                                                     (was: ..._TERMINAL_DOMAIN_AMBIGUOUS)
```

This is the right kind of repair: the projection was made **complete** for those cases rather than
re-worded a third time, and the new `unsupported` kind ("the state determines the answer and this
module declines to derive it") is an honest fourth category.

The brief asked me to hunt a third sub-case. **There is one**, and it is `..._TERMINAL_DOMAIN_AMBIGUOUS`
again, one level up from the one that was fixed: the new capacity filter is **per row**, while the
checker's rule is **per (asset, claimant, control_domain) SUM**. See **P1-2**.

### C3. The witnessed-lane row-contents carve-out — **CLOSED, and the residue is stated correctly in the module**

`test_a_witnessed_lane_whose_rows_drift_from_its_receipt_is_refused`
(`tests/core/…_projection_v1.py:540-586`) pins three things, not two, and I reproduced all three:
without the witness the certificate is still derived and the checker's witness pass refuses it with
`RECEIPT_WITNESS_FRAGMENT_DRIFT`; with the witness the projection refuses first with
`PROJECTION_WITNESS_FRAGMENT_DRIFT` and carries the unchanged state root; and — the non-vacuity half —
an undrifted state still projects to a fragment **equal** to the witness's, so the new check refuses
drift rather than refusing witnesses.

Module claim 2 (`src/core/…_projection_v1.py:49-60`) states the residue correctly: "V1 state does not
carry the receipt's rows, so from the state alone the projection cannot see it and derives … Without
the witness the derived object is refused by the checker's witness pass, so nothing unsound is
admitted either way — what differs is which layer says no." That is exactly right, and it is the
sentence both P41 reviewers asked for.

I also tried to break the new code by handing the projection a witness that does not correspond to the
state, which would make `..._WITNESS_FRAGMENT_DRIFT` a caller-input fact wearing an `unreconcilable`
label. `VerifiedLaneAllocationFragmentV1.fragment` is a read-only property on a sealed minted object
and cannot be forged with `dataclasses.replace` or `object.__setattr__`, so a caller cannot supply a
witness that is not the mint's. The kind membership stands. One residue: the sentence is in module
claim 2 and in the packet's `claim_scope`, but in **no numbered nonclaim** (**P3-5**).

### C4. The defensive branch's unreachability is a search claim — **PARTIAL (P2-3)**

`tests/core/…_projection_v1.py:494-513` is honestly framed ("That is a statement about what has been
searched, not a proof of unreachability") and the entry-point half holds — I confirmed
`PROJECTION_TERMINAL_WITHOUT_BACKING` is masked on ASSET_TRANSFER by `PROJECTION_ROWS_BEYOND_PRODUCER`.
The claim that the capacity filter closed the P41 zero-atom route is also true.

The brief said "try to reach it another way." One probe did. See **P2-3**.

### C5. The ordering claim is narrowed and pinned — **PARTIAL (P2-1)**

Narrowed correctly in **three** places: `_state_level_refusals_v1`'s docstring
(`src/core/…_projection_v1.py:323-335`, which now spells out the `RECEIPT_WITNESS_REQUIRED`
counterexample), the test helper `_no_certificate_binds` (`tests/core/…:297-310`), and O-008
nonclaim 5 ("in the checker's order — though not necessarily before every other code the checker could
raise: the receipt-witness check runs between them").

There is a **fourth** place, in the same docstring the author edited in this commit, and it still
carries the un-narrowed claim. **P2-1**.

### C6. The `--lib` killer form binds its declared file — **PARTIAL (P2-4)**

`tools/thv1_mutation_ledger_v1.py:174-190` now requires the filter to start with the declared file's
own module segment, and the primary P41 reviewer's exact example is refused:

```
zk/global_settlement_abi_v1/src/lib.rs::global_accounting_allocation_certificate::tests::the_source_…
  LEDGER: REJECT (crate unit-test filter must start with the declared module lib::)
```

To the brief's exact question — can an accepted row's killer fail to exercise the mutated code? — **no,
soundness holds**: `control_error_v1` requires a green selected control run and `mutant_verdict_v1`
requires a cargo summary with `failed > 0`, so some *selected* test must observe the mutation; a
compile-breaking mutant yields `UNVIABLE`. The residual defects are attribution and scope:
the filter is still a crate-wide substring, and the rule is enforced in the **ledger tool only**, not
in the packet validator that gates all 234 packets. **P2-4**.

### C7. Six guards that carried no row now have one; the checker file is a seventh gated packet — **CLOSED**

`LEDGER_GATED_PACKETS_V1` (`tools/o008_formal_cycle_admission_v1.py:95-103`) now has seven entries;
`tools/o008_formal_cycle_admission_v1.py` itself carries three rows (v38 rows 105-107), where it
carried zero across all 231 packets at P41. The projection's new branches carry rows 1, 26, 27, 28;
the witness pass carries 24 and 25; the ledger's new form carries 18 and 19. All twelve I applied by
hand kill (§1). The full ledger replay is 108 killed / 0 survived / 0 errors.

I then hunted for guards **this candidate added** that carry no row, which is the finding two reviews
running. Three exist — `if type(lane_witnesses) is not tuple:` (`:604`), the exact-type slot guard
(`:608-610`), and the outer `if lane_witnesses:` (`:706`) — but all three are killed by
`test_the_witness_slots_are_exactly_typed`, verified by mutating each to `if False:` (1 failed,
86 passed each time). Since the analogous `if type(lane_binding_roots) is not tuple:` **does** carry
row 6, this is an asymmetry in declared evidence, not a test gap: **P3-4**.

One claim about the ledger set is false, though: **not** all 108 rows are distinct (**P2-5**).

### C8. All six `REPLAY_LEDGER_*` codes have tests — **CLOSED**

`tests/test_check_o008_formal_cycle_v1.py:1288-1330`. The three opus2 P41 P2-5 named
(`..._ROW_NOT_KILLED`, `..._KILLED_COUNT_DRIFT`, `..._REPORT_UNPARSEABLE`) now have five parametrised
cases plus an unparseable-stdout case, each asserting the specific reject code — including
`survived: 1 → REPLAY_LEDGER_ROW_NOT_KILLED`, the one that review named explicitly. Closed.

### C9. Housekeeping repairs — **three of four CLOSED**

| item | verdict |
|---|---|
| Opus P40 P3-4 — the row harness selects the ENABLED lane | **CLOSED** — `tests/core/…:117-121` now takes `[root for root in state.lane_roots if root.enabled]` with an assertion that at most one is enabled |
| opus2 P40 P3-6 — the closed-and-ordered docstring claims more than its scan | **CLOSED** — `tests/core/…:700-710` now says the scan is textual over the whole file and that per-code reachability is established elsewhere |
| opus2 P41 P3-4 — the check order omits the producer-capability gate | **CLOSED** — `src/core/…_projection_v1.py:585-590` now lists it as `(2b)`, with the fact that it was omitted until P41 |
| Opus P40 P2-4 / opus2 P40 P3-3 — which THV1 packets the checker binds | **PRESENT BUT WRONG BY COUNT** — O-008 nonclaim 14 is added and says the right things, but says "The **six** ledger-gated packets" and "two of the **six**" when the same commit made it seven (part of **P1-1**) |

### C10. The two items stated as not addressed — **both open, and neither is stated anywhere (P3-6)**

opus2 P41 P3-1 is still open: `tests/test_check_o008_formal_cycle_v1.py:1066-1067` still says "the
grader now refuses a mutation applied to a file this packet does not bind (Opus P40 P2-1)", which
`_grade_ledger`'s own docstring (`tools/o008_formal_cycle_admission_v1.py:4116-4124`) says it does not
do. opus2 P41 P3-6 is still open **and worse**.

But the brief says these are "stated as NOT addressed". They are not stated anywhere I can find:
`git log -1 --format=%B 06897ef74 | grep -i "not addressed"` is empty, and searching all three new
packets for `P3-1`, `P3-6`, "not addressed", "still open" and "residue" returns nothing. **P3-6**.

### C11. The packet — **58 pins, 39 commands, ceiling intact; two of its nonclaims are false (P1-1)**

---

## 3. Findings

### P1-1 — Three false counts in the pinned artifact, every one of them in a sentence this commit edited, and one of them hides the candidate's own headline repair

P42's entire diff is the two packet files. All three defects below are in text S42 rewrote.

**(a) `tools/o008_formal_cycle_admission_v1.py:560` → O-008 nonclaim 5: "THREE kinds of refusal share
that family", and the fourth kind is never named.** The module says four:

```bash
"$PY" -c "
import sys,json;sys.path.insert(0,'.')
from src.core.global_accounting_allocation_projection_v1 import ALLOCATION_PROJECTION_REFUSAL_KINDS_V1 as K
print(sorted(K))
nc=json.load(open('docs/research/ZENODEX_O008_FORMAL_CYCLE_V1.json'))['nonclaims'][4]
print('artifact says THREE:', 'THREE kinds' in nc, '| names UNSUPPORTED:', 'UNSUPPORTED' in nc)"
#   ['caller_input', 'undetermined', 'unreconcilable', 'unsupported']
#   artifact says THREE: True | names UNSUPPORTED: False
```

`src/core/…_projection_v1.py:119` says "**FOUR** kinds of refusal share this family"; the artifact says
three and then enumerates CALLER INPUT, UNDETERMINED and UNRECONCILABLE. The missing one,
`unsupported` / `PROJECTION_ZERO_RESIDUAL_ROW_UNSUPPORTED`, is **this candidate's own answer to the
deepest finding of the previous round** (opus2 P41 P1-2 A). The artifact a later reader is pinned to
does not know it exists.

**(b) same nonclaim: "UNDETERMINED means more than one certificate that passes every row, partition and
aggregate check exists".** This is the wording the module *deliberately abandoned* in this same commit.
`src/core/…_projection_v1.py:126-138` now says "the state does not pin the row content" and then,
explicitly, "it does **not follow** that more than one ROW-CHECKED certificate exists either". The
commit message agrees: "this candidate stops wording it". The artifact still words it — and P1-2 below
falsifies it with a twenty-line probe, a third time.

**(c) `tools/o008_formal_cycle_admission_v1.py:606-609` → O-008 nonclaim 14: "The **six** ledger-gated
packets … and two of the **six** are not in hygiene_selection."** There are seven, because this commit
added the seventh, and the commit message says so ("the checker file becomes a seventh ledger-gated
packet"). The same nonclaim gets the *other* count right ("currently seven distinct packets" for
`hygiene_selection`), so the two numbers now contradict each other inside one sentence pair.

```bash
"$PY" -c "
import sys,json;sys.path.insert(0,'.')
from tools.o008_formal_cycle_admission_v1 import LEDGER_GATED_PACKETS_V1 as G
d=json.load(open('docs/research/ZENODEX_O008_FORMAL_CYCLE_V1.json'))
print('gated packets in code:', len(G))
print('ledger replay commands in artifact:', len([c for c in d['proof_replay']['commands'] if 'ledger' in c['command_id']]))
print('artifact nonclaim 14 says six:', 'The six ledger-gated packets' in d['nonclaims'][13])"
#   gated packets in code: 7
#   ledger replay commands in artifact: 7
#   artifact nonclaim 14 says six: True
```

**(d) `THV1-20260903-…-projection-v5.json:585`, nonclaim 8: "TEN of the twelve row cases are masked …
and TWO reach their own code".** There are thirteen row cases — this commit added the thirteenth
("a zero-atom entitlement cannot host a positive claim") — so it is eleven and two:

```bash
"$PY" -c "
import sys;sys.path.insert(0,'.')
import tests.core.test_global_accounting_allocation_projection_v1 as T
from src.core import global_accounting_allocation_projection_v1 as P
m=r=0
for c in T._ROW_CASES:
    st=T._backed_state(tuple(T._terminal(t[0],t[1],**(t[2] if len(t)>2 else {})) for t in c[2]), **c[1])
    o=P.project_allocation_certificate_v1(st, T._root_of(st))
    m += o.code is P.AllocationProjectionRejectCodeV1.PROJECTION_ROWS_BEYOND_PRODUCER
    r += o.code is not P.AllocationProjectionRejectCodeV1.PROJECTION_ROWS_BEYOND_PRODUCER
print('row cases', len(T._ROW_CASES), '| masked', m, '| reach own code', r)"
#   row cases 13 | masked 11 | reach own code 2
```

The same "twelve" is carried at `tests/core/…_projection_v1.py:92`, `:98` and `:1088`.

**Why P1.** This candidate exists for one reason: C9c-4 fixed two sentences in five places and left the
sixth — the durable artifact — standing. The repair for that is real (§C1). But in making it, the
author edited four artifact sentences and put a **new false count into three of them**, and the count
that went wrong in (a) is precisely the fourth refusal kind this candidate invented as its headline
answer to the previous round. The pattern being reported for the fifth consecutive review is not
"forgot to edit the artifact"; it is "edited the artifact and did not re-derive the numbers in it from
the code".

**Minimal fix.** In `NONCLAIMS_V1` nonclaim 5: "THREE kinds" → "FOUR kinds"; add the UNSUPPORTED
sentence from the enum docstring; replace the UNDETERMINED definition with the module's current one
("the state does not pin the row content, so the projection refuses rather than choosing"). Nonclaim
14: "six" → "seven" in both places. THV1 nonclaim 8: "TEN of the twelve" → "ELEVEN of the thirteen",
and the same at `tests/core/…:92,98,1088`. Better: derive all four counts from
`len(ALLOCATION_PROJECTION_REFUSAL_KINDS_V1)`, `len(LEDGER_GATED_PACKETS_V1)` and `len(_ROW_CASES)` at
render time so a count cannot go stale again, and add one test asserting the nonclaim text agrees with
those lengths.

### P1-2 — A third sub-case where an `..._AMBIGUOUS` code fires over a state with **exactly one** row-checked certificate: the capacity filter is per-row, the checker's rule is per-key SUM

`src/core/global_accounting_allocation_projection_v1.py:500-511`. The filter added for opus2 P41 P1-2
is

```python
capacity = {e.control_domain: e.amount_atoms for e in entitlements
            if e.asset == terminal.asset and e.claimant == terminal.claimant}
hosting = [domain for domain in domains if capacity.get(domain, 0) >= terminal.amount_atoms]
```

and its comment states the checker's rule correctly — "The checker bounds each (asset, claimant,
domain) key's **terminal total** by that key's entitlement". The filter implements only the
single-row case of that rule. With two OPEN terminals sharing a claimant and asset, the per-row filter
can leave two candidate domains for one of them while the aggregate constraint admits exactly one
global assignment.

**Reproduction** (state: custody 6 in `spot-pool` + 5 in `vault`, alice entitled 6 and 5 in the same,
two OPEN terminals of 4 and 6):

```bash
cd /tmp/zenodex-formal-core-opus2-c9c5
"$PY" - <<'EOF'
import sys, itertools; sys.path.insert(0, ".")
from dataclasses import replace
import tests.core.test_global_accounting_allocation_projection_v1 as T
from src.core import global_accounting_allocation_certificate_v1 as cert
from tools import render_global_accounting_allocation_certificate_v1_golden as renderer
st = T._backed_state((T._terminal("terminal-1", 4), T._terminal("terminal-2", 6)),
    custody=(("pool-a","USD","spot-pool",6), ("pool-a","USD","vault",5)),
    liabilities=(("alice","USD","spot-pool",6), ("alice","USD","vault",5)))
print("projection ->", T._derive_rows(st)[0].value, "|", T._derive_rows(st)[1])
base = T._state_consistent_candidate(st)
slot = [i for i,r in enumerate(st.lane_roots) if r.enabled][0]
frag, lane_root = base.ordered_lane_fragments[slot], st.lane_roots[slot]
def verdict(c):
    for f in (cert._check_exactly_once, cert._check_terminal_totals):
        try: f(c)
        except cert._Reject as r: return r.code.value
    for f in (cert._check_entitlement_rows, cert._check_reserve_rows, cert._check_external_obligations,
              cert._check_terminal_bindings, cert._check_lane_aggregates):
        try: f(c, st)
        except cert._Reject as r: return r.code.value
    return "ACCEPTED"
for a in itertools.product(["spot-pool","vault"], repeat=2):
    rows = tuple(sorted((cert.TerminalBindingRowV1(obligation_id=t.obligation_id, asset=t.asset,
        claimant=t.claimant, amount_atoms=t.amount_atoms, control_domain=d,
        controlling_principal="pool-a", lane_id=t.lane_id, lane_state_root=lane_root.state_root)
        for t, d in zip(st.terminal_obligations, a)), key=lambda r: r.obligation_id))
    f2 = replace(frag, terminal_bindings=rows)
    c2 = renderer._certificate_with_fragments(base, tuple(f2 if i==slot else e for i,e in enumerate(base.ordered_lane_fragments)))
    print(f"  t1->{a[0]:9s} t2->{a[1]:9s} : {verdict(c2)}")
EOF
#   projection -> PROJECTION_TERMINAL_DOMAIN_AMBIGUOUS | terminal-1: 2 entitlement domains
#     t1->spot-pool t2->spot-pool : TERMINAL_BINDING_DRIFT
#     t1->spot-pool t2->vault     : TERMINAL_BINDING_DRIFT
#     t1->vault     t2->spot-pool : ACCEPTED  root=0x9a5138662617
#     t1->vault     t2->vault     : TERMINAL_BINDING_DRIFT
```

**Exactly one** of the four assignments passes every row, partition and aggregate check (all seven
checks, `_check_reserve_rows` included). The state determines the answer; the projection calls it an
ambiguity. `terminal-2` at 6 fits only `spot-pool` (vault is entitled 5), which consumes all 6 of
`spot-pool`'s entitlement, so `terminal-1` at 4 must go to `vault` — reasoning the filter cannot do
because it looks at one row at a time.

**Why P1.** The brief named this in advance: "hunt a THIRD sub-case where an AMBIGUOUS code fires over
a state whose row content is in fact determined; that is the same finding a third time and it would be
a P1." It is the same finding a third time, and it lands on the sentence that P1-1(b) shows the pinned
artifact still asserts as a definition. The refusal is **sound** — refusing is always safe, nothing
unsound is derived, and the enum docstring anticipates exactly this ("A future counterexample of the
same shape would be a defect in this classification, not in the refusal"). The defect is that the
artifact carries the unhedged definitional form that the probe refutes.

**Minimal fix.** Either extend the filter to the aggregate rule — walk the OPEN terminals per
`(asset, claimant)` and refuse `..._TERMINAL_DOMAIN_AMBIGUOUS` only when more than one **global**
assignment satisfies the per-key sum bound — or, at minimum, delete the definitional sentence from the
artifact and use the module's current one, and add this state as `_ROW_CASES` entry fourteen so the
sentence has a test that could fail. The module's hedge should be in the artifact too, not only in the
enum docstring.

### P2-1 — The un-narrowed ordering claim survives in a fourth place: the same docstring the author edited, contradicted by the same file eight lines later

`src/core/global_accounting_allocation_projection_v1.py:150-153`, the enum docstring's UNRECONCILABLE
paragraph:

> "From the lane configuration, which no arrangement of rows can repair, evaluated before the rows and
> **in the checker's own order so the projection names the code the checker would raise first**:
> `..._ENABLED_LANE_WITHOUT_PRODUCER`, `..._REGISTERED_EMPTY_ROOT_DRIFT`."

That is verbatim the sentence Opus P41 P2-6 falsified, and `:329-333` of the **same file** now says
the opposite: "NOT 'the code the checker would raise first' in general: `RECEIPT_WITNESS_REQUIRED`
runs between them". `git diff f686e66ca 06897ef74` shows the author edited this docstring in this
commit — "THREE kinds" → "FOUR kinds" four lines above, "sixteen" → "eighteen" eight lines below, and
the UNRECONCILABLE list extended two lines below — and left the falsified clause between them.

**Reproduction** (P41's counterexample, still live at S42):

```bash
"$PY" -c "
import sys; from dataclasses import replace; sys.path.insert(0,'.')
import tests.core.test_global_accounting_allocation_projection_v1 as T
from src.core.global_settlement_types_v1 import LaneIdV1
from src.core.global_accounting_allocation_projection_v1 import project_allocation_certificate_v1
st=T._backed_state(); f='0x'+'ab'*32
st=replace(st, lane_roots=tuple(replace(l,state_root=f) if l.lane_id is LaneIdV1.PROOF_REWARDS else l for l in st.lane_roots))
print(project_allocation_certificate_v1(st, T._root_of(st)).code.value, '|', T._no_certificate_binds(st))"
#   -> PROJECTION_REGISTERED_EMPTY_ROOT_DRIFT | RECEIPT_WITNESS_REQUIRED
```

**Minimal fix.** Replace lines 151-152 with the wording already used at `:323` and in nonclaim 5:
"evaluated before the rows and, among themselves, in the checker's order — though not necessarily
before every other code the checker could raise".

### P2-2 — Both P41 reviewers' P2-1 is untouched and undisclosed: the evidence builder's stated limitation gives a reason its own code falsifies

`tests/core/test_global_accounting_allocation_projection_v1.py:136-139`:

> "WHAT THIS DOES NOT COVER … **it builds no terminal binding rows**, so for a state with an OPEN
> terminal obligation it is one candidate among more than one"

and again at `:1027`: "the builder omits terminal rows, so other candidates exist". The builder builds
them at `:168-198`:

```bash
"$PY" -c "
import sys; sys.path.insert(0,'.')
import tests.core.test_global_accounting_allocation_projection_v1 as T
st = T._backed_state((T._terminal('terminal-1', 3),))
print(len(T._state_consistent_candidate(st).ordered_lane_fragments[0].terminal_bindings))"
#   -> 1
```

Both P41 reviewers raised this independently — the primary as P2-1, the second reviewer as P2-1 — and
neither line changed, nor is it listed anywhere as not-addressed. The **limitation** is real; the
reason given for it is false. The true reason is at `:174-190`: for an OPEN terminal the builder picks
`domains[0]`, `principals[0]`, or a `fallback`/`"unbound"` placeholder, an arbitrary choice from a set
the state may leave open.

**Minimal fix.** In both places: "for a state with an OPEN terminal it chooses one control domain and
one controlling principal from a set the state may leave open, so it is one candidate among several."

### P2-3 — The defensive branch is reachable through the row harness by a route the capacity filter does not close

`tests/core/test_global_accounting_allocation_projection_v1.py:508-513` says the capacity filter closed
the P41 zero-atom route and "Every route this suite can find now refuses earlier". A claimant entitled
**only** in a domain nothing controls, at zero atoms, with a zero-atom OPEN terminal, reaches the branch
in one probe — the residual for that cell is `0 − 0 = 0`, so the negative-residual check does not fire,
and `domains` has one member so the capacity filter never gets two candidates to reject:

```bash
"$PY" -c "
import sys; sys.path.insert(0,'.')
import tests.core.test_global_accounting_allocation_projection_v1 as T
from src.core import global_accounting_allocation_projection_v1 as proj
st = T._backed_state((T._terminal('terminal-1', 0),),
    custody=(('pool-a','USD','spot-pool',10),),
    liabilities=(('bob','USD','spot-pool',10), ('alice','USD','vault',0)))
print('row harness ->', T._derive_rows(st))
print('entry point ->', proj.project_allocation_certificate_v1(st, T._root_of(st)).code.value)"
#   row harness -> (PROJECTION_TERMINAL_WITHOUT_BACKING, 'terminal-1: no controlled location in vault')
#   entry point -> PROJECTION_ROWS_BEYOND_PRODUCER
```

This is P2 rather than P1 because the docstring's framing is honest — it claims a search, not a proof,
and the entry-point half still holds on all twelve lanes. But `PROJECTION_TERMINAL_WITHOUT_BACKING` is
now the only code in the family with no `_ROW_CASES` entry, and this state supplies one.

**Minimal fix.** Add the state above as `_ROW_CASES` entry fourteen for
`PROJECTION_TERMINAL_WITHOUT_BACKING`, and restate the docstring: reachable in the row harness only
with a zero-atom entitlement in the claimant's sole entitled domain.

### P2-4 — The `--lib` module-segment rule is enforced only by the ledger tool; the packet validator that gates all 234 packets still accepts the decorative form

`tools/test_hygiene_evidence_v1.py:305-320` (`_validate_killer`) checks only that the killer's path is
a pinned `.rs` under `/tests/` or `/src/` and that the filter is non-empty and whitespace-free. The new
rule lives in `tools/thv1_mutation_ledger_v1.py:174-187`, which runs only for the seven ledger-gated
packets. The two disagree in **both** directions:

```bash
"$PY" - <<'EOF'
import sys, json; sys.path.insert(0, ".")
from tools import test_hygiene_evidence_v1 as thv
from tools.thv1_mutation_ledger_v1 import parse_killer_v1, cargo_argv_v1, LedgerError
pkt = json.load(open("tests/evidence/test_hygiene/THV1-20260901-global-accounting-allocation-certificate-v23.json"))
rust = frozenset(p["path"] for p in pkt["source_pins"] if p["path"].endswith(".rs"))
for k in ["zk/global_settlement_abi_v1/src/lib.rs::global_accounting_allocation_certificate::tests::the_source_principal_guard_refuses_and_the_check_is_what_refuses",
          "zk/global_settlement_abi_v1/src/global_accounting_allocation_certificate.rs::global_accounting_allocation_certificate::tests::"]:
    try: thv._validate_killer(k, packet_context="c", pinned_nodes=frozenset(), rust_test_paths=rust, legacy=False); v="VALIDATOR ACCEPT"
    except Exception as e: v=f"VALIDATOR REJECT"
    try: l="LEDGER ACCEPT -> " + " ".join(cargo_argv_v1(parse_killer_v1(k)))
    except LedgerError as e: l=f"LEDGER REJECT"
    print(v, "|", l)
EOF
#   VALIDATOR ACCEPT | LEDGER REJECT                                     <- the decorative form
#   VALIDATOR ACCEPT | LEDGER ACCEPT -> cargo test … --lib -- global_accounting_allocation_certificate::tests::
```

So 227 of the 234 packets — every one that is not ledger-gated — can still declare
`zk/…/src/lib.rs::<other module>::<test>`, pass `check_test_hygiene_v1.py` green, and have `_pin_drift`
guard `lib.rs` while the mutant sits in another file. That is Opus P41 P2-4 unrepaired everywhere the
ledger does not run. The second line also shows the residual attribution gap opus2 P41 P2-2 reported:
a filter ending in `::` selects every test in the module (16 here), so a row reading as "this named
test kills it" means "some test in this module notices it". Soundness is unaffected, as established
in §C6.

**Minimal fix.** Move the module-segment rule into `_validate_killer` so it gates all 234 packets (one
`if path.endswith('.rs') and '/src/' in path` branch calling the same check), and require the `--lib`
control run to select exactly one cargo test (`sum(passed) == 1` in `control_error_v1`).

### P2-5 — "every one distinct": 108 rows, 107 distinct triples, and the grader's distinctness rule is per-packet

The commit message closes with "Ledger 97 → 108 rows over seven packets, **every one distinct** and
every one killed", and the brief repeats it. One triple is declared twice, in two different
ledger-gated packets:

```bash
"$PY" - <<'EOF'
import json, pathlib, hashlib, collections
gated=["THV1-20260903-global-accounting-allocation-projection-v5","THV1-20260903-thv1-mutation-ledger-v6",
 "THV1-20260901-o008-formal-cycle-admission-v38","THV1-20260903-o008-asset-transfer-receipt-admission-mechanical-v3",
 "THV1-20260903-global-settlement-exact-ownership-mechanical-v3","THV1-20260901-global-accounting-allocation-certificate-v23",
 "THV1-20260902-test-hygiene-lineage-ordering-v5"]
txt=lambda v: v if isinstance(v,str) else "\n".join(v)
seen=collections.defaultdict(list)
for g in gated:
    d=json.loads(pathlib.Path(f"tests/evidence/test_hygiene/{g}.json").read_text())
    for i,m in enumerate(d.get("mutations",[])):
        if isinstance(m,dict) and "mutant" in m:
            mu=m["mutant"]
            seen[(mu["path"], hashlib.sha256(txt(mu["needle_lines"]).encode()).hexdigest(),
                  hashlib.sha256(txt(mu["replacement_lines"]).encode()).hexdigest())].append((g,i))
print("rows", sum(map(len,seen.values())), "distinct", len(seen))
for k,v in seen.items():
    if len(v)>1: print("DUP", k[0], v)
EOF
#   rows 108 distinct 107
#   DUP src/core/asset_transfer_types_v1.py
#       [('…-o008-asset-transfer-receipt-admission-mechanical-v3', 6),
#        ('…-global-settlement-exact-ownership-mechanical-v3', 12)]
```

The rule at `tools/o008_formal_cycle_admission_v1.py:4172-4176` uses a `seen` set that is local to one
`_grade_ledger` call, i.e. to one packet, so a triple repeated across packets is never seen. This is
not a false kill — both rows really do kill, and the duplicate predates this candidate — but the
*claim* is broader than the guard, which is the shape this campaign keeps flagging, and the guard's
scope is stated nowhere.

**Minimal fix.** Either say "distinct within each packet" in the commit message and in the ledger
packet's `claim_scope`, or hoist `seen` to the checker so it spans the seven gated packets and
retarget one of the two rows.

### P3-1 — The enum docstring says "three kinds" twice while declaring four, and the test that pins the partition is named for three

`src/core/global_accounting_allocation_projection_v1.py:161` — "**The three kinds** are a partition of
all eighteen codes" — is on the exact line the author edited (`sixteen` → `eighteen`) while the same
docstring's first line says FOUR. `:190` — "# The three kinds the family docstring names" — precedes a
four-key dict. `tests/core/…:700` `test_the_three_refusal_kinds_partition_the_family` asserts
`set(kinds) == {"caller_input","undetermined","unsupported","unreconcilable"}`, and its docstring
(`:701`) still says "three of its **thirteen** codes" for a family of eighteen. **Fix:** "four" in all
three, rename the test, and update the thirteen.

### P3-2 — The module docstring is still headed C9c-4 and still says "the two kinds"

`src/core/global_accounting_allocation_projection_v1.py:1` — "…from a verified global economic state
**(C9c-4)**" — and `:31` — "The distinction **the two kinds** draw is about what the STATE determines".
Both are stale by one candidate and by two kinds. **Fix:** "(C9c-5)" and "the kinds".

### P3-3 — The two-certificate exhibition still runs four of the seven checks its own sentence names (Opus P41 P3-1, carried, undisclosed)

`tests/core/…_projection_v1.py:845-850` runs `_check_exactly_once`, `_check_entitlement_rows`,
`_check_external_obligations` and `_check_lane_aggregates`; the claim in the docstring and in nonclaim
7 is "every row, **partition** and aggregate check", and the partition check is `_check_reserve_rows`.
I ran all seven on both candidates and all seven pass, so the claim is true and the test under-checks
it. **Fix:** add `_check_reserve_rows`, `_check_terminal_bindings` and `_check_terminal_totals`; three
lines.

### P3-4 — Two guards added by this candidate carry no mechanical row, where the guard beside them does

`src/core/…_projection_v1.py:604` (`if type(lane_witnesses) is not tuple:`) and `:608-610` (the exact
slot type guard) have no row in `projection-v5`, while `if type(lane_binding_roots) is not tuple:`
three lines above is row 6. Both are killed by `test_the_witness_slots_are_exactly_typed` (verified:
`if False:` → 1 failed, 86 passed, each), so this is a declared-evidence gap rather than a test gap.
**Fix:** two rows, gate count 29 → 31.

### P3-5 — The witnessed-lane residue is in module claim 2 and the `claim_scope`, but in no numbered nonclaim

Both P41 reviewers asked for it "in claim 2 **and** in the THV1 nonclaims". `projection-v5`'s ten
nonclaims carry no sentence about it; `grep -i "witness" ` over them returns nothing. The `claim_scope`
does ("without them the earlier behaviour and its disclosure stand"), but `claim_scope` is prose about
the candidate while the nonclaims are the numbered, durable list. **Fix:** one nonclaim.

### P3-6 — The two items the brief says are "stated as NOT addressed" are stated nowhere, and one of them got worse in two packets this candidate cut

`git log -1 --format=%B 06897ef74 | grep -i "not addressed"` is empty, and the three new packets carry
no `P3-1`, `P3-6`, "not addressed", "still open" or "residue". Both are open:

* opus2 P41 P3-1: `tests/test_check_o008_formal_cycle_v1.py:1066-1067` still describes the withdrawn
  pin-based path guard as shipped.
* opus2 P41 P3-6: the `claim_scope` repeats spread. `certificate-v23` still repeats three sentences;
  `thv1-mutation-ledger-v6` repeats two; and **`o008-formal-cycle-admission-v38` went from one repeat
  at v37 to two**, i.e. the prepend-and-carry construction added a repeat in a packet cut here.

**Fix:** de-duplicate on carry, and list both as known-open in the packet rather than in nothing.

### P3-7 — Two of the seven ledger-gated packets are still outside `hygiene_selection`

`THV1-20260901-global-accounting-allocation-certificate-v23` (the one carrying the Rust row) and
`THV1-20260902-test-hygiene-lineage-ordering-v5`. Nonclaim 14 now discloses this, which is the right
instinct and closes the disclosure half of opus2 P40 P3-3 — but with the wrong count (P1-1(c)), and the
gap itself is unchanged for a third review. **Fix:** add both to `hygiene_selection`.

---

## 4. INFO

**INFO-1 — The declared `lean_version` timeout does not cover a cold worktree, and the replay is
fail-closed about it.** My first `--replay` returned exit 1 / `EXECUTED_FAIL` with a single failing
run: `lean_version` (`lake env lean --version`, `cwd lean-mathlib`, `timeout_seconds 300`) at
`exit -1 timed_out=True`. All 38 other runs were green with the same comparables as the successful
second run. Re-running on the now-warm worktree gave `EXECUTED_PASS` in 17 minutes. The first
`lake env` invocation in a fresh worktree does one-time resolution work that exceeds 300 s; every
subsequent Lean command in the same replay fits its own budget. This is fail-closed (a red result, not
a false green) and it is an environment fact, not a candidate defect — but a reviewer replaying from a
fresh worktree gets a red result for a reason that has nothing to do with the subject, and the packet
does not say so. **Suggested:** raise `lean_version`'s budget, or warm `lake env` before the timed
command.

**INFO-2 — Review-brief drift, three items.** The brief describes the *predecessor's* packet set:
"58 source pins and 38 replay commands, six of which are mutation-ledger runs" and "Five THV1 packets
are cut by this candidate: …-projection-v4 (24 mechanical rows), …-admission-v37, …-certificate-v23,
…-ledger-v5 (18) and …-lineage-ordering-v5 (1)". At P42 it is 58 pins and **39** commands, **seven**
ledger runs, and the packets cut are **projection-v5 (29 rows)**, **admission-v38 (3)** and
**ledger-v6 (21)**; `certificate-v23` and `lineage-ordering-v5` are carried unchanged. The brief also
says the worktree "HEAD must equal P40"; it is at P42, which is correct. None of this changes any
verdict; recording it so the next brief can be re-derived from the packet.

**INFO-3 — Staging directory.** I set `TMPDIR` before every ledger-bearing run, per the campaign
guidance added after opus2 P41 INFO-3, so `_default_workdir()` resolved to
`/tmp/zenodex-opus2-c9c5-tmp/thv1-ledger` and never to the shared `/tmp/thv1-ledger`. During my first
replay another campaign session held `/tmp/zenodex-lean.lock` (observed with `fuser -v`: its `python`
plus two waiting `flock`s), which is why a bare `lake env lean --version` I ran to diagnose INFO-1
blocked for ten minutes with ~0 s of CPU. No result here depends on shared state: every ledger row I
spot-checked was re-executed in my own `git archive` extracts, outside any shared staging.

---

## 5. Worktree hygiene

`/tmp/zenodex-formal-core-opus2-c9c5` is at `d33598ec4c79274c5a325d5cc655074a951d8847` with
`git status --short` empty at the end of the review. Nothing was committed to any branch. All mutation
testing ran in `/tmp/opus2c9c5-mut` and `/tmp/opus2c9c5-full` (`git archive` extracts), both deleted,
as was `/tmp/zenodex-opus2-c9c5-cargo`. I did not read or write the author's worktree
(`/tmp/zenodex-formal-core-fable-20260901`), the canonical checkout, the other reviewer's worktree
(`/tmp/zenodex-formal-core-opus-c9c5`), or the author's scratchpad.

---

## 6. Bottom line

**REVISE (advisory). Grade B−.** Authority stays NONE, `formal_core_complete` stays false, the claim
ceiling did not move, and nothing consumes the projection.

The engineering in this candidate is the strongest of the recent run, and I verified it by execution
rather than by reading. Both P41 P1s are genuinely repaired in the two pinned nonclaims that carried
them. The answer to the deepest finding of the previous round is the right kind of answer: rather than
word UNDETERMINED a third time, the candidate made the projection **complete** for one sub-case and
gave the other its own kind, and both of that reviewer's probes now return what they should. The
witnessed-lane carve-out is closed for the caller who passes the witness, with a test that pins both
halves *and* the non-vacuity direction. The checker file that gates every other packet went from zero
mechanical rows to three; the ledger is 108 rows, 0 survived, 0 errors, and the twelve I applied by
hand all kill. All 58 packet pins, 87 THV1 pins, 55 hygiene rows and 953 node ids are byte-exact; the
Rust crate is clean at 536 tests; the campaign base is green over 234 packets; the full 39-command
replay is `EXECUTED_PASS`.

It is B− for the same reason its four predecessors were: the failure mode this candidate exists to
close is present in the artifact under review. The candidate fixed "edited five of six places" — and
then edited four artifact sentences and put a **new false count into three of them**. The artifact now
says the family has three kinds when the module says four and never names the fourth; says six
ledger-gated packets when this commit made it seven; says ten of twelve row cases when this commit made
it thirteen; and carries, as a definition, the UNDETERMINED wording the module abandoned in the same
commit — which a twenty-line probe falsifies a third time, through a capacity filter that applies the
checker's per-key-sum rule one row at a time. The same clause pattern repeats one level down: the
ordering claim was narrowed in three places and left standing in a fourth, four lines from an edit, and
contradicted eight lines later by the same file.

The lesson from P41 was "re-cut every text that carries the claim, and give the claim a test that could
fail". Half of it landed. The other half is the one that would end this: **no count in the artifact
should be typed by hand.** Derive the four numbers in nonclaims 5, 8 and 14 from
`len(ALLOCATION_PROJECTION_REFUSAL_KINDS_V1)`, `len(LEDGER_GATED_PACKETS_V1)` and `len(_ROW_CASES)` at
render time, and add the one test that asserts the rendered nonclaim text agrees with them. That single
change removes three of this round's four P1 sub-findings and every stale count in the module besides.
