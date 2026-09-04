# ZenoDEX Formal Functional Core Closure — C9c-5 (P42) independent review

| field | value |
|---|---|
| subject | S42 `06897ef74d5885dd1a5c7323c8dc111adcdeb7ea` — "fix: repair the claims in the artifact, not only in the code" |
| artifact | P42 `d33598ec4c79274c5a325d5cc655074a951d8847` (artifact-only child; complete diff = `docs/research/ZENODEX_O008_FORMAL_CYCLE_V1.{json,md}`) |
| packet json sha256 | `8cfe379a0011c00f1b6f625fc22873672df7de8bf5ef4032881c1209f226a073` (recomputed; matches the expected value) |
| worktree | `/tmp/zenodex-formal-core-opus-c9c5` (detached at P42; `git status --short` empty at start and at end) |
| reviewer | independent Opus 5 session, fresh context |
| date | 2026-09-03 |
| verdict | **B-** — 2 P1, 7 P2, 6 P3, 3 INFO. ACCEPT is **not** advised. Authority stays NONE; the claim ceiling did not move. |

**Independence caveat.** Fable 5.1 is out of credit until 2026-09-06, so this round's reviewers again share a
model family with the author. I did not read the author's worktree or scratchpad, the other reviewer's
worktree, or the canonical checkout.

---

## 1. Replays

`PY=/home/trevormoc/Downloads/Autonomous Tau DEX/.venv/bin/python`, `PYTHONDONTWRITEBYTECODE=1`,
`TMPDIR=/tmp/zenodex-opus-c9c5-tmp` (created by me), `CARGO_TARGET_DIR=/tmp/zenodex-opus-c9c5-cargo`,
`CARGO_INCREMENTAL=0`. Every Lean-bearing command ran under `flock -w 7200 /tmp/zenodex-lean.lock`.

| command | result |
|---|---|
| `check_o008_formal_cycle_v1.py --root $PWD --packet-commit d33598ec4` | exit 0; `ok true`, `packet_admitted true`, `current_source_drift []`, `errors []`, `proof_replay NOT_RUN` |
| same `--replay --esso-python /usr/bin/python3 --esso-pythonpath …/ESSO` | exit 0; **`EXECUTED_PASS`, 39 runs**, `ok true`, `errors []`, `current_source_drift []`. Result sha256 `a66e7975da0087b7987defb6b906276171e2fb31b059c71590a730240e20cd35`. Lean 4.27.0; `lean_axioms_probe` 25 theorems / certificate 16; both binding gates 6; `transfer_refinement_gate` 40; both ESSO models VERIFIED (z3 4.15.4 + cvc5 1.1.2), gates 20 / 24; `python_allocation_projection_gate` **87** |
| — the **seven** ledger runs inside it | `ledger_projection_rows` **29**, `ledger_tool_rows` **21**, `ledger_checker_rows` **3**, `ledger_admission_rows` **31**, `ledger_ownership_rows` **21**, `ledger_certificate_rows` **2**, `ledger_lineage_rows` **1** = **108 killed, 0 survived, 0 errors**, each exit 0 and each `mechanical == killed` — exactly the declared figures |
| `build_o008_formal_cycle_v1.py … --subject-commit 06897ef74 --created-date 2026-09-03 --check --replay …` | exit 0; `{"drift":[],"mode":"check","ok":true,"subject_commit":"06897ef74…"}`; `git status --short` empty afterwards and the packet still hashes to `8cfe379a…` — it regenerates byte-for-byte from S42 |
| `cargo fmt --all -- --check` (`zk/global_settlement_abi_v1`) | exit 0 |
| `cargo clippy --locked --all-targets -- -D warnings` | exit 0 |
| `cargo test --locked` | exit 0; 54 `test result: ok` summaries, **536 passed**, 0 `FAILED` — the declared figure |
| `tests/core/test_global_accounting_allocation_projection_v1.py` | **87 passed** (`PROJECTION_GATE_EXPECTED_PASSED_V1 = 87`; 79 at P41) |
| `tests/formal/test_lean_asset_transfer_refinement_v1.py` (under the lock) | exit 0; **40 passed** in 20 s |
| `…test_transition_resource_bound_totality_v1.py`, `…abi_v1_resource_bounds.py`, `…abi_v1.py`, `test_check_global_settlement_canonical_manifest_v1.py`, `test_thv1_mutation_ledger_v1.py` | one run, **129 passed** |
| `tests/test_check_o008_formal_cycle_v1.py` | **404 passed** in 303 s (398 at P41; +6) |
| `check_test_hygiene_v1.py --json` | exit 0; `ok true`, `evidence_packet_count` **234**, `changed_path_count 0`, `errors []` |
| `--base-ref e68a9e764 --json` (the receipts head) | exit 0; `ok true`, 234 packets, 0 changed |
| `--base-ref f686e66ca --json` (S42's parent) | exit 0; `ok true`, 234 packets, 11 changed |
| `--base-ref fd409ba6f7d… --json` (campaign base) | exit 0; `ok true`, 234 packets, 419 changed — **the campaign base is green** |

`tests/core/test_zusd_liquidation_partition.py` excluded as instructed.

### Pin and node-id audit — clean

* O-008 packet: **58** `source_pins`, **58** distinct roles, every one byte-exact on `sha256`, `size` and
  `git_blob` (`git hash-object`); 0 mismatches. **39** replay commands, **seven** of them ledger runs.
  `hygiene_selection`: 55 rows over 7 distinct packets, every `packet_sha256` / `packet_git_blob` /
  `pin_sha256` exact.
* The five THV1 packets I audited in full — the three this candidate cuts
  (`…-projection-v5`, `…-o008-formal-cycle-admission-v38`, `…-thv1-mutation-ledger-v6`) plus the two
  carried ledger-gated ones (`…-certificate-v23`, `…-lineage-ordering-v5`): **87** `source_pins` +
  `test_pins`, 0 bad; **703** pinned pytest node ids swept out of the packet text, **0 orphans** against
  `pytest --collect-only` over the twelve files they name.
* `subject_tree 684858f07b4af1414ee0d3ae72f4af41e33bd6a8` = `git rev-parse 06897ef74^{tree}`;
  `subject_parent f686e66ca`; `packet_commit_parent` = S42. P42's complete diff is the two packet files.
  All `created_date` fields are `2026-09-03`.
* Claim ceiling byte-identical to P40/P41: every authority axis `NONE`, `formal_core_complete false`,
  `o008_status OPEN_EXACT_ALL_12_RECONCILIATION_MISSING`, `value_movement_gates_closed 0 / 12`.
  **The ceiling did not move.**
* Ledger arithmetic: `LEDGER_GATED_PACKETS_V1` (`tools/o008_formal_cycle_admission_v1.py:96-102`) names
  **seven** packets at 29+21+3+31+21+2+1 = **108** mechanical rows. I counted 108 in the packet files.
  One `(path, needle, replacement)` triple repeats **across** two gated packets (INFO-2).

### Mutation spot-checks (applied by hand, run, restored; `git status --short` empty after each)

All six of this candidate's new projection rows kill:

| needle | named killer | observed |
|---|---|---|
| `hosting = [domain for domain in domains if capacity.get(domain, 0) >= terminal.amount_atoms]` → `hosting = list(domains)` | `test_only_a_domain_that_can_carry_the_amount_is_a_candidate` | exit 1, 1 failed |
| `if not hosting:` → `… and False:` | `…refuses_every_shape…[one-terminal-over-claiming-its-entitlement]` | exit 1, 1 failed |
| `if len(hosting) != 1:` → `if len(hosting) < 1:` | `…refuses_every_shape…[a-claimant-entitled-in-two-domains]` | exit 1, 1 failed |
| `if len(cells) == 1 and len(controlling) == 1:` → `… and False:` | `test_a_pending_row_over_no_residual_cell_is_declined_not_called_ambiguous` | exit 1, 1 failed |
| `if witness.fragment != fragment:` → `… and False:` | `test_a_witnessed_lane_whose_rows_drift_from_its_receipt_is_refused` | exit 1, 1 failed |
| `if lane_witnesses and len(lane_witnesses) != len(ALL_LANE_IDS_V1):` → `… and False:` | `test_the_witness_slots_are_exactly_typed` | exit 1, 1 failed |

**Reviewer error, recorded.** My first `--replay` returned `EXECUTED_FAIL` on `python_allocation_projection_gate`
because I ran these hand mutations in the worktree while the replay was executing that gate. The replay was
re-run from a clean tree with no concurrent edits; the row above is the clean run. Not a finding against the
candidate.

---

## 2. One verdict per claim

### C1. The three falsified sentences are gone from the artifact — **CLOSED for those three, NOT for what replaced them** (P1-1)

A tree-wide grep for the three phrases (`more than one acceptable certificate`, `Two kinds`,
`two accepted certificates` / `the checker would take either`, `unreachable through the public entry point`)
returns, outside `docs/research/reviews/` and the superseded `projection-v3`/`-v4` packets, only sentences
that **negate** them: `src/core/global_accounting_allocation_projection_v1.py:25,35,120,129`,
`tests/core/…_projection_v1.py:1044`, and `projection-v5` nonclaim 7
(*"NOT two ACCEPTED certificates: … the full checker refuses both (RECEIPT_WITNESS_REQUIRED)"*). O-008
nonclaim 5's "Two kinds" and "acceptable" are gone; `projection-v5` nonclaims 7 and 8 are rewritten and now
match what the tests pin. The three P41 P1 clauses are genuinely closed.

**But the NEW text of the same nonclaim is falsified by a probe, three ways at once.** See P1-1: the
replacement carries the wording opus2 P41 P1-2 falsified, says THREE kinds where the code this commit shipped
has FOUR, and assigns witness-slot refusals to a kind that contains none. This is the campaign's recurring
failure mode in its fifth consecutive round, in the same nonclaim string, edited in the same commit.

### C2. UNDETERMINED is defined by what the STATE does — **NOT CLOSED** (P1-2)

The two probes opus2 P41 P1-2 exhibited are answered:

```
# A: pending row over no residual cell -> PROJECTION_ZERO_RESIDUAL_ROW_UNSUPPORTED, fourth kind "unsupported"
# B: terminal entitled in two domains where one lacks the capacity -> DERIVES, control_domain "spot-pool"
```
Both reproduce here exactly as the candidate claims (`_derive_rows` on opus2's own two states), and both new
guards carry killing mechanical rows.

**The third sub-case the brief asked me to hunt exists, and so does the older shape.** A bounded sweep of 252
states, of which **30 reach `PROJECTION_TERMINAL_DOMAIN_AMBIGUOUS`**, counting row-checked certificates by
exhaustive enumeration of every (domain, principal) assignment:

| row-checked certificates over the state | states |
|---|---|
| **0** (UNRECONCILABLE, not undetermined) | **5** |
| **1** (DETERMINED, not undetermined) | **1** |
| 2 | 20 |
| 4 | 4 |

Six of thirty are misclassified. The root cause is in this candidate's own repair: the capacity filter
(`…projection_v1.py:501-509`) is applied **per terminal**, while the bound the checker enforces —
and which the same function re-enforces forty lines later at `:565-573` — is on the **sum** per
`(asset, claimant, control_domain)`. P1-2.

### C3. The witnessed-lane row-contents carve-out — **CLOSED for the caller, with a kind defect** (P2-1)

`project_allocation_certificate_v1(state, roots, slots)` takes the checker's own twelve-slot tuple, the
comparison at `:706-713` is exact, and both halves of the claim reproduce: with the drifted state and the
witness the projection refuses `PROJECTION_WITNESS_FRAGMENT_DRIFT`; without it the certificate is still
derived and the checker's witness pass refuses it; an undrifted state projects to exactly the witness's
fragment and the **full checker ACCEPTS** the result. Module claim 2's residue paragraph
(`…projection_v1.py:49-59`) states the limit correctly and in the right place, and `projection-v5`'s
`claim_scope` states what is not claimed (that a caller must pass witnesses; that this makes the projection a
verifier). This is the best-stated repair in the candidate.

The defect is where the new code sits in the taxonomy: `PROJECTION_WITNESS_FRAGMENT_DRIFT` is in
`unreconcilable` ("no certificate over this state can be accepted"), and it fires over a state that has one.
P2-1.

### C4. The defensive branch stated as a search — **CLOSED as a claim, one more route exists** (P3-1)

`tests/core/…_projection_v1.py:501-512` now says the branch is unreachable through the entry point on all
twelve lanes, that the zero-atom route P41 found is closed by the capacity filter, and that reaching it via
the builder "is a statement about what has been searched, not a proof of unreachability". I checked the hard
half (entry point, all twelve lanes: still masked) and found a second **row-harness** route the search missed
— a zero-**amount** terminal whose only entitlement domain has no controlled location. Because the docstring
is now framed as a search rather than a claim, this is P3, not P2.

### C5. The ordering claim is narrowed and pinned — **CLOSED in all three places**

`_state_level_refusals_v1`'s docstring (`:323-334`), `_no_certificate_binds` (`tests/core/…:305-310`) and
O-008 nonclaim 5 all now say "in the checker's order **among themselves / among these two**" and name the
witness pass as the code that can run between them.
`test_a_state_level_code_is_not_always_the_checkers_first_code` exhibits the counterexample. Verified.

### C6. The `--lib` killer binds its declared file — **CLOSED for this crate**

`parse_killer_v1` (`tools/thv1_mutation_ledger_v1.py:176-187`) now refuses a `--lib` filter that does not
start with the declared file's own module segment; both the guard and the `if killer.lib:` branch carry
killing rows in `thv1-mutation-ledger-v6`.

**The brief's attack does not land here.** For a row to be accepted the named filter must select a test that
*fails* under the mutation (`mutant_verdict_v1:270-280` returns `KILLED` only on a cargo summary reporting a
failure; a compile break yields `UNVIABLE`, a selection of zero or only-passing tests yields
`SURVIVED`/`UNVIABLE`), so a killer that does not exercise the mutated code cannot produce a `KILLED` verdict.
The residual weaknesses are structural, not exploitable in this tree: the filter is still a **substring**
match, so two same-stem files in different directories would be interchangeable (I checked — this crate has
no duplicate stems), and the form cannot express a nested module at all (`src/economic_command_authentication/
witness.rs` would require a filter starting `witness::` while its test path is
`economic_command_authentication::witness::…`). INFO-1.

### C7. Six guards gained a row; the checker became a seventh gated packet — **CLOSED, with the same shape reintroduced** (P2-2)

`tools/o008_formal_cycle_admission_v1.py` went from **zero** mechanical rows across all packets to three
(`_SHA256_HEX_RE_V1` loop, `_portable_repo_path_v1`, `if identity in seen:`), and the ledger tool's two new
branches carry rows. All 108 rows replay `KILLED`, 0 survived, 0 errors.

**And two guards added by this candidate carry no row** — the exact defect two reviews running:
`if type(lane_witnesses) is not tuple:` (`:604`) and the slot-type check (`:608-610`), while the *parallel*
`if type(lane_binding_roots) is not tuple:` **does** have one and the witness arity check **does** have one.
All three are tested by `test_the_witness_slots_are_exactly_typed`. P2-2.

### C8. All six `REPLAY_LEDGER_*` codes have tests — **CLOSED**

All six codes appear in `tests/test_check_o008_formal_cycle_v1.py`; the suite is 404 passed (398 at P41, +6).

### C9. Housekeeping — **three of four CLOSED**

* Row harness selects the ENABLED lane (`_derive_rows:112-117`, `_state_consistent_candidate:143-149`) —
  **CLOSED**, and the candidate builder was fixed the same way.
* `test_reject_codes_are_closed_and_ordered`'s docstring (`:722-731`) now says the scan is textual over the
  whole file and that per-code reachability is established elsewhere — **CLOSED**.
* Documented check order now names the producer-capability gate as `(2b)` (`:584-590`) — **CLOSED**.
* "Which THV1 packets this checker binds" is now O-008 nonclaim 14 — **PARTIAL**: it says "The **six**
  ledger-gated packets … two of the **six** are not in `hygiene_selection`" in the same commit that made
  them seven. P2-3.

### C10. Items stated as NOT addressed — **confirmed, plus two that were not declared**

opus2 P41 P3-1 (ledger test docstring claims a guard the grader lacks) and P3-6 (the `certificate-v23`
`claim_scope` repeats) are open as stated. **Two more are open and were not declared:** both P41 reviewers'
P2-1 (the false reason given for the evidence standard's scope limit) is untouched in both places — P2-4 —
and the primary's P3-1 (the two-certificate exhibition runs four of the seven checks it names) is untouched —
P3-2.

### C11. The packet — 58 pins, 39 commands, authority NONE, `formal_core_complete false` — **CLOSED**

---

## 3. Findings

### P1-1 — The replacement text of the nonclaim this candidate exists to repair is itself falsified, three ways, in the string the commit edited

**Where.** `tools/o008_formal_cycle_admission_v1.py:558-580` →
`docs/research/ZENODEX_O008_FORMAL_CYCLE_V1.json` nonclaim 5 and `.md:227`.

**(a) It carries the exact wording opus2 P41 P1-2 falsified.** The nonclaim says:

> "UNDETERMINED means **more than one certificate that passes every row, partition and aggregate check
> exists** (a domainless terminal with two entitlement domains, …)"

That is the *replacement* definition C9c-4 shipped and opus2 P41 P1-2 refuted with a twenty-line probe. The
S42 commit message says this candidate "stops wording it: the codes now say the STATE DOES NOT PIN THE ROW
CONTENT", and the module (`…projection_v1.py:126-127`) and the test header (`tests/core/…:13-19`) were both
rewritten accordingly. The pinned artifact was not. It is falsified here by the parenthetical's own first
example — "a domainless terminal with two entitlement domains":

```bash
"$PY" - <<'EOF'
import sys; sys.path.insert(0, ".")
import tests.core.test_global_accounting_allocation_projection_v1 as T
st = T._backed_state((T._terminal("t1", 5), T._terminal("t2", 3)),
    custody=(("pool-a","USD","spot-pool",5), ("pool-b","USD","vault",3)),
    liabilities=(("alice","USD","spot-pool",5), ("alice","USD","vault",3)))
print(T._derive_rows(st))
EOF
#   -> PROJECTION_TERMINAL_DOMAIN_AMBIGUOUS  't2: 2 entitlement domains'
# exhaustive enumeration of all four (domain,principal) assignments:
#   (spot-pool,spot-pool) TERMINAL_BINDING_DRIFT | (spot-pool,vault) ALL SEVEN PASS
#   (vault,spot-pool)     TERMINAL_BINDING_DRIFT | (vault,vault)     TERMINAL_BINDING_DRIFT
#   -> EXACTLY ONE certificate passes every row, partition and aggregate check
```

**(b) It says THREE kinds; this commit shipped FOUR.** `ALLOCATION_PROJECTION_REFUSAL_KINDS_V1`
(`…projection_v1.py:193-223`) has `caller_input`, `undetermined`, **`unsupported`**, `unreconcilable`, and
the enum docstring one line 118 says "**FOUR** kinds of refusal share this family". The nonclaim enumerates
three and never mentions the `unsupported` kind or `PROJECTION_ZERO_RESIDUAL_ROW_UNSUPPORTED`. Grepping both
packet files for `UNSUPPORTED`, `FOUR kinds` or `fourth kind` returns **nothing** — the fourth kind and the
two new codes this candidate added exist nowhere in the durable artifact. The previous cut's error was
"Two kinds" when there were three; this cut says "THREE" when there are four.

**(c) Its CALLER INPUT sentence assigns witness slots to a kind that has none.** The nonclaim says
"CALLER INPUT means the supplied binding roots **or witness slots** do not match the enabled receipt-backed
lanes". `caller_input` contains exactly `PROJECTION_BINDING_ROOT_UNEXPECTED` and
`PROJECTION_BINDING_ROOT_MISSING`; a witness-slot mismatch is `PROJECTION_WITNESS_FRAGMENT_DRIFT`, which the
same commit placed in `unreconcilable`, and a malformed slot is a `TypeError`, not a code.

**Why this is the P1.** The candidate's stated purpose is "repair the claims in the artifact, not only in the
code", and its own commit message says a grep for the three phrases "now returns only the sentence that
negates them" — which is true, and is not the same as the artifact being right. This is the fifth consecutive
round in which the repair lands in the code and the durable, sha256-pinned nonclaim states something the
code contradicts, and the third consecutive round in which it is **this** nonclaim, edited in **this**
commit. Nothing in the checker or the 404-test suite compares the nonclaim's kind count or definition to
`ALLOCATION_PROJECTION_REFUSAL_KINDS_V1`, which is why it drifts every round.

**Minimal fix.** In `tools/o008_formal_cycle_admission_v1.py:560-566`: "THREE" → "FOUR"; drop "or witness
slots" from the CALLER INPUT sentence; replace the UNDETERMINED definition with the module's own —
"UNDETERMINED means the state does not pin the row content"; add one sentence for UNSUPPORTED naming
`PROJECTION_ZERO_RESIDUAL_ROW_UNSUPPORTED`; and add `PROJECTION_WITNESS_FRAGMENT_DRIFT` to the UNRECONCILABLE
list. Then **add a test** that asserts the nonclaim's kind count equals `len(ALLOCATION_PROJECTION_REFUSAL_KINDS_V1)`
and that every kind name appears in it, so the sixth round cannot repeat this. Re-cut the packet.

### P1-2 — The capacity filter is per-terminal while the bound is per-key aggregate, so `PROJECTION_TERMINAL_DOMAIN_AMBIGUOUS` still fires over determined and over unreconcilable states

**Where.** `src/core/global_accounting_allocation_projection_v1.py:500-513` (the filter added for
opus2 P41 P1-2) against `:552-573` (the aggregate bound the same function enforces) and
`_check_terminal_totals` (`…certificate_v1.py:957-975`), which bounds the **sum** of a fragment's terminal
rows per `(asset, claimant, control_domain)`.

The filter asks only whether one domain's entitlement covers **this** row. It never asks whether the domains
left over can host the **other** OPEN terminals, so it resolves each row in isolation and reports an
ambiguity whenever more than one domain survives — including when the rest of the state forces the answer.

**Reproduction (determined).** The probe in P1-1(a): one certificate passes, the projection says ambiguous.

**Reproduction (unreconcilable).** Three OPEN terminals of 10 against entitlements of 10 + 10:

```bash
# custody (pool-a,USD,spot-pool,10)+(pool-b,USD,vault,10); liabilities alice 10 in each; t1=t2=t3=10
#   _derive_rows -> PROJECTION_TERMINAL_DOMAIN_AMBIGUOUS  't1: 2 entitlement domains'
#   all 8 domain assignments -> TERMINAL_BINDING_DRIFT ; ZERO row-checked certificates
```

**Bounded quantification.** Over 252 swept states, 30 reach `PROJECTION_TERMINAL_DOMAIN_AMBIGUOUS`; counting
row-checked certificates by exhaustive assignment gives **5 states with zero** and **1 state with exactly
one** — 6 of 30 misclassified. The zero-certificate cases are the shape primary P39 P1-1 and opus2 P40 P1-1
were both P1s for; the one-certificate case is the shape opus2 P41 P1-2 was a P1 for and is the third
sub-case the brief asked me to hunt.

The enum docstring hedges this in advance (`:132-134`: *"A future counterexample of the same shape would be
a defect in this classification, not in the refusal"*), which is honest and correctly says nothing unsound is
derived — but the sentence immediately above it makes the positive claim *"what is left under these two codes
is a state that genuinely leaves the content open"*, and that is what the sweep falsifies.

**Minimal fix.** Two options, both small. (i) Refuse honestly: when more than one domain survives the
capacity filter, first test whether any complete assignment of **all** OPEN terminals for that
`(asset, claimant)` satisfies the per-key sums; if none does, raise `PROJECTION_TERMINAL_EXCEEDS_ENTITLEMENT`
(unreconcilable), and if exactly one does, derive it. The search is over `|domains|^|terminals|` for one
claimant and is bounded by the fixture sizes the module already handles. (ii) If that is out of scope for
this cut, delete the positive sentence at `:130-132` and state the residue: these codes mean the module could
not pin the content, which does not imply the state leaves it open — with the two probes above as
`_ROW_CASES` entries so the sentence has a test.

### P2-1 — `PROJECTION_WITNESS_FRAGMENT_DRIFT` is in the `unreconcilable` kind and fires over states that have an accepted certificate

**Where.** `…projection_v1.py:222` (kind membership), `:153-157` (the enum docstring's description) and
`:696-714` (the check).

The kinds table's own comment (`:186-189`) says membership "is a claim about WHY a code is raised", and
`unreconcilable` is defined as "no certificate over this state can be accepted". The check compares the
derived fragment against **whatever object the caller handed it** — it never verifies that the slot holds the
witness that lane root's receipt actually admitted — so a caller who passes a foreign witness gets an
unreconcilable code for a perfectly reconcilable state:

```bash
"$PY" - <<'EOF'
import sys; sys.path.insert(0, ".")
import tests.core.test_global_accounting_allocation_projection_v1 as T
from src.core import global_accounting_allocation_certificate_v1 as cert
from src.core.global_accounting_allocation_projection_v1 import project_allocation_certificate_v1
from src.core.global_settlement_types_v1 import LaneIdV1
w, state, _c, slots = T._witnessed(with_rows=True)
roots = ((LaneIdV1.ASSET_TRANSFER, w.fragment.binding_root),)
good = project_allocation_certificate_v1(state, roots, slots)
print(cert.check_global_accounting_allocation_certificate_v1(good, state, slots))   # -> ACCEPTED
other, *_ = T._witnessed(authority_epoch=9, with_rows=True)
print(project_allocation_certificate_v1(state, roots, (other,) + slots[1:]).code)
EOF
#   -> the certificate for THIS state is ACCEPTED by the full checker
#   -> PROJECTION_WITNESS_FRAGMENT_DRIFT   ("ASSET_TRANSFER differs from its minted witness")
```

The enum docstring's phrasing — "raised when the fragment the state implies differs from the one **the lane
root's receipt admitted**" — describes a binding the code does not check.

**Minimal fix.** Move the code to `caller_input` (it is a statement about the caller's argument, exactly like
the two binding-root codes) and change the docstring to "differs from the one the supplied witness carries";
or keep it in `unreconcilable` and add the binding check that would make the claim true.

### P2-2 — Two witness type-boundary guards added by this candidate carry no mechanical row, while the parallel binding-roots guard does

**Where.** `…projection_v1.py:604` (`if type(lane_witnesses) is not tuple:`) and `:608-610` (the per-slot
exact-type check). `projection-v5` declares 29 rows over this module, including
`if type(lane_binding_roots) is not tuple:` and `if lane_witnesses and len(lane_witnesses) != len(ALL_LANE_IDS_V1):`
— the two neighbours of these guards — but none over these two.

```bash
"$PY" -c "
import json
rows=[m['mutant'] for m in json.load(open('tests/evidence/test_hygiene/THV1-20260903-global-accounting-allocation-projection-v5.json'))['mutations'] if 'mutant' in m]
n=[' '.join(r['needle_lines']) for r in rows]
print([x for x in n if 'type(lane' in x])"
#   -> ['    if type(lane_binding_roots) is not tuple:']      (the witness one is absent)
```

All three are exercised by `test_the_witness_slots_are_exactly_typed`, so this is a gap in the *declared
mechanical evidence*, not in coverage — which is precisely how both P40 reviews and P41 P2-5 described the
same defect on the previous surfaces. **Minimal fix:** two rows in `projection-v5`, gate 29 → 31.

### P2-3 — O-008 nonclaim 14, written this round to answer P40 P2-4, says "six ledger-gated packets" in the commit that made them seven

**Where.** `tools/o008_formal_cycle_admission_v1.py:602-610` → `…FORMAL_CYCLE_V1.md:236`, nonclaim 14:
*"The **six** ledger-gated packets are named by their replay commands … and **two of the six** are not in
`hygiene_selection`."*

`LEDGER_GATED_PACKETS_V1` (`:96-102`) has seven entries, the packet declares **seven** ledger replay commands
(39 total, not the 38 of P41), and the commit message says "the checker file becomes a **seventh**
ledger-gated packet". The substantive claim in the sentence is right — I confirmed exactly two of the seven
(`…certificate-v23`, `…lineage-ordering-v5`) are absent from `hygiene_selection`'s seven packets — only the
count is stale. **Minimal fix:** "six" → "seven", "two of the six" → "two of the seven".

### P2-4 — Both P41 reviewers' P2-1 is untouched and undeclared: the reason given for the evidence standard's scope limit is false, in both places

**Where.** `tests/core/test_global_accounting_allocation_projection_v1.py:135-138`
(*"it **builds no terminal binding rows**, so for a state with an OPEN terminal obligation it is one candidate
among more than one"*) and `:1025-1028` (*"the **builder omits terminal rows**, so other candidates exist"*).

The builder has built terminal rows since C9c-4 (`:168-213`):

```bash
"$PY" -c "
import sys; sys.path.insert(0,'.')
import tests.core.test_global_accounting_allocation_projection_v1 as T
st = T._backed_state((T._terminal('terminal-1', 99),))
print(len(T._state_consistent_candidate(st).ordered_lane_fragments[0].terminal_bindings))"
#   -> 1
```

The *limit* is real — the builder picks the first domain and first principal in canonical order (`:189`,
`:195`) — but the stated reason is false, and it was found independently by both P41 reviewers (primary P2-1,
opus2 P2-1). It is not among the items the candidate declares as not addressed. **Minimal fix:** replace both
sentences with "it chooses the first control domain and controlling principal in canonical order".

### P2-5 — `projection-v5` nonclaim 8, rewritten this round to repair a P1, states the wrong row-case count

**Where.** `tests/evidence/test_hygiene/THV1-20260903-global-accounting-allocation-projection-v5.json:585`,
and the same numbers in `tests/core/…:92` and `:1088-1091`: *"**TEN of the twelve** row cases are masked …
and **TWO** reach their own code"*.

`_ROW_CASES` has **thirteen** entries since this candidate added the zero-atom fixture:

```bash
"$PY" -c "
import sys; sys.path.insert(0,'.')
import tests.core.test_global_accounting_allocation_projection_v1 as T
from src.core.global_accounting_allocation_projection_v1 import AllocationProjectionRejectCodeV1 as C
m=o=0
for label,tab,ter,code,_ in T._ROW_CASES:
    s=T._backed_state(tuple(T._terminal(t[0],t[1],**(t[2] if len(t)>2 else {})) for t in ter), **tab)
    p=T.project_allocation_certificate_v1(s, T._root_of(s))
    m += p.code is C.PROJECTION_ROWS_BEYOND_PRODUCER; o += p.code is not C.PROJECTION_ROWS_BEYOND_PRODUCER
print(len(T._ROW_CASES), m, o)"
#   -> 13 11 2      (eleven masked, two reach their own code)
```

The *partition* the nonclaim points at (`test_which_row_cases_the_entry_point_reaches_is_pinned`) is correct
and parametrised over all thirteen; only the prose count is stale, in the sentence rewritten to close
Opus P41 P1-2. **Minimal fix:** ten → eleven, twelve → thirteen, in all three places.

---

### P2-6 — The narrowed ordering claim landed in three places and the unnarrowed one is still in the fourth, 177 lines from the sentence that contradicts it

**Where.** `src/core/global_accounting_allocation_projection_v1.py:150-153`, the enum docstring:

> "From the lane configuration, which no arrangement of rows can repair, evaluated before the rows and
> **in the checker's own order so the projection names the code the checker would raise first**"

That is verbatim the sentence Opus P41 P2-6 falsified. The commit message says the claim "was in a docstring,
a test helper AND the pinned nonclaim. All three now say 'in the checker's order among these two'" — and all
three do. This is the fourth. The same file says the opposite at `:329-334`
(*'NOT "the code the checker would raise first" in general: `RECEIPT_WITNESS_REQUIRED` runs between them'*),
and the candidate's own `test_a_state_level_code_is_not_always_the_checkers_first_code` exhibits the
counterexample.

```bash
grep -rn "checker would raise first" --include=*.py . | grep -v docs/research/reviews
#   -> src/core/global_accounting_allocation_projection_v1.py:152   (the claim)
#   -> src/core/global_accounting_allocation_projection_v1.py:329   (the denial)
```

**Minimal fix.** At `:151-153`, "in the checker's own order **among these two**, so among them the projection
names the code the checker raises first".

### P2-7 — The module summary says the projection "takes no witness" in the commit whose headline change is that it does

**Where.** `src/core/global_accounting_allocation_projection_v1.py:7`: *"It is pure, **takes no witness**, and
never mutates its inputs."* — against the signature the same commit added at `:576-580`:

```
project_allocation_certificate_v1(state, lane_binding_roots=(), lane_witnesses=())
```

and against the same docstring's own claim 2 at `:50-59` (*"Given `lane_witnesses`, the same slots the checker
requires, it refuses with `..._WITNESS_FRAGMENT_DRIFT` instead"*). "Verifies no receipt" is already stated
separately at `:65`, so this sentence is not a loose paraphrase of that — it is the summary line a reader
meets first, and it is now false. **Minimal fix:** "It is pure, verifies no receipt, and never mutates its
inputs; a caller may supply the checker's witness slots and the projection compares them."


---

## 4. P3 findings, INFO, and a verdict on every P41 finding

**P3-1 — a second row-harness route to `PROJECTION_TERMINAL_WITHOUT_BACKING` the search missed.** The
docstring (`tests/core/…:505-512`) says the zero-atom route is closed by the capacity filter and that "every
route this suite can find now refuses earlier". A zero-**amount** OPEN terminal reaches it, because
`capacity.get(domain, 0) >= 0` admits a domain entitled 0:

```bash
"$PY" -c "
import sys; sys.path.insert(0,'.')
import tests.core.test_global_accounting_allocation_projection_v1 as T
st = T._backed_state((T._terminal('terminal-1', 0),), custody=(('pool-a','USD','spot-pool',10),),
    liabilities=(('bob','USD','spot-pool',10), ('alice','USD','vault',0)))
print(T._derive_rows(st))"
#   -> PROJECTION_TERMINAL_WITHOUT_BACKING  'terminal-1: no controlled location in vault'
```
The hard half of the claim survives: through the entry point this state is still masked by
`PROJECTION_ROWS_BEYOND_PRODUCER`, and I re-checked all twelve lanes. Because the docstring is explicitly
framed as "a statement about what has been searched, not a proof", this extends the search rather than
falsifying a claim — P3, not P2. **Fix:** add it as a fourteenth `_ROW_CASES` entry so the code has a case
in the table again (it currently has none: the P41 fixture now reports `TERMINAL_EXCEEDS_ENTITLEMENT`).

**P3-2 — the two-certificate exhibition still runs four of the seven checks its own sentence names**
(primary P41 P3-1, carried, undeclared). `tests/core/…:1058-1064` runs `_check_exactly_once`,
`_check_entitlement_rows`, `_check_external_obligations`, `_check_lane_aggregates`; the claim in the module,
the tests and `projection-v5` nonclaim 7 is "passes every row, **partition** and aggregate check", and
`_check_reserve_rows`, `_check_terminal_bindings` and `_check_terminal_totals` are not run. The claim is
true — I ran all seven on both candidates — so this is a test under-checking its own sentence. One line.

**P3-3 — `_no_certificate_reconciles` still omits `_check_reserve_rows`** (carried from P41, undeclared).
`tests/core/…:275-293` runs six of the seven passes; `CHECK_ORDER_V1` places `_check_reserve_rows` between
the entitlement and external passes. The omission is conservative (it can only return `"ACCEPTED"` and fail
the test), but the code the helper returns is still not necessarily the code the full checker returns, and
its docstring does not say so. The new `test_a_pending_row_over_no_residual_cell_…` **does** run the reserve
check, which makes the omission in the shared helper look like an oversight rather than a decision.

**P3-4 — stale labels left by this round's changes.** `# The three kinds the family docstring names`
(`…projection_v1.py:190`); the test function name `test_the_three_refusal_kinds_partition_the_family`
(`tests/core/…:700`) whose body asserts the **four**-key set; that test's docstring "omitted three of its
thirteen codes" against a family of eighteen; the module docstring's own header `"(C9c-4)"` (`:1`) on the
C9c-5 module; and `"what three reviews have already falsified"` (`:14`) after four. Renaming the test and
five words is the whole fix.

**P3-5 — opus2 P41 P3-1, open as declared.** `tests/test_check_o008_formal_cycle_v1.py:1066-1067` still says
"the grader now refuses a mutation applied to a file this packet does not bind", which `_grade_ledger`
deliberately does not do and says so in its own docstring.

**P3-6 — opus2 P41 P3-6, open as declared and unchanged.** `THV1-20260901-global-accounting-allocation-certificate-v23`'s
`claim_scope` still repeats three sentences verbatim through the predecessor concatenation
(`"Earlier: v20 re-pin (C9c-1)…"`, `"Earlier: Candidate C8''' (Opus P19 repairs)…"`,
`"The asset-lane projection joins the pinned surface."`). Note that `projection-v5` dropped the concatenation
entirely, which is the better answer; `certificate-v23` was not re-cut this round.

### INFO

**INFO-1 — the `--lib` killer form is bound by module segment, not by file.** `Path(path).stem` plus a
substring filter means two same-stem files in different directories would produce interchangeable commands
(this crate has none — I checked `find src -name '*.rs' -printf '%f\n' | sort | uniq -d`), and a nested
module cannot use the form at all: `src/economic_command_authentication/witness.rs` would need a filter
beginning `witness::` while its tests are named `economic_command_authentication::witness::…`. Neither is
exploitable today; both are worth a sentence in the packet or a `--lib`-form docstring.

**INFO-2 — "every one distinct" is true per packet, not across the seven.** One
`(path, needle, replacement)` triple —
`src/core/asset_transfer_types_v1.py`, `if type(self.module_journal) is not LaneModuleTransitionJournalV1…` —
appears in both `…receipt-admission-mechanical-v3` and `…exact-ownership-mechanical-v3`, with different
killers. `_grade_ledger`'s distinctness rule is per replay run, so this is admitted by design; the commit
message's "108 rows over seven packets, every one distinct" reads as a global claim and is a 107/108 one.

**INFO-3 — P41 INFO-1 (ledger replay concurrency) is unrepaired and undisclosed.** All seven ledger commands
still declare `cwd "."`, `env_names []` and no `--workdir`, so the staging root is `$TMPDIR/thv1-ledger` and
falls back to a shared `/tmp/thv1-ledger`; `run_ledger_v1` `rmtree`s `<root>/<packet>` at start. It is
fail-closed (a vanished tree yields `UNVIABLE`/errors, never a false `KILLED`), and two reviewers replayed
the same packet names concurrently this round. I isolated with my own `TMPDIR`. **Suggested:** add
`--workdir` to the seven declared commands, or name `TMPDIR` in `env_names`.

### Verdict on every P41 finding

| P41 finding | verdict |
|---|---|
| Opus P1 — the three false sentences survive in the packets | **CLOSED for those sentences**; the replacement text carries three new falsehoods (P1-1) |
| Opus P2-1 / opus2 P2-1 — the scope limit's reason is false | **OPEN**, untouched and undeclared (P2-4) |
| Opus P2-2 — `TERMINAL_WITHOUT_BACKING` reachable through the harness | **CLOSED for that route**, claim restated as a search; a second route exists (P3-1) |
| Opus P2-3 — a determined state reported as an ambiguity | **CLOSED for that sub-case** (`..._ZERO_RESIDUAL_ROW_UNSUPPORTED`, fourth kind); a third sub-case exists (P1-2) |
| Opus P2-4 / opus2 P2-2 — the `--lib` path is decorative | **CLOSED** (module-segment binding, two killing rows) |
| Opus P2-5 — guards with no mechanical row | **CLOSED** for the three named; two new ones (P2-2) |
| Opus P2-6 — the ordering claim | **CLOSED in three places, open in a fourth** (P2-6) |
| opus2 P1-2 — the replacement UNDETERMINED definition is false | **CLOSED in the code**, both probes now derive or get their own code; **open in the artifact** (P1-1a) and a third sub-case exists (P1-2) |
| opus2 P2-5 — three untested `REPLAY_LEDGER_*` codes | **CLOSED**, all six have tests |
| opus2 P2-7 (declared open at P41) — the witnessed-lane carve-out | **CLOSED for the caller who passes the witness**, with a kind defect (P2-1) |
| Opus P3-2 / opus2 P3-3 — gated packets unpinned by the packet that claims the gate | **CLOSED as a disclosure**, with the wrong count (P2-3) |
| Opus P3-4 — the harness reads `lane_roots[0]` | **CLOSED** |
| Opus P3-6c / opus2 P3-6 — the reject-code scan's docstring | **CLOSED** |
| opus2 P3-4 — the documented check order omits the producer gate | **CLOSED** (`(2b)`) |
| opus2 P3-1 — the ledger test docstring | **OPEN as declared** (P3-5) |
| opus2 P3-6 — `certificate-v23` `claim_scope` repeats | **OPEN as declared** (P3-6) |
| Opus P3-1 — the exhibition runs 4 of 7 checks | **OPEN**, undeclared (P3-2) |
| Opus INFO-1 — ledger concurrency | **OPEN**, undisclosed (INFO-3) |

---

## 5. Reproduction scripts

All probes ran inside the worktree with `PYTHONDONTWRITEBYTECODE=1` and `TMPDIR` set to a directory I
created. The only edits were the six mutation spot-checks, each restored from a byte copy taken first;
`git status --short` is empty afterwards and the checker reports `current_source_drift []`.

```python
# P1-2 / C2: how many row-checked certificates a TERMINAL_DOMAIN_AMBIGUOUS state actually has.
import sys, itertools; sys.path.insert(0, ".")
from dataclasses import replace
import tests.core.test_global_accounting_allocation_projection_v1 as T
from src.core import global_accounting_allocation_certificate_v1 as cert
from src.core.global_accounting_allocation_projection_v1 import AllocationProjectionRejectCodeV1 as C
from tools import render_global_accounting_allocation_certificate_v1_golden as renderer

CHECKS = ((cert._check_exactly_once, 1), (cert._check_entitlement_rows, 2), (cert._check_reserve_rows, 2),
          (cert._check_external_obligations, 2), (cert._check_terminal_bindings, 2),
          (cert._check_lane_aggregates, 2), (cert._check_terminal_totals, 1))

def count_certs(st):
    """Every (domain, principal) assignment of the OPEN terminal rows; count the passers."""
    base = cert.build_registered_empty_certificate_v1(st)
    slot, lane = [(i, r) for i, r in enumerate(st.lane_roots) if r.enabled][0]
    controlled = tuple(cert.ControlledLocationRowV1(r.asset, r.owner, r.custody_domain, r.amount_atoms)
                       for r in st.custody)
    ents = tuple(cert.ClaimantEntitlementRowV1(r.asset, r.owner, r.custody_domain, r.amount_atoms)
                 for r in st.liabilities)
    opens = [t for t in st.terminal_obligations if t.status.value == "OPEN"]
    cand = {t.obligation_id: [(l.control_domain, l.controlling_principal)
                              for l in controlled if l.asset == t.asset] for t in opens}
    if any(not v for v in cand.values()):
        return 0
    n = 0
    for combo in itertools.product(*[cand[t.obligation_id] for t in opens]):
        rows = tuple(cert.TerminalBindingRowV1(
            obligation_id=t.obligation_id, claimant=t.claimant, asset=t.asset,
            amount_atoms=t.amount_atoms, control_domain=d, controlling_principal=p,
            lane_id=t.lane_id, lane_state_root=lane.state_root) for t, (d, p) in zip(opens, combo))
        frag = replace(base.ordered_lane_fragments[slot], enabled=lane.enabled,
            lane_state_root=lane.state_root, binding_root=lane.state_root,
            producer_kind=cert.LANE_ALLOCATION_PRODUCER_REGISTRY_V1[lane.lane_id][0],
            controlled_locations=controlled, claimant_entitlements=ents,
            terminal_bindings=tuple(sorted(rows, key=lambda r: r.obligation_id)))
        c = renderer._certificate_with_fragments(base, tuple(
            frag if i == slot else f for i, f in enumerate(base.ordered_lane_fragments)))
        try:
            for fn, ar in CHECKS:
                fn(c) if ar == 1 else fn(c, st)
            n += 1
        except Exception:
            pass
    return n

# exactly one certificate, reported as an ambiguity
det = T._backed_state((T._terminal("t1", 5), T._terminal("t2", 3)),
    custody=(("pool-a", "USD", "spot-pool", 5), ("pool-b", "USD", "vault", 3)),
    liabilities=(("alice", "USD", "spot-pool", 5), ("alice", "USD", "vault", 3)))
print(T._derive_rows(det), count_certs(det))          # -> (…TERMINAL_DOMAIN_AMBIGUOUS, 't2: 2 …'), 1

# zero certificates, reported as an ambiguity
zero = T._backed_state((T._terminal("t1", 10), T._terminal("t2", 10), T._terminal("t3", 10)),
    custody=(("pool-a", "USD", "spot-pool", 10), ("pool-b", "USD", "vault", 10)),
    liabilities=(("alice", "USD", "spot-pool", 10), ("alice", "USD", "vault", 10)))
print(T._derive_rows(zero), count_certs(zero))        # -> (…TERMINAL_DOMAIN_AMBIGUOUS, 't1: 2 …'), 0
```

The full sweep (6 custody tables × 6 liability tables × 7 terminal sets = 252 states) is the same loop with
`buckets[count_certs(st)] += 1` over every state whose `_derive_rows` verdict is
`PROJECTION_TERMINAL_DOMAIN_AMBIGUOUS`; it yields `{0: 5, 1: 1, 2: 20, 4: 4}`.

```python
# Bounded refutation, recorded as a positive result: over 192 entry-point states
# (4 custody × 6 liabilities × 2 outboxes × 4 terminal sets) the projection derived
# 5 certificates and NONE failed any of the seven row/partition/aggregate checks or
# _check_derived_roots. Claim 2 survives this search through the public entry point.
```

---

## 6. Worktree hygiene

`/tmp/zenodex-formal-core-opus-c9c5` is at P42 with `git status --short` empty at the end, and the checker
reports `current_source_drift []`. Every temporary edit (six projection mutants) was restored from a byte
copy taken before the edit. The symlinks (`external/ESSO`, `external/mathlib4`, and the nine packages under
`lean-mathlib/.lake/packages` including `mathlib`) were already in place and are gitignored.
`/tmp/zenodex-opus-c9c5-cargo` was deleted at the end. The author's worktree, the canonical checkout, the
other reviewer's worktree and the author's scratchpad were not read or written. Every Lean-bearing command
ran under `flock -w 7200 /tmp/zenodex-lean.lock`.

---

## 7. Bottom line

At the code level this is the strongest candidate of the C9c series, and I verified each repair
independently rather than by reading the commit message. The witnessed-lane carve-out that the previous
candidate declared open is genuinely closed for the caller who passes the witness, and closed the right way:
the entry point takes the checker's own twelve slots, the comparison is exact, one test pins both halves,
and I confirmed the undrifted state projects to a certificate the **full checker accepts**. Both of opus2
P41 P1-2's probes now derive or get their own code instead of being re-worded a third time — the fourth
kind, `unsupported`, is a real distinction and the right one to draw. The checker file that gates every
other packet went from zero mechanical rows to three, the ledger went 97 → 108 rows over seven packets, and
every one of the six new projection rows kills by hand. All six `REPLAY_LEDGER_*` codes have tests. The
`--lib` killer form now binds its declared module, and the brief's attack on it does not land: a `KILLED`
verdict still requires a test that actually fails. Pins (58 + 87), 703 node ids with zero orphans,
`subject_tree`, the claim ceiling, the 108 ledger kills and all 39 replay commands reproduce here exactly.

What stops this from being an ACCEPT is that the candidate whose stated purpose is *"repair the claims in
the artifact, not only in the code"* introduced six fresh claim defects while closing three, and two of them
are in the artifact. O-008 nonclaim 5 — the string this commit edited, for the third round running — now
carries the exact UNDETERMINED wording the second P41 reviewer falsified, says THREE kinds where the same
commit shipped four, and puts witness slots in a kind that has none; the fourth kind and its two new codes
appear nowhere in either packet. Nonclaim 14, written this round to answer P40 P2-4, says "six ledger-gated
packets" in the commit that made them seven. Nonclaim 8, rewritten this round to close a P1, says ten of
twelve row cases where there are eleven of thirteen. The ordering claim was narrowed in the three places the
last review named and left standing in a fourth, 177 lines from the sentence that denies it. The module
summary says the projection "takes no witness". And the one P2 that **both** P41 reviewers raised
independently — the false reason given for the evidence standard's scope limit — is untouched and is not
among the items the candidate declares as not addressed.

Below that sits one real design defect, and it is inside this round's headline repair: the capacity filter
resolves each terminal against its own domain's entitlement while the bound the checker enforces is the
**sum** per key, so `PROJECTION_TERMINAL_DOMAIN_AMBIGUOUS` still fires over states whose content is
determined (1 in 30 swept) and over states with no certificate at all (5 in 30). That is the third
consecutive round in which an `..._AMBIGUOUS` code is shown to mean something other than what the taxonomy
says, and the second in which the counterexample lives inside the fix for the previous one. Nothing unsound
is derived in any of these cases — a bounded sweep of 192 entry-point states produced five certificates and
no check failure — so the refusals stay conservative and the residual risk is classification, not soundness.

The P1s are one afternoon of work: a rewritten nonclaim with a test that pins its kind count against
`ALLOCATION_PROJECTION_REFUSAL_KINDS_V1`, and either a per-key assignment search or an honest narrowing of
the sentence at `…projection_v1.py:130-136`. Nothing in the design is wrong.

**Grade B-. Authority NONE. `formal_core_complete` false. The claim ceiling must not move on this candidate.**
