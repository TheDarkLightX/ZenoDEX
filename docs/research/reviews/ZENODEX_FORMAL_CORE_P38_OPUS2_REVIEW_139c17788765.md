# ZenoDEX Formal Functional Core Closure — Second Independent Review of C9c-1 (P38)

| field | value |
|---|---|
| subject | S38 = `2e18422919c8cd896c67553645778b46e38e34e5` (range reviewed: `1f5b1cb81..2e1842291`, five commits) |
| artifact | P38 = `139c1778876564ff0ec22d13a18e0b7669ee5601` (packet sha256 `61eeab4d…c220fa`) |
| worktree | `/tmp/zenodex-formal-core-opus2-c9c1` (detached, `git status --short` empty, HEAD = P38) |
| reviewer | fresh-context **Opus 5**, second reviewer |
| date | 2026-09-03 |
| verdict | **B-** — 2 P1, 3 P2, 5 P3, 5 INFO |

**INDEPENDENCE CAVEAT.** The campaign's second reviewer is normally a fresh-context Fable 5.1
session; Fable is out of usage credits until 2026-09-06, so this second review is a fresh-context
**Opus 5** session running in parallel with the primary Opus 5 reviewer (worktree
`/tmp/zenodex-formal-core-opus-c9c1`). I share a model family with the primary reviewer and
therefore **correlate with it**. I share no transcript, worktree, or notes with it or with the
author; I did not read its worktree or report, did not coordinate with it, and did not read the
author's scratchpad. Where a finding below coincides with one the primary reviewer may also have
reached, that is convergence, not confirmation.

---

## 1. Replays (all executed in this worktree; every Lean-bearing command under `flock -w 7200 /tmp/zenodex-lean.lock`)

| command | result |
|---|---|
| `check_o008_formal_cycle_v1.py --root $PWD --packet-commit 139c1778…` | exit 0; `ok true`, `packet_admitted true`, `current_source_drift []`, `proof_replay.status NOT_RUN` |
| same `--replay --esso-python /usr/bin/python3 --esso-pythonpath …/ESSO` | exit 0; `EXECUTED_PASS`, **32 runs** (not 31 — see INFO-1); `python_allocation_projection_gate` `passed:40` |
| `build_o008_formal_cycle_v1.py … --check --replay --output-json/-md` | not re-run separately: the checker replay above already executes the same 32 commands against the committed artifact and reports zero drift; the builder's `--check` is the same comparison in the other direction |
| `zk/global_settlement_abi_v1`: `cargo fmt --all -- --check` | exit 0 |
| `cargo clippy --locked --all-targets -- -D warnings` | exit 0 |
| `cargo test --locked` | exit 0 (all targets green incl. 3 compile-fail doctests) |
| six Python suites in one run | **542 passed** in 290s; per-file collected: totality 10, abi resource bounds 17, abi 75, `test_check_o008_formal_cycle_v1.py` **392**, canonical manifest 8, projection **40** |
| `tests/formal/test_lean_asset_transfer_refinement_v1.py` | 40 passed |
| `tests/formal/test_lean_global_claimant_custody_relation_v1.py` (lean_binding_gate) | 6 passed |
| `tests/formal/test_lean_global_accounting_allocation_certificate_v1.py` | 6 passed |
| `check_test_hygiene_v1.py --json` | exit 0; packets 206; `mutation_rows {mechanical:92, mechanical_current:90, narrative:2, legacy:5043}` |
| `--base-ref 8942d6bd2 --json` | exit 0; critical 5 |
| `--base-ref 42ccb6624 --json` | exit 0; critical 38 |
| `--base-ref fd409ba6f7da8f0ec3e0220a04b7406d69a8cb85 --json` | exit 0; critical 68 |
| `thv1_mutation_ledger_v1.py --packet THV1-20260903-global-accounting-allocation-projection-v1 --rev 139c1778…` | exit 0; `mechanical 9 / killed 9 / survived 0 / errors 0` |
| `thv1_mutation_ledger_v1.py --packet THV1-20260903-thv1-mutation-ledger-v2 --rev 139c1778…` | exit 0; `mechanical 16 / killed 16 / survived 0 / errors 0` |

Pin audit: all **94** `source_pins` + `test_pins` across the six named packets are byte-exact at P38
(the packet named `…-canonical-exact-admission-v8` is dated `THV1-20260902-`, not `-20260901-`).
Every pinned pytest node id resolves to a real `def` in its pinned file (0 orphans). Authority stays
`NONE` on every axis; `formal_core_complete false`; `o008_status OPEN_EXACT_ALL_12_RECONCILIATION_MISSING`.

`tests/core/test_zusd_liquidation_partition.py` was excluded as instructed (pre-existing, unrelated).

---

## 2. One verdict per claim

### C1. The certificate is DERIVED, not assembled; pure, exact-typed, reject-is-a-value — **PARTIAL**

The inversion is real and faithful for every field the checker constrains. Purity holds: I re-checked
`canonical_global_bytes_v1(state)` before and after both an accepting and a refusing projection —
unchanged; every emitted row is a freshly constructed value of a *different* type from the state row,
so no aliasing is possible by construction. The function docstring's check order (0→4) matches the
code. Three defects: the enum's order claim is false (P3-1), the declared failure mode "a projection
mutates or aliases the caller's state" has no covering test (P3-4), and the one arithmetic call that
can raise on the accept path sits outside the refusal boundary (INFO-2).

### C2. The fixture partition is the headline result — **PARTIAL** (counts reproduce; the property is vacuous on-fixture and false off-fixture)

The counts reproduce exactly: 20 accept / 7 projection-refusal / 2 state-level over 29 vectors, and
the accepted bucket **is** checked by the checker before it is counted
(`test_global_accounting_allocation_projection_v1.py:96-101`) — the earlier count-without-check
defect the mutation ledger caught is genuinely fixed, and I confirmed the pinning test would fail if
that assertion were removed. But see P1-2: every projected certificate over the fixture carries zero
rows, and the property is false off-fixture.

### C3. What the witness adds — **PARTIAL**

Byte-for-byte reproduction from the receipt root, acceptance in the witnessed slot, and the
`PROJECTION_BINDING_ROOT_MISSING` refusal without the root are all real and executed. The binding-root
half is non-vacuous (`witness.fragment.binding_root != lane_state_root`, verified). The rows half is
vacuous: see P2-2.

### C4. Two ambiguities refused, not guessed; hunt for a third — **PARTIAL**

Both declared codes are reachable and exercised. I found a third under-determined field the projection
guesses instead of refusing, and it moves the derived roots: **P1-1**.

### C5. The mechanical mutation ledger (the four unreviewed commits) — **CLOSED, with caveats**

Independently re-run: 9/9 and 16/16, both exit 0. The anti-fake-kill design is real and I could not
break it: `_parse_mutant` requires `mutant.path ∈ source_pins`
(`tools/test_hygiene_evidence_v1.py:307`), `_validate_killer` requires the killer node ∈ `test_pins`
node ids, and `_validate_path_partition` forbids one path being in both — so **a row cannot mutate its
own killer**, the obvious way to appear killed without the mutation mattering. `CONTROL_FAILED` does
what it claims. Archive isolation from the *working tree* is real (`git archive <commit>`, fresh
extraction per row, row dir deleted after). Caveats in P3-5.

### C6. The added-packet rule and its residual — **PARTIAL**

The rule has teeth where it applies (renames normalise to D+A at
`tools/check_test_hygiene_v1.py:342-346`; `path.stem == evidence_id` is required; an unreadable date
is treated as post-cutover). The residual is declared — but it is **understated, and this candidate
exercises it**: P2-1, P3-3.

### C7. The packet — **PARTIAL**

32 replay commands, all executed and all matching the artifact's declared list; the projection module
is pinned with role `allocation_projection`; the four nonclaims the prompt names are present in the
THV1 packet. The missing Rust twin is **not** declared: P2-3.

---

## 3. Findings

### P1-1 — `PendingExternalObligationRowV1.source_principal` is unconstrained, so the state does **not** determine the certificate, and two different `allocation_root`s are both acceptable for one state

`src/core/global_accounting_allocation_certificate_v1.py:874-889` (`_check_external_obligations`)
checks only the effect-id set, `destination_id` and `commitment_root`. `_check_exactly_once`
(`:842-857`) folds external rows by `(asset, control_domain)`. `_check_lane_aggregates` (`:955-966`)
folds `controlled_locations` only. **No check anywhere reads `source_principal`** — yet it is hashed
into the fragment root and therefore into `field_ownership_root` and `allocation_root`.

The projection guesses it at
`src/core/global_accounting_allocation_projection_v1.py:213-215, 226` (the unique controlling
principal of the residual cell) rather than treating it as undetermined. This directly contradicts the
module docstring's central claim (`:29-34`): *"the certificate is a function of the state except for
one scalar per witnessed lane (its `binding_root`)"*. There is a **second** free scalar per pending
external row, and unlike `binding_root` it is not supplied by any admission.

Reproduction (executed):

```
state: lane 0 enabled, custody [(pool-a, USD, spot-pool, 10)],
       liabilities [(alice, USD, spot-pool, 4)], one PENDING outbox entry
p = project_allocation_certificate_v1(state, ((ASSET_TRANSFER, lane_root),))
row/aggregate/derived-root checks over p                    -> PASS
replace p's external row source_principal with "attacker-not-in-custody",
recompute the three derived roots, re-run the same checks   -> PASS
forged.allocation_root != p.allocation_root                 -> True
```

Severity: the whole point of a derived certificate is that the state pins the roots. It does not.
There is no runtime consumer, so nothing is exploitable today — but the campaign's determination claim
is false as written.

Minimal fix (either): (a) add a check to `_check_external_obligations` binding `row.source_principal`
to a `controlled_locations` row of the same `(asset, control_domain)` — the symmetric analogue of the
terminal row's `controlled` binding at `:922-928`; or (b) drop `source_principal` from
`PendingExternalObligationRowV1`, since nothing reads it and its only effect is to make the roots
under-determined. (a) is preferable: it makes the projection's guess the only admissible value.

### P1-2 — The headline partition is vacuous with respect to rows: every one of the 29 projected certificates carries **zero** rows, and off-fixture the "never a row defect" property is false

Measured over `renderer.VECTORS_V1` (29 vectors): the maximum row count of any projected certificate
(controlled + entitlements + reserves + external + terminal, over all twelve fragments) is **0**.
Every state that carries economic rows lands in the `PROJECTION_NO_LANE_FOR_ROWS` bucket, because the
fixture enables a lane only in vectors whose tables are empty. Consequently:

- the twenty "accepted" certificates are twenty copies of the twelve-empty-fragment certificate — and
  `test_accepted_fixture_vectors_are_reproduced_byte_for_byte` (`:104-122`) asserts exactly that
  (`projected == build_registered_empty_certificate_v1(state)`);
- the row inversions the packet's `claim_scope` enumerates (*"controlled rows from custody,
  entitlements from liabilities, reserves from the reserve partition, external rows from the PENDING
  outbox residual, terminal rows from OPEN obligations"*) are **never validated by the checker
  anywhere in the suite**. The unit tests that do derive rows
  (`test_one_pending_obligation_takes_the_residual…:280-295`, `test_two_hidden_domain_preimages…:262-272`)
  end in `RECEIPT_WITNESS_REQUIRED`, i.e. the checker stops at the lane-binding pass *before* any row
  check runs;
- so "it never yields a row, aggregate or derived-root defect" holds because no row is ever derived.

And the property is **false** off-fixture. Two counterexamples, both from values `GlobalEconomicStateV1`
accepts (its `__post_init__` at `src/core/global_settlement_types_v1.py:1391-1449` enforces canonical
order, uniqueness and per-row u128 bounds — nothing more):

```
CEX-1  custody [(pool-a,USD,spot-pool,5)], liabilities [(alice,USD,spot-pool,3)],
       reserves [(resv,USD,spot-pool,2)], one OPEN terminal (alice, USD, 5)
       projection -> a certificate
       row checks -> REJECT TERMINAL_BINDING_DRIFT "ASSET_TRANSFER terminal total USD:alice:spot-pool"
       (the projection never checks the terminal bound _check_terminal_totals enforces at :931-950)

CEX-2  custody [(pool-a,USD,spot-pool,2^127),(pool-b,USD,spot-pool,2^127)],
       liabilities [(alice,…,2^127),(bob,…,2^127)]   (residual cancels to 0)
       projection -> a certificate
       row checks -> REJECT ALLOCATION_TOTAL_OVERFLOW "ASSET_TRANSFER controlled"
       (the projection's residual arithmetic uses unbounded Python ints; the checker's
        _fold at :836-841 is u128-checked over (asset, control_domain), a key that is NOT
        unique across custody rows)
```

Both were run by driving the checker's own row/aggregate/derived-root passes in checker order
(`_check_exactly_once` … `_check_derived_roots`); through the public entry point they are masked by
`RECEIPT_WITNESS_REQUIRED`, which is precisely the reason the property looks true.

The packet's `claim_scope` **is** scoped ("for every state the golden fixture renders"), so it is not
a false statement. The module docstring and the test docstring are not scoped:
`tests/core/test_global_accounting_allocation_projection_v1.py:58-61` — *"It never produces a
certificate that fails a row, aggregate, or derived-root check"*. That sentence is false.

Minimal fix: (i) state the limit in a nonclaim — *"over the golden fixture every derived certificate
is the twelve-empty-fragment certificate; no row inversion is exercised against the checker"*;
(ii) scope the two docstrings to the fixture; (iii) add the terminal bound
(`sum of OPEN terminal amounts per (asset, claimant, domain) ≤ entitlement`) and a u128 fold guard as
projection refusals, so the projection is refusal-total against the checker rather than accidentally so.

### P2-1 — The cutover rule this commit introduces is bypassed by four of the six packets the same commit ships

`_reject_added_legacy_packets` (`tools/check_test_hygiene_v1.py:186-224`) exempts an ADDED packet when
**both** its evidence-id date and its own `created_date` precede `MECHANICAL_MUTATION_ROWS_FROM =
"20260903"`. Commit `2e1842291` (author date **2026-09-03**) adds four packets that are 100% legacy
rows and each declares `created_date: "2026-09-02"`, inherited from its predecessor lineage version:

| packet | legacy rows | created_date | added in |
|---|---|---|---|
| `THV1-20260901-o008-formal-cycle-admission-v34` | 105 | 2026-09-02 | 2e1842291 (2026-09-03) |
| `THV1-20260901-global-accounting-allocation-certificate-v20` | 69 | 2026-09-02 | 2e1842291 (2026-09-03) |
| `THV1-20260901-claimant-backing-guard-golden-v27` | 13 | 2026-09-02 | 2e1842291 (2026-09-03) |
| `THV1-20260902-global-settlement-v1-canonical-exact-admission-v8` | 7 | 2026-09-02 | 2e1842291 (2026-09-03) |

194 string-only rows, cut on the cutover date, exempted by a stale date field. Reproduction (executed,
against a copy of the evidence dir; the worktree was not modified):

```
cp -r tests/evidence/test_hygiene /tmp/ev
check_test_hygiene_v1.py --evidence-dir /tmp/ev \
  --changed-file A:tests/evidence/test_hygiene/THV1-20260901-global-accounting-allocation-certificate-v20.json
  -> exit 0  "test-hygiene-v1: ok packets=206 … legacy:5043"
sed -i 's/"created_date": "2026-09-02"/"created_date": "2026-09-03"/' /tmp/ev/THV1-…-certificate-v20.json
same command
  -> exit 1  "error: added evidence packet … declares string-only mutation rows; declare mutant or narrative"
```

The declared residual says *"a packet that back-dates BOTH fields is exempt … nothing in the evidence
directory records when a packet was authored"*. That is honest about the mechanism but silent about the
fact that the candidate is exercising it: the reader is told about a theoretical hole while four
packets in the same commit are sitting in it.

Minimal fix: set `created_date` to the date the packet file is actually cut, and key the exemption on
the authoring commit's date instead of the packet's self-report — the checker already shells out to git
in diff mode, so `git log --diff-filter=A --format=%ad -1 -- <path>` is available and closes the residual
outright. Failing that, say in the docstring and in the campaign doc that the residual is currently in use
and for how many rows.

### P2-2 — The witness evidence is over a witness with **zero** rows, so the "not its rows" half of the claim is vacuous, and no nonclaim records it

`_witnessed()` (`tests/core/test_global_accounting_allocation_certificate_v1_golden.py:345-372`) builds
its state from `renderer._spec(lanes_enabled=ONE_ENABLED)` — the default spec, all economic tables empty.
Measured: the admitted `witness.fragment` has `(0,0,0,0,0)` rows across
`controlled_locations / claimant_entitlements / unencumbered_reserves / pending_external_obligations /
terminal_bindings`, and the state's five tables are likewise empty. So *"the sealed witness contributes
its binding root and its header, **not its rows**"* is established over a witness that has no rows at all.

The claim is also structurally hard to make non-vacuous as things stand: an enabled receipt-backed lane
requires a witness (`RECEIPT_WITNESS_REQUIRED`), and the witness's fragment must equal the certificate's
fragment (`RECEIPT_WITNESS_FRAGMENT_DRIFT`), so a projected fragment carrying rows can only be accepted
against a witness that already carries those same rows.

Neither the THV1 packet's five nonclaims nor `NONCLAIMS_V1[15]`
(`tools/o008_formal_cycle_admission_v1.py:539-543`) records this limit.

Minimal fix: add a nonclaim — *"the witnessed evidence is over an admission whose fragment carries no
rows; that the witness contributes no row information is not established for a witness with non-empty
tables"* — and, when an admission fixture with non-empty custody exists, promote it to a real test.

### P2-3 — The absent Rust twin of the projection is not declared anywhere

`SOURCE_PIN_ROLES_V1` (`tools/o008_formal_cycle_admission_v1.py:190-191`) registers the projection with
roles `allocation_projection` and `allocation_projection_replay` only. Every neighbouring surface in the
same list carries an explicit twin role (`admission_rust_twin`, `producers_rust_twin`,
`rust_compiled_projection_gate`, …), and `NONCLAIMS_V1` carries a dedicated paragraph on the receipt-
admission Rust twin's boundary. `grep -i rust` over
`tests/evidence/test_hygiene/THV1-20260903-global-accounting-allocation-projection-v1.json` returns
nothing, and `NONCLAIMS_V1[15]` does not mention it. A reader comparing the projection to its
neighbours cannot tell whether the twin is missing, deferred, or deemed unnecessary.

Minimal fix: one nonclaim — *"the allocation projection has no Rust twin; the derivation is
single-implementation and no differential evidence constrains it"*.

### P3-1 — `AllocationProjectionRejectCodeV1`'s "in the order the projection checks them" is false

`src/core/global_accounting_allocation_projection_v1.py:81-89` declares
`PROJECTION_NO_LANE_FOR_ROWS` fourth and `PROJECTION_EXTERNAL_RESIDUAL_AMBIGUOUS` fifth, under the
docstring *"Closed projection rejects, in the order the projection checks them."* But
`_terminal_rows_v1`'s foreign-lane branch (`:252-256`) also emits `PROJECTION_NO_LANE_FOR_ROWS`, and it
runs **after** `_external_rows_v1` (`:365-368`). Executed: a state with a foreign-lane OPEN terminal
*and* two PENDING entries over one residual cell emits `PROJECTION_EXTERNAL_RESIDUAL_AMBIGUOUS`, not
`PROJECTION_NO_LANE_FOR_ROWS`. Reject precedence is part of this repo's contract (CLAUDE.md, "Error
Model"), and the certificate module already carries a "realised precedence" comment for exactly this
reason (`global_accounting_allocation_certificate_v1.py:1004-1006`).

Minimal fix: adopt the same treatment — a comment naming the realised precedence, or move the
foreign-lane check into the row-placement pass so declared and realised order agree.

### P3-2 — `TEST_HYGIENE_CONTRACT_V1.md` documents mutant fields the parser refuses

`docs/testing/TEST_HYGIENE_CONTRACT_V1.md:116-119` specifies
`"mutant": {"path", "needle", "replacement"}`. The parser requires
`_MUTANT_FIELDS = {"path", "needle_lines", "replacement_lines"}` under `exact_fields`
(`tools/test_hygiene_evidence_v1.py:60, 303`) — the lines encoding introduced by `8942d6bd2`, the last
of the four unreviewed commits, which did not update the doc. A packet author following the contract
document writes a packet the checker rejects.

Minimal fix: update the three lines to `needle_lines` / `replacement_lines` and say why (printable-ASCII
packet encoding).

### P3-3 — The same doc states the added-packet rule more strictly than the code implements it

`docs/testing/TEST_HYGIENE_CONTRACT_V1.md:126-127`: *"an added packet may not carry them whatever date
its name claims."* The code exempts an added packet when the name date **and** `created_date` both
precede the cutover — which is what P2-1 relies on. The doc therefore describes a rule with no residual
while the shipped rule has one that is currently in use.

### P3-4 — A declared failure mode has no covering test

`THV1-20260903-global-accounting-allocation-projection-v1.json` `failure_modes[4]` is *"a projection
mutates or aliases the caller's state"*, and `reject_is_noop.reason` asserts *"the projection performs
no mutation of the state or of any caller-supplied tuple"*. No test in
`tests/core/test_global_accounting_allocation_projection_v1.py` asserts it (`grep` for
`alias|unchanged|canonical_global_bytes_v1(state` returns nothing). The property does hold — I verified
`canonical_global_bytes_v1(state)` is unchanged across both an accepting and a refusing projection —
but it is asserted by the packet and checked by nobody, which is the exact shape the THV1 contract
exists to prevent.

Minimal fix: two lines in the existing AAA tests capturing `canonical_global_bytes_v1(state)` before and
after and asserting equality.

### P3-5 — Mutation ledger: three hardening gaps

(a) **Asymmetric control guard.** `control_error_v1` (`tools/thv1_mutation_ledger_v1.py:197-209`)
requires, for a cargo killer, a green summary *and* `sum(passed) >= 1` — an explicit "at least one test
ran" guard. The pytest branch requires only `exit_code == 0`. A pytest killer that is skipped (or whose
selection collapses) passes the control. It cannot manufacture a KILL (it SURVIVES under the mutant and
the ledger exits 1), so this is fail-closed, but the asymmetry is undocumented and the docstring's
"the same killer must PASS on an unmutated control copy first" reads as stronger than it is for pytest.

(b) **Partial runs leave no trace in the report.** `--filter` and `--packet-file` change what the report
covers; `REPORT_KEYS_V1` (`:97-108`) has no field for either, and `ledger_report_v1` records neither.
The only signal is a stderr line ("the report is partial"), while the JSON is presented as *the*
deterministic artifact ("no timestamps", sorted rows). A filtered report is byte-shaped exactly like a
full one. Minimal fix: add `filters` and `packet_source` keys to the report.

(c) **The subprocess environment is inherited unscrubbed.** `run_environment_v1` (`:317-324`) sets
`PYTHONDONTWRITEBYTECODE`, locale and cargo variables but passes `PYTHONPATH`, `PYTEST_ADDOPTS` and
`PYTEST_PLUGINS` straight through. The docstring's *"the worktree is never read for sources"* is true of
the tool's own file handling, but the guarantee against a redirected import path rests on pytest's
rootdir insertion rather than on anything the ledger does. Minimal fix: pop those three keys in
`run_environment_v1`.

---

## 4. INFO

1. The packet declares and executes **32** replay commands, not 31; declared and executed sets are
   identical (I diffed them). `tests/test_check_o008_formal_cycle_v1.py` collects **392**, not 391.
2. `derive_canonical_allocation_rows_v1` can raise `OverflowError`
   (`global_accounting_allocation_certificate_v1.py:679-682`) and is called from the projection at
   `global_accounting_allocation_projection_v1.py:369`, **outside** the `try/except _Reject`. It is
   unreachable today because `state.liabilities` keys are unique, so the fold never exceeds one row's
   value — but it is the one raising arithmetic call on the accept path and it sits outside the
   reject-is-a-value boundary. Moving the three `derive_*` calls inside the `try` and mapping
   `OverflowError` to a closed code would make the totality structural rather than incidental.
3. Two of the six reject codes conflate under-determination with inconsistency. A terminal whose
   claimant has **zero** entitlement domains, a **negative** residual, and residual atoms with no
   PENDING obligation are all reported as `…_AMBIGUOUS`, though nothing is ambiguous: no certificate
   exists for those states. A consumer cannot distinguish "supply more information" from "this state
   reconciles to nothing". Given the repo's semantic-naming discipline this is worth a distinct code.
4. Corpus scale of the legacy residual, from the checker's own report:
   `mechanical 92 / mechanical_current 90 / narrative 2 / legacy 5043`. 1.8% of declared mutation rows
   in the repository have ever been executed. The checker reporting the count is the right design and
   makes this visible — the campaign doc should quote it rather than leaving it to a reviewer.
   (`mechanical_current 90 < 92`: two rows in the superseded `…thv1-mutation-ledger-v1` packet pin
   `tools/thv1_mutation_ledger_v1.py` at bytes the tool no longer has, so their needles are not checked.)
5. Positive: the pinning test's earlier defect is genuinely closed —
   `test_the_fixture_partition_of_states_is_pinned:88-101` runs the checker and asserts
   `AllocationCertificateAcceptedV1` before incrementing the accept bucket, and the parametrised
   companion test asserts the closed-code set for the refusal bucket. I attacked the count assertions
   adversarially as instructed and found no path by which a bucket is counted unchecked.

---

## 5. Grade — **B-**

Everything the candidate says it runs, runs, and reproduces here from a clean detached worktree: the
32-command replay, 542 Python tests, three Lean gates, the full Rust triple, four hygiene invocations,
and both mutation ledgers at 9/9 and 16/16. The mutation ledger is a real advance — it closes campaign
finding G7 by construction for new packets, and its anti-fake-kill design survived my attempts on it.
The projection module is careful, pure, exact-typed, and honest about having no consumer.

It does not reach B+ because two of the things it claims to have made executable are not:

- the headline partition is **vacuous with respect to rows** — all 29 derived certificates are the
  empty certificate, so none of the five row inversions the claim enumerates is ever checked — and the
  unscoped form of the property is **false**, with two executed counterexamples;
- the determination claim ("a function of the state except for one scalar per witnessed lane") is
  **falsified** by a second free field that the checker never reads and that changes all three derived
  roots.

And the cutover rule introduced here is bypassed, in this same commit, by four of the six packets it
ships — a residual that is declared in the abstract but not disclosed as in use.

None of this touches authority: authority stays `NONE` on every axis, `formal_core_complete` stays
false, the claim ceiling is unchanged, and the projection has no runtime consumer. The findings are
about what the campaign may *say*, which is exactly what this campaign trades in.
