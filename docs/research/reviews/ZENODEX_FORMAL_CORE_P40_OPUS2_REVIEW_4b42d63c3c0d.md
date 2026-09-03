# ZenoDEX Formal Functional Core Closure — Second Independent Review of C9c-3 (P40)

| field | value |
|---|---|
| subject | S40 = `42c2e40704181dc45d219634758d8b1fdd129fbf` ("fix: say which of the two things is true when the projection refuses") |
| artifact | P40 = `4b42d63c3c0de6b93bc0644817e1ab82d05c3b2f` (packet sha256 `59073e535075aadcb745ffaa0b781c6ac8a06add020b7f13014d69f39cc2eafc`, recomputed and matching) |
| worktree | `/tmp/zenodex-formal-core-opus2-c9c3` (detached, HEAD = P40, `git status --short` empty before and after) |
| reviewer | fresh-context **Opus 5**, second reviewer |
| date | 2026-09-03 |
| verdict | **REVISE (advisory)** — grade **B−**. 2 P1, 8 P2, 6 P3, 3 INFO. Authority stays NONE; the claim ceiling did not move. |

## Independence caveat (stated as required)

This campaign's second reviewer is normally a fresh-context **Fable 5.1** session. Fable is out of usage credit
until 2026-09-06, so **both** of this round's reviewers are fresh-context **Opus 5** sessions and the
independence is weaker than the campaign standard: the primary reviewer, this reviewer, and the author share a
model family. I have no access to the primary reviewer's worktree (`/tmp/zenodex-formal-core-opus-c9c3`),
report, or session, and did not read them; I did not read the author's worktree or scratchpad. Where a finding
below coincides with the primary reviewer's, read it as convergence between same-family sessions, not as
independent confirmation. The four I would weight most as my own — they came from probing the entry point, the
Rust twin and the grader directly rather than from the brief's checklist — are **P1-1**, **P1-2**, **P2-2** and
**P2-5**.

---

## 1. Replays executed here

Every Lean-bearing command ran under `flock -w 7200 /tmp/zenodex-lean.lock`. No pgrep detector was used; no
`pkill` was issued. `CARGO_TARGET_DIR=/tmp/zenodex-opus2-c9c3-cargo`, `CARGO_INCREMENTAL=0`,
`PYTHONDONTWRITEBYTECODE=1`, `PY="/home/trevormoc/Downloads/Autonomous Tau DEX/.venv/bin/python"`; the cargo dir
was deleted at the end.

| command | result |
|---|---|
| `check_o008_formal_cycle_v1.py --root $PWD --packet-commit 4b42d63c3` | exit 0; `ok true`, `packet_admitted true`, `current_source_drift []`, `errors []`, `proof_replay NOT_RUN` |
| the same `--replay --esso-python /usr/bin/python3 --esso-pythonpath …/ESSO` | exit 0; **`EXECUTED_PASS`, 38 runs**, `errors []`, `current_source_drift []`. Result sha256 `00c6cd71d4157f7b92d63df9ae0748f4aca196c4f8ba1759f772d6a5c9f2fe1b` |
| `ledger_projection_rows` / `tool` / `admission` / `ownership` / `certificate` / `lineage` (inside the replay) | `killed 20/22/31/21/1/2`, `mechanical` equal, **survived 0, errors 0** on every one — **97 kills, 0 survivors** |
| Lean inside the replay | `lean_version 4.27.0`; `lean_direct_check` and `lean_certificate_direct_check` empty stdout; `lean_axioms_probe` 25 theorems, `lean_certificate_axioms_probe` 16; `lean_binding_gate` 6, `lean_certificate_binding_gate` 6; `transfer_refinement_gate` **40** |
| ESSO inside the replay | `esso_validate` / `esso_certificate_validate` ir hashes as declared; both `verify-multi` **VERIFIED** with z3 4.15.4 + cvc5 1.1.2 and deterministic fingerprints; gates 20 / 24; `prior_restage_gate` 136 |
| `build_o008_formal_cycle_v1.py … --check --replay --output-json/-md` | exit 0; `{"drift":[],"mode":"check","ok":true,"subject_commit":"42c2e4070…"}`; `git status --short` empty afterwards and the packet sha256 unchanged — the packet reproduces byte-for-byte from S40 |
| `cargo fmt --all -- --check` (zk/global_settlement_abi_v1) | exit 0 |
| `cargo clippy --locked --all-targets -- -D warnings` | exit 0 |
| `cargo test --locked` | exit 0; 54 `test result: ok` summaries, **535 passed**, 0 failed |
| `pytest` over the six Python suites named in the brief, one run | **555 passed** in 274 s |
| `pytest tests/core/test_global_accounting_allocation_projection_v1.py` | **53 passed** (matches `PROJECTION_GATE_EXPECTED_PASSED_V1 = 53`) |
| `pytest tests/formal/test_lean_asset_transfer_refinement_v1.py` under the lock | exit 0; **40 passed** in 16.7 s (and `transfer_refinement_gate` 40 inside the replay) |
| `check_test_hygiene_v1.py --json` | exit 0; `ok true`, `evidence_packet_count 226`, `mutation_rows {legacy 5491, mechanical 280, mechanical_current 227, narrative 6}` |
| `--base-ref 2928191bbb9856341a42ef50cc73d9b6495b0d6a` (parent of S40) | exit 0, `ok true` |
| `--base-ref fd409ba6f7da8f0ec3e0220a04b7406d69a8cb85` (campaign base) | exit 0, `ok true` — the base is green |

`tests/core/test_zusd_liquidation_partition.py` excluded as instructed.

**Environment note (not a candidate defect).** The symlink recipe in the review brief is incomplete: the
`lean-mathlib` lakefile does `require mathlib from "../external/mathlib4"`, so `external/mathlib4` **and**
`lean-mathlib/.lake/packages/mathlib` must both point at `/home/trevormoc/deps/mathlib4`. Without them every
Lean-bearing replay command exits 1 with empty stdout and stderr, and the checker reports `EXECUTED_FAIL` with
eight `REPLAY_AUTHOR_RECORD_DRIFT` + eight `REPLAY_EXIT_CODE` errors. My first replay failed exactly that way. I
added the two symlinks (both paths gitignored; `git status --short` stayed empty) and re-ran from scratch; the
row above is the second run.

**Pin and node-id audit — clean.** The O-008 packet carries **58** `source_pins` with 58 distinct roles, all
byte-exact, and **38** replay commands, six of them ledger runs. Across the ten named THV1 packets all **135**
`source_pins` + `test_pins` are byte-exact and all **259** distinct pytest/cargo node ids resolve to a real
`def`/`fn` (0 orphans; the two `.rs` ids resolve at
`zk/global_settlement_abi_v1/tests/lane_module_release_route_binding.rs:6066,6095`). All **55**
`hygiene_selection` entries verify by `packet_sha256` and by `packet_git_blob` (`git hash-object`).
`claim_ceiling` is byte-identical to P39; authority NONE on every axis; `formal_core_complete false`;
`o008_status OPEN_EXACT_ALL_12_RECONCILIATION_MISSING`. P40 is a direct child of S40 whose complete diff is the
two packet files, `subject_tree` (`003c1295…`) equals `git rev-parse 42c2e4070^{tree}`, and P39→P40 adds exactly
two pins (`tools/test_hygiene_evidence_v1.py`, `tools/test_hygiene_model_v1.py`), closing P39 P3-3.

**Mutation-killer spot checks (three, all executed).** (a) The certificate v22 row: applied to a clean
`git archive` of **S39** its named killer passes — **SURVIVED, exit 0** — and at S40 it is KILLED, so the
`foreign` case added at `tests/core/test_global_accounting_allocation_certificate_v1_golden.py:185-201` is
load-bearing and the author's account of the first attempt is accurate. (b) A row for
`PROJECTION_ROWS_BEYOND_PRODUCER`, which the packet omits, KILLS when supplied (P2-4). (c) A row whose mutation
is unrelated to its description passes the strengthened grader (P2-5).

---

## 2. One verdict per claim

### C1. The false claim is withdrawn ("the certificate is a function of the state") — **CLOSED**

`src/core/global_accounting_allocation_projection_v1.py:16-26` now says the opposite explicitly: the checker
binds a pending row's source principal, and a terminal row's controlling principal, to *some* controlled
location, and the paragraph names its own earlier wording as false. I rebuilt the two-certificate witness
independently: custody `(USD, pool-a, spot-pool, 6)` + `(USD, pool-b, spot-pool, 4)`, one PENDING outbox entry;
`source_principal` `pool-a` vs `pool-b` both pass `_check_exactly_once`, `_check_entitlement_rows`,
`_check_external_obligations` and `_check_lane_aggregates` with `allocation_root` `0x611cd6ed0b43c02a…` vs
`0xb4fecce221699c58…`. The withdrawal is real, and I could not find a second admitting certificate the new
wording fails to cover: every state that admits an accepted certificate today produces either the
registered-empty projection or a fragment byte-equal to a minted witness's, both determined.

The **replacement** wording overshoots in the other direction — those two certificates are not *accepted*. See
P1-1.

### C2. A refusal says which of two disjoint things is true — **NOT CLOSED** (P1-1, P2-1, P3-1)

The thirteen codes exist in a closed enum, and I reached **all thirteen through the public entry point**. The
two branches are a precedence rather than a partition (`PROJECTION_ROWS_BEYOND_PRODUCER` is evaluated before the
residual codes, so a state that is both reports the first), which is harmless because both are unreconcilable —
but the taxonomy claim itself is false again, in the same shape as the P39 primary P1-1 it repairs: under the
current registry **every** state that reaches an `..._AMBIGUOUS` code has **zero** acceptable certificates. The
UNDETERMINED branch is empty. The taxonomy statement also omits three of its own thirteen codes, including this
candidate's headline code.

### C3. Unreconcilability is proved through the checker, not asserted — **NOT CLOSED** (P1-2)

`_no_certificate_reconciles` is **dead code**: defined at
`tests/core/test_global_accounting_allocation_projection_v1.py:97` and called nowhere in the repository. Every
one of the thirteen `_ROW_CASES` asserts the projection's own answer. No test anywhere exhibits two accepted
certificates. Both halves of the packet's declared standard are unimplemented.

### C4. The row-builder harness does not pretend to be the entry point — **PARTIAL** (P2-1)

The harness is honest about *using* the helpers, and I found no test result from it stated as a property of the
entry point — the direction the brief asked me to check is clean. It is not honest about *why*: its docstring
and two packet texts say these paths are "not reachable through the public entry today", and they are.

### C5. The ledger gate covers every mechanical packet — **CLOSED for coverage** (P2-4, P2-5, P2-8, P3-3 remain)

Verified by counting: sixteen packets carry mechanical rows; the six gated ones are exactly the current head of
each of the six lineages (the other ten are superseded v1/v2/v3 cuts of the same six). 20 + 22 + 31 + 21 + 1 + 2
= **97**, matching `LEDGER_GATED_PACKETS_V1` (`tools/o008_formal_cycle_admission_v1.py:95-102`). All 97 rows
mutate a source or tool file; **none** mutates a test file and **none** has its `killed_by` in the file it
mutates. All six ran in my replay: 97 KILLED, 0 SURVIVED, 0 errors. P39 primary P2-4 is closed.

The grader strengthening is real code but is neither binding (P2-5) nor tested (P2-8), and the headline guard of
this very candidate has no row (P2-4).

### C6. The certificate packet declares the source-principal guard — **PARTIAL** (P2-3)

The v22 `claim_scope` correctly withdraws the "module is unchanged" sentence and names P39 P2-1; its one
mechanical row is genuine and specific (spot check (a) above). But the packet claims a row "in both languages"
and there is one, Python-only.

### C7. The Rust half of the binding now has a test — **NOT CLOSED** (P2-2)

Proved by deletion: with the production guard removed the whole crate is still green, 535 passed.

### C8. Known-open items — **P39 second P2-5 still open (P2-6); its P3-2 is moot**

P3-2 is moot: the test it named is gone, and its replacement `test_row_derivation_accepts_the_determined_shapes`
(`:512`) claims only that rows "are derived and ordered" and calls no checker, so the name no longer asserts an
acceptance that does not happen. The overclaim did not move to a new test name — it moved into the packet's
statement of its evidence standard (P1-2).

The P39 second reviewer's P2-5 is not addressed: the module docstring now carries the carve-out (`:32-36`); neither the projection
packet's `claim_scope` nor the top-level packet's nonclaim 5 does.

### C9. Dates — **CLOSED** (P3-4 on the mechanism only)

All ten packets S40 adds stamp `created_date` `2026-09-03`, equal to the commit's author date (S40 author and
commit date `Thu Sep 3 11:37:50 2026 -0400`). P39 primary P2-3 and P39 second P3-1 are closed at the data level.

### C10. The packet — **CLOSED with one omission (P3-1)**

58 pins / 58 roles / 38 replay commands; ceiling byte-identical to P39; two new pins closing P39 P3-3. The four
nonclaims the brief requires are present verbatim in
`tests/evidence/test_hygiene/THV1-20260903-global-accounting-allocation-projection-v3.json`: the projection has
no Rust twin; the fixture partition is a statement about the twenty-nine golden states only and the general form
was false; a refusal does not say the state is invalid; nothing consumes any of it. Authority NONE;
`formal_core_complete false`.

---

## 3. Findings

### P1-1 — The UNDETERMINED branch is empty: every `..._AMBIGUOUS` refusal is over a state with **zero** acceptable certificates, so the taxonomy this candidate exists to draw mislabels every state it applies to

`src/core/global_accounting_allocation_projection_v1.py:91-100` (enum docstring), `:16-26` (module docstring
item 1), `tests/core/test_global_accounting_allocation_projection_v1.py:12-17`,
`tests/evidence/test_hygiene/THV1-20260903-global-accounting-allocation-projection-v3.json` `claim_scope` and
nonclaim 7, and `docs/research/ZENODEX_O008_FORMAL_CYCLE_V1.json` nonclaim 5 (and the rendered `.md`).

The claim, verbatim: *"UNDETERMINED means V1 state leaves more than one **acceptable** certificate open"*; the
packet nonclaim states it as *"a cell controlled by two principals admits **two accepted certificates** over one
state with different allocation roots"*.

**Structural proof.** No accepted certificate can carry a pending external row, a reserve row, or a terminal
binding row under the current registry:

* an enabled lane whose registered kind is not `RECEIPT_BACKED` fails `BLOCKED_LANE_PRODUCER_MISSING`
  (`src/core/global_accounting_allocation_certificate_v1.py:794-797`), and `ASSET_TRANSFER` is the only
  `RECEIPT_BACKED` registration (`:109-122`);
* an enabled `RECEIPT_BACKED` lane needs a witness (`:800-803`) whose fragment must **equal** the certificate's
  (`:808-810`); the witness is token-minted only by the admission (`:490-565`,
  `src/core/asset_transfer_receipt_admission_v1.py:289`) and the producer builds the fragment with
  `controlled_locations` and `claimant_entitlements` only
  (`src/core/global_accounting_lane_producers_v1.py:352-360`);
* a disabled lane carrying **any** of the five row families fails `DISABLED_LANE_NOT_EMPTY` (`:819-821`,
  `is_empty` at `:410-417`).

`..._EXTERNAL_RESIDUAL_AMBIGUOUS` is reachable only with a non-empty PENDING outbox — the
`if not open_cells and not pending: return ()` and `if len(open_cells) > len(pending)` guards at `:253-256`
absorb every case with `pending == ()` — and `..._TERMINAL_DOMAIN_AMBIGUOUS` only with an OPEN terminal. So
every state either code is returned for is UNRECONCILABLE, not undetermined.

**Executed reproduction** (`/tmp/opus2-c9c3-probe2.py`, `/tmp/opus2-c9c3-probe3.py`):

```
state: ASSET_TRANSFER enabled, custody (USD,pool-a,spot-pool,6)+(USD,pool-b,spot-pool,4), one PENDING outbox
  source_principal=pool-a: row-level [PASS,PASS,PASS,PASS]  alloc_root 0x611cd6ed…  FULL CHECKER -> RECEIPT_WITNESS_REQUIRED
  source_principal=pool-b: row-level [PASS,PASS,PASS,PASS]  alloc_root 0xb4fecce2…  FULL CHECKER -> RECEIPT_WITNESS_REQUIRED

with the suite's REAL minted witness (_witnessed(with_rows=True)), state given one PENDING entry:
  certificate equal to the witness fragment      -> EXTERNAL_OBLIGATION_BINDING_DRIFT
  certificate carrying the pending external row  -> RECEIPT_WITNESS_FRAGMENT_DRIFT
```

**Quantified** (`/tmp/opus2-c9c3-sweep.py`, 4000 pseudorandom states, seed 11): 122
`..._EXTERNAL_RESIDUAL_AMBIGUOUS` refusals and **0** AMBIGUOUS refusals over a state with neither a PENDING
outbox entry nor an OPEN terminal.

This is the P39 primary P1-1 one level up. That review showed four *shapes* mislabelled as ambiguous; the repair
gave those shapes their own codes and left the *class* mislabelled. The second P39 reviewer wrote the same
observation correctly — "two **row-check-passing** certificates", and explicitly "no external row can appear in
an accepted certificate at all" — and the candidate imported it while upgrading "row-check-passing" to
"accepted", which is the one word that makes it false.

Severity: nothing consumes the projection and it still refuses, so no bad object is derived. It is a P1 because
it is the candidate's headline claim, it is pinned in an enum docstring, a module docstring, a test docstring, a
THV1 `claim_scope`, a THV1 nonclaim and the top-level packet nonclaim, and a twenty-line probe falsifies it — for
the second consecutive candidate.

**Minimal fix.** In all six places replace "acceptable / accepted certificate" with "certificate that passes the
row, aggregate and derived-root checks", and add: *"Under the current registry no accepted certificate can carry
an external, reserve or terminal row, so every state reaching an `..._AMBIGUOUS` code is unreconcilable today;
the AMBIGUOUS codes record that the row content is undetermined, not that an accepted alternative exists."*

### P1-2 — The evidence standard the packet says it adopted is not implemented: `_no_certificate_reconciles` is dead code, and nothing exhibits two accepted certificates

`tests/core/test_global_accounting_allocation_projection_v1.py:97-137`.

The projection packet's `claim_scope` states: *"the suite's standard changed: an UNRECONCILABLE refusal is shown
by BUILDING the state-consistent certificate and having the checker refuse it, while the AMBIGUOUS one is shown
by exhibiting two certificates the checker accepts."* The commit message repeats it and adds "Neither is
asserted from the projection's own answer."

Both halves are false in the shipped tree.

```
$ git grep -n "_no_certificate_reconciles(" 42c2e4070 --
42c2e4070:tests/core/test_global_accounting_allocation_projection_v1.py:97:def _no_certificate_reconciles(state) -> str:
    # the definition, and nothing else, in the whole repository
```

An AST scan of the file agrees (`_no_certificate_reconciles: called=False`; `_root_of` at `:374` is dead too).
All thirteen `_ROW_CASES` (`:378-509`) assert `observed is code` on the value `_derive_rows` returns — the
projection's own answer, exactly the standard the claim says was replaced. The module's only four checker calls
(`:173`, `:199`, `:240`, `:355`) are the fixture partition and the two witnessed-reproduction tests; none runs
the checker twice on one state to show two acceptances.

The helper is also weaker than its name even if it were called: it builds one fragment and runs four checks
(`_check_exactly_once`, `_check_entitlement_rows`, `_check_external_obligations`, `_check_lane_aggregates`),
omitting `_check_reserve_rows` and `_check_terminal_bindings`, and it never populates
`pending_external_obligations` or `terminal_bindings` on the fragment it builds — so for exactly the states
where the row content is free, it would test a candidate the state does not imply.

**Minimal fix.** Either (a) call it — `assert _no_certificate_reconciles(state) != "ACCEPTED"` in the eight
UNRECONCILABLE `_ROW_CASES`, after adding `_check_reserve_rows`/`_check_terminal_bindings` to its check list and
building the external and terminal rows the state implies; or (b) delete `_no_certificate_reconciles` and
`_root_of` and strike the "standard of evidence changed" sentence from the packet and the commit trail. (a) is
what the claim describes and is a dozen lines.

### P2-1 — "The reserve, external and terminal derivation is unreachable through the public entry point" is false for all three families, and eight of the thirteen codes have no entry-point test

`tests/core/test_global_accounting_allocation_projection_v1.py:66-79` (harness docstring), `:493-503`
(parametrised test docstring), projection packet `claim_scope` and nonclaim 8, and the commit message.

The `PROJECTION_ROWS_BEYOND_PRODUCER` gate fires only when the owning lane's registered kind is `RECEIPT_BACKED`
(`src/core/global_accounting_allocation_projection_v1.py:464-479`). Eleven of the twelve lanes are not, so with
any of them enabled the entry point runs `_external_rows_v1` and `_terminal_rows_v1` exactly as `_derive_rows`
does. Executed through `project_allocation_certificate_v1` with `SPOT_LIQUIDITY` enabled
(`/tmp/opus2-c9c3-probe1.py`, `/tmp/opus2-c9c3-probe5.py`):

```
pending, no custody                    -> PROJECTION_PENDING_WITHOUT_BACKING
two residual cells / one pending       -> PROJECTION_UNASSIGNED_CONTROLLED_ATOMS
two pending / one cell                 -> PROJECTION_EXTERNAL_RESIDUAL_AMBIGUOUS
two principals control the cell        -> PROJECTION_EXTERNAL_RESIDUAL_AMBIGUOUS
terminal claimant with no entitlement  -> PROJECTION_TERMINAL_WITHOUT_ENTITLEMENT
terminal over-claiming                 -> PROJECTION_TERMINAL_EXCEEDS_ENTITLEMENT
claimant entitled in two domains       -> PROJECTION_TERMINAL_DOMAIN_AMBIGUOUS
terminal naming another lane           -> PROJECTION_NO_LANE_FOR_ROWS
```

and *derivation*, not only refusal, is reachable: with `SPOT_LIQUIDITY` enabled the entry point returns
certificates carrying a derived external row, a derived terminal row, and a derived reserve row
(`UnencumberedReserveRowV1(asset='USD', reserve_principal='pool-a', control_domain='spot-pool',
amount_atoms=6)`). `PROJECTION_ROW_TOTAL_OVERFLOW` is reachable through the entry point even on `ASSET_TRANSFER`
(no reserve, pending or terminal row is needed to reach the controlled fold).

So all thirteen codes are entry-point reachable, and **eight have no test that reaches them through the entry
point**: `..._EXTERNAL_RESIDUAL_AMBIGUOUS`, `..._TERMINAL_DOMAIN_AMBIGUOUS`, `..._NEGATIVE_RESIDUAL`,
`..._UNASSIGNED_CONTROLLED_ATOMS`, `..._PENDING_WITHOUT_BACKING`, `..._TERMINAL_WITHOUT_ENTITLEMENT`,
`..._TERMINAL_EXCEEDS_ENTITLEMENT`, `..._ROW_TOTAL_OVERFLOW`.

**Minimal fix.** Restate as *"the entry point refuses these states before the row logic on the only
receipt-backed lane; on the eleven lanes without a producer the row logic does run, and the checker then refuses
the result on the state-level gate"*, and re-point `_ROW_CASES` at the entry point with `SPOT_LIQUIDITY` enabled
— which deletes `_derive_rows` and gives all thirteen codes an entry-point test in one change.

### P2-2 — The new Rust test for the source-principal binding never calls the checker; deleting the production guard leaves the whole crate green

`zk/global_settlement_abi_v1/tests/global_accounting_allocation_certificate_golden.rs:298-371`, against the
guard at `zk/global_settlement_abi_v1/src/global_accounting_allocation_certificate.rs:1084-1094`.

The test builds `unbacked` and `backed` fragments and then asserts, of each, an inline closure
`fragment.pending_external_obligations.iter().all(|pending| fragment.controlled_locations.iter().any(|location|
location.asset == pending.asset && location.controlling_principal == pending.source_principal &&
location.control_domain == pending.control_domain))` — a copy of the production predicate evaluated in the test,
not a call into it. Its only `check_global_accounting_allocation_certificate_v1` call is on the **unmodified**
registered-empty vector, asserting `Accepted`.

**Executed reproduction** (worktree restored afterwards, `git status --short` empty, checker drift `[]`): I
replaced the guard body

```rust
        if !controlled {
            return fail(
                AllocationCertificateRejectCodeV1::ExternalObligationBindingDrift,
                format!("{effect_id} source binding"),
            );
        }
```

with `let _ = controlled;` and ran the crate:

```
cargo test --locked --test global_accounting_allocation_certificate_golden
  -> test result: ok. 4 passed  (including pending_external_source_principal_binds_to_a_controlled_location)
cargo test --locked
  -> 54 summaries, 535 passed, 0 failed
```

The Rust half of the P38 P1-1 repair is killed by nothing. This is P39 P2-2 answered with a test that does not
test it, and it is counted: `CERTIFICATE_RUST_GATE_EXPECTED_PASSED_V1` was raised 3 → 4 for it
(`tools/o008_formal_cycle_admission_v1.py:1138`). It is the "return h" tautology the campaign's own Lean quality
gates forbid, expressed in Rust.

**Minimal fix.** Put the fragments into a certificate, re-derive the three roots, and assert the checker's
verdict:

```rust
let mut forged = certificate.clone();
forged.ordered_lane_fragments[0] = unbacked;          // then re-derive the three roots
match check_global_accounting_allocation_certificate_v1(&forged, &state, &EMPTY_LANE_WITNESS_SLOTS_V1) {
    Ok(AllocationCertificateOutcomeV1::Rejected(r)) => {
        assert_eq!(r.code, AllocationCertificateRejectCodeV1::ExternalObligationBindingDrift);
        assert!(r.detail.ends_with("source binding"));
    }
    other => panic!("expected the source binding to reject, got {other:?}"),
}
```

and add the matching cargo mechanical row (P2-3), which would have caught this.

### P2-3 — The certificate packet says the guard is declared "as a mutation row in both languages"; there is one row and it is Python-only

`tests/evidence/test_hygiene/THV1-20260901-global-accounting-allocation-certificate-v22.json`, first sentence of
`claim_scope`, against its own `mutations` array.

The packet carries 70 rows, exactly one mechanical, whose `mutant.path` is
`src/core/global_accounting_allocation_certificate_v1.py`. Across **all 226** evidence packets no mutation row
names a `.rs` path or a cargo killer for this guard; across the six ledger-gated packets only 5 of the 97 rows
mutate Rust at all, all in `asset_transfer_receipt_admission.rs`.

```
python3 -c "import json;d=json.load(open('tests/evidence/test_hygiene/THV1-20260901-global-accounting-allocation-certificate-v22.json'));
print(d['claim_scope'][:200]); print([m['mutant']['path'] for m in d['mutations'] if m.get('mutant')])"
```

**Minimal fix.** Add a cargo mechanical row over `…certificate.rs:1084-1094` with the killer from P2-2 and bump
the gated count 1 → 2, or narrow the sentence to "in Python; the Rust twin is covered by an in-crate test".

### P2-4 — No mechanical row for `PROJECTION_ROWS_BEYOND_PRODUCER`, the candidate's headline guard; the missing row would kill

`tests/evidence/test_hygiene/THV1-20260903-global-accounting-allocation-projection-v3.json` (20 mechanical rows)
against `src/core/global_accounting_allocation_projection_v1.py:464-479`.

Every other guard in the module has a row — both binding-root branches, the multi-lane refusal, the type
boundary, the enum closure, both u128 folds, the negative residual, the unassigned atoms, the unbacked
obligation, both principal counts, the domain count, the foreign-lane terminal, the entitlement bound, the
witness rows. The gate this candidate exists to add has none. That is P39 P3-1 ("no mutation row for the
source-binding guard") repeated for the new headline guard.

It is an omission, not an impossibility. Executed with the row supplied on the command line (`--packet-file`, so
the tree was untouched):

```
needle       "                if beyond:"
replacement  "                if False and beyond:"
killer       tests/core/test_global_accounting_allocation_projection_v1.py::test_a_witnessed_lane_carrying_rows_no_producer_emits_is_refused
-> KILLED, exit 1, 2.2 s; report {mechanical 1, killed 1, survived 0, errors 0}
```

**Minimal fix.** Add that row and raise the gated count 20 → 21.

### P2-5 — The strengthened `_grade_ledger` still admits a KILLED row whose mutation is unrelated to what the row claims

`tools/o008_formal_cycle_admission_v1.py:4102-4122`.

The new block requires each KILLED row to carry `mutation.{path, needle_sha256, replacement_sha256}` as
non-empty strings with the two digests distinct, and `described == killed`. It never compares those digests with
the pinned packet's declared row and never checks that `mutation.path` is one of the packet's `source_pins`.
Since `_execute_mechanical_row` (`tools/thv1_mutation_ledger_v1.py:471-480`) hashes the row's **own** mutant, the
field is a faithful echo of whatever the row declares: it documents what ran, it does not bind what ran to what
the row's free-text `description` says.

**Executed demonstration** (packet supplied through `--packet-file`; the tree was untouched). I kept the v22
row's description verbatim — *"leave the pending-external source principal unbound, as it was when it was hashed
into every derived root and read by no check"* — and swapped its mutant to disable the unrelated
**duplicate-effect-id** guard in the same file:

```
needle       "            if row.effect_id in pending:"
replacement  "            if False and row.effect_id in pending:"
killer       …::test_duplicate_effect_id_across_lanes_is_rejected      (unchanged)
report       {mechanical 1, killed 1, survived 0, errors 0}; verdict KILLED; digests distinct
_grade_ledger(obs, 1) -> {'killed': 1, 'mechanical': 1, 'survived': 0, 'errors': 0}      # accepted
```

The source-principal guard was untouched and the gate passed. The commit's wording — "the grader checks that
every killed row **names the mutation that produced it**" — reads as a binding it is not. (Mitigating: the
report is produced live by the pinned tool from the packet at the pinned rev, so a *forged* report is not the
threat; a *mis-described row* is.)

**Minimal fix** (the P39 second reviewer's, unimplemented): have `_grade_ledger` load the pinned packet,
recompute `sha256(row.mutant.needle)` and `sha256(row.mutant.replacement)` for every declared mechanical row, and
require the report's set of `(path, needle_sha256, replacement_sha256)` triples to equal the packet's. That makes
a report reconcilable to one packet and no other.

### P2-6 — Known-open (P39 second P2-5): still open, and still unscoped in both places that carry the claim

`docs/research/ZENODEX_O008_FORMAL_CYCLE_V1.json` nonclaim 5, first sentence: *"the C9c projection, which refuses
with a closed code wherever V1 state does not determine a certificate the checker can accept"* — no exception.
The projection packet's `claim_scope` has the same sentence. The module docstring now carries the carve-out
(`src/core/global_accounting_allocation_projection_v1.py:32-36`), so the repair exists; it did not reach the
packets.

Executed: with `SPOT_LIQUIDITY`, `PROOF_REWARDS` or `EXTERNAL_CUSTODY` enabled and balanced rows, the entry point
derives a certificate and the checker refuses it `BLOCKED_LANE_PRODUCER_MISSING` (probe 1, B1-B5). Over the
4000-state sweep: **32** derived certificates rejected `BLOCKED_LANE_PRODUCER_MISSING`.

**Minimal fix.** Copy the module docstring's two-gate sentence into nonclaim 5 and into the projection packet's
`claim_scope`.

### P2-7 — A third undeclared carve-out: on the witnessed lane the repair covers row *families* but not row *contents*

`src/core/global_accounting_allocation_projection_v1.py:27-36` declares exactly two exceptions to "where NO
certificate over the state can be accepted, the projection refuses". There is a third. A lane's minted witness is
determined by its committed lane root (the producer folds `accepted.private_port.post_state.custody`,
`src/core/global_accounting_lane_producers_v1.py:342-360`), so a state whose `ASSET_TRANSFER` custody rows differ
from the ones that root's receipt admitted has **no** accepted certificate — and the projection derives one.

Executed (`/tmp/opus2-c9c3-probe4.py`): take `_witnessed(with_rows=True)`, add **one atom** to the single custody
row and the matching liability row, keep the same lane root and binding root:

```
projection DERIVED a certificate
  with the only minted witness for this lane root -> RECEIPT_WITNESS_FRAGMENT_DRIFT
  with empty witness slots                        -> RECEIPT_WITNESS_REQUIRED
```

This is the residue of the P39 second reviewer's P1-1: `PROJECTION_ROWS_BEYOND_PRODUCER` closes the case where the
state populates a family the producer cannot emit and leaves the case where it populates a family the producer
*can* emit with content the producer would not produce.

**Minimal fix.** Disclose it — a code for it would need the lane's own state, which V1 does not carry: *"a
witnessed lane's controlled and entitlement rows must also equal the ones the committed lane root's receipt
admitted; the projection cannot check that and will derive a certificate the witness check refuses."*

### P2-8 — The new `_grade_ledger` block has no test: none of the three `REPLAY_LEDGER_*` reject codes is asserted anywhere

`tools/o008_formal_cycle_admission_v1.py:4078-4122` against `tests/test_check_o008_formal_cycle_v1.py`.

S40 changed `_ledger_report` (`:1063-1090`) so the **passing** stub now emits per-row `mutation` blocks, and
that stub is used in exactly one place (`:1188`, inside `_passing_observations`). The negative table
`test_replay_observation_mutations_are_executed_fail` (`:1210-1234`) has thirteen entries, none of them a ledger
command. `grep -rn "REPLAY_LEDGER" tests/` returns nothing: `REPLAY_LEDGER_ROW_WITHOUT_MUTATION`,
`REPLAY_LEDGER_ROW_NOT_KILLED` and `REPLAY_LEDGER_KILLED_COUNT_DRIFT` are asserted by no test. Deleting the whole
new block would leave the suite green.

**Minimal fix.** Add three rows to that parametrised table: a report whose KILLED rows carry no `mutation`
(expect `REPLAY_LEDGER_ROW_WITHOUT_MUTATION`), one where `needle_sha256 == replacement_sha256` (same code), and
one with `survived: 1` (expect `REPLAY_LEDGER_ROW_NOT_KILLED`). Three `pytest.param` lines.

### P3-1 — The taxonomy statement omits three of its own thirteen codes, including the headline one

`src/core/global_accounting_allocation_projection_v1.py:94-100` says "Two kinds of refusal share this family"
and then names two AMBIGUOUS and eight UNRECONCILABLE codes. `PROJECTION_ROWS_BEYOND_PRODUCER`,
`PROJECTION_BINDING_ROOT_UNEXPECTED` and `PROJECTION_BINDING_ROOT_MISSING` appear in neither list; the O-008
nonclaim 5 enumeration has the same gap for `..._ROWS_BEYOND_PRODUCER`. Fix: add the headline code to the
UNRECONCILABLE list and say the two binding-root codes are argument errors about the supplied
`lane_binding_roots` rather than statements about the state.

### P3-2 — The documented check order does not mention the gate this candidate added

`src/core/global_accounting_allocation_projection_v1.py:400-407` lists (0) type boundary, (1) one enabled lane,
(2) binding roots, (3) rows placed on the lane, (4) fragments assembled. The producer-capability gate runs
between (2) and (3) and is absent. Fix: insert it and renumber.

### P3-3 — Two of the six ledger-gated packets are not pinned by the packet that claims the gate

`THV1-20260901-global-accounting-allocation-certificate-v22` and `THV1-20260902-test-hygiene-lineage-ordering-v4`
appear in `LEDGER_GATED_PACKETS_V1` but not among the seven packets in the O-008 packet's `hygiene_selection`, so
no `packet_sha256` / `packet_git_blob` binds their row content to this packet. The commit hash covers them for
this review; a later cut re-using the claim at another commit would not have to declare a change to their rows.
Fix: add both to `hygiene_selection` — every packet the checker executes should be pinned by the packet that
claims the execution.

### P3-4 — "the generator now stamps every packet it writes" names a tool that is not in the tree

The commit attributes the `created_date` repair to a generator change. S40 changes no generator: its sixteen
files are the projection module, three test files, ten THV1 packets, `tools/o008_formal_cycle_admission_v1.py`
and one Rust test. `grep -rn created_date tools/*.py` finds only readers and validators
(`check_test_hygiene_v1.py:190-262`, `test_hygiene_evidence_v1.py:156,488`) and the O-008 builder, which takes
`--created-date` from the command line. The outcome is correct and verified, so C9 is closed; the *mechanism* is
unverifiable from the tree, which matters because the near-identical sentence at P39 ("the generator now stamps
the authoring date") is the one both P39 reviewers falsified. Fix: name what actually stamps the date, or drop
the mechanism claim and keep the verified outcome.

### P3-5 — The v22 `claim_scope` repeats a sentence verbatim

`THV1-20260901-global-accounting-allocation-certificate-v22.json`: *"Earlier: v20 re-pin (C9c-1): the
certificate module is unchanged; it is now also pinned by the allocation-projection packet, whose derivation
inverts these checks."* appears twice in a row. The prepend-and-carry construction that produced the P39 P2-1
defect is still un-deduplicated. Fix: de-duplicate on carry.

### P3-6 — `test_reject_codes_are_closed_and_ordered` scans the file, not "this file's own assertions"

`tests/core/test_global_accounting_allocation_projection_v1.py:311-329`. The docstring says the claim is checked
"by scanning this file's own assertions"; the body regexes `AllocationProjectionRejectCodeV1\.([A-Z_]+)` over the
whole source text, so a code named only in a comment, a docstring, a data literal or a negative membership set
would satisfy it. All thirteen currently do have real assertions (I checked each), so nothing is false today —
the check is weaker than its description, which is the pattern P39 P3-4 asked to close. Fix: restrict the scan to
lines containing `assert`, or collect the codes appearing in `.code is …` comparisons.

---

## 4. INFO

**INFO-1 — Review-brief drift.** The brief says "Both reviewers' P39 P1 was the same". They were not: the
primary's P1-1 was the mislabelled `..._EXTERNAL_RESIDUAL_AMBIGUOUS` shapes; the second's P1-1 was the row
families no producer can emit. The claim the brief describes ("the certificate is a function of the state") was
the P38 P1 and reappears at P39 only as the second reviewer's P2-1. The candidate repairs all three, so nothing
was lost; I note it because that kind of drift can send a reviewer to check the wrong thing.

**INFO-2 — Process disclosure.** Two statements in the disclosure are in tension: the pinned battery ran
"against a tree byte-identical to the committed S40 tree", and the cargo gate was re-run at P "because that
battery predated the Rust golden refresh in this candidate". A tree byte-identical to S40 already contains that
refresh. I cannot resolve it from the tree, and it does not affect this review: I replayed all 38 commands, the
cargo gate, the Python suites and the three hygiene runs myself, from a clean worktree, at P40. What I *can*
verify of the disclosure holds: `subject_tree` equals `git rev-parse 42c2e4070^{tree}`; P40's complete diff is
the two packet files; the packet sha256 matches the declared value; no partial write survives (`git status
--short` empty and the builder `--check` reproduces both files byte-for-byte).

**INFO-3 — Carried, unchanged: the row derivation runs outside the refusal boundary.**
`src/core/global_accounting_allocation_projection_v1.py:499-511`: `derive_canonical_allocation_rows_v1`,
`derive_field_ownership_root_v1`, `derive_terminal_binding_root_v1` and `derive_allocation_root_v1` are all
called **after** `except _Reject`, so a checked-fold `OverflowError` inside them would escape as an exception
rather than as a closed refusal carrying the state root. Unreachable today — entitlement keys are unique per
state and only one lane may be enabled — and it was already recorded at P38 and P39. Noting it only because the
module docstring's "Every refusal is a value carrying the unchanged state root" (`:407`) has no exception
attached to it.

---

## 5. Worktree hygiene

`/tmp/zenodex-formal-core-opus2-c9c3` is at P40 with `git status --short` empty at the end of the review, and
`check_o008_formal_cycle_v1.py` reports `current_source_drift []` after the one temporary edit (the Rust guard
deletion in P2-2, restored from a byte copy taken before the edit). Every other adversarial experiment ran
outside the worktree: on a `git archive` extract under `/tmp`, through
`tools/thv1_mutation_ledger_v1.py --packet-file --workdir /tmp/…` (which mutates only its own extracted copies),
or as a probe script under `/tmp`. The two symlinks I added (`external/mathlib4`,
`lean-mathlib/.lake/packages/mathlib`) and the `lake-manifest.json` that lake wrote are all gitignored.
`/tmp/zenodex-opus2-c9c3-cargo` was deleted. The author's worktree, the canonical checkout, the other reviewer's
worktree and the author's scratchpad were not read or written.

## 6. Bottom line

The mechanical work is real and reproduces exactly here. The ledger gate now covers every current packet that
carries mechanical rows — six of six, 97 rows, 97 KILLED, 0 SURVIVED, 0 errors, re-run by me — and P39 primary
P2-4 is closed. The pin audit is spotless across 58 + 135 pins, 259 node ids and 55 `hygiene_selection` entries.
All ten packets are honestly dated. The two parsing dependencies are pinned. The `PROJECTION_ROWS_BEYOND_PRODUCER`
guard is correct and its premise is structurally sound: I verified from the registry, the witness mint and the
`DISABLED_LANE_NOT_EMPTY` gate that a reserve, pending or terminal row cannot appear in any accepted certificate.
The "certificate is a function of the state" wording is genuinely withdrawn, and the added `foreign` test case is
load-bearing (its absence lets the declared mutant survive at S39, which I reproduced).

Against that, three of this candidate's own repairs are stated larger than they shipped and one is vacuous. The
headline taxonomy is false again, by the same probe class that falsified it at P39: every `..._AMBIGUOUS` state
is unreconcilable today, so the UNDETERMINED branch has no members (P1-1). The evidence standard the packet says
it adopted is dead code — the helper written to prove unreconcilability through the checker is never called, and
nothing exhibits two accepted certificates (P1-2). The Rust repair for P39 P2-2 asserts its own re-implementation
of the guard: deleting the guard leaves 535 Rust tests green (P2-2). The headline guard has no mutation row, and
the row that is missing kills when supplied (P2-4). The strengthened grader neither binds a report to its packet
(P2-5) nor has a single test (P2-8). And the claim that the reserve, external and terminal paths are unreachable
through the entry point is false on eleven of twelve lanes (P2-1).

Four of the six P2s and both P1s are the same failure mode the last three reviews named: the repair lands in the
code, and the claim is written for a larger repair than the one that shipped. That is why this does not grade
above P39 despite being a larger candidate.

**Grade: B−.** REVISE (advisory). Advisory ACCEPT is withheld until P1-1 and P1-2 are closed. Authority stays
NONE on every axis; `formal_core_complete` stays false; the claim ceiling must not move.
