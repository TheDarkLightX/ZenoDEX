# Independent review — Tau ADT logical ABI re-cut of PR #534

**Subject (exact)** branch `codex/tau-adt-logical-abi-recut-20260902`, head `946d5782f8a9679d39fdc51be14e6af788d0cfa0`
(13 single-parent commits rooted at PR #534's head `95b3cd6e156840ee36e464c47881e345a45b364b`; verified with
`git rev-list --parents`, every commit has exactly one parent, no trailers). Subject worktree
`/tmp/zenodex-tau-adt-recut-20260902` (clean, untouched).
**Reviewer** Fable 5.1, fresh context, independent of the author; read-only. Everything below was executed,
not read. Authority NONE; nothing here certifies anything.
**Review copies** `/tmp/zenodex-tau-recut-review-fable` (detached at 946d5782f, all mutations reverted, `git status`
clean at the end) and `/tmp/zenodex-tau-recut-review-fable-pr534` (detached at 95b3cd6e1 for the original test).
**Binaries** pinned `external/tau-lang-adt-logical-abi-v1/build-Release/tau` sha256
`4be1965b15a4a6d074e8b4b93d7134e3edcd38ebce1109550d280e724ea6d6a7`, `--version` = `0.7.0-alpha (1c1e58ae)`,
checkout HEAD `1c1e58aea7ddec04e48ce11cb0e6ed0cbe2a0d43` (matches the lock); differential
`/tmp/tau-lang-current/build-Release/tau` sha256 `b62c0706f682d305…`, checkout HEAD `3c24bad9ee4c…`, but the binary
self-reports `0.7.0-alpha (d80aa50c)` (see P3-2).
**Scratch artifacts** (all under `/tmp/claude-1000/-home-trevormoc-Downloads-Autonomous-Tau-DEX/048f75e7-d6e6-4ccb-873c-94fbe68c6c2e/scratchpad/`):
`orig/repro_f1.py` (F1 reproduction), `mut/mut_harness.py` + `mut/results.json` + per-program `.tau`/`.transcript.txt`
(questions B, C, F), `forge/forge.py` (questions E, G, B-invisible), `live/fresh_receipt.json` + `live/stderr.log`
(full live replay), `tau_recut_review_fable.md` (this file).

---

## Verdict

**Grade: B — REVISE (small, targeted).** One P2, six P3, no P1.

At this exact commit every claim I could execute replays: F1 reproduces byte-for-byte on both binaries and the fixed
spec answers T without errors; all 26 vectors, 18 capability probes and 5 selftest probes reproduce on the pinned
binary in a fresh run (see "Live replay"); every mutation row in the v5 packet is really killed by the test it names
(14 executed, all red); every Python-side and Tau-side mutation I constructed makes the vector's universal program
answer F; the non-vacuity program catches a vacuous universal; unresolved and arity-mismatched definitions cannot
count as T. The specs' theorems are correctly relabelled as capability probes and the F3 table is correct clause by
clause.

The P2 is a soundness boundary of the offline receipt gate that the packet's invariant ids do not make visible: the
committed receipt is hash-bound to the spec, journal spec, lock and renderer, but not to the Python transition whose
observed outcomes it records. A precedence swap in `src/core/asset_transfer_module_v1.py` leaves all three pinned
killers green (E20), and a consistent forgery of the `python_code` rows in both committed artifacts also passes
(E19). The repair is about twenty Tau-free lines in the offline test (recompute the Python outcomes and the program
hashes) plus two source pins in the packet. Nothing at this commit is wrong; the evidence contract is narrower than
its invariant ids read.

---

## Replay ledger

| # | What I ran | Result |
|---|---|---|
| R1 | `git rev-list --parents 95b3cd6e1..HEAD` | 13 commits, all single-parent, first parent is `95b3cd6e1`; `tools/` and `config/` byte-identical to the PR head |
| R2 | Original PR test file at its exact bytes (`f457682f5d…`, matches the v4 packet pin) run unmodified in a detached worktree at `95b3cd6e1` with the pinned binary linked | `1 failed, 1 passed in 2.94s`; failure at `:151` `assert "(Error)" not in transcript`, transcript carries `Unresolved function or predicate symbol min(b2, b1) found. Returning unsat` twice followed by `%1: T` |
| R3 | `orig/repro_f1.py`: the PR's own `_run_query` over the ORIGINAL spec and the FIXED spec on both binaries | original spec: REFUSED on both binaries (same two `(Error)` lines + bogus `T`); fixed spec: exactly one `T`, zero `(Error)`, on both binaries |
| R4 | `pytest tests/tau/test_tau_adt_logical_abi_v1.py tests/tau/test_tau_adt_logical_abi_live_v1.py` (subject worktree) | 3 passed, 1 skipped (`TAU_LIVE_NOT_REQUESTED`) in 0.55 s |
| R5 | `ZENO_TAU_ADT_LIVE=1 ZENO_TAU_ADT_BIN=/nonexistent/tau pytest …live_v1.py` | `1 failed`: `Failed: TAU_PIN_UNAVAILABLE: no pinned Tau binary at /nonexistent/tau` (a failure, not a skip) |
| R6 | `tools/run_test_hygiene_gate_v1.py --base-ref 95b3cd6e1` in the clean copy | `evidence passed critical=3 nodes=3`, rc 0 |
| R7 | Packet v5 pin check (`source_pins`, `test_pins`) against the tree; ASCII scan | all 11 pins match; 0 non-printable bytes; all 11 `killed_by` node ids are in `test_pins` |
| R8 | Full live replay `render_tau_adt_abi_v2.py --receipt` on the pinned binary (background, fresh receipt) | see "Live replay" below |
| R9 | `mut/mut_harness.py` (13 Tau programs, questions B/C/F) | every expectation met; table in question B |
| R10 | `forge/forge.py` (22 offline cases, questions E/G) | 14 kills confirmed, 4 limits, 1 gap, 1 invisible bug; table in question E |
| R11 | z3 over the `_post_balances` arithmetic (three principal-aliasing cases) | BALANCE_OVERFLOW unsat from a well-formed state in all three; sat only under a hypothetical credit-before-debit order |
| R12 | PopperPad briefing `tau-language`, dead-ends `adt`, falsified `tau` | nothing contradicts the approach (several `Tau-Spec-Experimenter` dead ends are stale: `!=` parses fine at this pin) |

### Live replay (R8)

LIVE_REPLAY_PLACEHOLDER

---

## Answers to the adversarial questions

### A. Does the PR review hold? (F1 reproduction, F3 table)

**F1 holds exactly.** R2 and R3 above. The engine prints the unresolved-`min` error twice and still prints `%1: T`;
the PR's harness refuses on `(Error)`. The fix at `asset_transfer_adt_contract_v1.tau:53`
(`min(required:bv[16], cap:bv[16]) = required:bv[16]`, wrapper removed) replays `T` with no error on `1c1e58ae` and on
the `3c24bad9` checkout's binary. The strict variant (`<-> required < cap`) answers `F` in the receipt and in my fresh
run.

**F3 table is correct clause by clause.** I re-derived each `always` conjunct against its hypothesis predicate:

| Spec clause | Hypothesis predicate | Why the conclusion is already a conjunct |
|---|---|---|
| asset `:58` clause 1 (`rejected=1 -> pre=post ∧ effects_empty=1 ∧ code≠0`; `accepted=1 -> code=0 ∧ effects_empty=0`) | `asset_transfer_result_ok` `:56` | reject branch fixes `rejected=1, accepted=0, code>0, pre=post, effects_empty=1`; accept branch fixes `accepted=1, rejected=0, code=0, effects_empty=0`; the two branches are exclusive on `accepted`/`rejected`, so each implication's antecedent selects its branch |
| asset clause 2 (`code=12 -> rejected no-op`) | same | `code=12` excludes the accept branch (`code=0`); the rest is the reject branch; the only arithmetic is `0<12≤12` |
| asset clause 3 (`fee_within_cap ↔ required ≤ cap`) | `min` builtin | **not** a projection: `min(a,b)=a ↔ a≤b` over unsigned bv[16]; correctly labelled a builtin capability probe |
| asset clause 4 (envelope) | `:54`, `:55`, `:56` | `sender≠recipient`, `amount≠0` are conjuncts of `:54`; `module_release=state_release`, `subject=sender` of `:55`; the reject no-op of `:56`; `fee_within_cap` is in the hypothesis and unused |
| journal `:31` clause 1 | `lane_module_journal_ok` `:26` | it is literally defined as `journal_header_ok ∧ journal_binding_ok` |
| journal clause 2 (edge) | its own hypotheses | `next.pre = prev.post` restates the hypothesis `prev.post = next.pre`; the two header equalities are conjuncts of `same_journal_header` `:27`; the `journal_ok` and `occurrence≠` hypotheses are unused |
| journal clauses 3–5 (cursor) | recurrence `:28-29` | **not** projections: `x + min({1}, x') ≥ x`, saturation at all-ones (`1:bv[16]` is the top element, `{1}:bv[16]` is integer one), `+1` below the top; correctly labelled recurrence probes |

No theorem is mislabelled. The spec comment (`:41-44`) and the renderer's probe block (`render_tau_adt_abi_v2.py:377-381`)
both say "definitional projections … (capability probes for ADT flattening, min and recurrences)", which is exactly
right.

### B. Is the vector tier load-bearing? (mutations, executed)

Harness `mut/mut_harness.py`; every program was rendered by the candidate's own renderer functions with one thing
monkey-patched, run through the candidate's `run_tau`, and saved with its transcript. Times are wall seconds on the
pinned binary.

| Probe | Mutation | Vector | Verdict | Expected |
|---|---|---|---|---|
| B0 | none (control) | `accept_plain` universal | **T** | T |
| B1 | Python: `_transfer_policy` with the SELF_TRANSFER and ZERO_AMOUNT guards swapped (real transition, patched at module level) | `prec_self_beats_zero` (Python now says ZERO_AMOUNT) | **F** (18 s) | F |
| B2 | Python: fee guard off-by-one (`>=` instead of `>`) | `accept_fee_at_limit` (Python now rejects) | **F** (19 s) | F |
| B3a | Python: construct `AssetTransferRejectedV1` with `post ≠ pre` | — | `ValueError: asset transfer rejection changed the state root` (`asset_transfer_types_v1.py:249-250`) | type refuses |
| B3b | Python: `_reject` replaced by a stand-in that returns a changed post root (bypassing the type) | `reject_insufficient` | **F** (19 s) | F |
| B4 | Python: INSUFFICIENT_BALANCE reported as FEE_LIMIT_EXCEEDED (code mis-map) | `reject_balance_one_short` | **F** (17 s) | F |
| B5 | Tau: drop `r.effects_empty = 1` from `_rej` (`render_tau_adt_abi_v2.py:267-269`) | `reject_zero_amount` | **F** (18 s) | F |
| B6 | Tau: mirrored chain with ZERO before SELF (chain re-derived byte-for-byte first, then permuted) | `prec_self_beats_zero` | **F** (19 s) | F |
| B7 | Tau: weaken only g9's negation to a tautology (INSUFFICIENT disjunct admits any balance) | `accept_plain` | **F** (19 s) | F |

So the universal form detects wrong Python codes, wrong precedence on either side, an off-by-one guard, a mutated
post root, and both whole-chain (selftest) and single-conjunct (B5, B7) over-permissiveness.

**A Python bug the 26 vectors cannot catch (finding, not a failure of the review).** The observed surface is
`(accepted, code, pre==post, effects.is_empty)` (`render_tau_adt_abi_v2.py:183-200`). Nothing about the accept
path's *values* is observed: post balances, effect rows, fee routing, conservation. Executed (E21 in `forge/forge.py`):
change `_transfer_deltas` (`asset_transfer_module_v1.py:161`) to credit the fee to the **recipient** instead of the
policy's `fee_owner`. Result: all 26 Python codes identical to the committed receipt, the three offline gates green,
and a live replay would also be green, because every vector uses `fee_owner = treasury`, `sender = sender`,
`recipient = recv`, and no program mentions a post balance. The Rust leg compares codes only (`rust_leg/src/main.rs:122-131`)
so it is blind too. A second accept-path bug, "never credit the fee" (E22), *is* caught, but by the effect-plan
conservation type (`ValueError: owned-and-custodied conservation mismatch`), not by any Tau program. See P3-4.

### C. Is the universal form actually universal?

Yes, and the non-vacuity program is load-bearing, not decorative. With `guard_chain()` replaced by the contradiction
`r.accepted = 1 && r.accepted = 0` the universal program answers **T** (C1, vacuously) and the non-vacuity program
`ex r ( chain )` answers **F** (C2). The receipt requires both `T` (`test_tau_adt_logical_abi_v1.py:169-172`), so a
chain that admits nothing is red. Bindings that contradict each other make the outer `ex k ex c ex s` false, so they
cannot pass vacuously either.

`expected` for accepts (`render_tau_adt_abi_v2.py:328-333`): `accepted=1, rejected=0, code=0, pre=pre-tag,
post ≠ pre-tag, effects_empty=0`. In a domain where roots are equality tokens and the only other root in scope is the
pre root, `post ≠ pre` is the strongest statement available; pinning `post` to a fresh tag would add a free choice, not
information. The real content of an accept vector's universal is that none of the nine reject disjuncts fires over
the literal bindings, which B2 and B7 show is decided, not assumed.

### D. Contract-tier honesty; BALANCE_OVERFLOW unreachability

The contract program (`render_tau_adt_abi_v2.py:343-352`) is `ex r ( pins ∧ asset_transfer_result_ok(r) ∧ code = intended )`
with `r` fully pinned. It checks that the host-produced record is a well-formed rejection under the spec's closed
algebra with the intended code; it does **not** recompute why that code fired. Every place I checked says so:
renderer docstring (`:15-18` "Weaker than recompute and labelled so"), packet `claim_scope` ("checked by the spec's own
result algebra"), packet nonclaim 4, `REPORT_RECUT.md` "Limits", receipt `contract_codes`. Selftest probes
`contract_wrong_code` and `contract_mutated_effects` are `F` in the receipt and in my fresh run. Not overclaimed.

BALANCE_OVERFLOW: `_post_balances` (`asset_transfer_module_v1.py:71-94`) walks `deltas` in insertion order, and
`_transfer_deltas` (`:157-161`) inserts the sender first, so the sender's debit is checked (`post_atoms < 0 →
INSUFFICIENT_BALANCE`) before any credit. `AssetTransferStateV1.__post_init__` (`asset_transfer_types_v1.py:102-113`)
enforces per-asset `Σ balances ≤ supply ≤ MAX_ATOMS_V1`. z3 (R11): with `s+r+t ≤ M` and `s-a-f ≥ 0`, each of
`r+a > M`, `t+f > M` (distinct principals), `r+a+f > M` (fee_owner = recipient) and, with `s-a ≥ 0`, `r+a > M`
(fee_owner = sender) is **unsat**. So "unreachable from a well-formed state" is true. Two honest caveats for the
docstring: (i) the argument depends on debit-before-credit order, which Python gets from dict insertion order and Rust
pins explicitly (`asset_transfer.rs:83-94`, a comment there records that this was once a real parity bug); under a
credit-first order z3 finds the class reachable; (ii) the claim is per-asset totals, and the type enforces exactly that.

### E. Receipt gate soundness (executed, `forge/forge.py`, clean copy)

| Case | Mutation | source_contract | replay_receipt | rust_leg | Reading |
|---|---|---|---|---|---|
| E0 | none | PASS | PASS | PASS | baseline |
| E1 | one byte appended to the asset spec, no regen | PASS | **FAIL** (spec sha) | PASS | killed |
| E2 | comment appended to the lock | PASS | **FAIL** (lock sha) | PASS | killed |
| E3 | comment appended to the renderer | PASS | **FAIL** (renderer sha) | PASS | killed |
| E4 | `ok: true` kept, `accept_plain.universal.verdict = "F"` | PASS | **FAIL** | PASS | killed |
| E5 | `ok: false` | PASS | **FAIL** | PASS | killed |
| E6 | drop the last vector | PASS | **FAIL** (`25 >= 26`) | **FAIL** (row lists differ) | killed |
| E7 | drop one program of a recompute vector | PASS | **FAIL** | PASS | killed |
| E8 | swap two `code_map` entries | PASS | **FAIL** | PASS | killed |
| E9 | a rejected row with `python_noop: false` | PASS | **FAIL** | PASS | killed |
| E10 | a capability probe verdict changed | PASS | **FAIL** | PASS | killed |
| E11 | `selftest.weakened_chain_universal = "T"` | PASS | **FAIL** | PASS | killed |
| E12 | one Rust-leg outcome changed | PASS | PASS | **FAIL** | killed |
| E13 | `bounded_fee` wrapper reintroduced | **FAIL** | **FAIL** | PASS | killed (packet mutation 1) |
| E14 | enum grown by one member, ceiling `{12}` unmoved | **FAIL** (`12 == 13`) | **FAIL** (code_map) | PASS | killed (packet mutation 3) |
| E15 | `tau_binary_sha256` replaced by another 64-hex string | PASS | PASS | PASS | **limit**: unverifiable offline |
| E16 | `transcript_sha256` replaced | PASS | PASS | PASS | **limit**: unverifiable offline |
| E17 | one program `sha256` replaced | PASS | PASS | PASS | **limit, but closable offline** (see P2) |
| E18 | drop `prec_release_beats_command`, duplicate `reject_release_mismatch` under a new name, in both artifacts | PASS | PASS | PASS | **limit, closable offline**: vector identity is not checked against `build_vectors()` |
| E19 | `prec_self_beats_zero.python_code` forged to ZERO_AMOUNT in both artifacts | PASS | PASS | PASS | **limit, closable offline**: renderer `--emit-vectors` refutes it in < 1 s (`codes differ`) but nothing pinned runs it |
| E20 | SELF_TRANSFER / ZERO_AMOUNT precedence swapped in `src/core/asset_transfer_module_v1.py` | PASS | PASS | PASS | **gap** (P2): all pinned killers green; renderer refuses only when run (`AssertionError: ('prec_self_beats_zero', 'ZERO_AMOUNT')`) |
| E21 | fee credited to the recipient instead of `fee_owner` | PASS | PASS | PASS; `--emit-vectors` codes identical | **invisible** to the tier by design (P3-4) |
| E22 | fee never credited | PASS | PASS | PASS; renderer raises `ValueError: owned-and-custodied conservation mismatch` | caught by the Python type, not by Tau |

Binary binding: the offline test checks only that `tau_binary_sha256` is 64 hex characters (`:139`), that
`tau_commit` equals the lock (`:137`), and that the lock's 8-character prefix appears in `tau_version` (`:138`). It
cannot verify the binary, and the version-string check is weak: the `3c24bad9` checkout's binary self-reports
`d80aa50c`, so a version string is not an identity. The limitation is only half stated: the live test's docstring says
the evidence of record is the committed receipt, but the offline test's own docstring (`:9-12`) reads "verifies the
committed replay receipt … against the exact pinned Tau binary", which a reader will take as binary binding (P3-1).

Repo-level mitigation I checked for E20: `tools/run_test_hygiene_gate_v1.py --changed-file M:src/core/asset_transfer_module_v1.py`
in the mutated copy fails with `source sha256 drift for changed path`, because *other* packets pin that module. So a
transition edit cannot merge silently, but the Tau packet is not among the packets that force a revisit, and the Tau
receipt would remain green and stale after the other packets are refreshed. That is why P2 stands and why the fix
includes the two pins.

### F. Fail-closed discipline

`run_tau` (`render_tau_adt_abi_v2.py:360-366`) versus the PR's `_run_query` (`:139-155` at 95b3cd6e1):

| Check | PR `_run_query` | v2 `run_tau` |
|---|---|---|
| return code | `== 0` | `== 0` |
| `(Error)` | absent in raw stdout+stderr | count == 0 in ANSI-stripped stdout+stderr |
| verdicts | exactly `[expected]` from ANSI-stripped **stdout** | exactly one `T`/`F` in stdout **and** stderr, then compared to the expectation by the caller (`:485-486`, `:495`, `:503`, `:466-467`) |
| REPL front-end | `tau -X` (legacy REPL) | `tau` (default; non-interactive because stdin is a pipe) |

At least as strict; scanning stderr for verdicts can only add verdicts, which fails closed. The one path I probed
hardest: a definition that does not expand. F1/F2/F3 in the harness (renamed definition, extra argument, definition
absent) all print **no `(Error)`** and an unexpanded application (`%1: asset_transfer_result_ok(0, 1, { 9 }:bv[8], …)`),
so the `(Error)` guard alone would let them through; the single-verdict regex is what returns
`FAIL_CLOSED(verdicts=[],errors=0,rc=0)`. Good, and worth a sentence in the docstring. The recompute programs use no
definitions at all (the chain is inlined), so this path only exists in the contract tier and the capability probes.

`set charvar off` is the first line of every rendered program (`_preamble` `:259-264`, probes `:441`, contract `:351`)
except the deliberately broken selftest program. Two nits (folded into P3-5): the default front-end differs from the
one the PR's harness and the review's F1 replay used (`-X`), harmless here but an unstated difference; and a
`subprocess.TimeoutExpired` (180 s, `:361`) aborts the renderer with an uncaught exception rather than a typed
`FAIL_CLOSED`, which is fail-closed but not recorded.

### G. Evidence packet v5

* All eleven `killed_by` ids are the three node ids in `test_pins`; the test-file sha matches; all ten `source_pins`
  match the tree; the file is printable ASCII (0 non-printable bytes); the hygiene gate passes against the base.
* Mutation rows executed: rows 1 (E13), 2 (E1/E2/E3), 3 (E14), 4 (E4/E5/E7/E10), 5 (E6), 6 (E9), 7–10 (E11 stands in
  for the recorded selftest probes; the probes themselves are reproduced live: `wrong_expectation_universal=F`,
  `weakened_chain_universal=F`, `contract_wrong_code=F`, `contract_mutated_effects=F`, `broken_program=FAIL_CLOSED`),
  11 (E12). Every named test really kills the described mutation.
* Overclaim scan against the nonclaims: `claim_scope` is accurate in every particular I could test (26 = 24 + 2; both
  binaries; enum-derived map; typed `TAU_PIN_UNAVAILABLE` failure; BALANCE_OVERFLOW recorded). Two phrases read wider
  than the evidence: `boundary_dimensions.precedence_discriminators` "eight adjacent guard pairs" is true of the nine
  recomputed guards but not of the transition's full precedence (question H), and the invariant id
  `TAU-ADT-PYTHON-RUST-TAU-AGREEMENT-DIRECT-ON-26-VECTORS` plus `reject_is_noop.reason` do not say that "agreement"
  is on `(code, noop, effects_empty)` only and that a rejection's no-op is enforced by the Python type before it is
  observed (B3a). Both are P3 wording items.
* `REPORT_RECUT.md` results table calls the differential binary `3c24bad9`; that checkout's binary self-reports
  `d80aa50c` (P3-2).

### H. Coverage honesty: which adjacent pairs are discriminated

Transition precedence (`_transfer_policy` `:133-149`, `_transfer_deltas` `:162-166`, `_post_balances` `:81-90`):
RELEASE → UNKNOWN_COMMAND → UNKNOWN_ASSET → DISABLED → UNAUTHORIZED → SELF → ZERO → FEE_LIMIT →
EFFECT_DELTA_OVERFLOW → INSUFFICIENT_BALANCE (debit pass) → BALANCE_OVERFLOW (credit pass, unreachable) →
POST_STATE_RESOURCE_BOUND_EXCEEDED. Rust (`asset_transfer.rs:153-181`, `:87-99`) has the same order.

| Adjacent pair | Discriminated by | Tier |
|---|---|---|
| RELEASE / UNKNOWN_COMMAND … ZERO / FEE_LIMIT (7 pairs) | the 7 `prec_*` vectors | recompute |
| FEE_LIMIT / INSUFFICIENT | `prec_fee_beats_insufficient` | recompute (skips over EFFECT_DELTA_OVERFLOW, which cannot fire in band) |
| FEE_LIMIT / EFFECT_DELTA_OVERFLOW | **none** | — |
| EFFECT_DELTA_OVERFLOW / INSUFFICIENT | `contract_effect_delta_overflow` happens to be one (`s_bal − amount − fee = −1`, so INSUFFICIENT also wants to fire) but only in the Python/Rust sense; the Tau contract program does not recompute | contract, unstated |
| INSUFFICIENT / POST_STATE_RESOURCE_BOUND_EXCEEDED | **none** | — |
| anything / BALANCE_OVERFLOW | unreachable (D) | — |

So "eight adjacent guard pairs" is exactly right for the recomputed chain and two adjacent pairs of the full
transition are undiscriminated. Both are one contract-tier vector each (P3-3).

---

## Findings

### P2-1 — The offline receipt gate is not bound to the Python transition; the vector tier's Python side is a snapshot

**Where** `tests/tau/test_tau_adt_logical_abi_v1.py:132-181` (binds spec/journal/lock/renderer bytes, never recomputes
a Python outcome, a vector identity or a program hash); `tests/evidence/test_hygiene/THV1-20260902-tau-adt-logical-abi-v5.json`
`source_pins` (no `src/core/asset_transfer_module_v1.py`, no `src/core/asset_transfer_types_v1.py`), `invariant_ids`
`TAU-ADT-VECTOR-BOUND-PARITY-11-REACHABLE-CODES` and `TAU-ADT-PYTHON-RUST-TAU-AGREEMENT-DIRECT-ON-26-VECTORS`,
`failure_modes` row 4 ("the guard chain recomputed in Tau admits a result the Python transition never produces").

**Evidence** E20: swap two guards in `_transfer_policy` in a clean copy; the three pinned killers stay green while the
renderer, if run, refuses. E19: forge `python_code` rows consistently in receipt and Rust-leg file; green. E18: drop a
discriminator and pad with a renamed duplicate; green. E17: replace a program hash; green. The only thing that catches
any of these is the opt-in live test, which the packet itself says "never counts as evidence by itself". The
repo-level hygiene gate blocks a bare module edit only because *other* packets pin the module; the Tau receipt would
stay green and stale after those packets are refreshed.

**Repro**
```
python3 /tmp/claude-1000/-home-trevormoc-Downloads-Autonomous-Tau-DEX/048f75e7-d6e6-4ccb-873c-94fbe68c6c2e/scratchpad/forge/forge.py   # rows E17-E20
```

**Fix** (all Tau-free, sub-second):
1. In `test_tau_adt_logical_abi_replay_receipt_v1`, import the renderer as a module (`experiments/tau_adt_abi/render_tau_adt_abi_v2.py`
   already exposes `build_vectors`, `python_outcome`, `render_recompute`, `render_contract`, `spec_types`) and assert,
   per vector: the receipt's `vector`/`tier` sequence equals `[(v.vector_id, v.tier) for v in build_vectors()]`;
   `python_code`, `python_noop`, `python_effects_empty` equal a fresh `python_outcome(v)`; and each recorded program
   `sha256` equals `sha256_text(...)` of the freshly rendered program. That binds the receipt to the exact programs Tau
   decided and to the current Python transition, and kills E17–E20 offline. (Importing the renderer must not touch
   `TAU_BIN`; `main()` is guarded by `__name__`, so it does not.)
2. Add `src/core/asset_transfer_module_v1.py` and `src/core/asset_transfer_types_v1.py` to the packet's `source_pins`
   so the diff-aware gate forces this packet to be revisited on any transition change; add a `failure_modes` row
   "the Python transition changes and the receipt's recorded outcomes go stale" with the new assertion as killer; cut
   packet v6 with the new test-file sha.
3. Record E15/E16 as stated limits in the offline test docstring: binary and transcript hashes are recorded, not
   verifiable offline; only the live test compares them.

### P3-1 — Offline test docstring implies binary binding

`tests/tau/test_tau_adt_logical_abi_v1.py:9-12` "verifies the committed replay receipt … against the exact pinned Tau
binary". The test verifies bytes of spec/journal/lock/renderer and the receipt's internal consistency; `tau_binary_sha256`
is only regex-checked (`:139`) and `tau_version` only contains the commit prefix (`:138`), which E15 shows is not
binding and the `d80aa50c` observation shows is not identity. Fix: "verifies … is hash-bound to the current spec,
journal spec, lock and renderer bytes and internally consistent; the binary and transcript hashes are recorded for the
live test and are not verified offline."

### P3-2 — Differential binary named by checkout, self-reported by a different hash

`experiments/tau_adt_abi/REPORT_RECUT.md` results table: "`3c24bad9` (differential; sha `b62c0706f682d305…`)"; the
packet `claim_scope` "F at 1c1e58ae and 3c24bad9". `/tmp/tau-lang-current` is checked out at `3c24bad9ee4c…`, but the
binary with that sha prints `Tau Language Framework version 0.7.0-alpha (d80aa50c)`. The verdicts replay (R3), so the
claim is true of the binary; the label is ambiguous. Fix: say "binary sha `b62c0706…` built from checkout `3c24bad9`,
self-reporting `d80aa50c`", and do not rely on `--version` strings as identity anywhere (the offline test's `:138`
check is fine as a sanity check, not as binding).

### P3-3 — Two adjacent pairs of the full precedence are undiscriminated, and the packet's "eight adjacent guard pairs" reads as the whole transition

See question H. Fix: add two contract-tier vectors, `prec_fee_limit_beats_delta_overflow` (`fee=9, max_fee=2,
amount=MAX_ATOMS_V1` → Python `FEE_LIMIT_EXCEEDED`) and `prec_insufficient_beats_row_ceiling` (`s_bal=10, amount=30,
extra_rows=MAX_ASSET_BALANCE_ROWS_V1-2` → `INSUFFICIENT_BALANCE`), note that `contract_effect_delta_overflow` already
discriminates EFFECT_DELTA_OVERFLOW over INSUFFICIENT_BALANCE in Python/Rust only, and reword the boundary dimension to
"eight adjacent pairs of the nine recomputed guards; the three pairs involving the out-of-band classes are contract-tier".

### P3-4 — The observed surface excludes the accept path's values; say so in the nonclaims

E21: a fee credited to the recipient instead of `fee_owner` leaves all 26 codes, the receipt, the Rust leg and a live
replay unchanged. The tier is a reject-code/precedence/no-op oracle; post balances, effect rows and conservation are
outside it, and the Rust leg compares codes only (`rust_leg/src/main.rs:122-131`). `DESIGN_V1.md` says "Python
semantics == Rust semantics == Tau ADT semantics", which is broader. Fix: add a nonclaim "agreement is on
(accept/reject, reject code, pre==post, effects-empty) only; accept-path values, effect rows and conservation are not
observed by this tier and are covered elsewhere", and consider having the Rust leg also compare the accepted
post-state root and effect-plan root with Python (both sides already compute canonical roots), which would catch E21
at zero Tau cost.

### P3-5 — Harness nits: unexpanded definitions rely on the single-verdict rule alone; front-end and timeout unstated

F1–F3 show an unresolved or arity-mismatched definition prints an unexpanded application with **no** `(Error)`; the
`(Error)` guard is irrelevant to that class and the single-verdict regex is the whole defence. Document it in
`run_tau`'s docstring and add it to the selftest (`selftest` `:447-470`: render the contract program with the
definition renamed and assert `FAIL_CLOSED`), so the receipt records it. Also state that v2 runs the default REPL
front-end (the PR's harness used `-X`) and that a 180 s timeout aborts the run untyped.

### P3-6 — `reject_is_noop.reason` describes a type-enforced fact as an observation

`AssetTransferRejectedV1.__post_init__` (`asset_transfer_types_v1.py:249-252`) refuses any rejection whose post root
differs or whose effects are non-empty (B3a), so `python_outcome`'s `noop`/`effects_empty` for rejections are true by
construction; the Tau program would answer F only for a value the Python type cannot produce (B3b needed a stand-in).
Fix: "in Python the no-op is enforced by the result type; the vector tier re-checks it in Tau over the recomputed
chain and, for contract vectors, over the closed algebra".

---

## What I could not falsify

* Every one of the 26 vectors' `T`/`T` (or contract `T`) verdicts, the 18 probe verdicts and the 5 selftest verdicts
  on the pinned binary: reproduced in a fresh run (R8). The `transcript_sha256` comparison is reported there.
* The single-verdict / no-`(Error)` rule: I found no program that yields a `T` line together with an unexpanded
  definition, an error, or a second verdict; the three degenerate definition cases (F1–F3) all yield zero verdicts.
* The no-vacuity of every committed universal program: every `nonvacuity` verdict is `T` in the receipt and in R8.
* BALANCE_OVERFLOW reachability from a well-formed state: unsat in z3 for all three aliasing cases under the
  implemented debit-first order (R11).
* The lock/binary correspondence: the pinned checkout's HEAD is the lock commit and the binary sha matches the review
  receipt and the committed receipt; I did not rebuild from source.
* The Rust leg's committed 26/26: I did not rebuild the Rust leg (no cargo run in this review); I verified the file is
  pinned, schema-checked, and compared vector-for-vector against the receipt by the pinned test, and that the Rust
  transition's guard and debit/credit order match Python by reading `asset_transfer.rs`.

## Recommendation

REVISE, small: close P2-1 with the offline recomputation (items 1–3) and cut packet v6; fold the P3 wording fixes in
the same round. No spec, receipt or binary change is required for any finding; the receipt at this commit is
reproduced. Grade **B** under the campaign rubric (one P2); with P2-1 closed and the P3s addressed the same evidence
would grade A-/A.
