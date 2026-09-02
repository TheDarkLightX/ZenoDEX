# Independent review (Opus 5) — Tau ADT logical ABI re-cut of PR #534

**Subject** branch `codex/tau-adt-logical-abi-recut-20260902`, head
`946d5782f8a9679d39fdc51be14e6af788d0cfa0` (8 single-parent commits on PR #534's head `95b3cd6e1568`).
**Reviewer** Opus 5, independent of the author and of the Fable 5.1 reviewer whose receipt is the subject's
first commit. Read-only throughout.
**Review worktrees** `/tmp/zenodex-tau-recut-review-opus` (clean detached checkout at the head) and
`/tmp/opus-tau-mut` (a second detached checkout used only for mutation; restored after every experiment).
The subject worktree `/tmp/zenodex-tau-adt-recut-20260902` was not modified.
**Binary** `external/tau-lang-adt-logical-abi-v1/build-Release/tau`, sha256
`4be1965b15a4a6d074e8b4b93d7134e3edcd38ebce1109550d280e724ea6d6a7`,
`Tau Language Framework version 0.7.0-alpha (1c1e58ae)`, symlinked from the subject worktree.
**Authority** NONE. Nothing here certifies anything.

---

## Verdict

**Grade: B — REVISE.**

Findings: **0 P1, 1 P2, 5 P3.**

Everything the candidate asserts, replays. I rebuilt the evidence from source and it reproduces: the full
renderer run agrees with the committed receipt in **every field but one**, the Rust leg rebuilds and emits a
byte-identical JSON, F1 reproduces exactly at the pin and its fix is verified, and every packet mutation row
I executed is a real killer. The repairs the Fable review demanded were actually made, not asserted.

The one P2 is structural rather than cosmetic: **the offline gate checks the receipt's inputs but never
recomputes any of its content.** As a result the CI-pinned evidence cannot observe a change to the
authoritative Python transition — I inverted a guard precedence in `src/core/asset_transfer_module_v1.py`
and all three pinned tests stayed green — while the packet advertises `precedence_discriminators` as a
boundary dimension and `differential` as an evidence family. The fix is one loop, costs 0.15 s, needs no Tau
binary, and I verified it both passes on the clean tree and catches that exact mutation.

---

## What replayed

| Check | Result |
|---|---|
| F1 reproduced at the pin (PR's original spec, PR's harness shape) | **yes** — `(Error) Unresolved function or predicate symbol min(b2, b1) found. Returning unsat` twice, then `%1: T`; `run_tau` returns `FAIL_CLOSED(verdicts=['T'],errors=4,rc=0)` |
| F1 fix replays clean | **yes** — both specs' `always` theorems: rc 0, 0 errors, verdict `T` |
| Full renderer re-run at the pin | 26/26 vectors, 18/18 probes, `ok: true` |
| Fresh report vs committed receipt | identical in `ok`, `schema`, `width`, `tau_commit`, `tau_version`, `tau_binary_sha256`, `spec_path`, `spec_sha256`, `journal_spec_sha256`, `lock_sha256`, `renderer_sha256`, `code_map`, `recompute_codes`, `contract_codes`, `unreachable_codes`, `selftest`, `capability_probes`, `vectors` — **differs only in `transcript_sha256`** (P3-1) |
| Rust leg rebuilt (`cargo build --release --offline`, 35 s) and re-run on freshly emitted vectors | output **byte-identical** to the committed `tests/data/tau_adt_logical_abi_rust_leg_v1.json` |
| Packet integrity | all 10 `source_pins` + 1 `test_pins` sha256 match; every `killed_by` id is in `test_pins`; 0 non-printable-ASCII bytes |
| Counts in `REPORT_RECUT.md` and the packet | all accurate: 26 vectors = 24 recompute + 2 contract, 8 `prec_*` discriminators, 18 probes, 12 distinct outcomes (11 reachable codes + ACCEPT) |

Reproduction (from a detached checkout at the head with the binary symlinked at
`external/tau-lang-adt-logical-abi-v1/build-Release/tau`):

```
python3 experiments/tau_adt_abi/render_tau_adt_abi_v2.py > fresh.json     # ~35 min under load
python3 experiments/tau_adt_abi/render_tau_adt_abi_v2.py --emit-vectors \
  | ./experiments/tau_adt_abi/rust_leg/target/release/tau_adt_abi_rust_leg
python3 -m pytest tests/tau/test_tau_adt_logical_abi_v1.py -q                # 3 passed
```

---

## A. Does the PR review hold?

**F1: yes, exactly.** Running the PR's original spec (`git show 95b3cd6e1:src/tau_specs/recommended/asset_transfer_adt_contract_v1.tau`)
through the PR's own preamble/`valid` construction against the pinned binary produces two
`Unresolved function or predicate symbol min(b2, b1)` error lines and still prints `%1: T`. The fixed spec
(`fee_within_cap(required, cap) := (min(required:bv[16], cap:bv[16]) = required:bv[16]).`) answers `T` with
zero errors, and the journal spec does too. I also reproduced the minimal form: any
`w(a, b):bv[16] := min(a, b).` wrapper reproduces the failure, confirming the review's root cause (the return
annotation is dropped, `min`'s arguments arrive untyped) rather than a defect in `min`.

**F3: correct, clause by clause.** I checked all ten rows of the review's projection table against the two
spec files. Every conclusion listed is a literal conjunct of the predicate in its own hypothesis, modulo the
one case analysis that `asset_transfer_result_ok`'s disjunction forces (`rejected = 1` excludes the accept
branch because that branch fixes `rejected = 0`). Nothing is mislabelled. The two theorems the review calls
genuine really are: `min(a,b) = a <-> a <= b` over `bv[16]` is a fact about the builtin, and
`replay_cursor`'s `x + min(1, ~x)` recurrence saturating at all-ones is a fact about the recurrence. The
table is not exhaustive at the sub-clause level — the always block's `(r.accepted = 1) -> (r.effects_empty = 0)`
conjunct is not listed separately — but it is also a projection, so the classification does not change.

## B. Is the vector tier load-bearing?

**Yes, on both sides.** Mutating the real Python transition and re-rendering:

| Mutation of `src/core/asset_transfer_module_v1.py` | Observed | `universal` | `nonvacuity` |
|---|---|---|---|
| none (baseline, `prec_self_beats_zero`) | `SELF_TRANSFER` | T | T |
| swap the `SELF_TRANSFER` / `ZERO_AMOUNT` guards in `_transfer_policy` | `ZERO_AMOUNT` | **F** | T |
| `UNKNOWN_ASSET` guard returns `DISABLED_ASSET` | `DISABLED_ASSET` | **F** | T |

A third intended mutant — make `_reject` return a changed `post_state_root` — **cannot be built**:
`AssetTransferRejectedV1.__post_init__` (`src/core/asset_transfer_types_v1.py:249-252`) raises
`asset transfer rejection changed the state root`, and the next line raises on non-empty effects. See P3-5.

**Mutating the Tau side.** On an unmutated Python oracle, targeting the branch that actually fires for
`reject_self_transfer` (the `SELF_TRANSFER` disjunct of `guard_chain()`):

| Mutation of the rendered guard chain | `universal` | `nonvacuity` |
|---|---|---|
| none (baseline) | T | T |
| drop `r.post_state_root = s.state_root` from the firing branch | **F** | - |
| drop `r.effects_empty = 1` from the firing branch | **F** | - |
| emit reject code 7 instead of 6 in the firing branch | **F** | - |
| make the firing branch unreachable (negate its guard) | T (vacuous) | **F** |

So an over-permissive chain is visible, a wrong code is visible, and a chain that admits nothing is caught by
the companion program rather than passing as a vacuous T.

One nuance worth recording, because it cost me two wasted runs: a mutation of a chain branch that does *not*
fire for the vector under test survives, as it must. I checked that this is not a coverage gap — each of the
ten branches (nine reject classes plus accept) has at least one vector that fires it, so every branch's
result clause is exercised somewhere in the set.


**A Python bug the 26 vectors cannot catch.** The abstract Result has six members
(`accepted, rejected, reject_code, pre_state_root, post_state_root, effects_empty`) and no balance or effect
content. So route the transfer fee to the recipient instead of `policy.fee_owner`:

```
-    deltas[policy.fee_owner] = deltas.get(policy.fee_owner, 0) + policy.transfer_fee_atoms
+    deltas[command.recipient] = deltas.get(command.recipient, 0) + policy.transfer_fee_atoms
```

Conservation still holds, so nothing raises. Measured: **0 of 26 vectors change their abstract outcome and
0 of 26 Tau programs change a single byte**, so every verdict stays T by construction. The repo's own
`tests/core/test_asset_transfer_refinement_v1.py` catches it (13 failures), so this is a scope statement
about the vector tier, not a hole in the repo. It is not stated in the packet's nonclaims (P3-4).

## C. Is the universal form actually universal?

**Yes, and the non-vacuity program is genuinely load-bearing.** Measured on `reject_self_transfer`:

| Program | `universal` | `nonvacuity` |
|---|---|---|
| as rendered | T | T |
| guard chain replaced by an unsatisfiable one | **T (vacuous)** | **F** |

So the universal alone would pass vacuously and only the companion program prevents it. The outer
`ex k ex c ex s` cannot hide a vacuity: an unsatisfiable binding set makes the whole program `F`, not `T`.

**`expected` for accepts is the strongest statement the tag domain allows.** The accept clause says
`post_state_root != {1}` (the pre-state tag). I tried strengthening it to `post_state_root = {2}` on
`accept_plain`: the universal answers **F**, because the chain's accept branch only constrains the post root
to differ from the pre root, so results with post tag 3, 4, ... are admitted. Pinning a specific post tag is
therefore unsound in this abstraction, and `!= pre` is maximal. This matches the packet's nonclaim that roots
are equality tokens rather than hashes.

## D. Contract-tier honesty

**Not weaker than claimed.** The contract program is
`ex r ( pins && asset_transfer_result_ok(r) && expected_code )` where `pins` fixes all six members to
literals, so the existential ranges over exactly one candidate and cannot fail open. That it checks the
spec's closed algebra over a host-produced record rather than recomputing a guard chain is stated
consistently in three places: the renderer docstring ("Weaker than recompute and labelled so"),
`REPORT_RECUT.md:58`, and the packet nonclaim about "two by contract over host-produced records". I found no
docstring, packet string or receipt field that overstates it.

**`BALANCE_OVERFLOW` really is unreachable from a well-formed state.** `AssetTransferStateV1.__post_init__`
(`:111-113`) enforces `sum(balances[asset]) <= supply`, and `AssetSupplyV1.__post_init__` enforces
`supply <= MAX_ATOMS_V1`. In `_post_balances` the sender's row is always first in the `deltas` dict (the
recipient and fee-owner entries are inserted or merged after it), so `INSUFFICIENT_BALANCE` fires before any
credit is checked and therefore `amount + fee <= sender_balance`. Hence
`recipient_balance + amount <= recipient_balance + sender_balance <= total <= MAX_ATOMS_V1`. I also tried to
break it empirically — recipient at `MAX-1` with the sender paying its whole balance, a 50/50 split with a
maximal amount, `fee_owner = recipient`, and an amount at `2^127-1` — and every case accepted; the one
forged state that would reach the ceiling is rejected by `__post_init__` with "account balances exceed
supply". The `UNREACHABLE_CODES` justification string is accurate, though it omits the
insufficient-balance-first ordering that the argument needs.

## E. Receipt-gate soundness

Every attack the packet claims to stop is stopped. Measured against
`tests/tau/test_tau_adt_logical_abi_v1.py`:

| Attack | Result |
|---|---|
| edit one byte of the asset spec | **red** |
| set a vector's program verdict to `F` | **red** |
| forge `ok: true` and `parity: true` alongside a verdict `F` | **red** |
| drop the `reject_self_transfer` vector | **red** |
| change the code map | **red** |
| set `ok: false` | **red** |
| reintroduce the `bounded_fee` wrapper in the spec | **red** |
| reorder two `AssetTransferRejectCodeV1` members | **red** |
| grow the enum to 13 without moving the spec ceiling | **red** |
| record a rejected vector as `python_noop: false` | **red** |
| record the weakened-chain selftest as `T` | **red** |
| record the broken-program selftest as `T` | **red** |
| a Rust-leg outcome differing from the receipt | **red** |

Attacks the packet does not claim to stop, which succeed:

| Attack | Result |
|---|---|
| replace every `programs[*].sha256` with 64 zeros | **green** (P2-1) |
| change the authoritative Python transition | **green** (P2-1) |
| replace `transcript_sha256` with garbage | **green** (P3-1) |
| replace `tau_binary_sha256` with garbage | **green** (P3-2) |
| inject a fabricated `capability_probes` row whose verdict equals its expectation | **green** |

The receipt is bound to the binary only through the lock: the offline test checks
`receipt["tau_commit"] == lock["commit"]` and that the 8-hex prefix appears in `tau_version`. It never reads
the binary. That limitation is not stated (P3-2).

## F. Fail-closed discipline

**`run_tau` is at least as strict as the PR's `_run_query`, and in one respect stricter.** Both require
`rc == 0`, exactly one `T`/`F` verdict, and no `(Error)`. `run_tau`
(`experiments/tau_adt_abi/render_tau_adt_abi_v2.py:359-367`) strips ANSI *before* matching `(Error)`, whereas
`_run_query` matched the raw transcript and only worked because the engine happens to print the message
twice, the second time uncolored. Anything unexpected returns a `FAIL_CLOSED(...)` string that can never
compare equal to `"T"`.

`set charvar off` is emitted by `_preamble` for every recompute and contract program and by
`capability_probes` for every probe. The only program without it is the deliberately malformed
`broken_program` selftest, which must fail closed anyway.

**No path where an unexpanded definition counts as T.** I probed four shapes; all three that matter fail
closed:

| Program | Result |
|---|---|
| F1's broken-min program | `FAIL_CLOSED(verdicts=['T'],errors=4,rc=0)` |
| minimal `w(a,b):bv[16] := min(a,b)` wrapper | `FAIL_CLOSED(verdicts=['T'],errors=4,rc=0)` |
| undefined predicate in a falsifying position (`undefined_p(x) -> x != x`) | `FAIL_CLOSED(...errors=2...)` |
| misspelled `asset_transfer_result_ok_TYPO` in the contract-tier shape | `FAIL_CLOSED(...errors=2...)` |
| undefined predicate whose conclusion is trivially true (`undefined_p(x) -> x = x`) | `T`, 0 errors — but `T` is the *correct* answer for `anything -> true`, so this is not a fail-open |

The recompute tier is structurally immune to the F1 class anyway: those programs contain no user-defined
predicates at all, only the three `type` declarations plus fully inlined formulas.

`run_tau` omits the `-X` (`--legacy-repl`) flag the PR harness passed, so it drives the FTXUI REPL instead of
the legacy one. I compared both invocations on a true statement, a false statement and an unresolved-symbol
program: verdicts, error counts and return codes are identical in all three. The omission is benign, but it
is an undocumented divergence from the harness the review praised.

## G. Evidence packet v5

Clean. All 10 `source_pins` and the 1 `test_pins` sha256 match the files at this head; every `killed_by`
node id appears in `test_pins`; the file is printable ASCII only. I executed 7 of the 11 mutation rows (rows
1, 3 in both its senses, 6, 8, 10, 11) plus the two receipt-forging rows, and **every one is a real killer**
— see the table in section E.

The `nonclaims` block is unusually honest and I could not find a string in it that overstates the artifacts.
In particular it correctly says the specs' theorems are definitional projections, that the guard precedence
is hand-mirrored rather than derived, that the Rust leg does not execute Tau, and that `BALANCE_OVERFLOW` is
uncovered. Two strings elsewhere in the packet do overstate, both covered by findings: the
`precedence_discriminators` point (P2-1) and `reject_is_noop: applied` (P3-5).

## H. Coverage honesty

**All eight adjacent pairs among the nine recomputed guards are discriminated**, one vector each
(`prec_release_beats_command` through `prec_fee_beats_insufficient`). The packet's "eight adjacent guard
pairs" is exact.

**Three adjacent pairs in the real twelve-code precedence are not discriminated**, and all three are
constructible. Measured winners:

| Undiscriminated pair | Winner |
|---|---|
| `FEE_LIMIT_EXCEEDED` vs `EFFECT_DELTA_OVERFLOW` | `FEE_LIMIT_EXCEEDED` |
| `EFFECT_DELTA_OVERFLOW` vs `INSUFFICIENT_BALANCE` | `EFFECT_DELTA_OVERFLOW` |
| `INSUFFICIENT_BALANCE` vs `POST_STATE_RESOURCE_BOUND_EXCEEDED` | `INSUFFICIENT_BALANCE` |

These are exactly the seams between the recompute tier and the contract tier (P3-3). Pairs involving
`BALANCE_OVERFLOW` are vacuous because the code is unreachable.

---

## Findings

### P2-1 — The offline gate checks the receipt's inputs but never recomputes its content

`tests/tau/test_tau_adt_logical_abi_v1.py:132-181`.

The gate hash-binds the receipt to the asset spec, the journal spec, the lock and the renderer
(`:143-147`), and validates verdicts, coverage and the code map. It never recomputes anything the receipt
*contains*. Two consequences, both measured:

**(a) The `programs[*].sha256` fields are decorative.** `:173` only checks
`_SHA_RE.fullmatch(program["sha256"])`. Replacing all 52 program hashes with 64 zeros leaves the suite green.

**(b) The pinned evidence cannot observe a change to the authoritative Python transition.** The receipt's
`python_code`, `python_noop` and `python_effects_empty` are never re-derived, and
`src/core/asset_transfer_module_v1.py` is not in the receipt's hash binding nor in the packet's
`source_pins`. Inverting a real guard precedence leaves all three pinned tests passing:

```
cd <checkout>
# in src/core/asset_transfer_module_v1.py:144-147, swap the SELF_TRANSFER and ZERO_AMOUNT guards
python3 -m pytest tests/tau/test_tau_adt_logical_abi_v1.py -q     # 3 passed  <-- should be red
```

The receipt is now stale: `prec_self_beats_zero` records `SELF_TRANSFER` while the transition returns
`ZERO_AMOUNT`. Only the opt-in `ZENO_TAU_ADT_LIVE=1` path notices, via the renderer's
`assert o.code == v.intent` (`render_tau_adt_abi_v2.py:489`). Meanwhile the packet's
`boundary_dimensions.precedence_discriminators` asserts "a precedence drift between implementations surfaces
as a Tau parity F, not as a fixture edit", and `evidence_families` lists `differential`. Under the pinned
tests a precedence drift surfaces as nothing.

**Fix — one loop, no Tau binary, 0.15 s.** The program text is a pure function of the spec, the enum and the
observed Python outcome, so recomputing it offline closes both (a) and (b) at once. Add to
`test_tau_adt_logical_abi_replay_receipt_v1`:

```python
sys.path.insert(0, str(ROOT / "experiments" / "tau_adt_abi"))
import render_tau_adt_abi_v2 as rr

types = rr.spec_types()
by_id = {row["vector"]: row for row in vectors}
for v in rr.build_vectors():
    o = rr.python_outcome(v)                      # re-runs the REAL transition, no Tau
    row = by_id[v.vector_id]
    assert (o.code or "ACCEPT") == row["python_code"], v.vector_id
    assert o.noop == row["python_noop"] and o.effects_empty == row["python_effects_empty"]
    if v.tier == "recompute":
        u, n = rr.render_recompute(types, v, o)
        want = {"universal": rr.sha256_text(u), "nonvacuity": rr.sha256_text(n)}
    else:
        want = {"contract": rr.sha256_text(rr.render_contract(types, v, o))}
    for key, sha in want.items():
        assert row["programs"][key]["sha256"] == sha, (v.vector_id, key)
```

I ran exactly this. On the clean head it reports 0 mismatches; under the precedence swap it reports
`('prec_self_beats_zero', 'universal', 'receipt=7e5f0c997bea', 'recomputed=0b5edd572a36')` and fails. With
this in place the packet's `precedence_discriminators` and `differential` claims become true of the pinned
evidence.

### P3-1 — `transcript_sha256` is not reproducible and is never checked

`render_tau_adt_abi_v2.py:524`, checked only by `_SHA_RE.fullmatch` at
`tests/tau/test_tau_adt_logical_abi_v1.py:140`.

Tau's `--benchmarks` is on by default, so every transcript carries wall-clock lines. Running one identical
trivial program twice gives `valid: 0.142 ms` and `valid: 0.185 ms`. This is the single field in which my
full re-run differs from the committed receipt — everything else matches exactly. The field therefore records
a value that can never be reproduced or verified, and garbage passes the offline gate.

Fix: strip timing lines before hashing (`re.sub(r"(?m)^\w+: [\d.]+ ms$", "", clean)`), or disable benchmarks
in the invocation, or drop the field. Reproduce:

```
python3 -c "import sys; sys.path[:2]=['<checkout>','<checkout>/experiments/tau_adt_abi']; \
import render_tau_adt_abi_v2 as rr; p='set charvar off\nvalid all x:bv[16] (x = x).\nquit\n'; \
print(rr.run_tau(p)[1] == rr.run_tau(p)[1])"     # False
```

### P3-2 — The pinned test's docstring claims a binding to the Tau binary that it cannot check

`tests/tau/test_tau_adt_logical_abi_v1.py:10-11` says the test "verifies the committed replay receipt
produced by `render_tau_adt_abi_v2.py` **against the exact pinned Tau binary**". The test never reads the
binary; `tau_binary_sha256` is accepted on a 64-hex regex alone, and substituting `"b"*64` leaves the suite
green. The binding that exists is to the lock's commit string, not to the binary bytes. The module docstring's
own first line ("both runnable without a Tau binary") contradicts the sentence.

Fix: reword to "against the lock's exact Tau revision" and add a nonclaim stating that
`tau_binary_sha256` and `transcript_sha256` are recorded provenance, verifiable only by the opt-in live test.

### P3-3 — Three constructible adjacent precedence pairs have no discriminator

`render_tau_adt_abi_v2.py:230-237` provides eight discriminators, all among the nine recomputed guards. The
seams to the contract tier are undiscriminated: `FEE_LIMIT_EXCEEDED`/`EFFECT_DELTA_OVERFLOW`,
`EFFECT_DELTA_OVERFLOW`/`INSUFFICIENT_BALANCE`, `INSUFFICIENT_BALANCE`/`POST_STATE_RESOURCE_BOUND_EXCEEDED`.
I constructed all three and recorded the winners (section H). The existing
`contract_effect_delta_overflow` vector sets `s_bal = MAX_ATOMS_V1`, so no second guard ever contests it.

Fix: add three contract-tier vectors, one per pair; each only needs the observed code checked against the
closed algebra, which the contract tier already does. Then say "eleven adjacent pairs" instead of eight.

### P3-4 — The abstraction's blindness to balance and effect content is not a nonclaim

The six-member Result carries no amounts, owners or effect rows, so a fee routed to the wrong owner is
invisible to all 26 programs (section B, measured: 0 of 26 programs change a byte). The nonclaims say roots
are equality tokens and identifiers are tags, but never that the vector tier cannot observe *who was paid
what*. Add: "The abstract Result records only acceptance, reject code, root equality and effect emptiness; it
cannot observe balances, effect rows, fee routing or conservation."

### P3-5 — `reject_is_noop: applied` is non-discriminating on the Python leg

The packet's reason says "a rejection that mutated state would answer F". Such a rejection cannot be
constructed: `AssetTransferRejectedV1.__post_init__` (`src/core/asset_transfer_types_v1.py:249-252`) raises
`asset transfer rejection changed the state root` and, on the next line, `asset transfer rejection carried
effects`. My third planned mutant died on exactly that. So `o.noop` and `o.effects_empty` are `True` for every
rejected vector by construction, both sides of the implication always agree, and the dimension discriminates
nothing on this leg. It is not false, but it is evidence for a property already made unrepresentable upstream.

Fix: say so in the reason, and cite the dataclass invariant as the primary evidence for the property.

### Minor notes (not findings)

- `tests/data/tau_adt_logical_abi_rust_leg_v1.json` carries no self-binding — no vector-set hash, no crate
  revision, only `schema`/`ok`/`vectors`. The packet's `source_pins` cover the Rust sources, and I did
  reproduce the file byte-for-byte from a fresh build, so this is a shape observation, not a defect.
- `assert len(vectors) >= 26` (`:164`) permits padding the receipt with extra vectors; harmless, since each
  must still carry `parity: true` and verdict `T`.
- The renderer hashes with `Path.read_text()` (locale encoding) while the test hashes bytes. Every hashed
  file is pure ASCII at this head, so the two agree; passing `encoding="utf-8"` would remove the latent
  divergence.

---

## What I could not falsify

- **The F1 diagnosis and its fix.** Reproduced at the pin from the PR's own bytes; the minimal wrapper
  reproduces it; the fixed form is clean on both specs.
- **F3's projection table.** Checked all ten rows against the spec text; every one holds, and the two
  theorems called genuine are genuine.
- **The receipt's integrity.** A full independent re-run agrees field-for-field except the one
  non-reproducible field, so the committed receipt was really produced by this renderer against this binary.
- **The Rust leg.** Rebuilt from source and re-run on freshly emitted vectors; byte-identical output. The
  crate really is the repo's `zk/global_settlement_abi_v1`, not a reimplementation.
- **`run_tau`'s fail-closed discipline.** Four unresolved-symbol shapes, all `FAIL_CLOSED`; the only `T` I
  could obtain from an undefined predicate was one where `T` is the correct answer.
- **`BALANCE_OVERFLOW` unreachability.** Argued from the two `__post_init__` bounds and the dict ordering,
  and attacked empirically from five directions.
- **The universal form's non-vacuity and maximality.** The companion program is the only thing standing
  between the design and a vacuous `T`, and it does stand there; the accept expectation cannot be
  strengthened within the tag domain.
- **The guard chain's own integrity.** Weakening the firing branch (dropping the no-op conjunct, dropping
  effect emptiness, or emitting the wrong code) answers `F` every time; making it unreachable is caught by
  the companion program. Every one of the ten branches is fired by at least one vector.
- **Every packet mutation row I executed** (7 of 11, plus 2 receipt forgeries). All real killers.
- **The eight advertised precedence discriminators.** All eight adjacent pairs among the recomputed guards
  are covered, exactly as claimed.

---

## Recommendation

**REVISE.** Land P2-1 (the offline recompute loop) and it becomes an A- artifact: that single change turns
`precedence_discriminators` and `differential` from aspirations into properties the CI-pinned evidence
actually has, and it costs 0.15 s and no Tau binary. The five P3s are wording and coverage, all cheap. There
is no P1: nothing in this candidate claims something that fails to replay, and the discipline on display —
reproducing the PR's failure before fixing it, labelling the old theorems as capability probes rather than
deleting or defending them, recording `BALANCE_OVERFLOW` as unreachable rather than manufacturing a vector,
and writing nonclaims that concede more than a reviewer would have to extract — is the right discipline.
