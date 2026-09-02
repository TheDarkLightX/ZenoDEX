# Opus independent review — C8'' (P18 repair) at S19 / P19

- **Subject S19**: `dd6d13daf9f84e95305978ffdc066749e169d9a5`
- **Packet P19**: `738b54f631bcb6bc85dff1814ff22aca40923203`
- **Worktree**: `/tmp/zenodex-formal-core-opus-c8pp` (clean, detached, nothing edited)
- **Packet schema**: `zenodex/o008-formal-cycle-evidence/v15`
- **Review date**: 2026-09-02
- **Prior receipt reviewed against**: `docs/research/reviews/ZENODEX_FORMAL_CORE_P18_OPUS_REVIEW_00453474681e.md`
  (sha256 `844bd29b13c8baf7ed56532ed9f25f944d75b6bf7d33a01cf2ac475731778952`, grade C+, 0 P1 / 4 P2 / 7 P3)

## Grade: B

**Findings: 0 × P1, 1 × P2, 5 × P3.**

C8'' is a substantially better candidate than C8'. The masking disjunction is gone and replaced
with a real reachability test built from a live transition; the closed-family escape P2-D named is
closed on **both** classes; the precedence inversion P3-a named is gone; the Rust reject-code
family now has a semantic pin that runs inside the packet's own replay gate; the packet claim
boundary and both certificate module headers now say what they mean. Every gate replays green,
the envelope is byte-clean, and the claim ceiling is byte-identical to P18.

It is held to B rather than B+ because the sentence P17 and P18 both graded P2 — *"No lane
producer is receipt-backed in the running code"* — is still in the candidate, in the pinned ESSO
model that the packet's own `esso_evidence.certificate_model` block names, and is now **mechanically
asserted by a test that runs in the packet's replay** (`esso_certificate_gate`, 24 passed). C8''
reworded three instances of that clause and left the one instance a test enforces, so the packet
block that carries the corrected wording also carries the pin to the file that contradicts it.
Two further documentation repairs (P3-c, P3-d) were applied in one twin and not the other, which
leaves the two languages saying different things about the same check.

---

## 1. Envelope (duty 1) — PASS

| Check | Result |
|---|---|
| P19 is a direct child of S19 | `git log --format='%H %P' -1 738b54f63` → parent `dd6d13daf9f84e95305978ffdc066749e169d9a5` ✓ |
| P19 is packet-only | `git diff --stat dd6d13daf 738b54f63` = `ZENODEX_O008_FORMAL_CYCLE_V1.{json,md}` only (2 files, 53+/53−) ✓ |
| S19 is a direct child of the P18 receipt | parent `1014b1f74ce957adb502aa473782428e04e9d07f` ✓ |
| Worktree clean at P19 | `git status --porcelain` empty (excluding the `external/`, `lean-mathlib/.lake` symlinks I created) ✓ |
| Subject commit / parent / tree in packet | `dd6d13daf9f8…` / `1014b1f74ce9…` / `f7aeedaaf34f…`; `git rev-parse dd6d13daf^{tree}` = `f7aeedaaf34f3589fff2d60b6d23313a6de655c1` ✓ |
| Packet schema | `v14` → `v15`, `PACKET_SCHEMA_DRIFT` re-pinned to v15, old-schema mutation row updated to `old_schema_v14` ✓ |

**Checker, both modes, at the exact packet hash:**

```
$ "$PY" tools/check_o008_formal_cycle_v1.py --root "$PWD" \
    --packet-commit 738b54f631bcb6bc85dff1814ff22aca40923203
NOREPLAY_EXIT=0   ok=True  proof_replay.status=NOT_RUN  runs=0  errors=[]  drift=[]

$ ... --replay --esso-python /usr/bin/python3 --esso-pythonpath /home/trevormoc/Downloads/ESSO
REPLAY_EXIT=0     ok=True  proof_replay.status=EXECUTED_PASS  runs=28
                  errors=[]  current_source_drift=[]  packet_admitted=True
                  stderr: empty
```

`drift: []` on the replay means the 28 replayed commands — including the re-pinned
`python_producer_gate: 27` and `rust_producer_gate: 7` — reproduce the committed packet exactly.

**Direct re-runs (independent of the replay):**

```
cargo test --locked                          exit 0; lib 15 passed; tests/global_accounting_lane_producers.rs 7 passed
                                             (53 "test result: ok" blocks, 0 FAILED)
cargo clippy --locked --all-targets -D warnings   exit 0
pytest -q tests/core/test_global_accounting_lane_producers_v1.py   27 passed
pytest -q tests/test_check_o008_formal_cycle_v1.py                389 passed, exit 0
pytest -q tests/formal/test_lean_global_claimant_custody_relation_v1.py         6 passed, exit 0
pytest -q tests/formal/test_lean_global_accounting_allocation_certificate_v1.py 6 passed, exit 0
   (the two Lean gates run strictly serially — never concurrently)
tools/check_global_settlement_canonical_manifest_v1.py --json      ok:true,
   source_closure_sha256 f7984e22d22a61c31efd9e828b9c023e84e9e41ac50a0ead9e8fbcad9b52b015 (= the re-pinned value)
tools/check_test_hygiene_v1.py --json                              ok:true, changed_path_count 0
tools/check_test_hygiene_v1.py --json --base-ref 838ec10cbe34…     ok:true, 18 changed, 11 critical paths,
   selected exactly THV1-…-claimant-backing-guard-golden-v13 / …-certificate-v10 / …-admission-v20
```

## 2. Claim ceiling, nonclaims (duties 3, 4) — INTACT, NOT MOVED

Decoding both packet JSONs and comparing key by key: `claim_ceiling`, `nonclaims`,
`lane_source_data`, `lean_evidence`, `packet_write_set` and `v1_information_loss` are **identical**
to P18. Every authority is `NONE`; `value_movement_gates_closed: 0` of `12`;
`formal_core_complete: false`; `whole_value_movement_safe: false`;
`o008_status: OPEN_EXACT_ALL_12_RECONCILIATION_MISSING`.

Only three sentences changed anywhere in the packet, and they are exactly the three the repair
claims:

- `completion_scope`: "ten closed reject codes" → "eleven closed reject codes";
- `esso_evidence.certificate_model.claim_boundary`: "no lane producer is receipt-backed in the
  running code" → "no lane producer is REGISTERED receipt-backed and none is on an acceptance path
  (an implemented, unregistered wave-B producer exists)";
- `required_sidecar.implementation.producers.asset_transfer.binding`: the same eleven-code
  correction plus an explicit enumeration of all eleven causes.

## 3. THV1 successors — PASS

`THV1-20260901-claimant-backing-guard-golden-v13.json`,
`THV1-20260901-global-accounting-allocation-certificate-v10.json`,
`THV1-20260901-o008-formal-cycle-admission-v20.json` are append-only new files. I re-hashed every
pin against the committed bytes: **73 pins (12 + 21 + 40), 0 mismatches.** The base-ref hygiene run
selects exactly these three and covers all 11 changed critical paths.

Eight new mutation rows (6 in certificate-v10, 2 in admission-v20). Every named killer collects as
a real pytest node id, and I re-derived the two load-bearing ones:

| new mutation row | killer verified |
|---|---|
| prior fragment of the wrong producer kind | `…[stale_journal_prior_kind]` — probe confirms `STALE_JOURNAL`/`"prior kind"` |
| disabled prior fragment | `…[stale_journal_prior_disabled]` — probe confirms `STALE_JOURNAL`/`"prior disabled"` |
| entitlement row ceiling exceeded | `test_receipt_backed_producer_rejects_entitlement_row_ceiling` — probe confirms `ENTITLEMENT_ROWS_NOT_CANONICAL`/`"row ceiling"` |
| shared canonical row order reordered | `test_receipt_backed_producer_preserves_the_shared_canonical_row_order` |
| Rust family drifts from Python | `test_rust_twin_reject_code_families_match_the_pinned_tuples` — 4 of 6 mutation classes killed (see P3-f) |
| drop/reorder the eleven-code family | `test_receipt_backed_reject_family_is_closed_and_ordered` |
| drop/reorder a producer reject code | `…::test_producer_reject_code_families_are_mechanically_pinned` |
| under-report the rust producer gate | `…::test_new_gate_observation_mutations_are_executed_fail[rust_producer_count]` |

Lean/manifest pin refreshes are exact: `PYTHON_CHECKER` `8d81e896…`, `RUST_TWIN` `f7452d9a…`, and
`EXPECTED_SOURCE_CLOSURE_SHA256_V1` `f7984e22…` all equal `sha256(committed bytes)`.

---

## 4. Per-finding closure table

| P18 finding | Verdict | Evidence |
|---|---|---|
| **P2-A** Rust module header stale for wave B | **CLOSED** | `zk/…/global_accounting_lane_producers.rs:1-11` now describes both waves, names `produce_asset_transfer_fragment_v1`, and states the registry keeps ASSET_TRANSFER at NO_PRODUCER. Its claim that a verifier exists is true in both languages (`…/src/lane_module_receipt_verification.rs:105`, `src/core/lane_module_receipt_verification_v1.py:240`). |
| **P2-B** the false clause survived in the packet | **PARTIAL** | 3 of 4 instances repaired. Packet `claim_boundary`, `src/core/global_accounting_allocation_certificate_v1.py:20-22`, `zk/…/global_accounting_allocation_certificate.rs:13-15` are all registry-scoped now. The fourth instance survives and is test-enforced — see **N1**. |
| **P2-C** masked disjunctive Rust terminal-root assertion | **CLOSED** | The disjunction that stood at `…/tests/global_accounting_lane_producers.rs:383-397` in P18 is gone; that site (`:375-387`) now `assert_eq!`s `ACCEPTED_INVALID` + detail `"accepted validation"` only. The reachable path moved to a lib unit test, `…/src/global_accounting_lane_producers.rs:463-598`, which builds from a real transition, sets the terminal root on port **and** journal, rebinds `private_port_root`, recomputes `receipt_root` via the newly `pub(crate)` `receipt_root`, asserts `accepted.validate().is_ok()` — so no earlier gate can fire — then `assert_eq!`s `TERMINAL_ROOT_NOT_EMPTY` + `"terminal root"`. Runs green (`…::tests::terminal_root_check_is_reachable_with_a_fully_rebound_accepted_value ... ok`). |
| **P2-D** closed-family escape (uncaught `ValueError`) | **CLOSED** | Entitlement side: explicit ceiling at `src/core/global_accounting_lane_producers_v1.py:286-292` (`ENTITLEMENT_ROWS_NOT_CANONICAL` / `"row ceiling"`), mirrored at `zk/….rs:329-337`. Controlled side: `MAX_ASSET_TRANSFER_CUSTODY_ROWS_V1` at `src/core/asset_transfer_lane_module_v1.py:50` + `:85`, and custody is a pure pass-through (`:286`, `:292`), so post custody ≤ 4096. Backstop `try/except (TypeError, ValueError)` → `FRAGMENT_INVALID` at `…producers_v1.py:342-360`; Rust gets its own `FRAGMENT_INVALID` (`…rs:451-458`) instead of reusing `ENTITLEMENT_ROWS_NOT_CANONICAL`. I re-ran both P18 escape probes: neither escapes now. Residual naming/twin divergence in **N2**. |
| **P3-a** realised Rust precedence contradicted the enum order | **CLOSED** | The fallback moved from index 7 to index 10 and the ceiling to index 7, so earlier-index always wins. Verified in both languages with four adversarial pairs (Python `/tmp/zenodex-opus-c8pp-probes/probe_precedence.py`, Rust `…/rustprobe`): `>4096 rows` → idx 7; `disabled + >4096` → idx 2; `prior kind + >4096` → idx 5; `coverage only` → idx 9. |
| **P3-b** carry-forward admitted an unemittable predecessor | **CLOSED** | `producer_kind is not RECEIPT_BACKED` → `STALE_JOURNAL`/`"prior kind"` (`…producers_v1.py:266-269`, `…rs:289-296`); `not enabled` → `"prior disabled"` (`…producers_v1.py:270-273`, `…rs:297-304`). Both P18 shapes (`REGISTERED_EMPTY_DISABLED` prior, `NO_PRODUCER` prior) now refuse in both languages, pinned by two parametrised Python cases and two Rust assertions. |
| **P3-c** "defensively unreachable" overstated | **PARTIAL** | Python corrected to "unreachable through construction here … only `object.__new__` forgery bypasses it" (`…producers_v1.py:192-195`) — accurate. The Rust twin still says "**defensively unreachable** in Python, reachable here" at `zk/….rs:235`, repeating the phrasing P18 rejected and now contradicting the corrected Python. The separate sort claim is sound: `EconomicAmountV1.key` = `(asset, owner, custody_domain)` equals `ControlledLocationRowV1.key` = `(asset, controlling_principal, control_domain)`, and the projection enforces that order, so the re-sort is a genuine no-op; `test_receipt_backed_producer_preserves_the_shared_canonical_row_order` pins it end to end (a weak test, but the claim rests on the structural argument, not the test). |
| **P3-d** "no verifier admits the journal yet (C9)" imprecise | **PARTIAL** | Fixed in the Rust **module header** (`…rs:6-10`) and the Python **function docstring** (`…producers_v1.py:221-227`: "a journal verifier exists … but this producer does not yet require it — C9a will take the witness"). Still verbatim false in the Python **module header** (`…producers_v1.py:10-11` — the exact lines P18 cited) and the Rust **function docstring** (`…rs:221-223`). Each twin got one half of the fix. |
| **P3-e** sidecar claimed ten codes, named nine | **CLOSED** | `tools/o008_formal_cycle_admission_v1.py:3079` and `:3586` (and thus the packet) now enumerate all eleven: accepted-validation, lane, disabled-lane, release, post-root, carry-forward (incl. prior kind and enabled flag), terminal-root, non-canonical-or-over-ceiling entitlements, fold-ceiling, coverage, defensive fragment-validation. Count checks out. |
| **P3-f** reject-code semantic pin was Python-only | **CLOSED** | `tests/core/test_global_accounting_lane_producers_v1.py:408-440` parses the **Rust enum declaration** and the `code()` arms and compares to the core's tuples, and also pins the Python **member names** via `ast` (closing the value-vs-name gap). This test sits in the file the packet gates at `python_producer_gate: 27` (`…admission_v1.py:1488-1491`), so a Rust-side drift now fails a replayed gate, not only a blob sha. I replayed the test's parser against six mutations: declaration reorder, member drop, wire-code rename and member rename are all **killed**; `ALL`-array drift survives (**N3**). |
| **P3-g** Python lacked Rust's custody row ceiling | **CLOSED** at the cited line | `src/core/asset_transfer_lane_module_v1.py:85` now passes `maximum=MAX_ASSET_TRANSFER_CUSTODY_ROWS_V1`, exactly the call P18 named. The deeper asymmetry at the layer Rust actually enforces (`AssetLaneStateProjectionV1`) survives — **N2**. |

**Summary: 6 CLOSED, 3 PARTIAL, 1 CLOSED-as-cited-with-residual. No finding is NOT CLOSED.**

---

## 5. New findings

### N1 (P2) — the clause P17 and P18 both adjudicated false is still asserted, by a test in the packet's own replay

`src/kernels/dex/global_accounting_allocation_certificate_v1.yaml:62-64` (`meta.notes`)
sha256 `07caf71835c5e8a6c671f4bcd967cc6c42c0ef77ba5875c56abe41265050a5a8`

```yaml
    production, settlement authority, or whole-value-movement safety. No lane
    producer is receipt-backed in the running code, so the only certificate it
    accepts today is the registered-empty one; enable_lane models the future
    receipt-backed producers, not a present capability.
```

`tests/formal/test_esso_global_accounting_allocation_certificate_v1.py:271`
sha256 `8dd91d6d037e02cb151c59baa3f2cd5647825165e01a03ccb5a721f7dacdcb16`

```python
        "No lane producer is receipt-backed in the running code",
```

— a required substring inside `test_model_source_scope_and_claim_ceiling_are_exact`.

Both files are in the packet's pinned source surface (roles `allocation_certificate_bounded_esso_model`
and `allocation_certificate_esso_replay_gate`, registered at `tools/o008_formal_cycle_admission_v1.py:135-136`),
and the gate runs in the replay as `esso_certificate_gate` (`gate_expected_passed: 24`,
`…admission_v1.py:1375-1376`).

The falsity is the one P17 adjudicated and P18 re-raised: the running code emits
`producer_kind=RECEIPT_BACKED` (`src/core/global_accounting_lane_producers_v1.py:348`,
`zk/….rs:416`). The clause's *consequent* ("the only certificate it accepts today is the
registered-empty one") is true because the registry has no receipt-backed lane; the *antecedent*
as written is false. "enable_lane models the future receipt-backed producers, not a present
capability" is now inaccurate for the same reason.

The aggravating factor is placement. The packet's `esso_evidence.certificate_model` block carries
**both** the corrected `claim_boundary` and `model_path` + `model_source_sha256` for the file that
contradicts it — the correction and the contradiction are pinned side by side in one block. And
unlike P18's instance, which was an inert string, this one is enforced: any attempt to reword the
model without also editing the test fails `esso_certificate_gate`.

**Minimal repro**

```
$ grep -rn "producer is receipt-backed in the running code" \
    src/kernels/dex/global_accounting_allocation_certificate_v1.yaml \
    tests/formal/test_esso_global_accounting_allocation_certificate_v1.py
src/kernels/dex/global_accounting_allocation_certificate_v1.yaml:64:    producer is receipt-backed in the running code, so the only certificate it
tests/formal/test_esso_global_accounting_allocation_certificate_v1.py:271:        "No lane producer is receipt-backed in the running code",

$ grep -c "no lane producer is receipt-backed in the running code" \
    docs/research/ZENODEX_O008_FORMAL_CYCLE_V1.json
0
```

I did **not** name this instance in P18 — I named the packet and the two certificate module
headers. It is the same clause and the same defect class, and a mechanical grep for
`"receipt-backed in the running code"` over the tree finds it in one step, so a repair whose stated
scope was "reword the sentence P17 adjudicated false, then re-freeze" should have caught it. A
sweep of all 42 packet source pins for `no lane (producer is|has a) receipt-backed` returns
these two files and nothing else, so the fix is bounded: reword the YAML notes, update the pinned
phrase in the gate, re-pin `model_source_sha256` and the ir hash, re-freeze.

### N2 (P3) — the twins now name different codes for the same input class, and the Rust docstring claims they cannot

`zk/global_settlement_abi_v1/src/global_accounting_lane_producers.rs:218-219`

```rust
/// `src/core/global_accounting_lane_producers_v1.py`; the check order and reject
/// codes mirror it exactly.
```

False for the class "accepted whose private-port post-state carries more than 4096 custody rows".
Rust bounds it at check 0 (`AssetTransferLaneModuleAcceptedV1::validate()` →
`private_port.validate_resource_bounds()` → `AssetLaneStateProjectionV1::validate_resource_bounds()`,
`zk/…/asset_transfer_lane_module.rs:111`, `zk/…/asset_lane_projection.rs:79-83`,
`MAX_ASSET_CUSTODY_ROWS_V1 = 4096` at `zk/…/canonical.rs:13`). Python's
`AssetLaneStateProjectionV1.__post_init__` (`src/core/asset_lane_projection_v1.py:78-83`) still
calls `_require_ordered_objects(self.custody, …)` with `maximum` defaulted to `None`, so the value
constructs and the divergence lands at check 10.

**Exploit / evidence.** Both probes build the accepted through the real transition and then rebind
every root the accepted's own validation checks — no `object.__new__`, every constructor runs.

Python (`/tmp/zenodex-opus-c8pp-probes/probe_projection_ceiling.py`):

```
A  AssetLaneStateProjectionV1 with 5000 custody rows: CONSTRUCTED (Rust MAX_ASSET_CUSTODY_ROWS_V1 = 4096 refuses this)
C  accepted rebuilt with 5000 post-custody rows: __post_init__ ACCEPTED it
D  python producer: REJECT code=FRAGMENT_INVALID detail='fragment validation'
```

Rust (`/tmp/zenodex-opus-c8pp-probes/rustprobe`, links the worktree crate by path; nothing in the
worktree edited):

```
C  accepted.validate() with 5000 port post-custody rows = Err(InvalidBounds("asset lane declared accounting-location rows"))
D  rust producer: REJECT code=ACCEPTED_INVALID detail="accepted validation"
```

Same input class, `FRAGMENT_INVALID` (index 10) vs `ACCEPTED_INVALID` (index 0). Severity is P3,
not P2: both languages *refuse*, both refusals are closed typed values, and the registry keeps
ASSET_TRANSFER at `NO_PRODUCER` so no acceptance path is reached. The defect is the docstring's
unconditional "mirror it exactly", and the underlying cause is that the P3-g repair put the ceiling
on the module **input** rather than on the **projection**, which is where Rust puts it. The clean
fix is `maximum=MAX_ASSET_TRANSFER_CUSTODY_ROWS_V1` on `asset_lane_projection_v1.py:78-83` as well;
that makes Python refuse at check 0 too and makes both languages' defensive codes symmetric.

### N3 (P3) — `ReceiptBackedProducerRejectCodeV1::ALL` is unconsumed and unpinned

`zk/global_settlement_abi_v1/src/global_accounting_lane_producers.rs:135-146`. Nothing in the crate
or its tests reads it (`grep -rn "ReceiptBackedProducerRejectCodeV1::ALL" zk/` → no hits outside the
definition; the wave-A twin is read once, at `…/tests/global_accounting_lane_producers.rs:90`). The
new P3-f test parses only the enum declaration and the `code()` arms, so `ALL` can drift silently:

| mutation of the Rust family | new pin |
|---|---|
| enum declaration reorder | **KILL** |
| drop a variant from the declaration | **KILL** |
| wire-code string rename in `code()` | **KILL** |
| member rename everywhere | **KILL** |
| drop a member from `ALL` (adjusting the length) | **PASS** |
| reorder `ALL` only | **PASS** |

(Replica of the committed test's parser run over mutated source strings; the worktree was not
modified.) Consequence is bounded because nothing consumes `ALL` — but the packet's "closed
eleven-code family" language reads as if the array were load-bearing. Either read `ALL` in the
family-closure test or delete it.

### N4 (P3) — the mirrored ceiling constants are not mechanically bound

`src/core/asset_transfer_lane_module_v1.py:50-51` declares
`MAX_ASSET_TRANSFER_CUSTODY_ROWS_V1: Final = 4096` with the docstring *"Mirrors the Rust
projection's MAX_ASSET_CUSTODY_ROWS_V1"*. No test or checker compares the two values
(`grep -rn "MAX_ASSET_CUSTODY_ROWS_V1" tests/ tools/` returns only THV1 prose). The same holds for
`MAX_FRAGMENT_ROWS_V1` (`src/core/global_accounting_allocation_certificate_v1.py:65` vs
`zk/…/global_accounting_allocation_certificate.rs:32`). Both are blob-sha pinned, so drift is caught
today, but — the argument P18 made for P3-f — a legitimate hygiene re-freeze regenerates those shas
mechanically and a value change would ride along. The P3-f test already parses Rust source; adding
two integer comparisons to it costs nothing.

### N5 (P3) — the eleventh code has no reachability test in either language

`FRAGMENT_INVALID` appears in exactly one test, `tests/core/test_global_accounting_lane_producers_v1.py:316`,
inside the family-closure list. Nothing reaches it. It **is** reachable in Python (probe N2, line D)
and appears to be unreachable in Rust, where check 0's `validate_resource_bounds` and the check-7
ceiling jointly bound both row families before the fragment is assembled — the exact mirror image of
`ACCEPTED_INVALID`, which is documented as reachable in Rust only. The asymmetry is worth stating in
the docstrings, and the Python reachability is worth a test: it is a two-line addition to the probe I
already wrote.

---

## 6. What C8'' genuinely sealed

Recorded so the next candidate does not redo it:

- **P2-C** is properly closed. The new lib unit test is the right shape: it constructs through the
  real transition, rebinds the port root and recomputes the receipt root, and **asserts
  `accepted.validate().is_ok()` before calling the producer** — so the test would fail loudly if a
  future change made an earlier gate fire, instead of silently passing on the wrong disjunct. The
  `ACCEPTED_INVALID` case kept its own exact assertion at the old site.
- **P2-D** is closed on both classes. I re-ran both P18 escape probes (5000 canonical entitlement
  rows; 5000 controlled rows) and neither escapes the closed family in either language.
- The `ControlledLocationRowV1` constructions outside the `try` block cannot raise: they take their
  four fields from an already-validated `EconomicAmountV1` and both types call the *same*
  `_require_token` / `_require_atoms_u128` imported from `global_settlement_types_v1`
  (`…certificate_v1.py:41-54`, `…types_v1.py:1220-1224`). Verified, not assumed — the 5000-row probe
  constructs all 5000 rows before reaching `FRAGMENT_INVALID`.
- The producer bodies have no panic surface: every `expect`/`panic!` in
  `zk/…/global_accounting_lane_producers.rs` is inside `#[cfg(test)]` (lines 486, 545, 547, 553, 560, 606).
- **P3-f** is closed in substance by a different mechanism than I proposed: a gated pytest rather
  than a checker projection. That is equally durable — it runs inside `python_producer_gate` and
  survives a hygiene re-freeze — and it additionally closes the member-name-vs-value gap I raised.
- The `receipt_root` visibility widening to `pub(crate)` (`zk/…/asset_transfer_lane_module.rs:76`) is
  disclosed in the THV1 claim scope and does not cross the crate boundary.
- The `try/except (TypeError, ValueError)` in the Python producer is narrow (two types, one
  construction) and converts to a closed reject rather than swallowing. Given the stated total-function
  contract this is the right trade, and P18 asked for it.

## 7. Recommendation

Admissible as a repair of P18, not yet as a closure of it. A C9-prefix candidate should:

1. reword `src/kernels/dex/global_accounting_allocation_certificate_v1.yaml:62-64` and the pinned
   phrase at `tests/formal/test_esso_global_accounting_allocation_certificate_v1.py:271` to the
   registry-scoped wording already used in the packet, then re-pin `model_source_sha256` / ir hash
   and re-freeze (**N1** — the only P2);
2. put `maximum=MAX_ASSET_TRANSFER_CUSTODY_ROWS_V1` on `src/core/asset_lane_projection_v1.py:78-83`
   so the twins agree at check 0, and drop the unconditional "mirror it exactly" claim (**N2**);
3. finish the two half-applied wording fixes: `src/core/global_accounting_lane_producers_v1.py:10-11`
   and `zk/…/global_accounting_lane_producers.rs:221-223` (**P3-d**), and
   `zk/…/global_accounting_lane_producers.rs:235` (**P3-c**);
4. read or delete `ReceiptBackedProducerRejectCodeV1::ALL` (**N3**), add the two constant comparisons
   to the P3-f test (**N4**), and add one Python reachability test for `FRAGMENT_INVALID` (**N5**).

Items 3 and 4 are cheap and mechanical. Item 1 is the one that matters: it is the third review in a
row to raise this sentence.

Authority remains `NONE` everywhere; `formal_core_complete: false`; the claim ceiling did not move
and must not.

---

## 8. sha256 of every file quoted

```
65d0168521c858571fe91b977a270fe5b5619824a7cdc9984fe2e9ed1e6e76a6  docs/research/ZENODEX_O008_FORMAL_CYCLE_V1.json
a47e75f49dd4ccc30fb57a21e8e451bfe57a1362b72480cc98143dce8a1f4d69  docs/research/ZENODEX_O008_FORMAL_CYCLE_V1.md
844bd29b13c8baf7ed56532ed9f25f944d75b6bf7d33a01cf2ac475731778952  docs/research/reviews/ZENODEX_FORMAL_CORE_P18_OPUS_REVIEW_00453474681e.md
017554d088f7d9f6720527b0e3d2a8335d71c5010e1fab6455749a76d3b6f856  src/core/global_accounting_lane_producers_v1.py
b9f7083f41a313a4576e260b11c12db94c7dd9723d7a6a5c12b373ff07a0ce3c  src/core/asset_transfer_lane_module_v1.py
8d81e8961e134d7bfe436fc32cf3ac1b71a3ce23fc85a1a6ca64010e175dc0da  src/core/global_accounting_allocation_certificate_v1.py
3f0078d009d30247f97506501db4a08062c1ef54403348b0d6c32e3cc177a010  src/core/asset_lane_projection_v1.py
07caf71835c5e8a6c671f4bcd967cc6c42c0ef77ba5875c56abe41265050a5a8  src/kernels/dex/global_accounting_allocation_certificate_v1.yaml
c4de91ca2ba3e0152196404348f4a9863da1445dbe5667e99924cd2433499e88  tests/core/test_global_accounting_lane_producers_v1.py
19482600413f8ea19cbe4c76a000729500f46424770ceefdce7851c1b4b79478  tests/test_check_o008_formal_cycle_v1.py
8dd91d6d037e02cb151c59baa3f2cd5647825165e01a03ccb5a721f7dacdcb16  tests/formal/test_esso_global_accounting_allocation_certificate_v1.py
a2b24bf990889fa6efc03524578676390dce61e2e72b768f78c3e4755fca0490  tests/formal/test_lean_global_accounting_allocation_certificate_v1.py
b4e55d50d2e3e4469cb38564a2ab6dca9f88eadafb9c7bb1368cccfe2df6b0dc  tests/evidence/test_hygiene/THV1-20260901-claimant-backing-guard-golden-v13.json
a436be79a4342193205a3fc774918f90302523936b84e932dafa61984507f612  tests/evidence/test_hygiene/THV1-20260901-global-accounting-allocation-certificate-v10.json
b3c431ba712736bb18ae462f5feb0f3899850620ad9cd59c4671e8abb2a6f164  tests/evidence/test_hygiene/THV1-20260901-o008-formal-cycle-admission-v20.json
5939fa4da24ab2ac01605c093cf10508a7de2e90454c8cae2778dffdaaedef1a  tools/o008_formal_cycle_admission_v1.py
b1991c086c6f76b04eda328daf20f5091afd901613a08bb7d1c6f2de4039e549  tools/check_global_settlement_canonical_manifest_v1.py
2008df87d05b71431f0d41f351006d50c15138c309ce78b3df63e1a203eb5358  zk/global_settlement_abi_v1/src/global_accounting_lane_producers.rs
26ac83d8359690a352328893debbf7d64685bd3bb44982527afcfbc4e4ce57a9  zk/global_settlement_abi_v1/src/asset_transfer_lane_module.rs
c2c4aafd4ac7a4d23343e9e71fc1d36d59ee25de8476ed3a5c5bef9f55602c1c  zk/global_settlement_abi_v1/src/asset_lane_projection.rs
f7452d9a8d7036d18fe23700af733fb8dc83b454ab5a50835e4ea509c9288653  zk/global_settlement_abi_v1/src/global_accounting_allocation_certificate.rs
6cce2178582ae4f38ff95fade6f544ae54b0d7568b7599dfa6214a56515cd46a  zk/global_settlement_abi_v1/src/canonical.rs
eddd63dde0b472b0967a4a5570aaa69eee3c02f733e2046fd260c0b7440bcab5  zk/global_settlement_abi_v1/tests/global_accounting_lane_producers.rs
```

Probe artefacts (outside the worktree, nothing in `/tmp/zenodex-formal-core-opus-c8pp`,
`/tmp/zenodex-formal-core-fable-20260901` or the canonical checkout was modified):
`/tmp/zenodex-opus-c8pp-probes/{probe_projection_ceiling.py,probe_precedence.py,rustprobe/}`.
