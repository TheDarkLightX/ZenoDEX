# Opus independent review — C8''' (P19 repair) at S20 / P20

- **Subject S20**: `3906f79d42fc044ae9e66d0d917a403425ad238d`
- **Packet P20**: `3273b03c4ae16dc08298379677d1e7205e62a9c6`
- **Worktree**: `/tmp/zenodex-formal-core-opus-c8ppp` (clean, detached, nothing edited)
- **Packet schema**: `zenodex/o008-formal-cycle-evidence/v15`
- **Review date**: 2026-09-02
- **Prior receipt reviewed against**: `docs/research/reviews/ZENODEX_FORMAL_CORE_P19_OPUS_REVIEW_738b54f631bc.md`
  (grade B, 0 P1 / 1 P2 / 5 P3)

## Grade: B+

**Findings: 0 × P1, 1 × P2, 2 × P3.**

All seven P19 items are closed, and — the part that matters — they are closed with pins I
independently verified kill real mutations rather than with prose. I rebuilt the family-parser
replica that survived two mutations in P19 and it now kills all eight I threw at it, including
the two it missed. The 5000-row projection probe that constructed in P19 now raises at
construction. The five mirrored ceilings are compared against integers parsed out of Rust, and
the parser is fail-closed on a literal shape it cannot read. Every gate replays green at the
exact packet hash, the claim ceiling is byte-identical to P19, and all 74 THV1 pinned digests
equal committed bytes.

It is B+ and not A- for two reasons. First, the commit message's headline claim — "Registry-scope
the **last** instance of the receipt-backed clause" — is false. Two unscoped present-tense
instances survive, one of them in `tools/o008_formal_cycle_admission_v1.py`, a file this very
commit edited, and it is emitted verbatim into the packet's own `nonclaims[1]` and into
`ZENODEX_O008_FORMAL_CYCLE_V1.md:192`. That is the fourth consecutive review in which this clause
family is the finding. Second, the N2 repair is framed as making the twins agree on projection row
ceilings; it closes one of eight `_require_ordered_objects` call sites in the same two files, and
seven siblings whose Rust twins bound the identical row families are still unbounded in Python.

---

## 1. Envelope (duty 1) — PASS

| Check | Result |
|---|---|
| P20 is a direct child of S20 | `git log --format='%H parent=%P'` → `3273b03c4…` parent `3906f79d42fc044ae9e66d0d917a403425ad238d` ✓ |
| P20 is packet-only | `git diff --stat 3906f79d4 3273b03c4` = `ZENODEX_O008_FORMAL_CYCLE_V1.{json,md}` only (2 files, 49+/49−) ✓ |
| S20 is a direct child of the R16 receipt | parent `3c09d2059088fc5723b719b697ba7bc87d1c7692` ✓ |
| Subject tree | packet says `61edee4e3e167dd606eb927f65d72b2887c35a7e`; `git rev-parse 3906f79d4^{tree}` = same ✓ |
| Worktree clean at P20 | `git status --porcelain` empty (excluding the `external/`, `lean-mathlib/.lake` symlinks I created) ✓ |
| Packet schema | `v15` → `v15`, unchanged ✓ |
| Claim ceiling | byte-identical to P19 (compared the two committed JSONs field-by-field) ✓ |
| Top-level packet keys that changed | `esso_evidence`, `hygiene_selection`, `packet_commit_parent`, `proof_replay`, `source_pins`, `subject_commit`, `subject_parent`, `subject_tree` — evidence only ✓ |

**Checker, both modes, at the exact packet hash:**

```
$ "$PY" tools/check_o008_formal_cycle_v1.py --root /tmp/zenodex-formal-core-opus-c8ppp \
    --packet-commit 3273b03c4ae16dc08298379677d1e7205e62a9c6
NOREPLAY_EXIT=0   ok=True  packet_admitted=True  proof_replay.status=NOT_RUN
                  errors=[]  current_source_drift=[]  stderr: empty

$ ... --replay --python "$PY" --esso-python "$PY" \
      --esso-pythonpath /tmp/zenodex-formal-core-opus-c8ppp/external/ESSO
REPLAY_EXIT=0     ok=True  packet_admitted=True  proof_replay.status=EXECUTED_PASS  runs=28
                  errors=[]  current_source_drift=[]  stderr: empty
```

All 28 replayed commands exit 0 and reproduce the committed comparables. The ones the repair
moved:

| command_id | comparable |
|---|---|
| `python_producer_gate` | `passed: 29` (was 27) |
| `esso_certificate_validate` | `ir_hash: sha256:01a34e8dcd5bef3cb8a43b132d1679259e3a026dd36f17fbaf8331702faff3c8` (re-recorded) |
| `esso_certificate_gate` | `passed: 24` |
| `rust_producer_gate` | `passed: 7` |
| `python_certificate_golden_gate` | `passed: 37` |
| `prior_restage_gate` | `passed: 136` |

Independent re-runs, not through the checker:

```
cargo test --all-targets            522 passed; 0 failed
cargo clippy --all-targets -D warnings   exit 0, no diagnostics
pytest tests/core/test_global_accounting_lane_producers_v1.py
       tests/test_check_o008_formal_cycle_v1.py
       tests/core/test_global_accounting_allocation_certificate_v1_golden.py
       tests/test_o008_v1_projection_runtime_gate.py
       tests/core/test_asset_lane_coordinator_v1.py
       tests/core/test_asset_lane_coordinator_rejections_v1.py      494 passed
pytest tests/formal/test_lean_global_claimant_custody_relation_v1.py          6 passed   (serial)
pytest tests/formal/test_lean_global_accounting_allocation_certificate_v1.py  6 passed   (serial)
tools/check_test_hygiene_v1.py --base-ref dd6d13daf9f84e95305978ffdc066749e169d9a5
                                    test-hygiene-v1: ok packets=123 critical=8
tools/check_global_settlement_canonical_manifest_v1.py     PASS
```

The two Lean gates were run one after the other, never concurrently; no SIGBUS.

The canonical closure re-pin is real, not echoed: `tools/check_global_settlement_canonical_manifest_v1.py:441-448`
recomputes `_source_closure_sha256` over the discovered closure and compares it to
`EXPECTED_SOURCE_CLOSURE_SHA256_V1 = 384274def4f91e1fdd61491963dd53a487d8d84902a1d6bd0c118c14620665cc`;
PASS means the recomputed digest equals the new pin.

**THV1 pins.** I recursively walked the three successor packets and re-hashed every pinned path:
admission-v21 **40/40 match**, certificate-v11 **22/22 match**, backing-v14 **12/12 match**, zero
mismatches, zero missing files.

**Mutation rows.** certificate-v11 adds exactly five rows over v10 (50 → 55), one per P19 finding,
each naming a test that exists and passes. I verified the killers mechanically rather than
trusting the row text — see §2 N3 and N4.

---

## 2. Per-finding closure table

| # | P19 finding | Verdict | Evidence |
|---|---|---|---|
| **N1** (P2) | receipt-backed clause still in the pinned ESSO model and its gate | **CLOSED** | `src/kernels/dex/global_accounting_allocation_certificate_v1.yaml:62-72` now reads *"No lane producer is registered receipt-backed and none is on an acceptance path (an implemented, unregistered wave-B producer exists), so the only certificate the registry accepts today is the registered-empty one; enable_lane models future registered receipt-backed producers, not a present registry entry."* The gate's pinned phrases at `tests/formal/test_esso_global_accounting_allocation_certificate_v1.py:271-272` match (the test normalises whitespace at line 261, so the YAML line folding is not a hole). `RECORDED_SOURCE_SHA256` at line 37 = `7afad7b256a19b1a162dd24dad5ca89f3ebe47c8c02f63bb60d1cfff7b709456` = live `sha256sum` of the YAML. `RECORDED_IR_HASH` at line 38 = `sha256:01a34e8dcd…`, confirmed **by live replay**, not by the pin (`esso_certificate_validate` produced that exact ir_hash). Grep sweep for `"receipt-backed in the running code"`, `"not a present capability"`, `"models the future receipt-backed"`, `"No lane producer is receipt-backed"` over the whole tree returns **zero hits in live source** — remaining hits are historical review receipts under `docs/research/reviews/` and superseded THV1 packets v1–v9, which are frozen records. The clause family does survive elsewhere; I raise that as a new finding rather than reopening N1, because the surface N1 named is genuinely repaired. |
| **N2** (P3) | Python projection had no row ceilings; Rust rejects at check 0 | **CLOSED** | `src/core/asset_lane_projection_v1.py:31-38` declares `MAX_ASSET_LANE_BALANCE_ROWS_V1=4096`, `MAX_ASSET_LANE_CUSTODY_ROWS_V1=4096`, `MAX_ASSET_LANE_SUPPLY_ROWS_V1=256`; enforced at `:82-101` via the `maximum=` parameter of `_require_ordered_objects` (`src/core/global_settlement_types_v1.py:1360-1364`, which checks the ceiling **before** the type check, matching Rust's `validate_resource_bounds()` running first at `zk/…/asset_lane_projection.rs:90`). The mapping is correct: Rust bounds supplies with `MAX_ASSET_POLICY_ROWS_V1` (`asset_lane_projection.rs:84`), which is what the Python supply ceiling mirrors. `src/core/asset_transfer_lane_module_v1.py:51` now aliases the projection constant instead of restating `4096`. **My P19 probe re-run:** `custody-5000 → ValueError: asset lane custody exceeds its 4096-item ceiling`; `balances-5000 → ValueError: asset lane balances exceeds its 4096-item ceiling`; `supplies-257 → ValueError: asset lane supplies exceeds its 256-item ceiling`; `custody-4097 → ValueError`. The 5000-row projection **fails construction in Python**, as required. The Rust docstring no longer says the codes "mirror it exactly" and instead states where the accepted-value invariants live in each language (`zk/…/global_accounting_lane_producers.rs:218-231`) — the honest framing, since the same bytes now raise in Python and return `ACCEPTED_INVALID` in Rust. |
| **N3** (P3) | `ReceiptBackedProducerRejectCodeV1::ALL` unconsumed and unpinned | **CLOSED** | `tests/core/test_global_accounting_lane_producers_v1.py:442-445` parses the `ALL` block and compares its sequence to `core.RECEIPT_BACKED_PRODUCER_REJECT_CODES_V1`. I rebuilt my six-mutation replica against the **new** parser and added two more. All eight are killed: declaration reorder (AssertionError), drop a variant from the declaration (AssertionError), wire-code rename in `code()` (AssertionError), member rename everywhere (AssertionError), **drop a member from `ALL` adjusting the length 11→10 (IndexError — the hardcoded `[Self; 11]` needle vanishes, fail-closed)**, **drop a member from `ALL` keeping length 11 by duplicating another (AssertionError)**, **reorder `ALL` only (AssertionError)**, delete `ALL` entirely (IndexError). The two survivors from P19 are dead. |
| **N4** (P3) | mirrored ceiling constants not mechanically bound | **CLOSED** | Same test, `:447-465`, parses `zk/…/canonical.rs` and `zk/…/global_accounting_allocation_certificate.rs` and compares five integers. I re-derived all five independently: `MAX_ASSET_LANE_BALANCE_ROWS_V1` 4096 = `MAX_ASSET_BALANCE_ROWS_V1` 4096; `MAX_ASSET_LANE_CUSTODY_ROWS_V1` 4096 = `MAX_ASSET_CUSTODY_ROWS_V1` 4096; `MAX_ASSET_LANE_SUPPLY_ROWS_V1` 256 = `MAX_ASSET_POLICY_ROWS_V1` 256; `MAX_ASSET_TRANSFER_CUSTODY_ROWS_V1` 4096 = `MAX_ASSET_CUSTODY_ROWS_V1` 4096; `MAX_FRAGMENT_ROWS_V1` 4096 = Rust `MAX_FRAGMENT_ROWS_V1` 4096. A Rust-side change 4096→8192 is detected. The parser handles underscore-free literals and **asserts** (rather than silently skipping) on a suffixed literal such as `8_192usize` — fail-closed, which is the right failure mode for a source-scraping pin. |
| **N5** (P3) | eleventh code `FRAGMENT_INVALID` had no reachability test | **CLOSED** (docstring caveat — see NEW-3) | `tests/core/test_global_accounting_lane_producers_v1.py:496-531` reaches the arm through `object.__new__` forgery of a duplicate custody key and asserts `code is FRAGMENT_INVALID` and `detail == "fragment validation"`. The claim that the arm is *defensive* is sound: I traced every constructor invariant the producer can violate (`_ordered_rows`, `src/core/global_accounting_allocation_certificate_v1.py:336-346`) against what the producer has already checked, and each one is pre-empted — the row ceiling by the N2 projection bound plus check 7, canonical order and uniqueness by the projection's own key uniqueness (`EconomicAmountV1.key` = `(asset, owner, custody_domain)` at `global_settlement_types_v1.py:1226-1228` is exactly `ControlledLocationRowV1.key` at `global_accounting_allocation_certificate_v1.py:181-183`) and by check 7 for entitlements, and `_require_root(module_release_id)` by `LaneStateRootV1.__post_init__` (`global_settlement_types_v1.py:1200`) already forbidding the zero root. So the arm is genuinely unreachable through validated construction today. The caveat is what that argument rests on — NEW-3. |
| **P3-c** residual | check-0 comment applied in one twin only | **CLOSED** | `zk/…/global_accounting_lane_producers.rs:240-241`: *"In Python this is unreachable through construction (`__post_init__` validates; only `object.__new__` forgery bypasses it); reachable here."* Matches the Python docstring at `src/core/global_accounting_lane_producers_v1.py:193-196`. Both twins now say the same thing about the same check. |
| **P3-d** residual | journal-verifier wording applied in one twin only | **CLOSED** | Python module header `src/core/global_accounting_lane_producers_v1.py:8-13` and function docstring `:223-228`; Rust fn docstring `zk/…/global_accounting_lane_producers.rs:227-228`. Both carry *"a journal verifier exists … but this producer does not yet require it — C9a will take the witness"*. The referenced verifier is named in each language's own vocabulary (`lane_module_receipt_verification_v1` / `lane_module_receipt_verification`), which is correct, not drift. |

**7 of 7 closed.**

---

## 3. New findings

### NEW-1 (P2) — the receipt-backed clause is not at its last instance; one survivor is emitted into the packet

`tools/o008_formal_cycle_admission_v1.py:468-472`, `NONCLAIMS_V1[1]`:

```python
NONCLAIMS_V1: Final[tuple[str, ...]] = (
    "The completed formal cycle does not complete O-008.",
    "The GlobalAccountingAllocationCertificateV1 checker has no receipt-backed lane producer and"
    " is not mounted; the only certificate it accepts today is the registered-empty certificate"
    " over a state with every lane disabled, so no exact all-twelve-lane reconciliation exists.",
```

This is the same unscoped present-tense construction that P17, P18 and P19 each adjudicated. It is
emitted verbatim into the committed packet as `nonclaims[1]` and into
`docs/research/ZENODEX_O008_FORMAL_CYCLE_V1.md:192`. Under the registry reading it is true; under
the running-code reading it is false, because `produce_asset_transfer_fragment_v1` is implemented
and emits `producer_kind=RECEIPT_BACKED`. Eliminating exactly that ambiguity is what C8''' set out
to do, and every neighbouring surface now carries the disambiguation:

- `esso_evidence.certificate_model.claim_boundary` in the same packet: *"no lane producer is
  REGISTERED receipt-backed and none is on an acceptance path (an implemented, unregistered wave-B
  producer exists)"*
- THV1 certificate-v11 `claim_scope` and `nonclaims`: the registry-scoped wording
- the ESSO model notes and its gate phrases (N1)
- both twin module headers (P3-d)

So the packet's `esso_evidence` block and the packet's `nonclaims` block now disagree with each
other about the same fact, in the same file, at the same commit.

Aggravating: `tools/o008_formal_cycle_admission_v1.py` **is a file this commit edited** — S20
changes `PRODUCERS_PYTHON_GATE_EXPECTED_PASSED_V1` at line 1038 from 27 to 29. Line 470 was in
the editor's hands.

Second surviving instance, `src/core/global_accounting_allocation_certificate_v1.py:88-89`:

```python
# Exhaustive over LaneIdV1: the producer kind the registry supports today and the
# obligation that blocks a receipt-backed producer. No lane is receipt-backed yet.
```

Weaker, because it sits directly above the registry dict, but still an unscoped present-tense
claim in a packet-pinned source file. Note the same module gets it right 559 lines later, at
`:648`: *"with no receipt-backed producer **registered**"*.

Reproduce:

```
$ grep -rn "no receipt-backed lane producer\|No lane is receipt-backed" \
    src/ tools/ --include=*.py
src/core/global_accounting_allocation_certificate_v1.py:89:...No lane is receipt-backed yet.
tools/o008_formal_cycle_admission_v1.py:470:"The GlobalAccountingAllocationCertificateV1 checker has no receipt-backed lane producer and"
```

Consequence is bounded — authority is NONE, nothing is mounted, and the sentence is defensible
under one reading — but this is a P2 on the same grounds P19's N1 was: it is a claim-boundary
sentence in a pinned executing tool, it reaches the packet, and no prior review adjudicated *this*
instance. Fix: replace with the registry-scoped wording already used in `claim_boundary`, re-pin
`tools/o008_formal_cycle_admission_v1.py`, rebuild the packet.

### NEW-2 (P3) — the N2 ceiling mirror closed 1 of 8 sibling call sites in the same family

The repair added `maximum=` to the three projection call sites. Seven `_require_ordered_objects`
call sites in the same asset-lane family still pass no ceiling, and for all but one the Rust twin
bounds the identical row family:

| Python call site | Rust twin that bounds it | asymmetric? |
|---|---|---|
| `src/core/asset_transfer_types_v1.py:75` policies | `zk/…/asset_transfer_types.rs:67-70` `MAX_ASSET_POLICY_ROWS_V1` | **yes** |
| `src/core/asset_transfer_types_v1.py:81` balances | `zk/…/asset_transfer_types.rs:74` `MAX_ASSET_BALANCE_ROWS_V1` | **yes** |
| `src/core/asset_transfer_types_v1.py:87` supplies | `zk/…/asset_transfer_types.rs:67-70` `MAX_ASSET_POLICY_ROWS_V1` | **yes** |
| `src/core/managed_asset_lifecycle_types_v1.py:121` policies | `zk/…/managed_asset_lifecycle_types.rs:112-117` | **yes** |
| `src/core/managed_asset_lifecycle_types_v1.py:127` balances | `zk/…/managed_asset_lifecycle_types.rs:119` | **yes** |
| `src/core/managed_asset_lifecycle_types_v1.py:133` supplies | `zk/…/managed_asset_lifecycle_types.rs:112-117` | **yes** |
| `src/core/managed_asset_lifecycle_lane_module_v1.py:78` custody | `zk/…/managed_asset_lifecycle_lane_module.rs:47-51` `MAX_ASSET_CUSTODY_ROWS_V1` | **yes** |
| `src/core/asset_lane_projection_v1.py:315` compatible modules | Rust has no length ceiling either (`asset_lane_projection.rs:275-286` checks non-empty and order only) | no — symmetric |

This is the P19 N2 defect exactly, one type up the stack. Minimal repro (nothing forged, every
object passes its own `__post_init__`):

```python
from src.core.asset_transfer_types_v1 import AssetTransferStateV1, AssetTransferPolicyV1
from src.core.global_settlement_types_v1 import EconomicAmountV1, AssetSupplyV1
N = 4097                                    # Rust MAX_ASSET_BALANCE_ROWS_V1 = 4096
st = AssetTransferStateV1(
    module_release_id="0x" + "11" * 32,
    policies=(AssetTransferPolicyV1("USD", "fees", 0, True),),
    balances=tuple(sorted((EconomicAmountV1(f"acct-{i:06d}", "USD", "accounts", 1)
                           for i in range(N)), key=lambda r: r.key)),
    supplies=(AssetSupplyV1("USD", N),),
)
```

Observed: `AssetTransferStateV1 with 4097 balance rows: CONSTRUCTED`, `state_root = 0xd5beb9d59f34a315…`.
Its Rust twin fails `validate()` at `asset_transfer_types.rs:74` with
`InvalidBounds("asset transfer balance rows")`. Same for 257 policies/supplies against
`MAX_ASSET_POLICY_ROWS_V1 = 256` (`state_root = 0x851aa9130817fec5…`). So Python and Rust still
disagree about which asset-transfer states are well-formed and about which state roots exist.

Exposure is bounded and I checked the boundary rather than assuming it: an oversized state cannot
reach the wave-B producer, because `AssetTransferLaneModuleInputV1.__post_init__`
(`src/core/asset_transfer_lane_module_v1.py:88-93`) projects the pre-state, and the projection now
raises. The divergence is confined to the standalone state types and their roots. Nothing is
mounted, authority is NONE.

Note the `managed_asset_lifecycle_lane_module_v1.py:78` row is the direct sibling of the site the
P18 P3-g repair fixed in `asset_transfer_lane_module_v1.py:81`; that asymmetry has now survived
two consecutive repairs of its twin.

### NEW-3 (P3) — `FRAGMENT_INVALID` unreachability rests on an unpinned inequality, and the test's name overstates its body

The N5 test is named `test_fragment_invalid_is_reachable_only_through_construction_forgery` and its
docstring (`tests/core/test_global_accounting_lane_producers_v1.py:497-503`) states *"Through
validated constructions the projection ceilings (N2) and the canonical gates make the arm
unreachable in both languages"*. The body witnesses **one** forgery reaching the arm; it does not
establish the "only" in the name, and nothing in the repo pins the property the docstring asserts.

The load-bearing fact is the inequality `MAX_ASSET_LANE_CUSTODY_ROWS_V1 ≤ MAX_FRAGMENT_ROWS_V1`
(4096 ≤ 4096). The N4 pins compare each constant to *its own* Rust counterpart; none compares the
two to each other:

```
$ grep -rn "MAX_FRAGMENT_ROWS_V1" tests/ tools/ --include=*.py
tests/core/test_global_accounting_lane_producers_v1.py:463:  match = re.search(r"pub const MAX_FRAGMENT_ROWS_V1: usize = ([0-9_]+);", cert_rs)
tests/core/test_global_accounting_lane_producers_v1.py:465:  assert cert.MAX_FRAGMENT_ROWS_V1 == int(match.group(1).replace("_", ""))
```

The two constants live in different files in each language (`canonical.rs:13` vs
`global_accounting_allocation_certificate.rs:32`), so nothing forces them to move together. Break
the inequality and the arm opens on a fully validated path — no `object.__new__`, no forgery:

```python
accepted, lane_root, prior, entitlements = t._wave_b_setup()   # all validated constructions
producers.produce_asset_transfer_fragment_v1(accepted, lane_root, prior, entitlements)
# -> LaneAllocationFragmentV1                                  (baseline accept)
cert.MAX_FRAGMENT_ROWS_V1 = 0        # simulate the fragment ceiling drifting below the custody ceiling
producers.produce_asset_transfer_fragment_v1(accepted, lane_root, prior, entitlements)
# -> ReceiptBackedProducerRejectedV1 FRAGMENT_INVALID "fragment validation"
```

(`cert.MAX_FRAGMENT_ROWS_V1` is read as a module global by `_ordered_rows`; the producer's check 7
holds a separate binding, so this isolates the constructor ceiling — exactly the drift scenario.)
The same argument applies in Rust: `zk/…/global_accounting_lane_producers.rs:454-460` guards the
identical assembly with the identical unpinned inequality.

The behaviour is correct today and the arm is correctly defensive. The finding is that the
docstring states a structural property where only a numeric coincidence exists, and the test name
asserts a universal the body does not check. One assertion — `MAX_ASSET_LANE_CUSTODY_ROWS_V1 <=
MAX_FRAGMENT_ROWS_V1` — in the test that already imports both would convert the coincidence into a
pin.

---

## 4. Observations (no finding)

- **Superseded THV1 certificate packets v1–v9** still carry *"No lane producer is receipt-backed;
  the only accepted certificate is the registered-empty certificate…"*. They are frozen historical
  records and the hygiene selection takes the newest packet per path, so they are inert. v10 and
  v11 both carry the registry-scoped wording. Not a finding; recorded so the next reviewer's grep
  sweep does not re-open it.
- **Construction precedence differs from Rust inside the projection.** Python's `__post_init__`
  validates the two registry roots (`asset_lane_projection_v1.py:73-80`) *before* the row ceilings
  (`:82-101`); Rust's `validate()` calls `validate_resource_bounds()` first
  (`asset_lane_projection.rs:90`). For an input that is both oversized and carries a bad root the
  two languages name different invariants. No pinned contract declares precedence for this type
  (unlike the producer's check order), so this is not a finding — but it is the kind of thing the
  next "twins agree at check 0" claim should be careful not to overstate.
- **The N2 mutation row's named killer covers half its stated class.** certificate-v11's row *"give
  the twins different reject codes for an oversized accepted value"* names
  `test_projection_row_ceilings_reject_oversized_construction`, which is Python-side only. A
  Rust-only ceiling change is caught, but by the N4 row's test rather than this one. The mutation
  is killed; the attribution is loose.
- The `zenodex_ab_*` and unrelated suites were not re-run; scope was the O-008 formal-core surface.

## 5. What C8''' genuinely sealed

Recorded so the next candidate does not redo it:

- **The `ALL` array is properly pinned.** Both P19 survivors die, and the hardcoded `[Self; 11]`
  needle makes a length-adjusting drop fail closed rather than silently reparse. This is the right
  shape.
- **The ceiling constants are bound to parsed Rust integers, fail-closed on unparseable literals.**
  A legitimate hygiene re-freeze can no longer carry a value change along with it — which was the
  precise argument N4 made.
- **The projection ceilings are real and enforced before the type check**, matching Rust's own
  ordering, and the Rust docstring stopped claiming the two languages mirror each other exactly.
- **P3-c and P3-d are applied in both twins.** The two languages now say the same thing about
  check 0 and about the journal verifier.
- **The ESSO ir_hash re-record is verified by replay, not by the pin.** `esso_certificate_validate`
  regenerates `sha256:01a34e8d…` from the moved model source.

## 6. Claim ceiling

Unchanged and byte-identical to P19. `formal_core_complete: false`,
`o008_status: OPEN_EXACT_ALL_12_RECONCILIATION_MISSING`,
`supported_claim: O008_RELATION_NECESSARY_CHECKS_AND_INFORMATION_LOSS_PROVED`,
`value_movement_gates_closed: 0 / 12`, every authority field `NONE`,
`whole_value_movement_safe: false`. Nothing in this review moves it. Authority granted by this
review: **NONE**.

## 7. sha256 of every file quoted

```
b7eba00b3ac9420278602ed1e4d4ee74ae807490a025b7c21be40c4a13d5b440  src/core/asset_lane_projection_v1.py
acd8df6b201bb916bb79d7c3bec78a801bf3743bd643a825e8f17d3f296a63da  src/core/asset_transfer_lane_module_v1.py
09dfdc46c6e8e78d1b87ad9ea765438d8c6604d17e0674c2fb984a9935349645  src/core/asset_transfer_types_v1.py
b42f0fe6839b940742b4a6ea0f433869df952965b583ebcfd7f280e41203fa80  src/core/managed_asset_lifecycle_types_v1.py
65bb3d4a527372190fbd60a06f6bbf04fb6a9a588be20f636739d85d93d44227  src/core/managed_asset_lifecycle_lane_module_v1.py
26be354b4d83af62a5c96967bad4f505cd2c8332fc9ae43a851b0c5b697e44b7  src/core/global_accounting_lane_producers_v1.py
8d81e8961e134d7bfe436fc32cf3ac1b71a3ce23fc85a1a6ca64010e175dc0da  src/core/global_accounting_allocation_certificate_v1.py
13871fb586d7e5c1106edd5c0a9fdcd6f817016925027a6bdfb5ca8f53f29f58  src/core/global_settlement_types_v1.py
7afad7b256a19b1a162dd24dad5ca89f3ebe47c8c02f63bb60d1cfff7b709456  src/kernels/dex/global_accounting_allocation_certificate_v1.yaml
5f16ef2107e574cfc12ec99735be50f110587e1d47d62d44c26efe82177bdcb8  tests/core/test_global_accounting_lane_producers_v1.py
95fe6a2df39c8ee35913f8c2d30ab3f59125ad129b8726a0a15fededd5629ac9  tests/formal/test_esso_global_accounting_allocation_certificate_v1.py
22c6dc69bb63d5da816a5384accd6aaadf44616846378eb44a1e8394e7e73633  tools/o008_formal_cycle_admission_v1.py
6cd5f13685b8176374a3cab6468bc38b866dbdf109a9b82759e92e89f35b03d1  tools/check_global_settlement_canonical_manifest_v1.py
4c92915cbcde4c588b88fc8a1b9aec570c1cc20fb2b153679fb4dcf3b8ea6230  zk/global_settlement_abi_v1/src/global_accounting_lane_producers.rs
c2c4aafd4ac7a4d23343e9e71fc1d36d59ee25de8476ed3a5c5bef9f55602c1c  zk/global_settlement_abi_v1/src/asset_lane_projection.rs
717fac261af10b837ad11276c37cf9513defea48909e94273f16ae6ad6ec38ae  zk/global_settlement_abi_v1/src/asset_transfer_types.rs
33620989420de792f73e0d181ff8828e9c379f0d052f6e3d9633380da69e2835  zk/global_settlement_abi_v1/src/managed_asset_lifecycle_types.rs
bf55ace7af4801f13b7c622602ee7d99a0cef0558d9bd1e7104f1f5edfdc4d4a  zk/global_settlement_abi_v1/src/managed_asset_lifecycle_lane_module.rs
6cce2178582ae4f38ff95fade6f544ae54b0d7568b7599dfa6214a56515cd46a  zk/global_settlement_abi_v1/src/canonical.rs
f7452d9a8d7036d18fe23700af733fb8dc83b454ab5a50835e4ea509c9288653  zk/global_settlement_abi_v1/src/global_accounting_allocation_certificate.rs
9ad37d858f05c348dffc5d8a20d3320b35c4bc735d25133837c7a21399bd9d23  docs/research/ZENODEX_O008_FORMAL_CYCLE_V1.json
71556a1d0c2b33f378c0cd5795d9fa9ef9eb0d5c8752550a097e77d189ee2bf3  docs/research/ZENODEX_O008_FORMAL_CYCLE_V1.md
96eeb5c64d4cde26b9c8ede263158caa3fe13a8a49e7cd589d314d21222ef160  tests/evidence/test_hygiene/THV1-20260901-o008-formal-cycle-admission-v21.json
1a598e268057f4824b0016798873bdf433722d5ee3426970143ebf76bd43cacf  tests/evidence/test_hygiene/THV1-20260901-global-accounting-allocation-certificate-v11.json
d74c05fa3014bfa5c02a322960aca7bd7d33470da5145d598f0bac58b4056283  tests/evidence/test_hygiene/THV1-20260901-claimant-backing-guard-golden-v14.json
```

## 8. Ordered repair list for C8''''

1. Registry-scope `tools/o008_formal_cycle_admission_v1.py:470` and
   `src/core/global_accounting_allocation_certificate_v1.py:89`; re-pin the admission core and
   rebuild the packet (**NEW-1**). Then the clause really is at its last instance.
2. Add `maximum=` to the seven asymmetric `_require_ordered_objects` call sites in
   `asset_transfer_types_v1.py`, `managed_asset_lifecycle_types_v1.py` and
   `managed_asset_lifecycle_lane_module_v1.py`, aliasing the same projection constants, and extend
   the N4 comparison block to cover them (**NEW-2**).
3. Assert `MAX_ASSET_LANE_CUSTODY_ROWS_V1 <= MAX_FRAGMENT_ROWS_V1` in the test that already
   imports both, and either rename
   `test_fragment_invalid_is_reachable_only_through_construction_forgery` or state in its docstring
   that the "only" rests on that inequality (**NEW-3**).
4. Tighten the certificate-v11 mutation row for N2 to name both killers, or split it into the
   Python-construction half and the constant-drift half (observation).
