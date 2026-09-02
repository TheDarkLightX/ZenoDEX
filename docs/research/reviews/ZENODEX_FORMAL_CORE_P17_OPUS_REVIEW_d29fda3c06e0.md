# Opus independent review — C8 (wave B) at S17 / P17

- **Subject S17**: `31671bab8853a9247654f2a4ae2e21420b503f1c`
- **Packet P17**: `d29fda3c06e069aa1f5ab4b8a108f4ed824e9d2a`
- **Worktree**: `/tmp/zenodex-formal-core-review-p-d29fda3c0` (clean, detached, nothing edited)
- **Packet schema**: `zenodex/o008-formal-cycle-evidence/v13`

## Grade: B+

**Findings: 0 × P1, 4 × P2, 6 × P3.**

C8 is sound: no input produces a fragment whose receipt binding is false, the coverage fold
agrees exactly with the certificate's exact-once partition, the exact-type gates hold against
subclasses and near-misses, the documented fold-ceiling unreachability is **true**, and "no
acceptance path uses this producer" is **verified twice over**. It is held below A- by four
P2s: one omitted check with a live witness, one **false** claim sentence in a pinned source
file, one reachable reject path with zero test coverage in either language, and one caller-input
class that escapes the closed reject family as an uncaught `ValueError`.

---

## 1. Envelope (duty 1) — PASS

| Check | Result |
|---|---|
| P17 is a direct child of S17 | `git rev-list --parents -n1 HEAD` → `d29fda3c0 31671bab8` ✓ |
| P17 is packet-only | write set = `ZENODEX_O008_FORMAL_CYCLE_V1.{json,md}` only, `status: M` ✓ |
| S17 is a direct child of the P16 receipt | parent `36217eb3f` ✓ |
| Worktree clean at P17 | `git status --porcelain` empty ✓ |
| `packet_commit_parent` | `31671bab8853…` = S17 ✓ |
| `subject_parent` / `subject_tree` | `36217eb3f8ea…` / `c68e6c3de520…` ✓ |

**Builder `--check --replay` at S17**

```
{"drift":[],"mode":"check","ok":true,"subject_commit":"31671bab8853a9247654f2a4ae2e21420b503f1c"}
EXIT=0        stderr: empty
```

**Checker `--replay --packet-commit d29fda3c0…`**

```
ok=true  packet_admitted=true  current_applicable=true  errors=[]
proof_replay=EXECUTED_PASS   head=packet=d29fda3c0…   subject=31671bab8…
EXIT=0        stderr: 0 bytes
```

Both round trips are byte-clean. `source_pins` unchanged at 42 (the producer files were already
pinned in wave A); the three new `tests/evidence/test_hygiene/THV1-20260901-*.json` vectors
(admission-v18, certificate-v8, claimant-backing-golden-v11) are covered by `hygiene_selection`
with `pin_sha256` + `packet_sha256` entries. Manifest re-pin verified: 103→104 serializers,
34→35 enums, closure digest `15e3ed79…` → `8c7d5adc94a32d2e9cc1c3575cfb3cb9ee64b554e92191c70c5fdebb00e8d1f1`.
Replay gate counts re-pinned 5→14 (Python) and 2→5 (Rust); I re-ran the Python suite directly:
**14 passed**.

## 2. Claim ceiling and nonclaims (duty 3) — INTACT

`claim_ceiling` is **byte-identical** to P16: every authority `NONE`,
`value_movement_gates_closed: 0` of `12`, `formal_core_complete: false`,
`whole_value_movement_safe: false`, `supported_claim:
O008_RELATION_NECESSARY_CHECKS_AND_INFORMATION_LOSS_PROVED`. `nonclaims` **unchanged** (no
additions, no removals). C8 raises nothing.

### "no acceptance path uses this producer" — VERIFIED (double-gated)

1. `LANE_ALLOCATION_PRODUCER_REGISTRY_V1[ASSET_TRANSFER] = (NO_PRODUCER, "VM-04 wave B …")`
   (`global_accounting_allocation_certificate_v1.py:97`). The producer stamps
   `producer_kind=RECEIPT_BACKED`, so the certificate's `PRODUCER_KIND_DRIFT` check
   (`:632-634`) rejects any such fragment today.
2. `BINDING_ROOT_DRIFT` (`:646-651`) additionally requires `binding_root == lane_state_root`
   for **every** fragment, which a receipt-root binding violates by construction.
3. Repo-wide grep: the only callers of `produce_asset_transfer_fragment_v1` in either
   language are the two test files and the two sidecar prose strings.

### "controlled-side fold ceiling unreachable for well-formed inputs" — VERIFIED TRUE

`AssetLaneStateProjectionV1.__post_init__` (`asset_lane_projection_v1.py:101-111`) enforces
`Σ(balances ∪ custody) per asset == supplies[asset]`, and `supplies[asset]` passes
`_require_atoms_u128`. The producer folds custody by `(asset, custody_domain)` — a sub-sum of
that per-asset total — so every controlled key is bounded by `MAX_ATOMS_U128_V1`. The
documented finding is accurate and the reachable path really is the caller's entitlement rows.

## 3. Adversarial audit of the producer (duty 2)

### Attacks that FAILED (the producer is sound here)

| Probe | Result |
|---|---|
| Fragment at a root the journal does not commit | Blocked. Check 4 forces `journal.post_lane_root == lane_root.state_root` and the fragment's `lane_state_root` **is** that value. |
| Receipt root the journal does not carry | Blocked. `binding_root = journal.receipt_root`, and `AssetTransferLaneModuleAcceptedV1.__post_init__` (`asset_transfer_lane_module_v1.py:229-235`) **recomputes** `_receipt_root(statement_root, journal, port, effects)` and requires equality. The receipt root transitively commits `private_port.port_root`, hence the custody rows the fragment reports. |
| Terminal rows smuggled past the zero-root check | Blocked. `terminal_bindings` is hard-coded `()`; check 6 rejects any nonzero `terminal_obligations_root`. Nothing to smuggle. |
| Entitlement multiset the coverage fold accepts but the certificate's exact-once partition rejects | **None exists.** Both fold by `(asset, control_domain)`; the producer emits empty `unencumbered_reserves` and `pending_external_obligations`, so the certificate's `assigned` (`:664-687`) reduces to exactly the producer's `assigned`. The two are the same predicate. |
| Duplicate-key entitlements double-counting into an accepted fragment | Blocked — but by a `ValueError`, not a reject code. See **P2-4**. |
| Exact-type boundaries | **All four hold.** A `LaneStateRootV1` **subclass**, a `ClaimantEntitlementRowV1` subclass, a `list` instead of a tuple, a generator, and `None` in each of the four positions all raise the intended `TypeError`. No `isinstance` softness on the producer's own gates. |
| Python/Rust reject-code and detail parity | **Clean.** All 8 codes, all 8 messages, and all detail strings match. `JOURNAL_LANE_DRIFT`'s Rust `format!("journal {:?} vs committed {:?}", …)` yields the same text as Python's `.value` form because the Rust `LaneIdV1` variant names are identical to the Python enum **values**. Detail length stays far under the 200-char cap. |
| Precedence for checks 1–6 | Real. First failing check wins; verified `disabled + entitlement-overflow` → `LANE_DISABLED`. |

### P2-1 — the carry-forward check does not verify the predecessor is *this lane's* fragment

`src/core/global_accounting_lane_producers_v1.py:235-238`
(Rust twin: `zk/global_settlement_abi_v1/src/global_accounting_lane_producers.rs:251-258`)

```python
if journal.pre_lane_root != prior_fragment.lane_state_root:
    return _reject_receipt_backed(..., STALE_JOURNAL, ..., "pre root")
```

`prior_fragment` is gated only on **exact type**. Its `lane_id`, `module_release_id`, `enabled`,
`producer_kind` and `binding_root` are never read. Contrast check 1, which *does* require both
the journal and the committed root to name `ASSET_TRANSFER`. The code's own message —
"journal pre root does not continue the prior fragment" — asserts a continuation relation the
check cannot establish.

**Exploit (run, accepted):** a predecessor from a completely different lane is accepted and the
producer emits a byte-identical fragment.

```
[baseline]                  ACCEPTED fragment root=0x05450cbdac7b78 binding=0x9492f0446a23fe
[P1 foreign-lane prior]     ACCEPTED fragment root=0x05450cbdac7b78 binding=0x9492f0446a23fe
[P1b external-custody prior]ACCEPTED fragment root=0x05450cbdac7b78 binding=0x9492f0446a23fe
```

P1 used `lane_id=SPOT_LIQUIDITY, module_release_id=0x…4d, enabled=False,
producer_kind=NO_PRODUCER, binding_root=0x…22b`; P1b used `lane_id=EXTERNAL_CUSTODY,
producer_kind=REGISTERED_EMPTY_DISABLED, binding_root=ZERO_ROOT_V1` — a *registered-empty
disabled* lane's fragment accepted as the ASSET_TRANSFER receipt chain's predecessor. Only
`lane_state_root` had to match. No hash collision is needed: `LaneAllocationFragmentV1` does
not bind `lane_id` to `lane_state_root`, so the caller simply sets both.

**Impact today:** none (no acceptance path). **Impact at C9:** the chain-continuity property
the STALE_JOURNAL code is meant to carry is not actually enforced, and C9's assembler inherits
it. **Fix:** require `prior_fragment.lane_id is LaneIdV1.ASSET_TRANSFER` (and, for a genuine
receipt chain, `prior_fragment.module_release_id == lane_root.module_release_id`) before or
alongside the pre-root comparison.

### P2-2 — the module docstring states the opposite of what the module now does

`src/core/global_accounting_lane_producers_v1.py:1` and `:11-12`

```
"""Registered-empty lane fragment producers (wave A: EXTERNAL_CUSTODY, PROOF_REWARDS).
…
Research-only evidence. It grants no writer, verifier, release, or
publication authority, and no lane producer is receipt-backed.
"""
```

`produce_asset_transfer_fragment_v1` at `:273` sets
`producer_kind=LaneProducerKindV1.RECEIPT_BACKED`, and my accept probe confirms the returned
fragment carries it. The clause **"no lane producer is receipt-backed" is false at this
commit**, and the header still scopes the module to wave A. This is a pinned source file; a
reader auditing "is anything receipt-backed yet?" from the module header gets the wrong answer.
The Rust header (`…/global_accounting_lane_producers.rs:1-6`) is stale in the same way but
merely incomplete rather than false — it describes only the wave-A producer.

**Fix:** retitle to cover both waves and replace the clause with the accurate one already used
in the function docstring (`:198-201`): no *verifier admits* the journal yet, and the registry
keeps ASSET_TRANSFER at `NO_PRODUCER`.

### P2-3 — `TERMINAL_ROOT_NOT_EMPTY` is reachable and untested in **both** languages

`src/core/global_accounting_lane_producers_v1.py:239-242`; Rust `:259-266`.

Coverage map over the eight closed codes (grep of both test files):

| Code | Python | Rust |
|---|---|---|
| JOURNAL_LANE_DRIFT | ✓ | **✗** |
| LANE_DISABLED | ✓ | ✓ |
| MODULE_RELEASE_DRIFT | ✓ | **✗** |
| JOURNAL_ROOT_DRIFT | ✓ | ✓ |
| STALE_JOURNAL | ✓ | ✓ |
| **TERMINAL_ROOT_NOT_EMPTY** | **✗** | **✗** |
| ENTITLEMENT_COVERAGE_DRIFT | ✓ | ✓ |
| CONTROLLED_FOLD_OVERFLOW | ✓ | ✓ |

The six-way `pytest.mark.parametrize` at `tests/core/…_producers_v1.py:170-179` covers
`foreign_lane, disabled, release, post_root, stale_prior, coverage` — terminal-root is absent.

It is **not** an unreachable defensive check (unlike the fold ceiling, which C8 correctly
documents as unreachable). I constructed a fully well-formed accepted value carrying a nonzero
terminal root — `AssetLanePrivatePortV1` allows it (`allow_zero=True`,
`asset_lane_projection_v1.py:198-202`), and setting it consistently on the port **and** the
journal, then recomputing `_receipt_root`, satisfies every one of
`AssetTransferLaneModuleAcceptedV1.__post_init__`'s consistency checks:

```
constructed accepted with NONZERO terminal root: OK
TERMINAL CHECK REACHABLE -> REJECT TERMINAL_ROOT_NOT_EMPTY 'terminal root'
```

So this is a reachable reject path with no test, in a family the packet advertises as "eight
closed reject codes". Nothing catches it: the replay gate pins only the *counts*
(`PRODUCERS_PYTHON_GATE_EXPECTED_PASSED_V1 = 14`, `…RUST… = 5`), not which codes are exercised.
Repo discipline is explicit that a CBC change tests "each reject path".

### P2-4 — entitlement ordering/uniqueness escapes the closed reject family as a `ValueError`

`src/core/global_accounting_lane_producers_v1.py:210-213` (type gate) and `:279` (pass-through)

The gate pre-validates that `claimant_entitlements` is a tuple of exact
`ClaimantEntitlementRowV1`, and the coverage fold validates per-`(asset, control_domain)`
totals. Neither validates the **canonical ordering and uniqueness by
`(asset, claimant, control_domain)`** that `LaneAllocationFragmentV1.__post_init__` requires via
`_ordered_rows` (`…certificate_v1.py:338-345`). Entitlements are handed straight to the
constructor at `:279`, *after* every reject check has passed.

**Exploit (run):** two caller inputs whose per-key totals are exactly correct, both of which
raise instead of returning a value:

```
[P3 unordered ents]  RAISED ValueError: lane fragment claimant entitlements must be canonically ordered and unique
[P3b duplicate ents] RAISED ValueError: lane fragment claimant entitlements must be canonically ordered and unique
```

P3 used `(USD, zed, spot-pool, 2), (USD, alice, spot-pool, 3)` (correct total 5, wrong order);
P3b used `(USD, alice, spot-pool, 2), (USD, alice, spot-pool, 3)` (correct total 5, duplicate
key). The declared signature is `-> LaneAllocationFragmentV1 | ReceiptBackedProducerRejectedV1`
and the docstring promises "every reject is a no-op value naming its cause". This is fail-closed
and not a soundness hole, but the function is not total over its own declared input type, and
the failure carries no reject code.

**The Rust twin diverges here, and in the less safe direction.** Rust's
`LaneAllocationFragmentV1` is a plain struct with an *explicit* `validate()`
(`global_accounting_allocation_certificate.rs:397-440`) that performs the same per-row token/root
checks, the same strict-ordering-and-uniqueness test (`validate_ordered`, `:309-325`), and the
same `MAX_FRAGMENT_ROWS_V1 = 4_096` cap that Python enforces in `_ordered_rows`
(`…certificate_v1.py:334-343`). But `produce_asset_transfer_fragment_v1`
(`global_accounting_lane_producers.rs:307-330`) **never calls it** — Rust has no `__post_init__`,
so the struct literal is returned unvalidated. On the identical P3/P3b inputs Python raises and
Rust returns `Ok(fragment)` carrying unordered or duplicate entitlement rows; the same applies to
a >4096-row family. So for this input class the two implementations disagree on accept-vs-refuse,
which the "implemented in Python and Rust" claim does not admit.

**Fix:** pre-validate ordering/uniqueness in the Python type gate and add a ninth code (or reuse
`ENTITLEMENT_COVERAGE_DRIFT`), and have the Rust producer call `fragment.validate()?` before
returning — mapping its error into the same closed code so the twins agree.

### P3 findings

**P3-1 — the enum's "in check precedence" ordering is falsified by the repo's own test.**
`…_producers_v1.py:109-119` declares the codes "in check precedence" with
`ENTITLEMENT_COVERAGE_DRIFT` (`:118`) **before** `CONTROLLED_FOLD_OVERFLOW` (`:119`), and the
function docstring (`:187-192`) lists coverage as step 7 with the fold ceiling as a parenthetical
under it. The implementation runs both folds (`:243-260`) *before* the coverage comparison
(`:261`), so the overflow code always wins. This is not a corner case: an entitlement fold that
overflows can never match a controlled total (which is bounded by `MAX_ATOMS_U128_V1`), so
**every** overflow input is also a coverage-drift input, and the documented precedence demands
the other code. The repo's own `test_receipt_backed_producer_rejects_entitlement_fold_overflow`
is the witness — it asserts `CONTROLLED_FOLD_OVERFLOW`. I reproduced it:
`[P2 overflow+coverage] REJECT CONTROLLED_FOLD_OVERFLOW detail='entitlements'`. The Rust enum
carries no precedence claim and is therefore correct as written. Fix: swap the last two entries,
or drop the "in check precedence" phrase for that pair.

**P3-2 — the sidecar's binding sentence enumerates 7 of the 8 checks.**
`tools/o008_formal_cycle_admission_v1.py:3048` and `:3555` (the projected and the expected copy)
say the producer refuses "lane, release, post-root, carry-forward, terminal-root, coverage, and
fold-ceiling drift" — **`disabled` (`LANE_DISABLED`) is missing**. The `completion_scope`
sentence says "eight closed reject codes" without enumerating, so the two are not contradictory,
but the sidecar is the machine-pinned surface of record and it under-reports the enforcement by
one check. Compare the producer docstring (`:181-192`), which lists all eight, and the campaign
brief, which also lists eight.

**P3-3 — a Rust test names precedence coverage it does not provide.**
`zk/global_settlement_abi_v1/tests/global_accounting_lane_producers.rs:244`,
`receipt_backed_producer_rejects_binding_drifts_in_precedence_order`, mutates exactly one field
per case. No case makes two checks fail simultaneously, so no precedence *pair* is pinned in
either language. Given P3-1, the one precedence relation that is actually wrong is precisely the
one no test constrains.

**P3-4 — zero-amount entitlement rows are accepted, so `fragment_root` is not canonical under
economic equivalence.** `_require_atoms_u128` admits `0`, and the producer's fold is
total-preserving, so appending a zero row passes coverage:

```
[P5 zero-amount extra row] ACCEPTED fragment root=0x3429bd5775608b
                           ents=[('USD','alice','spot-pool',5), ('USD','zzz','spot-pool',0)]
```

versus baseline `fragment root=0x05450cbdac7b78`. Two economically identical entitlement sets
yield different committed fragment roots. The analogous lane projection explicitly forbids this
("asset lane projection must omit zero balances / zero custody rows",
`asset_lane_projection_v1.py:93-99`); the fragment row families do not. The certificate would
catch it downstream via `ENTITLEMENT_ROWS_DRIFT` against `state.liabilities`, so this is a
canonical-form gap, not a soundness one.

**P3-5 — every fragment field except the (as-yet unverified) `binding_root` is invariant under
custody owner, chain, epoch, and occurrence.** `_bound_journal`
(`asset_transfer_lane_module_v1.py:312-326`) copies `pre/post_lane_root` from the *base* module
journal, i.e. roots over `AssetTransferStateV1` (policies, balances, supplies) — which does not
contain custody, chain id, writer epoch, or command occurrence. Measured:

```
post_lane_root equal (different custody owner):        True   receipt_root equal: False
owner=pool-a  : lane_state_root=0x25c944386c9f  controlled=[('pool-a', 5)]
owner=mallory : lane_state_root=0x25c944386c9f  controlled=[('mallory', 5)]

post_lane_root same across chain_id change:            True
post_lane_root same across writer_epoch/occurrence:    True
fragment identical except binding_root (chain):        True
fragment identical except binding_root (epoch/occ):    True
```

So the committed lane root does **not** determine the fragment's `controlled_locations`, and no
fragment field ties it to a chain or epoch. The receipt root does carry all of it (via
`statement_root` and `port_root`), which is exactly why `binding_root = journal.receipt_root` is
the right design — but it means the integrity of C8's controlled rows rests entirely on a
receipt verification that does not exist yet. The function docstring's NONCLAIM discloses this
("no verifier admits that journal yet (C9), the caller is trusted for `accepted`"); the
`completion_scope` sentence, which a reader meets first, says only "binding the fragment to the
journal receipt root" and does not convey that the committed lane root carries none of it.
Worth a clause in the sentence, and a mandatory obligation on C9.

**P3-6 — no mechanical Python/Rust pin on the producer reject-code family.** The certificate's
codes are pinned as a closed constant `CERTIFICATE_REJECT_CODES_V1`
(`tools/o008_formal_cycle_admission_v1.py:411-428`) and cross-checked against the Python class
(`:2974`, `:3024-3027`). The producer families (wave A's 3 and wave B's 8) have no such
constant, no order pin, and no cross-language comparison — the parity I verified by hand is
maintained by hand. Given P3-2 (prose that already drifted by one check), the "eight closed
reject codes" claim currently rests on the test counts alone.

**INFO — serde derive asymmetry.** Wave A's `LaneProducerRejectCodeV1` carries
`#[derive(… Deserialize, … Serialize)] #[serde(deny_unknown_fields)]`
(`…/global_accounting_lane_producers.rs:18-19`); wave B's `ReceiptBackedProducerRejectCodeV1`
(`:113-114`) carries neither, although the Python twin **is** registered in
`GLOBAL_SETTLEMENT_CANONICAL_ENUM_TYPES_V1`. Nothing serializes either today; flagging only for
consistency.

## 4. P16 P3 direction (duty 4) — NOT REGRESSED

`git diff 06a3591f7 31671bab8 -- tools/build_o008_formal_cycle_v1.py
tools/check_o008_formal_cycle_v1.py tools/o008_formal_cycle_shell_v1.py` is **empty**. The
post-replay re-verification is intact and still S-bound:

- `tools/build_o008_formal_cycle_v1.py:79` —
  `_require_worktree_equals_subject(root, snapshot, code="REPLAY_WORKTREE_MUTATED")` runs after
  `shell.run_proof_replay_v1`, comparing every `core.SOURCE_PIN_PATHS_V1` path's working bytes
  against the **subject snapshot** blob sha256 (`:52-58`).
- `tools/o008_formal_cycle_admission_v1.py:3988-4006` — `replay_worktree_mutation_errors_v1`
  fails closed on a missing pin as well as a changed one.

The P16 P3 itself (the re-verification set is the pinned + hygiene closure rather than the full
transitive read set) remains open as recorded — it was logged as a direction for a future
candidate, not a required fix, and C8 neither addresses nor weakens it.

## 5. Summary

| # | Sev | Finding | Location |
|---|---|---|---|
| P2-1 | P2 | Carry-forward accepts a foreign-lane predecessor (`prior_fragment.lane_id` unchecked) | `global_accounting_lane_producers_v1.py:235-238`; rs `:251-258` |
| P2-2 | P2 | Module docstring: "no lane producer is receipt-backed" is false | `global_accounting_lane_producers_v1.py:1, 11-12` |
| P2-3 | P2 | `TERMINAL_ROOT_NOT_EMPTY` reachable, untested in both languages (Rust also misses 2 more) | `:239-242`; tests `:170-179` |
| P2-4 | P2 | Unordered/duplicate entitlements raise `ValueError` instead of a closed code; Rust never calls `validate()` and returns them | `:210-213, 279`; rs `:307-330` |
| P3-1 | P3 | Enum "in check precedence" inverted for coverage vs fold-ceiling | `:109-119, 187-192` |
| P3-2 | P3 | Sidecar binding sentence omits `disabled` (7 of 8 checks) | `o008_formal_cycle_admission_v1.py:3048, 3555` |
| P3-3 | P3 | Rust test claims precedence coverage it does not provide | `tests/…producers.rs:244` |
| P3-4 | P3 | Zero-amount entitlement rows accepted; `fragment_root` non-canonical | `:252-260` |
| P3-5 | P3 | Only `binding_root` carries custody/chain/epoch; completion-scope sentence understates it | `asset_transfer_lane_module_v1.py:312-326` |
| P3-6 | P3 | No mechanical py/rust pin on the producer reject-code family | `o008_formal_cycle_admission_v1.py:411-428` (contrast) |

**Promotable after repair.** The envelope, the authority ceiling, the receipt binding, the
coverage/partition agreement and the type boundaries are all clean, and the two documented
findings C8 volunteered (fold-ceiling unreachability, no acceptance path) both check out as
stated. P2-1 and P2-4 should be closed before C9 builds on this producer; P2-2 is a one-line
correction; P2-3 needs one test per language.
