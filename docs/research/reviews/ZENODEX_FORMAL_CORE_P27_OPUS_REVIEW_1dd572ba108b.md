# Opus independent review — candidate C8-p10 (O-008 formal cycle)

Reviewer: Opus (independent). Authority granted by this review: **NONE**.
Date: 2026-09-02.

| Field | Value |
|---|---|
| Branch | `codex/formal-core-fable-20260901` |
| Subject commit S27 | `f1e2b83816069eea90b9dac4b519f2e19c4f1a03` |
| Subject parent | `cd4014894881136ce160d3324eb1951591882c84` (R23 receipt) |
| Subject tree | `7faa6ef26fd2a075f5a64e8e8f4c753a0d614446` |
| Artifact commit P27 | `1dd572ba108bd1d168c665b3ea2663b9a7ad2067` |
| Review worktree | `/tmp/zenodex-formal-core-opus-c8p10` (detached at P27) |
| Prior receipt | R23 `cd4014894`, grade A- (0 P1, 0 P2, 3 P3) |

## Verdict

**Grade: B**

The three P26 findings are repaired well — NEW-16 is closed beyond what the
finding asked for, NEW-17 is exact, NEW-18 takes the honest-defensive route,
which is the right call. The 28-command replay reproduces the author record
byte-for-byte and the claim ceiling does not move.

The grade is held at B, not A-, by one new P1: the V1 asset-transfer reject
family drifted from 11 to 12 members **six commits before S27**, four V1
refinement artifacts were never updated, and **three tests that detect exactly
this are RED at the reviewed head**. They are red in neither the packet's gate
set nor CI's critical gate, so every replay is green while a detector sits
failing. The candidate under review is a *repair of cross-language reject-family
drift*; a live, undisclosed instance of that same defect class in the same
family is squarely in scope.

## Replay results

All commands run in a clean detached worktree at P27, `CARGO_TARGET_DIR=/tmp/zenodex-opus-c8p10-cargo`,
`CARGO_INCREMENTAL=0`, Lean gates strictly serially.

| Gate | Result |
|---|---|
| `check_o008_formal_cycle_v1.py` (no `--replay`) | exit 0, `packet_admitted: true`, `current_applicable: true`, `NOT_RUN`, 0 errors, 0 drift |
| `check_o008_formal_cycle_v1.py --replay` | exit 0, **`EXECUTED_PASS`, 28/28 runs, 0 failing** |
| Author-record comparison | **28/28 `comparable` blocks byte-identical**, incl. ESSO fingerprints, Lean probe hashes, every pass count |
| `cargo fmt --check` | clean (exit 0) |
| `cargo test --offline --locked` (all targets) | **527 passed, 0 failed** |
| Directly relevant Python files (6 files) | **185 passed, 0 failed** |
| `tests/formal/test_lean_asset_transfer_refinement_v1.py` (isolated) | **3 failed, 37 passed** — see NEW-19 |
| `tests/formal/test_lean_asset_lane_refinement_v2.py` | 12 passed |

Toolchain reproduced exactly as recorded: Lean 4.27.0, Python 3.12.3, cargo/rustc
1.87.0 (`17067e9ac6d7ecb70e50f92c1944e545188d2359`), z3 4.15.4, cvc5 1.1.2,
ESSO code hash `7f80c6216be85c827e8d1cc2fa08ee3107a74588`.

### Claim ceiling — unchanged

Structural diff of `ZENODEX_O008_FORMAL_CYCLE_V1.json` across P27 shows exactly
four changed leaves, all subject pins:

```
/subject_commit        240255e1e… -> f1e2b8381…
/subject_parent        071a6b5f4… -> cd4014894…
/subject_tree          13729394d… -> 7faa6ef26…
/packet_commit_parent  240255e1e… -> f1e2b8381…
```

Every `claim_ceiling` key is untouched: `production/settlement/publication/
verifier/migration/release/value_movement_authority = NONE`,
`value_movement_gates_closed = 0/12`, `formal_core_complete = false`,
`whole_value_movement_safe = false`. **The ceiling did not move.** The checker
emits the ceiling from module constants, not packet content, and the emitted
ceiling matches.

S27 touches only 2 test files and adds 2 THV1 evidence files; no production
source byte changed. All 24 THV1 `source_pins`/`test_pins` sha256 values match
the tree exactly (0 bad).

## P26 finding closure

| ID | Verdict | Basis |
|---|---|---|
| NEW-16 (enum scanner drops unparsed lines) | **CLOSED** | 3/3 survivors now fail loudly; 7 further mutant shapes also killed; count pin does real work |
| NEW-17 (stale total-parity docstring) | **CLOSED** | Docstring now matches `rglob` exactly |
| NEW-18 (BALANCE_OVERFLOW coverage) | **CLOSED (with residuals)** | Honest-defensive treatment is the right call; transfer arm gets a real witness; managed arm gets a bounded refutation |

### NEW-16 — CLOSED

The scanner now asserts on any non-blank enum-block line that is not exactly
`SCREAMING_SNAKE,`. I replayed my three P26 survivors against the **real** test
node by mutating `zk/global_settlement_abi_v1/src/asset_transfer_types.rs` in my
own worktree (restored clean afterwards):

| Survivor | Old scanner | New scanner |
|---|---|---|
| Rust-only variant, no trailing comma (`SHADOW_ADMIT`) | 12 vars, **silently equal** | `AssertionError: unparsed enum line 'SHADOW_ADMIT'` |
| Rust-only CamelCase variant (`ShadowAdmit,`) | 12 vars, **silently equal** | `AssertionError: unparsed enum line 'ShadowAdmit,'` |
| Rust-only tuple variant (`SHADOW(u8),`) | 12 vars, **silently equal** | `AssertionError: unparsed enum line 'SHADOW(u8),'` |

Baseline unmutated: exit 0. Seven additional shapes I invented are also killed:
explicit discriminant (`EXTRA = 7,`), two variants on one line, trailing line
comment, per-variant attribute, doc comment inside the block, lowercase variant,
struct variant. The block-extraction split also fails loudly if the enum header
is absent (IndexError) or a struct variant truncates the block.

The pinned member counts (12, 15) are **not** padding: a coordinated 13th member
added to *both* Python and Rust passes the list equality and is caught by the
count assert at `tests/core/test_transition_resource_bound_totality_v1.py:206`.
Verified by mutation.

Residual (not a finding, a stated limit): a coordinated **rename** or **reorder**
of the same number of members on both sides passes both the equality and the
count pin. In principle the golden vectors cover this; see NEW-19 for where that
assumption currently fails.

### NEW-17 — CLOSED

Docstring: "Every `pub const MAX_...` declaration in every .rs file under the
crate's src/ tree (recursive)". Code: `crate_src.rglob("*.rs")` with
`crate_src = zk/global_settlement_abi_v1/src`. Exact match, and the scope limit
(src/ only) is now stated rather than implied. Cosmetically the reflow leaves
awkward line breaks ("whatever its type / spelling", "must / resolve through this
single / mapping"); no correctness impact.

### NEW-18 — CLOSED with residuals

**The honest-defensive treatment answers the finding, and is the better answer
than manufactured coverage.** My finding was that BALANCE_OVERFLOW had a claimed
coverage row with no asserting test. Fabricating an in-domain reach would have
required weakening a real invariant. Two arms, two honest treatments:

*Transfer arm — genuine asserting witness.* I verified the reachability argument
independently: `AssetTransferStateV1.__post_init__` enforces
`sum(balances per asset) <= supply` (`asset_transfer_types_v1.py:111-113`), and
both `EconomicAmountV1` and `AssetSupplyV1` bound `amount_atoms <= MAX_ATOMS_V1`
via `_require_atoms_u128`. Since transfer deltas sum to zero, every post-balance
is bounded by the asset total, hence by supply, hence by `MAX_ATOMS_V1`. The arm
is genuinely unreachable in-domain, and the test reaches it only by forging past
`__post_init__`, getting the closed typed reject rather than a wrap or a raise.
This is a real witness of a real guard.

*Managed arm — bounded refutation.* Verified: `_snapshot_state` reconstructs
`ManagedAssetLifecycleStateV1(...)`, re-running `__post_init__`, so the forged
state raises before any fold. And in-domain, `_post_supply` runs before
`_post_balances`, so `SUPPLY_OVERFLOW` fires first. Both claims hold.

Residuals (P3-tier, folded into the grade but not blocking):

1. The docstring's parenthetical "(verified: supply at the ceiling yields
   `SUPPLY_OVERFLOW`)" is **true** — `tests/core/test_managed_asset_lifecycle_module_v1.py:381-392`
   pins exactly that — but that node is not in the THV1 `test_pins`, so the
   evidence packet cites a verification it does not pin.
2. `assert ManagedAssetLifecycleRejectCodeV1.BALANCE_OVERFLOW.value == "BALANCE_OVERFLOW"`
   is a tautology by the repo's own bar: it is already implied by
   `all(member.value == member.name ...)` in the family test. It makes the
   managed test *look* like it touches the arm when it does not. Drop it, or
   state in the docstring that the arm is deliberately unwitnessed.
3. The managed test has no mutation row in the THV1 packet — correct, since it
   kills nothing about BALANCE_OVERFLOW, but the test name
   (`..._balance_overflow_is_a_defensive_guard_with_a_forgery_witness`) promises
   a witness the body does not deliver. The transfer test earns that name; the
   managed one does not.

**On deferring cross-language reject precedence:** as stated, this should not
block — precedence pinning is real work and naming it as deferred is honest.
**However**, see NEW-19: precedence is *not* unpinned. `REJECT_PRECEDENCE_V1` in
`tools/check_asset_transfer_refinement_v1.py` and `reject_precedence` in
`tests/data/asset_transfer_refinement_v1.json` are precedence pins, they are
stale at 11 members, and their tests are red. "Deferred" understates it; the
accurate statement is "pinned, drifted, and failing".

## New findings

### NEW-19 (P1) — the V1 asset-transfer reject family drifted to 12 members; four refinement artifacts are stale and three detector tests are RED at the reviewed head

**Status at P27: three tests fail.**

```
tests/formal/test_lean_asset_transfer_refinement_v1.py::test_lean_guard_order_matches_python_enum_and_transition_source
tests/formal/test_lean_asset_transfer_refinement_v1.py::test_report_reject_code_rows_match_python_enum
tests/formal/test_lean_asset_transfer_refinement_v1.py::test_report_covers_exactly_the_vector_table
```

Isolated run of that file: **3 failed, 37 passed in 86.52s.** The other 37 —
including the `lake env lean` typechecks — pass, so this is not an environment
artifact. The failure is a plain value comparison:

```
>       assert lean_order == enum_order
E       AssertionError: Right contains one more item: 'POST_STATE_RESOURCE_BOUND_EXCEEDED'
tests/formal/test_lean_asset_transfer_refinement_v1.py:508
```

**Root cause.** Commit `a18699202` ("security: incorporate PR #532 and close the
P24 residuals"), an ancestor of S27 six commits back on this branch, added
`POST_STATE_RESOURCE_BOUND_EXCEEDED` to the Python and Rust V1 transfer reject
families (11 -> 12) and did not touch the V1 refinement artifacts. Confirmed:
`git show --stat a18699202` touches no Lean file.

**Stale carriers — all still at 11 members:**

| Artifact | Stale surface |
|---|---|
| `lean-mathlib/Proofs/AssetTransferRefinementV1.lean` | `inductive RejectCode` (11 ctors, L137-149), `RejectCode.code` (L152-163), `RejectCode.rank` (0..10, L166-177) |
| `lean-mathlib/Proofs/AssetTransferRefinementV1Challenge.lean` | same family |
| `tools/check_asset_transfer_refinement_v1.py` | `REJECT_PRECEDENCE_V1` 11-tuple (L44-47) |
| `tests/data/asset_transfer_refinement_v1.json` | `reject_precedence`, `unreachable_codes` |

Python `AssetTransferRejectCodeV1` and Rust `AssetTransferRejectCodeV1` both
carry 12. The Lean `RejectCode` is a **closed inductive**: the refinement model
cannot even express the runtime's 12th reject code, so the V1 asset-transfer
refinement — a headline evidence class for this campaign — is incomplete with
respect to the code it claims to refine. Its docstring ("matching the Python enum
values") is now false.

**Why nothing catches it.**

- The packet's 28 replay commands do not include `tests/formal/test_lean_asset_transfer_refinement_v1.py`.
  The Lean gates run `GlobalClaimantCustodyRelationV1.lean` and
  `GlobalAccountingAllocationCertificateV1.lean` only.
- CI's `tools/run_critical_quality_gate.sh` runs a hand-maintained list of 66
  test paths; that file is not on it (verified by grep).
- So the detector exists, is correct, is red, and is outside every enforced gate.

**Why this is in scope for C8-p10 and why it is P1 for this campaign.** The
candidate under review exists to harden a cross-language reject-family drift pin
(NEW-15/NEW-16). It strengthened the Python<->Rust edge to near-total. The same
family has a *live, already-detected, four-artifact* drift on the Python<->Lean
edge, and the packet's own claim scope asserts the opposite of the truth —
"cross-language reject PRECEDENCE remains unpinned (deferred, named honestly)" —
when the precedence pin exists and is failing. This is the campaign's own
recurring "scanner narrower than its row" shape, one level up: the *pin* was
widened while the *gate set* stayed narrow enough to keep the replay green.

It is not attributable to S27 — S27 changed no production byte and did not
introduce it — but it is undisclosed in every packet and receipt on this branch
(`grep` over `docs/` and `tests/evidence/` finds no mention of any of the three
node ids, nor of `AssetTransferRefinementV1`).

**Suggested repair.** Extend the Lean `RejectCode` inductive, `code`, and `rank`
to 12; add the code to `REJECT_PRECEDENCE_V1` and the corpus at its true
precedence position (last, after `BALANCE_OVERFLOW`, matching `_post_balances`);
regenerate the corpus; then add the three node ids to the packet's replay set so
the gate is as wide as the claim. If the intended position in the precedence
order is disputed, that dispute is itself the reason a precedence pin is needed.

### NEW-20 (P3) — the `rglob` recursion repair (P25 NEW-13, re-documented by NEW-17) has no regression pin and is currently vacuous

`test_every_canonical_rust_bound_has_a_python_twin` scans `crate_src.rglob("*.rs")`.
Today every one of the 37 `pub const MAX_` declarations lives in `src/*.rs`
directly; the only files under a subdirectory
(`src/economic_command_authentication/{witness,types}.rs`) declare none.
Verified: `glob("*.rs")` and `rglob("*.rs")` return **identical 37-bound sets**.

So reverting `rglob` to `glob` leaves every test green. NEW-17 has just made the
docstring *assert* recursion, which raises the stakes: the prose claim is now
strictly stronger than anything enforced.

Cheap fix: assert that the scanned file set contains at least one file whose
parent is not `crate_src` (true today, and it fails loudly if the glob narrows or
the subdirectory is removed), or add a fixture bound in a subdirectory.

### NEW-21 (P3) — sibling transitions on the same lane have divergent hostile-input postures, and NEW-18's own evidence walks past it

`transition_managed_asset_lifecycle_v1` guards its inputs with exact-type checks
and a deep re-validating snapshot (`_snapshot_state`, L361-380).
`transition_asset_transfer_v1` guards with `isinstance` only (L297-302) and does
not re-snapshot. Demonstrated in this worktree:

```
class EvilState(AssetTransferStateV1):
    __slots__ = ()
    def __post_init__(self): pass                       # skip every invariant
    @property
    def state_root(self): return "0x" + "ff"*32          # attacker-chosen root

transition_asset_transfer_v1(ctx, EvilState(...), cmd)
  -> AssetTransferAcceptedV1
  -> the forged root appears verbatim in the accepted effect plan's lane write
```

The same shape against the managed sibling is refused:
`TypeError: managed asset lifecycle pre-state must be the exact typed value`.
A second variant (balances >> supply, `__post_init__` skipped) makes the transfer
transition raise an uncaught `ValueError` from post-state construction — a
totality break in a function this campaign has been busy totalising.

**Severity is P3, not higher**, because the deployed path is protected: the lane
wrapper `asset_transfer_lane_module_v1.py` does apply exact-type checks
(L147-157) and `_snapshot_asset_transfer_state_v1` re-runs the constructor, and
it is the only in-repo caller. So this is a defense-in-depth inconsistency, not a
reachable defect.

It is raised here because the NEW-18 repair **compared these two arms directly**
— "the transfer arm reaches the arm, the managed arm is refused by snapshot
re-validation" — and recorded the divergence as if both were intended, rather
than noting that the divergence exists because the transfer module lacks the
hardening its sibling has. Either harden `transition_asset_transfer_v1` to match,
or state in both docstrings that the transfer module's hostile-input boundary is
its lane wrapper.

## Observations (not findings)

- `tests/core/test_zusd_liquidation_partition.py` cannot be collected anywhere
  (`generated.liquity_v1_sp_offset_redistribution_bounded` is untracked and
  absent in both worktrees). Pre-existing, unrelated to this candidate.
- A bare `pytest tests/formal` run reports 142 failures, but the large majority
  are environment-driven: the ESSO suites need `PYTHONPATH`/`ZENO_ESSO_PYTHON`
  (the same nodes pass 20/20 and 24/24 inside the checker replay, which sets
  them), and many `..._typechecks` nodes need a built local `Proofs` library.
  I did not treat those as findings. The three NEW-19 failures are the exception:
  they are pure value comparisons and fail in an isolated run where the other 37
  tests in the same file, including the lake typechecks, pass.
- `tests/core/test_ab_child_frontier_transition_group_compression_20260629.py`
  fails 2 of 7 (`..._report`, `..._cli_replay`). This is a 2026-06-29 A/B
  research family last touched by `12d5704bd` / `49569cff5`, unrelated to this
  campaign; the canonical checkout already carries its `generated/.../report.json`
  as locally modified. Pre-existing artifact drift, not a finding here.
- Those A/B research tests **write into the tracked tree** when run: after my
  sweep, 31 `generated/*/report.json` and `docs/research/ZENODEX_AB_*.md` files
  were locally modified. That is why they fail — they regenerate and compare
  against a stale committed artifact. Worth its own ticket outside this review;
  a test that mutates tracked files is not a gate.
- A whole `pytest tests/core` sweep is not practical for a review of this size
  (2% in ~40 minutes); I stopped it and instead ran the six files that the
  candidate actually touches or depends on (185 passed, 0 failed) plus targeted
  diagnosis of the two early failures above.

## Review hygiene

- Every mutation I made to replay the NEW-16 survivors was reverted; `git diff`
  over `src/`, `tests/`, `zk/`, `tools/`, `lean-mathlib/` and the packet JSON is
  empty at the end of this review. The only dirty paths are the 31 research
  artifacts the A/B tests rewrite themselves.
- The fable worktree and the canonical checkout were not modified.
- **Note:** while this review ran, `codex/formal-core-fable-20260901` advanced two
  commits past P27 to `8d86d6248` ("freeze the O-008 formal-cycle packet at C9a",
  on `431b5679d` "land C9a receipt admission for the asset-transfer fragment").
  P27 remains an ancestor, so this review is of a valid point in that history,
  but it does **not** cover C9a. NEW-19/NEW-20/NEW-21 are all in code that C9a
  did not obviously touch and should be re-checked against the new head.

## Grade

**B.**

- Replay integrity: excellent. 28/28 EXECUTED_PASS, byte-identical to the author
  record, zero drift, cargo 527/0 with `fmt --check` clean, claim ceiling frozen.
- Repair quality: NEW-16 is a model repair — it closes the finding, generalises
  past it, and its own count pin survives mutation testing. NEW-17 is exact.
  NEW-18 chooses honesty over manufactured coverage, which is the correct call
  and is well-argued; its residuals are cosmetic.
- Held below A- by NEW-19: a P1-class, four-artifact, six-commit-old drift in the
  *same reject family this candidate is hardening*, with three red detector tests
  at the reviewed head, undisclosed in every packet, and invisible to both the
  packet gate set and CI. A candidate whose subject is reject-family drift should
  not ship while a live instance of it is red in the tree.
- NEW-20 and NEW-21 are P3 and do not move the grade on their own.

Fixing NEW-19 (12-member Lean/corpus family + adding the three nodes to the
replay set) and trimming the NEW-18 residuals would put this at A-.

## Authority

This review grants **no** authority. The claim ceiling is unchanged and must
remain: `production/settlement/publication/verifier/migration/release/
value_movement_authority = NONE`, `value_movement_gates_closed = 0/12`,
`formal_core_complete = false`, `whole_value_movement_safe = false`,
`o008_status = OPEN_EXACT_ALL_12_RECONCILIATION_MISSING`.
