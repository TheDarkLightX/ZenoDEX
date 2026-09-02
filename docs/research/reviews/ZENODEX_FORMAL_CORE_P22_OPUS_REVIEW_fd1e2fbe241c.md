# Opus independent review — candidate C8''''' (repair of P21 / receipt R18)

- Reviewer: Opus, independent. Authority granted by this review: **NONE**.
- Branch: `codex/formal-core-fable-20260901`
- Subject S22: `b0c6d1d0f20b99ef4afc036653fd3cec340c7781`
- Artifact P22: `fd1e2fbe241ca31aba68d3747dd763de11197366`
- Prior receipt R18: `24dd5e42a984d61b4a2259ab90791c50e6fe4316` (A-; 0 P1, 0 P2, 3 P3)
- Review worktree: `/tmp/zenodex-formal-core-opus-c8p5` (detached at P22, clean throughout; `git status --porcelain` empty at every checkpoint)
- Date: 2026-09-02

## Grade: A-

**0 P1, 0 P2, 4 P3.** All three P21 findings are CLOSED and observation 1 is correctly
taken. Every P21 repair is mechanically real, not asserted: I reproduced the killer
behaviour of both new tests end-to-end against mutated inputs. The grade is held at A-
rather than A by NEW-7: the evidence packets and the test docstring state the NEW-4
parity claim as unqualified ("TOTAL", "every `pub const MAX_` bound"), and I have a
**concrete surviving mutant** of the mutation-table class that the resource-bounds-v2
packet declares killed. That is a defect in the evidence, not in the implementation.

The claim ceiling did not move.

---

## 1. Topology and admission

`git rev-list --parents -n 1` confirms a single-parent chain, artifact-only leaf:

```
fd1e2fbe2 (P22) -> b0c6d1d0f (S22) -> 24dd5e42a (R18 receipt)
```

P22 diffstat is exactly the two packet files (48 insertions / 48 deletions):
`docs/research/ZENODEX_O008_FORMAL_CYCLE_V1.{json,md}`. S22 touches 13 files
(1914 insertions / 19 deletions), of which four are new/updated THV1 evidence packets.

### Checker, non-replay mode

```
$PY tools/check_o008_formal_cycle_v1.py --root /tmp/zenodex-formal-core-opus-c8p5 \
    --packet-commit fd1e2fbe241ca31aba68d3747dd763de11197366
```

exit 0 — `ok: true`, `packet_admitted: true`, `errors: []`, `current_source_drift: []`,
`current_applicable: true`, `proof_replay.status: NOT_RUN`. The author record correctly
did **not** upgrade the replay status. stderr empty.

### Checker, replay mode — EXECUTED_PASS, 28/28

```
$PY tools/check_o008_formal_cycle_v1.py --root /tmp/zenodex-formal-core-opus-c8p5 \
    --packet-commit fd1e2fbe241ca31aba68d3747dd763de11197366 --replay \
    --python "$PY" --esso-python /home/trevormoc/Downloads/ESSO/.venv/bin/python \
    --esso-pythonpath /home/trevormoc/Downloads/ESSO
```

exit 0, stderr empty, `proof_replay.status: EXECUTED_PASS`, 28 runs all `exit_code 0`.
Every count matched the packet expectation:

| command_id | observed | command_id | observed |
| --- | --- | --- | --- |
| lean_version | 4.27.0 | prior_restage_gate | 136 passed |
| lean_direct_check | empty stdout | python_version | 3.12.3 |
| lean_axioms_probe | 25 theorems | python_projection_gate | 13 passed |
| lean_binding_gate | 6 passed | rust_projection_gate | 7 passed |
| lean_certificate_direct_check | empty stdout | rust_version | cargo 1.87.0 |
| lean_certificate_axioms_probe | ok | rust_refinement_gate | 41 passed |
| lean_certificate_binding_gate | 6 passed | python_golden_gate | 35 passed |
| esso_validate | ir_hash ok | rust_golden_gate | 3 passed |
| esso_verify_multi | solvers agreed | rust_bounded_vec_unit_gate | 1 passed |
| esso_gate | 20 passed | python_certificate_golden_gate | 37 passed |
| esso_certificate_validate | ir_hash ok | rust_certificate_golden_gate | 3 passed |
| esso_certificate_verify_multi | solvers agreed | rust_certificate_unit_gate | 4 passed |
| esso_certificate_gate | 24 passed | python_producer_gate | 30 passed |
| | | rust_producer_gate | 7 passed |

The two Lean gates and the cargo gates were executed by the checker strictly serially;
no concurrent Lean invocation occurred at any point in this review.

### Claim ceiling — unchanged

```
formal_core_complete        false
formal_cycle_status         FORMAL_CYCLE_COMPLETE_O008_OPEN
o008_status                 OPEN_EXACT_ALL_12_RECONCILIATION_MISSING
supported_claim             O008_RELATION_NECESSARY_CHECKS_AND_INFORMATION_LOSS_PROVED
migration/production/publication/release/settlement/value_movement/verifier  NONE
value_movement_gates_closed 0 of 12
whole_value_movement_safe   false
```

Identical in both checker modes and in the committed packet. Nothing raised it.

### Independent batteries

| Battery | Command | Result |
| --- | --- | --- |
| Full cargo | `cargo test --offline --locked` in `zk/global_settlement_abi_v1` | **53 suites, 523 passed, 0 failed, 0 ignored** |
| cargo build | `cargo build --offline --locked` | **0 warnings** |
| New repair tests | `pytest tests/core/test_global_settlement_abi_v1_resource_bounds.py` | **18 passed** |
| Module suites | transfer + managed-lifecycle + both lane modules + projection gate + checker gate | **456 passed** |
| Closure digest | `tools/check_global_settlement_canonical_manifest_v1.py` | **PASS** (re-pin `9caa14e6…` correct) |
| Test hygiene | `tools/check_test_hygiene_v1.py --base-ref 24dd5e42a` | **ok: true**, 7 critical paths covered, 4 selected evidence ids |
| ruff (configured) | `ruff check src/core/global_settlement_types_v1.py` | **All checks passed** |

The hygiene checker (which the O-008 checker explicitly does not run — nonclaim 9)
selects exactly the four expected packets: `claimant-backing-guard-golden-v16`,
`semantic-restage-v5`, `resource-bounds-v2`, `o008-formal-cycle-admission-v23`.

---

## 2. Closure table

| P21 finding | Verdict | Evidence |
| --- | --- | --- |
| NEW-4 — total parity over `canonical.rs` | **CLOSED** (residual → NEW-7) | Hand-maintained name list gone; new test kills the drift class end-to-end (M1/M5/M12 below) |
| NEW-5 — constant placement | **CLOSED** (residual → NEW-8) | Constants at `global_settlement_types_v1.py:32-34`, exactly Rust declaration positions 6/7/8; stray block deleted; `__all__` order verified by AST |
| NEW-6 — non-total boundary | **CLOSED** (residuals → NEW-9, NEW-10) | Both docstrings accurate in both languages; boundary test causally sound (4095 accepts, 4096 raises) |
| Observation 1 — `completion_scope` wording | **TAKEN** | `tools/o008_formal_cycle_admission_v1.py:275`; remaining bare instances are grammatically registry-scoped and correct |

### NEW-4 — CLOSED

`tests/core/test_global_settlement_abi_v1_resource_bounds.py:190-238`
(sha256 `8fa0cc4b12db685208e409975547b0f92c55b8e855d0a7ff9c6df39ebe268016`).

I ran the **actual in-repo test** against mutated copies of `canonical.rs`, using a
mirror directory (`/tmp/c8p5-mut`) whose `src` is a symlink to the worktree so that
`Path(__file__).resolve().parents[2]` resolves to the mutated tree. The worktree itself
was never modified.

| Mutant | Expected | Observed |
| --- | --- | --- |
| baseline | pass | **1 passed** |
| M1 `pub const MAX_SYNTHETIC_ROWS_V1: usize = 77;`, no Python twin | fail | **1 failed** ✓ |
| M5 `MAX_ASSET_BALANCE_ROWS_V1: usize = 8_192` (value drift) | fail | **1 failed** ✓ |
| M12 delete `MAX_ASSET_CUSTODY_ROWS_V1` from Rust | fail | **1 failed** ✓ (`>= 24` floor) |

Unparseable expression forms fail **loudly** rather than silently (fail-closed):
`0xFF` → `ValueError: invalid literal for int()`; an alias to another const → same;
`(1 << 64) - 1` → same. Good.

`canonical.rs` currently declares exactly 24 `MAX_` bounds (lines 6-29), so the
`>= 24` floor is tight, not slack.

**The special case is sound.** `python_twins["MAX_LANE_MODULE_RECEIPT_BYTES_V1"]` at
line 232 is justified: the Python constant is `16 * 1024 * 1024` at
`src/core/lane_module_receipt_verification_v1.py:85` and the Rust constant is
`16 * 1_048_576` at `zk/global_settlement_abi_v1/src/canonical.rs:27` — both 16777216 —
and both guard the same quantity at the same point
(`lane_module_receipt_verification_v1.py:339` vs `lane_module_receipt_verification.rs:225`,
`receipt_bytes` length). It is a special case only because the Python twin lives outside
`global_settlement_types_v1`, so `getattr(types, name)` cannot reach it. Its removal from
Rust would be caught: line 232 writes the key unconditionally, so
`set(python_twins) - set(rust_bounds)` would be non-empty.

### NEW-5 — CLOSED

`src/core/global_settlement_types_v1.py:32-34`
(sha256 `8d37ed72fcf15cf7849179d4ff358f4fbbdc33905348f7ab790b2fe090e8044d`):

```
MAX_ASSET_POLICY_ROWS_V1: Final = 256
MAX_ASSET_BALANCE_ROWS_V1: Final = 4_096
MAX_ASSET_CUSTODY_ROWS_V1: Final = 4_096
```

between `MAX_POLICY_BINDINGS_V1` (:31) and `MAX_EFFECT_PLAN_ROWS_V1` (:35), as required.
Side-by-side against `canonical.rs:6-29`, the Python mirror block reproduces the Rust
declaration order exactly for positions 1-21; the only divergences past that point are
`MAX_LANE_MODULE_RECEIPT_BYTES_V1` (lives in another Python module, the known special
case) and `MAX_U64_V1` (Python-only) — both pre-existing, neither introduced here. The
three new constants land at positions 6/7/8, matching `canonical.rs:11-13`.

The stray block formerly at `:1354` is gone. `__all__` verified by AST parse: for all
`MAX_`/`MIN_` names, `__all__` order equals module declaration order, and the three new
names joined in declaration order. All 69 `__all__` entries resolve; no duplicates.

The `semantic-restage-v5` claim is **honest**. Its `claim_scope` reads "…in Rust
declaration order **with the block's literal convention** … byte moves only, no value,
function, inequality, message, or precedence changed." The literal restyle `4096` →
`4_096` is disclosed by that clause, and 4096 == 4_096, so "no value changed" is true.

### NEW-6 — CLOSED

Both docstrings — `src/core/asset_transfer_module_v1.py:286-294` and
`src/core/managed_asset_lifecycle_module_v1.py:402-408` — state the ceiling is an ABI
decode bound enforced at state construction. I verified **both halves in both languages**:

- Python transfer: `src/core/asset_transfer_types_v1.py:87-90` passes
  `maximum=MAX_ASSET_BALANCE_ROWS_V1` to `_require_ordered_objects`, which raises
  `ValueError(f"{name} exceeds its {maximum}-item ceiling")`.
- Rust transfer: `zk/global_settlement_abi_v1/src/asset_transfer_types.rs:74-75` →
  `Err(AbiErrorV1::InvalidBounds("asset transfer balance rows"))`, reached from
  `asset_transfer_lane_module.rs:265` `accepted.validate()?`. The docstring's
  "`Err(InvalidBounds)` from `accepted.validate()`" is exact.
- Rust managed-lifecycle: `managed_asset_lifecycle_types.rs:119-120` →
  `Err(AbiErrorV1::InvalidBounds("managed asset balance rows"))`, reached from
  `managed_asset_lifecycle.rs:348` `accepted.validate()?`.

**Ceiling-boundary repro re-run, with a control.** Driving the real transition:

```
n=3    : RETURNED ok
n=4094 : RETURNED ok
n=4095 : RETURNED ok
n=4096 : ValueError: asset transfer balances exceeds its 4096-item ceiling
```

The boundary is exact and monotone — at ceiling-1 the same command accepts, at the
ceiling it raises. The test is therefore passing for the right reason, and the message
raised is the ceiling message, not another `ValueError` from the same constructor.

(In my first pass I read the control as a reject; that was my own probe bug — I queried a
non-existent `accepted` attribute on `AssetTransferResultV1`, whose fields are
`post_state`, `effects`, `module_journal`. Corrected above.)

**Is documented-not-totalised an honest answer?** Yes, at this authority level. The
finding was that the transition is non-total at the ceiling relative to the CBC core
shape (`transition -> Result<accept | reject>`). The repair does not fix that; it
documents it in both modules, pins the transfer boundary with a test, and records the
deferral in **both** THV1 `claim_scope` strings, not only in a docstring. With authority
NONE and `formal_core_complete=false`, disclosing and pinning a known non-totality — and
naming where it will be closed — is a legitimate response to a P3. It would not be
acceptable as a response to a promotion request.

### Observation 1 — TAKEN

`completion_scope` now reads "…and no **registered** receipt-backed producer…"
(`tools/o008_formal_cycle_admission_v1.py:275`), and nonclaim 1 carries the same
qualifier. I swept every live bare "no receipt-backed" instance:

- `global_accounting_allocation_certificate_v1.py:147` and the Rust twin at
  `global_accounting_allocation_certificate.rs:191` are **reject-message bytes**
  ("enabled lane has no receipt-backed fragment producer") — lane-scoped and correct;
  changing them would break the golden fixture for no gain.
- `render_global_accounting_allocation_certificate_v1_golden.py:10` ("The registry has
  no receipt-backed producer") and `o008_formal_cycle_admission_v1.py:408` ("producer
  registry (no receipt-backed lane)") are **grammatically registry-scoped** — the subject
  is the registry — so they already say what nonclaim 1 says.
- All other hits are archived `Earlier:` text in superseded THV1 packets.

No finding.

---

## 3. New findings

### NEW-7 (P3) — the "TOTAL parity" claim is stated without its qualifier, and one declared mutation class has a surviving member

**Where.**
- `tests/core/test_global_settlement_abi_v1_resource_bounds.py:191,193` —
  "total parity over canonical.rs" / "Every \`pub const MAX_...\` in canonical.rs must
  resolve through this single mapping"
- `tests/evidence/test_hygiene/THV1-20260901-o008-formal-cycle-admission-v23.json:5` —
  "parity over canonical.rs is TOTAL (every pub const MAX_ bound must resolve through one
  Python mapping with an equal value, failing on any unlisted name, NEW-4)"
- `tests/evidence/test_hygiene/THV1-20260901-global-settlement-v1-resource-bounds-v2.json:5`
  mutation entry — `"description": "add a Rust canonical bound with no Python twin (Opus
  P21 NEW-4)"`, `"killed_by": "…::test_every_canonical_rust_bound_has_a_python_twin"`

**What is actually enforced.** The regex at line 223 is

```python
r"pub const (MAX_[A-Z0-9_]+): (?:usize|u64|u128) = ([^;]+);"
```

which admits only bounds whose type is one of three names **and** whose `=` is followed
by a space on the declaration line. The hand-maintained *name* list became a
hand-maintained *type* list — a real and worthwhile reduction, but not totality.

**Minimal repro — surviving mutant.** Append one line to `canonical.rs` and run the
declared killer:

```bash
printf 'pub const MAX_SYNTHETIC_ROWS_V1: u32 = 77;\n' >> zk/global_settlement_abi_v1/src/canonical.rs
pytest -q tests/core/test_global_settlement_abi_v1_resource_bounds.py::test_every_canonical_rust_bound_has_a_python_twin
# => 1 passed        (expected: 1 failed)
```

This mutant is a member of the class the resource-bounds-v2 mutation table declares
killed. Confirmed escapes, run against the real in-repo test:

| Mutant | Result |
| --- | --- |
| M2 `pub const MAX_SYNTHETIC_ROWS_V1: u32 = 77;` | **1 passed** (escapes) |
| M3 `pub const MAX_SYNTHETIC_ROWS_V1: i64 = 77;` | **1 passed** (escapes) |
| M4 `pub const MAX_SYNTHETIC_ROWS_V1: u16 = 77;` | escapes (parser probe) |
| M6 `pub const MAX_SYNTHETIC_ROWS_V1: usize =\n    77;` | **1 passed** (escapes) |
| M7 `pub const MAX_SYNTHETIC_ROWS_V1: usize\n    = 77;` | escapes (parser probe) |

**Why it matters.** `resource-bounds-v2`'s own `claim_scope` states the claim
*correctly* — "(usize/u64/u128, expression-valued included)". Three of the four places
that state the claim drop the qualifier, and the one that governs mutation adequacy is
among them. Under this campaign's credibility discipline, a mutation-table row whose
stated class has a surviving member is a defect in the evidence.

**Suggested repair (not applied).** Either (a) drop the type alternation and match
`pub const (MAX_[A-Z0-9_]+)\s*:\s*[A-Za-z0-9_:]+\s*=\s*([^;]+);`, letting `evaluate`'s
existing loud failure handle any type it cannot value — which makes the claim true as
written; or (b) keep the regex and qualify the claim in all three places, and narrow the
mutation description to "add a Rust canonical `usize`/`u64`/`u128` bound with no Python
twin". (a) is strictly better: it makes the artifact match the word "TOTAL".

*Note for whoever repairs this:* an unqualified regex will also pick up commented-out
declarations (`// pub const MAX_COMMENTED_V1: usize = 5;` already fails the test today —
verified, probe M8). That is loud and fail-closed, so it is acceptable, but it should be
a conscious choice.

### NEW-8 (P3, cosmetic) — the deleted stray block left three blank lines

**Where.** `src/core/global_settlement_types_v1.py:1355-1357` — three consecutive blank
lines between the close of `OutboxStateV1.to_canonical` (`:1354`) and
`def _require_ordered_objects` (`:1358`), where PEP 8 wants two.

**Repro.**
```bash
ruff check --select E303 --preview --no-cache src/core/global_settlement_types_v1.py
# => E303 too many blank lines, 1 error, 1 fixable
ruff check src/core/global_settlement_types_v1.py   # configured gate
# => All checks passed
```

The repo's configured ruff (`pyproject.toml`, `select = ["B","E","F","I"]`) does not
catch it, because E3xx is preview-only in stable ruff. Purely cosmetic; no claim depends
on it. Worth naming only because NEW-5's claim is "byte moves only" and this is the one
byte the move left behind.

### NEW-9 (P3) — the NEW-6 boundary test's `match=` does not discriminate the ceiling reject

**Where.** `tests/core/test_global_settlement_abi_v1_resource_bounds.py:285` —
`pytest.raises(ValueError, match="asset transfer balances")`.

**Why.** `_require_ordered_objects` raises **two** different `ValueError`s under the same
`name="asset transfer balances"` (`global_settlement_types_v1.py:1367` and `:1373`):

```
"asset transfer balances exceeds its 4096-item ceiling"
"asset transfer balances must be canonically ordered and unique"
```

Both match the pattern:

```python
re.search("asset transfer balances", "asset transfer balances exceeds its 4096-item ceiling")  # True
re.search("asset transfer balances", "asset transfer balances must be canonically ordered and unique")  # True
```

Today the ceiling message is the one raised (verified above), so the test is sound *now*.
But the test cannot distinguish the two, so a future change that moved this input from
the ceiling branch to the ordering branch would leave the test green while the pinned
boundary silently moved — which is precisely what NEW-6 asked to prevent.

**Suggested repair (not applied).** `match="asset transfer balances exceeds its 4096-item ceiling"`,
or at minimum `match="exceeds its .*-item ceiling"`.

### NEW-10 (P3) — the managed-lifecycle half of the NEW-6 claim is documented but pinned by no test

**Where.** `src/core/managed_asset_lifecycle_module_v1.py:402-408` carries the same
ceiling docstring, and the module joined `resource-bounds-v2`'s `source_pins`
(sha256 `613ae04adb22bc15bde4a1641c892d7292dd6f24ad03f240e6dd424c66e297fd`) — but the
mutation table's NEW-6 row is scoped to "the transfer transition" only, and there is no
`test_..._managed_..._ceiling_raises_at_construction`.

**I verified the claim is true today**, so this is an unbound claim, not a false one:

```
n=3    : RETURNED ok, post rows=4
n=4095 : RETURNED ok, post rows=4096
n=4096 : ValueError: managed asset lifecycle balances exceeds its 4096-item ceiling
```

(using `ManagedAssetClassV1.REGISTERED_ORDINARY_TOKEN`; the other five classes reject a
generic issue/burn policy at construction via
`managed_asset_lifecycle_types_v1.py:99-101`.)

**Suggested repair (not applied).** Add the twin boundary test and a matching mutation
row, or narrow the managed-lifecycle docstring to say the boundary is asserted by
analogy with the transfer module and pinned only there.

---

## 4. Observations (not findings)

1. **Two pre-existing red tests in the tree, outside this candidate's scope.** A sweep of
   all 74 test files importing `global_settlement_types_v1` gave **1875 passed, 15
   failed**. Thirteen are `tests/formal/test_esso_global_claimant_custody_certificate_v1.py`
   failing only because my sweep did not set `PYTHONPATH`/`ZENO_ESSO_PYTHON`; the checker
   replay runs that same file with the right environment and reports **20 passed**. The
   other two are real and reproduce in isolation:

   - `tests/core/test_global_settlement_canonical_admission_v1.py:24` —
     `assert len(GLOBAL_SETTLEMENT_CANONICAL_SERIALIZER_TYPES_V1) == 92` fails with
     `104 == 92` (stale hard-coded count).
   - `tests/core/test_perps_margin_lane_coordinator_v1.py:184` —
     `test_withdraw_refines_candidate_rows_into_complete_conservation` state-root assertion.

   **Both fail identically at the parent commit `24dd5e42a`** (verified in a throwaway
   detached worktree, since removed), so C8''''' did not introduce them. Neither file nor
   its module is in the packet's `source_pins`, in any of the 28 replay commands, or in
   the hygiene critical paths, so no C8''''' claim rests on them. Flagging so the campaign
   knows the tree is not fully green.

2. `MAX_TOKEN_BYTES_V1` is declared at `global_settlement_types_v1.py:27` but absent from
   `__all__` — the only mirror-block bound so omitted. Pre-existing, not touched by this
   candidate, no claim depends on it.

3. `tests/core/test_global_settlement_abi_v1_resource_bounds.py` — which now carries both
   NEW-4 and NEW-6 killers — is **not** among the packet's 28 replay commands. It is bound
   by `resource-bounds-v2` and by the hygiene critical-path set, so it is gated; but a
   reader of the packet alone will not see the two repair tests execute. Consider adding it
   as a replay command if these boundaries are meant to be packet-visible.

4. Line 232 writes `python_twins["MAX_LANE_MODULE_RECEIPT_BYTES_V1"]` unconditionally.
   If that constant were ever *also* added to `global_settlement_types_v1`, the write would
   overwrite the `getattr` value and mask a divergence between the two Python copies. Very
   hypothetical; noted for completeness only.

---

## 5. Verdict

C8''''' closes all three P21 findings with real mechanism, not wording. The two new tests
genuinely kill their target mutants (verified end-to-end against mutated inputs, not by
reading), the constant relocation is exactly as claimed and honestly scoped, the ceiling
boundary is causally pinned with a correct control, and the full replay is EXECUTED_PASS
at 28/28 with the claim ceiling untouched. The residual is documentation accuracy: three
of the four statements of the NEW-4 claim say "TOTAL" where the enforced regex is
type-restricted, and I can produce a surviving mutant of a class the mutation table
declares killed.

**Grade: A-. 0 P1, 0 P2, 4 P3 (NEW-7, NEW-8, NEW-9, NEW-10).**

Authority granted: **NONE**. `formal_core_complete` remains **false**. The claim ceiling
did not move and must not move on the strength of this review.

---

## Appendix — sha256 of every file quoted

```
d458a8b4ff056701cea64aee1522dabcf85caf3c234dcd5dbf5a4821921fe5d5  docs/research/ZENODEX_O008_FORMAL_CYCLE_V1.json
62fa13f385c70067f04b24c2421394466e186ccf13e3af94b2769267de1274a6  docs/research/ZENODEX_O008_FORMAL_CYCLE_V1.md
8d37ed72fcf15cf7849179d4ff358f4fbbdc33905348f7ab790b2fe090e8044d  src/core/global_settlement_types_v1.py
2d0d7116faecde2090a00ca38dad91e9bbb3e7f0597045750ceeed8725bd938c  src/core/asset_transfer_module_v1.py
613ae04adb22bc15bde4a1641c892d7292dd6f24ad03f240e6dd424c66e297fd  src/core/managed_asset_lifecycle_module_v1.py
1c5e7fd918870892565068b189d784221dc085d2a65eab353031d4714aa8481f  src/core/asset_transfer_types_v1.py
d6867627e5f5d45fe8f0209f53de26e124151e5b9f74a67a75a322b3b0774172  src/core/managed_asset_lifecycle_types_v1.py
768e6d82d3e7a5807b0b4501e84488f2d5e19bd3ca488488ed0710fbb09f4201  src/core/lane_module_receipt_verification_v1.py
8fa0cc4b12db685208e409975547b0f92c55b8e855d0a7ff9c6df39ebe268016  tests/core/test_global_settlement_abi_v1_resource_bounds.py
6ae9e2bcd90c75d5bb8158e8c75dec0cb58812ea95eb8213ae2e5116592bd44f  tests/core/test_global_settlement_canonical_admission_v1.py
12d3a37e118cf9915262399d6033fd0817593d2841e649b2cf660ec7ba46ab4c  tests/core/test_perps_margin_lane_coordinator_v1.py
9de0c9328b6e6ff164bb4d0090b0b0f170b1ebbe525889351d6205dd34c76206  tests/evidence/test_hygiene/THV1-20260901-global-settlement-v1-resource-bounds-v2.json
964bdd40fdbc13e53e3dbac14d9374b95c48a0df9d5383dda58922b7f4b2ec1b  tests/evidence/test_hygiene/THV1-20260901-o008-formal-cycle-admission-v23.json
2df05aefe271bb06c66ae67749aab1652e6eb9a21f87f7b7b49c961be0183572  tests/evidence/test_hygiene/THV1-20260901-global-settlement-formal-core-semantic-restage-v5.json
1e6cf3154001b79f7d2400e5560a2818507358a06fd695f3edbb30710bf541b6  tools/o008_formal_cycle_admission_v1.py
e6a3557404f65d57e5d76f9b00324397fbe4988dfa27fa14df23836b923f7163  tools/check_global_settlement_canonical_manifest_v1.py
b1a1a9b14f4fa4e646cd850943f871241eb2fb8f671fff7870f3f01ada8c07e5  tools/render_global_accounting_allocation_certificate_v1_golden.py
6cce2178582ae4f38ff95fade6f544ae54b0d7568b7599dfa6214a56515cd46a  zk/global_settlement_abi_v1/src/canonical.rs
717fac261af10b837ad11276c37cf9513defea48909e94273f16ae6ad6ec38ae  zk/global_settlement_abi_v1/src/asset_transfer_types.rs
33620989420de792f73e0d181ff8828e9c379f0d052f6e3d9633380da69e2835  zk/global_settlement_abi_v1/src/managed_asset_lifecycle_types.rs
26ac83d8359690a352328893debbf7d64685bd3bb44982527afcfbc4e4ce57a9  zk/global_settlement_abi_v1/src/asset_transfer_lane_module.rs
e39d6c44cb9ec705e7b01f4f0ec1c161f40b165c4cd59108713eadcdcb315f16  zk/global_settlement_abi_v1/src/managed_asset_lifecycle.rs
1d4ba651bedbb7e1260975acbe78aaf534431b48ad406bd18d7510194ab7de64  zk/global_settlement_abi_v1/src/lane_module_receipt_verification.rs
232c294680d1dacdb03d8a9320b59cf14fdc780fbb7c5d364f52e224f281fa75  pyproject.toml
```

Reproducer scripts written during this review (outside the worktree):
`/tmp/c8p5_parser_probe.py`, `/tmp/c8p5_ceiling_probe.py`, `/tmp/c8p5_ceiling_probe2.py`,
`/tmp/c8p5_managed_probe.py`; mutation mirror `/tmp/c8p5-mut`; checker reports
`/tmp/c8p5-checker-norun.json`, `/tmp/c8p5-checker-replay.json`, `/tmp/c8p5-hygiene.json`.
