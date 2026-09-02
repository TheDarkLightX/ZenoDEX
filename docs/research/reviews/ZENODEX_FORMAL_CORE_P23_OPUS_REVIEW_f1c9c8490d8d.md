# Opus independent review — candidate C8'''''' (repair of P22 / receipt R19)

- Reviewer: Opus, independent. Authority granted by this review: **NONE**.
- Branch: `codex/formal-core-fable-20260901`
- Subject S23: `9a74fe1b98c27d5a9b115095b668b6783b9cbcea`
- Artifact P23: `f1c9c8490d8ddcfc8e27a46eab245eb15848e313`
- Prior receipt R19: `bdca1b640542be29c1ef3d38772e447de37b9d99` (A-; 0 P1, 0 P2, 4 P3)
- Review worktree: `/tmp/zenodex-formal-core-opus-c8p6` (detached at P23; `git status --porcelain`
  empty at every checkpoint, including the last)
- Date: 2026-09-02

## Grade: A-

**0 P1, 0 P2, 1 P3.** All four P22 findings are CLOSED, and closed with mechanism I
reproduced end-to-end rather than with wording. Every mutant I reported surviving in P22
(`u32`, `i64`, `u16`, and both newline-around-`=` forms) is now killed by the declared
killer, along with five more I had not named. The managed-lifecycle fixture is provably
an authorised issue, and I isolated the ceiling as the *cause* of the raise with a
control that flips the outcome by changing one field.

The grade is held at A- by NEW-11, and by consistency with my own P22 rule rather than by
severity: this campaign treats "a mutation-table row whose stated class has a surviving
member" as a defect in the evidence, and mutation row 6 of `resource-bounds-v3` reads
"declare a canonical bound with a different integer type **or spacing**" while three
spacing variants still escape. The residual is materially smaller than P22's — the
escaping forms cannot survive `rustfmt`, and the escaping *type* forms are spellings the
crate does not currently use for any bound — and a one-line widening that I verified is
byte-for-byte behaviour-preserving on the real `canonical.rs` closes it. That should take
the next round to A.

The claim ceiling did not move.

---

## 1. Topology, admission, and replay

`git rev-list --parents -n 1` confirms a single-parent chain with an artifact-only leaf:

```
f1c9c8490 (P23) -> 9a74fe1b9 (S23) -> bdca1b640 (R19 receipt) -> b6b0652af
```

P23 changes exactly the two packet files (47 insertions / 47 deletions):
`docs/research/ZENODEX_O008_FORMAL_CYCLE_V1.{json,md}`. S23 touches 10 files
(1883 insertions / 11 deletions): one source file (a single deleted blank line), one test
file, four new THV1 packets, and four pin refreshes. I reviewed all ten.

### Checker, non-replay mode

```
$PY tools/check_o008_formal_cycle_v1.py --root /tmp/zenodex-formal-core-opus-c8p6 \
    --packet-commit f1c9c8490d8ddcfc8e27a46eab245eb15848e313
```

exit 0 — `ok: true`, `packet_admitted: true`, `errors: []`, `current_source_drift: []`,
`current_applicable: true`, `proof_replay.status: NOT_RUN`. stderr empty. The author record
correctly did not self-upgrade the replay status.

### Checker, replay mode — EXECUTED_PASS, 28/28

```
$PY tools/check_o008_formal_cycle_v1.py --root /tmp/zenodex-formal-core-opus-c8p6 \
    --packet-commit f1c9c8490d8ddcfc8e27a46eab245eb15848e313 --replay \
    --python "$PY" --esso-python /home/trevormoc/Downloads/ESSO/.venv/bin/python \
    --esso-pythonpath /home/trevormoc/Downloads/ESSO
```

exit 0, stderr empty, `proof_replay.status: EXECUTED_PASS`, 28 runs, **0 non-zero exits**.
Every observed value is identical to my P22 replay:

| command_id | observed | command_id | observed |
| --- | --- | --- | --- |
| lean_version | 4.27.0 | prior_restage_gate | 136 passed |
| lean_direct_check | empty stdout | python_version | 3.12.3 |
| lean_axioms_probe | 25 theorems | python_projection_gate | 13 passed |
| lean_binding_gate | 6 passed | rust_projection_gate | 7 passed |
| lean_certificate_direct_check | empty stdout | rust_version | cargo 1.87.0 |
| lean_certificate_axioms_probe | 16 theorems | rust_compiler_version | rustc 1.87.0 |
| lean_certificate_binding_gate | 6 passed | rust_refinement_gate | 41 passed |
| esso_validate | ir_hash ok | python_golden_gate | 35 passed |
| esso_verify_multi | z3+cvc5 agreed | rust_golden_gate | 3 passed |
| esso_gate | 20 passed | rust_bounded_vec_unit_gate | 1 passed |
| esso_certificate_validate | ir_hash ok | python_certificate_golden_gate | 37 passed |
| esso_certificate_verify_multi | z3+cvc5 agreed | rust_certificate_golden_gate | 3 passed |
| esso_certificate_gate | 24 passed | rust_certificate_unit_gate | 4 passed |
| | | python_producer_gate | 30 passed |
| | | rust_producer_gate | 7 passed |

The two Lean gates and the cargo gates were executed by the checker strictly serially. No
concurrent Lean invocation occurred at any point in this review; I ran nothing else while
the replay was in flight.

### Claim ceiling — unchanged, and byte-identical in both checker modes

```
formal_core_complete        false
formal_cycle_status         FORMAL_CYCLE_COMPLETE_O008_OPEN
o008_status                 OPEN_EXACT_ALL_12_RECONCILIATION_MISSING
supported_claim             O008_RELATION_NECESSARY_CHECKS_AND_INFORMATION_LOSS_PROVED
migration/production/publication/release/settlement/value_movement/verifier  NONE
value_movement_gates_closed 0 of 12
whole_value_movement_safe   false
```

Verified equal between the non-replay and replay reports by direct dict comparison, and
equal to the P22 ceiling. Nothing raised it.

### Independent batteries

| Battery | Command | Result |
| --- | --- | --- |
| Full cargo | `cargo test --offline --locked` in `zk/global_settlement_abi_v1` | **53 suites, 523 passed, 0 failed, 0 ignored** |
| cargo build | `cargo build --offline --locked` | **0 warnings** |
| Repair test file | `pytest tests/core/test_global_settlement_abi_v1_resource_bounds.py` | **19 passed** (was 18; +1 for NEW-10) |
| Module suites | transfer module + transfer lane module + managed lifecycle + lane coordinator + projection gate + checker gate + repair file | **475 passed** |
| Closure digest | `tools/check_global_settlement_canonical_manifest_v1.py` | **PASS** (re-pin `6335a2b4…` correct) |
| Test hygiene | `tools/check_test_hygiene_v1.py --base-ref bdca1b640 --json` | **ok: true**, 12 changed paths, 5 critical paths, 576 node ids |
| ruff (configured) | `ruff check src/core/global_settlement_types_v1.py` | **All checks passed** |
| ruff E303 preview | `ruff check --select E303 --preview --no-cache …` | **All checks passed** (was 1 error) |

The hygiene checker selects exactly the four expected packets —
`claimant-backing-guard-golden-v17`, `semantic-restage-v6`, `resource-bounds-v3`,
`o008-formal-cycle-admission-v24` — and `tests/core/test_global_settlement_abi_v1_resource_bounds.py`
is one of the five covered critical paths, so the repair test is gated.

### Pin integrity

I recomputed every pin in all four THV1 packets against the tree at P23:

```
resource-bounds-v3        8/8 source pins match
semantic-restage-v6      12/12 source pins match
admission-v24            36/36 source pins match
backing-guard-golden-v17  9/9 source pins match
                         12/12 test pins match (all 6 resource-bounds node ids exist)
TOTAL PIN MISMATCHES: 0
```

The one-byte change to `global_settlement_types_v1.py`
(`8d37ed72…` → `854a65b6…`) is propagated consistently to all four places that pin it:
the blueprint pin row (`ZENODEX_GLOBAL_FUNCTIONAL_CORE_FORMAL_BLUEPRINT_V1.md:103`), the
ESSO restage gate (`tests/formal/test_esso_global_settlement_core_v1.py:124`), the Lean
custody gate (`tests/formal/test_lean_global_claimant_custody_relation_v1.py:45`), and the
packet's `source_pins`. The evidence history is append-only: `restage-v1..v6`,
`resource-bounds-v2..v3`, `admission-v2, v20..v24` all still present; `removed_paths` empty.

---

## 2. Closure table

| P22 finding | Verdict | Evidence |
| --- | --- | --- |
| NEW-7 — "TOTAL parity" over-claimed; declared mutation class had a surviving member | **CLOSED** (residual → NEW-11) | All 5 named mutants now killed, plus 5 more; see §2.1 |
| NEW-8 — stray blank lines from the deleted block | **CLOSED** | `global_settlement_types_v1.py:1355-1356` is exactly two blank lines; `ruff --select E303 --preview` clean |
| NEW-9 — boundary `match=` could not discriminate the ceiling reject | **CLOSED** | `test_…resource_bounds.py:283` pins the exact message; verified it rejects the ordering message |
| NEW-10 — managed-lifecycle ceiling claim unbound | **CLOSED** | New test at `:288-353`; fixture proved authorised and the ceiling proved causal; see §2.4 |
| Note 1 — pre-existing red tests | **Confirmed out of scope** | See §3.1 |
| Note 2 — repair file outside the 28 replay commands | **Stays an observation** | Nonclaim 10 discloses it; see §3.2 |

### 2.1 NEW-7 — CLOSED

`tests/core/test_global_settlement_abi_v1_resource_bounds.py:224`
(sha256 `3c9841f820ec37d12d7d3311135a9211f7b784af000741553f6ff7a472d229dd`):

```python
r"pub const (MAX_[A-Z0-9_]+)\s*:\s*[a-z0-9]+\s*=\s*([^;]+);",
rust_source,
re.S,
```

The integer-type alternation is gone and `re.S` is set, so the character class covers every
Rust integer primitive (`i8`…`i128`, `u8`…`u128`, `isize`, `usize`) and the whitespace is
free around both `:` and `=`.

**Mutation battery, run against the real in-repo test.** I used a mirror root
(`/tmp/c8p6-mut`) whose `src` is a symlink into the worktree so that
`Path(__file__).resolve().parents[2]` resolves to the mutated tree; the worktree itself was
never modified (confirmed clean afterwards). Harness: `/tmp/c8p6_mutants.sh`.

| Mutant | P22 result | P23 result |
| --- | --- | --- |
| M0 baseline | 1 passed | **1 passed** |
| `…: u32 = 77;` | 1 passed (escaped) | **1 failed** ✓ killed |
| `…: i64 = 77;` | 1 passed (escaped) | **1 failed** ✓ killed |
| `…: u16 = 77;` | escaped | **1 failed** ✓ killed |
| `…: usize =\n    77;` | 1 passed (escaped) | **1 failed** ✓ killed |
| `…: usize\n    = 77;` | escaped | **1 failed** ✓ killed |
| `…: u8 = 77;` | not tested | **1 failed** ✓ killed |
| `…: isize = 77;` | not tested | **1 failed** ✓ killed |
| `…: i128 = 77;` | not tested | **1 failed** ✓ killed |
| `MAX_X\n    : usize = 77;` | not tested | **1 failed** ✓ killed |
| `MAX_X  :  usize  =  77;` | not tested | **1 failed** ✓ killed |
| C1 value drift `4_096` → `8_192` | killed | **1 failed** ✓ still killed |
| C2 delete `MAX_ASSET_CUSTODY_ROWS_V1` | killed | **1 failed** ✓ still killed |

Every mutant the lead asked me to re-run is caught by the declared killer. The `>= 24`
floor at `:240` remains tight: `canonical.rs:6-29` declares exactly 24 `MAX_` bounds.

The docstring at `:191-196` now reads "total parity … Every `pub const MAX_...`
declaration in canonical.rs, **whatever its integer type or spacing**, must resolve
through this single mapping" — which is true for every integer primitive and for all
spacing around `:` and `=`. The residual is NEW-11.

### 2.2 NEW-8 — CLOSED

`src/core/global_settlement_types_v1.py`
(sha256 `854a65b68a0c76a3af3afc62b53eb48c333b9e87f854e8f10fd54a851ff27ac4`), lines
1354-1357 under `cat -A`:

```
1354	        }$
1355	$
1356	$
1357	def _require_ordered_objects($
```

Exactly the module's two-line convention.

```bash
ruff check --select E303 --preview --no-cache src/core/global_settlement_types_v1.py
# P22: E303 too many blank lines, 1 error, 1 fixable
# P23: All checks passed!
```

The diff is exactly one deleted blank line, and `semantic-restage-v6`'s `claim_scope`
scopes it honestly: "the residual blank lines from the stray-block deletion collapse to
the module's two-line convention (Opus P22 NEW-8); whitespace only, no value or statement
changed." I re-verified the rest of the NEW-5 surface survived intact: by AST parse,
`__all__` still contains 69 entries with no duplicates, all resolvable, and the
`MAX_`/`MIN_` subsequence is in declaration order, with the three new constants at
declaration positions 6/7/8 matching `canonical.rs:11-13`.

### 2.3 NEW-9 — CLOSED

`tests/core/test_global_settlement_abi_v1_resource_bounds.py:281-284`:

```python
with pytest.raises(
    ValueError,
    match=rf"asset transfer balances exceeds its {MAX_ASSET_BALANCE_ROWS_V1}-item ceiling",
):
```

`_require_ordered_objects` raises two `ValueError`s under the same `name`
(`global_settlement_types_v1.py:1367` ceiling, `:1372` ordering). The new pattern
discriminates them:

```
ceiling  msg: new pattern matches=True   (old pattern matched=True)
ordering msg: new pattern matches=False  (old pattern matched=True)
```

Also good: the pattern interpolates `MAX_ASSET_BALANCE_ROWS_V1` rather than hard-coding
`4096`, so it tracks the constant instead of drifting from it.

### 2.4 NEW-10 — CLOSED, and the fixture is genuinely authorised

The new test is `tests/core/test_global_settlement_abi_v1_resource_bounds.py:288-353`.
The lead asked me to judge whether its fixture is a real authorised issue rather than an
earlier reject. It is, and I established it three independent ways.

**(a) Structurally.** `transition_managed_asset_lifecycle_v1`
(`src/core/managed_asset_lifecycle_module_v1.py:397-423`) runs `_authorize` first and
*returns* `_reject(...)` for every authorisation failure — it never raises. The observed
`ValueError` therefore can only originate after `_authorize`, `_post_supply` and
`_post_balances` all succeeded, from the post-state constructor in `_accept`. The message
`"managed asset lifecycle balances exceeds its 4096-item ceiling"` is produced at exactly
one place: `ManagedAssetLifecycleStateV1.__post_init__`
(`managed_asset_lifecycle_types_v1.py:130-136`) delegating to `_require_ordered_objects`.

**(b) Field alignment.** Every gate in `_authorize`
(`managed_asset_lifecycle_module_v1.py:78-115`) is satisfied by the fixture:
`context.module_release_id == pre_state.module_release_id` (`root(3)`); command kind is
`MANAGED_ASSET_ISSUE_COMMAND_KIND_V1`; the `"USD"` policy exists, is `enabled=True`, and
is `REGISTERED_ORDINARY_TOKEN`; `issue_policy_root` is set; `context.subject_id ==
policy.issue_authority_subject` (`"issuer"`); `context.grant_root == policy.issue_policy_root`
(`root(5)`); `amount_atoms=1` is non-zero and under `MAX_DELTA_ATOMS_V1`.

**(c) Empirically, with live controls.** `/tmp/c8p6_managed_probe.py` drives the real
transition. Monotone boundary, fixture unchanged except the row count:

```
n=3      : ACCEPTED post_rows=4     post_supply=4
n=4094   : ACCEPTED post_rows=4095  post_supply=4095
n=4095   : ACCEPTED post_rows=4096  post_supply=4096
n=4096   : RAISED ValueError: managed asset lifecycle balances exceeds its 4096-item ceiling
```

At the ceiling, perturbing exactly one authorisation field turns the raise into a typed
reject — proving each check is live and that the fixture passes it rather than short-circuiting:

```
n=4096 wrong subject    : REJECTED code=UNAUTHORIZED_SUBJECT
n=4096 wrong grant root : REJECTED code=AUTHORITY_PROFILE_MISMATCH
n=4096 disabled policy  : REJECTED code=DISABLED_ASSET
n=4096 unknown kind     : REJECTED code=UNKNOWN_COMMAND
```

And the decisive causal isolation — same state, same authority, same amount, only the
target owner differs:

```
n=4096 existing owner (acct-000000) : ACCEPTED post_rows=4096 post_supply=4097
n=4096 new owner (brand-new-owner)  : RAISED ValueError: … exceeds its 4096-item ceiling
```

Issuing to an existing owner adds no row and accepts; issuing to a new owner adds the
4097th row and raises. The ceiling is the cause, not a coincidence of the ceiling-sized
state.

**The accept side is pinned too, implicitly and correctly.** Neither boundary test asserts
"ceiling-1 accepts" inline, but both construct a pre-state at *exactly* the ceiling
**outside** the `pytest.raises` block. Any mutation that tightened the bound (e.g.
`maximum=MAX_ASSET_BALANCE_ROWS_V1 - 1` at `managed_asset_lifecycle_types_v1.py:135` or
`asset_transfer_types_v1.py:90`) would raise during fixture construction and error the
test. So the fixture is itself the accept-side control. Worth stating because it is not
obvious from reading the test.

**Cross-language half.** The docstring's "Rust returns Err(InvalidBounds) for the same
input" is bound, not merely asserted: `zk/global_settlement_abi_v1/src/managed_asset_lifecycle.rs:348`
and `asset_transfer_lane_module.rs:265` both call `accepted.validate()?`, and
`zk/global_settlement_abi_v1/tests/managed_asset_lifecycle.rs:378-401` /
`tests/asset_transfer.rs:388-411` pin the two-sided boundary on `validate()` (`is_ok()` at
the ceiling, `InvalidBounds("managed asset balance rows")` / `("asset transfer balance rows")`
above it). The Rust binding is at `validate()` level rather than end-to-end through the
transition, but the transition's only path to acceptance goes through that call, so the
composition holds.

---

## 3. The two P22 "worth knowing" notes

### 3.1 Pre-existing red tests — confirmed out of scope, no C8'''''' claim rests on them

Both still fail at P23, with the identical assertion as at P22:

```
tests/core/test_global_settlement_canonical_admission_v1.py::test_canonical_admission_manifest_is_frozen_sorted_and_disjoint
    assert len(GLOBAL_SETTLEMENT_CANONICAL_SERIALIZER_TYPES_V1) == 92
    AssertionError: assert 104 == 92        <- same 104 as at P22, unmoved
tests/core/test_perps_margin_lane_coordinator_v1.py::test_withdraw_refines_candidate_rows_into_complete_conservation
    :184 AssertionError                     <- same
```

I checked this properly rather than by assertion. Neither file, nor
`src/core/perps_margin_lane_coordinator_v1.py`, is referenced by *any* of the five
C8'''''' evidence artifacts (the packet JSON and the four THV1 packets); neither appears
in the 28 replay commands; and the hygiene checker's `covered_critical_paths` is exactly
five paths, none of them these. S23's 10-file diff touches neither. **No C8'''''' claim
newly rests on them.** They remain a pre-existing red spot in the tree, correctly outside
this candidate.

One thing I did check specifically: S23 modified
`tools/check_global_settlement_canonical_manifest_v1.py` (the closure-digest re-pin), and
the canonical-admission red test asserts a serializer *count*. The count is still 104,
unchanged from P22, so the re-pin did not perturb it.

### 3.2 The repair test outside the 28 replay commands — stays an observation, not a finding

I re-examined this with the question the lead posed. It stays an observation, and the
reason is explicit rather than charitable: **nonclaim 10** of the packet
(`ZENODEX_O008_FORMAL_CYCLE_V1.json`) reads

> "Selected test-hygiene packets are bound by pin only; their evidence families and
> mutation tables are validated by `tools/check_test_hygiene_v1.py`, which this checker
> does not run."

That is precisely the gap, disclosed in the packet's own voice. The parity and ceiling
claims live in `resource-bounds-v3`'s `claim_scope` and mutation table, not in the O-008
packet's `completion_scope` (13 items, none of which is the resource-bounds claim). A
reader who replays the packet gets exactly what the packet claims; a reader who wants the
mutation table validated is told which tool to run. The test is bound by pin
(`3c9841f8…`, all 6 node ids), by `resource-bounds-v3`'s mutation rows, and by the hygiene
checker's critical-path set, which I ran green.

I would still add it as a replay command if the campaign wants the boundaries
packet-visible, but with nonclaim 10 present that is a preference, not a defect.

---

## 4. New findings

### NEW-11 (P3) — mutation row 6 says "or spacing", and three spacing forms still escape; "TOTAL" still admits two type spellings

**Where.**
- `tests/core/test_global_settlement_abi_v1_resource_bounds.py:224` — the regex keeps
  `pub const ` as a fixed literal (single space between `const` and the name, single space
  between `pub` and `const`) and restricts the type to `[a-z0-9]+` (no `_`, no uppercase,
  no `::`).
- `tests/evidence/test_hygiene/THV1-20260901-global-settlement-v1-resource-bounds-v3.json`,
  `mutations[6]`: `"description": "declare a canonical bound with a different integer type
  **or spacing** (Opus P22 NEW-7)"`.
- `tests/evidence/test_hygiene/THV1-20260901-o008-formal-cycle-admission-v24.json`,
  `claim_scope`: "parity over canonical.rs is **TOTAL** (every pub const MAX_ bound must
  resolve through one Python mapping with an equal value, failing on any unlisted name,
  NEW-4)" — still unqualified.

**Minimal repro — five surviving mutants, run against the real in-repo test.**

```bash
# in a mirror root whose src/ symlinks the worktree (see §2.1)
printf 'pub const  MAX_SYNTHETIC_ROWS_V1: usize = 77;\n' >> zk/global_settlement_abi_v1/src/canonical.rs
pytest -q tests/core/test_global_settlement_abi_v1_resource_bounds.py::test_every_canonical_rust_bound_has_a_python_twin
# => 1 passed   (expected: 1 failed)
```

| Surviving mutant | Class named by row 6 | rustfmt-stable? |
| --- | --- | --- |
| `pub const  MAX_X: usize = 77;` (two spaces `const`→name) | spacing | no |
| `pub  const MAX_X: usize = 77;` (two spaces `pub`→`const`) | spacing | no |
| `pub const\n    MAX_X: usize = 77;` | spacing | no |
| `pub const MAX_X: RowCountV1 = 77;` (type alias) | "every pub const MAX_ bound" | **yes** |
| `pub const MAX_X: core::primitive::usize = 77;` | "every pub const MAX_ bound" | **yes** |

**Why it matters, stated at its real weight.** The three spacing escapes cannot survive
`cargo fmt`, so in practice they need a hand-written non-canonical declaration. The two
type escapes *are* rustfmt-stable, and the type-alias form is not hypothetical in this
crate: `canonical.rs:63` already declares `pub type AbiResultV1<T> = Result<T, AbiErrorV1>;`
and the crate has a second `pub type` at
`global_economic_state_effect_refinement.rs:189`. A future `pub type RowCountV1 = usize;`
next to the bounds is an ordinary refactor, and a `MAX_` bound declared with it — with no
Python twin — would pass the test that the packet says makes parity total.

This is a defect in the evidence, not in the runtime: no shipped bound uses any of these
spellings today, and I verified the current 24 bounds are enumerated correctly.

**Suggested repair (not applied), verified zero-diff.** Widen the literal and the type class:

```python
r"pub\s+const\s+(MAX_[A-Z0-9_]+)\s*:\s*[A-Za-z0-9_:]+\s*=\s*([^;]+);"
```

On the real `canonical.rs` this is behaviour-preserving — I checked both regexes against
the file and they return the identical 24 name/expression pairs — and it kills all five
survivors above plus `NonZeroUsize`. Any type it cannot value still fails loudly through
`evaluate`'s existing `int()` raise, which is fail-closed. Alternatively, narrow the two
claim strings to what the regex enforces; but the widening is strictly better, because it
makes the artifact match the word "TOTAL" instead of retreating from it.

---

## 5. Observations (not findings)

1. `resource-bounds-v3`'s `boundary_dimensions` still lists the same three dimensions as
   v2 (`effect_plan_collection_cardinality`, `global_state_collection_cardinality`,
   `cross_language_limit_parity`). The two new transition-ceiling boundaries are carried
   by `mutations[5]` and `mutations[7]` rather than by a boundary dimension of their own.
   Nothing is over-claimed; a fourth dimension would just make the evidence easier to read.

2. `THV1-20260901-claimant-backing-guard-golden-v17.json` contains the line
   `"Earlier: v14 re-pin (C8''')…"` twice. I checked v16: the duplication is already
   there, so it was inherited, not introduced here. Cosmetic.

3. `MAX_TOKEN_BYTES_V1` (`global_settlement_types_v1.py:27`) is still the one mirror-block
   bound absent from `__all__`. Pre-existing, untouched, no claim depends on it — repeated
   from P22 only so it is not lost.

4. The machine's root filesystem hit 100% during this review (110 MB free), which broke a
   throwaway `git worktree add`. I freed my own `CARGO_TARGET_DIR`
   (`/tmp/zenodex-opus-c8p6-cargo`, 1.8 GB) after the cargo battery completed, restoring
   ~1.9 GB. Five sibling review cargo target dirs of ~1.8 GB each remain and belong to
   other agents; I did not touch them. Flagging because a full disk will eventually make a
   replay fail in a way that looks like an evidence failure.

---

## 6. Verdict

C8'''''' is a clean repair round. Each of the four P22 findings was closed by changing
mechanism, and I verified each by reproduction rather than by reading: ten mutants killed
where five previously escaped, the E303 check flipped from error to clean, the ceiling
message pinned exactly and shown to reject its sibling, and the managed-lifecycle
boundary bound by a test whose fixture I proved authorised with four reject controls and
one accept control that isolates the ceiling as the cause. Full replay is EXECUTED_PASS at
28/28 with every observed value identical to the previous round, cargo is 523/0 with zero
warnings, all 65 source pins and 12 test pins verify, and the claim ceiling is untouched.

The single residual is a word: `resource-bounds-v3`'s mutation row 6 claims a "spacing"
class that still has surviving members, and `admission-v24` still says "TOTAL / every pub
const MAX_ bound" while two rustfmt-stable type spellings escape. By this campaign's own
credibility rule that is an evidence defect, and applying it consistently with P22 is why
the grade does not move to A. It is a one-line, verified-behaviour-preserving fix away.

**Grade: A-. 0 P1, 0 P2, 1 P3 (NEW-11).**

Authority granted: **NONE**. `formal_core_complete` remains **false**. The claim ceiling
did not move and must not move on the strength of this review.

---

## Appendix — sha256 of every file quoted

```
92d0bb689befb0e8f06de43e49317853dcd1f32cf3ecb020d861282cd47c9e19  docs/research/ZENODEX_O008_FORMAL_CYCLE_V1.json
ec931a290dc6fbb335668d97113f720414e2b5a9bfa0c40bae3653b6267e4709  docs/research/ZENODEX_O008_FORMAL_CYCLE_V1.md
e5da0022e1558b6cc2c65d492a49554b3fda8357ab9f126e30fa1cea665f46eb  docs/research/ZENODEX_GLOBAL_FUNCTIONAL_CORE_FORMAL_BLUEPRINT_V1.md
854a65b68a0c76a3af3afc62b53eb48c333b9e87f854e8f10fd54a851ff27ac4  src/core/global_settlement_types_v1.py
2d0d7116faecde2090a00ca38dad91e9bbb3e7f0597045750ceeed8725bd938c  src/core/asset_transfer_module_v1.py
1c5e7fd918870892565068b189d784221dc085d2a65eab353031d4714aa8481f  src/core/asset_transfer_types_v1.py
613ae04adb22bc15bde4a1641c892d7292dd6f24ad03f240e6dd424c66e297fd  src/core/managed_asset_lifecycle_module_v1.py
d6867627e5f5d45fe8f0209f53de26e124151e5b9f74a67a75a322b3b0774172  src/core/managed_asset_lifecycle_types_v1.py
768e6d82d3e7a5807b0b4501e84488f2d5e19bd3ca488488ed0710fbb09f4201  src/core/lane_module_receipt_verification_v1.py
3c9841f820ec37d12d7d3311135a9211f7b784af000741553f6ff7a472d229dd  tests/core/test_global_settlement_abi_v1_resource_bounds.py
6ae9e2bcd90c75d5bb8158e8c75dec0cb58812ea95eb8213ae2e5116592bd44f  tests/core/test_global_settlement_canonical_admission_v1.py
12d3a37e118cf9915262399d6033fd0817593d2841e649b2cf660ec7ba46ab4c  tests/core/test_perps_margin_lane_coordinator_v1.py
f98b3dd2b041d848f7e5fa64d629c78437dae47da135dfa0a419891a18cebd35  tests/formal/test_esso_global_settlement_core_v1.py
d6e4a272f4a77786e7c9ba1a4b462cd5d550cd926dc000829f8255ff32d67d9b  tests/formal/test_lean_global_claimant_custody_relation_v1.py
372a8444a833e466fbd7cfa850ac664e15d5ac2f83089619dbae8f6b5cac8835  tests/evidence/test_hygiene/THV1-20260901-global-settlement-v1-resource-bounds-v3.json
474ec652969657453bd68615b3e3eba71f009577a23b9397680a9e52febc5b89  tests/evidence/test_hygiene/THV1-20260901-o008-formal-cycle-admission-v24.json
62d94549f33080e5003b0e6f0e9b94743b242d2942c652e11d75557a28d60803  tests/evidence/test_hygiene/THV1-20260901-global-settlement-formal-core-semantic-restage-v6.json
8f0be831619f036b0b6aaf5aa4e6dfff1edfffd4325a832c44d423886b3f4981  tests/evidence/test_hygiene/THV1-20260901-claimant-backing-guard-golden-v17.json
9fe18c2d44864572e85d3f56ee17b5c7d827664bdd424367c42f5822405188df  tools/check_global_settlement_canonical_manifest_v1.py
3b958699f5d96591cf174e910fd6f8000be73a879f6cc369da333bfdac1a55cd  tools/check_test_hygiene_v1.py
6cce2178582ae4f38ff95fade6f544ae54b0d7568b7599dfa6214a56515cd46a  zk/global_settlement_abi_v1/src/canonical.rs
717fac261af10b837ad11276c37cf9513defea48909e94273f16ae6ad6ec38ae  zk/global_settlement_abi_v1/src/asset_transfer_types.rs
33620989420de792f73e0d181ff8828e9c379f0d052f6e3d9633380da69e2835  zk/global_settlement_abi_v1/src/managed_asset_lifecycle_types.rs
26ac83d8359690a352328893debbf7d64685bd3bb44982527afcfbc4e4ce57a9  zk/global_settlement_abi_v1/src/asset_transfer_lane_module.rs
e39d6c44cb9ec705e7b01f4f0ec1c161f40b165c4cd59108713eadcdcb315f16  zk/global_settlement_abi_v1/src/managed_asset_lifecycle.rs
742fb42a5250a55555050964edbfa595c1ca6139cf9fc79b83b83a27a27a4e8c  zk/global_settlement_abi_v1/tests/managed_asset_lifecycle.rs
e1817600d61b350faa98d39c16f6cc67b243a5d2cc079d2d4c2bcc0599c35c70  zk/global_settlement_abi_v1/tests/asset_transfer.rs
232c294680d1dacdb03d8a9320b59cf14fdc780fbb7c5d364f52e224f281fa75  pyproject.toml
```

Artifacts written during this review (all outside both worktrees):
`/tmp/c8p6-checker-norun.json`, `/tmp/c8p6-checker-replay.json`, `/tmp/c8p6-hygiene.json`,
`/tmp/c8p6-cargo.log`, `/tmp/c8p6_mutants.sh` (mutation harness),
`/tmp/c8p6_managed_probe.py` (boundary + authorisation controls), mutation mirror
`/tmp/c8p6-mut`.
