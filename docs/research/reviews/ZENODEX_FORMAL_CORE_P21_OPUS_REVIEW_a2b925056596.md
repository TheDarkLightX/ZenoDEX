# Opus independent review — candidate C8'''' (P21)

- Subject `S21` = `1acf20873e543335657a504609c166d882753dbe`
- Artifact child `P21` = `a2b925056596a2e4aa33efbbdccebcee0821cf44`
- Parent receipt `R17` = `c907b3007ccc911128fbbf74c0580873e61c6eb0` (P20 review, grade B+)
- Branch `codex/formal-core-fable-20260901`
- Review worktree `/tmp/zenodex-formal-core-opus-c8pppp` (detached at P21, clean before and after)
- Authority granted by this review: **NONE**. The claim ceiling did not move.

---

## Grade: A-

Every P20 finding is **CLOSED**, each with evidence I reproduced independently rather than
read off the diff. The full battery replays green. The claim ceiling is byte-identical to R17.
Three new P3 findings, all bounded, none a regression, none touching authority — two of them
are properties of the repair's own construction rather than pre-existing conditions, which is
what holds this back from A.

- P1: 0
- P2: 0
- P3: 3 (NEW-4, NEW-5, NEW-6)

The NEW-3 repair is better than the repair I asked for: the inequality is pinned in *both*
languages transitively inside a single test function, and the docstring now states honestly
what the test does and does not establish. The NEW-2 repair went past the seven named sites and
introduced shared constants instead of duplicating literals, which is the correct structural
fix; I confirmed by exhaustive sweep that the whole ABI V1 bound family is now closed.

---

## 1. Envelope — PASS

### Artifact-only child

```
$ git diff --stat 1acf20873 a2b925056
 docs/research/ZENODEX_O008_FORMAL_CYCLE_V1.json |   2 +-
 docs/research/ZENODEX_O008_FORMAL_CYCLE_V1.md   | 102 ++++++++++++------------
 2 files changed, 52 insertions(+), 52 deletions(-)
```

P21 touches only the two packet files. Confirmed.

### Checker, both modes

```
$ "$PY" tools/check_o008_formal_cycle_v1.py --root /tmp/zenodex-formal-core-opus-c8pppp \
    --packet-commit a2b925056596a2e4aa33efbbdccebcee0821cf44
exit=0  ok=True  packet_admitted=True  proof_replay.status=NOT_RUN
        errors=[]  current_source_drift=[]  stderr: empty

$ ... --replay --python "$PY" --esso-python "$PY" \
      --esso-pythonpath /tmp/zenodex-formal-core-opus-c8pppp/external/ESSO
exit=0  ok=True  packet_admitted=True  proof_replay.status=EXECUTED_PASS  runs=28
        errors=[]  current_source_drift=[]  stderr: empty
```

All 28 recorded tools executed with exit 0. The counts the lead named both hold:

| command_id | comparable | expected |
|---|---|---|
| `python_producer_gate` | `passed: 30` | 30 (was 29) ✓ |
| `prior_restage_gate` | `passed: 136` | 136 ✓ |

Other replay comparables: `lean_version 4.27.0`; `lean_axioms_probe theorems_probed 25`;
`lean_certificate_axioms_probe theorems_probed 16`; `lean_binding_gate passed 6`;
`lean_certificate_binding_gate passed 6`; `esso_verify_multi verdict VERIFIED`
(z3 4.15.4, cvc5 1.1.2, ir_hash `sha256:918526261e71b37c…`);
`esso_certificate_verify_multi VERIFIED` (ir_hash `sha256:01a34e8dcd5bef3c…`);
`esso_gate passed 20`; `esso_certificate_gate passed 24`; `python_version 3.12.3`;
`python_projection_gate passed 13`; `rust_projection_gate passed 7`;
`rust_version cargo 1.87.0`; `rustc 1.87.0 / 17067e9ac6d7ecb70e50f92c1944e545188d2359`;
`rust_refinement_gate passed 41`; `python_golden_gate passed 35`; `rust_golden_gate passed 3`;
`rust_bounded_vec_unit_gate passed 1`; `python_certificate_golden_gate passed 37`;
`rust_certificate_golden_gate passed 3`; `rust_certificate_unit_gate passed 4`;
`rust_producer_gate passed 7`.

The worktree was clean after the replay (`git status --porcelain` empty), so the checker's
worktree-mutation guard had nothing to trip on. Note the checker overrides `CARGO_TARGET_DIR`
to a per-run temp dir (`tools/o008_formal_cycle_shell_v1.py:389-391`), so the replay's cargo
build is hermetic and my exported target dir is correctly ignored.

### Independent battery, run strictly serially

| battery | result |
|---|---|
| `cargo test --offline` in `zk/global_settlement_abi_v1` | 53 suites, **523 passed, 0 failed** |
| 7 Python suites (producers, certificate golden, backing guard, admission gate, projection runtime gate, ESSO restage gate, resource bounds) | **656 passed** in 286.6s |
| `tests/formal/test_lean_global_claimant_custody_relation_v1.py` | **6 passed** |
| `tests/formal/test_lean_global_accounting_allocation_certificate_v1.py` | **6 passed** |

No concurrency between cargo, pytest and the two Lean gates.

### Claim ceiling did not move

```
claim_ceiling identical R17 vs P21: True
completion_scope identical:         True
nonclaims: 11 -> 11, only nonclaims[1] changed
changed top-level keys: hygiene_selection, nonclaims, packet_commit_parent,
                        proof_replay, source_pins, subject_commit, subject_parent, subject_tree
```

`formal_core_complete=False`, every authority field `NONE`,
`value_movement_gates_closed 0 / 12`, `o008_status OPEN_EXACT_ALL_12_RECONCILIATION_MISSING`,
`supported_claim O008_RELATION_NECESSARY_CHECKS_AND_INFORMATION_LOSS_PROVED`.

### Pin integrity

Every re-pinned hash equals the file on disk:

| path | pinned in | sha256 |
|---|---|---|
| `src/core/global_settlement_types_v1.py` | blueprint pin row, `ENFORCED_PINS`, custody Lean gate `PYTHON_TYPES`, packet | `2150c794…` ✓ |
| `src/core/global_accounting_allocation_certificate_v1.py` | certificate Lean gate `PYTHON_CHECKER`, packet, THV1 cert-v12 | `de37103e…` ✓ |
| `tools/o008_formal_cycle_admission_v1.py` | packet, THV1 admission-v22 | `2031804a…` ✓ |
| `tests/core/test_global_accounting_lane_producers_v1.py` | packet | `706dc9ee…` ✓ |
| `tests/formal/test_esso_global_settlement_core_v1.py` | packet | `31b5b026…` ✓ |
| `docs/research/ZENODEX_GLOBAL_FUNCTIONAL_CORE_FORMAL_BLUEPRINT_V1.md` | packet | `48441f1f…` ✓ |

### Semantic-restage lineage (the lead's extra item) — VERIFIED MECHANICALLY

The blueprint pin row, `THV1_PACKET`/`THV1_EVIDENCE_ID` and `ENFORCED_PINS` all move v3 → v4
together (`tests/formal/test_esso_global_settlement_core_v1.py:95-99,121-124`;
`docs/research/ZENODEX_GLOBAL_FUNCTIONAL_CORE_FORMAL_BLUEPRINT_V1.md:29,103`).

The v4 packet's `claim_scope` asserts the change is *"additive `Final` constants only, no
modeled function, inequality, message, or precedence changed."* I did not take that on trust —
I reconstructed R17 from S21:

```
R17 sha256: 13871fb586d7e5c1106edd5c0a9fdcd6f817016925027a6bdfb5ca8f53f29f58
S21 sha256: 2150c794d2583fe6419357f072f9b08c85ed9a2ba87632ee4ccf067dc4cef085

removed lines: 0
added lines: 10  (2 blank + 3 constants + 3 docstrings + 2 blank)
contiguous added block found at char 56283
reconstructed == R17 bytes: True
```

Deleting exactly the one contiguous added block from S21 reproduces R17 **byte for byte**.
Zero lines removed, zero lines modified. The claim is exact.

The `prior_restage_gate` (136 tests) replays green inside the packet replay and again in my
own battery.

---

## 2. Per-finding closure table

| P20 finding | verdict | evidence |
|---|---|---|
| **NEW-1** (P2) — receipt-backed clause not at its last instance; one survivor emitted into the packet | **CLOSED** | Both named sites repaired. `tools/o008_formal_cycle_admission_v1.py:470-473` now reads *"has no **registered** receipt-backed lane producer (an implemented, unregistered wave-B producer exists on no acceptance path)"*, and that string is what reaches `nonclaims[1]` in `ZENODEX_O008_FORMAL_CYCLE_V1.json` and `.md:192`. `src/core/global_accounting_allocation_certificate_v1.py:88-90` now reads *"No lane is **registered** receipt-backed yet (the implemented wave-B producer is on no acceptance path)"*. The packet's `nonclaims` block and its `esso_evidence.certificate_model.claim_boundary` now agree. My sweep (below) found no other unscoped present-tense instance. |
| **NEW-2** (P3) — the N2 ceiling mirror closed 1 of 8 sibling call sites | **CLOSED** | All seven asymmetric sites now pass `maximum=`; the one symmetric site is untouched. Both of my reproducers now raise; the 4096/256 boundary still constructs. Exhaustive AST sweep and an exhaustive Rust-bound sweep confirm the family is closed with **zero** remaining Python/Rust value divergence. |
| **NEW-3** (P3) — `FRAGMENT_INVALID` unreachability rests on an unpinned inequality; the test name overstates its body | **CLOSED** | The inequality is pinned, and pinned in *both* languages transitively; the pin is non-vacuous; the test is renamed to match its body; the docstring is now accurate; the THV1 successor rewrites the inherited `killed_by` rows; the stale name survives only inside the frozen v11 record and never reaches an executed gate. |

### NEW-1 detail — the sweep

```
$ grep -rn "no receipt-backed\|No receipt-backed\|not receipt-backed\|receipt-backed producer\
\|receipt-backed lane producer" --include=*.py --include=*.md --include=*.json \
    --include=*.yaml --include=*.rs --include=*.tau .
```

Sorting the hits by kind:

- **Repaired (2):** `tools/o008_formal_cycle_admission_v1.py:470`,
  `src/core/global_accounting_allocation_certificate_v1.py:89`.
- **Already registry-scoped (5):** `global_accounting_allocation_certificate_v1.py:649`
  ("with no receipt-backed producer **registered**"), the Rust twin at
  `global_accounting_allocation_certificate.rs:774`, its module header at `:14`
  ("an implemented, unregistered wave-B producer exists"),
  `tools/render_global_accounting_allocation_certificate_v1_golden.py:10` ("**The registry**
  has no receipt-backed producer") and `:53` ("no receipt-backed producer **is registered**").
- **Conditional / normative, not status claims (many):** every
  *"an enabled lane without a receipt-backed producer"* string — reject-code messages, golden
  fixture vector names, ESSO mutant descriptions. These describe a hypothetical lane
  configuration, not the registry's present contents.
- **Frozen history:** superseded THV1 packets v1-v11. Append-only records of prior candidates;
  correct to leave.

**The two intentionally-untouched hits are correctly judged.** I checked both:

- `src/kernels/dex/global_accounting_allocation_certificate_v1.yaml:70` — *"enable_lane models
  future registered receipt-backed producers, not a present registry entry."* Already
  registry-scoped, and the surrounding note at `:64-68` carries the full disambiguation.
  (I also read `:30`, *"An enabled lane needs a receipt-backed producer and a disabled lane is
  registered-empty (inv_producer_gate)"* — that is a statement of the ESSO invariant's
  normative rule, not a claim about the registry's contents. Correct to leave.)
- `tools/check_zrpf_shapeforge_global_epoch_admission_v1.py:7` — *"one evidence-axis
  receipt-backed lane composition increment."* A different checker, about ZRPF ShapeForge lane
  composition. Different module, different lane concept, no relation to the certificate
  registry. Correct to leave.

### NEW-2 detail — reproducers re-run

```
=== P20 NEW-2 repro 1: 4097 balance rows ===
  ValueError: asset transfer balances exceeds its 4096-item ceiling   <-- CLOSED
=== P20 NEW-2 repro 2: 257 policies/supplies ===
  ValueError: asset transfer policies exceeds its 256-item ceiling    <-- CLOSED
=== the 4096 / 256 boundary must still construct ===
  4096 rows OK     state_root=0x9819598dd4454437a4...
  256 policies OK  state_root=0x1591a035eead92fbea...
```

The pre-repair state roots I reported in P20 (`0xd5beb9d59f34a315…`, `0x851aa9130817fec5…`)
are now unreachable through validated construction. `ManagedAssetLifecycleStateV1` with 4097
balance rows likewise raises.

Exhaustive AST sweep of every `_require_ordered_objects` call site in the tree (32 sites):

| P20 table row | now |
|---|---|
| `asset_transfer_types_v1.py` policies / balances / supplies | `:77` / `:84` / `:91` with `MAX_ASSET_POLICY_ROWS_V1` / `MAX_ASSET_BALANCE_ROWS_V1` / `MAX_ASSET_POLICY_ROWS_V1` ✓ |
| `managed_asset_lifecycle_types_v1.py` policies / balances / supplies | `:123` / `:130` / `:137` ✓ |
| `managed_asset_lifecycle_lane_module_v1.py` custody | `:79` with `MAX_ASSET_CUSTODY_ROWS_V1` ✓ |
| `asset_lane_projection_v1.py:318` compatible modules (judged symmetric) | **untouched**, still no ceiling — correct; Rust `asset_lane_projection.rs` checks non-empty and order only |

The remaining eight unbounded sites in the tree are all symmetric with Rust — I checked each
twin rather than assuming: `perps_margin_lane_coordinator_v1.py:79,85,91` against
`PerpsMarginLaneProjectionV1::validate` (`perps_margin_lane_coordinator.rs:94-115`, no length
ceiling either); `:224` compatible modules against `perps_margin_lane_coordinator.rs:270-282`
(non-empty and order only); `perps_margin_types_v1.py:522` against `perps_margin_types.rs:451`
(equality binding, no ceiling); `global_settlement_types_v1.py:1866` against
`LaneTransitionAcceptedV1::validate` (`effects.rs:442-464`, order only, no `deserialize_with`).
`asset_transfer_policy_registry_v1.py:76`, `managed_asset_policy_registry_v1.py:65` and
`perps_margin_types_v1.py:186` look unbounded at the call but each carries its own explicit
`len()` guard against a matching constant (`:74`, `:71`, `:192`) in the same order Rust uses.

The parity binding is mechanical and reads the real Rust source
(`tests/core/test_global_accounting_lane_producers_v1.py:451-455,468-474`).

### NEW-3 detail — the pin, its non-vacuity, and the rename

`tests/core/test_global_accounting_lane_producers_v1.py:476`:

```python
assert proj.MAX_ASSET_LANE_CUSTODY_ROWS_V1 <= cert.MAX_FRAGMENT_ROWS_V1
```

Combined with the two equalities already in the same function
(`:459-461` custody, `:465` fragment), this pins the inequality in **both** languages by
transitivity: `rust MAX_ASSET_CUSTODY_ROWS_V1 == proj.X <= cert.Y == rust MAX_FRAGMENT_ROWS_V1`.
That is a stronger repair than the one I asked for — my P20 note only asked for the Python side.

Live values, all four read at review time:

```
python  MAX_ASSET_LANE_CUSTODY_ROWS_V1 = 4096      rust MAX_ASSET_CUSTODY_ROWS_V1 = 4096
python  MAX_FRAGMENT_ROWS_V1           = 4096      rust MAX_FRAGMENT_ROWS_V1      = 4096
```

Non-vacuity — I re-ran the exact drift scenario from my P20 repro:

```
MAX_FRAGMENT_ROWS_V1 -> 4095: pinned assertion passes? False   (must be False)
MAX_FRAGMENT_ROWS_V1 -> 0:    pinned assertion passes? False   (must be False)
```

So the pin catches the drift that opened the arm on a fully validated path. Not a tautology.

Name and docstring (`:507-518`): `test_fragment_invalid_defensive_arm_has_a_forgery_witness`,
docstring *"This test witnesses ONE path into the arm … The arm's unreachability through
validated constructions is not a structural theorem; it rests on the pinned inequality …"*.
Name matches body; the universal my P20 flagged is gone; the residual dependency is named and
points at the test that pins it.

THV1 hygiene: `certificate-v12` carries the new node id at `:234` and rewrites the inherited
`killed_by` at `:505`. The old name survives only in `certificate-v11` (`:222`, `:492`), a
superseded, frozen record. I confirmed it never reaches an executed gate —
`tools/check_test_hygiene_v1.py --emit-pytest-nodes` with each of the three relevant changed
paths emits 428 node ids, and the stale id appears in none of them.

---

## 3. New findings

### NEW-4 (P3) — Python/Rust bound parity is a hand-maintained name list, and 8 of 23 canonical.rs bounds have no assertion at all

The NEW-2 repair added three names to a hand-maintained list. It did not make the list total.
Parity over `zk/global_settlement_abi_v1/src/canonical.rs` is asserted in two places with two
disjoint regexes and no completeness check:

- `tests/core/test_global_settlement_abi_v1_resource_bounds.py:180-187` —
  regex `MAX_(?:EFFECT_PLAN|GLOBAL_)[A-Z0-9_]+`, covering 12 constants.
- `tests/core/test_global_accounting_lane_producers_v1.py:468-472` — three names spelled out
  literally.

I enumerated every bound in `canonical.rs` and compared it to its Python twin:

```
value mismatches: 0
canonical.rs bounds with NO Python/Rust parity assertion (8 of 23):
  MAX_ATOMS_V1, MAX_CYCLE_BUDGET_V1, MAX_EPOCH_COMMANDS_V1,
  MAX_EPOCH_LEAF_OCCURRENCES_V1, MAX_JOURNAL_BYTES_V1,
  MAX_POLICY_BINDINGS_V1, MAX_ROUTE_MODULES_V1, MAX_TOKEN_BYTES_V1
```

**The bounded refutation first, because it is the more useful half of this finding:** across all
23 bounds there are **zero** value divergences. Every Rust `len() > MAX_…` guard in the crate
has a Python enforcement site with an equal constant — I checked each of the 34 guard sites
individually, including the ones outside the asset family (`economic_command_authorization_registry`,
`economic_command_signature_verifier_{deployment,registry}`, `economic_initial_state_atom_coverage`,
`economic_initial_state_outbox_continuity`, `zdex_hyperdeflation_types`,
`zdex_tokenomics_lane_types`, `lane_module_receipt_verification`, `release`). **There is no
further sibling family carrying the NEW-2 asymmetry.** The answer to the lead's hunt question is
a clean negative, and it is worth recording as one.

What remains is a drift channel, not a live defect. Eight constants agree today with nothing
holding them together, and — the sharper half — a *newly added* Rust bound is matched by
neither regex, so it gets no Python twin and no failing test. That is precisely the mode that
produced NEW-2: `MAX_ASSET_*_ROWS_V1` existed in Rust and the Python side simply never mirrored
it, and no test noticed for the whole campaign.

Minimal repro (no edit needed — the gap is in what is asserted):

```
$ grep -c "pub const MAX_" zk/global_settlement_abi_v1/src/canonical.rs      # 23 bounds
$ grep -n "MAX_(?:EFFECT_PLAN|GLOBAL_)" tests/core/test_global_settlement_abi_v1_resource_bounds.py:183
$ # add a 24th bound to canonical.rs with no Python twin -> both parity tests still pass
```

Fix: one assertion that enumerates every `pub const MAX_[A-Z0-9_]+: usize` in `canonical.rs`
and requires each name to resolve in a single Python mapping, failing on any unlisted name.
That converts the family from a list to a total function and subsumes both existing regexes.

Note this interacts with a disclosed nonclaim rather than contradicting one: the packet already
states that *"canonical.rs, release.rs, and the lane modules are compiled unpinned, so the
closure binds the V1 record shapes and their container decode path, **not the bound constants**"*
(`ZENODEX_O008_FORMAL_CYCLE_V1.md:191`). The parity assertions read `canonical.rs` live at test
time, so the equality is checked, not pinned — consistent with that nonclaim. The finding is
about coverage of the check, not about the pin.

### NEW-5 (P3) — the shared constants are in the right module but the wrong place in it, and are outside its export surface

The layering question the lead asked: **the module is correct.** `global_settlement_types_v1.py`
is Python's twin of `canonical.rs`'s constant surface — it already holds
`MAX_EFFECT_PLAN_*`, `MAX_GLOBAL_*`, `MAX_TOKEN_BYTES_V1`, `MAX_ROUTE_MODULES_V1`,
`MAX_EPOCH_COMMANDS_V1`, `MAX_EPOCH_LEAF_OCCURRENCES_V1`, `MAX_POLICY_BINDINGS_V1`,
`MAX_JOURNAL_BYTES_V1`, `MAX_CYCLE_BUDGET_V1`, `MAX_ATOMS_V1` — and all four consumers already
import from it, so no import edge and no cycle is added. Putting the three bounds anywhere else
would have been worse.

The placement inside it is wrong in three concrete ways:

1. **Out of the mirror block.** `src/core/global_settlement_types_v1.py:27-49` is a contiguous
   block that mirrors `canonical.rs:5-29` in Rust's own declaration order. In `canonical.rs` the
   three asset bounds sit at lines 11-13, immediately after `MAX_POLICY_BINDINGS_V1` and
   immediately before `MAX_EFFECT_PLAN_ROWS_V1` — i.e. exactly between Python's line 31 and
   line 32. Instead they were appended at `:1354-1360`, roughly 1,300 lines below, after
   `OutboxStateV1` and just above `_require_ordered_objects`. A reader auditing "does Python
   mirror `canonical.rs`?" by reading the block at the top now concludes three constants are
   missing.
2. **Different literal convention.** The block at `:27-49` writes `4_096` throughout, matching
   Rust's `4_096`. The new constants at `:1357` and `:1360` write `4096`.
3. **Absent from `__all__`.** Every other row bound in the module is exported; these three are
   not:

```
  MISSING    MAX_ASSET_BALANCE_ROWS_V1
  MISSING    MAX_ASSET_CUSTODY_ROWS_V1
  MISSING    MAX_ASSET_POLICY_ROWS_V1
  IN __all__ MAX_EFFECT_PLAN_ROWS_V1        (and 18 more)
```

Four sibling modules now import these three names across a module boundary while they sit
outside the module's declared export surface. Nothing enforces `__all__` completeness here, so
this is unenforced today — which is the point: it will stay wrong silently.

No behavioural consequence; the parity test binds the values mechanically and everything
replays green. This is a maintainability finding on a claim-hygiene campaign whose whole method
is keeping mirrored surfaces mechanically legible.

Repro: `sed -n '27,49p;1354,1360p' src/core/global_settlement_types_v1.py` beside
`sed -n '5,29p' zk/global_settlement_abi_v1/src/canonical.rs`.

Fix: move the three constants to `:31`/`:32` in Rust's order, write `4_096`, add all three to
`__all__`.

### NEW-6 (P3) — at exactly the new ceiling the asset-transfer transition raises instead of returning a result; symmetric with Rust, so a shared non-total boundary rather than a divergence

The new ceilings are enforced in `__post_init__`, and `AssetTransferStateV1` is constructed for
the **post**-state inside the accept path (`src/core/asset_transfer_module_v1.py:243-248`),
which is not guarded by any reject code. A transfer to a new recipient grows the balance-row
count by one (`_post_balances`, `:70-91`), so a fully validated pre-state sitting exactly at the
ceiling drives the transition into an uncaught `ValueError`:

```
pre_state: 4096 balance rows (== ceiling), root=0x53e83ad10048c800...
UNCAUGHT ValueError from the transition: asset transfer balances exceeds its 4096-item ceiling
  -> not an accept, not a typed reject code
```

Full repro (every object passes its own `__post_init__`; nothing is forged):

```python
from src.core.asset_transfer_module_v1 import transition_asset_transfer_v1
from src.core.asset_transfer_types_v1 import (
    AssetTransferContextV1, AssetTransferCommandV1, AssetTransferPolicyV1,
    AssetTransferStateV1, ASSET_TRANSFER_COMMAND_KIND_V1)
from src.core.global_settlement_types_v1 import (
    EconomicAmountV1, AssetSupplyV1, MAX_ASSET_BALANCE_ROWS_V1)
R = "0x" + "11" * 32
N = MAX_ASSET_BALANCE_ROWS_V1                       # 4096, exactly at the ceiling
rows = tuple(sorted((EconomicAmountV1(f"acct-{i:06d}", "USD", "accounts", 10)
                     for i in range(N)), key=lambda r: r.key))
pre = AssetTransferStateV1(module_release_id=R,
        policies=(AssetTransferPolicyV1("USD", "acct-000000", 0, True),),
        balances=rows, supplies=(AssetSupplyV1("USD", 10 * N),))
ctx = AssetTransferContextV1("zenodex", R, R, 1, R, R, "acct-000001", R)
cmd = AssetTransferCommandV1(ASSET_TRANSFER_COMMAND_KIND_V1, "USD",
                             "acct-000001", "brand-new-owner", 1, 0)
transition_asset_transfer_v1(ctx, pre, cmd)          # ValueError
```

`transition_asset_transfer_v1` is documented *"Apply one transfer with fixed rejection
precedence and no hidden inputs"* (`:286`), returns `AssetTransferResultV1`, and its reject
enum has 11 closed codes (`asset_transfer_types_v1.py:32-43`), none of which covers a row
ceiling. Same shape in `managed_asset_lifecycle_module_v1.py:236-241`, whose 14-code enum
(`managed_asset_lifecycle_types_v1.py:44-58`) likewise has no row-ceiling code.

**This is not a divergence and not a regression, and I want to be precise about that.** Rust
does the same thing: `accept_transfer` builds the post state and calls `accepted.validate()?`
(`zk/…/asset_transfer.rs:344`), which reaches `post_state.validate()`
(`asset_transfer_types.rs:242`) and returns `Err(InvalidBounds("asset transfer balance rows"))`
(`:74`) — an out-of-band error, not an `AssetTransferResultV1::Rejected`. So both languages
exit out-of-band at exactly the same input. And *before* this repair Python **accepted** the
4097-row post state and returned a valid `AssetTransferAcceptedV1` while Rust errored; the
repair closed that divergence. The residual is a pre-existing shared property that S21 newly
exposed on the Python side.

What remains worth naming: CLAUDE.md's CBC contract requires the transition to be a total
function returning a deterministic accept or a deterministic reject, and this boundary returns
neither in either language. It is fail-closed (no state moves, authority NONE, nothing mounted),
so severity is P3. There is no test at the boundary in either language.

Fix, when the lane is worked next: add a row-ceiling reject code to both enums and check the
post-state row count before construction, or state in the module docstring that the ceiling is
an ABI decode bound rather than a transition reject and pin the boundary with a test.

---

## 4. Observations (no finding)

1. **`completion_scope[8]` keeps the weaker wording, and I judge that acceptable.**
   `tools/o008_formal_cycle_admission_v1.py:274-278` still reads *"with a producer registry
   exhaustive over the twelve lanes and no receipt-backed producer"*, and it is emitted into the
   packet. I considered calling this a NEW-1 survivor and decided against it on two grounds.
   Grammatically the clause's head noun is *"a producer registry"* — it predicates over the
   registry, so the running-code reading ("no such producer is implemented anywhere") is not
   available, unlike the bare *"The checker has no receipt-backed lane producer"* that NEW-1 was
   about. And `completion_scope[9]`, the very next entry, states that *"the first receipt-backed
   fragment producer (wave B, ASSET_TRANSFER) is implemented in Python and Rust … the
   certificate registry keeps ASSET_TRANSFER at NO_PRODUCER until then, so no acceptance path
   uses it."* The two entries agree; a reader of the block gets both facts. That is exactly the
   internal contradiction NEW-1 objected to, absent. Adding "registered" would still be an
   improvement, and I would take it in a later candidate, but it is not a finding.
   `:288` (a conditional describing a Lean theorem) and `:408` (a parenthetical code comment,
   not emitted) are fine as they stand.

2. **The N4 assertions are now redundant with the NEW-2 assertions.** Because
   `asset_lane_projection_v1.py:34,37,40` alias the shared constants,
   `proj.MAX_ASSET_LANE_CUSTODY_ROWS_V1 is types.MAX_ASSET_CUSTODY_ROWS_V1` is `True`, so
   `test_global_accounting_lane_producers_v1.py:459-461` and `:470-472` assert the same three
   equalities twice. Harmless; worth knowing before someone deletes the "duplicate".

3. **THV1 `certificate-v12` pins the three Python sibling files but not their Rust twins.**
   It gains `asset_transfer_types_v1.py` (`1c5e7fd9…`), `managed_asset_lifecycle_types_v1.py`
   (`d6867627…`) and `managed_asset_lifecycle_lane_module_v1.py` (`312f6214…`), all matching
   disk. `zk/…/asset_transfer_types.rs`, `zk/…/managed_asset_lifecycle_types.rs` and
   `canonical.rs` are unpinned. For `canonical.rs` that is deliberate and already disclosed
   (see NEW-4); for the two Rust type modules it is simply the existing pin scope.

4. **The NEW-3 docstring names one dependency where there are three.** It says unreachability
   *"rests on the pinned inequality"*. In P20 I traced two further dependencies: the key
   equality `EconomicAmountV1.key == ControlledLocationRowV1.key`, and
   `LaneStateRootV1.__post_init__` forbidding the zero root. Naming only the inequality is
   defensible — it is the one dependency that can drift by a constant edit, while the other two
   are structural type facts — so I am not calling it a finding.

---

## 5. What C8'''' genuinely sealed

- The registry-scoped wording now reaches its last instance in both the packet nonclaims and the
  certificate registry comment; the packet no longer disagrees with itself.
- Python and Rust now agree on which asset-lane states are well-formed. I verified this
  exhaustively rather than at the seven named sites: **zero value divergences across all 23
  `canonical.rs` bounds and all 34 Rust ceiling guards.** The state roots I exhibited as
  divergent in P20 are unreachable.
- The `FRAGMENT_INVALID` unreachability argument rests on a pinned, non-vacuous, two-language
  inequality instead of a numeric coincidence between four files, and the test that carries it
  no longer claims more than it checks.
- The semantic-restage lineage moved with the bytes, and its "additive constants only" claim is
  exact under byte-level reconstruction.

## 6. Claim ceiling

Unchanged and byte-identical to R17. `formal_core_complete=False`; `migration`, `production`,
`publication`, `release`, `settlement`, `value_movement` and `verifier` authority all `NONE`;
`value_movement_gates_closed 0 / 12`; `o008_status OPEN_EXACT_ALL_12_RECONCILIATION_MISSING`.
This review grants no authority and moves no ceiling.

## 7. sha256 of every file quoted

```
2150c794d2583fe6419357f072f9b08c85ed9a2ba87632ee4ccf067dc4cef085  src/core/global_settlement_types_v1.py
de37103e3905b9236a2a99f2ebe0eae9c6cb3453f434bb04f8fe90a00b51aa75  src/core/global_accounting_allocation_certificate_v1.py
26be354b4d83af62a5c96967bad4f505cd2c8332fc9ae43a851b0c5b697e44b7  src/core/global_accounting_lane_producers_v1.py
1c5e7fd918870892565068b189d784221dc085d2a65eab353031d4714aa8481f  src/core/asset_transfer_types_v1.py
3cb479e053efe18f962e773e6f158582dccbc6da07fc90ee009d98d86df95596  src/core/asset_transfer_module_v1.py
3078bb86c1225a9035d1603654a901973092ef9d430959ba4c18f83d97863a0d  src/core/asset_transfer_policy_registry_v1.py
d6867627e5f5d45fe8f0209f53de26e124151e5b9f74a67a75a322b3b0774172  src/core/managed_asset_lifecycle_types_v1.py
312f6214901a46e912156c6b0f7c9f28008506f000abbae93aafb84b8587769c  src/core/managed_asset_lifecycle_lane_module_v1.py
fa808d2dccf69fe9945f5580cb3c230a78d48e35693bc8af322a08d38b2f3d74  src/core/managed_asset_lifecycle_module_v1.py
8e0cb30a530cb796a8fdf388dca74d85d1aee79e28063f36ff239f6c2f1bd22f  src/core/managed_asset_policy_registry_v1.py
c7ed4c946d5d411ca654c5b54f5d129f817546a6c41c82719d4b9a13d0fbc75c  src/core/asset_lane_projection_v1.py
30061112b5239934c6b8c192ac893078a2a092d8e2310f7fa50ab9a1314882a9  src/core/perps_margin_types_v1.py
b0119e640e45c3a0e55c160d12a0fbe857d4fb54cf5a51620535c80b2044a604  src/core/perps_margin_lane_coordinator_v1.py
2031804a80f251592084067c19415dd5ecd6bd0814718fe3d3b0af7866f47e24  tools/o008_formal_cycle_admission_v1.py
c669f26a50ed6922548bcc80826fc929ff62aeb5f0a81189a5828fcb71a12a16  tools/check_global_settlement_canonical_manifest_v1.py
238c85cf91a8b9ab0d9e45769addf1bb4082b6e27f2bc653e2cb72b0073e6b46  tools/check_zrpf_shapeforge_global_epoch_admission_v1.py
706dc9eeaacb7be93b716dbc565c7ef4b110f331aa76554fc54114b31380c4d9  tests/core/test_global_accounting_lane_producers_v1.py
f7705ca92f29e6f27fa0fffbcd77527fba4be2aaf89ae4ff7629d0f51810cb5a  tests/core/test_global_settlement_abi_v1_resource_bounds.py
31b5b026d689077a20b6f64e16abeef6d28c6aef4d8abc720775b2e8f31e0c1a  tests/formal/test_esso_global_settlement_core_v1.py
b97d1619240e19944bac68a97efd843797da89b038bb8dbbbc20e2b013c21a6f  tests/formal/test_lean_global_accounting_allocation_certificate_v1.py
c05b353de2dc89aba4d8b9ef7f4cdc67f46ff6c73b425228e95f94cc3efd01d3  tests/formal/test_lean_global_claimant_custody_relation_v1.py
7afad7b256a19b1a162dd24dad5ca89f3ebe47c8c02f63bb60d1cfff7b709456  src/kernels/dex/global_accounting_allocation_certificate_v1.yaml
6cce2178582ae4f38ff95fade6f544ae54b0d7568b7599dfa6214a56515cd46a  zk/global_settlement_abi_v1/src/canonical.rs
c6ef355d4d1f7ee3770d99fe067d4b45cb2ea3b178f3ceca2be049de92ef853a  zk/global_settlement_abi_v1/src/asset_transfer.rs
717fac261af10b837ad11276c37cf9513defea48909e94273f16ae6ad6ec38ae  zk/global_settlement_abi_v1/src/asset_transfer_types.rs
33620989420de792f73e0d181ff8828e9c379f0d052f6e3d9633380da69e2835  zk/global_settlement_abi_v1/src/managed_asset_lifecycle_types.rs
57c5e17c545b5034ac252470f27b0d5891895a6a76839fd80e4e6a1b24689762  zk/global_settlement_abi_v1/src/perps_margin_lane_coordinator.rs
bd11416d4f48dcb59a584a07edc02c8e558f9caa9f7939871d7cea1aaf5709f0  zk/global_settlement_abi_v1/src/perps_margin_types.rs
0e691ba4be7be58ded9a87ba28f1cd747b67bf5cdfd4c39bbe232480fe20b7f6  zk/global_settlement_abi_v1/src/effects.rs
f7452d9a8d7036d18fe23700af733fb8dc83b454ab5a50835e4ea509c9288653  zk/global_settlement_abi_v1/src/global_accounting_allocation_certificate.rs
4c92915cbcde4c588b88fc8a1b9aec570c1cc20fb2b153679fb4dcf3b8ea6230  zk/global_settlement_abi_v1/src/global_accounting_lane_producers.rs
f053f20cd3b0703b796fdaa7f846a64a45eb56f8ae7ac2ffd46d4e7f4630842c  tests/evidence/test_hygiene/THV1-20260901-o008-formal-cycle-admission-v22.json
110d7b4b2bbf581178acf39ee92701eb49fe69d5dad7664106829382687e282b  tests/evidence/test_hygiene/THV1-20260901-global-accounting-allocation-certificate-v12.json
9b6f409939f57068e9a6a450d97698d4a4219c787d70d60d5aa775b7d4360b77  tests/evidence/test_hygiene/THV1-20260901-global-settlement-formal-core-semantic-restage-v4.json
5716dbd1dfc4a735cdd510aaed472423440e52c01ace4510c2e5daa265664802  tests/evidence/test_hygiene/THV1-20260901-claimant-backing-guard-golden-v15.json
48441f1fc8a598adc969bfac19013b3554005a6946bfe3fcf9d6329d769b6da6  docs/research/ZENODEX_GLOBAL_FUNCTIONAL_CORE_FORMAL_BLUEPRINT_V1.md
fdabeebbe0e0b1b04c1f99c0167c235327f2e1f0921d4f00fe33806ddd0bffc5  docs/research/ZENODEX_O008_FORMAL_CYCLE_V1.json
d7bf16c8bec6a0151af33965958a863a0e51afb928d0645e3b12875a6cc1b827  docs/research/ZENODEX_O008_FORMAL_CYCLE_V1.md
```

Superseded blob quoted for the reconstruction proof:
`13871fb586d7e5c1106edd5c0a9fdcd6f817016925027a6bdfb5ca8f53f29f58` =
`src/core/global_settlement_types_v1.py` at R17 (`c907b3007`).

## 8. Ordered repair list for C8'''''

1. Replace the two hand-maintained parity name lists with one assertion that enumerates every
   `pub const MAX_[A-Z0-9_]+: usize` in `canonical.rs` and requires each to resolve in a single
   Python mapping, failing on any unlisted name (**NEW-4**). This is the highest-value item: it
   closes the drift mode that produced NEW-2 rather than patching its latest instance.
2. Move `MAX_ASSET_POLICY_ROWS_V1` / `MAX_ASSET_BALANCE_ROWS_V1` / `MAX_ASSET_CUSTODY_ROWS_V1`
   from `global_settlement_types_v1.py:1354-1360` up into the mirror block at `:31`, in Rust's
   declaration order, written `4_096`, and add all three to `__all__` (**NEW-5**).
3. Either add a row-ceiling reject code to `AssetTransferRejectCodeV1` and
   `ManagedAssetLifecycleRejectCodeV1` and check the post-state row count before construction in
   both languages, or state in both module docstrings that the ceiling is an ABI decode bound
   rather than a transition reject — and in either case pin the boundary with a test
   (**NEW-6**).
4. Optional: add "registered" to `completion_scope[8]`
   (`tools/o008_formal_cycle_admission_v1.py:275`) so the whole packet uses one vocabulary
   (observation 1).
