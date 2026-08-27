# ZenoDEX Global Functional Core Formal Blueprint V1

Date: 2026-08-26

Task: `FORMAL-MODEL-001` (`rlm-subagent-task/v1`, role `implementer`)

Implementation base: `f7e851565e063fb3e74b060a9c45f27b8621a8d7`

Status: `RESEARCH_ONLY_UNMOUNTED`, `FORMAL_VERDICT_INCOMPLETE_ESSO_ABSENT`

Production authority: `NONE`

Settlement authority: `NONE`

Release authority: `NONE`

Value-moving authority: `NONE`

This document is advisory until an independent Max review and a local replay
of the commands in the Evidence section. It is not a proof, a verifier
receipt, a release, a migration certificate, a settlement authorization, or a
whole-DEX safety claim.

## Result

This blueprint pins the structural `GlobalSettlementABI V1` functional core to
exact source and gives it one bounded, executable formal model before any FCIS
runtime work:

- `src/kernels/dex/global_settlement_core_v1.yaml` is an `esso-ir/v1` model
  with one total step action, 40 state variables, and 13 safety invariants.
- `tests/formal/test_esso_global_settlement_core_v1.py` is the executable
  bounded model: a strict interpreter of the same YAML that runs AAA
  scenarios, boundary cases, reject-is-exact-no-op cases, sequential
  composition, bounded sweeps, and six named semantic mutants with RIPR
  evidence. It also carries the ESSO `validate` and `verify-multi`
  invocations.
- This document records the source pins, the model, its safety, liveness,
  refinement, and nonclaim sections, the retained counterexamples, the model
  bounds, and the exact commands with their results.

The ESSO toolchain is absent from this checkout (`external/ESSO` does not
exist and `python3 -m ESSO` reports `No module named ESSO`), so the two ESSO
tests skip. That skip is recorded as `INCOMPLETE`. It is not a pass, and no
solver-backed formal verdict is claimed here. The executable bounded model
passed locally (43 passed, 2 skipped).

## Source pins

The repository base is `f7e851565e063fb3e74b060a9c45f27b8621a8d7`. SHA-256
values were computed on that base. The first row is enforced by
`test_blueprint_pins_base_commit_and_semantic_source_hash`; drift there means
this blueprint must be re-reviewed before it is trusted. The remaining rows are
informative pins.

| Pinned source | SHA-256 |
| --- | --- |
| `src/core/global_settlement_types_v1.py` | `df06cbff2800ed7e2a1a296766cd132a86fdcce51c5d8a9da3a01791344c16b0` |
| `src/core/global_settlement_abi_v1.py` | `c02a137fdd2e892a5a4529b99e6ee4054394b4b68e863c2c24fc2ec2346846e5` |
| `src/core/asset_transfer_module_v1.py` | `d8ac43bf64f08ea1a8318c21c4f0f6d1c5ef4baf7bb6e91820e29a2762695aef` |
| `src/core/managed_asset_lifecycle_module_v1.py` | `4e116ee9b875834dfae96f0c526a1043453c1d262c2e96a610d498d01cc5dc15` |
| `src/core/asset_lane_coordinator_v1.py` | `6047468214d835ff9d6d9823d845df4ef0c4a1cd6d94f098911377daaf4996ae` |
| `docs/research/GLOBAL_SETTLEMENT_ABI_V1_REFERENCE_20260805.md` | `294d61cc85da08cfb93a3f44ce815bffa5e6b9776f390395adf2db3859de010d` |
| `docs/research/ZENODEX_WHOLE_PROGRAM_PLAN_V2.json` | `eedf486571e3d628294c0ad965fe46d0589565478a4db9104141d5537b3a5684` |
| `docs/research/ZENODEX_WHOLE_PROGRAM_PLAN_V2.md` | `f865f36b59a0bdfb5ce95fbefeb36ab64e6b37f4e94144b3f1a3404806a580d1` |
| `docs/research/ZENODEX_WHOLE_VALUE_MOVEMENT_FORMAL_SAFETY_CLAIM_V1.md` | `32985ee88b0b15a0b6ef1408e60ac1767f93e20eade434090011e144ecd56990` |
| `src/kernels/dex/global_settlement_core_v1.yaml` (subject) | `9dc7f7657e0f4248e1d4720c6ef3ce655411e7d48cf36429a5e5fa3691b52440` |

Pinned semantics, by source location on the base:

- Lane registry: `LaneIdV1` and `ALL_LANE_IDS_V1`
  (`src/core/global_settlement_types_v1.py:201-216`) close exactly twelve
  lanes in canonical order; `LaneRegistryV1.release_for` rejects any other
  value as `unknown lane id` (`:463-466`).
- Widths: consensus control fields are unsigned 64-bit, atoms are unsigned
  128-bit, signed deltas are signed 128-bit (`:26-29`).
- Global state: `GlobalEconomicStateV1` commits `height`, unique
  `replay_state` rows whose occurrence ids must be unique, and canonically
  ordered `terminal_obligations` (`:1273-1344`, uniqueness `:1323-1331`,
  obligations `:1332-1337`). `TerminalObligationV1` carries `OPEN`,
  `DRAINED`, or `TOMBSTONED` status (`:1190-1223`).
- Effect rows: `ISSUE` rows are positive, `BURN` rows are negative, every row
  is nonzero (`:1438-1471`).
- Conservation rows: `AssetConservationRowV1` requires
  `owned_and_custodied_post = owned_and_custodied_pre + authorized_issue -
  authorized_burn` and `supply_post = supply_pre + authorized_issue -
  authorized_burn` (`:1474-1515`). `FeeConservationRowV1` requires
  `fee_charged = current_allocations + carried_residue` (`:1518-1542`).
- Effect plan: issue and burn projections must equal the canonical rows
  (`:1637-1653`); fee allocations must equal the fee row (`:1655-1666`); the
  empty plan is `GlobalEconomicEffectPlanV1.empty()` (`:1684-1686`).
- Rejection: `LaneTransitionRejectedV1` must keep the exact pre-state root and
  carry the empty effect plan (`:1754-1785`); the closed transition reject
  codes are `LaneTransitionRejectCodeV1` (`:1700-1707`).
- Module reject orders used as informative anchors:
  `src/core/asset_transfer_module_v1.py:126-161` (`UNKNOWN_COMMAND`,
  `UNAUTHORIZED_SUBJECT`, `ZERO_AMOUNT`, `EFFECT_DELTA_OVERFLOW`,
  `INSUFFICIENT_BALANCE`, `BALANCE_OVERFLOW`) and
  `src/core/perps_margin_module_v1.py:111-222` (`ACCOUNT_MISSING`,
  `NONCE_MISMATCH`, `ZERO_AMOUNT`, `INSUFFICIENT_COLLATERAL`). Epoch
  composition rejects disconnected conservation and lane-write histories
  (`src/core/epoch_effect_composition_v1.py:91,141`).
- Whole-program plan: obligation `O-008` (phase P3) requires per-asset
  conservation across all 12 lanes and reject-no-op evidence
  (`docs/research/ZENODEX_WHOLE_PROGRAM_PLAN_V2.json:437-446`). Policy
  decisions `UP-01`, `UP-12`, `UP-13`, `UP-14`, and `UP-16` remain
  unselected (`:300-315`).
- Safety claim: `Step(R, P, S, C) = Reject(code) | Accept(...)`, the
  accepted-transition equations, and rejection safety
  (`docs/research/ZENODEX_WHOLE_VALUE_MOVEMENT_FORMAL_SAFETY_CLAIM_V1.md:58-63,
  146-160, 193-206`).

## Scope

In scope: the structural step of the global functional core, abstracted to
two assets, one authenticated subject account per asset, four named custody
partitions, a closed command set, a closed lane registry, a bounded height,
and a bounded occurrence identity space.

Out of scope: canonical bytes and roots, receipts, proof journals, routes and
lane composition, epochs, Oracle occurrences, external outbox, migration,
durable publication, cryptographic authentication, and every economic policy.

## Model

### State

Two assets `a` and `b`. For each asset `X` every same-ledger atom sits in
exactly one of five disjoint accounting partitions, and the model tracks the
committed supply:

```text
payer_X        account balance of the authenticated subject
rest_X         every other account balance
fee_alloc_X    named custody holding current fee allocations
fee_residue_X  named custody holding explicitly carried fee residue
obligation_X   named custody backing OPEN terminal obligations
supply_X       committed supply
owned_X      := payer_X + rest_X + fee_alloc_X + fee_residue_X + obligation_X
```

Control state is `height` (0..3) and three occurrence-consumed flags
`consumed_0..2`. Ghost variables (prefix `g_`) journal the last step: the
decision, the reject code, the command kind, the lane of the last accepted
write, the pre-state height and consumed flags, a mixed-radix pre-state root
per asset, the pre-state owned and supply totals per asset, and the
`ISSUE`, `BURN`, and fee rows per asset. The transition never reads a ghost
except `g_lane`, which preserves itself on rejection; a structural test
enforces this so the ghost journal cannot influence acceptance.

### Command

One total action `step`. Its parameters are the command fields:

| Parameter | Domain | Meaning |
| --- | --- | --- |
| `command_kind` | 0..5 | 0 `CMD_TRANSFER`, 1 `CMD_ISSUE`, 2 `CMD_BURN`, 3 `CMD_OPEN_OBLIGATION`, 4 `CMD_DRAIN_OBLIGATION`, 5 outside the closed set |
| `asset` | 0..1 | 0 = `a`, 1 = `b` |
| `lane_index` | 0..12 | 0..11 index the twelve `LaneId` symbols in canonical order; 12 is outside the registry |
| `bound_height` | 0..3 | replay identity bound by the command |
| `occurrence` | 0..2 | occurrence identity |
| `amount` | 0..4 | atoms moved, issued, burned, opened, or drained |
| `fee_charged` | 0..4 | fee atoms charged by the fee policy (parameterized) |
| `fee_alloc` | 0..4 | fee atoms allocated now (parameterized); `fee_charged - fee_alloc` is carried residue |
| `authority_ok` | bool | verifier-produced authorization fact; an abstraction, never a caller-supplied runtime authority |

The twelve lane symbols are exactly `ASSET_TRANSFER`, `SPOT_LIQUIDITY`,
`FARM_INCENTIVES`, `ZDEX_TOKENOMICS`, `ZUSD_MONETARY`, `PERPS_MARKET`,
`ORACLE_MARKET`, `SEALED_AUCTION`, `STRATEGY_ESCROW`, `PROOF_REWARDS`,
`EXTERNAL_CUSTODY`, and `GOVERNANCE_MIGRATION`.
`test_model_declares_exactly_the_twelve_stable_lane_ids_in_canonical_order`
compares them to `ALL_LANE_IDS_V1` from the pinned source.

### Accepted step

For the selected asset only:

```text
TRANSFER:         payer -= amount + fee_charged;  rest       += amount
ISSUE:            payer += amount - fee_charged;  supply     += amount
BURN:             payer -= amount + fee_charged;  supply     -= amount
OPEN_OBLIGATION:  payer -= amount + fee_charged;  obligation += amount
DRAIN_OBLIGATION: payer += amount - fee_charged;  obligation -= amount
every accepted step:
  fee_alloc   += fee_alloc
  fee_residue += fee_charged - fee_alloc
  height      += 1
  consumed[occurrence] := true
  rows: issue = amount if ISSUE else 0; burn = amount if BURN else 0;
        fee row = (fee_charged, fee_alloc, fee_charged - fee_alloc)
```

The untouched asset keeps every partition and emits zero rows.

### Reject table

The first failing condition, in this order, names the code. Every rejection
is an exact no-op: identical state, empty rows, no height advance, no
occurrence consumption.

| Code | Condition | Informative source anchor |
| --- | --- | --- |
| `RC_UNKNOWN_LANE` | `lane_index > 11` | registry closure, types `:463-466` |
| `RC_UNKNOWN_COMMAND` | `command_kind > 4` | `LaneTransitionRejectCodeV1.UNKNOWN_COMMAND` |
| `RC_DUPLICATE_OCCURRENCE` | occurrence already consumed | unique replay occurrence ids, types `:1329-1331` |
| `RC_STALE_REPLAY` | `bound_height != height` | stale competing head, ABI reference publisher paragraph |
| `RC_UNAUTHORIZED` | `authority_ok` is false | `UNAUTHORIZED_SUBJECT`, transfer module `:136-137` |
| `RC_MISSING_TERMINAL_OBLIGATION` | drain while `obligation_X = 0` | `ACCOUNT_MISSING`, perps module `:164-165` |
| `RC_ZERO_AMOUNT` | `amount = 0` | `ZERO_AMOUNT`, transfer module `:140-141` |
| `RC_FEE_RECONCILIATION` | `fee_alloc > fee_charged` | fee row reconciliation, types `:1533-1534` |
| `RC_INSUFFICIENT` | a post quantity would be negative | `INSUFFICIENT_BALANCE`, transfer module `:77-78` |
| `RC_UNREPRESENTABLE` | a post quantity would exceed width 4, or `height = 3` | `BALANCE_OVERFLOW`, transfer module `:79-80`; the height case is a model horizon artifact |

The mapping column is informative. The model's codes are its own closed enum;
no claim is made that they are the exact source codes.

### Bounds

| Bound | Model | Source |
| --- | --- | --- |
| atoms per quantity | 0..4 | unsigned 128-bit |
| height | 0..3 | unsigned 64-bit |
| occurrence identities | 3 | unbounded replay set |
| assets | 2 | unbounded |
| accounts per asset | subject account plus one aggregate | unbounded |
| lanes | exactly 12 plus one unregistered index | exactly 12 |
| command kinds | 5 closed plus one unknown | per-release closed set |
| pre-state root | base-5 mixed radix over six quantities (max 15624) | SHA-256 canonical root |

## Safety

Every property is a state invariant checked at genesis and preserved by the
single step action. Each invariant is written to be inductive on its own so
the result does not depend on whether a checker assumes the conjunction or one
invariant at a time.

| Invariant | Meaning |
| --- | --- |
| `inv_core_bounds` | every quantity is in `[0, 4]`; height is in `[0, 3]` |
| `inv_owned_equals_supply_a`, `inv_owned_equals_supply_b` | `owned_X = supply_X` per asset (the `AssetLaneStateProjectionV1` equation) |
| `inv_owned_step_a`, `inv_owned_step_b` | `owned_X = owned_pre_X + issue_X - burn_X` for the last step |
| `inv_supply_step_a`, `inv_supply_step_b` | `supply_X = supply_pre_X + issue_X - burn_X` for the last step |
| `inv_fee_step_a`, `inv_fee_step_b` | `fee_charged_X = fee_alloc_X + fee_residue_X` for the last step |
| `inv_step_rows_nonnegative` | canonical rows are unsigned atoms |
| `inv_reject_exact_noop` | a rejected step keeps both pre-state roots, height, and consumed flags, emits zero rows, and carries a reject code |
| `inv_accept_advances_one` | an accepted step advances height by one, consumes exactly one fresh occurrence, and carries no reject code |
| `inv_consumed_monotone` | a consumed occurrence identity is never released |

Required semantics and where they are established:

- Exact twelve stable lane IDs: enum `LaneId`, `g_lane`, and the source
  comparison test.
- Per-asset holdings and supply conservation with explicit issue and burn:
  `inv_owned_equals_supply_*`, `inv_owned_step_*`, `inv_supply_step_*`, plus
  the direct specification checks in `spec_failures`.
- Fee charged equals allocations plus carried residue, per asset:
  `inv_fee_step_*`.
- Rejection is an exact no-op with empty effects: `inv_reject_exact_noop`
  and the per-code no-op tests.
- Accepted steps require non-negative post quantities: the acceptance
  conjunction (`c_nonnegative_post`) and `RC_INSUFFICIENT`.
- Sequential composition preserves the per-asset equations: the invariants
  are inductive, and `test_sequential_composition_preserves_per_asset_equations`
  checks the cumulative equations over a three-step trace.
- Unknown lane, unknown command, duplicate occurrence, stale replay identity,
  and missing terminal obligation reject: the reject table and
  `test_each_reject_class_is_an_exact_noop_with_empty_rows`.

## Liveness

These are bounded progress and non-vacuity statements checked by the
executable model; the ESSO model states no liveness kind.

- `L1` Non-vacuity of acceptance: every closed command kind has an accepting
  instance from an invariant-satisfying state
  (`test_every_command_kind_and_every_reject_class_is_reachable`).
- `L2` Non-vacuity of rejection: every reject code is reachable from an
  invariant-satisfying state (same test).
- `L3` Bounded progress: from genesis, three accepted steps reach the height
  horizon; at the horizon the step stays total and every command rejects as
  an exact no-op
  (`test_bounded_progress_reaches_the_horizon_then_every_command_rejects_totally`).
- `L4` Totality and determinism: one action with guard `true`, one update per
  state variable, identical inputs give identical outputs
  (`test_model_is_one_total_deterministic_step_action`,
  `test_step_is_deterministic_for_identical_inputs`, and the random box).

Not claimed: fairness, eventual acceptance under adversarial input, or any
progress beyond the finite horizon.

## Refinement

The intended direction is that the source step refines the model step after
abstraction. The correspondence is by inspection of the pinned source; no
refinement theorem, simulation relation, or generated-reference parity exists
yet.

| Model | Source |
| --- | --- |
| `payer_X`, `rest_X` | `GlobalEconomicStateV1.balances` rows for the asset |
| `fee_alloc_X`, `fee_residue_X`, `obligation_X` | `GlobalEconomicStateV1.custody` rows and `terminal_obligations` amounts |
| `supply_X` | `GlobalEconomicStateV1.supplies` |
| `height`, `bound_height` | `GlobalEconomicStateV1.height` and the command's bound pre-state identity |
| `consumed_i`, `occurrence` | `replay_state` occurrence ids and `occurrence_consumptions` |
| `lane_index`, `g_lane` | `LaneIdV1` and the lane of the single module-local `LaneWriteV1` |
| `g_issue_X`, `g_burn_X` | `ISSUE` and `BURN` rows and `AssetConservationRowV1.authorized_*` |
| `g_fee_*_X` | `FEE_ALLOCATION` rows and `FeeConservationRowV1` |
| `g_pre_root_X` | the exact pre-state root that a rejection must preserve |
| `RC_*` | the module reject codes and `LaneTransitionRejectCodeV1` (informative) |

Abstractions that a future refinement argument must discharge: the single
subject account, two assets, three occurrence identities, small widths, the
absence of canonical bytes and hashes, the absence of route and lane
composition, the collapse of module context checks into `authority_ok`, and
the fee policy collapsed into two parameters.

## Policy inputs: parameterized or blocked

| Input | Treatment | Plan reference |
| --- | --- | --- |
| fee amount and allocation split | parameterized as `fee_charged` and `fee_alloc`; no percentage is selected | `UP-01`, `UP-12`, `UP-13` |
| burn floor or retained-supply rule | blocked; the model only checks explicit burn rows and non-negative supply | `UP-14`, `UP-20` |
| issue and burn authority | parameterized as `authority_ok`; no grant policy is selected | `UP-13` |
| Oracle economics | blocked; no Oracle occurrence exists in the model | `UP-06` |
| margin rules | blocked; only the terminal-obligation shape of a close is modelled | `UP-05` |
| governance decisions and route selection | blocked; only registry membership of the twelve lanes is checked | `UP-10`, `UP-16` |
| replay domains beyond height and occurrence identity | blocked | `UP-16` |

## Counterexamples and semantic mutants

Each mutant is a structure-preserving edit of the loaded YAML applied by the
test module. For every mutant the honest model passes the witness, the mutant
reaches the edited node, infects the post-state, propagates to an observed
variable, and is revealed by a named invariant (RIPR). The bounded accept box
also kills every mutant
(`test_every_named_mutant_is_killed_by_the_bounded_accept_box`).

| Mutant | Defect | Minimal witness | Revealed by | Note |
| --- | --- | --- | --- | --- |
| `MUT_CROSS_ASSET_SCALAR_SUM` | issue of asset `a` credits `supply_b` | genesis; `ISSUE(a, 1)` gives `owned_a = 1`, `supply_a = 0`, `supply_b = 1` | `inv_owned_equals_supply_a`, `inv_supply_step_a` | the scalar identity `owned_a + owned_b = supply_a + supply_b` still holds (1 = 1), so cross-asset scalar summation cannot reveal the defect |
| `MUT_OMITTED_BURN` | supply is not decremented on burn | `payer_a = supply_a = 1`; `BURN(a, 1)` gives `owned_a = 0`, `supply_a = 1` | `inv_owned_equals_supply_a`, `inv_supply_step_a` | implicit burn |
| `MUT_OMITTED_BURN_ROW` | the explicit `BURN` row is omitted | same witness; `owned_a = supply_a = 0` with `burn_a = 0` | `inv_owned_step_a`, `inv_supply_step_a` | supply changed without a row |
| `MUT_OMITTED_RESIDUE` | the unallocated fee remainder is dropped | `payer_a = supply_a = 2`; `TRANSFER(a, amount 1, fee 1, alloc 0)` gives `owned_a = 1`, `supply_a = 2` | `inv_owned_equals_supply_a`, `inv_owned_step_a` | the fee row alone still reconciles (1 = 0 + 1); only holdings conservation reveals the loss |
| `MUT_OMITTED_RESIDUE_ROW` | residue is custodied but the fee row omits it | same witness; `fee_residue_a = 1` with row residue 0 | `inv_fee_step_a` | |
| `MUT_REJECT_WITH_EFFECTS` | a rejected step still moves the fee | `payer_a = supply_a = 1`; `TRANSFER(a, amount 0, fee 1)` is `RC_ZERO_AMOUNT` yet `payer_a = 0`, `fee_alloc_a = 1` | `inv_reject_exact_noop` | `owned_a = supply_a` still holds, so conservation alone cannot reveal it |

## Evidence

Commands were run on the base from the repository root. Each command was
invoked separately.

```text
python3 -m ESSO --help
  -> /usr/bin/python3: No module named ESSO   (toolchain absent; no verdict)

python3 -c "import ESSO, sys; print(ESSO.__file__)"
  -> ModuleNotFoundError: No module named 'ESSO'

python3 -c "import yaml; d=yaml.safe_load(open('src/kernels/dex/global_settlement_core_v1.yaml')); ..."
  -> 40 40 13 9 40 19 40 19   (state vars, inits, invariants, params, updates, effects, observed vars, observed effects)

PYTHONDONTWRITEBYTECODE=1 python3 -m pytest -q -p no:cacheprovider \
  tests/formal/test_esso_global_settlement_core_v1.py -rs
  -> 43 passed, 2 skipped
     SKIPPED: ESSO toolchain absent (no external/ESSO checkout, no importable
     ESSO): formal verdict INCOMPLETE; a skip is not a pass   (x2)

python3 -m ruff check tests/formal/test_esso_global_settlement_core_v1.py
  -> All checks passed!
```

Local toolchain facts: Python 3.12.3, pytest 7.4.4, PyYAML 6.0.1, ruff
0.16.0; `z3` and `cvc5` binaries are on `PATH`; the `ESSO` package is not
installed and `external/ESSO` is absent.

The ESSO invocation that the repository uses (`src/fire/verifier/esso_kernels_v1.py`,
`tests/formal/test_esso_settlement_witness_lifecycle_v1.py`) and that must be
replayed on a host with the private toolchain is:

```bash
PYTHONPATH=external/ESSO python3 -m ESSO validate \
  src/kernels/dex/global_settlement_core_v1.yaml
PYTHONPATH=external/ESSO python3 -m ESSO verify-multi \
  src/kernels/dex/global_settlement_core_v1.yaml \
  --solvers z3,cvc5 --determinism-trials 2 --timeout-ms 5000
```

Acceptance on that host means `validate` returns `ok: true` and
`verify-multi` returns `ok: true`, `determinism: true`, `report.verdict ==
"VERIFIED"`, `report.solvers_agreed == true`, `report.failed_queries == 0`,
and `report.inconclusive_queries == 0`. Until that replay is recorded, the
formal status of the YAML is `INCOMPLETE`. The test module encodes exactly
these checks and skips, rather than passes, when the toolchain is absent.

Bounded model sweeps executed by the test module:

- accept box: 21 asset-`a` states (every partition of at most two atoms over
  the five buckets) x 3 asset-`b` fixtures x 5 command kinds x 2 assets x 27
  parameter triples (`amount`, `fee_charged`, `fee_alloc` in `{0, 1, 2}`) =
  17,010 steps, current context, no violation;
- random box: seed `20260826`, 4,000 samples over the full declared domain,
  including unknown lanes, unknown commands, consumed occurrences, stale
  heights, missing authority, and the height horizon, no violation;
- every named mutant: first violation found inside the accept box.

Test design: every scenario test is Arrange, Act, Assert with exact
observables. Boundary cases cover zero amount, one atom, the payer balance at
the exact boundary and one atom short, the maximum neighbour (`3 + 1 = 4`)
and the overflow boundary (`4 + 1`), the `rest` partition reaching the width
exactly, the height horizon neighbour and the horizon, duplicate occurrence
and the last fresh identity, and stale replay identity in both directions.
Mutation tests follow RIPR: reach, infect, propagate, reveal. Direct
specification checks (`spec_failures`) are evaluated next to the YAML
invariants so a defect in the invariants and a defect in the transition are
both observable.

## Nonclaims and residual risk

- No production, settlement, release, or value-moving authority is granted or
  implied. No whole-DEX safety claim is made.
- No solver-backed verdict exists for the YAML. The ESSO toolchain is absent
  here; the two ESSO tests are skipped and recorded as `INCOMPLETE`.
- The executable bounded model is a pure-Python interpreter of an `esso-ir/v1`
  subset written for this task. Its assumptions about ESSO semantics
  (simultaneous updates over the pre-state, effects over the post-state,
  Euclidean `div` and `mod`) are taken from existing kernels and
  `tools/esso_gpu_semantics.py`; they are not verified against the private
  toolchain. Passing the interpreter does not establish that ESSO validates or
  verifies the file.
- The refinement between this model and the Python or Rust source is by
  inspection only. There is no theorem, simulation relation, generated
  reference, or parity vector.
- The bounded sweeps cover the stated boxes only. They are not exhaustive over
  the declared domain and are not a proof.
- The reject-code mapping to source codes is informative. The model neither
  proves nor claims the source's reject order.
- Fee percentages, burn floors, retained-supply rules, Oracle economics,
  margin rules, authority grants, route selection, and governance are not
  represented and remain unselected.
- Canonical bytes, roots, receipts, journals, routes, epochs, Oracle
  occurrences, the external outbox, migration, and durable publication are
  outside the model.
- The Test Hygiene Contract V1 requires a `THV1-*.json` evidence packet for
  changes under `tests/formal/**`. This task's write boundary is three files,
  so no packet was created and `tools/check_test_hygiene_v1.py` and
  `tools/run_test_hygiene_gate_v1.py` were not run. Creating that packet is an
  integrator action.
- The commit introducing these files is not pushed and is bound to no receipt;
  its hash lives outside these files. An independent Max review and a local
  replay of the Evidence commands are required before any downstream use.

## Next safest step

Replay the ESSO `validate` and `verify-multi` commands on a host with
`external/ESSO`, record the JSON payloads, and only then mark the formal
status of `global_settlement_core_v1.yaml` as verified. Keep the three-file
boundary until the integrator adds the test-hygiene packet. Do not derive
FCIS runtime code from this blueprint until the ESSO replay and the
independent review are recorded.
