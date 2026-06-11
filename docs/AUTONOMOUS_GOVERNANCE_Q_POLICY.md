# Autonomous Governance Q-Policy

`src/integration/autonomous_governance_q_policy.py` implements deterministic
autonomous parameter revision for the DEX.

See `docs/AUTONOMOUS_GOVERNANCE_ARCHITECTURE.md` for the Julia optimizer and
EBRM training architecture.

The live path is:

```text
oracle observation -> frozen Q-table lookup -> proposed parameter deltas -> revision_policy_v1 envelope packet
```

Q-learning can train or tune the table offline. Runtime execution uses only the
hash-bound table artifact, integer binning, integer Q scores, deterministic
tie-breaking, and the existing pointwise revision envelope.

The governance-surface mode uses the same table machinery, but evaluates the
proposed action against the concrete governance guard suite:

```text
oracle observation -> frozen Q-table lookup -> proposed fee/router/risk deltas -> gov_gate.py + Tau-verified governance specs
```

This mode covers swap fee, fee-router split, MCR/CCR, whale-defense
`staker_bps`, and perps funding-cap revisions.

The concrete governance-surface evaluator binds the trusted Python/Tau gate
functions when the runtime module is imported. Later monkeypatches or forged
wrappers of `gov_gate` do not change the final gate report; artifact source
manifests still record the verifier/runtime files so drift is explicit at
promotion time.

Cross-trajectory sessions are now explicit. A single trajectory bounds one
multi-step run; a session is the ordered sequence of such receipts. The session
continuation helper derives the next segment's carry-in from a fully reverified
parent receipt, and the session verifier replays the whole sequence under one
policy hash and one trajectory budget. That closes the operator reset path for
`trajectory_used`, anti-oscillation history, cooldown state, and
`previous_chain_head` inside the integration artifact path.

Surface evaluation can also bind the committed-state context with
`expected_committed_context_hash`. The hash covers the current surface state,
`current_epoch`, `proposal_epoch`, optional `last_update_epoch`,
`previous_approved_deltas`, and `trajectory_used`. A mismatch adds
`committed_context_hash_mismatch`, keeps `approved = false`, and makes
`commit_autonomous_governance_surface_q_policy_v1` return a deterministic no-op.
This is the integration hook that prevents a proposer or relay from choosing a
convenient `curr`/epoch anchor for the step gate.

Optimized policies may use `selection.mode = "first_admissible"`. In that mode
the table is a deterministic action ranking: the evaluator checks candidates in
score order and executes the first one accepted by the governance gates. A
policy without `selection.mode` uses the original `top_scored` behavior and
checks only the highest-score action.

Optimized policies may also enable `selection.anti_oscillation` for chosen
parameters. The evaluator then skips reversal candidates relative to the last
approved nonzero delta before running the exact gate check on the next ranked
candidate. This reduces fee/funding direction flips in multi-epoch replay.

Optimized policies may also enable `selection.trajectory_budget`. The runtime
then tracks absolute movement already used in the current governance trajectory
and skips candidates whose next delta would exceed a per-parameter movement
limit. The selected candidate still needs the exact governance gates. The budget
is a deterministic selection guard that prevents repeated small valid steps from
becoming an unbounded autonomous drift path.

Surface-mode policies can include governed values in `state_bins`, for example
`fee_bps`, `funding_cap_bps`, `buyburn_bps`, and `reserve_bps`. The evaluator
bins those values alongside oracle observations, so offline Julia layers can
rank edge-safe actions earlier while the exact governance gates still decide
whether a candidate executes.

The current optimized action set also includes compound liquidity-floor actions
that move fee, funding, and reserve routing together. These are deterministic
lookup-table candidates. A compound proposal executes only when the exact
surface gates accept every affected parameter.

The receipt reports each surface gate and also reports
`governance_surface_all_gates_ok`. The imported `master` gate is the composed
fee/router/collateral/whale subset from `gov_revision_master_v1`; funding-cap
acceptance is enforced by the separate `funding` surface bit and by
`governance_surface_all_gates_ok`.

For an actual autonomous step, use
`commit_autonomous_governance_surface_q_policy_v1` or the CLI `step` command.
That path evaluates the policy, recomputes the governance gates against the
committed surface state, and returns `applied_state = committed_state` on every
rejection. The receipt remains an audit artifact; `admitted` is the state
transition bit.

## Authority Boundary

The policy can automatically approve a governed parameter update when all of the
following hold:

- the policy hash matches the expected frozen artifact hash;
- oracle freshness, divergence, volatility, liquidity, pause, and cooldown
  checks pass;
- the selected table action is deterministic for the binned observation;
- every proposed parameter satisfies bounds and per-epoch step limits;
- tier and weight ordering constraints remain valid.
- in governance-surface mode, every reported surface gate is true.
- if a trajectory budget is supplied, the proposed absolute movement remains
  within that budget.

The receipt explicitly does not claim settlement authority, immutable rule
changes, oracle truth, or online Q-table training.

## Replay

Generate a sample evaluation bundle:

```bash
python3 tools/autonomous_governance_q_policy.py sample --output /tmp/autogov-q-bundle.json
```

Generate a governance-surface sample bundle:

```bash
python3 tools/autonomous_governance_q_policy.py sample --surface --output /tmp/autogov-surface-q-bundle.json
```

Generate a multi-step trajectory bundle:

```bash
python3 tools/autonomous_governance_q_policy.py sample --trajectory --output /tmp/autogov-trajectory-bundle.json
```

Generate a Julia-optimized frozen policy plus replay report:

```bash
python3 tools/autonomous_governance_policy_factory.py --out-dir /tmp/autogov-policy-factory
```

Validate a frozen policy and its evidence artifacts:

```bash
python3 tools/autonomous_governance_policy_factory.py \
  --check-policy /tmp/autogov-policy-factory/optimized_policy.frozen.json \
  --training-corpus /tmp/autogov-policy-factory/ebr_training_corpus.json \
  --optimizer-report /tmp/autogov-policy-factory/optimizer_report.json \
  --factory-report /tmp/autogov-policy-factory/policy_factory_report.json
```

The factory checker includes single-step replay, intra-bin stress replay,
safety-boundary sweep replay, paired safety-interaction replay,
surface-boundary sweep replay, safety lanes, negative controls,
action-gate diagnostics, and multi-epoch sequence replay.
Sequence replay applies only approved updates to the next state, so edge-invalid
proposals become explicit no-ops in the evidence report. The checker also reports
`safety_feasible_count`, `safety_blocked_count`, and `opportunity_miss_count`;
promotion requires zero missed opportunities among safety-feasible replay cases.
When a factory report is provided, the artifact gate also compares its recorded
source manifest with the current generator and verifier files, then checks that
its replay, coverage, training-summary, and promotion-gate sections match
recomputation.

`action_gate_diagnostics` checks the frozen action vocabulary itself. Every
listed action is applied to the canonical committed governance envelope and
rechecked against the exact fee, router, collateral, whale-defense, funding,
and master gates. Promotion requires that diagnostic to pass before any replay
or learned residual metric can support the artifact.

`environment_curriculum_diagnostics` checks the long-horizon replay suite as a
software training environment. It requires the multi-step governance scenarios
to cover state-changing approvals, calm holds, fail-closed no-op rejections,
safety interrupts, diverse bin paths, zero frontier regret, and safe final
states. This is the main lesson from the "software, not datasets" framing:
the autonomous policy improves through expert-designed replay environments, not
by merely increasing static row count.
The current checked environment contains ten long-horizon sequences and 127
steps, including trajectory-budget, trajectory-safety interruption, and router
budget-walk cases. The trajectory-safety interruption combines high-pressure
movement, four fail-closed safety no-ops, and later budget-edge holds in one
trajectory. The router budget walk spends the full permitted buyburn/reserve
movement budget toward reserve under liquidity stress. The router recovery walk
spends the same budget back toward buyback under healthy liquidity, then
verifies the remaining steps hold safely instead of chasing irrelevant actions.

The EBRM corpus summary now includes `ranking_diagnostics`. This replays the
frozen table as an action ranker against verifier-labeled candidate rows and
reports first-accepted verifier calls, best-utility regret, hard-negative score
margins, and verifier-call savings versus exhaustive action checking.
Promotion requires the optimized table to put an accepted best-utility action
first for every safety-feasible normal-grid scenario.

The sequence corpus records every candidate action at each long-horizon replay
step, using the current committed state at that point in the sequence. This
turns the multi-epoch evidence into training data for temporal ranking and
anti-oscillation behavior, rather than a log of only the selected action.
`sequence_ranking_diagnostics` reports the verifier calls needed to reach the
first accepted temporal candidate, zero-regret coverage against the sequence
frontier, and whether anti-oscillation blockers are represented as explicit
training negatives. Trajectory-budget blockers are represented the same way,
so repeated bounded movement becomes a learned hard-negative family without
becoming an execution authority.

The corpus summary also includes `pairwise_diagnostics`. This audits
candidate-complete normal-grid, intra-bin, safety-boundary,
safety-interaction, surface-boundary, and sequence-step groups as training
examples: the
highest-scored best-utility accepted action must outrank gate-rejected hard
negatives, best-utility accepted actions must outrank dominated accepted
actions, and anti-oscillation skips must appear as temporal hard-negative
pairs. These margins measure ranking quality only. The exact governance gates
still decide execution.

The intra-bin stress corpus records every candidate action for floor and
ceiling probe values inside each oracle bin. This gives the EBRM training set
examples where the binned state is identical but the raw observation is near a
bin boundary, which is where coarse lookup tables are most likely to hide
ranking or utility mistakes.

The safety-boundary sweep records every candidate action for 80 stratified
near-threshold scenarios across oracle freshness, divergence, volatility,
liquidity floor, and cooldown controls. Each probe has an inside-limit case
that must approve and an outside-limit case that must reject with the expected
error. The current corpus contributes 800 rows from this source, and promotion
requires 40/40 inside approvals, 40/40 outside rejections, and zero missing
expected errors.

The safety-interaction sweep records every candidate action for 160 paired
near-threshold scenarios. It crosses four anchor bins with all ten pairs of
freshness, divergence, volatility, liquidity, and cooldown controls, then tests
`both_inside`, `first_outside`, `second_outside`, and `both_outside` profiles.
The current corpus contributes 1,600 rows from this source, and promotion
requires 40/40 paired inside approvals, 120/120 paired outside rejections, and
zero missing expected errors.

The surface-boundary sweep records every candidate action for 12 exact
governance-surface edge scenarios: fee floor/cap, funding floor/cap, reserve
cap, and buyburn cap, each with just-inside and at-limit states. The selected
policy must approve all 12 states, the residual layer must report zero
`q_row_missing` errors, and forced candidate actions must still expose the
expected fee, funding, router, and master gate rejections at exact limits. The
current corpus contributes 120 rows from this source.

Every candidate-complete row also receives verifier-derived supervision fields:
`target_class`, `frontier_action_id`, `frontier_utility`,
`utility_regret_to_frontier`, `score_gap_to_frontier`, and
`rank_gap_to_frontier`. These fields support EBRM pairwise/listwise and
regret-weighted training without giving the model authority over execution.

The corpus summary also includes entropy-vs-energy diagnostics. Those metrics
compare frontier-vs-negative score gaps with candidate-pool breadth and report a
temperature-based verifier-call bound. The bound is an offline search-efficiency
claim; the exact governance gates still decide whether a candidate executes.

The same summary assigns deterministic group-level train/validation splits.
All candidate actions for one scenario stay in the same split, and validation
must still contain every source and target class. This gives future EBRM
training a held-out audit without changing runtime selection.

The summary also includes a feature contract. Each row carries a fixed numeric
`feature_vector` built from pre-decision context and action fields only:
source/action/probe ids, state bins, observation values, surface state, deltas,
policy score, and policy rank. Labels, errors, gate reports, frontier targets,
utilities, regrets, and split membership remain excluded from model inputs.

The summary also includes `diversity_diagnostics`. This checks unique
feature-vector coverage, duplicate concentration, candidate-group completeness,
target-class presence in both train and validation, and hard-negative
failure-family diversity. Promotion requires this to pass so the residual layer
is trained on a broad verifier-labeled frontier rather than repeated examples.
The current corpus snapshot contains 11,002 rows, 1,099 candidate groups, 1,270
sequence-step rows, 318 selection-blocked rows, and hard-negative families for
`trajectory_budget_exceeded:fee_bps` and
`trajectory_budget_exceeded:buyburn_bps`.

The factory also emits `ebr_residual_model.json`. This is a deterministic
train-split residual lookup model, represented as another bounded Q layer over
deviation, volatility, liquidity, fee, funding, buyburn, and reserve bins. The
layer is appended to the frozen policy only when validation keeps rank-1
frontier selection and improves non-frontier and hard-negative margins. The
deterministic gates still decide whether the selected candidate executes.
Unseen residual bin keys use a neutral `*` fallback row, so the base Q layers
decide instead of the residual layer producing `q_row_missing`. The residual
report still records the full effective grid size, currently 9,216 residual
keys, and the number of keys filled by the neutral fallback.
The current residual layer uses a wider bounded correction range (`score_clamp`
320, `score_scale` 2). It also applies a neutral-edge prior only to learned
rows where all actions otherwise collapse to zero because the train split saw
only equal no-accept targets. The prior penalizes actions that push fee,
funding, buyburn, or reserve farther into a coarse cap/floor bin. In the checked
artifact this raises held-out residual pairwise accuracy to 0.988898 and
residual hard-negative accuracy to 1.0 while the hybrid scorer keeps held-out
frontier rank-1 coverage and hard-negative accuracy at 1.0.
The residual report also reruns the same check over seven salted group-level
splits, so a single lucky train/validation partition is not enough to promote
the layer.

The normal-grid, intra-bin, safety-boundary, safety-interaction,
surface-boundary, and long-horizon checkers also compute finite-action
frontiers or exact-limit candidate evidence by forcing every candidate action
through the exact gates and comparing realized replay utility or expected gate
rejections.
First-admissible runtime accounting separates exact gate checks from deterministic
selection screens. `candidate_checked_count_total` counts candidates that reached
the governance gate suite, `selection_screened_count_total` counts candidates
skipped by anti-oscillation or trajectory-budget guards during the ranked scan,
and `selection_penalized_count_total` counts blocked raw candidates moved behind
selection-feasible candidates by deterministic selection-aware scoring.
`candidate_considered_count_total` counts candidates actually scanned by
first-admissible selection. `fallback_used_count` counts only moves past the
first selection-feasible candidate after exact gate evaluation.
Long-horizon frontier checks include the same anti-oscillation rule used by
runtime selection. Promotion requires zero optimized-policy frontier regret
under the current finite action set and replay utility metric. The same report
compares optimized utility against hold-only and PID-shaped baselines in both
normal-grid and long-horizon replay. The PID-shaped baseline uses fixed
observation-bin rules plus the same deterministic state-edge guards.
For the current checked artifact, long-horizon replay reports 11,380 optimized
utility, 11,380 frontier utility, zero regret, 116 approved steps, 11 rejected
steps, 116 exact gate checks, 48 deterministic selection-blocked raw candidates
penalized before scanning, zero gate fallbacks, and no trajectory-budget
failures. Hold-only scores 1,440 utility with 12,040 regret; the PID-shaped
baseline scores 11,280 utility with 130 regret.

Evaluate it:

```bash
python3 tools/autonomous_governance_q_policy.py evaluate /tmp/autogov-q-bundle.json
```

Evaluate and apply one governance-surface step:

```bash
python3 tools/autonomous_governance_q_policy.py step /tmp/autogov-surface-q-bundle.json
```

Run a multi-step trajectory and independently verify the receipt:

```bash
python3 tools/autonomous_governance_q_policy.py trajectory /tmp/autogov-trajectory-bundle.json > /tmp/autogov-trajectory-receipt.json
python3 - <<'PY'
import json
bundle = json.load(open("/tmp/autogov-trajectory-bundle.json"))
receipt = json.load(open("/tmp/autogov-trajectory-receipt.json"))
json.dump({"policy": bundle["policy"], "trajectory_receipt": receipt}, open("/tmp/autogov-trajectory-verify-bundle.json", "w"), sort_keys=True)
PY
python3 tools/autonomous_governance_q_policy.py verify-trajectory /tmp/autogov-trajectory-verify-bundle.json
```

Run the stricter client-side refuse-loop, binding the external policy pin and
expected state anchors:

```bash
python3 - <<'PY'
import json
bundle = json.load(open("/tmp/autogov-trajectory-bundle.json"))
receipt = json.load(open("/tmp/autogov-trajectory-receipt.json"))
json.dump(
    {
        "policy": bundle["policy"],
        "trajectory_receipt": receipt,
        "expected_policy_hash": bundle["expected_policy_hash"],
        "expected_initial_state": bundle["initial_surface_state"],
        "expected_final_state": receipt["final_state"],
    },
    open("/tmp/autogov-trajectory-admit-bundle.json", "w"),
    sort_keys=True,
)
PY
python3 tools/autonomous_governance_q_policy.py admit-trajectory /tmp/autogov-trajectory-admit-bundle.json
```

Continue a trajectory session from the verified parent receipt:

```bash
python3 - <<'PY'
import json
bundle = json.load(open("/tmp/autogov-trajectory-bundle.json"))
receipt = json.load(open("/tmp/autogov-trajectory-receipt.json"))
steps = [
    {
        "observation": bundle["steps"][0]["observation"],
        "current_epoch": 175,
        "proposal_epoch": 151,
    }
]
json.dump(
    {
        "policy": bundle["policy"],
        "previous_receipt": receipt,
        "steps": steps,
        "expected_policy_hash": bundle["expected_policy_hash"],
    },
    open("/tmp/autogov-trajectory-continue-bundle.json", "w"),
    sort_keys=True,
)
PY
python3 tools/autonomous_governance_q_policy.py continue-trajectory /tmp/autogov-trajectory-continue-bundle.json > /tmp/autogov-trajectory-child.json
```

Verify the ordered session:

```bash
python3 - <<'PY'
import json
bundle = json.load(open("/tmp/autogov-trajectory-bundle.json"))
parent = json.load(open("/tmp/autogov-trajectory-receipt.json"))
child = json.load(open("/tmp/autogov-trajectory-child.json"))
json.dump(
    {
        "policy": bundle["policy"],
        "trajectory_receipts": [parent, child],
        "expected_policy_hash": bundle["expected_policy_hash"],
    },
    open("/tmp/autogov-session-verify-bundle.json", "w"),
    sort_keys=True,
)
PY
python3 tools/autonomous_governance_q_policy.py verify-session /tmp/autogov-session-verify-bundle.json
```

Exit code `0` means the autonomous revision packet is approved. Exit code `2`
means it was rejected fail-closed. Exit code `3` means the input could not be
evaluated.

For `step`, exit code `0` means the commit loop produced a deterministic
decision. Inspect `admitted` to distinguish an applied revision from a no-op.

For `trajectory`, the runner owns the cross-step state that is easy for callers
to forget: applied surface state, `trajectory_used`,
`previous_approved_deltas`, and `last_update_epoch`. Every internal single-step
call is supplied with an `expected_committed_context_hash`; the final
hash-chained receipt is verified by replay through
`verify_autonomous_governance_surface_trajectory_v1`.
`admit_verified_autonomous_governance_surface_trajectory_v1` is the
client-facing refuse-loop. It requires successful replay verification,
`trajectory_ok`, completed status, all invariant flags true, the external policy
hash to match the policy and receipt pins, and any caller-supplied state or
previous-chain anchors to match.

For cross-trajectory operation, use
`continue_autonomous_governance_surface_trajectory_v1` instead of hand-supplying
carry fields to `run_autonomous_governance_surface_trajectory_v1`. It rechecks
the parent receipt and copies only the parent's verified final state,
`trajectory_used_final`, `previous_approved_deltas_final`,
`last_update_epoch_final`, `trajectory_budget`, and `chain_head` into the child
run. `verify_autonomous_governance_surface_session_v1` then checks the ordered
receipt list independently, including fresh genesis, exact boundary carry,
policy-hash consistency, budget consistency, strictly increasing boundary
epochs, completed statuses, drift conservation, and monotone session usage.

## Design Notes

Layered lookup tables keep the state space explicit. Each layer maps a small set
of binned features to action scores. Runtime sums scores across layers and
selects the highest-scoring action, with action-list order as the deterministic
tie-breaker. In `first_admissible` mode, that same order becomes the candidate
check order for the exact gates.

Selection-aware ranking is a deterministic pre-scan adjustment over that same
ranked action list. The runtime computes anti-oscillation and trajectory-budget
failures for every raw-ranked action, then subtracts a fixed blocker penalty
from those actions before first-admissible scanning. A penalized action remains
auditable through `candidate_search.selection_penalized_candidates`, while an
action that still appears during the adjusted scan is reported through
`candidate_search.selection_screened_candidates`. Exact gate failures remain in
`candidate_search.rejected_candidates`.

The v9 selection-aware ranker changed only runtime ordering and replay
accounting. It did not change the frozen Q table, residual model, exact
governance gates, Tau specs, or the candidate action set. The important code
paths are:

- `src/integration/autonomous_governance_q_policy.py`: applies the blocker
  penalty before first-admissible selection and emits the candidate-search
  counters.
- `src/integration/autonomous_governance_trajectory.py`: owns multi-step
  trajectory threading, context hashes, receipt chains, and independent replay
  verification.
- `src/integration/autonomous_governance_session.py`: owns cross-trajectory
  continuation and whole-session verification, so the movement budget and
  cooldown state cannot be reset at a receipt boundary inside the integration
  artifact path.
- `tools/autonomous_governance_policy_factory.py`: aggregates
  `selection_penalized_count_total` alongside exact gate checks and scanned
  candidates.
- `tools/autonomous_governance_q_policy.py`: exposes `trajectory`,
  `continue-trajectory`, `verify-trajectory`, `admit-trajectory`, and
  `verify-session` for replay and client admission checks.
- `tests/integration/test_autonomous_governance_q_policy.py`: checks that
  anti-oscillation and trajectory-budget blockers are penalized before gate
  scanning.
- `tests/tools/test_autonomous_governance_q_table_optimizer.py`: fixes the
  artifact-level replay expectations for the generated policy.

For developers reading replay reports, use these counters as separate facts:

- `candidate_checked_count_total`: candidates that reached exact governance
  gates.
- `selection_penalized_count_total`: raw-ranked candidates moved behind
  feasible actions by deterministic selection-aware scoring.
- `selection_screened_count_total`: blocked candidates encountered during the
  adjusted scan.
- `candidate_considered_count_total`: candidates actually scanned by
  first-admissible selection.
- `fallback_used_count`: cases that moved past the first selection-feasible
  candidate after exact gate evaluation.

The table can learn richer behavior than a PID controller while still compiling
to deterministic decision rules. The exact revision envelope remains the release
bar for autonomous execution.

PID is optional. A PID-derived pressure score can be a feature or a baseline
layer, but the primary autonomous policy should be the frozen table plus the
verified governance gates.
