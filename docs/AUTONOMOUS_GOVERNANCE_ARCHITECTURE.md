# Autonomous Governance Architecture

This design makes governance autonomous inside a bounded, verified envelope. The
learned or optimized component chooses candidate actions. The deterministic
governance gates decide whether the action can execute.

## Control Path

```text
oracle/state snapshot
  -> feature extraction and binning
  -> frozen Q-policy lookup or ranked candidate list
  -> proposed governance deltas
  -> Python/Tau governance gates
  -> approved receipt or fail-closed rejection
  -> commit step: apply approved proposal, otherwise no-op
```

Runtime execution uses the frozen policy artifact only. It does not call Julia,
train online, sample probabilistically, or use an energy score as an acceptance
predicate.

The authority contract is:

```text
QPolicy(state) = candidate_action or ranked_candidate_actions
GovernanceGates(state, candidate_action) = admissible?
Commit(state, candidate_action) = proposed_state if admissible else state
```

The first line is optimization. The gate and commit lines are authority.
The commit step binds `state` to the committed governance state, recomputes the
surface gates against the proposed state, and returns the unchanged state on any
receipt, safety, hash, or gate rejection.

The runtime evaluator binds the trusted governance gate functions at import
time, and the factory source manifest records the verifier/runtime files. A
later forged wrapper of `gov_gate` cannot become the authority for admission
without changing the trusted source set.

## What Julia Does

Julia is useful offline because the action/state space is bounded and mostly
integer-valued. The optimizer in
`tools/autonomous_governance_q_table_optimize.jl` enumerates the bin space:

```text
deviation_bin x volatility_bin x liquidity_bin
```

For each state bin, it scores every candidate governance action with an integer
energy:

```text
E(action, state)
  = hard_gate_penalty
  + target_miss
  + churn
  + overcontrol
  + ebrm_prior
```

Then it writes a Q-table where:

```text
Q(state_bin, action) := -E(action, state_bin)
```

The runtime evaluator selects the highest Q score. This means Julia can search
for the best table entries without becoming part of the live governance path.

The optimized artifact includes both oracle bins and surface-state bins. The
oracle layer scores pressure from deviation, volatility, and liquidity. Surface
edge layers then adjust the ranking near `fee_bps`, `funding_cap_bps`,
`buyburn_bps`, and `reserve_bps` boundaries so obviously edge-safe actions rank
ahead of proposals that the exact gates would reject.

The current artifact uses 10 bounded actions. Alongside single-parameter fee,
funding, and router moves, it includes compound actions for liquidity-floor
stress:

```text
raise_fee_10_shift_router_to_reserve_100
raise_fee_10_tighten_funding_5_shift_router_to_reserve_100
lower_fee_10_relax_funding_5_shift_router_to_reserve_100
```

Those compound actions are still ordinary candidates. The exact gates decide
whether the whole proposed delta is admissible.

Optimized policies may set:

```json
{"selection": {"mode": "first_admissible"}}
```

In that mode the Q table ranks candidate actions, and the runtime checks them
in deterministic score order until the governance gates accept one. If no
candidate is admissible, the receipt stays rejected. Existing policies without
that field use the stricter `top_scored` behavior, where only the highest-score
action is checked for execution.

Optimized policies may also add a deterministic anti-oscillation filter:

```json
{
  "selection": {
    "mode": "first_admissible",
    "anti_oscillation": {
      "enabled": true,
      "parameters": ["fee_bps", "funding_cap_bps"]
    }
  }
}
```

The filter skips a candidate when its delta reverses the last approved nonzero
delta for a listed parameter. It is a selection rule, not an authority rule. The
remaining candidate still needs the exact governance gates to approve it.

Optimized policies may also add a deterministic trajectory budget:

```json
{
  "selection": {
    "mode": "first_admissible",
    "trajectory_budget": {
      "enabled": true,
      "limits": {"fee_bps": 250, "funding_cap_bps": 125}
    }
  }
}
```

The runtime tracks absolute movement already used in the current trajectory and
skips ranked candidates that would exceed a configured per-parameter budget.
This prevents repeated small admissible moves from accumulating into an
unbounded autonomous path. Budget skips are training negatives and audit
signals; the exact gates still decide the candidate that remains.

The current optimizer is a deterministic hand-energy baseline. A learned EBRM
can replace or augment `ebrm_prior` after it is trained and audited.

## EBRM Role

EBRM means an energy-based reasoning model over structured governance states
and candidate actions:

```text
E_theta(context, action)
  = hard_constraint_terms(context, action)
  + soft_objective_terms(context, action)
  + learned_residual_theta(context, action)
```

Lower energy means the action should be checked earlier or receive a higher
lookup-table score. It does not mean the action is allowed.

Good EBRM training labels come from replay and exact gates:

```text
label(context, action) := GovernanceGates(context, action)
```

Useful training objectives:

- pairwise ranking: admissible and useful actions rank above invalid or noisy
  actions;
- listwise ranking: the best action for a state bin ranks first;
- hard-negative mining: actions just outside fee, funding, timelock, router, or
  collateral bounds get strong separation;
- churn calibration: unnecessary parameter movement is penalized in calm
  states;
- regime coverage: train across volatility, liquidity, oracle freshness, and
  parameter-edge regimes.

## Lookup Table Generation

The production-candidate artifact is a frozen JSON policy:

```text
{
  "schema": "zenodex.autonomous_governance.q_policy.v1",
  "policy_id": "...",
  "state_bins": {...},
  "actions": [...],
  "q_layers": [...]
}
```

The policy hash is computed by the Python integration layer. Governance
execution should pin the expected hash. A hash mismatch rejects fail-closed.

The table can be generated in stages:

1. hand-energy Julia baseline;
2. replay-labeled EBRM residual;
3. cross-seed stress reports;
4. frozen policy artifact;
5. action-vocabulary gate diagnostics;
6. Python/Tau gate replay;
7. production promotion only after evidence gates pass.

The current factory command is:

```bash
python3 tools/autonomous_governance_policy_factory.py \
  --out-dir runs/autonomous_governance_policy_factory/latest
```

It writes:

```text
optimized_policy.raw.json
optimized_policy.frozen.json
optimizer_report.json
ebr_training_corpus.json
ebr_residual_model.json
policy_factory_report.json
```

The frozen policy includes the Python-computed `policy_hash`. The factory
report replays the optimized policy, a hold-only baseline, and a deterministic
PID-shaped baseline over the same stress grid and long-horizon sequence suite.
It also checks every frozen action from the canonical committed governance
envelope. This catches action-vocabulary drift directly: each action must fit
the pointwise Python/Tau gate suite before the artifact is promotable.

Validate an existing artifact without rerunning Julia:

```bash
python3 tools/autonomous_governance_policy_factory.py \
  --check-policy runs/autonomous_governance_policy_factory/latest/optimized_policy.frozen.json \
  --training-corpus runs/autonomous_governance_policy_factory/latest/ebr_training_corpus.json \
  --optimizer-report runs/autonomous_governance_policy_factory/latest/optimizer_report.json \
  --factory-report runs/autonomous_governance_policy_factory/latest/policy_factory_report.json \
  --report-output runs/autonomous_governance_policy_factory/latest/policy_artifact_check.json
```

The checker recomputes the policy hash, replay grid, safety lanes, negative
controls, action-gate diagnostics, surface-boundary sweep, long-horizon
sequences, coverage profile, and EBRM training labels from the files on disk.
It also compares the factory report's recorded source manifest, replay block,
coverage profile, training summary, and promotion gate against the current
recomputation. Promotion fails if the embedded `policy_hash` no longer matches
the policy content, even when replay under the recomputed hash would pass.

The training summary also includes EBRM ranking diagnostics over the full
normal-grid candidate corpus. For each scenario it ranks the frozen table's
candidate actions, then compares that order with verifier labels and replay
utility. The promotion gate requires rank-1 acceptance on all safety-feasible
normal-grid cases, zero best-utility regret, and positive hard-negative score
margins. These are evidence about search efficiency and training quality; they
do not authorize execution.

The intra-bin stress corpus is also candidate-complete. For every oracle bin and
surface-state bin, the factory probes representative floor and ceiling values
inside the same discrete bin. This catches policies that look correct at the
coarse bin representative but fail or lose utility near the bin edge.

The safety-boundary sweep is candidate-complete too. It anchors eight
representative state bins and probes five runtime controls exactly at and just
outside the limit: freshness, divergence, volatility, liquidity floor, and
cooldown. The current sweep has 80 scenarios and 800 candidate rows. Promotion
requires all 40 inside-limit scenarios to approve, all 40 outside-limit
scenarios to reject, and every outside case to report its expected error.

The safety-interaction sweep adds paired runtime-control coverage. It anchors
four representative state bins, enumerates all ten pairs of freshness,
divergence, volatility, liquidity, and cooldown controls, and tests
`both_inside`, `first_outside`, `second_outside`, and `both_outside` profiles.
The current sweep has 160 scenarios and 1,600 candidate rows. Promotion
requires all 40 paired inside-limit scenarios to approve, all 120 paired
outside-limit scenarios to reject, and every outside case to report its
expected errors.

The long-horizon portion of the training corpus is candidate-complete. For each
sequence step, the factory records every available action under the current
committed state, not only the action selected by the policy. Anti-oscillation
skips become labeled hard negatives with `anti_oscillation:*` failure families,
so an EBRM can learn the temporal selection rule from replay labels instead of
seeing only the winning trace.

The sequence-ranking diagnostic then audits those temporal rows. It checks that
each accepted sequence step reaches a best-utility candidate on the first
verifier call after deterministic selection filters, that temporal regret is
zero, and that blocked reversal candidates are present as training negatives.

The pairwise diagnostic audits the corpus as a training set. For every
candidate-complete normal-grid, intra-bin, safety-boundary,
safety-interaction, or sequence-step group, it checks that a highest-scored
best-utility accepted action outranks gate-rejected hard negatives, that
best-utility accepted actions outrank dominated accepted actions, and that
anti-oscillation hard-negative pairs are represented. This is evidence about
EBRM ranking quality and hard-negative curriculum coverage. It does not create
an acceptance rule.

Each candidate-complete row also carries verifier-derived supervision targets:
`target_class`, `frontier_action_id`, `frontier_utility`,
`utility_regret_to_frontier`, `score_gap_to_frontier`, and
`rank_gap_to_frontier`. These fields make the EBRM training set directly useful
for pairwise, listwise, and regret-weighted objectives. They are labels for
offline training only. The runtime still checks the selected candidate against
the deterministic gates.

The entropy diagnostic audits whether the Q/energy gaps are large enough for
the size of the candidate pool. It reports actual verifier calls to the first
frontier action, score-margin tails, hard-negative entropy mass, and a
temperature-based call bound. This turns the EBRM evidence into a search-cost
claim:

```text
larger frontier-vs-negative gap -> lower expected verifier-call mass
```

The current promotion gate requires the diagnostic to pass, including
nonnegative non-frontier margins, positive hard-negative margins, finite entropy
mass, and a mean call bound below exhaustive checking.

The corpus also assigns a deterministic group-level train/validation split.
Every action row for the same scenario stays in the same split, so a learned
EBRM residual can train on complete candidate groups while held-out groups still
cover every source and target class. The validation report checks frontier-call
count, no-accept coverage, hard-negative margins, and entropy call bounds on the
held-out side.

The feature-contract diagnostic attaches a fixed numeric `feature_vector` to
each row and audits that it uses only pre-decision context and action fields:
source id, action id, probe id, state bins, raw observation, surface state,
deltas, policy score, and policy rank. Verifier labels, errors, gate reports,
frontier targets, regrets, utilities, and split membership remain outside the
feature vector. This gives future EBRM training a stable input schema without
letting training labels leak into model inputs.

The diversity diagnostic checks that the training set is not mostly repeated
prototypes. It reports unique feature-vector coverage, duplicate concentration,
target-class presence across train and validation, per-source vector diversity,
candidate-group completeness, and hard-negative failure-family diversity. This
keeps the residual lookup training honest about breadth before any learned layer
can affect candidate ordering.

The environment-curriculum diagnostic treats the long-horizon replay suite as
the training environment. It checks that required sequences are present,
multi-step, and diverse; that approved steps change state; that calm holds and
fail-closed no-ops both occur; that the safety-interrupt sequence has mixed
approved and rejected outcomes; and that final states remain inside the
governance envelope. This is the environment-quality gate for autonomous
training, separate from static corpus row count.

The factory then trains a deterministic residual lookup layer from the train
split of that corpus. The layer uses binned observation and surface-state
features to add bounded action-score corrections on top of the Julia hand-energy
table. It is applied only when held-out diagnostics show that the hybrid scorer
keeps rank-1 frontier coverage and improves non-frontier and hard-negative
margins. After the layer is appended, the normal replay, intra-bin replay,
long-horizon replay, safety lanes, negative controls, corpus checks, and
promotion gate are recomputed against the residual-augmented frozen policy.
The residual layer materializes learned rows plus a neutral `*` fallback row for
unseen residual-bin keys. That keeps the runtime fail-closed behavior for
malformed required layers, while valid untrained residual states contribute
zero learned preference and fall back to the base Q layers.
The current promoted residual uses `score_clamp` 320 and `score_scale` 2. It
also applies a neutral-edge prior only to learned rows where every action would
otherwise receive zero residual after mean-centering. The prior penalizes
actions that push fee, funding, buyburn, or reserve farther into a coarse
cap/floor bin. On the held-out split it raises residual-alone pairwise accuracy
to 0.988898 and residual hard-negative accuracy to 1.0; the hybrid policy
retains frontier rank-1 coverage and hard-negative accuracy at 1.0.
Selection-blocked entropy is reported separately from verifier-call entropy
because runtime trajectory filters screen those candidates before exact gate
evaluation. Replay reports therefore separate `candidate_checked_count_total`
for exact gate checks from `selection_screened_count_total` for cheap
deterministic anti-oscillation or trajectory-budget screens, while
`candidate_considered_count_total` preserves the full ranked-action audit
width. `fallback_used_count` is reserved for moving past the first
selection-feasible candidate after exact gate evaluation.
The residual artifact also runs seven salted group-level train/validation
splits. Every alternate split must keep frontier candidates at rank 1, improve
held-out p50 separation, and retain positive hard-negative margins before the
residual is considered promotable.

## Replay Stress Grid

The factory stress grid covers:

```text
4 deviation bins x 4 volatility bins x 3 liquidity bins x 5 surface states = 240 scenarios
```

The five surface states are:

- base parameters;
- fee near the cap;
- funding cap near the floor;
- router split near a reserve edge;
- combined fee/funding/router edge.

The factory also runs an intra-bin stress grid:

```text
48 oracle bins x 5 surface states x 2 probe profiles = 480 scenarios
```

The two probe profiles use the floor and ceiling values inside each binned
observation. Promotion requires every observed bin to match the intended bin,
both probe profiles to appear, every safety-feasible intra-bin case to approve,
and optimized intra-bin frontier regret to stay zero.

The factory also runs a safety-boundary sweep:

```text
8 anchor bins x 5 safety controls x 2 inside/outside probes = 80 scenarios
```

The five controls are oracle freshness, oracle divergence, volatility,
liquidity depth, and cooldown. Inside probes sit exactly at the limit and must
approve when the candidate is otherwise admissible. Outside probes cross the
limit by one deterministic step and must reject with the expected error.

The factory also runs a paired safety-interaction sweep:

```text
4 anchor bins x 10 control pairs x 4 inside/outside profiles = 160 scenarios
```

The four profiles are `both_inside`, `first_outside`, `second_outside`, and
`both_outside`. This checks that the policy still admits safe paired boundary
states while rejecting every one-control or two-control violation with the
expected fail-closed reason.

The factory also runs a surface-boundary sweep:

```text
12 fee/funding/router cap-floor scenarios x 10 candidate actions = 120 training rows
```

It covers fee floor/cap, funding floor/cap, reserve cap, and buyburn cap with
just-inside and at-limit states. The selected policy must approve all 12 safe
surface states, report zero `q_row_missing` errors from the residual layer, and
still expose expected fee, funding, router, and master gate rejections when
each candidate action is forced through the exact surface gate.

The promotion gate currently requires:

- optimizer success;
- policy hash present;
- every frozen action is gate-admissible from the canonical committed envelope;
- environment-curriculum diagnostics pass: long-horizon replay covers the
  required multi-step regimes, state transitions, holds, fail-closed no-ops,
  and safety interrupts;
- all 48 state bins covered;
- non-empty stress grid;
- zero invalid accepts;
- zero inconsistent accepts;
- all unsafe safety lanes reject;
- every unsafe safety lane reports its expected fail-closed reason;
- all adversarial negative-control policies reject;
- every negative-control policy reports its expected surface error;
- all required long-horizon sequence cases are present;
- all safety-feasible normal-grid scenarios approve some admissible action;
- all safety-feasible long-horizon steps approve some admissible action;
- optimized normal-grid replay has zero finite-action frontier regret;
- optimized intra-bin replay has zero finite-action frontier regret;
- safety-boundary sweep approves all inside-limit cases and rejects all
  outside-limit cases with expected errors;
- safety-boundary sweep covers every required probe profile and anchor bin;
- safety-interaction sweep approves all paired inside-limit cases and rejects
  all paired outside-limit cases with expected errors;
- safety-interaction sweep covers every required profile, control pair, and
  anchor bin;
- surface-boundary sweep approves every exact safe surface state, has zero
  residual `q_row_missing` errors, and observes expected fee, funding, router,
  and master gate rejections among forced candidates;
- surface-boundary sweep covers every required cap/floor profile;
- optimized long-horizon replay has zero finite-action frontier regret;
- intra-bin stress covers every state bin and required probe profile;
- intra-bin stress has zero invalid or inconsistent accepts;
- long-horizon sequence replay has zero invalid accepts;
- long-horizon sequence replay has zero inconsistent approved receipts;
- long-horizon final states remain inside the governance envelope;
- long-horizon cumulative drift stays within explicit per-parameter limits;
- coverage profile is complete;
- EBRM training corpus is complete;
- EBRM ranking diagnostics pass: first accepted action at rank 1, zero
  best-utility regret, and positive hard-negative margins;
- EBRM sequence-ranking diagnostics pass: first verifier-checked temporal
  candidate is best-utility, with anti-oscillation hard negatives present;
- EBRM pairwise diagnostics pass: best accepted actions outrank gate-rejected
  hard negatives, best-utility actions outrank dominated accepted actions, and
  temporal blocker pairs are present;
- EBRM supervision targets are present on every row, with frontier, dominated,
  gate-rejected, no-accept, selection-blocked, safety-lane, and negative-control
  target classes represented;
- EBRM entropy diagnostics pass: the frontier action is reached on the first
  verifier call, hard-negative margins are positive, entropy mass is finite, and
  the mean call bound is below exhaustive checking;
- EBRM train/validation split diagnostics pass: no group leakage, all target
  classes and corpus sources appear in validation, and held-out hard-negative
  margins remain positive;
- EBRM feature-contract diagnostics pass: every row has a fixed numeric
  pre-decision feature vector, with no label, gate, error, utility, frontier, or
  split fields in the feature schema;
- EBRM diversity diagnostics pass: unique feature-vector coverage is high,
  duplicate concentration is bounded, every target class appears in train and
  validation, and hard-negative families remain diverse;
- trained residual lookup diagnostics pass before the residual layer is applied
  to the frozen policy, cross-seed residual diagnostics pass, and all
  deterministic replay gates pass afterward;
- optimized replay utility greater than hold-only replay utility;
- optimized replay utility at least as high as the PID-shaped baseline;
- optimized long-horizon utility greater than hold-only long-horizon utility;
- optimized long-horizon utility at least as high as the PID-shaped
  long-horizon baseline;
- long-horizon cumulative drift and trajectory movement remain within limits;
- complete source manifest.

This is a release-candidate screen for the artifact. It is still a bounded
replay check, not a proof of global market optimality.

Replay utility is a comparison metric only. It rewards approved realized
parameter movement in stressed regimes and calm holds in low-stress regimes. It
scores the resulting proposal, not just the action name, and only gives the
extra funding-tightening reward when the resulting funding cap keeps the soft
retained floor. It is never an acceptance predicate.

The safety lanes are explicit fail-closed checks for:

- stale oracle data;
- excessive oracle divergence;
- excessive volatility;
- cooldown not elapsed;
- timelock not met;
- policy hash mismatch.

These lanes are scored only by rejection and expected error coverage. Utility
does not compensate for a safety-lane approval.

The factory also reports an opportunity profile. A replay step is
`safety_feasible` when the policy safety settings and current surface state do
not already require rejection. Since `hold` is always gate-admissible for a
valid surface state, a safety-feasible step should approve at least one
candidate. The promotion gate requires `opportunity_miss_count == 0` for both
normal-grid replay and long-horizon replay.

The normal-grid, intra-bin, and long-horizon replays also report finite-action
frontiers. For each step the factory forces each action through the exact
evaluator, computes the replay utility of every admissible action, and records
the best attainable utility within the frozen action set. The sequence frontier
also applies the same anti-oscillation and trajectory-budget rules used by
runtime selection. Promotion requires `frontier_regret_total == 0` for the
optimized policy in normal-grid, intra-bin, and long-horizon replay, so the
table must match the best finite-action utility under the current replay
metric.

The PID-shaped baseline is a deterministic controller encoded in the same Q
schema. Its joint observation layer maps deviation, volatility, and liquidity
bins to fixed actions, while state-edge guard layers keep the same fee, funding,
and router envelope awareness. This makes the comparison about action choice
under the same deterministic admission gates.
On the current checked long-horizon replay, hold-only scores 1,440 utility with
12,040 regret, the PID-shaped baseline scores 11,280 utility with 130 regret,
and the optimized Q/EBRM policy scores 11,380 utility with zero regret.

The long-horizon replay simulates repeated autonomous updates across ten
multi-epoch cases:

- persistent high deviation;
- calm pressure near the fee floor;
- router pressure near a router-share edge;
- alternating high/calm pressure;
- funding-cap pressure near the floor;
- a safety-interrupted sequence with stale and divergent oracle steps;
- a trajectory-budget walk that spends the fee movement budget and then holds;
- a trajectory-safety interruption sequence with liquidity, freshness,
  divergence, and volatility no-op rejections before the budget edge;
- a router-budget walk that spends the full buyburn/reserve trajectory budget
  toward reserve under stressed liquidity and then holds;
- a router-recovery walk that spends the full buyburn/reserve trajectory budget
  back toward buyback under healthy liquidity and then holds.

The sequence gate checks every accepted step, applies only approved proposals to
the next state, and records rejections as no-ops. Promotion requires safe final
states, bounded cumulative drift, and bounded absolute trajectory movement.
Sequence rejections are reported because they reveal policy inefficiency at
parameter edges, but rejection itself is a safe fail-closed outcome.

The current optimized artifact uses surface edge layers, `first_admissible`, and
anti-oscillation for `fee_bps` and `funding_cap_bps`, plus trajectory movement
limits. Edge-aware ranking makes many edge cases select `hold` or a valid
alternative as the first candidate instead of relying on fallback, and
alternating high/calm pressure no longer flips fee/funding direction every step.
The report records `fallback_used_count`, `candidate_checked_count_total`,
`selection_screened_count_total`, `candidate_considered_count_total`,
`oscillation_count`, `max_trajectory_budget_used`, and
`trajectory_budget_failures` to make that behavior auditable. In the current
checked artifact, long-horizon replay covers 127 steps, approves 116, rejects
11, performs 116 exact gate checks plus 48 deterministic selection screens,
uses zero gate fallbacks, scores 11,380 utility against an 11,380 frontier,
spends the full 1,000 bps
buyburn/reserve router trajectory budget in both the router-budget and
router-recovery walks, and reports zero regret.

The negative controls deliberately force bad policies through the same runtime
evaluator:

- fee step above `50` bps;
- fee above the `1000` bps cap;
- funding-cap underflow;
- router split sum break;
- collateral order/step break;
- whale-defense step above `500` bps.

The promotion report must show that each control rejects and names the expected
surface gate. These controls prove the exact gates still dominate the optimized
lookup table and any EBRM prior used to generate it.

The coverage profile makes the replay evidence explicit. It requires:

- every normal-grid state bin to appear;
- every state bin to have all five surface variants;
- every intra-bin stress state bin to appear;
- every intra-bin stress probe profile to appear;
- every safety-boundary probe profile to appear;
- every safety-boundary anchor bin to appear;
- every safety-interaction profile to appear;
- every safety-interaction control pair to appear;
- every safety-interaction anchor bin to appear;
- every safety lane id to appear;
- every negative-control id to appear;
- every long-horizon sequence id to appear;
- every required rejection family to appear at least once.

The required rejection families currently include fee, router, collateral,
whale, funding, master-composition rejection, trajectory-budget exhaustion,
stale oracle, divergence, volatility, liquidity depth below minimum, cooldown,
and policy-hash mismatch.

## EBRM Training Corpus

The factory also writes `ebr_training_corpus.json`. This file is for offline
model training only. It contains verifier-labeled rows from:

- every normal-grid scenario crossed with every candidate action;
- every intra-bin stress scenario crossed with every candidate action;
- every safety-boundary sweep scenario crossed with every candidate action;
- every safety-interaction sweep scenario crossed with every candidate action;
- every surface-boundary sweep scenario crossed with every candidate action;
- every unsafe safety lane;
- every adversarial negative control;
- every candidate action at every long-horizon sequence step.

Each row records the source, scenario id, action id, deltas, accepted/rejected
label, gate report, errors, failure family, and replay utility. The labels come
from the same deterministic evaluator used by the promotion report.

The current corpus check requires:

- all normal-grid action candidates are present;
- all intra-bin stress action candidates are present;
- all safety-boundary sweep action candidates are present;
- all safety-interaction sweep action candidates are present;
- all surface-boundary sweep action candidates are present;
- safety-lane rows are present;
- negative-control rows are present;
- sequence-step rows are present;
- verifier-derived supervision targets are present on every row;
- entropy-vs-energy diagnostics over frontier margins and hard negatives pass;
- deterministic group-level train/validation diagnostics pass;
- feature vectors contain only pre-decision context and action fields;
- the trained residual lookup artifact is generated from train rows and audited
  against held-out groups before it is used as a policy layer;
- both accepted and rejected labels are present;
- zero invalid accepts;
- every required rejection family is represented.
- pairwise/listwise ranking diagnostics over candidate-complete groups pass.

The current checked corpus has 11,002 rows, including 1,270 long-horizon
sequence-step rows and 318 selection-blocked rows. Its hard-negative families
include `trajectory_budget_exceeded:fee_bps` and
`trajectory_budget_exceeded:buyburn_bps`, so the residual ranker learns that
movement-budget exhaustion is a temporal blocker rather than an acceptable
late-sequence action.

The corpus can train or calibrate an EBRM residual for future lookup-table
generation. It does not authorize governance and does not replace replay.

## Autonomous Actions

The policy can propose bounded updates to:

- swap fee;
- fee-router split;
- MCR and CCR;
- whale-defense `staker_bps`;
- perps funding cap.

The current live evaluator reports:

```text
governance_surface_gate_report
governance_surface_all_gates_ok
```

Every surface bit must be true before `approved=true`.

## Failure Modes

The system rejects when:

- the policy hash is wrong;
- the policy is malformed;
- oracle freshness, divergence, volatility, liquidity, pause, or cooldown
  checks fail;
- a Q-table row is missing;
- a proposed value violates a width, bound, step, order, sum, timelock, or
  surface gate;
- funding fails even if the imported fee/router/collateral/whale master subset
  passes.

## Promotion Requirements

A governance policy should not be promoted from research to release candidate
until it has:

- deterministic generation command and source manifest;
- frozen policy hash;
- replay over representative oracle/market regimes;
- hard-negative coverage near every governance bound;
- invalid-accept count of zero under the exact gates;
- comparison against hold-only, PID, and hand-energy baselines;
- cross-seed EBRM stress reports if a learned residual is used;
- explicit non-claims in the receipt and docs.

The release bar is exact acceptance, not model accuracy alone.
