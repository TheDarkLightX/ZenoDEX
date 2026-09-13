# ZenoDEX V3 partial-progress assessment, September 8, 2026

Status: advisory planning baseline. No completion or promotion authority.

Both reviewers inspected committed source at `70f9157ef097384c6b48db22c254d8134f19f8f5`.
Fable used `claude-fable-5-1` at Max; Opus used `claude-opus-5` at Max.
A subsequent compact Opus cross-review used High. The independent initial
assessments came before that cross-review. Model agreement is correlated evidence.

| Assessment | Full V3 central | Judgment scenarios | Formal core central | Judgment scenarios |
| --- | ---: | --- | ---: | --- |
| Fable, adopted tracking method | 23.4% | 16.1–31.4% | 21.0% | 15.2–27.1% |
| Opus, independent alternate method | 28.9% | 18.6–40.0% | 23.4% | 14.9–34.1% |

These are weighted estimates of partial completion. The ranges are chosen
evidence scenarios, not statistical confidence intervals. They do not measure
remaining time, required lines of code, or the probability that funds are safe.
The central readings support roughly 23–29% for V3 and 21–23% for the formal
core, under the two declared methods. We retain both instead of averaging them.

The existing closure inventory remains 0/14 complete workstreams, 0/12 complete
lanes, 0/4 complete routes and 0/12 qualified value-movement gates. Those counts
do not erase the implemented and proved partial work reflected in the estimates.

## Reproducible baseline

[Scored data](ZENODEX_V3_PROGRESS_ASSESSMENT_20260908.json) preserves every
capability score, row weight, evidence reference and remaining acceptance item.
The standalone calculator checks identity coverage, finite numeric inputs,
the pinned denominator and arithmetic. It does not verify cited evidence.

```bash
python3 tools/v3_progress_assessment_calc.py docs/research/ZENODEX_V3_PROGRESS_ASSESSMENT_20260908.json
python3 -m pytest -q tests/tools/test_v3_progress_assessment_calc.py
```

The [reusable skill](../../tools/skills/zenodex-v3-progress-assessment/SKILL.md)
describes how to refresh the baseline without counting support work as closure.
It leaves the existing acceptance tracker and all qualification flags unchanged.

## Method and sensitivity

Fable scores all 103 capabilities in 12 lanes. V3 assigns 30 of 100 weight points to
those lanes, 8 to the four routes and 2 to the four exclusions; the other 60 cover
the remaining workstreams. Formal core assigns 103 capability units, 12 route
units and 25 shared formal units. Each formal capability combines semantics,
preservation proofs and implementation refinement with weights 0.3/0.4/0.3.

Exclusions receive credit for evidence that excluded behavior is prevented.
Required disabled features remain incomplete; reject-only coverage is partial
assurance credit, not delivery of the feature. Some capability judgments are
interpolated from lane evidence; the numeric detail exceeds the precision of
the underlying inspection. The bands do not capture every source of error.

Fable arithmetic from the original candidate calculator was reproduced as:

| Scenario | Full V3 | Formal core |
| --- | ---: | ---: |
| Central | 23.369% | 20.981% |
| Legacy-only donor credit reduced to the declared 0.03 baseline | 21.697% | 15.423% |
| Entirely unverified rows assigned their low score | 22.889% | 20.981% |

The original narrative gave 22.3% for the last V3 scenario; the calculation
corrects it to 22.9%. Legacy credit substantially affects the formal-core score.
Changing shell-versus-lane weighting also changes V3 materially. Neither model
has measured an empirically optimal weighting.

Opus uses the following alternate rows. Their exact numbers are also retained
under `integrator_review.independent_comparison` in the scored JSON.

| Section | Row | Weight | Low credit | Central credit | High credit |
| --- | --- | ---: | ---: | ---: | ---: |
| full_v3 | W00 | 2 | 0.55 | 0.7 | 0.82 |
| full_v3 | W01 | 4 | 0.22 | 0.35 | 0.48 |
| full_v3 | W02 | 8 | 0.22 | 0.35 | 0.48 |
| full_v3 | W03 | 6 | 0.35 | 0.5 | 0.62 |
| full_v3 | W04 | 6 | 0.22 | 0.32 | 0.44 |
| full_v3 | W05 | 3 | 0.45 | 0.6 | 0.72 |
| full_v3 | W06 | 6 | 0.32 | 0.45 | 0.55 |
| full_v3 | W07 | 22 | 0.1455 | 0.229 | 0.3198 |
| full_v3 | W08 | 7 | 0.09 | 0.1525 | 0.235 |
| full_v3 | W09 | 14 | 0.18 | 0.28 | 0.4 |
| full_v3 | W10 | 6 | 0.08 | 0.18 | 0.3 |
| full_v3 | W11 | 8 | 0.13 | 0.22 | 0.33 |
| full_v3 | W12 | 4 | 0.02 | 0.06 | 0.12 |
| full_v3 | W13 | 4 | 0.05 | 0.2 | 0.4 |
| formal_core | FC1 | 12 | 0.3 | 0.45 | 0.6 |
| formal_core | FC2 | 28 | 0.2166 | 0.3221 | 0.4369 |
| formal_core | FC3 | 28 | 0.1209 | 0.1972 | 0.3033 |
| formal_core | FC4 | 24 | 0.0546 | 0.0988 | 0.1812 |
| formal_core | FC5 | 8 | 0.07 | 0.13 | 0.23 |

Recompute each percentage as `100 * sum(weight * credit) / sum(weight)`.
The formal-core dimension weighting differs from Fable's capability weighting;
its lower refinement dimension is a useful view of the remaining bottleneck.

## Integrator qualifications

- A V1 registry lists nine lanes without producers and two blocked/disabled
  lanes. Together those 11 lanes cover 96 capabilities outside ASSET_TRANSFER.
  Registry status alone does not establish the reachability of every consumer.
- Historical unresolved policy rows need reconciliation with later approved
  decisions. A missing proposed successor filename does not prove missing
  semantics. No policy constants were selected by this assessment.
- The source snapshot contained 2217 committed files. Omitted Rust guests,
  tools, UI and other trees are inspection gaps, not absent implementations.
- Isolated mounting, synthetic-RISC0 tests, historical genuine receipts and
  current production qualification are separate evidence classes.
- Cancellation and recovery apply to relevant workflows. An already-atomic
  transfer need not gain a cancellation command to satisfy a uniform checklist.
- The initial reviewers inspected source and historical records. They did not
  rerun the proof suites or establish universal Python/Rust execution refinement.

The cross-review suggested new exclusion caps, an averaged point estimate and
raising lower scenario floors. Those judgments were not adopted: their precise
values have no stronger evidence, and changing scores would erase the original
independent baseline. Useful factual qualifications were retained above.

## Remaining work and parallel repair

The largest remaining work is complete lane lifecycles and cross-lane routes,
concrete runtime/formal refinement, and production publication/recovery/finality
qualification. Existing kernels can reduce that work; completion credit is
limited where their contracts are not connected through the intended runtime.

After the assessment subject, commit `3a20d7aa9884a662b3f7cf79f11f6f9562c8a7d0`
aligned two Python derived-root returns with the existing Rust zero-root rejection
policy. Normal hash bytes and explicit empty-plan sentinels were preserved.
Independent root testing passed 217 targeted tests, and controlled zero-digest
failures were retained. That repair is separate from these unchanged scores.

No Lean, Kani, ESSO, RISC0 proving or production suite was rerun for the
assessment. The pre-existing claims-registry failure remains open: record 123
references missing `tools/check_derivatives_authorization_matrix.py`.

Next: close a concrete constructor/journal correspondence obligation and review
the requested simplification proposals. Do not extend the measurement tool
unless an actual reporting failure requires it.

## Code-value account, September 9, 2026

The recorded estimate moved **0.000 percentage points** for both V3 and formal
core after the scored source. No revised numerical assessment was recorded.
The later implementation gains below are `NOT_RESCORED`; this does not assign
them zero value. Continuing to quote the frozen percentages without a change
account left the engineering value inadequately tracked.

The audited range is `70f9157ef097384c6b48db22c254d8134f19f8f5` through
`45c3310cee9a4e4b62ba0868e5b4f4d4e6bfe44a`: 16 commits, 98 files,
27,021 added lines, 38 removed lines, **26,983 net added lines**. These are
physical Git diff lines, including blanks and comments. Uncommitted unrelated
work is excluded. Rust trailing `#[cfg(test)] mod tests` blocks are counted as
tests. This measures retained source growth, not cumulative model output or
the amount of necessary code. Reproduce the raw counts with:

```bash
git diff --numstat 70f9157ef097384c6b48db22c254d8134f19f8f5 45c3310cee9a4e4b62ba0868e5b4f4d4e6bfe44a
```

| Retained content | Net added lines |
| --- | ---: |
| Python/Rust core, runtime and guest implementation | 3,187 |
| Lean proof source | 353 |
| Test code, including Rust unit-test modules | 6,904 |
| Tooling code | 1,518 |
| CI and build configuration | 169 |
| Assessment and acceptance JSON | 4,932 |
| Golden-vector JSON | 3,964 |
| Retained evidence JSON | 2,167 |
| Documentation and skills | 1,227 |
| Dependency lockfile | 2,562 |
| **Total** | **26,983** |

The following batches are nonoverlapping. Runtime/proof/test/other columns are
net line counts; other includes tools, configuration, data, locks and docs.
Each batch remains **NOT_RESCORED**; the last adopted aggregate estimate is
unchanged. The existing score file and its denominator remain unchanged.

| Commit range | Runtime | Proof | Tests | Other | Delivered value and score treatment |
| --- | ---: | ---: | ---: | ---: | --- |
| `70f9157e..3a20d7aa` | 0 | 0 | 81 | 0 | Two runtime lines replaced: Python derived-root zero rejection aligns with Rust. Existing rejection regression repaired; no numerical rescore. |
| `3a20d7aa..7888cad58` | 0 | 0 | 176 | 4,907 | Assessment calculator, retained scoring data and reviewed simplification guidance. Support value; no economic behavior delivered. |
| `7888cad58..062e08f01` | 1,977 | 353 | 3,021 | 4,265 | Custody-aware transfer/issue/burn, complete-table global checks, canonical byte ingress and a scoped Lean lift. Affects W07/ASSET_TRANSFER and W09; `NOT_RESCORED`. |
| `062e08f01..77870977b` | 488 | 0 | 1,322 | 5,367 | Derived custody statement, bounded frame, native guest entry and conditional receipt adapter. Affects W03/W06/W09/W10; `NOT_RESCORED`. Actual image/receipt and publisher qualification remain open. |
| `77870977b..f4239d23b` | 722 | 0 | 1,846 | 1,254 | Sealed V2 BLS verification and one captured command/state/profile across authentication and economic checks. Affects W03/W06 and ASSET authorization; `NOT_RESCORED`. Publication remains open. |
| `f4239d23b..45c3310ce` | 0 | 0 | 458 | 746 | Existing hygiene ledger now executes declared faults on a pinned commit. Six mutants killed with passing controls. Support value; no economic capability or formal-core completion credit. |

The last batch added 1,204 net lines: 227 tooling, 458 tests, 59 CI, 106 docs
and 354 evidence. It repaired a reproduced false-success case: a declared
negative test weakened to `assert True` passed the old runner. The
[retained replay](../../tests/evidence/required_mutation_replay_gate_v1_20260909.json)
establishes the six declared fault checks. Hosted CI and independent host
approval remain unqualified.

### Evidence-backed value and remaining delivery cost

- The [custody regression](../../tests/core/test_asset_lane_custody_v2.py) shows
  80 account atoms plus 20 custody atoms reaching an authorized transfer while
  preserving 100 total atoms and the custody rows. It also covers issue/burn,
  vault-only supply, dormant reissue and unauthorized no-effect rejection.
  The earlier account-only representation rejects this required state.
- The [statement contract](../specifications/ASSET_LANE_CUSTODY_GLOBAL_STATEMENT_V2.md)
  and retained five-vector comparison connect Python and Rust execution to the
  concrete global relation and exact journal bytes. The genuine receipt and
  deployed image remain unqualified; native tests cannot discharge that step.
- The [combined consumer](../../src/integration/authenticated_asset_lane_custody_receipt_v2.py)
  prevents command substitution, input changes during verifier acquisition and
  coherent foreign profile metadata. Its current external callers found in
  `src` and `tools` do not include a production publisher; the mounted caller
  found by this review is its integration test. The
  [profile-binding mutation evidence](../../tests/evidence/asset_lane_custody_profile_binding_v2_mutation_20260909.json)
  retains four detected guard-removal faults.
- The Lean addition proves a restricted custody lift using existing leaf
  models. The retained compilation and axiom audit are described in the
  [continuity record](../ZENODEX_SESSION_CONTINUITY.md). It is not a universal
  proof of codecs, authentication, publication or all command families.

An independent Astra review of this exact range corroborated these bounded
gains through source and retained evidence inspection; it did not rerun tests
or proofs. The existing rubric already credited typed and partially proved
ASSET components. The higher isolated-publisher band still requires mounting
and genuine receipts. This review therefore supplies no defensible numerical
increase to substitute for a full score update. No workstream, complete lane,
required route or value-movement gate closed in this range.

The code has demonstrated component and regression-prevention value. Its
maintenance cost is substantial, and this audit does not establish that every
added line is necessary or that the overall engineering effort was efficient.
Next, qualify the rebuilt custody receipt and its explicit role/schema, then
carry the same cases through current-store publication and recovery. This
finishes an existing delivery path. The requested cross-model reporting below
addresses missing contribution accounting; it does not resolve that economic
blocker or change this assessment's denominator.

For future batches, append the same compact account: exact commits, affected
score rows, before/after acceptance behavior, evidence, categorized line delta,
reviewed score delta or `NOT_RESCORED`, and the next delivery blocker. Review
partial credit after each substantive batch; preserve prior assessments and
run the existing calculator before announcing a new percentage. Support work
must name a concrete defect or the acceptance step it enables. Use this record
to challenge repeated growth without acceptance gains. Lines or percentages
alone cannot establish optimality, remaining effort or production safety.

The requested [cross-model contribution report](ZENODEX_V3_PRODUCTIVITY.md)
reuses Git observations and this assessment calculator. It records shared
outcomes once, exposes missing model/resource data and retains corrections.
This reporting work claims no economic or formal-core percentage advancement.
Its implementation is outside the frozen range counted above.


## September 9 custody trace amendment

The [reviewed batch amendment](ZENODEX_CUSTODY_TRACE_DELIVERY_20260909.md) moves
the carried formal-core estimate from 20.981% to 21.038% (+0.057 percentage
points). V3 remains 23.369%. Only the managed issue/burn proof components
changed; all other rows and earlier unrescored work remain carried forward.
This is a narrow amendment, not a full current-checkout reassessment. The
existing calculator replays both endpoint inputs; closure remains 0/14
workstreams, 0/12 lanes, 0/4 routes and 0/12 value-movement gates.


## September 12 isolated custody publication amendment

Implementation `3018ec0f133ea9388153544b45cbe8edfcab66d6` adds a fresh isolated
V2 store owner for complete global/custody state, selected receipt admission,
current authority, atomic publication and bounded recovery. Daybreak reviewed
the exact source; Astra integrated and repaired it. The
[delivery evidence](../../tests/evidence/isolated_custody_publication_v2_20260912.json)
records 209 distinct targeted tests, six killed mutations after passing controls,
development failures, source hashes and unrun proof/release obligations.

The existing rubric's W06 weight remains five. Only its low/central/high score
changes from 0.40/0.50/0.60 to 0.50/0.60/0.70. Prior V1 publication mechanics
already received credit; this increment credits the complete current V2 state
consumer. No W07 capability gets the same credit again. Formal-core scores stay
fixed because this patch adds no new semantics, preservation or refinement proof.

| Carried estimate | Before | After | Change |
| --- | ---: | ---: | ---: |
| Full V3 central | 23.369% | 23.869% | +0.500 pp |
| Full V3 low/high | 16.113–31.447% | 16.613–31.947% | +0.500 pp |
| Formal core central | 21.038% | 21.038% | 0.000 pp |
| Formal core low/high | 15.208–27.124% | 15.208–27.124% | 0.000 pp |

The predecessor is the adopted September 9 trace amendment, not the original
September 8 baseline. The two frozen calculator inputs carry all unchanged rows
without fresh assessment. Earlier unrescored deliveries remain excluded. Replay:

```sh
python3 tools/v3_progress_assessment_calc.py tests/evidence/v3_custody_publication_assessment_before_20260912.json
python3 tools/v3_progress_assessment_calc.py tests/evidence/v3_custody_publication_assessment_after_20260912.json
```

These are planning judgments under fixed weights. All 103 capabilities, 12 lanes,
four routes and four exclusions remain. Closure stays at 0/14 workstreams,
0/12 lanes, 0/4 routes and 0/12 value-movement gates. Genuine matching RISC0
receipts, multi-occurrence epoch qualification, certified initialization,
concrete runtime/store refinement and production lifecycle obligations remain.

The implementation commit adds 1,275 runtime lines, 1,382 test lines, 135
specification lines and 269 hygiene-data lines, removing zero. It adds no proof,
dependency or new tracker. The subsequent evidence and immutable calculator
snapshots are support data, recorded separately in the existing productivity
manifest. Provider tokens and total development time were unavailable; test
runtimes are not development-time measurements.

## September 12 complete custody projection amendment

The batch `be2693fcd5da816c8e723853b92d3fbe47754bc7` through
`e2224617a092380d21ac6028d889a511cfc00e74` proves exact accepted leaf
reprojection and adds a complete four-payload state encoder. Previously, the
finite projection omitted origin metadata and had no full-state byte model.
[Retained evidence](../../tests/evidence/custody_complete_projection_v2_20260912.json)
records nine passing tests, 18 encodings, all ten transaction vectors, the full
byte-cap boundary and two compiling semantic mutants killed by assertions.

That implementation adds 892 proof/control lines, 874 Python test lines and 114
hygiene-data lines, with no removals or runtime changes. The following evidence
and accounting commits through `5e1e5a9e84b162ebfa3c0e00fcf78aef6968d38a` add
2,828 support lines, including 2,361 copied before/after assessment lines.
They receive no additional delivery credit. The append-only contribution
manifest records known native contributions; provider tokens and development
time remain unavailable for that batch.

[Independent review](../../tests/evidence/custody_complete_projection_review_20260912.md)
supports only a 0.02 refinement-score increase for generic transfer, managed
issue and managed burn. Under the unchanged denominator this moves the carried
formal-core estimate from 21.081% to 21.094% (+0.013 percentage points). V3 stays
23.869%, and qualification stays 0/12. Other rows are inherited judgments.
The [before](../../tests/evidence/v3_custody_complete_projection_assessment_before_20260912.json)
and [after](../../tests/evidence/v3_custody_complete_projection_assessment_after_20260912.json)
calculator inputs preserve the exact scored subjects. Constructor admission,
ordered source-journal/effect checks, universal runtime refinement and genuine
receipt/publication qualification remain the delivery blockers.

## September 12 constructor admission and conservation repair

Batch `5e1e5a9e84b162ebfa3c0e00fcf78aef6968d38a` through
`0f14e8dc294df181c9ffc40de7136449f118d452` adds complete modeled constructor and
policy-origin admission, inhabited transfer/issue/burn applications and exact
runtime-generated input/post-row comparisons. It also repairs Python/Rust
acceptance of a faulty internal USD leaf carrying coherent EUR conservation.
[Evidence](../../tests/evidence/custody_admission_guard_v2_20260912.json) and
[independent review](../../tests/evidence/custody_admission_guard_review_20260912.md)
retain the scope, red/green controls, all failed attempts and remaining gaps.

| Whole-file category | Added | Removed | Net |
| --- | ---: | ---: | ---: |
| Proof and Lean controls | 1,075 | 0 | 1,075 |
| Runtime, including inline Rust tests | 107 | 10 | 97 |
| Python tests | 632 | 6 | 626 |
| Hygiene and regenerated data | 273 | 2 | 271 |
| Documentation | 4 | 2 | 2 |
| Total | 2,091 | 20 | 2,071 |

The proof category comprises 276 theorem-module lines and 799 Lean control lines.
Most runtime additions are the inline Rust regression; line count is not delivered
functionality. The subsequent review, usage, assessment snapshots and continuity
account are support work and receive no extra capability credit.

The unchanged calculator validates a narrowly reviewed proof increment from 0.75
to 0.76 for generic transfer, managed issue and managed burn only. The carried
formal-core estimate moves **21.094% to 21.103% (+0.009 pp)**. V3 remains **23.869%**;
qualification remains **0/12**. Other scores and uncertainty labels are inherited.
The scope does not support a whole-program percentage reassessment.

Five Fable 5.1 Max workers actually ran. None supplied an accepted implementation
file. A parent permission-rule error denied output writes, and three runs ended
with provider credits exhausted. Two review outputs informed corrections. After
a corrected output-only permission probe, Opus supplied the proof candidate;
parent/native review and compilation repaired it. The
[usage record](../../tests/evidence/custody_admission_worker_usage_20260912.json)
retains all fourteen main/auxiliary provider records. Fable reports 423,520 output
tokens across its five runs; the Opus implementation reports 81,562, both including
provider-reported reasoning. These are source-recorded usage counters, not LOC,
billable invoices, exclusive wall time or accepted-work measurements. Native/root
resource use is unavailable; actual billed cost remains unknown.

The small percentage gain exposes an inefficient batch decomposition. The next
acceptance unit is the complete coordinator outcome/journal/effect/runtime bundle,
with one implementation owner and independent adversarial review. A separate lane
bundle should proceed concurrently only where exact state and normative policy
are established. Retain focused development checks, then run the shared proof
closure at integrated checkpoints. Do not weaken proof premises, round up scores,
claim a launch as delivery or repeatedly rescore individual lemmas to show activity.

## September 12 integrated coordinator amendment

The coherent coordinator bundle is committed at
`244c50ebcbed2a3fbb332d5853ce7260d989a5e2`, with
[source-bound evidence](../../tests/evidence/custody_coordinator_bundle_v2_20260912.json)
and [independent review](../../tests/evidence/custody_coordinator_bundle_review_20260912.md).
It integrates ordered typed rejection, internally derived finite successors,
source/effect/journal/receipt bindings, complete resource admission and preservation
at every accepted or rejected prefix. The current runtime corresponds on ten fixed
vectors and a four-attempt mixed history. Coherent unauthorized recipient state
and effects are rejected by correct independent publication replay.

| Carried estimate | Before | After | Change |
| --- | ---: | ---: | ---: |
| Formal core central | 21.103% | 21.169% | +0.066 pp |
| Formal core low/high | 15.272–27.188% | 15.339–27.254% | about +0.066 pp |
| V3 central | 23.869% | 23.969% | +0.100 pp |
| V3 low/high | 16.613–31.947% | 16.713–32.047% | +0.100 pp |

The three transfer/issue/burn proof cells move 0.76→0.80 and their refinement
cells each increase 0.05. W09 increases 0.01 under its unchanged weight of ten.
The exact formal increment before row/report rounding is approximately 0.0664 pp.
All other rows, semantic scores and uncertainty labels are inherited; this is
a scoped amendment rather than a new whole-repository assessment. The calculator
checks the [new after input](../../tests/evidence/v3_custody_coordinator_assessment_after_20260912.json)
against the existing rubric. Its before input is the previous admission after
input, reused without a second copy. Qualification remains 0/12.

The measured implementation interval `afb5fd52…` through `244c50eb…` adds 3,470
lines and removes 12: 1,378 proof-module additions; 2,090 test/control additions
and ten removals; one source-inventory line and one tooling pin each replaced.
Rust production bytes are unchanged; its inline test diff is counted as tests
here. The automated contribution report retains its whole-file classification.
The code adds assurance and adversarial coverage, with no new economic behavior.

The two draft fixture/harness files totaled 1,784 lines. Integration uses 1,351,
a reduction of 433 lines, while adding full commitment comparisons and history
controls. Reuse of the existing constructor witness removes duplicated fixtures.
Aristotle supplied three fixed proof bodies; root corrected and integrated the
Opus drafts and independently checked the returned proofs. The new assessment,
review, usage and continuity records are subsequent support data with no extra
product credit. Git's implementation checkpoint interval is 2h03m21s, including
earlier research and overlapping worker work; exclusive development time is
unknown. Provider usage is source-recorded separately from accepted LOC.

The next bottlenecks are actual runtime/source refinement and the existing V2
guest's genuine image/receipt/publication qualification. Other lane and route
obligations remain. Bounded correspondence and proof preservation do not imply
complete cryptography, parser verification, production safety or full formal-core
completion.

# September 12 amendment: current perps margin-account lifecycle

New implementation range: `e97d6f4d510962e6887a12e7de28d8444feef5f5` →
`88c9f27d992cb57664870887542e379f91c1e0fa`. The scoped assessed subject advances
from `244c50ebcbed2a3fbb332d5853ce7260d989a5e2`; intervening support work receives
no extra product credit. [Evidence](../../tests/evidence/perps_margin_lifecycle_v1_20260912.json)
and [independent review](../../tests/evidence/perps_margin_lifecycle_review_20260912.md)
retain exact sources, tests, failed attempts, claim ceilings and contributors.

Before: no Lean transition for the current margin module; the older rounding
proof uses different legacy units. After: selected-account ordered transition,
subject/nonce/identity properties, exact close tombstone, fixed-account history,
least quote ceiling and bounded flat-account drain/close proofs. Thirty-eight
shared outcomes and seven history attempts compare full Python/Rust outputs;
six single-site semantic mutants are killed by independent assertions.

| Measure | Before | After | Change |
| --- | ---: | ---: | ---: |
| Formal central estimate | 21.169% | 21.219% | +.050 points |
| V3 central estimate | 23.969% | 24.069% | +.100 points |
| Qualified value-safety gates | 0/12 | 0/12 | none |

Only `margin_deposit` and `margin_withdraw` preservation .30→.35 and refinement
.35→.40, and W09 .23/.31/.41→.24/.32/.42, change. Semantics, uncertainty and all
other rows are inherited. The unchanged calculator validates the [after input](../../tests/evidence/v3_perps_margin_lifecycle_assessment_after_20260912.json).

Code value: **+936/−2** across four files: proofs +308; tests and their native
transport +628/−2; economic runtime +0/−0. The transport is a 29-line Rust
example, so the automated whole-file classifier may label it runtime. The
two-string inherited golden repair restores an existing parity gate and earns
no separate product credit. Evidence, assessment and continuity changes are
support work, counted separately after their commit. Model token/cost and
exclusive elapsed time are unavailable; test durations are retained as tests.

Remaining acceptance: complete market selection/reconstruction and numeric
admission refinement, then broader market obligations and real publication.
No full formal core, lane, route or production completion follows.

## September 12 amendment: full perps market preservation

Implementation `321d4d032`→`7386fa2ea` adds **638/removes 17**: proofs 385/4,
tests 253/13, economic runtime 0/0. The full model now derives selection/count,
preserves siblings, order, capacity, exact numeric/gross bounds and arbitrary
multi-account histories. [Evidence](../../tests/evidence/perps_margin_market_v1_20260912.json)
and [review](../../tests/evidence/perps_margin_market_review_20260912.md) retain
sources, commands, contributors, failed drafts and remaining exclusions.

Formal **21.219%→21.297%** (+.078 points); V3 **24.069%→24.169%** (+.100).
Judgment bounds are formal 15.468–27.383%, V3 16.913–32.247%. Only margin
deposit/withdraw proof/refinement and W09 change. The existing after-input was
revised with its earlier bytes pinned at `26057f389…`, avoiding another complete
1,199-line snapshot. The unchanged calculator validates all derived row/section
caches. Other scores are inherited; no lane, route or safety gate closes.

Fresh gate: ten tests, 43 states, 19 history attempts, seven mutants, twelve exact
theorem consumers and three constructive admission witnesses. Next: concrete
effect/terminal projection and coordinator binding, universal runtime/decoding
refinement and genuine publication. Support metadata receives no separate credit.

## September 13 amendment: connected margin V2 successor

`2f1c0e055`→`417ec94ad` adds 2,567 lines across ten files: runtime 685,
proof 411, tests 1,350, specification 121; no deletions. The [evidence](../../tests/evidence/perps_margin_global_v2_20260913.json)
and [review](../../tests/evidence/perps_margin_global_review_20260913.md) tie this
growth to a previously failing connected behavior: withdrawal/refill now respects
V2 terminal history and synchronizes the asset frame so ordinary transfers remain
usable. Unsupported consumed objects and accepted-result aliases were repaired.

The new model proves episode availability, exact claim correspondence and V2
lifecycle/frame/history preservation. Its 115-case Python bridge and eleven typed
theorem consumers pass. Runtime qualification here is a pure candidate for one
market with a reserve-free asset frame. No receipt or publication authority follows.

Reviewed estimates: formal **21.297%→21.419%** (+.122 points); V3
**24.169%→24.239%** (+.070). Judgment ranges: 15.589–27.505% and
16.983–32.317%. Only the two margin capabilities change. Uncertainty H, all other
rows and the 0/12 qualification count remain fixed; no separate W09 credit.
The existing after-input is revised with its previous bytes pinned at `2f1c0e055`.
The in-progress Rust successor receives no credit yet. Evidence/assessment
metadata is support work and is counted separately in the contribution report.

Root contributed 1,086 source lines, Luna 694 and the Astra proof worker 787.
Root reviewed both workers; Astra independently reviewed runtime and the score
amendment. Exclusive model time, native token usage and actual cost are unknown.
Recorded test durations are not substituted for work time. The next acceptance
is Rust/Python successor correspondence and then real admission/publication.

### September 13: Rust counterpart of the connected margin path

`e95e897c…` → `22e330b4…` adds 2,764/removes zero lines: 1,331 runtime,
1,174 tests including the JSON transport, 18 configuration, 218 lockfile and
23 documentation. No proof lines were added. Luna implemented the Rust
counterpart; root repaired a finite-width rejection mismatch and completed
actual Python comparison; Astra independently reviewed both runtime and evidence.
The [source-bound account](../../tests/evidence/perps_margin_rust_v2_20260913.json)
retains the findings, commands, contributors and limits.

Sixty combined Python tests and six native Rust tests passed; 37 shared cases
compare complete typed observations across the joined lifecycle. Two observer
corruption controls are distinct from executed Rust mutants. Strict Clippy,
Ruff, mypy and formatting pass. The inherited missing claims-registry file
remains a failed gate. No full proof build or new receipt was produced.

The reviewed amendment changes only margin deposit/withdrawal refinement
`.50→.55`. Formal core **21.419%→21.440%**, a **+0.021-point** rounded gain;
V3 remains **24.239%**, with no newly mounted workflow. Formal uncertainty
range is 15.611–27.526%. All other scores and 0/12 qualified gates are unchanged.
The earlier assessment remains pinned at `e95e897c…`. Support metadata receives
no further credit. The next integration is receipt/route admission and isolated
publication against authentic current state, with exact joint roots and claims.


### September 13: isolated TauFold verifier support

ZenoDEX parent `4247e619…`; [upstream handoff](TAUFOLD_ZENODEX_ASSURANCE_ARCHITECTURE_20260913.md)
pins public TauFold source `55ec8821…` and the exact reviewed candidate patch.
The upstream delta is **+869/−17**: verifier runtime +296/−17, tests +573/−0,
proofs +0/−0. Patch packaging, independent replay probes and this account are
additional support, not ZenoDEX economic implementation.

The repair closes demonstrated executable-substitution and bounded-I/O/parser
failures while retaining genuine receipt acceptance. Evidence: 27 focused tests,
four real receipts/49 rejections, ten independent boundary controls and nine
synthetic transport controls. Astra repaired two review-found process edge cases.
Assessment **NOT_RESCORED**; carried formal 21.440% and V3 24.239% are historical,
not a fresh zero-gain measurement. No lane or 0/12 qualification gate closes.
Authenticated input/state linkage and actual isolated publication remain required;
the full margin/custody receipt cannot be replaced by this small policy guard.
