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
