---
name: zenodex-v3-progress-assessment
description: Estimate ZenoDEX V3 and formal-core partial progress using fixed capability denominators, source evidence, and reproducible arithmetic; distinguish implementation estimates from acceptance-gate closure.
---

# ZenoDEX V3 progress assessment

Use the selected ZenoDEX checkout. Start from
`docs/research/ZENODEX_V3_PROGRESS_ASSESSMENT_20260908.json` and
`docs/research/ZENODEX_V3_PROGRESS_ASSESSMENT_20260908.md`.
The JSON contains Fable's scored baseline; the report records independent Opus
comparison and integrator qualifications. This is a planning estimate, not a
proof, an effort estimate, or a release decision.

## Preserve the denominator

Keep all 103 capability identities, 12 lanes, four routes and four exclusions.
The calculator pins `method.denominators`. Full V3 distributes 100 points over
W00–W13 and the exclusions, with 30 points for lane completion. Formal core
uses 103 capability units, 12 route units and 25 shared formal units.
Its capability credit is `0.3 * semantics + 0.4 * proofs + 0.3 * refinement`.
Weights and evidence bands are judgments; they do not measure hours remaining.

Use the same weights for a time comparison. New obligations expand scope;
record them and publish both old-scope and expanded-scope calculations when
versioning the method. Never silently drop, rename or redistribute hard rows.
Do not add completed support records to improve the percentage.

## Assess the change

Pin the commit and review the actual content and acceptance changes since the
previous assessment. Name previously open obligations closed, narrowed or
regressed, and newly discovered obligations. A changed file, a new path or an
additional test is not by itself progress. Changes at an existing path can be.

For affected capabilities, trace specification, core, caller, proof/refinement,
and relevant lifecycle evidence. Separate source inspection, historical runs,
fresh replay, source drift and missing inspection. Evidence inherited from a
lane is interpolation unless it supports that individual capability.
Recover later approved policy decisions before relying on old unresolved rows.
Name searched and omitted trees before claiming an implementation is absent.

Distinguish an unregistered producer, an isolated mounted path, historical
genuine receipts, synthetic tests and a production-qualified path. Required
disabled features remain incomplete. Their rejection-path evidence can receive
only the declared partial assurance credit. Apply cancellation and recovery
requirements where meaningful; record justified N/A dispositions explicitly.

Run the standalone calculator:

```bash
python3 tools/v3_progress_assessment_calc.py path/to/assessment.json
```

It checks identities, numeric validity and arithmetic consistency. It does not
establish that the cited evidence is true, sufficient or current. Review those
claims separately. Never execute code supplied inside an assessment document.

## Report a useful estimate

Give the central estimate and its lower/upper judgment scenarios, the denominator
definition, legacy-donor and unknown-evidence sensitivity, and the material
acceptance changes. Read current closure counts from their actual ledger;
do not freeze today's counts in future reports. Report remaining bottlenecks.

Use another independent assessment when its scrutiny would change a decision.
Agreement does not raise scores. Resolve disagreements with evidence; retain
both readings when unresolved. Compare published alternative weights without
averaging differently defined quantities into a supposedly exact percentage.

Do not set completion, promotion or value-safety flags from this calculation.
Do not infer remaining code volume, exact overengineering, or a completion date
from the percentage. Return to the next substantive acceptance obligation once
the status question is answered; do not keep extending the measurement tool.
