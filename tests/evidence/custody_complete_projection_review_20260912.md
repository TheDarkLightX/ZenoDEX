# Custody proof progress final advisory review, 2026-09-12

## Decision

Adopt the previously conditional refinement-only amendment for three `FC:ASSET_TRANSFER` capabilities.
The frozen evidence conditions are now met, using parent-reported fresh runs plus the independently inspected source, test, JUnit and mutation receipts below.
This remains a bounded judgment under the existing rubric and is not completion or release evidence.

## Exact amendment

- `generic_transfer.ref`: 0.45 -> 0.47; semantics 0.70 and proof 0.75 unchanged; uncertainty remains `H`.
- `managed_issue.ref`: 0.40 -> 0.42; semantics 0.60 and proof 0.75 unchanged; uncertainty remains `V`.
- `managed_burn.ref`: 0.40 -> 0.42; semantics 0.60 and proof 0.75 unchanged; uncertainty remains `V`.
- `FC:ASSET_TRANSFER` low/central/high: 0.4121/0.4693/0.5236 -> 0.4147/0.4719/0.5261.
- Formal-core low/central/high: 15.251/21.081/27.167 -> 15.264/21.094/27.179.
- Full-V3 low/central/high remains 16.613/23.869/31.947.

Arithmetic: `3 * 0.3 * 0.02 = 0.018` formal capability-score units.
On the fixed 140-unit denominator, `100 * 0.018 / 140 = 0.012857` percentage points, reported as +0.013.
The full-V3 score is unchanged because this batch adds proof/refinement evidence without changing a W07/W09 acceptance score.

## Fixed method and authority

The denominator remains 103 capability units + 12 route units + 25 shared-formal units = 140.
The full-V3 denominator remains 100 points, with the same 12 lanes, four routes and four exclusions.
No capability identity, weight, workstream, route, exclusion or evidence band was added or redistributed.
Production authority remains `NONE`; formal-core completion, whole-value safety, release readiness and production promotion remain false.
Closed value-movement gates remain 0/12.

## Independently inspected evidence

Frozen commit: `e2224617a092380d21ac6028d889a511cfc00e74` over parent `be2693fcd5da816c8e723853b92d3fbe47754bc7`.
Structural source SHA-256: `a1d6e09ff74cbca8627a6f7add05c897b732f17e09f2110c5bd2550a9bf170fd`.
ExactProjection source SHA-256: `9486eb80bc01d6eb26c3ae0f86ba94c74c6e4b5ddeba6adc4538306459dce03b`.
CompleteState source SHA-256: `f7101c17778fe4bff9ca2481f184b2176307e4366141961ee8ac79fa9c7f1802`.
CompleteState test SHA-256: `1f5ffe6ebba80d9a020572e83e187395d00c2a8ff8ca1e7dc2b3a70e2b9fa9ab`.
Metadata test SHA-256: `02699c80cba2bc74075cd222545dc5b3754e1278e4e93832e05250a6900cdf8f`.
The final metadata file contains no `cast` import or calls; its three constructor/precedence observations are otherwise the reviewed subject.
JUnit SHA-256 `085787ad8948793997d0544821038e0df5229384cfe1b37d5f0d595ca6d2fb8f` records four tests, zero failures/errors/skips, 133.150 seconds.
Mutation receipt SHA-256 `be72d1e326cacaa4a0e1259eb5c983f4d901b1aa714091737f3e167165153943` records two compiling semantic mutants killed at the intended byte/resource assertions with zero errors.
Both baseline and proposed assessment records independently passed `tools/v3_progress_assessment_calc.py`, reproducing 21.081 and 21.094 respectively.

## Parent-reported fresh gates

ExactProjection: 2 tests passed in 133.73 seconds.
CompleteState: 4 tests passed in 133.17 seconds, covering 18 encodings, ten actual steps (seven accepted, three rejected), full-size BVA and nine exact contracts across the two proof subjects.
Metadata: 3 tests passed in 0.63 seconds; all three Python files passed MyPy and Ruff.
Six critical-path hygiene checks passed with zero red flags.
These long-running gates were not rerun during this advisory review; the CompleteState JUnit and mutation receipt were inspected directly.

## Closed, narrowed and open obligations

Closed in the finite model: accepted transfer and managed leaf reprojection, including managed siblings and zero supply; four-payload state materialization; exact finite encoder/resource relations; metadata retention across modeled steps.
Narrowed by differential evidence: complete canonical bytes and accepted/rejected materialized post behavior on the frozen finite corpus, including aggregate 1 MiB and 1 MiB+1 boundaries.
Still open: constructor metadata and registry-policy admission, canonical root authenticity, and universal Python/Rust codec/parser/arithmetic/execution refinement.
Still open: whole-coordinator first-error theorem, global journal/effect correspondence, guest receipt qualification, initialization, migration and cross-lane lifecycle refinement.
`F-GLOBAL` stays 0.28/0.35/0.45, `F-REFINE` stays 0.15/0.25/0.35, and `F-TOOLS` stays 0.45/0.55/0.65.
If the existing 0.40-0.45 refinement scores are judged to have already included this exact finite bridge, retain 21.081; no evidence supports a larger increment.
