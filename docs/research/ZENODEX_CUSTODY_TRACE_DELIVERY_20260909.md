# Custody trace and successor delivery, September 9, 2026

Implementation: `c61f536315191bd0a1a482a3932fdeb43009cd6f`, based on
`ff9112b9970e4f510fcf198f7baafe149b98265a`. This is a bounded functional-core
increment. The full formal core and V3 remain incomplete.

The new Lean proof derives complete finite-row invariants through mixed
transfer/issue/burn histories from initial row admission plus static policy
selection and command-shape premises. Python and Rust now
construct the full admitted global successor. The host can prepare the existing
five guest frames from predecessor and command without supplying a proposed
successor. Existing policy, wire bytes and publication authority are unchanged.

[Verification](../../tests/evidence/asset_lane_custody_trace_successor_v2_20260909.json)
records eight formal checks, 146 native Rust tests, 24 new core cases and 49
selected integration cases. Four prover-input cases were rerun with integration
and are already included in the 24 core count. One optional measured-native BLS
test skipped.
[Archived mutation replay](../../tests/evidence/asset_lane_custody_successor_v2_mutation_20260909.json)
passed both unmodified controls and killed both declared mutants. Full Clippy
still fails an existing argument-count warning in unchanged code. Broad release,
ESSO/Kani and real guest/receipt qualification were not performed.

## Reviewed score amendment

This applies only this batch to the retained September 8 assessment. Other
scores are carried forward without reinspection, including earlier deliveries
marked NOT_RESCORED. It is not a complete reassessment of the current checkout.
The baseline comparison starts at the last accounted commit, `a9cbd37...`, so
its later bookkeeping is charged once. No economic changes occurred between
that commit and this batch's implementation base `ff9112...`.

Astra's independent review recommends changing only `managed_issue.prf` and
`managed_burn.prf` from 0.60 to 0.70. Their semantics and refinement components
remain 0.60 and 0.40. Initial-only trace preservation justifies this modeled
command proof band; generic transfer already had 0.70 proof credit. Root accepts
that narrow recommendation. W07 delivery, W09, shared formal rows, other
capabilities, routes, exclusions, weights and uncertainty classes are unchanged.
The constructor is useful implementation, without a universal runtime theorem
or a mounted publisher that would justify a higher delivery band.

| Fixed rubric | Before | After | Change |
|---|---:|---:|---:|
| Full V3 central estimate | 23.369% | 23.369% | 0.000 pp |
| Formal core central estimate | 20.981% | 21.038% | +0.057 pp |
| Formal low/high scenarios | 15.151–27.067% | 15.208–27.124% | +0.057 pp |

V3 low/high remains 16.113–31.447%. Formal legacy-donor-zero sensitivity rises
15.423→15.480%; V3 remains 21.697%. Unknown-evidence-as-low remains 22.889% V3
and moves to 21.038% formal. These are judgment scenarios, not confidence
intervals, elapsed-work fractions or release qualification. The denominators
remain 103 capabilities, 12 lanes, four routes and four exclusions. Closure
counts remain 0/14 workstreams, 0/12 lanes, 0/4 routes, 0/12 value-movement gates.

Replay the two compact, complete calculator inputs with the unchanged tool:

```bash
python3 tools/v3_progress_assessment_calc.py tests/evidence/v3_custody_trace_assessment_before_20260909.json
python3 tools/v3_progress_assessment_calc.py tests/evidence/v3_custody_trace_assessment_after_20260909.json
```

They inherit the original source-pinned assessment and retain every score row.
The unchanged productivity reporter requires complete endpoint score inputs;
these data snapshots receive no product-completion credit.

## Contribution cost and quality

The complete accounted range `a9cbd37...c61f536...` adds 2,830 and removes 6 lines:
212/6 runtime, 537/0 proof (including the independent Lean controls), 1,525/0
tests, 473/0 data and 83/0 documentation; zero new tooling. The implementation
commit itself adds 2,694/removes 6. Subsequent assessment/mutation/accounting
artifacts are outside that measured endpoint and must be charged in the next
range. Line volume earns no score credit.

Opus implemented the two constructors and language-specific tests. Root reviewed,
integrated and implemented the theorem/prover-input path; independent Astra
supplied mathematical review and concrete controls, and Daybreak supplied
security review. Opus's 20 Python and 14 Rust cases passed their first execution.
Root repaired its own rejection-code expectation, opaque-context test fixture
and type narrowing; it corrected Opus's replay-sort comment and Rust formatting.
No runtime economic repair or guard weakening was needed.

The CLI reported 2,031,567ms for Opus, 173,204 output tokens, 218 uncached input,
409,174 cache-creation input and 24,292,189 cache-read input tokens. It also
reported a small Haiku helper call, retained separately in the contribution
manifest. These are CLI observations, not independent provider accounting.
Its $20.5708085 total is a list-price equivalent, not a confirmed charge.
Actual billed cost and root/builtin-agent resource observations remain unknown.
This Max run was expensive for a bounded constructor task; use high/xhigh for
similar implementation and reserve Max for difficult proof/search work, with
short source packets, required fixture data and confined test commands. This
worker lacked tests/data and shell execution; future packets should provide
those needed inputs and mechanical feedback, retaining independent acceptance.

The next delivery boundary is custody guest/profile-role qualification and a
real receipt, followed by current-store publication with exact retry/recovery.
Do not count this model trace proof as replay-consumption or publication proof.
