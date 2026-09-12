# ZenoDEX V3 contribution and delivery reporting

Status: advisory engineering account. No completion or publication authority.

The [contribution manifest](ZENODEX_V3_PRODUCTIVITY.json) connects committed
changes to existing obligations, documented contributors, review findings and
resource records. The report measures recorded work; it cannot prove that
unrecorded work did not occur or that a source record is truthful. Model review
remains advisory. The existing assessment rubric and acceptance gates remain
the owners of their respective judgments.

Generate the report from committed evidence, without running commands supplied
by the manifest:

```bash
python3 tools/v3_productivity_report.py docs/research/ZENODEX_V3_PRODUCTIVITY.json
```

After the first manifest commit, check append-only continuity against its
previous committed version:

```bash
python3 tools/v3_productivity_report.py docs/research/ZENODEX_V3_PRODUCTIVITY.json --baseline-manifest-commit PREVIOUS_MANIFEST_COMMIT
```

Replace the final argument with the full commit ID that contains the previous
manifest. The report is offline JSON. An invalid reference, altered prefix,
inconsistent assessment or duplicate credit fails with a nonzero exit.

## What is measured

| Measure | Source and interpretation |
| --- | --- |
| Progress gain | Before/after assessments checked by the unchanged calculator, with reviewed exact subjects and the same weights. Include decreases. Missing reassessment is `NOT_RESCORED`, not a measured zero. |
| Delivery and quality | Evidence-pinned, source-recorded dispositions and named confirmed/repaired/reopened findings. These are review judgments; their counts are not capability closures or independent proof. |
| Code growth | Full committed diff: added, removed and net physical lines by category, including tests, evidence, generated data and locks. Repeatedly changed paths flag inspection candidates; they do not establish churn. |
| Participation | Run IDs, model identities as recorded, roles, task kinds and risk classes. Shared outcomes count once at team level; each contributing model does not receive the whole gain. |
| Resource use | Source-recorded input/output tokens, elapsed milliseconds and cost in millionths of a US dollar, where available. Every non-null observation must match an integer at a JSON pointer in its pinned evidence. Missing values remain unknown. |
| Coverage | Unattributed batches, missing identities/provenance/resources and the absence of reconciliation against a dispatch inventory. A partial backfill cannot establish complete model coverage. |

The automated line categories use whole files. Rust implementation files include
inline test modules. The earlier [manual code-value account](ZENODEX_V3_PROGRESS_ASSESSMENT_20260908.md#code-value-account-september-9-2026)
split trailing Rust test modules into tests. The total line change is comparable;
category totals using these two conventions must not be compared silently.
Team line totals sum distinct batch diffs. Repeated edits between batches can
increase gross additions and deletions without increasing retained source size;
per-batch file counts can include the same path more than once. The initial six
batches contain 27,046 additions and 63 deletions, net 26,983, across 98 unique
paths. The single start-to-end diff has 27,021 additions and 38 deletions with
the same net change. Neither is cumulative model output.

One shared run is charged once even if multiple batches cite it. Wall time
reported for runs is not exclusive human effort or end-to-end project duration;
concurrent run times can overlap. Do not invent token costs from commit times,
model names, subscription counters or current public prices. Keep any provider
accounting convention with its source record. Unknown total spend is not zero
spend.

## Collection and review workflow

1. Before delegation or local implementation, name the existing obligation, the
   smallest acceptance change, the baseline commit and owned files. Record the
   dispatched run ID, requested model/effort and task in the coordination log.
   Preserve failed, cancelled and no-change attempts as well as successes.
2. At the end of a run, add one record using the identity actually reported by
   the execution harness. If only a family name is documented, retain that
   limitation. Preserve resource metadata when the harness exposes it; never
   export secrets, private reasoning or entire session logs to this manifest.
   Pin only the small sanitized source records needed for the measurements.
3. At integration, record the complete commit range and participating run IDs.
   Record the observed before/after behavior and its evidence, with named
   findings for defects and rework. `support_only` work must name the defect it
   repairs or the acceptance step it enables. A review without code changes
   uses the same before/after commit and earns no implementation delta.
4. Review affected assessment rows when evidence changes. Preserve the previous
   assessment; use the same fixed denominator. A reviewer reference and two
   valid assessment records are necessary for a score delta. Their hashes
   establish integrity, not independent reviewer identity or execution truth.
5. Run this reporter and inspect evidence correspondence. A replay against an
   earlier code commit remains historical even when its report was committed
   later. Keep source-recorded outcomes separate from current qualified gates.
6. Append corrections with `supersedes`; retain the earlier batch. The corrected
   batch replaces its contribution to active totals. Use the prior manifest
   commit to detect rewritten or omitted history. Reconcile listed runs against
   actual dispatch records before claiming every contributor was captured.

Version 1 freezes run records once recorded; only batches support supersession.
Do not add a second run ID to charge or reattribute the same execution. Recovering
or correcting a recorded run's identity, provenance or usage requires a reviewed
schema successor with run supersession before those corrections enter totals.
Collect final available metadata before recording each run. This limitation is
explicit in the initial backfill, whose resource values are all unknown.

For each delivery batch, give the user the reviewed score change or
`NOT_RESCORED`, the concrete acceptance gain, code delta, unresolved findings,
resource coverage and next delivery blocker. At a weekly review, compare runs
only within comparable task/risk cohorts and state coverage. This tool does not
schedule reports or rank models automatically.

Select the next work by acceptance value. If successive batches add code
without advancing the intended behavior, review the blocker and the smallest
existing solution before expanding implementation. Evidence-backed deletion or
simplification can be valuable without increasing a completion score. Support
work can also have value, but must not become a substitute for the economic
path it was intended to unblock. Neither LOC nor a composite productivity score
can establish mathematically optimal code or detect every instance of churn.

## Initial backfill and limits

The initial manifest covers the six nonoverlapping delivery batches from
`70f9157ef097384c6b48db22c254d8134f19f8f5` through
`45c3310cee9a4e4b62ba0868e5b4f4d4e6bfe44a`. It records 15 documented
contributions across Fable, Opus, Astra, Terra and Daybreak. Historical `HIST-`
IDs identify reconstructed contribution records, not recovered provider run
receipts. Exact versions for three families and complete dispatch history are
unavailable. These records must not be used as an exact census of agent calls.

Historical token, time and cost observations are absent. All six delivered
batches are `NOT_RESCORED`. The last adopted assessment remains 23.369% V3 and
20.981% formal core for its September 8 source, with the published judgment
ranges. No complete workstream, lane, route or value-movement gate closed in
this range. The four `accepted_partial` dispositions document bounded behavior
gains; the two `support_only` dispositions receive no product completion credit.

This requested reporting work is itself support work. Its acceptance condition
is reproducible collection and honest aggregation with negative controls for
inflated or missing measurements. It claims no economic or formal-core score
increase. The next economic bottleneck remains genuine custody receipt
qualification and current-store publication/recovery.

## Verification

The [retained local verification](../../tests/evidence/v3_productivity_verification_20260909.json)
pins the reviewed source and records the commands, contributors and limits.
Reporter and assessment-calculator tests passed **42/42**; Ruff and focused
mypy passed. Daybreak independently replayed eight draft defect families and
accepted the repaired reporter within its declared scope. Ordered score
checkpoints, unique usage observations, current manifest continuity, finding
lifecycles and binary changes have retained regression cases. Binary LOC is
unavailable and reported separately; competing branches cannot earn one combined
delivery delta.

The broader run passed 55 tests and failed 21 existing progress-replay tests.
Its ledger expects an older hash of
`ZENODEX_POST_CORRECTNESS_SIMPLIFICATION_20260907.md`; the current document
matches the starting commit byte for byte. That stale evidence remains open.
No old test, ledger pin or score was changed to make the run pass. Full economic,
Lean, ESSO, Kani, RISC0 and hosted CI gates were not run for this advisory change.

## Reporting implementation checkpoint

The reporting implementation is committed at
`a9cbd37dc17c5190655a557070f2d45c2ee573e7`. Its complete seven-file diff adds
2,747 lines: 1,143 tooling, 680 tests, 641 data and 283 documentation. It adds
zero economic-runtime or proof-source lines and earns no product-completion
credit. The concrete support gain is a replayable contribution account with
the inflation and continuity regressions described above.

The manifest now includes this support batch and its four recorded contributors
(Terra implementation, Astra review/integration and Daybreak review): **19
contribution records across seven batches**. Append-only replay against the
implementation commit passes. All resource observations remain unknown. The
legacy stale document pin is retained as a confirmed unresolved finding.

This checkpoint's data/documentation append follows the measured implementation
commit and is outside that 2,747-line range. Future batches should start at the
last accounted implementation commit so this bookkeeping is included once.


## Custody trace and successor delivery

The [reviewed increment](ZENODEX_CUSTODY_TRACE_DELIVERY_20260909.md) now has a
REVIEWED_DELTA: formal-core estimate 20.981%→21.038% (+0.057pp), V3 unchanged
at 23.369%, with all other scores explicitly carried forward. The existing
reporter validates 26 contribution records across 8 batches and the seven new
records (Opus, root, Astra review, Daybreak review, CLI auxiliary Haiku and two
launches rejected before model execution). Shared credit is counted once.

Five source-bound resource observations are now available. Opus input includes
uncached, cache-creation and cache-read categories; it is not a unique-source
token count. Actual billed cost, root and builtin-agent resources remain
unknown. The measured code range ends at `c61f536315191bd0a1a482a3932fdeb43009cd6f`;
later assessment/mutation/accounting data must be included once in the next
range. The compact complete endpoint inputs are required by the existing
reporter; no reporting tool or runtime framework was added.

```bash
python3 tools/v3_productivity_report.py docs/research/ZENODEX_V3_PRODUCTIVITY.json --baseline-manifest-commit ff9112b9970e4f510fcf198f7baafe149b98265a
```

## September 12 constructor and command-binding delivery

The manifest now records 93 source-declared contributions across 24 active
batches. The new delivery interval is `5e1e5a9` through `0f14e8d`: 2,091 additions,
20 removals and a reviewed formal-core delta of +0.009 percentage points. V3 is
unchanged. Preceding-checkpoint to implementation-commit elapsed time is 1h34m11s;
through the evidence/formatting checkpoint `e648560f` it is 1h49m10s. These are
Git checkpoint intervals, not exclusive measured development time.

The 19 added contribution records include five Fable main calls, their auxiliary
calls, the Opus permission probe and implementation with auxiliary calls, and
five native/root task records. Failed and discarded implementation attempts
remain in the account. Five Fable workers delivered zero accepted implementation
files; useful review findings are described separately. The provider usage file
contains only sanitized counters and outcome descriptions, not private reasoning.
Actual billed cost is unknown. A following Opus coordinator bundle is in flight
and earns no delivery credit here.

Validation against manifest commit `5e1e5a9e84b162ebfa3c0e00fcf78aef6968d38a`
preserves the full earlier prefix, verifies all 235 referenced blob occurrences
and 65 integer JSON-pointer observations, and counts the new shared score delta
once. Fourteen provider records have input/output observations; seven have elapsed
observations. Native/root resources for this batch remain unknown. The prior
199-line manifest tail is accounted once as support. Review/usage/assessment
support through `e648560f` adds 3,344 lines and removes four, with no extra score.
The current manifest/report append is a further support tail, to be counted at
the next committed delivery interval.

The next batch consolidates ordered coordinator outcomes, journal/effect binding,
aggregate resource/reprojection and runtime correspondence. Its implementation,
adversarial controls and proof review proceed concurrently on disjoint files.
No launch, documentation volume, individual lemma or repeated check increments
completion credit.
