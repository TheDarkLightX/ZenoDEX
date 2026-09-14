# ZenoDEX V3 contribution and delivery reporting

Status: advisory engineering account. No completion or publication authority.

Latest recorded repair: `d8041717…` → `0e13f0e37…`, bounded lifetime in
both legacy JSON verifier ports. [Scoped evidence](../../tests/evidence/legacy_verifier_lifetime_v1_20260913.json)
records the reproduced failures, 83 focused/102 native passes (two proof skips),
seven killed mutants and passing critical/boundary gates. Independent review
passed 30 lifecycle tests and found no blocker. Root and reviewer are recorded
separately; exact serving-model identifiers and resource totals are unavailable.
Both operate as Codex/GPT-6-family agents. No Fable model request was sent.

The implementation is +475/−65: runtime +71/−56, tests +220/−9, and
required test evidence +184/−0. The preceding +410/−1 account update and
the following 144-line evidence/continuity record count once as support.
Source correspondence uses the evidence's explicit candidate commit. The
assessment remains **NOT_RESCORED**; this repair changes no economic transition
or formal proof. Full AS07, genuine margin receipts and independent
finality/delivery remain open. This manifest append itself receives no product
credit and should be carried as support in the next batch.
The reporter passes against baseline manifest `d8041717…`, preserves its
existing entries and matches this repair/review evidence to `0e13f0e37…`.

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

## September 12 integrated coordinator delivery

The coordinator bundle `afb5fd52…`→`244c50eb…` records one shared delivery:
ordered complete outcomes, constructor/policy preservation through actual
accepted/rejected histories, full finite runtime correspondence, and adversarial
independent replay. It adds 3,470 lines and removes 12. Root owns integration;
Opus drafts, Aristotle's three fixed proof bodies, native reviews and unsuccessful
Luna fixture reuse are retained in the contribution account. Fable supplied no
new work in this integration turn.

The [reviewed amendment](../../tests/evidence/custody_coordinator_bundle_review_20260912.md)
moves the carried estimates to 21.169% formal core (+0.066 pp) and 23.969% V3
(+0.100 pp). The previous assessment supplies the before endpoint without another
snapshot copy. The accompanying assessment/evidence/continuity changes are
support-only; their line growth earns no second delivery increment.

[Sanitized usage](../../tests/evidence/custody_coordinator_worker_usage_20260912.json)
records the earlier Opus run's 390,084 output tokens, 11,863,139 input tokens
including cache rereads, and 4,111,855 elapsed milliseconds. Output includes
provider-reported reasoning; these are neither accepted-source tokens nor a
per-model productivity score. Its terminal status was an execution error after
interruption and its drafts needed parent repair. One auxiliary provider call is
listed separately. Actual billed cost, native and Aristotle resources, and
exclusive development time remain unknown. The Git checkpoint interval is
2h03m21s and overlaps research, reviews and worker activity.

Fixture/harness reuse reduced the two drafts from 1,784 to 1,351 lines while
strengthening their oracle. Correct independent replay catches the coherent
recipient state/effect reroute. The remaining value blocker is genuine current
guest/receipt qualification and broader runtime refinement, alongside other
lane obligations. The missing historical claims-registry evidence remains open.

The reporter requires score subjects to equal batch endpoints. Its coordinator
scoring interval therefore starts at the last adopted source `0f14e8dc…`, and
supersedes the preceding admission-evidence-only batch. That retains the existing
before assessment and counts intervening metadata once. Historical records remain
in the manifest. The broader interval's LOC includes earlier support work; the
new implementation alone remains the separately reported 3,470 additions and
12 removals. No score or runtime change is attributed to that older metadata.

Append-only replay now validates **100 contribution records and 25 active
batches**, with one preserved superseded support batch. All referenced blobs
match; there are no overlapping, duplicate or divergent active ranges. The
reporter reproduces the +0.066 pp formal-core and +0.100 pp V3 transition.
Replay with `--baseline-manifest-commit afb5fd52cae91077276c36653dfe95d5e163ecd9`.
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

# September 12: perps margin-account lifecycle delivery

Implementation `e97d6f4d…` → `88c9f27d…` adds 936 lines and removes two: 308 proof
lines and 628/2 test/transport lines, with no economic runtime edits. Root Astra
implemented; native Astra supplied mathematical review and Daybreak reviewed
security, mutation quality and the stale-golden provenance. No external Claude,
Fable, Opus or Aristotle job was launched for this batch. Individual native model
token/cost/elapsed counters are unavailable and remain unknown.

The [delivery account](../../tests/evidence/perps_margin_lifecycle_v1_20260912.json)
records eight final formal/differential/mutation tests, 49 Python runtime tests,
18 Rust margin tests and the matching Rust coordinator vector. Six single-site
runtime mutants return typed accepted results that the independent oracle
rejects. Failed proof/probe drafts, serializer setup and the inherited golden
failure are included; none receives delivery credit. Completed duplicate Cargo
caches totaling 323,985,990 logical bytes were removed after ownership/structure
and active-process checks; final replay caches and logs remain local.

The reviewed gain counts once: formal +.050 percentage points and V3 +.100.
The existing fixed-rubric before subject is `244c50eb…`; its intervening
metadata-only interval is superseded in the contribution manifest by this
longer scored interval. Keep the exact new implementation count
above separate from that carried support work. The same two margin capabilities
remain partial; complete-market refinement and genuine publication remain open.

Manifest validation against `e97d6f4d…` passed: prior prefix preserved, all 266
referenced blob occurrences and 70 integer observations verified, 103 contributor
records and 26 active batches. The shared reviewed gain counts once. The 1,611
lines of evidence/assessment/continuity support in `26057f38…` receive no extra
credit; this final manifest/report append is a further support tail for the next
committed interval.

## September 12: complete perps market delivery

New implementation `321d4d032`→`7386fa2ea`: +638/−17, with proofs +385/−4,
tests +253/−13 and no economic runtime changes. Root Astra implemented and
integrated the proof; Luna Max implemented bounded full-market tests; native
Astra reviewed mathematical scope and scores. The attempted Daybreak follow-up
hit the thread limit and produced no verdict. Native token/cost/exclusive elapsed
counters remain unavailable; no remote or external-model job ran.

One shared reviewed gain: formal +.078 points, V3 +.100. Source-bound final
evidence includes ten fresh passing tests, seven killed semantic mutants and
three required admitted-state witnesses. Failed drafts/setup and assessment
cache repairs are retained in the delivery evidence. The existing after-input
is revised with a Git-pinned predecessor instead of duplicating 1,199 lines.
Support and carried metadata count once, with no automatic product credit.

Manifest validation against `321d4d0325e0f0c8f8304e1ff67678084814b1e4`
passed with the prior prefix preserved and the shared gain counted once.
The first invocation used an abbreviated baseline SHA and rejected before
acceptance; the corrected full-SHA invocation passes. There are 107 recorded
contributions/attempts and 27 active batches. Support metadata adds306/removes47
through `8810e75e7`; this manifest/report tail is further unscored support.
Three completed duplicate Cargo targets, 336,427,271 logical bytes, were removed
after exact path/marker and active-process checks. Final gate artifacts and
source/log/JUnit evidence remain available.

## September 13: connected margin claim lifecycle

Implementation `2f1c0e05…` → `417ec94a…` adds **2,567 lines**, removes none:
685 runtime, 411 Lean, 1,350 tests and 121 specification. The shared delivery
connects deposit, drain, ordinary transfer, refill and close through the V2
checker with fresh claim episodes and synchronized margin/asset lane roots.
Root Astra supplied 1,086 lines; Luna supplied 694; Astra's reviewer supplied
787 proof/test lines, independently inspected by root. Counts describe retained
source, not tokens generated or individual productivity rates.

[Evidence](../../tests/evidence/perps_margin_global_v2_20260913.json) and
[review](../../tests/evidence/perps_margin_global_review_20260913.md) retain
53 focused tests, the broad critical gate, 11 typed theorem consumers and 115
finite Python/Lean cases. Unsupported consumed-object IDs and mutable result
aliases were found and repaired with retained regressions. Rust is undergoing
separate review and receives no credit here. Universal runtime refinement,
authenticated receipts and publication remain open.

The reviewed shared gain counts once: **formal +0.122 percentage points** and
**V3 +0.070 points**, reaching 21.419% and 24.239%. Only margin deposit and
withdrawal change. Metadata commit `51c20a93…` adds 357/removes 21 and earns no
additional credit. The scored interval begins at the previous assessed source
`7386fa2e…`; it supersedes the previous evidence-only batch and includes its
support and intervening contribution accounting once. The reporter validates
the unchanged manifest prefix at `2f1c0e05…`.

Seven new contribution records include native integration, implementation and
review, an earlier Opus architecture review, the rejected Daybreak launch,
blocked new Opus disclosure and failed Fable availability probe. The earlier
Opus record reports 432,107 ms, 32 uncached input tokens and 33,055 output tokens;
its 83,425 cache-creation and 639,265 cache-read tokens remain separately named
in the source evidence. Fable's generic probe lasted 5,656 ms and returned a
quota error without running a model. Other per-model time, tokens and actual
cost remain unknown. Test durations are not charged as exclusive model work.

## September 13: Rust margin counterpart and actual correspondence

Implementation `e95e897c…` → `22e330b4…` adds **2,764 lines** with no deletions:
1,331 runtime, 1,174 tests including transport, 18 configuration, 218 lockfile
and 23 documentation. The automatic report classifies the 365-line Rust example
as runtime by path/suffix; the manual split labels its actual test-only role.
[Evidence and independent review](../../tests/evidence/perps_margin_rust_v2_20260913.json)
pin 37 shared complete-output cases, 60 combined Python tests and six Rust tests.

Luna implemented the Rust counterpart and transport. Root supplied critical
integration, the height repair and actual Python comparison. Astra independently
reviewed implementation and evidence. The initial Cargo-only pytest wrapper
was insufficient and was replaced. Review repaired a maximum-height rejection
mismatch, a synthesized rejection-root observation and boolean/float integer
aliases in the comparison. Those corrections are recorded with the delivery;
there is no extra repair credit. Native per-model resources remain unknown.

The reviewed refinement-only gain is **formal +0.021 percentage points**, reaching
**21.440%**; V3 stays **24.239%**. No new mounted workflow or proof theorem was
added. The scored interval starts at the previous assessed `417ec94a…` and
supersedes its evidence-only batch, carrying prior support once. Evidence commit
`22b459867…` adds 213/removes 22 and earns no extra credit. The reporter checks
append-only continuity against `e95e897c…`; all shared model gains count once.
The next acceptance is versioned receipt/route admission and isolated publication
against authentic current state with complete joint lane roots and claims.

After all compiler/test processes exited, root removed only this batch's
regeneratable incremental compilation cache (410,598,815 logical bytes).
Compiled test/parity binaries, libraries, source and evidence logs remain.


## September 13: TauFold upstream verifier repair and developer handoff

[Exact source and evidence](taufold_verifier_handoff_20260913/verification.json)
record a reviewed isolated upstream patch: runtime +296/−17 and tests +573/−0.
Astra supplied architecture, independent real-proof/transport controls, integration
and two review repairs. A separate Astra agent reviewed the final source.
Claude Opus 5 high implemented the executable snapshot and bounded-I/O/parser
changes. This is W03/W06 support; the ZenoDEX runtime is unchanged and the
assessment is **NOT_RESCORED**. Shared support counts once.

The initial Opus Max attempt produced no artifacts after two output-token-limit
continuations and was stopped after 1,854,925 ms of launcher elapsed time.
Its token/cost totals are unavailable. The two successful high runs report
285,109 and 608,181 ms; 20 and 42 uncached input tokens; 23,171 and 49,056 output
tokens. Cache creation/read counts and auxiliary Haiku usage remain separately
identified in the sanitized record. Provider list-price estimates are not actual
billed costs. Native Astra resources remain unknown. No Fable or Runpod was used.

Initial tests exposed fixture cleanup errors; integration repaired empty-request
and late-completion bugs. An independent fixture's missing native newline was
corrected; sandbox execution denial required approved host replay. Final controls
pass without weakening failed baselines. The inherited claims-registry missing
file remains unresolved. The next acceptance is authenticated current-state
input binding and existing publication integration, with full economic receipts.

Handoff commit `157533341…` adds 1,733 packaged artifact/probe/documentation
lines. Its 938-line patch represents the upstream source delta above; those
counts must not be added as two implementations. The automatic classifier calls
the 218 replay-probe lines runtime because they are Python; they are verification
tools, not mounted economic code. The existing reporter accepts seven new run
records and one unscored support batch, preserving the manifest prefix at
`4247e619…`. This contribution-account append is additional unscored metadata.


## September 13: independent TauFold V2 delivery review

[The review](TAUFOLD_V2_FOUNDATION_REVIEW_20260913.md) pins the delivered
manifest and fresh evidence. Root Astra replayed 86 source pins, 12 external
pins, eight core groups/8,480 Python vectors and SMT/generated-source checks;
a separate Astra agent reviewed the core, guest, host and reservation adapter.
No external-model calls, builds or provider resource observations were made.
Native per-model time/tokens remain unknown; 69.045 seconds is test runtime.

Root found a reintroduced deadline failure in the successor transport and
retained a failing regression plus an unapplied +4/−1 upstream repair candidate.
Late completion rejects after repair and an ordinary exchange succeeds. The
source-owner's real-receipt/process gates remain required. Verifier binary
location is pending, so original Rust/native/browser/receipt results were not
reclassified as fresh replays. This is `NOT_RESCORED` review/repair support;
no ZenoDEX economic runtime changed and no V3 score or gate credit follows.

Review commit `fd1776504…` adds 178 lines: 56 executable regression lines
and 122 review/patch/account lines. The upstream candidate itself is +4/−1;
packaging is not a second implementation. Two native Astra contributions and
one unscored review batch are appended. The deadline finding is reopened for
the newly delivered implementation until its owner integrates and qualifies
the repair; the earlier subject's retained passing result remains historical.

## September 13 joint margin publication

The [source-bound delivery](../../tests/evidence/perps_margin_publication_v2_20260913.json)
records implementation `51cb8e8a` → `6a4a806db`: **+3,246/−67**, including
**+1,442/−58 runtime**, **+1,719 tests**, **+75/−7 specification** and **+10/−2
inherited-baseline metadata**. No proof or dependency source was added.

One fixed isolated store now processes the connected margin/transfer lifecycle,
with claim continuity, current authority, exact retries and PRE/POST recovery.
The reviewed score gain is **+0.029 V3 percentage points** and **0 formal
points**. All new receipt evidence uses protocol fixtures; no production gate
closed. The final suite passed 195 focused tests plus the existing broad gates.

Contributors: root integration, two reused native implementation workers and
independent Astra review. Exact identities for the two inherited workers are
unknown. A requested Terra Max spawn failed at the harness thread limit and
produced no code. Initial fixture errors, root test-observer corrections and
one redundant worker legacy gate are retained in the account. Provider token,
exclusive time and billing records remain unavailable. Shared delivery counts
once. The follow-up evidence and reporting edits receive no additional credit.

The append-only manifest replay against `51cb8e8a` passes and records five
contribution attempts for this delivery, including the failed spawn. Prior
review bookkeeping and this delivery's evidence are separate support batches.
This manifest append follows the accounted `301a4389` evidence commit and must
be carried once into the next code-value range.


## September 13: attack-surface goal and verifier lifetime repair

The approved [plan](../ZENODEX_ATTACK_SURFACE_REDUCTION_PLAN.md) is an active
V3 workstream with no token cap. [Repair evidence](../../tests/evidence/attack_surface_repairs_20260913.json)
pins `be7dcd006` → `b5c55c18d`: runtime +17/−2, tests +84/−0, plan/continuity
+151/−0. Root Astra implemented/integrated; Daybreak Max independently reviewed.
Provider tokens, billing and exclusive model time are unavailable. Terra Max's
separate ongoing guest task has no accepted delivery credit in this repair.

Two retained counterexamples now pass: a verifier leader could leave a child
running after return, and exact protocol completion at the deadline could
accept. The six final boundary/lifecycle cases, 41 focused tests, 108 integration
tests, 433 TCB tests and 852 critical tests pass. The existing production-boundary
posture check passes; the inherited missing derivatives checker still fails its
claims registry. An extra test handshake proposed by review was rejected after
both reviewers established the existing pipe already enforces the ordering.

This is NOT_RESCORED security repair. All full AS01-AS08 exits remain open;
no formal-core, lane or production gate credit is assigned. Group/session escape,
same-UID access and compromised hosts remain outside the repaired guarantee.
No build, proof generation, remote compute, cleanup or dependency installation
was performed for this repair. Initial 3.3 GiB availability declined to 1.9 GiB
while the batch ran; these are observations, not attribution to this batch.
The earlier `301a4389` → `be7dcd006` metadata is counted once as support.

## September 13: compiled margin guest and actual execution

Implementation `cb20c16a…` → `bb56ec4c…` adds 4,150/removes 18 lines:
743/0 runtime, 312/12 tests, 76/3 configuration, 184/0 evidence,
111/3 documentation and 2,724/0 lockfile. The existing classifier counts Rust
examples and inline tests as runtime. Lockfile entries reuse the custody
workspace's external versions; these lines are dependency pins, not new proofs.

[Execution evidence](../../tests/evidence/perps_margin_guest_execution_v2_20260913.json)
records 44 native Python cases, seven pure Rust tests, twelve compiled workspace
tests and nine actual guest/verifier tests. The unchanged two-root journal now
comes from the measured guest over connected deposit, drain, refill and close.
Malformed/unauthorized guest inputs produce no journal. Actual measured Python
verifier launch rejects invalid receipts. No genuine receipt was produced.

Root implemented, simplified, repaired and verified directly after the user
stopped delegation. Terra's partial draft and Astra's unfinished review are
recorded as cancelled; neither receives independent-review credit. Draft compile,
canonical-order, doctest, lockfile and nested Clippy issues were repaired with
passing final gates. Provider tokens, exclusive model duration and billing are
unknown; test times do not measure model work. Shared delivery counts once.

The batch is **NOT_RESCORED**. AS02 next requires genuine receipts for the
publisher's exact selected context and current-store admission. The preceding
repair-accounting interval is carried once as support. This evidence/report
append earns no further product credit.

Manifest replay against `cb20c16a54ade99435a31c93c33cf01ad40b8ed6` passes with
the prior prefix preserved. Execution source pins, complete hygiene pins and
the external lockfile package-set comparison pass. The inherited claims-registry
failure remains: missing `tools/check_derivatives_authorization_matrix.py`.

## September 13: exact margin proving workload

`ac54d54d…` → `0786c161…` adds 605/removes 10 lines: 209 tooling, 197/10
tests, 107 evidence and 92 documentation. No economic runtime or formal-proof
code changes. [Source-bound evidence](../../tests/evidence/margin_proving_workload_v2_20260913.json)
pins the three exported inputs, measured execution and native boundary cases.
Root implemented and reviewed directly; no independent-model verdict is claimed.

The packet rebuilds profile/state/signature roots around the measured BLS
endpoint and uses the rebuilt margin guest. Seven focused tests pass; two
genuine-receipt tests explicitly skip. Thirty existing publisher/role tests pass;
all three old default command frames and signatures remain byte-identical.
Review reproduced a FIFO hang and symlink acceptance in the draft acquisition
helper. Reuse of the existing bounded regular-file reader repairs both; the
failed and passing observations are retained. These repairs receive no separate
delivery credit. The ordinary formatter repair is also included in the batch.

Actual guest execution totals 22,750,173 user cycles over three inputs totaling
20,419 bytes. These are execution measurements, not proof runtime, memory,
exclusive model duration or billed resources. No proof generation, new build,
remote expenditure or external model call occurred. Provider counters remain
unknown. A proof host has been requested for the frozen job.

This is **NOT_RESCORED**. AS02 still needs genuine proofs and publication replay;
all full AS exits remain open. The preceding 340-line evidence/account append
is carried once as support. This new record earns no extra product credit.

The existing reporter passes against baseline
`ac54d54d80e8f88519b04372c288bff8dd780e7e`, preserving its manifest prefix.
Current and committed source pins, changed-file hygiene and production-boundary
posture checks pass. These checks do not turn the two skipped proof tests into
evidence of successful publication.

## September 13: read-only historical reauthentication

`5254febf…` → `b97d2f75…` adds 690/removes 7 lines: runtime 86/6,
tests 340/0, tooling 9/0, documentation 66/1 and evidence 189/0. No economic
transition or formal-proof changes. [Evidence](../../tests/evidence/custody_history_audit_v2_20260913.json)
pins the copied-history audit, original recovery trust gap, real BLS/receipt
rejections, 21 passing focused cases with two genuine-proof skips, 108 passing
regressions, five killed source mutants and the passing critical gate.

Root implemented and reviewed directly. The draft test's incorrect successor
call and import ordering were repaired. Native launch restrictions required the
existing authorized host shell; the broad gate reused the installed development
venv after system Python lacked coverage tooling. The new hygiene declaration's
node/family errors were corrected. No new dependencies, fleet calls or remote
proving were used. Provider tokens, exclusive model time and billing remain
unknown; test/commit timings do not measure those resources.

The API reuses existing records and verifiers, closes a read-only connection
before external execution, and returns detached data. It qualifies no separate
verification host, finality source or effect destination. AS02 remains pending
the frozen remote proof job. Assessment is **NOT_RESCORED**. The preceding
292-line accounting append is carried once as support; this evidence/account
append earns no additional delivery credit. The inherited claims-registry
missing-file failure remains open.

The existing reporter passes against baseline
`5254febf8d7cf326f63b1231404346be97075770`, preserving the earlier manifest
prefix and confirming the categorized line changes. Source and hygiene pins
match the tested implementation. Mutation replay removed its temporary copies.

## September 13: native verifier containment

`26da460e…` → `5fd40f6a…` adds 488/removes 6 lines: runtime 31/5,
tests 216/1, documentation 44/0 and evidence 197/0. No economic transition,
formal proof, guest or wire format changed. The shared receipt/BLS launcher now
requires a read-only namespace containing its measured executable and four
runtime libraries. Retained native probes demonstrate denied host-file/socket
access and termination of a child that changes sessions.

[Evidence](../../tests/evidence/verifier_process_isolation_v1_20260913.json)
records 102 passing native/integration cases, two genuine-margin-proof skips,
five killed source mutants with passing controls, and the critical gate's
433 TCB plus 852 critical tests. Root implemented and reviewed directly;
independent-model review was not run. Draft launcher probes needed explicit
loader execution; the final policy removes procfs. An audit correctly rejected
a mid-run commit and passed when replayed on the stable subject. Temporary
mutation copies were removed. No heavy build or remote proving was performed.

The Claude usage check sent no model request: Fable's live weekly counter was
100%, all models 63%, and the new CLI session reported zero tokens. Provider
tokens, exclusive root duration and billing remain unknown. This batch is
**NOT_RESCORED**. Aggregate resource quotas, prover/observer containment and
independent finality/publication enforcement remain open; AS02 still needs the
prepared remote receipts. The preceding 327-line audit-account append is carried
once as support. This new evidence/account append receives no additional credit.

## September 13: standalone margin audit

`02f9729a…` → `394ddbf22…`: +308/−15, split as tooling 47/11,
tests 120/1, docs 25/3 and required test evidence 116/0. Runtime and formal
proofs are unchanged. [Evidence](../../tests/evidence/independent_margin_audit_v2_20260913.json)
records 43 passing integration cases, two genuine-proof skips, three killed
mutants and passing boundary/hygiene checks. Independent review passes; it
also rejected an unmounted fixed-quorum proposal. Root implemented directly.
The first hygiene draft needed exact parameterized killer pins; the corrected
packet passes. No heavy build or external-model request occurred. Model serving
IDs, billed resources and exclusive work duration remain unknown.

This is **NOT_RESCORED**. The command mounts existing read-only verification;
trusted checkpoint provenance/freshness, independent enforcement and the three
genuine margin receipts remain outstanding. The claims registry has an unchanged
missing-file failure. The prior 185-line accounting append and this 129/9-line
evidence append are carried once as support, with no extra delivery credit.

The existing reporter passes against baseline `02f9729a…`: its manifest prefix
is preserved, all 376 referenced blobs match, and categorized line totals agree.
### September 13: consolidated assessment of completed attack-surface work

Fable independently reviewed `6a4a806db…` through `e05f293e3…`; root accepted
four workstream edits after source inspection and calculator validation. The
[review record](../../tests/evidence/v3_attack_surface_assessment_review_20260913.json)
and scored input are stored at `2a6f06a5e56a54ffc87ffb4066a717dcd26104f1`.
Shared delivery credit is **V3 +0.560 pp**, formal core **+0.000 pp**. This
assesses earlier implementation once; the assessment itself adds no feature.
Per-batch and consolidated commit ranges overlap, so their line totals must
not be summed as independent growth.

Fable's CLI recorded 361,216 ms, 26,959 output tokens, 226 uncached input tokens,
134,626 cache-creation and 430,452 cache-read input tokens. Its $4.150343
list-price estimate is not an observed bill and is excluded from billing
rollups. A small CLI Haiku helper is disclosed in the review; root resources
remain unknown. No fleet or further proof build ran for this assessment.

The contribution reporter passed against `e05f293e3…`: prior prefix preserved,
385 reference occurrences/62 unique references hash-match, and 88 source
JSON-pointer observations validate. The existing denominator and all capability
and formal scores are unchanged. Assessment support at `e05f293e3…→2a6f06a5e…`
is +338/−29 metadata lines; the preceding +168-line account is carried once.
Current quota probes remain uncommitted, unscored failing acceptance evidence.

## September 14: verifier quotas, review repair and formal-core handoff

`3a44ff5e…` → `376625932…` delivers per-invocation resource limits with
independent scoped review: runtime 37/7, tests 346/4, support 248/12 lines.
The [evidence](../../tests/evidence/verifier_resource_limits_v1_20260914.json)
retains the initially failed cleanup control, the three review corrections,
71 focused passes and all six mutations killed. Integration and critical gates
passed on the unchanged runtime before the test-only correction. Root and the
independent reviewer share delivery credit once; exact model/resource counts
were unavailable. This batch is NOT_RESCORED. The prior 198-line support tail
and the 172/10-line evidence append are carried once without product credit.

Fable 5.1 is the primary implementer for the separate connected margin formal
proof under the user's September 14 instruction; Astra owns review and fixes.
The launch is live, with no result or formal credit recorded. Actual pre-run
usage was 2% weekly Fable and 1% weekly all models. Final usage and accepted
changes must be appended after its handback; the private coordination packet
and live CLI session are preserved. This accounting append is unscored support.

Reporter validation passes against `3a44ff5e…`: prior prefix preserved,
390 referenced blob occurrences / 63 unique references match, and 88 resource
pointer observations verify. No assessment delta is assigned.
