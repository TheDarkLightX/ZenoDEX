# O-003B evidence-pin requalification candidate

This is the preserved pre-commit candidate record. Its pending authorization
and absent-receipt statements describe that earlier snapshot. The user later
authorized creating commits and requested remote publication, then explicitly
approved including the branch's 213 earlier unpublished commits.
Use the committed V4 receipt and its checker for subsequent qualification.

Status: **PREPARED, UNCOMMITTED, NOT QUALIFIED, NOT_RESCORED**.
This record grants no production, release, settlement or value-movement authority.
No value-safety gate, capability or historical audit finding closes.

## Purpose and exact scope

Evidence pins identify the exact source bytes to which a result applies.
The immutable-ownership repair changed two historical Tau adapter pins. Merely
changing their hashes would not establish that the original bounded claim still
holds. This candidate preserves the V3 receipt and tools, replays its historical
subject, checks the reviewed successor delta and reruns the underlying static
import, route, discovery and classification predicates.

The claim is retired-bridge classification O-003B. It does not prove immutable
ownership, arithmetic, custody, transaction finality or complete value movement.
The historical audit rows and frozen spreadsheet/webpage are unchanged.

Active and candidate base HEAD is
`d20556bb1c1eab8e236e9c7c420edac809172d24`, with preserved dirty/untracked context.
The nine-file successor remains isolated; its location is in the continuity
note. Active source and the production-boundary consumer were not changed by
this batch. The active gate retains its prior `WORKTREE_SOURCE_DRIFT` refusal.
No source commit, receipt commit, push or deployment occurred.

The preserved V3 receipt SHA256 is
`bd66f99523f904821e6417c588e41b96ef9a219f573d6cc4293d671a4c165dac`.
Historical Stage A is `ac468ec83f7a85b11e70508ee9d1e525f4f7ac2e`;
receipt-only Stage B is `abea06127ae3a6cd9aca38e18314673af7cd4ffb`.
The candidate preserves their topology and ancestry requirements. V3 files and
receipt were checked unchanged against HEAD.

## Candidate and design review

The candidate adds a pure V4 derivation module, bounded acquisition/builder,
fail-closed checker, two conformance test modules and a versioned contract.
Three existing files change: the production-boundary consumer, its mocked
report tests and its historical/current scope documentation. Exactly five
legacy pinned changes are allowed: those three plus the two previously reviewed
snapshot adapters. Other legacy pinned bytes must equal the predecessor.
Adapter normalization removes only the named Snapshot imports and copy-helper
argument annotations before comparing the remaining complete syntax tree.
This does not establish universal or transitive Python semantic equivalence.

Independent Astra source review accepted the final scope and added coverage.
Review corrected an initially mistyped predecessor identity and an AST-context
comparison error. Additional targeted mypy found six annotation/alias errors;
explicit missing-annotation rejection and a type alias resolved them. No gate
was weakened. The reviewer ran no tests; root owns the combined final result.

The metrics scanner flagged the pure module above its 400-LOC heuristic. Its
single bounded derivation responsibility is intentionally retained so reviewers
can trace predecessor validation through source delta, predicate replay and
canonical receipt construction together. Acquisition and filesystem topology
remain separate modules; frozen V3 helpers are reused unchanged. The scanner
could not obtain Git-history coupling for these new files. Redflags reported
zero findings; that is triage, not safety evidence.

## Final ordinary checks

Run in the isolated candidate after the final source edits:

```bash
python3 -m pytest -q tests/test_retired_tau_bridge_closure_v4.py tests/test_retired_tau_bridge_closure_v4_shell.py tests/test_check_production_boundary.py -k 'not test_current_production_boundary_audit_passes'
python3 -m ruff check tools/retired_tau_bridge_closure_v4.py tools/build_retired_tau_bridge_closure_v4.py tools/check_retired_tau_bridge_closure_v4.py tools/check_production_boundary.py tests/test_retired_tau_bridge_closure_v4.py tests/test_retired_tau_bridge_closure_v4_shell.py tests/test_check_production_boundary.py
python3 -m mypy tools/retired_tau_bridge_closure_v4.py tools/build_retired_tau_bridge_closure_v4.py tools/check_retired_tau_bridge_closure_v4.py
python3 -m mypy
git diff --check
python3 tools/check_retired_tau_bridge_closure_v4.py
```

Results: **51 passed, one explicitly deselected**, 66.64 seconds; Ruff passed;
targeted mypy passed three new tools; configured mypy passed 25 runtime files;
diff whitespace check passed. The deselected real production-boundary acceptance
requires the actual source/receipt commits and remains mandatory. It was not
rewritten or marked passing. The final V4 checker exited 1 with `FILE_NOT_FOUND`
for the not-yet-generated receipt, `o003b_status=OPEN`, zero value-movement gates
and all authority fields `NONE`.

The positive pure fixture mixes historical Git inputs and current candidate
bytes with explicitly synthetic qualification metadata. It exercises derivation
and canonical replay only. Tiny temporary Git fixtures exercise commit topology.
Neither is a real repository qualification. Historical vulnerability witnesses,
the full critical/release suite and production qualification were not run.

## Code value and next acceptance

Nine-file candidate delta against its captured preimage: tooling +822/-5 across
four files; tests +394/-4 across three files; contract/scope docs +111/-1 across
two files. No runtime, proof, economic or dependency implementation is added.
This is assurance support justified by the concrete stale-pin refusal after
the ownership repair. Product credit and reviewed percentage-point change are
not assigned. Separate continuity/productivity records are documentation work.

Root owns architecture, shell, consumer, review and integration. A Terra Max
worker implemented the pure module and its tests; Astra provided independent
source reviews. One attempted reviewer follow-up hit a harness thread limit;
an existing reviewer completed the review. Model token/cost totals are unknown.

Next: obtain scoped local commit approval, integrate the nine reviewed files
without unrelated changes, commit reviewed source as Stage A, generate V4 from
that committed subject, and commit only its newly added receipt as Stage B.
Run the V4 checker, builder `--check`, real production-boundary acceptance and
relevant tests on those final commits. Stop on any mismatch. No push or deployment
is included. Optional PerpsState ownership and native LP withdrawal remain
separate unfinished work.

The companion `.sha256` identifies the nine candidate files. Its entries were
generated with `sha256sum` over the sorted relative paths shown in that file;
check them from the candidate root with `sha256sum -c <manifest>` before resuming.
