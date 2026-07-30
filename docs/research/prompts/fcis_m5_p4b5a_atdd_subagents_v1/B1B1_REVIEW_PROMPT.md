# B1B-1 exact-head review prompt

```text
status: compiled candidate
prompt kind: independent exact-head falsification
visibility: implementation review packet
compiled from: FCIS M5-P4B5A ATDD execution contract v1
execution authorized: read-only review
local commit authority: false
push, PR mutation, publication, and external messaging authority: false
terminal condition: one closed verdict over one exact implementation packet
```

## Role

Perform an independent, falsification-first review of one exact B1B-1
implementation head. Do not repair the target during the review.

## Required inputs

```text
exact implementation commit
documentation-only packet commit that is exactly one child of the implementation
source manifest:
  docs/research/prompts/
  fcis_m5_p4b5a_b1b1_implementation_review_v1/SOURCE_MANIFEST.sha256
builder:
  python3 -m tools.build_fcis_b1b1_implementation_review_packet --check
complete implementation diff gate:
  python3 -B tools/check_fcis_m5_p4b5a_atdd_contract.py --assigned-id ATDD-B1B1-009 --diff-base 1665e788a4c4daf43982262c307d0c04b914d89b
approved Revision 3.4 target and packet identities
ATDD acceptance matrix
documented reproduction commands
```

Verify all identities from repository bytes before trusting the packet.

## Scope

Review only the assigned repository, exact worktree, manifest paths, and changed
files. Do not search broader directories or unrelated temporary workspaces.

## Falsification targets

At minimum:

1. approved-source drift or replacement;
2. undocumented `PYTHONPATH` or other hidden setup;
3. unknown, missing, duplicate, or trailing carrier fields;
4. Boolean-as-integer, negative, and U256 overflow admission;
5. surrogate, identifier-bound, and digest-form violations;
6. Python/Rust byte or root mismatch;
7. admission-to-authority promotion;
8. bare-header transition or anchor-to-pin conversion;
9. premature state, transition, receipt, bundle, proof, publication, or mount;
10. runtime reachability from the three carrier types;
11. stale or self-inconsistent source manifest;
12. an acceptance claim without an executable killing test.

Mutants must preserve valid types and recompute unrelated outer hashes whenever
possible. Report exact witnesses.

## Required verdict

Choose exactly one:

```text
APPROVE_B1B1_EXACT_HEAD_UNMOUNTED
REVISE_B1B1_EXACT_HEAD
REJECT_B1B1_SCOPE_VIOLATION
```

Even after approval, B1B-2 remains blocked until its separate source-bound
design receives approval. The phrase `exact-head` means the reviewed commit
itself, with no unreviewed descendant.

## Required output

```text
Exact target and manifest:
Commands run:
Acceptance cases:
Falsification results:
Scope and reachability:
Cross-language parity:
Unrun gates:
Non-claims:
Verdict:
Smallest safe next checkpoint:
```
