# Context Drift Prevention and Re-entry Protocol

Status: **mandatory for implementation and review**

The authoritative memory for this work is this versioned repository packet.
Chat summaries, model memory, PR descriptions, and review prose are navigation
aids. They cannot override the packet.

## 1. Mandatory triggers

Run this protocol before further editing after any of these events:

- context compaction, resumed session, or model replacement;
- branch switch, rebase, cherry-pick, conflict resolution, or manual rebuild;
- dependent-PR start or parent-head change;
- edit to a shared authority helper, schema, codec, or registry;
- peer-review finding that exposes a new accepted input;
- failed canonical/root parity;
- generated-reference refresh;
- claim that a PR is ready, green, mergeable, or complete;
- more than one working day without an exact-head checkpoint.

## 2. Re-entry sequence

Perform these steps in order.

### Step 1: establish exact source

Record:

```text
repository
branch
HEAD
base HEAD
merge base
git status --short
active PR number and current GitHub head
```

If local HEAD and GitHub PR head differ, stop. Select one exact source before
review or implementation.

### Step 2: reload the design lock

Read, in order:

```text
README.md
DECISIONS.md
ASSURANCE_FACTORIZATION_ADDENDUM.md
AUDIT_FINDINGS.md
COMBINATOR_CONTRACT.md
PR477_STATE_SCHEMA.md
PR478_AUTHORITY_EFFECT_SCHEMA.md
TEST_MATRIX.md
TEST_MATRIX_PR477_PR478.md
IMPLEMENTATION_RUNBOOK.md
requirements.json
```

Also read applicable `AGENTS.md` overlays. Do not rely on remembered versions.

### Step 3: bind the packet

Produce a deterministic packet receipt that contains every packet-relative
file path and SHA-256 digest sorted by path. Record the aggregate receipt hash
in the work log and final handoff. A packet edit invalidates the prior receipt.

The receipt is evidence of the design version read. It does not prove that the
implementation satisfies it.

### Step 4: reconstruct the requirement table

For every active requirement, fill:

| Field | Required content |
|---|---|
| Requirement ID | exact ledger ID |
| Source | packet file/section and source head |
| Positive requirement | required semantic property |
| Forbidden mechanism | concrete implementation pattern that violates it |
| Code binding | exact current file/symbol |
| Status | `SATISFIED`, `VIOLATED`, or `UNVERIFIED` |
| Witness | minimized counterexample or structural proof |
| Evidence | test/checker/proof command and artifact |
| Claim impact | exact claim that stays blocked |

Unknown is `UNVERIFIED`. Do not infer `SATISFIED` from a nearby test or a
similarly shaped implementation.

### Step 5: run the hard-stop scan

Search the entire mounted authority path, including callers and consumers, for:

```text
Any -> Any authority functions
copy, deepcopy, pickle, copy protocols
reflective dataclass or enum admission
broad isinstance at declared authority types
generic Mapping, Sequence, Iterable, set, or frozenset admission
mutable-base inheritance for committed values
object.__new__ constructor bypass
unbounded recursive traversal
unregistered records, enums, events, intents, or perps variants
canonical encoder detached from the owned type
ambient clock, environment, global, filesystem, network, or random reads
dependent work built on an unreviewed foundation
```

Any match is a review target. Any match on the authoritative admission path is
a hard stop unless the packet explicitly permits it.

### Step 6: replay negative and parity evidence

Run the narrow tests and static checker before editing. After editing, rerun
them and the mounted consumers. Compare canonical bytes, state/support roots,
effect hashes, signing bytes, and rejection codes at the exact head.

### Step 7: independent read-only drift review

For these critical surfaces, a separate reviewer or subagent reads the packet,
exact diff, and mounted callers without editing. It returns the table from Step
4 and deliberately searches for a design-level mismatch rather than only code
defects.

The implementer must reconcile every `VIOLATED` or `UNVERIFIED` row before
asking for merge approval.

## 3. Checkpoint receipt

Each implementation checkpoint returns a machine-readable object with this
minimum shape:

```json
{
  "schema": "zenodex/fcis-context-checkpoint/v1",
  "repository": "TheDarkLightX/ZenoDEX",
  "branch": "",
  "head": "",
  "base_head": "",
  "spec_packet_sha256": "",
  "active_requirements": [],
  "satisfied_requirements": [],
  "violated_requirements": [],
  "unverified_requirements": [],
  "commands": [],
  "artifacts": [],
  "design_deviations": [],
  "production_claim_status": "blocked"
}
```

The validator rejects duplicate IDs, unknown IDs, stale heads, missing packet
hashes, unclassified active requirements, and `production_claim_status` other
than `blocked` during these PRs.

## 4. Design-change protocol

An implementation agent cannot silently change the design. A proposed change
requires:

1. a new decision ID and rationale;
2. exact requirement/test/claim impact;
3. a minimized witness showing why the existing decision is impossible or
   unsafe;
4. alternatives considered;
5. user or designated design-owner approval;
6. packet version and aggregate hash update;
7. fresh independent drift review before coding resumes.

Until approval, implementation stops at the contradiction. Code is not an
implicit decision record.

## 5. Implementation-agent working rhythm

Use short verified slices:

```text
read requirement IDs
write minimized failing evidence
implement only those IDs
run narrow tests and checker
record checkpoint
request review
```

PR #477 stops for review before #478 begins. #478 rebases onto the reviewed
final #477 head and reruns #477 evidence before adding code.

## 6. Independent drift-review prompt

Give the reviewer this prompt:

```text
Perform a read-only context-drift audit. Read every file in
docs/specs/fcis_authority_snapshot_v1 and the exact candidate diff plus mounted
callers. Reconstruct each active requirement independently. For every row,
return Requirement ID, source, positive requirement, forbidden mechanism,
exact code binding, SATISFIED/VIOLATED/UNVERIFIED, minimized witness, required
evidence, and claim impact. Search specifically for a smaller or broader
accepted type language than the design, caller-controlled behavior during
admission, lost phase distinctions, unstable rejection precedence, stale
stack ancestry, detached canonical encoding, and tests that cover examples
instead of the accepted language. Do not edit files. Do not accept the PR
description as evidence. Pin all conclusions to the exact SHA.
```

## 7. Merge-readiness rule

A PR can be presented for final peer review only when:

```text
clean exact head
correct reviewed ancestry
packet receipt recorded
all PR-scoped requirements classified SATISFIED
all required negative tests retained
canonical and root parity passed
mounted consumers passed
static checker mutation tests passed
independent drift review has no unresolved violation
GitHub checks apply to the same exact head
production claim remains accurately blocked where wider obligations remain
```

Mergeability reported by GitHub is necessary operational information. It is not
semantic approval.
