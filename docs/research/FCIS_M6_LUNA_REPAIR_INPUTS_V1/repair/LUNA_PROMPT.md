# Repair the FCIS M6 Durable Retraction Research Packet

**Status:** candidate  
**Prompt kind:** build and verification  
**Intended use:** GPT-5.6 Luna implementation agent  
**Visibility:** repository-local  
**Contract version:** `fcis-m6-durable-retraction-luna-repair-v1`  
**Execution authorized:** yes for a clean-worktree repair, local verification,
dedicated remote draft branch, and draft PR; no merge, mount, deployment,
authority switch, or value movement

## Intent mirror

### User's real job

Turn the reviewed M6 durable-retraction research packet into an exact,
reviewable, internally consistent research implementation that fails closed at
its authority boundaries and carries only claims supported by executable
evidence.

### Desired result

Produce a repaired implementation target plus one documentation-only packet
child on a remote draft PR. Retain the durable-retraction construction, kill the
four blocking defect families, compile the Lean theorem under the pinned
toolchain, pass the focused Python/Julia/ESSO/quality gates, and keep the entire
checkpoint unmounted.

### Decision enabled

An independent reviewer can decide whether the durable-retraction research
checkpoint is safe to use as the next implementation basis for M6 R05-R11.

### Non-goals

Do not implement a production datastore adapter, runtime command path,
destination integration, R08 proof-context mount, R12 no-bypass mount, R13
whole-system accounting, migration authority switch, or value movement.

## Semantic traceability

| ID | Requirement | Origin | Status | Consequence if wrong |
| --- | --- | --- | --- | --- |
| R1 | Repair the reviewed packet before further implementation | user-stated | approved | Luna could build on refuted evidence |
| R2 | Preserve functional-core/imperative-shell authority separation | repository guidance | approved | caller data could masquerade as verified authority |
| R3 | Retain failing witnesses before repair | repository guidance and review | approved | green tests could miss the exact defect mechanism |
| R4 | Keep the checkpoint unmounted | source packet and review | approved | research evidence could become runtime authority |
| R5 | Deliver a remote, exact-head, independently reviewable packet | prior user direction and review | approved | the result could not receive reproducible review |
| R6 | Use one canonical archive and exact manifest | review-derived | inferred | reviewers could inspect different file sets |

## Exact inputs

Repository:

```text
https://github.com/TheDarkLightX/ZenoDEX
```

Exact intended base:

```text
babffa56dcbddc5886487fbb6e62740b15370000
```

Intended branch:

```text
agent/fcis-m6-r05-r11-durable-retraction-20260731
```

At review time this branch still pointed exactly to the base. Stop if that is
no longer true unless the invoking user supplies a new exact base.

Reviewed archives:

```text
fcis-m6-durable-retraction-tree.tar.gz
sha256:
3d1ac7ed5d9404cc4b293a9707502e4e4d8d714498448501b4b878d7b8afcd70

fcis-m6-durable-retraction-bundle.zip
sha256:
8e1c5cea2588682f84da2a9fe71f7e1b2bacd79143f1df12695d4542e81d9890
```

The common files were byte-identical. The ZIP alone contained
`README_BUNDLE.md` and `SHA256SUMS.txt`; the TAR alone contained the load-bearing
`lean-mathlib/lakefile.lean`. Do not silently choose one as the final packet.
Construct one canonical file inventory and explain every included file.

Normative repair inputs:

```text
REVIEW_AND_REPAIR_SPEC.md
REPAIR_TASKS.json
this prompt
the repository AGENTS.md hierarchy
the supplied packet sources
```

## Review verdict

```text
REVISE_M6_DURABLE_RETRACTION_RESEARCH_PACKET_V1
```

Evidence already independently reproduced:

```text
17 focused Python tests passed
Python bounded result:
  49 reachable safe states
  254 safe transitions
  7/7 original mutants killed
Julia output exactly matched the parsed Python result
ESSO validate passed
ESSO verify-multi passed 15/15 inductive queries
Z3 and CVC5 agreed
```

Evidence that failed:

```text
Lean 4.27 compilation
Ruff
mypy with 40 errors
exact remote packet commit and CI
```

## Blocking findings

### B1. Caller-mintable reopen authorization

The current API accepts a caller-selected `external_authorization_root` and
hashes it into `ReopenAuthorizationV1`. This binds freshness but does not prove
that an authorized external verifier produced the root.

Required law:

```text
ExternalEvidence
  -> AuthoritativeVerifier
  -> VerifiedExternalHeadAuthorization
  -> ReopenAuthorization
```

Bind:

```text
canonical snapshot root
committed-state root
authority-state root
authority epoch
deployment/configuration identity
verifier or signer-set identity
external statement root
activation or expiration bounds when applicable
```

A self-selected digest must never construct a controlled token.

Python privacy is a misuse barrier, not an unforgeability proof. Reconstruct or
reverify the witness at the shell boundary that owns the external verifier.
Keep the research model conditional on that verifier premise.

### B2. Forgeable destination acknowledgment

The current deterministic receipt-root helper lets a caller calculate the
expected digest and construct an acknowledgment without delivery.

Required law:

```text
RawDestinationResponse
  -> DestinationVerifierAdapter
  -> VerifiedDestinationReceipt
  -> AcknowledgeCommittedOutboxRow
```

Bind:

```text
effect ID
destination
payload root
destination receipt root
adapter/verifier profile identity
destination idempotency identity
```

A well-shaped, locally recomputed digest remains untrusted.

### B3. Open type, width, and resource boundaries

At minimum repair:

```text
OutboxRowV1.ordinal:
  exact int, not bool
  u32 domain

CrashPointV1:
  exact enum
  string aliases rejected

fixed-width encoders:
  range validation before serialization

durable row tuples:
  explicit per-table and total canonical-byte budgets
  reject before expensive reconstruction

host overflow:
  typed reject as defense in depth
```

Retain the witnesses:

```text
ordinal = 2^32
ordinal = 2^40
ordinal = True
crash_point = "BEFORE_LINEARIZATION"
oversized redundant durable tables
```

The string crash point must not silently commit.

### B4. Lean theorem does not compile and models the wrong relation

The current Lean file uses total `reopen : D -> A`; runtime reopen is partial.
Use:

```text
reopen : D -> Except Reject A
```

or an equivalent accepted-layout subtype that preserves rejection semantics.

Prove at least:

```text
reopen (encode a) = Except.ok a
encode injectivity
successful normalization idempotence
authoritative fixed-point characterization
same-commit observational stutter
changed-head authorization invalidation
PRE/POST crash alternatives
stable-effect replay idempotence under its declared observation
```

Lean 4.27 and the pinned mathlib must compile the exact declarations. No
`sorry`, `admit`, user `axiom`, `unsafe`, or `sorryAx` dependency is permitted.

## Required implementation order

Follow `REPAIR_TASKS.json`:

```text
L00 exact-source preflight
L01 failing witnesses
L02 reopen authority
L03 destination acknowledgment
L04 bounds and typed rejection
L05 Lean repair
L06 cross-artifact synchronization
L07 focused gates
L08 exact remote review packet
```

L02-L04 may proceed independently after L01. L05 may proceed independently
after L01. Do not update public claims until all affected gates finish.

## Functional architecture

Keep this boundary:

```text
imperative shell:
  acquire durable bytes
  obtain store-current root/version
  authenticate external head grant
  verify destination response

deterministic core:
  strict typed admission
  canonical reopen and fixed-point check
  retry classification
  candidate and effect identity
  migration transition legality
  typed accept or reject

imperative shell:
  atomic compare-and-swap publication
  idempotent external delivery
  verified acknowledgment persistence
```

The shell must not reconstruct authority, identity, effects, or migration
semantics already decided by the core. The core must not treat raw shell facts
as verified witnesses.

## Failing evidence first

Before each repair, add a permanent deterministic test or model mutant that
fails on the reviewed implementation for the intended reason.

Required negative families:

```text
self-selected reopen root
cross-snapshot reopen token
cross-deployment or cross-epoch token
changed-head stale token
forged destination hash without delivery
cross-effect, destination, payload, or verifier receipt
u32 maximum plus one
Boolean integer alias
string crash-point alias
oversized durable tables
partial reopen failure
ESSO unauthenticated authorization action
```

Every rejection must preserve byte-identical durable pre-state and produce no
new outbox effect or authority witness.

## Cross-artifact synchronization

Update together:

```text
src/core/fcis_durable_retraction.py
tests/core/test_fcis_durable_retraction.py
experiments/fcis_durable_retraction_bounded_search.py
experiments/fcis_durable_retraction_bounded_search_result.json
experiments/julia/fcis_durable_retraction_oracle.jl
formal/esso/fcis_durable_retraction_v1.yaml
lean-mathlib/Proofs/FCISDurableRetraction.lean
lean-mathlib/lakefile.lean
the workflow
research report
Research Kernel ledger
Morph/LEAP records when their claims change
Luna taskbook and task graph
```

The bounded Python explorer uses `MAX_DEPTH = 14`. Correct prose that says the
complete 49-state result was obtained through depth seven. If a depth-seven
subset is useful, name its actual separate count and scope.

The existing 105-task JSON targets R02-R13 and program composition. Describe
that scope accurately or encode R01 explicitly.

Use only these positive labels until stronger evidence exists:

```text
RESEARCH_HYPOTHESIS
PYTHON_REFERENCE_MODEL_TESTED
ESSO_INDUCTIVE_MODEL_VERIFIED_BOUNDED
PYTHON_JULIA_BOUNDED_PARITY
UNMOUNTED
```

`PROVED_CONNECTIVE_MATH` becomes available only after the exact theorem
statement, assumptions, toolchain, compile result, and dependency audit pass.

## Acceptance commands

Discover and obey all applicable `AGENTS.md` files first. Run the repository
style map and security triage on the exact changed files.

Python:

```bash
python3 -m py_compile \
  src/core/fcis_durable_retraction.py \
  tests/core/test_fcis_durable_retraction.py \
  experiments/fcis_durable_retraction_bounded_search.py

python3 -m ruff check \
  src/core/fcis_durable_retraction.py \
  tests/core/test_fcis_durable_retraction.py \
  experiments/fcis_durable_retraction_bounded_search.py

python3 -m ruff format --check \
  src/core/fcis_durable_retraction.py \
  tests/core/test_fcis_durable_retraction.py \
  experiments/fcis_durable_retraction_bounded_search.py

python3 -m mypy src/core/fcis_durable_retraction.py

python3 -m pytest -q tests/core/test_fcis_durable_retraction.py

python3 experiments/fcis_durable_retraction_bounded_search.py \
  > /tmp/fcis-durable-retraction-python.json

git diff --exit-code -- \
  experiments/fcis_durable_retraction_bounded_search_result.json
```

Julia:

```bash
julia --startup-file=no \
  experiments/julia/fcis_durable_retraction_oracle.jl \
  > /tmp/fcis-durable-retraction-julia.json
```

Parse both JSON documents and require exact structural equality.

ESSO, from a pinned ESSO checkout:

```bash
python3 -m ESSO validate \
  /absolute/path/to/ZenoDEX/formal/esso/fcis_durable_retraction_v1.yaml

python3 -m ESSO verify-multi \
  /absolute/path/to/ZenoDEX/formal/esso/fcis_durable_retraction_v1.yaml \
  --solvers z3,cvc5
```

Replace the displayed absolute path with the actual clean-worktree path. Any
solver `UNKNOWN`, timeout, missing solver, or disagreement is a failed gate.

Lean:

```bash
cd lean-mathlib
lake update
lake exe cache get
lake build Proofs.FCISDurableRetraction
lake env lean Proofs/FCISDurableRetraction.lean
```

Run a placeholder and dependency audit over the exact file. Record:

```text
Lean version
mathlib revision
theorem names
theorem assumptions
exact compile result
axiom dependencies
```

Repository triage:

```bash
python3 .claude/skills/zenodex-style-map/scripts/which_style.py \
  src/core/fcis_durable_retraction.py \
  tests/core/test_fcis_durable_retraction.py \
  formal/esso/fcis_durable_retraction_v1.yaml \
  lean-mathlib/Proofs/FCISDurableRetraction.lean

python3 .claude/skills/zenodex-security-analysis/scripts/trust_surface.py

python3 .claude/skills/zenodex-security-analysis/scripts/redflags.py \
  src/core/fcis_durable_retraction.py \
  tests/core/test_fcis_durable_retraction.py

python3 .claude/skills/zenodex-refactoring/scripts/design_metrics.py \
  src/core/fcis_durable_retraction.py \
  --top 20 \
  --coupling
```

Scanners are triage evidence only.

## Exact-head delivery

Use a clean worktree based on the exact base. Preserve unrelated work.

Required topology:

```text
declared base
  -> implementation target
  -> documentation-only packet commit
```

The packet child may add only its declared review files. Include:

```text
target and tree
parent and tree
packet commit and tree
status-aware change inventory including deletions
source manifest
canonical archive
toolchain record
review prompt
implementation report
explicit nonclaims
```

Push only the dedicated branch and open or update a draft PR. Do not merge it.
Run CI on the exact PR head, not a synthetic merge commit. Upload the verified
review archive as a workflow artifact.

## Stop conditions

Stop and report the exact blocker if:

```text
the intended branch no longer equals the declared base
the packet source hashes do not match
an authority repair requires choosing a real signer or verifier policy that is
  absent from the approved design
the destination has no verifiable receipt contract
Lean requires weakening the theorem or adding trust-expanding declarations
ESSO returns UNKNOWN, times out, or the solvers disagree
Python and Julia disagree
the repair would require a production mount or compatibility decision
disk pressure prevents a clean exact-head build
```

For a missing real external verifier or destination adapter, keep the research
model conditional on an explicit verified witness. Do not invent production
authority.

## Forbidden shortcuts

Do not:

```text
replace a witness with a Boolean
use module privacy as the security boundary
treat a digest shape as authentication
catch and suppress broad exceptions
weaken, delete, skip, or xfail negative tests
edit frozen outputs without regeneration
change the allocator
add a datastore or API mount
switch migration authority
claim M6 completion
merge the PR
```

Do not add dependencies without a written determinism, security, license,
pinning, transitive-size, and removal analysis.

## Terminal condition

Finish only when:

```text
all blocking witnesses are retained and killed
Ruff and mypy pass
focused Python tests pass
Python and Julia bounded results agree
ESSO validate and multi-solver checks pass
Lean 4.27 compiles the faithful partial-reopen theorem with no trust expansion
claims match evidence
one canonical manifest-bound archive is reproducible
exact implementation target and packet child are remotely reviewable
the diff remains unmounted
```

## Required completion response

Return:

```text
Result:
- Base commit/tree:
- Implementation target commit/tree:
- Packet commit/tree:
- Branch:
- Draft PR:
- Changed files:
- Invariants and authority impact:
- Retained counterexamples:
- Python/Ruff/mypy results:
- Python/Julia parity:
- ESSO validate and solver results:
- Lean toolchain, theorem, compile, and axiom results:
- Canonical archive and manifest SHA-256:
- Exact-head CI:
- Commands not run:
- Residual risks:
- Explicit nonclaims:
- Next safest review step:
```

Do not use phrases such as “all good” or “production ready.” Give exact commands,
outcomes, and remaining gaps.
