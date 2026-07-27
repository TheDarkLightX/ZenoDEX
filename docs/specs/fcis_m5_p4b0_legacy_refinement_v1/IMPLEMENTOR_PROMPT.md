# Implementor Prompt: FCIS M5-P4B0 Legacy Refinement

## Role and authorized result

Implement one bounded, unmounted FCIS evidence checkpoint in ZenoDEX.

The only authorized successful outcome is:

```text
M5_P4B0_REFINEMENT_EVIDENCE_ONLY
```

This checkpoint determines whether each frozen P4A legacy observation is
refined by the corresponding FCIS V1 observation under one closed,
source-owned policy. It produces evidence. It grants no runtime authority.

Do not switch mounted authority. Do not modify production dispatch, verifier
policy, proof guests, Rust authority, Tau authority, deployment configuration,
or public release claims.

## Required inputs

The reviewer will provide:

```text
REQUIRED_ANCESTOR=fd1ef9f1
PACKET_COMMIT=<exact documentation commit supplied with this prompt>
```

Refuse to begin if `PACKET_COMMIT` is absent, if the packet checker fails at
that commit, or if `fd1ef9f1` is unavailable.

The packet commit is documentation provenance. It is deliberately later than
the reviewed implementation ancestor. Do not cherry-pick it into the
implementation branch.

## Worktree setup

Use a new worktree and branch. Preserve every existing checkout and user edit.

```bash
git fetch origin
git cat-file -e fd1ef9f1^{commit}
git cat-file -e "$PACKET_COMMIT"^{commit}
git worktree add \
  /tmp/zenodex-fcis-m5-p4b0-refinement-20260726 \
  -b agent/fcis-m5-p4b0-refinement-20260726 \
  fd1ef9f1
```

Record:

```bash
git rev-parse HEAD
git status --short
git diff --exit-code fd1ef9f1 -- src/core/dex.py
python3 tools/check_fcis_m5_p4a_readiness.py --check
```

Read every packet file directly from `PACKET_COMMIT` in this order:

```bash
for file in CONTRACT.md TEST_MATRIX.md REVIEW_CHECKLIST.md \
  IMPLEMENTOR_PROMPT.md requirements.json README.md check_packet.py; do
  git show \
    "$PACKET_COMMIT:docs/specs/fcis_m5_p4b0_legacy_refinement_v1/$file"
done
```

The reviewer has run `check_packet.py` at `PACKET_COMMIT`. Your implementation
must bind both `PACKET_COMMIT` and its packet-tree hash in the generated
evidence artifact.

## Normative design

Implement exactly the contract in `CONTRACT.md`. The authority pipeline is:

```text
canonical bytes
  -> strict canonical JSON decode
  -> admit(declared_schema, value, path, context)
  -> exact owned observation values
  -> pure RefinesV1 | MismatchV1 | InvalidEvidenceV1
  -> canonical source-bound artifact
```

The existing closed admission combinator is the only structural validation
engine. Schemas declare structure. Admission must call:

```text
admit(declared_schema, value, path, context)
```

Do not implement parallel hand-written validation. Domain construction after
successful admission may enforce semantic relationships that the schema
cannot express, provided those checks consume only admitted exact values and
return stable typed errors.

The refinement policy is closed and source-owned. Evidence may name the policy
version and hash. Evidence cannot supply mappings, ignored paths, expected
differences, constructors, registries, resolvers, encoders, or callbacks.

The relation is directional:

```text
RefinesV1(legacy_observation, exact_observation, fixed_policy)
```

Direct legacy-envelope and FCIS-envelope byte equality is not expected.
Refinement requires same canonical command, pre-state, and context bytes;
identical shared semantic projections; and complete self-consistency of every
exact-only patch, receipt, bundle, replay, and outbox value.

## Required implementation surface

Prefer these new, unmounted modules unless an existing exact module already
owns the responsibility:

```text
src/core/fcis_legacy_refinement_values.py
src/core/fcis_legacy_refinement_schema.py
src/core/fcis_legacy_refinement_admission.py
src/core/fcis_legacy_refinement_policy.py
src/core/fcis_legacy_refinement.py
tools/build_fcis_m5_p4b0_refinement.py
tools/check_fcis_m5_p4b0_refinement.py
tests/core/test_fcis_legacy_refinement_values.py
tests/core/test_fcis_legacy_refinement.py
tests/tools/test_check_fcis_m5_p4b0_refinement.py
docs/research/FCIS_M5_P4B0_REFINEMENT_V1.json
docs/research/FCIS_M5_P4B0_IMPLEMENTOR_REPORT_20260726.md
```

You may extend these existing structural checker files only to bind the new
unmounted authority surface:

```text
tools/check_fcis_authority_snapshot_contract.py
tests/tools/test_check_fcis_authority_snapshot_contract.py
```

You may add narrowly scoped test helpers under `tests/`. Do not alter the P4A
baseline, differential artifact, call-graph ledger, matrix, receipt, checker,
or reviewed report. They are immutable inputs to this checkpoint.

Stop and return a blocker before changing any other production file. A missing
field or helper in an existing FCIS module is a design finding for the reviewer,
not implicit permission to widen the diff.

## Forbidden mechanisms

The new path must contain none of these:

```text
Any in an authority-bearing type
generic deep_freeze
copy.copy or copy.deepcopy
mutable-class inheritance
subclass-based freezing
seal or _snapshot_sealed flags
MappingProxyType over caller-owned data
open Mapping or Sequence as committed storage
isinstance-based permissive admission
object.__setattr__ outside constructor-time frozen-value initialization
input-selected registry, constructor, resolver, encoder, or policy
broad except Exception that promotes or hides unknown evidence
wall clock, randomness, network, filesystem, environment, locale, or globals
```

Exact final frozen slotted values, tuples, and composition-owned collections
are required. Defensive commit-time revalidation must detect hostile nested
mutation rather than trusting cached roots or Python `frozen=True` alone.

## Required checkpoint order

Keep commits reviewable. Complete the work in this order:

### P4B0-A: values, schemas, admission, and policy

1. Add the closed result algebra and exact owned observation/witness values.
2. Declare schemas in the dedicated schema module.
3. Route every evidence value through the existing combinator.
4. Add the source-owned policy registry and deterministic policy hash.
5. Bind `P4B0-001` through `P4B0-006`, `P4B0-014`, `P4B0-015`, and
   `P4B0-016` with executable tests.
6. Run the structural checker and forbidden-mechanism mutations.

Commit this checkpoint before proceeding.

### P4B0-B: pure refinement and exact-only consistency

1. Implement result-kind and rejection refinement.
2. Implement the shared semantic projection across all eight state fields.
3. Compare ordered economic outputs, fees, dust, and replay-relevant nonces.
4. Recompute and validate patch, receipt, bundle, replay, and outbox values.
5. Preserve the first mismatch using a stable versioned ordering.
6. Bind `P4B0-007` through `P4B0-013` with executable tests.

Commit this checkpoint before proceeding.

### P4B0-C: artifact, checker, mutations, and report

1. Generate one canonical row for every P4A fixture.
2. Bind source, reviewed ancestor, packet, policy, and P4A artifact hashes.
3. Add normal validation and `--require-all-refine` semantics.
4. Rehash and kill every named semantic mutation in `TEST_MATRIX.md`.
5. Bind `P4B0-017` through `P4B0-020`.
6. Write the implementor report with exact commands and nonclaims.

Commit this checkpoint. Do not squash the three checkpoints before review.

## Required tests and gates

Every test ID in `requirements.json` must have exactly one discoverable binding.
Names or test metadata must allow the reviewer to map IDs to executable tests.
Use fixed and reported seeds for generated/property inputs.

Run at the final head:

```bash
python3 -m py_compile \
  src/core/fcis_legacy_refinement_values.py \
  src/core/fcis_legacy_refinement_schema.py \
  src/core/fcis_legacy_refinement_admission.py \
  src/core/fcis_legacy_refinement_policy.py \
  src/core/fcis_legacy_refinement.py \
  tools/build_fcis_m5_p4b0_refinement.py \
  tools/check_fcis_m5_p4b0_refinement.py

python3 -m ruff check <all changed Python files>
python3 -m ruff format --check <all changed Python files>
python3 -m mypy \
  src/core/fcis_legacy_refinement_values.py \
  src/core/fcis_legacy_refinement_schema.py \
  src/core/fcis_legacy_refinement_admission.py \
  src/core/fcis_legacy_refinement_policy.py \
  src/core/fcis_legacy_refinement.py \
  tools/build_fcis_m5_p4b0_refinement.py \
  tools/check_fcis_m5_p4b0_refinement.py

python3 tools/build_fcis_m5_p4b0_refinement.py
python3 tools/build_fcis_m5_p4b0_refinement.py --check
python3 tools/check_fcis_m5_p4b0_refinement.py
python3 tools/check_fcis_m5_p4b0_refinement.py --require-all-refine

python3 tools/check_fcis_authority_snapshot_contract.py --profile state-substrate
python3 tools/check_fcis_authority_snapshot_contract.py --profile authority-graph
python3 tools/check_fcis_authority_snapshot_contract.py --profile exact-replay
python3 tools/check_fcis_authority_snapshot_contract.py --profile exact-consumers
python3 tools/check_fcis_authority_snapshot_contract.py --profile final-mount

python3 -m pytest -q \
  tests/core/test_fcis_legacy_refinement_values.py \
  tests/core/test_fcis_legacy_refinement.py \
  tests/tools/test_check_fcis_m5_p4b0_refinement.py \
  tests/tools/test_check_fcis_authority_snapshot_contract.py

git diff --check fd1ef9f1...HEAD
git diff --exit-code fd1ef9f1...HEAD -- src/core/dex.py
```

Interpret expected failures honestly:

- Normal refinement validation must pass for a canonical, source-bound artifact
  even when it contains typed mismatches.
- `--require-all-refine` must exit nonzero whenever one or more fixtures are
  `MismatchV1` or `InvalidEvidenceV1`.
- The `final-mount` profile must remain fail-closed. Record the exact count and
  categories. Do not repair mounted paths in this checkpoint.
- Missing Rust, Tau, proof-guest, verifier, datastore, or crash-recovery lanes
  remain missing. Do not convert them to passes.

Run the repository style classifier, security red-flag scan, and design metrics
on every changed critical path. Run the broad critical gate only after the
narrow source checkpoint is clean. If a required tool or dependency is absent,
record the exact unavailable command. Do not install dependencies without
reviewer approval.

## Mandatory stop conditions

Stop with a blocker and make no authority change if any of these occurs:

- a P4A observation lacks the exact bytes required by the same-input check;
- either observation omits one of the eight state fields or an economic output;
- the policy would need an input-controlled ignored path or wildcard;
- a rejection mapping is ambiguous or loses an authoritative distinction;
- exact patch, receipt, replay, outbox, or bundle cannot be recomputed from
  existing controlled constructors;
- a mismatch can be hidden only by weakening a comparator, test, schema, or
  checker;
- the closed combinator cannot express a structural boundary without a design
  change;
- any requested change touches mounted dispatch or a prohibited surface;
- disk pressure, missing dependencies, or an unrelated dirty tree prevents a
  clean exact-head result.

An honest blocked result is acceptable. Never manufacture `RefinesV1`.

## Required handoff

Do not push. Return control to the reviewer with:

```text
Result:
- Outcome: M5_P4B0_REFINEMENT_EVIDENCE_ONLY or BLOCKED
- Exact start head:
- Exact end head:
- Branch and worktree:
- Checkpoint commits:

Changed:
- Files and invariant ownership:

Invariant/authority impact:
- Refinement claims actually established:
- Exact mismatch counts and first paths:
- Confirmation that mounted authority is unchanged:

Evidence:
- Test IDs and executable bindings:
- Exact commands and outcomes:
- Mutation ledger:
- Artifact and policy hashes:

Commands not run:
- Exact reason for each omission:

Residual risk:
- Missing consumers, proofs, datastore, crash, and cross-language lanes:

Next safest step:
- Return to reviewer. Do not mount or begin P4B/P5/M6.
```

The reviewer will independently rerun all 12 attacks in `TEST_MATRIX.md`,
inspect every contract obligation, grade the result, repair worthwhile defects,
and decide whether another checkpoint may begin.
