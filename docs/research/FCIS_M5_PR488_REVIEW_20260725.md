# FCIS M5 PR #488 Review

**Review date:** 2026-07-25  
**PR:** `TheDarkLightX/ZenoDEX#488`  
**Reviewed PR head:** `a2b570a8e5da043380ec1b3e43aab9932a42692f`  
**Reviewed source checkpoint:** `77a73c93dbd23729b743aa2fb46f0d62554c7578`  
**Base:** `d3f7b5068effd793d8d16ea63aa8c36e19e32243`  
**Contract:** `zenodex/fcis-m5-atomic-mount/v2`  
**Verdict:** `NO_GO_M5_PREREQUISITE_REWORK_REQUIRED`

## Executive verdict

PR #488 correctly leaves production authority unmounted. That stopping decision
must remain in force.

The prerequisite checkpoint itself does not satisfy the reviewed M5 handoff.
It is outside the closed admission algebra and outside the structural and
normative packet gates. Three minimized authority counterexamples succeed
against the source checkpoint:

1. a successor state can be spliced into an already-built `AcceptV1`, after
   which `encode_decision_v1` still accepts and encodes the contradictory
   decision;
2. a `RejectV1.reason` can disagree with
   `rejection_receipt.public_reason`, after which `encode_decision_v1` still
   accepts and encodes both values;
3. the reference commit port publishes a nonce change for an account absent
   from `replay_updates`.

A fourth metamorphic witness shows that two different successor states can
carry the same claimed canonical patch bytes and patch root. The patch is
caller-supplied opaque bytes, rather than a typed patch derived from the exact
transition candidate.

The focused M5 workflow is green because it does not run the FCIS structural
checker or the normative packet checker, and because its tests do not contain
these witnesses.

Do not merge PR #488. Do not mount or extend its public authority types.

## Automatic no-go findings

### F1. New authority files are outside every structural profile

The changed authority files are:

```text
src/core/fcis_atomic_mount_values.py
src/core/fcis_atomic_mount_codec.py
src/integration/fcis_atomic_commit_reference.py
```

None appears in:

```text
STATE_SUBSTRATE_AUTHORITY_PATHS
AUTHORITY_GRAPH_AUTHORITY_PATHS
EXACT_REPLAY_AUTHORITY_PATHS
EXACT_CONSUMERS_AUTHORITY_PATHS
FINAL_MOUNT_AUTHORITY_PATHS
```

The required relation therefore fails:

```text
ChangedAuthorityFiles subset_of StructuralCheckerCheckedPaths
```

The four prerequisite profiles report `ok: true` only because they do not
inspect the new files. The `final-mount` profile remains red on the inherited
legacy path, as expected before a mount.

This is the same gate-design failure class that allowed PR #478's forbidden
freeze/copy mechanisms through focused behavioral tests.

### F2. The normative packet contains no M5 requirements or test bindings

The packet checker reports:

```json
{
  "ok": true,
  "requirement_count": 39,
  "declared_test_id_count": 103,
  "bound_test_id_count": 103
}
```

No M5 type, source path, requirement, or test ID from PR #488 occurs in
`requirements.json`, `TEST_MATRIX.md`, or
`TEST_MATRIX_PR477_PR478.md`. The green result proves only that the older
packet remains internally consistent.

### F3. The new authority graph bypasses the closed admission algebra

The new modules do not call:

```text
admit(schema, value, path, context)
```

Instead, public frozen dataclasses and builders perform hand-written validation
and raise host exceptions. `FCISRootBoundPayloadV1` accepts arbitrary bytes,
hashes them, and labels the result as a canonical patch, value plan, receipt
detail, or outbox payload.

This violates M5-D01 and the P0 requirement to add:

```text
closed schemas
stable typed errors
canonical encoders
structural checker bindings
```

Hash binding proves that bytes were not changed after hashing. It does not prove
that the bytes are the unique canonical encoding of a valid typed patch or
plan.

### F4. `DecisionV1` does not enforce same-candidate derivation

`FCISAcceptV1` and `FCISCommittedFailureV1` check only that the receipt and
plan carry the same `candidate_root`. They do not prove that `next_state`
belongs to that candidate.

`validate_decision_v1` repeats the same incomplete relation. It then encodes
the independently supplied successor-state root beside the plan and receipt
roots.

Minimized witness:

```python
spliced = dataclasses.replace(valid_accept, next_state=other_state)
encode_decision_v1(spliced)  # succeeds
```

Observed result:

```text
spliced_decision_encoded = 125 bytes
```

This is an automatic no-go under the same-candidate rubric.

### F5. The claimed canonical patch is not transition-derived

`build_accept_decision_v1` accepts:

```text
next_state
canonical_patch_bytes
value_plan_bytes
replay_updates
outbox_effects
```

as independent caller arguments. It hashes them together, but never derives
the patch from the candidate or proves that the patch transforms the exact
pre-state into the successor.

Metamorphic witness:

```text
same pre-state
same canonical_patch_bytes
different successor states
```

Observed:

```json
{
  "different_next_roots": true,
  "same_claimed_canonical_patch_root": true,
  "same_patch_bytes": true
}
```

A typed patch constructor must derive canonical operations and expected-old
values from one evaluated candidate. The caller must not be able to attach an
arbitrary byte string to a successor and call it canonical.

### F6. Replay validation proves inclusion in only one direction

The reference port checks every declared replay update against the pre-state
and successor. It does not prove that every nonce change in the successor is
declared.

Minimized witness:

```text
pre-state:
  owner_1 nonce = 0
  owner_2 nonce = 0

replay_updates:
  owner_1: 0 -> 1

successor:
  owner_1 nonce = 1
  owner_2 nonce = 7
```

Observed:

```json
{
  "status": "published",
  "undeclared_nonce_after": 7,
  "declared_replay_pubkeys": ["owner_1"]
}
```

Required law:

```text
ChangedNonceCells(pre_state, next_state)
  = DeclaredReplayNonceCells(replay_updates)
```

The same exact-containment law is required for every authoritative patch
section.

## Additional findings

### F7. `RejectV1` can carry conflicting public reasons

`RejectV1.reason` duplicates `rejection_receipt.public_reason`, but neither
construction nor validation requires equality.

Minimized witness:

```python
conflict = dataclasses.replace(valid_reject, reason="different reason")
encode_decision_v1(conflict)  # succeeds
```

Observed result:

```text
conflicting_reject_encoded = 78 bytes
```

Remove the duplicate field or require equality in construction, revalidation,
and cross-language vectors.

### F8. Stable rejection codes and resource budgets are incomplete

Receipt codes and public reasons are unrestricted strings rather than members
of a versioned closed registry. The checkpoint also lacks the required
first-class `TransitionBudgetV1` covering reads, writes, candidates, effects,
witness bytes, receipt bytes, and integer magnitude.

### F9. The completion receipt is not a complete source-bound receipt

`FCIS_M5_COMPLETION_RECEIPT_V1.json` lacks required fields including:

```text
exact ending PR head
packet hash
checkpoint commit map
every command and exact result
source/toolchain/schema/algorithm artifact hashes
v4/v5 golden roots
structural profile results
Python/Rust parity status by command
unavailable evidence lanes
```

Its `completed_capabilities` list also overstates same-candidate and replay
closure in light of F4 through F6.

### F10. The mandatory checkpoint review stop was skipped

The handoff requires review after M5-P0 before continuing. PR #488 implemented
P0-shaped values and a P3-shaped commit reference without first closing and
reviewing P0 schemas, stable errors, packet bindings, and structural checker
coverage.

### F11. Focused workflow coverage is insufficient

`.github/workflows/fcis-m5-atomic.yml` runs Ruff, mypy, and two focused test
files. It omits:

```text
ruff format --check
packet checker
all FCIS structural profiles
changed-authority-file coverage assertion
checker mutation specimens
property-based tests
git diff --check
```

The exact PR range also fails `git diff --check` on Markdown trailing
whitespace.

## Grade

| Rubric category | Score | Maximum | Reason |
| --- | ---: | ---: | --- |
| Frozen-design fidelity | 8 | 20 | Frozen exact records, but manual parallel admission and arbitrary byte authority |
| Exact authority graph | 7 | 15 | Eight fields represented, but no closed schemas and replay containment is incomplete |
| Support-root correctness | 10 | 15 | Correctly left blocked and unchanged; no closure implemented |
| Same-candidate derivation | 3 | 15 | Hash material is broad, but spliced decisions and unrelated patches are accepted |
| Atomic bundle and rejection law | 8 | 15 | Reference all-or-none publication exists; replay and reject contradictions remain |
| Structural and mutation gates | 0 | 10 | Changed authority files and tests are outside the gate |
| Python/Rust refinement | 4 | 5 | Correctly recorded as an open nonclaim |
| Evidence and nonclaims | 2 | 5 | Safe mount nonclaim, incomplete receipt and inflated completed capabilities |
| **Total** | **42** | **100** | **Automatic no-go** |

## Divergent PBT branch comparison

The local branch:

```text
agent/fcis-m5-atomic-mount-20260724
head d2cc011bef0b998db3986963404bdecbc2927544
```

contains useful minimized counterexamples and property-based evidence,
including commit `8db4212ffe9930be0ed0a0b22d4bb0d06810fe67`.
It catches patch, outbox, receipt-codec, replay-root, and transitive
immutability defects that PR #488's tests do not cover.

It is not promotion-ready. Its new authority files are also absent from every
structural profile and normative packet. It contains reflective dataclass
encoding and `isinstance`-based dispatch rather than the closed schema
interpreter. Treat it as the preferred bug corpus and a possible source of
typed domain records, not as an approved authority implementation.

The remote branch with that name still points to the M4 base, so the local
commits are not durable on GitHub.

## Required consolidation checkpoint

Create one branch from the reviewed M4 base. Do not add a third authority
graph. Use the following order:

1. Select one type inventory. Prefer the existing exact M4
   `FCISStepCandidateV1` and the PBT branch's typed patch, replay, receipt,
   outbox, and plan concepts. Record an explicit supersession map for both
   divergent implementations.
2. Define a closed tagged schema for every new authority value. Every public
   admission edge must call `admit(schema, value, path, context)` and return a
   stable typed rejection. Direct dataclass constructors remain trusted
   internal constructors only.
3. Replace generic root-bound byte envelopes with domain-specific typed values
   and explicit encoders. No `dataclasses.is_dataclass`, reflective field walk,
   `isinstance` variant dispatch, `str(value)` fallback, or generic
   `bytes -> canonical authority` binder.
4. Derive `DecisionV1`, typed patch, plan, effects, replay updates, receipt, and
   outbox plan from one `FCISStepCandidateV1`. A decision validator must reject
   successor substitution before encoding.
5. Enforce exact patch containment, including:

   ```text
   ChangedNonceCells = DeclaredReplayNonceCells
   ChangedStateCells = DeclaredPatchCells
   ```

6. Add all new authority files to a named structural profile and to
   `final-mount`. Add an executable assertion that every changed authority file
   is in `checked_paths`.
7. Add M5 requirements and test IDs to the normative packet. Bind every
   counterexample and property to a requirement.
8. Port the PBT branch's useful properties and add the four PR #488 witnesses
   from this review as permanent negative tests.
9. Mutation-test the checker with at least: generic byte binder, hand-written
   admission, reflective dataclass dispatch, omitted authority path,
   successor splice, undeclared replay change, and duplicate reject reason.
10. Stop after the consolidated M5-P0 checkpoint for review. Do not implement
    P1, P2, P3, or a mount in the same review cycle.

## Promotion condition

The next checkpoint may be reviewed only when:

```text
ChangedAuthorityFiles subset_of StructuralCheckerCheckedPaths
and PacketRequirements == BoundTests
and ClosedAdmissionOnly
and SameCandidateCounterexamplesReject
and ReplayAndPatchContainmentHold
```

Until then:

```text
M5_BLOCKED_NO_AUTHORITY_SWITCH
```
