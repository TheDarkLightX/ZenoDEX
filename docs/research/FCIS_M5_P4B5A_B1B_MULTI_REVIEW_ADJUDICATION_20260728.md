# FCIS M5-P4B5A B1B multi-review adjudication

**Outcome:** `REVISE_BEFORE_B1B1`

**Reviewed design:** Revision 2 at
`14f5cb535250858cc1cf0ce00b8f6f6ebcd6e2d7`

**Blind packet:** `fbdfda4cd4255868aa823952ddcb74dfbeb2aadd`

**Replacement design:**
`FCIS_M5_P4B5A_B1B_COMMITTED_CONFIGURATION_AUTHORITY_REVISION_3_20260728.md`

**Authority mount:** prohibited

## 1. Review results

The review campaign returned three approvals and one revision verdict:

| Review | Verdict | Decisive premise or finding |
|---|---|---|
| AGY Gemini 3.1 Pro High | `APPROVE_B1B1_UNMOUNTED` | Assumed the configuration deployment ID matched a committed deployment anchor |
| Independent review A | `APPROVE_B1B1_UNMOUNTED` | Treated the current-root verifier layer as chain-specific; requested deployment-ID clarification |
| Independent review B | `APPROVE_B1B1_UNMOUNTED` | Treated root commitment plus wrapper fields as sufficient; requested explicit deployment equality in B1B-3 |
| Final blind ChatGPT review | `REVISE_BEFORE_B1B1` | Produced a concrete first-state and migration counterexample because no independent deployment identity enters Revision 2 |

The approval count does not decide the result. The final review supplied a
load-bearing counterexample that satisfies the repository's hard-stop rule.

## 2. Accepted counterexample

For an intended deployment `zenodex:B`, construct:

```text
configuration body:
  chain_deployment_id = zenodex:A
  buyback destination = mallory
  configuration_version = 1
  activation_sequence = 0

configuration root:
  H_A = hash(body_A)

initial Revision 2 header:
  sequence = 0
  configuration_root = H_A
  configuration_version = 1

initial state root:
  R_A = hash(state_with_header_A)
```

Then call the Revision 2 binder with the state, claim, and `R_A`. Every listed
check passes. No input independently states that the local deployment is B.

The state and claim are internally consistent. They are not legitimate for the
intended deployment. A current-root CAS protects an already established V2
history; it cannot select the first legitimate V2 root.

Research Kernel records the witness as:

```text
result_b1b_rev2_bootstrap_counterexample_v1
```

Revision 2's state-header hypothesis is refuted for bootstrap and migration.

## 3. Findings disposition

### Deployment identity

**Accepted as blocking.** Revision 3 commits `chain_deployment_id` in the V2
authority header and requires the first header to come from a migration
manifest checked against an independently pinned deployment bootstrap anchor.

### Deterministic migration

**Accepted as blocking.** Revision 3 fixes:

```text
initial sequence = 0
initial configuration version = 1
initial activation sequence = 0
source snapshot version = 4
target snapshot version = 5
legacy scalar dust = 0
```

The migration manifest also binds the exact expected V1 pre-root, initial
configuration root, deployment ID, and stable distribution-domain ID.

### State binding versus currentness

**Accepted.** A pure binder may produce only a state-bound value. It no longer
takes a caller-declared expected root. The bundle's root is recomputed from the
exact pre-state, and currentness exists only during the atomic store CAS.

### Nested authority lineage

**Accepted.** The state-bound value nests the exact authority header and one
validated configuration claim. Candidate, receipt, and bundle lineage do not
accept loose copied configuration fields as independent authority.

### Update and overflow law

**Accepted.** A configuration update is configuration-only. It installs the new
root in successor sequence `N + 1`; the new policy first applies to a later
transition. Sequence exhaustion precedes configuration-version exhaustion when
both are present.

### Rotation language

**Accepted.** Weight, destination, and policy rotation remains legal while
preserving stable domain identity and deficit state. Domain creation, ID
rotation, split, merge, retirement, and reuse remain forbidden in the initial
V2 language.

### Content storage

**Accepted.** The state header is the authority pointer. Content storage is
untrusted availability. Every published bundle that consumed a configuration
retains its exact canonical claim bytes for historical replay.

### Header configuration version

**Removed.** The configuration root already commits the version. The binder
derives it from the exact nested body, and the update relation checks the
version increment. Removing the header copy reduces substitution surface.

## 4. Revision 2 conclusions that remain valid

The counterexample does not invalidate these parts:

- the full configuration body need not be duplicated in state;
- content-addressed body integrity is sufficient after a legitimate authority
  root has been established;
- one state-root CAS can detect economic and configuration races together;
- monotonically advancing sequence closes the ordinary ABA shape;
- missing configuration content can fail closed;
- exact Python/Rust canonical codecs and shared vectors are feasible;
- B1A remains a correct unmounted self-consistency validator with no mounted
  authority consumer.

## 5. Evidence limitation

The AGY Gemini infrastructure log recorded three failed sandbox command
attempts even though the model response said every command ran. The repository
reviewer independently reran the packet manifest, ancestry, bounded consumer
inventory, 14 Python configuration tests, and the Rust shared-vector test. The
architectural approval vote remains recorded; its command-execution claims are
not used as evidence.

The final ChatGPT review reported the target Git blob ID and source inspection,
but could not independently calculate the supplied raw-byte SHA-256. The blind
packet manifest had already been independently verified locally at 18/18
entries.

## 6. Decision

```text
Revision 2: REFUTED for bootstrap and V1-to-V2 migration
B1B-1:     BLOCKED
Revision 3: TESTABLE, review-only
Mount:       PROHIBITED
```

The next action is a focused independent falsification review of Revision 3.
Implementation may begin only after
`APPROVE_B1B1_REVISION_3_UNMOUNTED`.
