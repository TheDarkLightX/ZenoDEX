# FCIS M6-R04 Lineage Certificate Closure

**Date:** 2026-07-30  
**Status:** `RESEARCH_ONLY_EXECUTABLE_UNMOUNTED`  
**Base:** M6-R01 Segmented Lineage Normal Form  
**Abstract theorem:** LEAP Certificate Closure Cube / finite closure hypercube

## 1. Result

This checkpoint instantiates the first concrete part of the M6 LineageCube over
actual ZenoDEX artifacts:

```text
FCISStepEvaluationOkV1
AcceptV1 / AcceptanceReceiptClaimV1
CommitBundleV1
OutboxPlanV1
CanonicalFeeOccurrenceSegmentV1
```

The implementation projects those values into one fixed, conflict-detecting
claim language and computes one deterministic fixed-point certificate. The three
projection families are:

```text
semantic
  exact evaluation evidence
  exact patch and commit-plan roots
  exact SLNF fee semantic and provenance roots

authority
  acceptance-receipt binding
  transition-budget hash
  lineage-bound receipt extension

durability
  exact retained decision
  recomputed base bundle root
  recomputed outbox plan
  lineage-bound bundle and outbox extensions
```

Every permutation of those axes must close to the same claim set and certificate
root. A disagreement on any overlapping key rejects; no stage overwrites an
earlier value.

This is a concrete certificate spine, not a production authority switch.

## 2. Mathematical basis

For a claim set `X`, immutable seed set `A`, and closure operator `cl`, one axis
is:

$$
T_A(X)=cl(X\cup A).
$$

When closure is extensive, monotone, and idempotent:

$$
cl(cl(X)\cup A)=cl(X\cup A).
$$

Therefore:

$$
T_B(T_A(X))=T_A(T_B(X)).
$$

The LEAP theorem now proves the stronger finite-hypercube result:

```text
for every finite axis list xs and ys,
Perm(xs, ys)
  -> stageMany(xs, base) ≈ stageMany(ys, base)
```

R04 uses the three-axis instance. Later migration, reopen, proof context, and
outbox acknowledgment can become additional axes without introducing a bespoke
pairwise proof for every old/new combination, provided they preserve the same
closure laws.

## 3. Fixed claim registry

`FCISLineageClaimKeyV1` is a closed enum. No caller chooses claim names or
closure rules.

### Source and candidate claims

```text
source/command_root
source/execution_context_hash
source/pre_state_root
source/next_state_root
source/support_root
source/support_set_commitment
source/snapshot_commitment
candidate/patch_root
candidate/commit_plan_root
```

### Fee lineage claims

```text
fee/boundary_root
fee/policy_root
fee/witness_tuple_root
fee/semantic_stream_root
fee/lineage_stream_root
```

The semantic root identifies allocator arithmetic. The lineage root identifies
the exact ordered source-witness decomposition. Both are mandatory.

### Authority claims

```text
authority/budget_hash
authority/acceptance_receipt_root
```

### Durability claims

```text
durability/outbox_plan_root
durability/base_bundle_root
```

### Derived claims

```text
derived/evaluation_certificate_root
derived/receipt_certificate_root
derived/bundle_certificate_root
derived/outbox_certificate_root
```

## 4. Fixed derivation manifest

The module has four module-owned, single-writer rules.

```text
EvaluationCertificate
  <- command
     context
     pre-state
     next-state
     support
     support-set commitment
     snapshot commitment
     patch
     commit plan
     fee boundary
     fee policy
     fee witness tuple
     fee semantic stream
     fee lineage stream

ReceiptCertificate
  <- EvaluationCertificate
     budget hash
     base acceptance-receipt root

BundleCertificate
  <- ReceiptCertificate
     base commit-bundle root
     outbox-plan root

OutboxCertificate
  <- BundleCertificate
     outbox-plan root
     base acceptance-receipt root
```

Each value is a domain-separated hash over an ordered dependency-key/value
sequence. A supplied value at a derived key must equal fresh derivation or the
closure rejects.

## 5. Artifact projections

### Semantic projection

The evaluator is independently rerun from the supplied state source,
settlement, intents, and execution context. The projection revalidates the exact
`FCISStepEvaluationOkV1`, derives the patch and commit plan again, and binds:

```text
command/context/pre/post/support/snapshot roots
patch root
commit-plan root
SLNF boundary/policy/witness/semantic/lineage roots
```

### Authority projection

The authoritative decision path is independently rerun from the same source
inputs and budget. The projection binds the exact fields retained in
`AcceptanceReceiptClaimV1.binding`, recomputes the receipt root, and carries a
new research extension that adds the five SLNF roots.

The extension is necessary because the current mounted receipt schema does not
carry fee-occurrence provenance. Without it, a receipt for one witness
composition could be paired with another composition having the same grouped
amount.

### Durability projection

`CommitBundleV1` must retain the exact acceptance object by identity. The
projection then recomputes:

```text
canonical bundle bytes
base bundle root
outbox plan from the retained decision
canonical outbox-plan root
```

A lineage bundle extension binds the base bundle and outbox roots to the lineage
receipt extension.

## 6. Concrete crossed-lineage falsifier

Within one accepted boundary and policy:

```text
W1 = [867]
W2 = [493, 374]
```

SLNF gives:

```text
semantic_stream_root(W1) = semantic_stream_root(W2)
lineage_stream_root(W1)  != lineage_stream_root(W2)
witness_tuple_root(W1)   != witness_tuple_root(W2)
```

The test combines:

```text
semantic projection from W2
authority projection from W1
durability projection from W1
```

Closure rejects at the fee-lineage claim rather than allowing the authority or
durability face to overwrite the semantic face.

This is the first executable crossed-lineage mutant for the concrete R04 schema.

## 7. Fresh recomputation and exact retention

The artifact builder rejects when:

- evaluation and receipt fields differ;
- independently derived patch or commit-plan roots differ;
- the budget hash differs;
- the base bundle does not retain the exact decision object;
- cached canonical bundle bytes or bundle root differ from recomputation;
- the outbox plan differs from fresh derivation;
- any SLNF segment invariant fails;
- any duplicated claim has a second value;
- any supplied derived claim differs from the fixed rule result.

The code intentionally treats Python `frozen=True` as insufficient and reruns
all available revalidators before accepting research evidence.

## 8. Executable surface

The module is:

```text
src/core/fcis_lineage_closure.py
```

Principal values:

```text
FCISLineageClaimV1
FCISLineageClaimSetV1
FCISLineageReceiptExtensionV1
FCISLineageBundleExtensionV1
FCISLineageClosureCertificateV1
FCISLineageClosureRejectV1
```

Principal functions:

```text
canonicalize_fcis_lineage_claims_v1
close_fcis_lineage_claim_sets_v1
build_fcis_lineage_closure_from_artifacts_v1
derive_fcis_lineage_closure_v1
```

`derive_fcis_lineage_closure_v1` runs the evaluator, decision derivation, bundle
derivation, three exact projections, and closure. It returns evidence only. It
does not commit state or enqueue/deliver an effect.

## 9. Tests

The focused test file is:

```text
tests/core/test_fcis_lineage_closure.py
```

It covers:

1. All six semantic/authority/durability orders have one claim set and root.
2. Same semantic fee amount with different witness provenance conflicts.
3. A forged derived evaluation claim is recomputed and rejected.
4. The semantic axis alone cannot derive receipt, bundle, or outbox authority.
5. Boundary and policy substitution change the terminal certificate.
6. A bundle from an equal-but-distinct decision object rejects.
7. A corrupted cached bundle root rejects under fresh recomputation.
8. Axis order must be one exact permutation of all three axes.
9. Identical duplicate claims are idempotent.
10. Conflicting duplicate claims never use last-writer-wins behavior.

The exact-head workflow runs this corpus together with the R01 occurrence tests,
strict static typing, compilation, and focused linting.

## 10. Relation to the generic LineageCube

The generic cube still states the extensional target:

```text
semantic face commutes
authority face commutes
durability face commutes
one lineage identity reaches every terminal
```

Certificate closure supplies a constructive implementation discipline:

```text
typed artifact
  -> exact projection
  -> immutable claim join
  -> deterministic closure
  -> one normal form
```

The proof burden becomes:

1. each projection is complete and injective over value-moving fields;
2. independent source claims are authenticated;
3. the fixed closure implementation refines the abstract closure operator;
4. terminal artifacts reconstruct uniquely from the closed certificate and
   explicitly retained payload;
5. every production path requires the resulting certificate.

This checkpoint addresses parts of 2–3 only for currently available roots and
artifact revalidation. It does not yet establish complete projection or mounting.

## 11. Evidence ledger

| Claim | Status | Evidence |
| --- | --- | --- |
| Closed claim registry | `IMPLEMENTED` | exact enum and bounded tuple values |
| Conflict-detecting join | `IMPLEMENTED_TESTED` | duplicate and crossed-lineage mutants |
| Deterministic fixed-point closure | `IMPLEMENTED_TESTED` | fixed single-writer rules |
| Three-axis order independence | `TESTED_ALL_6` | concrete artifact projections |
| Arbitrary finite-axis confluence | `PROVED_ABSTRACTLY` | LEAP Lean permutation theorem |
| Evaluation/receipt shared lineage | `RECOMPUTED_TESTED` | duplicate roots and plan derivation |
| Bundle exact-decision retention | `RECOMPUTED_TESTED` | identity and corruption mutants |
| Outbox plan lineage | `RECOMPUTED_TESTED` | retained decision replay |
| Fee semantic and provenance identity | `BOUND_IN_EXTENSION` | SLNF dual roots |
| Fee witness roots authenticated from settlement replay | `GAP` | external segment input |
| Current acceptance receipt carries fee roots | `GAP` | research extension only |
| Current base bundle carries lineage receipt extension | `GAP` | research extension only |
| Durable datastore publication | `GAP` | no commit-port projection yet |
| Reopen/history/nullifier face | `GAP` | later R07/R09 work |
| Runtime no-bypass | `UNMOUNTED` | later R12 work |

## 12. Falsifiers

Reject or revise this checkpoint if:

- any of the six axis orders produces a different closed root;
- a crossed command, state, context, policy, semantic stream, or lineage stream
  survives claim join;
- a forged derived claim survives fresh closure;
- bundle corruption survives recomputation;
- an omitted value-moving artifact field can vary without changing the claim
  set;
- the receipt extension can be detached from its exact base receipt;
- the bundle extension can be detached from its exact base bundle or outbox;
- a terminal artifact cannot be reconstructed uniquely from the certificate and
  declared retained payload;
- a production path accepts without the lineage certificate.

## 13. Nonclaims and next checkpoint

This checkpoint does not authenticate the fee boundary, policy, or source
witness roots. It does not derive fee occurrences from exact settlement replay,
change the mounted receipt or bundle schema, commit state, persist history or
nullifiers, recover a datastore, deliver an external effect, prove Python/Rust
root parity, or establish no-bypass mounting.

The next honest R04 checkpoint is:

1. derive the SLNF witness tuple directly from exact settlement replay;
2. add the five fee-lineage roots to the real candidate and acceptance-receipt
   schemas rather than a research extension;
3. add the lineage receipt root to the real commit-bundle claim;
4. project atomic datastore publication and reopen state;
5. prove terminal reconstruction uniqueness;
6. run crossed-lineage mutants through the actual commit port;
7. then make the certificate mandatory at every value-moving entrypoint.
