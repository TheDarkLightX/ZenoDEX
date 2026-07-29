# FCIS M5-P4B5A B1B Revision 3 multi-review adjudication

**Outcome:** `REVISE_BEFORE_B1B1`

**Reviewed design:** Revision 3 at
`798f4ba862ff07cf1f92b54946c67e13e7a939b6`

**Review packet:** `2f5dee71a20968d858e45a24aea34e6fa72afbb5`

**Source-manifest SHA-256:**
`83457084f6c3892d9088ca46f9b89a07bf5bc053f8e3d2712295deb710f042df`

**Replacement design:**
`FCIS_M5_P4B5A_B1B_COMMITTED_CONFIGURATION_AUTHORITY_REVISION_3_1_20260729.md`

**Research Kernel result:**
`result_b1b_rev3_provenance_loss_counterexamples_v1`

**Authority mount:** prohibited

## 1. Review results

The Revision 3 campaign returned two detailed approval verdicts and one detailed
revision verdict. All three verified the exact target and bounded source
manifest. The revision verdict supplied three concrete authority
counterexamples that the approvals did not close.

| Review | Verdict | Decisive premise or finding |
|---|---|---|
| Independent review A | `APPROVE_B1B1_REVISION_3_UNMOUNTED` | Treated the pinned verifier comparison as preserved by the verified wrapper and wrapper revalidation |
| Independent review B | `APPROVE_B1B1_REVISION_3_UNMOUNTED` | Confirmed bootstrap, deterministic migration, compact header, update boundary, and canonical feasibility |
| Final independent review | `REVISE_BEFORE_B1B1` | Coordinated mutation can replace every self-checking wrapper field after the independent source leaves the relation; ordinary header writes are not exhaustively closed |

The approval count does not decide the outcome. A concrete counterexample to an
authority claim is a hard veto under the repository trust ladder.

## 2. Findings accepted as blocking

### 2.1 Verified migration authority loses the pinned anchor

Revision 3 proposed:

```text
VerifiedV1ToV2MigrationAuthorityV2(
    manifest,
    manifest_root,
)
```

The migration core consumed that value without the independently pinned
bootstrap verifier. Hostile code can replace the manifest and root together
with a different self-consistent pair. The migration core can recompute the
replacement root, but it cannot compare that root with the independent pinned
root because the source fact is absent.

Private construction and frozen values reduce accidental misuse. They do not
restore provenance under Revision 3's declared hostile same-process mutation
model.

**Disposition:** accepted as blocking.

**Correction:** Revision 3.1 removes the durable verified-authority wrapper.
Every migration derivation and commit-time rederivation receives the
independently pinned verifier at the point of use.

### 2.2 State-bound configuration loses the exact state

Revision 3 proposed:

```text
StateBoundFeeDistributionConfigurationV2(
    pre_state_root,
    authority_header,
    validated_configuration_claim,
)
```

The snapshot root commits the whole exact state. It is not an inclusion proof
for an isolated header. Hostile code can retain the legitimate pre-state root
while replacing the header and configuration claim together. Wrapper
self-revalidation can prove only that the substituted claim matches the
substituted header.

The store's current-root comparison does not detect this attack because the
attacked wrapper deliberately retains the legitimate root.

**Disposition:** accepted as blocking.

**Correction:** every state-bound use must freshly bind the nested claim against
the exact pre-state and compare the complete fresh aggregate with the supplied
aggregate. Commit-time verification uses the store's exact current state.

### 2.3 Authority-header change is not monopolized

Revision 3 specified the dedicated configuration-update relation and required
sequence advancement for every committed accept and committed failure. It did
not explicitly require ordinary successors to preserve deployment ID and
configuration root.

An ordinary accepted or committed-failure candidate could therefore carry:

```text
next.sequence = pre.sequence + 1
next.configuration_root = attacker-selected self-consistent root
```

while preserving the expected pre-root and a consistently constructed
successor.

**Disposition:** accepted as blocking.

**Correction:** Revision 3.1 defines a closed header transition sum containing
only migration, ordinary advance, and configuration update. Ordinary accept and
committed failure preserve deployment ID and configuration root. Generic header
writes are structurally forbidden.

## 3. Findings retained from Revision 3

The counterexamples do not invalidate these decisions:

- `chain_deployment_id` belongs in the committed V2 authority header;
- the configuration root commits the body and version, so header version
  duplication remains unnecessary;
- the bootstrap verifier must be independently pinned before transaction
  processing;
- initial sequence, configuration version, and activation sequence remain
  fixed at `0`, `1`, and `0`;
- source and target snapshot versions remain `4` and `5`;
- legacy scalar dust must be zero;
- currentness exists only inside atomic publication against the store's current
  root;
- configuration updates remain configuration-only and activate for a later
  transition;
- weight, destination, and policy rotation is legal while stable domain
  identity and deficit state remain unchanged;
- domain creation, ID rotation, split, merge, retirement, and reuse remain
  absent from the initial V2 language;
- content storage remains an untrusted availability mechanism;
- Python/Rust canonical codecs and shared vectors remain feasible.

## 4. Exact migration projection correction

The phrase:

```text
all other economic namespaces = exact migration projections
```

is too open for an authority migration contract.

Revision 3.1 replaces it with explicit equalities for balances, pools, LP
balances, nonces, vault, oracle, and perps; a zero-dust requirement for the V1
fee accumulator; and construction of the canonical empty V2 fee-apportionment
state.

Any actual schema or semantic conversion in a retained namespace requires a
separately named relation and evidence.

## 5. Research Kernel disposition

Research Kernel now records:

```text
hypothesis_b1b_rev3_authenticated_bootstrap_v1:
  REFUTED

result_b1b_rev3_provenance_loss_counterexamples_v1:
  SUPPORTED actual counterexample

hypothesis_b1b_rev31_source_bound_authority_v1:
  TESTABLE
```

The Revision 3.1 refutation plan includes coordinated manifest/root mutation,
coordinated header/claim mutation, missing exact-state rebinding, unauthorized
ordinary header writes, hidden namespace conversion, and B1B-1 scope expansion.

No claim has been promoted to production authority.

## 6. Revised B1B-1 boundary

B1B-1 is narrower than both approving reviews proposed. It may implement only:

```text
FCISAuthorityHeaderV2
DeploymentBootstrapAnchorClaimV2
V1ToV2MigrationManifestV2
their exact field registries and schemas
canonical Python/Rust codecs and roots
shared positive and negative vectors
structural checker coverage for this limited scope
```

It may not implement:

```text
PinnedDeploymentBootstrapVerifierV2
VerifiedV1ToV2MigrationAuthorityV2
V1ToV2MigrationCandidateV2
FCISCommittedStateV2
StateBoundFeeDistributionConfigurationV2
migration execution or successor
configuration update
receipt, bundle, or proof input
authority mount
```

This boundary preserves progress on byte-level parity while the later
source-bound authority relations remain under review.

## 7. Evidence status

The review packet manifest verified all 30 bounded entries. Independent reviews
reported focused Python, Rust, golden-vector, and structural-checker results
against the existing B1A and apportionment substrate.

Those tests do not validate Revision 3 authority because Revision 3 was
documentation only. The blocking evidence is the source-level counterexample.

No mounted runtime file changed. No migration, state-bound authority, committed
V2 state, or publication path exists from this design work.

## 8. Decision

```text
Revision 2:   REFUTED for bootstrap and first-state authority
Revision 3:   REFUTED for source-provenance retention and header monopoly
B1B-1:        BLOCKED
Revision 3.1: TESTABLE, review-only
Mount:         PROHIBITED
```

The next action is a focused independent falsification review of Revision 3.1.
B1B-1 may begin only after:

```text
APPROVE_B1B1_REVISION_3_1_UNMOUNTED
```
