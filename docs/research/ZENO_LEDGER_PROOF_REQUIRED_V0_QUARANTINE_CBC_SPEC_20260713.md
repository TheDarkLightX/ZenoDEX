# ZenoLedger Proof-Required V0 Quarantine CBC Specification

Status: implemented fail-closed quarantine, 2026-07-13.

## Scoped claim

Generic ZenoLedger V0 consumers with either `proof_required = true` or
`bridge_policy.requires_proof_journal = true` cannot grant checkpoint
admission, watcher-attestation, or Tau-export authority from a nonzero proof
journal, proof metadata, or caller-authored verification booleans.

The stable typed rejection is:

```text
proof_required.authenticated_cryptographic_authority_unavailable_v0
```

`validate_checkpoint_structural_compatibility_v0` remains available for local
diagnostics. It validates checkpoint/profile shape and commitments without
granting admission authority.

Caller-authored V0 proof-verification reports remain structural diagnostics.
The replay-bound verifier rejects `proof_verification_report_dir` and
`require_proof_verification_report`; a future authenticated receipt needs a
separate opaque capability path.

## Positive governed path

The replay-bound range verifier retains its strict Spot authority path. That
path verifies through `PinnedStrictSpotAuthorityVerifierV1`, resolves a
governed binding, checks the exact ledger state-domain bridge, and produces its
authenticated decision before reporting proof authority as satisfied.

The range verifier calls structural checkpoint compatibility before that
cryptographic step. It does not call the quarantined generic admission API.
Legacy metadata/report-only and V0 verifier-envelope paths remain unavailable.

## Authority boundary

```text
metadata, nonzero journal, or caller report
  -> bounded structural validation
  -> diagnostic observation only
  -> no generic checkpoint admission
  -> no proof-required watcher attestation
  -> no Tau export

strict governed Spot receipt
  -> pinned verifier and manifest
  -> exact state-domain bridge
  -> authenticated proof-authority decision
  -> replay-bound range report only
```

`validate_checkpoint_admission_v0` accepts only `checkpoint` and `profile`.
There is no report, `verified` Boolean, or capability parameter that can reopen
the generic V0 boundary.

## Disaster-state closure

Mallory may author a JSON report containing `risc0_verified: true`, or place a
nonzero digest into `proof_journal_hash`. Those values remain inspectable as
structural evidence. Generic admission, proof-required watcher creation, and
Tau export independently reject with the typed reason above.

Executable reachability tests cover:

- a nonzero proof journal at generic checkpoint admission;
- a fabricated accepted watcher report;
- a caller-authored proof-verification report presented to replay-bound mode;
- a Tau export attempt;
- a bridge policy requiring a proof journal while the profile flag is false;
- the absence of report/Boolean escape parameters from generic admission.

The existing strict Spot range-authority suite separately protects the
governed positive path.

## Non-claims

This change does not establish:

- generic V0 production proof authority;
- arbitrary-profile completion of the RISC0 proof-to-ledger chain in issue
  #412;
- settlement, bridge, release, watcher-proof, or production authority;
- a generic DA or finality certificate;
- TEE authority;
- proof generation, proof reproducibility, or proof-system soundness.

Opening another positive path requires an opaque authenticated capability,
consensus-bound verifier policy, canonical journal binding, and executable
negative evidence at every consuming authority boundary.
