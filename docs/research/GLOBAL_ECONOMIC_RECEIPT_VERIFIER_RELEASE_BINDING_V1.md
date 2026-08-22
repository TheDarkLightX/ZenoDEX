# Global Economic Receipt Verifier Release Binding V1

Status: `IMPLEMENTED_TESTED_DISCOVERY`, unmounted.

Production authority: `NONE`.

## Obligation

Select one receipt-verifier release from the registry committed by the active
economic profile, bind it to one deployment and one measured implementation
artifact, then expose receipt verification through an opaque process-local
capability. A caller cannot substitute a protocol-shaped verifier object at the
durable publication boundary.

The protected invariant is:

```text
Profile.verifier_registry_root = Registry.root
Profile.root_image_id = SelectedRelease.root_image_id
MeasuredArtifact.root = SelectedRelease.implementation_root
Manifest.root = SelectedRelease.evidence_manifest_root
Request.image_id = SelectedRelease.root_image_id
```

Every equality is exact and type-sensitive. One release is selected for the
closed purpose `RESEARCH_SHADOW` or `PRODUCTION_NEW`. An `ACTIVE_NEW` release
requires the complete evidence set declared by V1. The current publisher
requires `RESEARCH_SHADOW`, so this implementation cannot promote itself into a
production verifier path.

## Preflight and pattern selection

Affected authority surfaces:

- profile-owned verifier registry and root-image selection;
- verifier evidence, implementation, and backend-protocol binding;
- genesis and ordinary-epoch receipt admission;
- the verifier-to-SQLite publisher boundary;
- the journal's process-local write capability.

The canonical economic epoch schemas, effects, roots, and SQLite linearization
point are unchanged. This change narrows who may propose receipt acceptance.

Alternatives considered:

1. Accept any object matching the verifier protocol. This leaves verifier
   selection with the caller and was rejected.
2. Store verifier metadata on a caller-constructible dataclass. This allows
   authority-shaped data to be forged and was rejected.
3. Resolve a profile-committed release and issue a data-slot-free capability
   whose authority is retained in a private weak registry. This is implemented.
4. Load and attest a deployed executable in a separate verifier service. This
   is the production-oriented successor and remains unimplemented.

The selected pattern makes profile, release, manifest, artifact, deployment,
image, byte ceilings, and purpose one owned aggregate. The publisher retains
the capability identity, release ID, and binding root across each backend call.

## Mechanical guarantees

- release IDs are content-derived from proof-system and verifier coordinates;
- registry roots commit release status, purpose-relevant evidence, and exact
  release contents;
- unknown, duplicate, unsorted, ambiguous, or profile-mismatched releases fail
  closed;
- shadow and active release states have separate evidence requirements;
- manifest coordinates and evidence statuses must exactly match the release;
- measured artifact bytes must match the release implementation root;
- the backend protocol has a deterministic root and exact success contract;
- receipt, journal, and image boundaries are checked before backend execution;
- backend success is exactly `None`; truthy or other return values reject;
- verifier authority coordinates are rechecked after backend execution;
- the durable publisher accepts only the opaque bound-verifier type;
- the journal commit additionally requires an instance-bound write capability.

## Non-guarantees and trusted premises

The backend object and artifact bytes are supplied by the integration caller.
V1 does not securely open a deployed executable, bind a process image, attest a
remote verifier service, or replay a real RISC0 receipt. Python process privacy,
weak registries, and underscore-prefixed functions do not form a security
boundary against code executing in the same interpreter.

Evidence statuses and artifact roots are exact committed data in this slice;
they are not derived from independently replayed checker receipts. A production
promotion gate must derive each status from exact-subject evidence rather than
trusting a release producer's labels.

The trusted constructors are
`bind_economic_receipt_verifier_deployment_v1`, the publisher `create`/`open`
methods, and the module-private journal factory. Production use also requires an
OS-separated verifier loader/service, authenticated deployment configuration,
active release evidence, Rust/RISC0 parity, and exclusive durable writer
fencing.

## Counterexamples and lifecycle behavior

- stale or wrong registry roots reject before capability construction;
- multiple releases eligible for one purpose reject as ambiguous;
- wrong image, deployment, manifest, artifact, byte ceiling, or backend
  protocol rejects;
- hostile mutation of a frozen release is detected by reconstruction;
- generic verifier objects reject before their backend method is called;
- a foreign journal write capability rejects before SQLite mutation;
- a verifier capability cannot be serialized as authority; durable restart
  reconstructs it from the profile, registry, manifest, artifact, deployment,
  and backend premises;
- migration to a different verifier requires a new profile/registry root and a
  separately reviewed activation path.

Concurrency and crashes retain the existing publisher behavior. Receipt
verification is side-effect-free with respect to the journal. The SQLite
transaction remains the sole durable ordinary-epoch publication point.

## Evidence hooks

The focused deterministic tests use Arrange/Act/Assert structure and cover
unique selection, evidence-state closure, registry and image mismatch, measured
artifact mismatch, manifest-coordinate mutation, receipt byte BVA at 0/1/max/
max+1, wrong backend return shape, generic-verifier rejection, reflective
release mutation, capability construction denial, absent public journal commit,
and cross-journal write-capability rejection.

Rust enforcement and Python/Rust/RISC0 differential replay are absent. This
document records implementation evidence only. It does not establish
`PROVED`, `MOUNTED`, `NO_BYPASS`, `RELEASE_BACKED`, or production readiness.
