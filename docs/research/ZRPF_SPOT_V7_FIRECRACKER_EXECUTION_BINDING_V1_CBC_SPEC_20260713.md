# ZRPF Spot V7 Firecracker Execution Binding V1 CBC Specification

Date: 2026-07-13

Status: exact static execution-data binding implemented; governed live jailed
execution capability, settlement authority, and production authority remain
unavailable

## Purpose

The Spot V7 settlement candidate already binds the authenticated V7 receipt,
journal, effect plan, and economic state transition. The Firecracker output
decoder already binds the fixed request, committed output image, and nested
Spot V7 payload at the byte level. The remaining runtime seam must establish
that one governed jailed lifecycle owned the exact artifacts, request, output,
and teardown before it can mint the private settlement capability.

The current Firecracker controller emits ordinary launch and finish
observation documents. Those documents have no cryptographic or
process-local authority. The committed output marker is an unkeyed completion
and internal-binding commitment. It is not an attestation of execution.

This V1 slice closes the deterministic data join while preserving the exact
missing authority condition:

```text
governed policy proposal
  + observed artifact identities
  + exact fixed Firecracker request
  + exact committed output image
  + exact Spot V7 settlement candidate
  + canonical launch and finish observations
  -> exact static execution record
  -> authority-false binding assessment
  -> no governed runtime or settlement capability
```

## Exact bindings

`_zrpf_spot_v7_firecracker_execution_binding.py` validates all of these values
as one bounded deterministic object:

```text
nonzero 256-bit run nonce
canonical Firecracker profile digest
exact runtime-manifest bytes and request-bound SHA-256
input-drive SHA-256
replay-intent SHA-256
artifact-set identity
Firecracker and Jailer executable identities
guest kernel, rootfs, input image, and guest-init identities
fixed output-device size and payload cap
request digest carried by the committed output
complete output-device commitment and trailing-zero rules
exact nested Spot V7 output, journal, and settlement-plan bytes
exact Spot V7 receipt, program, manifest, state, and effect bindings
canonical launch observation and exact cgroup path
canonical finish observation, process exit, cgroup kill, and empty teardown
candidate copy of the canonical execution record
```

Any single mismatch rejects with a stable typed code. The lifecycle documents
must contain the exact authority-false field set. A publisher-supplied `true`
authority field rejects.

## Authority boundary

Successful static verification returns only
`_AuthorityFalseSpotV7FirecrackerExecutionBindingV1`. It permanently reports:

```text
static_binding_verified = true
governed_execution_result_verified = false
firecracker_execution_verified = false
settlement_authority = false
production_authority = false
```

The object has no runtime or binder seal. Passing it to the existing
Firecracker settlement binder rejects. The module cannot construct either
`_GovernedJailedFirecrackerExecutionV1` or
`_GovernedFirecrackerSpotV7SettlementV1`.

The exact remaining blocker is:

```text
governed_live_jailed_execution_result_capability_missing
```

The policy and artifact records used by this detector are proposed and
observed data. Their internal consistency does not prove policy governance,
release admission, source-to-binary identity, privileged execution, or
historical provenance. A final governed Spot V7 runtime-manifest schema that
derives every artifact role and identity from the manifest is also still
required.

## Negative evidence

Focused tests reject independent mutation of:

```text
run nonce
runtime-manifest binding
input-drive binding
replay-intent binding
artifact identity
canonical Firecracker profile
launch cgroup path
finish teardown facts
committed output marker
canonical execution-record copy
lifecycle JSON canonical form
publisher-supplied settlement authority
```

The architecture ratchet includes the new module in its no-public-alias,
no-export, and no-authority-capability reachability checks. Required ZRPF CI
includes the module and tests in Ruff, mypy, and pytest lanes.

## Non-claims

This evidence does not establish:

```text
live privileged Firecracker or Jailer execution
root-owned immutable V7 artifact staging
final governed Spot V7 runtime-manifest and artifact-role validation
exclusive network-namespace ownership
pre-exec cgroup and sandbox enforcement
same-UID mutation resistance
hardware attestation
release or revocation authority
data availability or external finality
settlement or production authority
```

## Next safe implementation step

The root-owned launcher must add a private one-shot execution API that owns the
complete lifecycle:

```text
governed release and runtime policy
  -> stable root-owned artifact descriptors
  -> fresh nonce and exact request
  -> preconfigured cgroup and exclusive network namespace
  -> jailed Firecracker launch
  -> exact output read through the retained descriptor
  -> Spot V7 payload decode and candidate binding inside the lifecycle
  -> cgroup kill and populated=0 teardown
  -> private _GovernedJailedFirecrackerExecutionV1
```

That mint site must consume a Spot V7-specific governed runtime manifest and
artifact set. It must not reconstruct authority from the observation
documents checked by this V1 detector. Release admission, operational DA and
finality gates, and the final atomic economic store remain separate required
capabilities.
