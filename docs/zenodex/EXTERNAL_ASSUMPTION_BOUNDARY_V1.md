# External Assumption Boundary v1

## Purpose

This note states the strongest honest assurance claim available when part of the
execution or proof surface is controlled outside this repository.

For the Tau-native signer-registry and app-hash provenance lanes, the limiting
fact is:

- ZenoDEX does not control the Tau Testnet codebase
- Tau node behavior is therefore an external contract surface
- stronger end-to-end claims must remain conditional on that external surface

In practice, that means the repo can prove the host-side logic and fail-closed
behavior, but it cannot honestly claim a full proof of the upstream Tau node
implementation or network semantics.

## Core Conditional Law

```text
HostArtifactsOK
  := LoaderOK
   ∧ TransportRefinementOK
   ∧ ViewContractsOK

ExternalTauContractOK
  := upstream_tau_node_exposes_expected_command_surface
   ∧ upstream_tau_node_emits_payloads satisfying typed view contracts
   ∧ upstream_tau_node_does_not silently downgrade required provenance lanes

ConditionalCorrectness
  := HostArtifactsOK ∧ ExternalTauContractOK
   -> AdmissionBehaviorMatchesPublishedContract
```

The fail-closed corollary is:

```text
¬ExternalTauContractOK
  -> reject
   ∨ disable_stronger_path
   ∨ narrow_public_claim
```

## What Is Under ZenoDEX Control

- host-side typed parsers
- settlement signer-registry loader logic
- fail-closed policy and snapshot binding
- Tau app-hash provenance checks
- formal ESSO / TLA+ / Lean artifacts in this repository
- executable parity tests and focused release gates in this repository

## What Is Not Under ZenoDEX Control

- the upstream Tau Testnet implementation
- the exact semantics of its TCP transport handlers
- whether or when commands like `gettaustate <state_hash>` are shipped
- node honesty, uptime, or network-level non-equivocation

## Release Discipline

Release-facing documents must therefore distinguish:

- `proved in-repo host-side contract`
- `observed live-node conformance`
- `external assumption`

They must not collapse those into a single “proved Tau-native end-to-end”
statement unless the upstream Tau boundary itself is brought under proof or
under equivalent machine-checked contract control.

## Practical Rule

Use these labels consistently:

- `proved`: mechanized or replay-gated within this repository
- `observed`: checked against a running external Tau node
- `assumed`: required from the external Tau surface but not proved here

That is the correct maximum-assurance posture for a dependency controlled by an
external maintainer.
