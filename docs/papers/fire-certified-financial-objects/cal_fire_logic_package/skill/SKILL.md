# CAL / FIRE Logic Engineering Skill

Use this skill when designing, reviewing, or implementing CAL / FIRE Logic artifacts for ZenoDEX FIRE certified financial objects.

## Canonical source order

1. `spec/CAL_v0.1_Spec.md` is the normative logic specification.
2. `spec/CAL_FireLogic_Book.md` is the teaching/reference text.
3. `stdlib/cal_stdlib_rules.yaml` is the initial machine-readable rule catalog.
4. `schemas/fire_cert_rules.schema.json` is the FIRE-Cert proof-rule schema.
5. `agent/CAL_Agent_Build_Blueprint.md` is the implementation plan.
6. `lean/CAL_Core_Skeleton.lean` is only a formalization starting point, not a completed proof.

Do not treat product cards, UI text, marketing copy, or this skill file as canonical settlement semantics.

## Current repo compatibility notes

In the current Autonomous Tau DEX repo, these CAL sources live under:

```text
docs/papers/fire-certified-financial-objects/cal_fire_logic_package/
```

Keep these distinctions explicit:

```text
src/fire/spec/fire-cert.schema.json
  = current runtime FIRE cert schema

schemas/fire_cert_rules.schema.json
  = CAL proof-tree cert schema draft
```

Do not silently treat the CAL proof-tree schema as the current runtime cert schema.

The current runtime bundle filenames are:

```text
object_manifest.json
instance_manifest.json
object_lock.json
certificate.json
replay_input.json
replay_receipt.json
bundle_manifest.json
```

The CAL logical names:

```text
object.fire.json
instance.fire.json
object.firecert.json
object.lock.json
object.replay.json
```

are planned/logical names, not the current checked-in filenames. Use them only when doing an explicit migration.

## Core theorem to preserve

Every implementation must preserve the main admissibility theorem:

```text
FIREVAccept(O, I, Gamma, w, C) -> SettlementSafe(O, I, w, C)
```

where:

- `O` is the canonical FIRE-IR object template.
- `I` is the canonical object instance.
- `Gamma` is the FIRE-Cert proof/evidence bundle.
- `w` is the witness bundle.
- `C` is the posted collateral table.

The practical meaning is:

```text
CertOK and BoundOK and CollateralOK and WitnessOK and ReplayOK
  -> collateral-safe, delta-conserving, deterministic settlement.
```

## Required judgment forms

Use these judgment forms consistently:

```text
WitnessOK(w) -> L <= f(w) <= U
IntervalCert(x, L, U) := L <= x and x <= U
CollateralOK(C, Delta, L) := C >= max(0, -L)
ArtifactBound(h, P) := claim P is bound to canonical artifact hash h
Evidence(E, P) := claim P is supported at evidence class E
```

## Evidence discipline

Use the evidence order:

```text
proved > contract > implemented > tested_discovery > hypothesis
```

For composite claims, take the meet of dependencies. Never upgrade a composite object above its weakest required evidence dependency.

## Security boundary

The compiler, Refiner/ORE, product-card generator, registry UI, and docs are non-authoritative.

Only FIRE-V / FIRE-VCore acceptance may authorize settlement. No code path may apply deltas without a verifier receipt bound to the object hash, instance hash, witness bundle, and delta hash.

Private ESSO is an internal admission tool. Public runtime behavior and public CI must not depend on the ESSO toolchain being present.

## Naming rules

Use `FIRE Refiner` or `ORE` for the object-refinement subsystem. Do not use `Morph` in public or technical FIRE docs, because Morph is reserved for a separate private tool.

Use these replacement names:

```text
CapRefinement
ClampRefinement
CollateralRefinement
WitnessRefinement
UnitRepairRefinement
SpreadRefinement
TrancheRefinement
EvidenceRefinement
```

## Agent tasks

When implementing CAL/FIRE artifacts:

1. Read `spec/CAL_v0.1_Spec.md` first.
2. Check any rule against `stdlib/cal_stdlib_rules.yaml`.
3. Validate certificate artifacts against `schemas/fire_cert_rules.schema.json`.
4. Distinguish draft CAL proof-tree cert work from the current runtime cert schema in `src/fire/spec/fire-cert.schema.json`.
5. Keep template and instance artifacts separate.
6. Ensure every theorem or rule names its assumptions explicitly.
7. Preserve fail-closed behavior. Failed gates must reject, not degrade silently.
8. Add positive and negative tests for every rule.
9. Treat `lean/CAL_Core_Skeleton.lean` as a skeleton; fill missing proofs before claiming theorem-grade evidence.

## Red flags

Reject or mark simulation-only when any of these occur:

- Unbounded payoff.
- Missing witness policy.
- Insufficient collateral.
- Object hash/certificate hash mismatch.
- Instance not bound to object hash.
- Floating dependency version.
- Evidence floor manually asserted instead of derived.
- Product claim stronger than evidence allows.
- AMM theorem imported without its local/smooth/symmetric/homogeneous/fee-free assumptions.
- Any settlement path that bypasses FIRE-V.

## Output expectations

A complete CAL/FIRE implementation artifact should include:

```text
object.fire.json
instance.fire.json
object.firecert.json
object.lock.json
object.replay.json
registry entry
positive tests
negative tests
```

In the current repo, that output set should be read as the logical/canonical target. The checked-in runtime filenames may still use the existing bundle-era names until an explicit migration is performed.

A completed spec change should include:

```text
normative text
machine-readable rule/schema change
examples
negative examples
proof obligations
version/hash update notes
```
