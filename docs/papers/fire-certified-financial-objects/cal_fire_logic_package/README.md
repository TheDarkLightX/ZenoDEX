# CAL / FIRE Logic Package v0.1

This package defines **Canonical Admissibility Logic (CAL)**, also called **FIRE Logic** in product-facing contexts. CAL is a proof calculus for artifact-bound, evidence-labeled, witness-indexed, collateral-safe value movement.

It is designed for ZenoDEX/FIRE agents to implement a verifier-friendly logic layer around certified financial math objects.

## Files

- `spec/CAL_FireLogic_Book.md` - teaching document / mini-book.
- `spec/CAL_v0.1_Spec.md` - normative v0.1 specification.
- `agent/CAL_Agent_Build_Blueprint.md` - implementation instructions for agents.
- `stdlib/cal_stdlib_rules.yaml` - first reusable rule catalog.
- `schemas/fire_cert_rules.schema.json` - proof-rule certificate schema draft.
- `lean/CAL_Core_Skeleton.lean` - Lean skeleton for the core definitions and theorems.
- `../../../../lean-mathlib/Proofs/CALCoreSoundness.lean` - checked Lean bridge from the CAL acceptance shape to `CertifiedFinancialObject` collateral/replay safety.
- `examples/BurnBoostCall_CAL_Derivation.md` - worked derivation.
- `examples/CompoundRewardNote_CAL_Derivation.md` - worked derivation.
- `examples/CappedILCover_CAL_Derivation.md` - worked derivation.

## Core theorem

```text
FIREVAccept(O, I, Gamma, w, C) -> SettlementSafe(O, I, w, C)
```

where the accepted settlement is bound to canonical object and instance artifacts, evidence certificates, admissible witnesses, and sufficient collateral.

The package-local skeleton remains a proof target. The checked theorem-grade
artifact currently lives in the main Lean package as
`Proofs.CALCoreSoundness.fireV_accept_soundness`.

## Security boundary

CAL is a logic/specification layer. It is not settlement authority. FIRE-V and FIRE-Kernel remain the funds-moving authority.

```text
Refiner/ORE suggests. FIRE-C compiles. FIRE-V decides. FIRE-Kernel settles.
```
