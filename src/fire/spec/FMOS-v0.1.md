## FMOS v0.1

Canonical source for FIRE rules in the current migration slice.

### Canonical split

```text
FMOS / FIRE Spec -> canonical for rules
FIRE template manifest -> canonical for reusable object semantics
FIRE instance manifest -> canonical for live instance binding
FIRE cert -> canonical for evidence bound to template/instance hashes
```

Plain English: prose, UI, ZPL source, and product cards are explanatory only.

### Settlement rule

```text
FIREVAccept(O, I, Γ, w, C) -> SettlementSafe(O, I, w, C)
```

Plain English: only verifier acceptance over machine-readable artifacts may authorize settlement.

Runtime application also requires a verifier receipt bound to the runtime
authorization surface:

```text
FIREVReceiptOK(receipt) :=
  object_hash ∧ instance_hash ∧ cert_sha256 ∧ witness_hash ∧ delta_hash
```

Plain English: the receipt must bind the object, instance, certificate,
witness bundle, and emitted settlement delta before any delta application path
may proceed.

### Current bridge posture

In this repo today:
- object specs live as JSON object files under `src/fire/stdlib/objects`
- authoring sources live under `src/fire/zpl`
- `src/fire` is the canonical implementation boundary
- legacy `src/kernels/python/fire_*` modules are compatibility shims, not the
  intended long-term source of truth

### Non-authoritative tooling

```text
FIRE Refiner / ORE suggests
FIRE-C emits artifacts
FIRE-V checks
FIRE-Kernel settles
```

Plain English: no refinement, compiler, UI, or document bug may move funds by itself.
