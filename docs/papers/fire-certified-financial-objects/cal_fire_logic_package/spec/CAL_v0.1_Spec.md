# CAL v0.1 Normative Specification

**Canonical Admissibility Logic for FIRE/ZenoDEX**
**Status:** normative draft for implementation agents
**Version:** v0.1

This specification defines the v0.1 core of Canonical Admissibility Logic (CAL). CAL is the formal logic used to state and check admissibility of FIRE financial objects.

Normative words `MUST`, `MUST NOT`, `SHOULD`, `MAY`, and `RECOMMENDED` are used in their ordinary RFC-style sense.

---

## 1. Scope

CAL v0.1 defines:

1. artifact-bound claims;
2. evidence-labeled claims;
3. witness-indexed bound claims;
4. collateral-safety claims;
5. delta-conservation claims;
6. replay-determinism claims;
7. settlement-admissibility claims;
8. refinement claims for non-authoritative object repair.

CAL v0.1 does not define a general-purpose theorem prover. The live verifier MUST check small proof certificates against admitted proof rules.

---

## 2. Canonical sources

The system MUST use the following canonical hierarchy:

```text
FMOS / FIRE Spec
  canonical for rules, semantics, evidence labels, proof rules, verifier rules

fire-stdlib
  canonical for reusable certified financial math objects and admitted rule objects

FIRE-IR object template
  canonical for reusable object semantics

FIRE instance manifest
  canonical for actual live position parameters, parties, maturity, nonce, settlement window

FIRE-Cert
  canonical for proof/evidence attached to object and/or instance hashes

FIRE Registry
  canonical for publication status only

ZPL, product cards, UI, whitepaper, marketing
  explanatory only, never settlement-canonical
```

A settlement implementation MUST NOT read semantics from ZPL, product cards, UI state, marketing copy, or registry prose.

---

## 3. Core sets and types

### 3.1 Evidence

```text
Evidence ::= proved | contract | implemented | tested_discovery | hypothesis
```

Ordering:

```text
proved > contract > implemented > tested_discovery > hypothesis
```

Meet operation:

```text
meet(e1, e2) = weaker(e1, e2)
```

Composite evidence MUST be the meet of all required dependencies.

### 3.2 Artifact hashes

```text
Hash ::= domain-separated digest of canonical bytes
```

Every hash MUST include a domain separator and version tag.

Required domain separators:

```text
FIRE_OBJECT_TEMPLATE_V1
FIRE_INSTANCE_V1
FIRE_CERT_V1
FIRE_DEP_LOCK_V1
FIRE_RECEIPT_V1
```

### 3.3 Dimensions and units

A unit dimension is an integer vector over the asset basis.

```text
Amount[A] has dimension e_A
Price[A/B] has dimension e_B - e_A
Index, Rate, Multiplier have dimension 0
```

The verifier MUST reject unit-invalid certificates.

### 3.4 Intervals

```text
Interval[tau] = { lower : tau, upper : tau, proof lower <= upper }
```

The canonical notation is:

```text
x in [L, U]
```

meaning:

```text
L <= x AND x <= U
```

---

## 4. Core predicates

### 4.1 Artifact predicates

```text
SchemaOK(O, I, Gamma)
HashBindOK(O, I, Gamma)
DependencyClosed(O)
CanonicalSerializeOK(A)
```

### 4.2 Object and instance predicates

```text
UnitOK(O)
DomainOK(O)
ParamOK(I, O)
AuthorizationOK(I)
NonceOK(I)
MaturityOK(I, w)
WindowOK(I, w)
```

### 4.3 Certificate predicates

```text
CertOK(O, I, Gamma)
EvidenceOK(Gamma)
ClaimEvidence(Gamma, claim) = evidence
EvidenceFloor(Gamma) = meet(all claim evidences)
```

### 4.4 Witness predicates

```text
WitnessOK(O, I, w)
FreshEnough(w)
ProvenanceOK(w)
ReplayBoundWitness(w, instance_hash)
```

### 4.5 Financial predicates

```text
BoundOK(O, I, f, L, U)
CollateralOK(O, I, C)
DeltaConservationOK(O, I, Delta)
IntegerEvalOK(O, I, w, Delta)
ReplayOK(O, I, w, Delta)
SettlementSafe(O, I, w, C)
```

### 4.6 Acceptance predicate

```text
FIREVAccept(O, I, Gamma, w, C)
```

---

## 5. Denotational semantics

A FIRE object instance denotes a partial function:

```text
[[O@I]] : WitnessBundle x CollateralTable -> DeltaTable OR bottom
```

where `bottom` means fail-closed rejection.

The verifier MUST return rejection, not a partial or best-effort delta, if any required gate fails.

---

## 6. Bound semantics

### 6.1 Witness-indexed bound

`BoundOK(O, I, f, L, U)` means:

```text
forall w,
  ParamOK(I, O) AND WitnessOK(O, I, w)
    -> L(O, I) <= f(O, I, w) <= U(O, I)
```

BoundOK MUST be over admissible witnesses, not arbitrary malformed witness data.

### 6.2 Interval certificate

```text
IntervalCert(x,L,U) := L <= x AND x <= U
```

Proof certificates MAY encode interval derivations using the admitted rules in Section 9.

---

## 7. Settlement safety semantics

`SettlementSafe(O, I, w, C)` means all of the following:

### 7.1 Collateral safety

For every party `p` and asset `a`:

```text
C[p,a] + Delta[p,a] >= 0
```

### 7.2 Delta conservation

For every asset `a`:

```text
sum_p Delta[p,a] + Fees[a] + Burns[a] - Mints[a] = 0
```

### 7.3 Deterministic replay

```text
same(O, I, w) -> same(Delta)
```

### 7.4 Integer boundedness

The integer evaluation MUST implement the FMOS fixed-point semantics and MUST NOT produce a payout exceeding the certified upper bound.

---

## 8. Main theorem

FIRE-VCore MUST be specified against this theorem:

```text
FIREVAccept(O, I, Gamma, w, C) -> SettlementSafe(O, I, w, C)
```

Expanded acceptance:

```text
FIREVAccept(O,I,Gamma,w,C) :=
  SchemaOK(O,I,Gamma)
  AND HashBindOK(O,I,Gamma)
  AND DependencyClosed(O)
  AND UnitOK(O)
  AND DomainOK(O)
  AND ParamOK(I,O)
  AND AuthorizationOK(I)
  AND NonceOK(I)
  AND MaturityOK(I,w)
  AND WindowOK(I,w)
  AND CertOK(O,I,Gamma)
  AND EvidenceOK(Gamma)
  AND WitnessOK(O,I,w)
  AND CollateralOK(O,I,C)
  AND IntegerEvalOK(O,I,w,Delta)
  AND DeltaConservationOK(O,I,Delta)
  AND ReplayOK(O,I,w,Delta)
```

---

## 9. Admitted proof rules v0.1

### 9.1 Unit rules

```text
same_dim(x,y) -> dim(x+y) = dim(x)
dim(x*y) = dim(x) + dim(y)
dim(x/y) = dim(x) - dim(y)
dim(log x) valid only if dim(x)=0
dim(exp x) valid only if dim(x)=0
```

### 9.2 Interval rules

Constants:

```text
const(c) in [c,c]
```

Addition:

```text
x in [Lx,Ux], y in [Ly,Uy]
-> x+y in [Lx+Ly, Ux+Uy]
```

Subtraction:

```text
x-y in [Lx-Uy, Ux-Ly]
```

Multiplication:

```text
xy in [min(LxLy,LxUy,UxLy,UxUy), max(LxLy,LxUy,UxLy,UxUy)]
```

Nonnegative scalar multiplication:

```text
a >= 0, x in [L,U] -> a*x in [aL,aU]
```

Positive part:

```text
pos(x)=max(x,0), x in [L,U]
-> pos(x) in [max(L,0), max(U,0)]
```

Cap:

```text
cap_C(x)=min(max(x,0),C), C>=0
-> cap_C(x) in [0,C]
```

Clamp:

```text
clamp(x,A,B), A<=B
-> clamp(x,A,B) in [A,B]
```

Finite sum:

```text
forall t, x_t in [L_t,U_t]
-> sum_t x_t in [sum_t L_t, sum_t U_t]
```

Guarded reciprocal:

```text
x in [eps,U], eps>0 -> 1/x in [1/U, 1/eps]
```

Guarded log:

```text
x in [eps,U], eps>0 -> log(x) in [log(eps), log(U)]
```

### 9.3 Collateral rules

One-sided writer:

```text
payoff in [0,U]
C_writer >= U
-> C_writer - payoff >= 0
```

Two-sided payoff:

```text
f in [L,U]
C_A >= max(0,-L)
C_B >= max(0,U)
-> C_A + f >= 0 AND C_B - f >= 0
```

### 9.4 Evidence rules

```text
[E1] P, [E2] Q -> [meet(E1,E2)] (P AND Q)
```

### 9.5 Hash binding rule

```text
h = H(domain_separator || canonical_bytes(A))
cert.names_hash = h
-> cert claims are artifact-bound to h
```

### 9.6 Settlement rule

```text
CertOK AND BoundOK AND CollateralOK AND WitnessOK
AND DeltaConservationOK AND ReplayOK AND IntegerEvalOK
-> SettlementSafe
```

---

## 10. Refinement / ORE

The FIRE object-refinement subsystem MUST be called **FIRE Refiner** or **ORE: Object Refinement Engine**. It MUST NOT be called Morph if that name conflicts with a private tool.

ORE is non-authoritative.

```text
RefineOK(R,O,O') AND FIREVAccept(O',I,Gamma,w,C)
  -> SettlementSafe(O',I,w,C)
```

The following is invalid:

```text
RefineOK(R,O,O') -> SettlementSafe(O')
```

Protective refinements that alter payoff semantics MUST require explicit user approval.

---

## 11. No-bypass invariant

The ledger adapter MUST enforce:

```text
FIREVReceiptOK(receipt) :=
  receipt.object_hash = object_hash
  AND receipt.instance_hash = instance_hash
  AND receipt.cert_sha256 = cert_sha256
  AND receipt.witness_hash = H(w)
  AND receipt.delta_hash = H(Delta)
```

```text
ApplyDeltas(Delta)
  -> exists receipt,
     FIREVReceiptOK(receipt)
     AND receipt.object_hash = object_hash
     AND receipt.instance_hash = instance_hash
     AND receipt.cert_sha256 = cert_sha256
     AND receipt.witness_hash = H(w)
     AND receipt.delta_hash = H(Delta)
```

No compiler, registry, Refiner, UI, product card, or admin path may apply deltas without a verifier receipt bound to the object, instance, certificate, witness bundle, and emitted delta.

---

## 12. Certificate requirements

FIRE-Cert MUST include:

```text
object_hash
instance_hash or template-only marker
claim list
per-claim evidence class
aggregate evidence floor
proof tree
rule identifiers
dependency hashes
fixed-point rounding assumptions
witness policy references
```

The verifier MUST reject a certificate if:

1. object hash mismatch;
2. instance hash mismatch where an instance is required;
3. unknown proof rule;
4. malformed proof tree;
5. evidence floor is overstated;
6. dependency hash mismatch;
7. rule preconditions are not met.

---

## 13. Security requirements

The live verifier MUST NOT trust:

```text
FIRE-C compiler
ZPL source
ORE/FIRE Refiner
product cards
UI
registry prose
whitepapers
simulation output
```

The live verifier MAY consume:

```text
canonical FIRE-IR object template
canonical FIRE instance
FIRE-Cert
valid witness bundle
posted collateral table
locked dependencies
```

---

## 14. Minimum viable CAL v0.1 implementation

Agents SHOULD implement the following first:

1. evidence lattice;
2. artifact hash binding;
3. unit checker;
4. interval proof checker;
5. collateral checker;
6. witness policy checker;
7. deterministic fixed-point evaluator;
8. delta conservation checker;
9. settlement admissibility checker;
10. `fire explain` derivation renderer.

---

## 15. Non-goals

CAL v0.1 does not attempt to prove:

```text
profit
price appreciation
oracle metaphysical truth
market liquidity
regulatory compliance
arbitrary user code safety
unbounded derivatives safety
```

CAL v0.1 proves admissibility of value movement under explicitly declared assumptions.
