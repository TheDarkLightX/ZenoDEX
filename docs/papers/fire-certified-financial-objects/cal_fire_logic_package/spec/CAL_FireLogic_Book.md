# Canonical Admissibility Logic for FIRE/ZenoDEX

**Version:** CAL / FIRE Logic v0.1
**Status:** design draft for agents
**Audience:** protocol engineers, formal-methods agents, compiler/verifier agents, product safety reviewers

---

## 0. Purpose

Canonical Admissibility Logic, abbreviated **CAL**, is a proposed logic for proof-carrying financial settlement. Product-facing documents may call it **FIRE Logic**. It is designed to be the reasoning layer underneath FIRE, the Formula-Invariant-Risk-Evidence system for certified financial objects on ZenoDEX.

The purpose of CAL is not to replace FIRE. FIRE is the system. CAL is the meta-logic that explains and formalizes why FIRE objects are admissible to settle.

The core slogan is:

```text
Truth is not enough for finance. Value movement needs admissibility.
```

Ordinary logic asks whether a proposition is true. Temporal logic asks whether a proposition holds now, eventually, always, or until some condition. Deontic logic asks whether an action is obligatory, permitted, or forbidden. CAL asks a more operational question:

```text
Is this exact value-moving transition admissible to execute under canonical artifacts, valid witnesses, sufficient collateral, deterministic integer semantics, and checkable evidence?
```

The central theorem is:

```text
FIREVAccept(O, I, Gamma, w, C) -> SettlementSafe(O, I, w, C)
```

where:

- `O` is a canonical FIRE object template.
- `I` is a canonical FIRE instance.
- `Gamma` is the FIRE certificate/evidence object.
- `w` is the witness bundle.
- `C` is the collateral table.

Settlement safety is deliberately narrow. It means:

```text
CollateralSafe AND DeltaConserved AND ReplayDeterministic AND IntegerEvalWithinBounds
```

It does **not** mean profit, token appreciation, perfect oracle truth, market liquidity, or legal safety.

---

## 1. What CAL adds beyond FIRE

FIRE already gives the practical architecture:

```text
FMOS / FIRE Spec -> canonical rules
fire-stdlib -> reusable certified math objects
ZPL -> authoring language
FIRE-C -> compiler
FIRE-IR -> canonical object semantics
FIRE-Cert -> proof/evidence
FIRE-V -> verifier
FIRE-Kernel -> deterministic evaluator
FIRE Registry -> publication status
```

CAL gives the formal proof calculus behind those pieces. It turns procedural gates into derivable judgments.

A normal implementation might say:

```text
if UnitOK and BoundOK and CollateralOK and WitnessOK:
    accept
```

CAL states the inference rule:

```text
CertOK    BoundOK    CollateralOK    WitnessOK    ReplayOK    DeltaOK
---------------------------------------------------------------------
                         SettlementSafe
```

CAL is useful because it gives agents a common language for:

1. composition of financial math objects;
2. evidence non-inflation;
3. artifact-bound truth;
4. witness-indexed bounds;
5. collateral safety;
6. deterministic replay;
7. fail-closed settlement;
8. non-authoritative refinement;
9. theorem-boundary enforcement;
10. formal verifier specifications.

---

## 2. Basic ontology

CAL models value movement using the following entities.

### 2.1 Artifact entities

```text
O  : object template / FIRE-IR object manifest
I  : object instance / live position manifest
Gamma : certificate or proof/evidence bundle
D  : dependency lock set
R  : registry entry
```

The object template defines reusable semantics. The instance binds actual parties, parameter values, maturity, nonce, collateral references, and settlement window.

### 2.2 Runtime entities

```text
w : witness bundle
C : collateral table
Delta : settlement delta table
L, U : lower and upper bounds
```

### 2.3 Hash entities

```text
hO = object_hash
hI = instance_hash
hG = certificate_hash
hD = dependency_hash
```

A CAL claim about an object is not valid unless it is bound to the exact canonical artifact hash.

### 2.4 Evidence entities

Evidence lives in a finite lattice:

```text
proved > contract > implemented > tested_discovery > hypothesis
```

The evidence grade of a composite claim is the meet, or weakest required dependency.

For example:

```text
proved MEET contract = contract
contract MEET implemented = implemented
implemented MEET hypothesis = hypothesis
```

---

## 3. Judgments

CAL has several judgment forms.

### 3.1 Unit and interval judgment

```text
Gamma |- e : tau [L, U]
```

Read as:

```text
Under assumptions Gamma, expression e has type/unit tau and value in interval [L, U].
```

Example:

```text
Gamma |- x : Index [0, 1]
```

### 3.2 Bound judgment over witnesses

```text
Gamma |- BoundOK(f, L, U)
```

means:

```text
forall w, WitnessOK(w) -> L <= f(w) <= U
```

More precisely, with object and instance:

```text
ParamOK(I, O) AND WitnessOK(O, I, w)
  -> L(O, I) <= f(O, I, w) <= U(O, I)
```

### 3.3 Artifact-bound judgment

```text
Box[h] P
```

Read as:

```text
Claim P applies to the canonical artifact with hash h.
```

For example:

```text
Box[object_hash] BoundOK(O)
```

### 3.4 Evidence-labeled judgment

```text
[E] P
```

Read as:

```text
Claim P is supported at evidence class E.
```

Example:

```text
[proved] BoundOK(f, 0, N*Cap)
[contract] WitnessOK(BurnCertificate[TDEX])
```

### 3.5 Settlement judgment

```text
Gamma; E; W; C |- O@I Downarrow Delta : Safe[L, U]
```

Read as:

```text
Under assumptions Gamma, evidence E, witnesses W, and collateral C, object template O at instance I evaluates to canonical deltas Delta and is safe within bounds [L, U].
```

This is the central CAL judgment.

---

## 4. CAL semantics

A CAL model is:

```text
M = (Artifacts, Instances, WitnessWorlds, CollateralStates, EvidenceLattice, DeltaTables, LedgerStates)
```

A FIRE object denotes a partial function:

```text
[[O@I]] : (w, C) -> Delta OR bottom
```

where `bottom` means reject/fail-closed.

```text
[[O@I]](w, C) = Delta     if all admissibility gates pass
[[O@I]](w, C) = bottom    otherwise
```

Rejection is not an exceptional runtime state. It is the safe default.

---

## 5. Core predicates

CAL v0.1 standardizes these predicates.

### 5.1 Artifact predicates

```text
SchemaOK(O, I, Gamma)
HashBindOK(O, I, Gamma)
DependencyClosed(O)
CanonicalSerializeOK(O)
CanonicalSerializeOK(I)
```

### 5.2 Object predicates

```text
UnitOK(O)
DomainOK(O)
ParamOK(I, O)
CertOK(O, Gamma)
EvidenceOK(Gamma)
```

### 5.3 Witness predicates

```text
WitnessOK(O, I, w)
FreshEnough(w)
ProvenanceOK(w)
ReplayBoundWitness(w, hI)
```

### 5.4 Financial predicates

```text
BoundOK(O, I, f, L, U)
CollateralOK(O, I, C)
DeltaConservationOK(O, I, Delta)
IntegerEvalOK(O, I, w, Delta)
ReplayOK(O, I, w, Delta)
```

### 5.5 Authorization predicates

```text
AuthorizationOK(I)
NonceOK(I)
MaturityOK(I, w)
WindowOK(I, w)
```

### 5.6 Final predicates

```text
FIREVAccept(O, I, Gamma, w, C)
SettlementSafe(O, I, w, C)
```

---

## 6. LiveOK gate

The standard live gate is:

```text
LiveOK =
  SchemaOK
  AND HashBindOK
  AND DependencyClosed
  AND UnitOK
  AND DomainOK
  AND ParamOK
  AND CertOK
  AND EvidenceOK
  AND WitnessOK
  AND CollateralOK
  AND IntegerEvalOK
  AND DeltaConservationOK
  AND ReplayOK
  AND AuthorizationOK
  AND NonceOK
  AND MaturityOK
  AND WindowOK
```

For v0.1, agents may implement a subset, but the full predicate must remain visible.

Alternative witness lanes are modeled by disjunction:

```text
WitnessOK =
  (PricePacketOK AND FreshEnough AND ProvenanceOK)
  OR SignedAttestationOK
```

Disjunction does not magically strengthen evidence. The selected branch determines the evidence class.

---

## 7. Inference rules

### 7.1 Evidence meet rule

```text
[E1] P    [E2] Q
-------------------------
[E1 MEET E2] (P AND Q)
```

This is the evidence non-inflation rule.

### 7.2 Artifact binding rule

```text
h = H(canonicalSerialize(A))    CertNames(Gamma, h)
----------------------------------------------------
Box[h] ClaimsHold(Gamma, A)
```

If the hash does not match, no claims in the certificate may be used for that artifact.

### 7.3 Bound introduction rule

```text
forall w, WitnessOK(w) -> L <= f(w) <= U
------------------------------------------------
BoundOK(f, L, U)
```

With template and instance:

```text
forall w, ParamOK(I,O) AND WitnessOK(O,I,w)
    -> L(O,I) <= f(O,I,w) <= U(O,I)
----------------------------------------------------------------
BoundOK(O,I,f,L,U)
```

### 7.4 Collateral rule

For party `i` and asset `a`:

```text
BoundOK(Delta_i,a, L_i,a, U_i,a)
C_i,a >= max(0, -L_i,a)
----------------------------------
CollateralSafe(i, a)
```

For a two-party payoff where Alice receives `f` and Bob receives `-f`:

```text
f in [L, U]
C_Alice >= max(0, -L)
C_Bob >= max(0, U)
-------------------------------
NoMechanicalDefault
```

### 7.5 Delta conservation rule

```text
forall asset a,
  sum_i Delta_i,a + Fees_a + Burns_a - Mints_a = 0
--------------------------------------------------
DeltaConservationOK
```

For ordinary cash-settled derivatives, fees/burns/mints are zero.

### 7.6 Replay determinism rule

```text
same(O, I, w) -> same(Delta)
----------------------------
ReplayOK(O, I, w, Delta)
```

### 7.7 Settlement admissibility rule

```text
CertOK    BoundOK    CollateralOK    WitnessOK
DeltaConservationOK    ReplayOK    IntegerEvalOK
-------------------------------------------------
SettlementSafe
```

This is the most important inference rule in CAL v0.1.

---

## 8. Interval calculus

CAL inherits the interval calculus used by certified financial math objects.

### 8.1 Constants

```text
c in [c, c]
```

### 8.2 Addition

```text
x in [Lx, Ux]
y in [Ly, Uy]
---------------------------
x + y in [Lx + Ly, Ux + Uy]
```

### 8.3 Subtraction

```text
x - y in [Lx - Uy, Ux - Ly]
```

### 8.4 Multiplication

```text
xy in [min(LxLy, LxUy, UxLy, UxUy), max(LxLy, LxUy, UxLy, UxUy)]
```

### 8.5 Positive part

```text
pos(x) = max(x, 0)
x in [L, U]
--------------------------------------
pos(x) in [max(L, 0), max(U, 0)]
```

### 8.6 Cap

```text
cap_C(x) = min(max(x, 0), C)
C >= 0
--------------------------------------
0 <= cap_C(x) <= C
```

### 8.7 Clamp

```text
clamp(x, A, B) = min(max(x, A), B)
A <= B
--------------------------------------
A <= clamp(x,A,B) <= B
```

### 8.8 Finite sum

```text
forall t, x_t in [L_t, U_t]
-----------------------------------------
sum_t x_t in [sum_t L_t, sum_t U_t]
```

---

## 9. Unit calculus

Assets are represented as basis vectors:

```text
e_ETH, e_zUSD, e_TDEX, ...
```

An amount of asset `A` has dimension:

```text
[A] = e_A
```

A price of `A` in `B`, meaning `B per A`, has dimension:

```text
[Price[A/B]] = e_B - e_A
```

A percentage, multiplier, rate, burn index, reward index, or volatility index is dimensionless:

```text
[Index] = 0
```

Rules:

```text
[x] = [y] -> [x + y] = [x]
[xy] = [x] + [y]
[x/y] = [x] - [y]
log(x) requires [x] = 0
exp(x) requires [x] = 0
```

Example:

If protocol revenue `R_t` is in zUSD and token price `P_t` is zUSD per TDEX, then token buyback quantity is:

```text
q_t = lambda * R_t / P_t
```

because:

```text
zUSD / (zUSD/TDEX) = TDEX
```

The formula `q_t = lambda * R_t` is not a TDEX amount. CAL must reject it as a unit error if `q_t` is declared as `Amount[TDEX]`.

---

## 10. Evidence logic

CAL uses an evidence lattice:

```text
proved > contract > implemented > tested_discovery > hypothesis
```

The composite evidence grade is the meet of every required component.

If:

```text
[proved] BoundOK
[contract] WitnessOK
[implemented] ReplayOK
```

then:

```text
[implemented] SettlementSafe
```

because:

```text
proved MEET contract MEET implemented = implemented
```

A product card may show the aggregate evidence floor, but FIRE-Cert must retain the per-claim evidence vector.

---

## 11. Refinement logic and ORE

The private tool name `Morph` should not be reused for the FIRE subsystem. The recommended FIRE term is:

```text
ORE = Object Refinement Engine
```

User-facing name:

```text
FIRE Refiner
```

ORE is not trusted. It may propose transformations, but its output must still compile and verify.

```text
Refiner suggests. FIRE-C compiles. FIRE-V decides. FIRE-Kernel settles.
```

### 11.1 Refinement judgment

```text
RefineOK(R, O, O')
```

means rule `R` transforms draft object `O` into candidate object `O'`.

The safety theorem is not:

```text
RefineOK(R,O,O') -> SettlementSafe(O')
```

The correct theorem is:

```text
RefineOK(R,O,O') AND FIREVAccept(O',I,Gamma,w,C)
  -> SettlementSafe(O',I,w,C)
```

### 11.2 Semantics-preserving refinement

```text
[[O]] = [[O']]
```

Examples:

```text
inline dependency
normalize syntax
lower ZPL sugar into FIRE-IR
```

### 11.3 Protective refinement

Protective refinement changes economics to add safety.

Example:

```text
f -> min(max(f, 0), Cap)
```

Guarantee:

```text
0 <= f' <= Cap
```

Such refinements require explicit user approval because they change payoff semantics.

---

## 12. No-bypass theorem

CAL must include a no-bypass invariant:

```text
ApplyDeltas(Delta) -> exists receipt, FIREVReceiptOK(receipt)
```

The receipt predicate is a binding predicate, not a loose status flag:

```text
FIREVReceiptOK(receipt) :=
  receipt.object_hash = object_hash
  AND receipt.instance_hash = instance_hash
  AND receipt.cert_sha256 = cert_sha256
  AND receipt.witness_hash = H(w)
  AND receipt.delta_hash = H(Delta)
```

More explicitly:

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

This prevents compiler, UI, registry, product-card, or Refiner bugs from moving funds by requiring every applied delta to be tied to the accepted object, instance, certificate, witness bundle, and delta.

---

## 13. Template and instance distinction

CAL distinguishes object templates from object instances.

### 13.1 Template

```text
O = reusable object semantics
```

Example:

```text
BurnBoostCall(N, K, Cap)
```

with parameter bounds:

```text
N in [0, 1_000_000]
K in [0, 1]
Cap in [0, 0.50]
```

### 13.2 Instance

```text
I = actual live position
```

Example:

```text
holder = Alice
writer = Bob
N = 100_000
K = 0.05
Cap = 0.20
maturity = 2026-07-01
nonce = ...
```

The theorem is parameterized:

```text
ParamOK(I,O) AND WitnessOK(O,I,w)
  -> L(I) <= f(O,I,w) <= U(I)
```

Settlement binds to the instance hash, not only the template hash.

---

## 14. Relationship to deontic logic

CAL is deontic-adjacent but not the same.

Deontic logic says:

```text
P(settle) = settlement is permitted
O(collateralized) = collateralization is obligatory
F(uncollateralized_settlement) = uncollateralized settlement is forbidden
```

CAL says:

```text
O@I Downarrow Delta : Safe[L,U]
```

meaning:

```text
this exact object instance, with this exact certificate, witness bundle, and collateral table, produces these canonical deltas and satisfies mechanical settlement safety.
```

Deontic permission is qualitative. CAL admissibility is artifact-bound, evidence-labeled, witness-indexed, quantitative, and executable.

---

## 15. Relationship to AMM theorem objects

The AMM local frontier theorem can be imported as a theorem object:

```text
[proved] (Smooth AND Symmetric AND Homogeneous AND Local AND FeeFree -> S*C = 1/8)
```

Any FIRE object or product card importing that theorem must carry the assumptions. If those assumptions do not hold, the claim must be downgraded to `hypothesis` or `simulation_only`.

This makes theorem-boundary honesty a logic rule rather than a prose warning.

---

## 16. Worked example: BurnBoostCall

Payoff:

```text
f(w) = N * min(max(B_T(w) - K, 0), Cap)
```

Assumptions:

```text
N >= 0
Cap >= 0
WitnessOK(w) -> B_T(w) in [0, Bmax]
```

Derivation:

```text
max(B_T - K, 0) >= 0
min(max(B_T - K, 0), Cap) <= Cap
0 <= min(max(B_T - K, 0), Cap) <= Cap
0 <= N * min(max(B_T - K, 0), Cap) <= N * Cap
```

Therefore:

```text
BoundOK(f, 0, N*Cap)
```

Writer collateral:

```text
C_writer >= N*Cap
```

Then:

```text
C_writer - f(w) >= 0
```

If witness, replay, delta conservation, authorization, nonce, maturity, and hash binding also pass:

```text
SettlementSafe
```

---

## 17. What agents should implement first

1. CAL predicate data structures.
2. Evidence lattice and meet operation.
3. Artifact-bound hash predicates.
4. Interval proof rules.
5. Unit proof rules.
6. Collateral proof rules.
7. Delta conservation proof rules.
8. Settlement admissibility proof rule.
9. FIRE-Cert proof tree checker.
10. `fire explain` derivation display.

Do not implement arbitrary theorem proving in the live verifier. FIRE-V should check small proof certificates.

---

## 18. Limits

CAL does not prove:

```text
profit
future liquidity
token appreciation
oracle truth beyond witness assumptions
regulatory safety
market demand
arbitrary user code safety
```

CAL proves admissibility of value movement under declared assumptions.

---

## 19. Summary

CAL is the logic of proof-carrying financial settlement.

The key transition is:

```text
from truth to admissibility
from prose to canonical artifacts
from permission to replay-verifiable settlement
from formulas to bounded collateral-safe deltas
from evidence claims to evidence-labeled derivations
```

The core theorem remains:

```text
FIREVAccept(O, I, Gamma, w, C) -> SettlementSafe(O, I, w, C)
```

Everything else is infrastructure for making that theorem compositional, auditable, and hard to bypass.
