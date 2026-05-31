# Agent Build Blueprint: CAL / FIRE Logic v0.1

**Purpose:** Give implementation agents enough context to build a practical CAL/FIRE Logic layer around FIRE certified financial objects.

---

## 1. Agent objective

Build a minimal, checkable logic layer that supports the theorem:

```text
FIREVAccept(O, I, Gamma, w, C) -> SettlementSafe(O, I, w, C)
```

Do not build a general theorem prover. Build a small proof-rule checker and derivation format for FIRE-Cert.

---

## 2. Required repository tree

Recommended monorepo layout:

```text
fire/
  spec/
    CAL_v0.1_Spec.md
    CAL_FireLogic_Book.md
    fire-ir.schema.json
    fire-instance.schema.json
    fire-cert.schema.json
    verifier-rules.yaml
    evidence-lattice.yaml
    canonical-serialization.md

  stdlib/
    core/
    functions/
    state/
    payoffs/
    collateral/
    witnesses/
    amm/
    refinements/

  proofs/
    lean/
      CAL/
        CAL_Core_Skeleton.lean

src/fire/
  python/
    firec/
    refiner/
    cli/
    product_cards/

  rust/
    fire-codec/
    fire-vcore/
    fire-kernel/
    fire-ledger-adapter/

tests/fire/
  cal/
  cert/
  negative/
  replay/
  fuzz/
  golden/
```

If implementation is currently Python-only, use Python for the prototype but keep the funds-moving core isolated behind an interface that can later be replaced by Rust or formally extracted code.

---

## 3. Non-negotiable security boundary

The compiler is untrusted.

```text
FIRE-C may generate candidate manifests and certificates.
FIRE-V must independently verify them.
```

The Refiner/ORE is untrusted.

```text
ORE may suggest repairs.
ORE may generate candidate ZPL or FIRE-IR.
ORE may not make an object live.
```

The registry is nonsemantic.

```text
Registry status cannot rewrite object semantics.
```

Only this path may move funds:

```text
canonical object template
+ canonical instance
+ FIRE-Cert
+ valid witnesses
+ posted collateral
-> FIRE-VCore receipt
-> FIRE-Kernel deltas
-> ledger adapter
```

---

## 4. Build order

### Phase A - CAL core data model

Deliver:

```text
Evidence enum
Evidence meet function
Artifact hash record
Interval record
Unit/dimension record
Predicate enum
ProofRule enum
ProofNode structure
Derivation structure
```

Acceptance tests:

```text
proved meet contract = contract
implemented meet tested_discovery = tested_discovery
hypothesis is absorbing for meet
interval [L,U] rejects L>U
unknown evidence label rejected
```

### Phase B - interval and unit proof checker

Implement admitted rules:

```text
const_interval
add_interval
sub_interval
mul_interval
nonnegative_scalar_mul
positive_part_bound
cap_bound
clamp_bound
finite_sum_bound
guarded_reciprocal
guarded_log
unit_add
unit_mul
unit_div
unit_log_dimensionless
unit_exp_dimensionless
```

Acceptance tests:

```text
valid cap proof accepted
invalid cap proof rejected
price + amount rejected
zUSD / (zUSD/TDEX) = TDEX accepted
log(Amount[ETH]) rejected
```

### Phase C - collateral and delta proof checker

Implement:

```text
one_sided_writer_collateral
two_sided_collateral
delta_conservation_cash
delta_conservation_with_fee
delta_conservation_with_burn
```

Acceptance tests:

```text
collateral >= upper bound accepted
collateral one unit below upper bound rejected
cash-settled deltas sum to zero accepted
unbalanced deltas rejected
burn sink declared and balanced accepted
undeclared burn rejected
```

### Phase D - artifact and certificate binding

Implement:

```text
canonical serialization check
object_hash check
instance_hash check
cert_hash check
dependency lock check
cert names object_hash
cert names instance_hash when required
```

Acceptance tests:

```text
tamper object -> certificate rejected
tamper dependency hash -> rejected
same semantics with noncanonical formatting -> same canonical hash, if canonicalizer allows it
same raw text with duplicate JSON keys -> rejected
```

### Phase E - witness policy checker

Implement:

```text
WitnessOK
FreshEnough
ProvenanceOK
ReplayBoundWitness
MaturityOK
WindowOK
NonceOK
AuthorizationOK
```

Acceptance tests:

```text
stale witness rejected
wrong instance_hash in witness rejected
witness outside settlement window rejected
replayed nonce rejected
missing authorization rejected
```

### Phase F - FIREVAccept checker

Implement full gate:

```text
FIREVAccept =
  SchemaOK
  AND HashBindOK
  AND DependencyClosed
  AND UnitOK
  AND DomainOK
  AND ParamOK
  AND AuthorizationOK
  AND NonceOK
  AND MaturityOK
  AND WindowOK
  AND CertOK
  AND EvidenceOK
  AND WitnessOK
  AND CollateralOK
  AND IntegerEvalOK
  AND DeltaConservationOK
  AND ReplayOK
```

Acceptance tests:

```text
valid BurnBoostCall accepted
missing BoundOK proof rejected
insufficient collateral rejected
stale witness rejected
delta mismatch rejected
evidence floor overstatement rejected
```

### Phase G - `fire explain`

Implement a derivation renderer:

```text
fire explain object.zpl
fire explain object.fire.json object.firecert.json
```

Output:

```text
LiveOK failed because:
  BoundOK failed
  CollateralOK failed
Suggested refinements:
  CapRefinement
  CollateralRefinement
```

`fire explain` is non-authoritative.

### Phase H - ORE / FIRE Refiner

Implement only after the verifier exists.

Allowed first refinements:

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

ORE output must remain draft until verified by FIRE-V.

---

## 5. Proof certificate format

A proof tree node should look like:

```json
{
  "rule": "cap_bound",
  "inputs": ["node_id_1", "node_id_2"],
  "claim": {
    "expr": "min(max(B.final - K, 0), Cap)",
    "lower": "0",
    "upper": "Cap"
  },
  "preconditions": ["Cap >= 0"]
}
```

The checker must verify:

1. known rule;
2. required inputs exist;
3. input claims match rule premises;
4. preconditions are present and proved;
5. output claim follows exactly.

No rule may call arbitrary Python functions in the funds-moving verifier.

---

## 6. First worked product: BurnBoostCall

Payoff:

```text
f = N * min(max(B.final - K, 0), Cap)
```

Required proofs:

```text
B.final in [0, Bmax]
N >= 0
Cap >= 0
0 <= min(max(B.final - K, 0), Cap) <= Cap
0 <= f <= N*Cap
writer collateral >= N*Cap
holder_delta + writer_delta = 0
WitnessOK(BurnCertificate[TDEX])
ReplayOK
```

Acceptance criterion:

```text
FIREVAccept(BurnBoostCallTemplate, BurnBoostCallInstance, Gamma, w, C) = true
```

Reject cases:

```text
Cap negative
N outside template bounds
witness missing
witness stale
collateral below N*Cap
certificate claims object_hash but object changed
```

---

## 7. Implementation notes

### Python prototype

Python is acceptable for:

```text
FIRE-C
ORE/FIRE Refiner
product cards
registry tooling
simulation
agent workflows
```

### Funds-moving core

Before serious value is at risk, move these to a tiny Rust or formally verified core:

```text
canonical codec
hash binding
FIRE-Cert checker
fixed-point evaluator
collateral checker
delta conservation checker
witness-policy checker
ledger adapter guard
```

### No generated settlement code

Live settlement must not execute object-specific generated Python code.

Use a small admitted interpreter/kernel over FIRE-IR.

---

## 8. Test corpus

Add negative tests for:

```text
tampered object hash
tampered instance hash
tampered cert hash
duplicate JSON key
noncanonical integer
stale witness
wrong instance hash in witness
insufficient collateral
parameter outside bound
maturity not reached
settlement window expired
dependency hash mismatch
unknown proof rule
evidence floor overstatement
delta conservation failure
payout exceeds certified upper bound
```

Add mutation tests:

```text
remove CollateralOK gate
round collateral down instead of up
ignore witness freshness
skip dependency hash check
replace min with max in cap
flip <= to <
ignore delta conservation
```

The suite must fail on each dangerous mutation.

---

## 9. Definition of done for CAL v0.1

CAL v0.1 is minimally complete when agents can:

1. encode the BurnBoostCall derivation;
2. check the certificate independently of the compiler;
3. reject all listed negative cases;
4. render a human-readable derivation with `fire explain`;
5. produce a verifier receipt only when all gates pass;
6. prove or at least explicitly state the theorem:

```text
FIREVAccept(O,I,Gamma,w,C) -> SettlementSafe(O,I,w,C)
```

---

## 10. Product language boundary

Do not say CAL proves:

```text
profit
risk-free yield
token appreciation
oracle truth
market liquidity
legal compliance
```

Say CAL proves:

```text
mechanical admissibility of settlement under declared artifacts, witnesses, collateral, evidence, and deterministic integer semantics.
```
