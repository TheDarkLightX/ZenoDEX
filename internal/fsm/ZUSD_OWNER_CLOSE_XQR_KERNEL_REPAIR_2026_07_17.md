# zUSD Owner-Close x/q/r Kernel Repair

Date: 2026-07-17
Profile: `zenodex/zusd-liquity-v1-minimum`
Scenario family: `CE159`
Status: pure F25 candidate implemented; F15/F16 authority remains absent

## Exact problem

The owner-close route crosses two collateral unit domains:

```text
internal accounting: E18 collateral atoms
physical custody:    E8 collateral atoms
K:                   10^10 E18 atoms per physical E8 atom
```

For closed-vault collateral `x`, the successor must derive exactly:

```text
q = floor(x / K)
r = x mod K
x = K*q + r
0 <= r < K
```

Physical custody and external owner balances move by `q`. The exact remainder
`r` remains an E18 owner claim. A quotient of zero forbids an adapter transfer;
it is not represented as a zero-value transfer effect.

## Pure F25 relation

For Balanced or SurplusQuarantined custody:

```text
ActivePoolShadowE18_after = ActivePoolShadowE18_before - x
AccountedCustodyE8_after  = AccountedCustodyE8_before - q
ObservedCustodyE8_after   = ObservedCustodyE8_before - q
OwnerExternalE8_after     = OwnerExternalE8_before + q
OwnerClaimE18_after       = OwnerClaimE18_before + r
QuarantineE8_after        = QuarantineE8_before
```

The candidate rejects before construction when any admitted successor would:

- underflow Active Pool shadow;
- underflow accounted custody;
- underflow observed custody;
- overflow owner external E8;
- overflow owner claim E18.

Every independently observed arithmetic failure is retained in canonical order.
DeficitFrozen custody blocks successor arithmetic and returns only the typed
custody-mode violation.

## Representation

- E18 collateral, E8 custody, and E18 claim values are distinct frozen nominal
  types.
- Every amount is a checked U256 value.
- `NoPhysicalTransfer` and `PhysicalTransferE8` are distinct variants.
- A positive physical-transfer variant cannot carry zero.
- Candidate construction rederives x/q/r, all post values, quarantine
  preservation, and transfer-directive consistency.
- Rejection construction rederives q/r and requires a unique canonical
  violation vector.
- `OwnerCloseProjectionCandidate.is_commit_receipt` is always false.

## Evidence

Python regressions cover:

- exact divisibility and zero residue;
- quotient plus positive residue;
- all sub-E8 cases with no adapter directive;
- zero-collateral totality;
- DeficitFrozen rejection;
- simultaneous underflow and overflow visibility;
- each individual arithmetic reject;
- SurplusQuarantined preservation;
- nominal unit separation;
- forged successor rejection;
- noncanonical violation-vector rejection.

Lean proves:

- exact Euclidean decomposition;
- residue bound;
- sub-E8 zero quotient and all-residue behavior;
- exact-multiple quotient and zero residue;
- E8 physical credit plus E18 claim credit recomposes exactly to `x`;
- Active Pool and custody debits preserve their removed amounts under bounds;
- no physical owner credit for sub-E8 collateral;
- the adopted divisible, residue, and sub-E8 examples.

## Explicit nonclaims

- The candidate does not prove owner identity, vault uniqueness, source roots,
  staged net debt, burns, or final active-vault semantics.
- It does not produce F17/F25 evidence bytes, an F15 composite certificate, an
  F16 CAS commit, a physical transfer, a nonce/nullifier, a receipt, or an
  outbox record.
- Adapter atomicity and crash recovery remain F16 shell obligations.
- Rust codec, transition, U256/U512 refinement, RISC0 proof, and release claims
  remain false until separately implemented and evidenced.
