# CAL Derivation: CappedILCover

## Object

```text
IL_T = V_HODL(T) - V_LP(T)
Payoff_lp = min(max(IL_T - Deductible, 0), Cap)
Payoff_insurer = -Payoff_lp
```

## Assumptions

```text
Cap >= 0
Deductible >= 0
LPValuePacketOK
HODLBenchmarkPacketOK
PriceProvenanceOK
Witnesses are bound to the instance hash
```

## Bound derivation

Let:

```text
X = IL_T - Deductible
Y = max(X, 0)
Z = min(Y, Cap)
```

Then by cap rule:

```text
0 <= Z <= Cap
```

Therefore:

```text
0 <= Payoff_lp <= Cap
-Cap <= Payoff_insurer <= 0
```

Insurer collateral:

```text
C_insurer >= Cap
```

## AMM theorem dependency boundary

If a product card mentions the local AMM frontier theorem, the certificate must include the theorem assumptions:

```text
Smooth
Symmetric
Homogeneous
Local
SecondOrder
FeeFree
Continuous
```

The theorem supports local AMM risk labeling. It does not prove global LP profitability or oracle truth.

## Required FIRE-Cert roots

```text
LPValuePacketOK
HODLBenchmarkPacketOK
PriceProvenanceOK
BoundOK_lp
CollateralOK_insurer
DeltaConservationOK
ReplayOK
SettlementSafe
```

## Negative tests

Reject:

```text
missing LP value packet
missing HODL benchmark packet
stale price packet
Cap < 0
collateral below Cap
attempted theorem claim without assumption packet
```
