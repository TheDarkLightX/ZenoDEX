# CAL Derivation: BurnBoostCall

## Object

```text
Payoff_holder = N * min(max(B.final - K, 0), Cap)
Payoff_writer = -Payoff_holder
```

## Assumptions

```text
N : Amount[zUSD], N >= 0
K : Index
Cap : Index, Cap >= 0
B.final : BurnIndex[TDEX]
WitnessOK(B) -> B.final in [0, Bmax]
writer collateral Cw >= N * Cap
```

## Goal

```text
FIREVAccept(O, I, Gamma, w, C) -> SettlementSafe(O, I, w, C)
```

For this payoff, the key bound goal is:

```text
0 <= Payoff_holder <= N * Cap
-N * Cap <= Payoff_writer <= 0
```

## Derivation

1. From `WitnessOK(B)`, source bound:

```text
B.final in [0, Bmax]
```

2. By interval subtraction, for `X = B.final - K`, some interval is derived. The exact lower and upper do not matter for the cap proof.

```text
X in [Lx, Ux]
```

3. Positive part:

```text
Y = max(X, 0)
Y >= 0
```

4. Cap:

```text
Z = min(Y, Cap)
Cap >= 0
0 <= Z <= Cap
```

5. Nonnegative multiplication:

```text
N >= 0
0 <= N*Z <= N*Cap
```

6. Therefore:

```text
BoundOK(Payoff_holder, 0, N*Cap)
BoundOK(Payoff_writer, -N*Cap, 0)
```

7. Collateral:

```text
Cw >= N*Cap
Cw + Payoff_writer >= 0
```

8. Delta conservation:

```text
Payoff_holder + Payoff_writer = 0
```

9. If artifact hash, instance hash, witness, replay, authorization, nonce, maturity, and integer-eval gates also pass:

```text
SettlementSafe
```

## Required FIRE-Cert roots

```text
UnitOK
BoundOK_holder
BoundOK_writer
CollateralOK_writer
DeltaConservationOK
WitnessOK_BurnCertificate
ReplayOK
SettlementSafe
```

## Negative tests

The verifier must reject:

```text
Cap < 0
N < 0
N outside template bounds
missing BurnCertificate
stale BurnCertificate
Cw < N*Cap
tampered object_hash
tampered instance_hash
payoff integer eval > N*Cap
```
