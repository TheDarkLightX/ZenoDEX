# CAL Derivation: CompoundRewardNote

## Object

State variable:

```text
G_0 = 1
r_t = clamp(R_t, 0, rMax)
G_{t+1} = G_t * (1 + r_t)
```

Payoff:

```text
Payoff_holder = N * min(G_T - 1, Cap)
Payoff_writer = -Payoff_holder
```

## Assumptions

```text
N >= 0
Cap >= 0
0 <= rMax
forall t, WitnessOK(R_t) -> R_t admissible
r_t in [0, rMax]
T is finite and static
```

## State invariant

```text
1 <= G_t <= (1 + rMax)^t
```

### Base

```text
G_0 = 1
1 <= G_0 <= (1+rMax)^0 = 1
```

### Step

Assume:

```text
1 <= G_t <= (1+rMax)^t
0 <= r_t <= rMax
```

Then:

```text
1 <= 1+r_t <= 1+rMax
```

Since both sides are nonnegative:

```text
G_{t+1} = G_t(1+r_t)
```

so:

```text
1 <= G_{t+1} <= (1+rMax)^(t+1)
```

## Payoff bound

```text
0 <= G_T - 1 <= (1+rMax)^T - 1
```

Therefore:

```text
0 <= min(G_T - 1, Cap) <= min((1+rMax)^T - 1, Cap)
```

and:

```text
0 <= Payoff_holder <= N * min((1+rMax)^T - 1, Cap)
```

Writer collateral must satisfy:

```text
Cw >= N * min((1+rMax)^T - 1, Cap)
```

## Required FIRE-Cert roots

```text
StateInvariantOK
BoundOK_holder
BoundOK_writer
CollateralOK_writer
DeltaConservationOK
WitnessOK_RewardPacketSequence
ReplayOK
SettlementSafe
```

## Negative tests

Reject:

```text
T not finite/static
rMax < 0
missing reward witness
state transition mismatch
collateral below computed maximum
integer overflow in compounder
```
