# Mechanism Design Math Hypothesis Registry

This registry tracks mechanism-design hypotheses that have replayable evidence
inside `experiments/mechanism_design_math_v1/`.

| ID | Obligation | Domain | Current verdict | Evidence |
|---|---|---|---|---|
| `H-MD-SS-002` | `O-SS-02` | spot settlement | `SUPPORTED` | `wave1_spot_settlement/test_spot_fee_arithmetic.py` |
| `H-MD-SS-008` | `O-SS-07` | spot settlement | `SUPPORTED` | `wave1_spot_settlement/test_spot_fee_arithmetic.py` |

Open charter rows remain queued until a wave adds tests, simulations, ESSO,
Lean, or miner evidence and records the result in a wave-local
`evidence/results.json`.
