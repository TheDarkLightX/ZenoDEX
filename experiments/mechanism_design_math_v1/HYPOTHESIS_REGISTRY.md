# Mechanism Design Math Hypothesis Registry

This registry tracks mechanism-design hypotheses that have replayable evidence
inside `experiments/mechanism_design_math_v1/`.

| ID | Obligation | Domain | Current verdict | Evidence |
|---|---|---|---|---|
| `H-MD-SS-002` | `O-SS-02` | spot settlement | `SUPPORTED` | `wave1_spot_settlement/test_spot_fee_arithmetic.py` |
| `H-MD-SS-008` | `O-SS-07` | spot settlement | `SUPPORTED` | `wave1_spot_settlement/test_spot_fee_arithmetic.py` |
| `H-MD-SB-001` | `O-SB-01` | sealed bid | `SUPPORTED` | `wave2_sealed_bid/test_sealed_bid_deviations.py` |
| `H-MD-SB-002` | `O-SB-02` | sealed bid | `SUPPORTED` | `wave2_sealed_bid/test_sealed_bid_deviations.py` |
| `H-MD-SB-003` | `O-SB-03` | sealed bid | `SUPPORTED` | `wave2_sealed_bid/test_sealed_bid_deviations.py` |
| `H-MD-SB-004` | `O-SB-04` | sealed bid | `SUPPORTED` | `wave2_sealed_bid/test_sealed_bid_deviations.py` |
| `H-MD-SB-005` | `O-SB-05` | sealed bid | `SUPPORTED` | `wave2_sealed_bid/test_sealed_bid_deviations.py` |
| `H-MD-SB-006` | `O-SB-06` | sealed bid | `SUPPORTED` | `wave2_sealed_bid/test_sealed_bid_deviations.py` |
| `H-MD-VM-001` | `O-VM-01` | verification markets | `SUPPORTED` | `wave4_verification_markets/test_verification_market_deviations.py` |
| `H-MD-VM-002` | `O-VM-02` | verification markets | `SUPPORTED` | `wave4_verification_markets/test_verification_market_deviations.py` |
| `H-MD-VM-003` | `O-VM-03` | verification markets | `SUPPORTED` | `wave4_verification_markets/test_verification_market_deviations.py` |
| `H-MD-VM-004` | `O-VM-04` | verification markets | `SUPPORTED` | `wave4_verification_markets/test_verification_market_deviations.py` |
| `H-MD-VM-005` | `O-VM-05` | verification markets | `SUPPORTED` | `wave4_verification_markets/test_verification_market_deviations.py` |
| `H-MD-VM-006` | `O-VM-06` | verification markets | `SUPPORTED` | `wave4_verification_markets/test_verification_market_deviations.py` |

Open charter rows remain queued until a wave adds tests, simulations, ESSO,
Lean, or miner evidence and records the result in a wave-local
`evidence/results.json`.
