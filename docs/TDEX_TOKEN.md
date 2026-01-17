# TDEX Token - Deflationary DEX Governance Token

## Overview

TDEX is the native governance and utility token of the Tau DEX protocol. It features built-in deflationary mechanics that create sustainable value appreciation as the DEX grows.

## Token Specifications

| Property | Value |
|----------|-------|
| **Name** | Tau DEX Token |
| **Symbol** | TDEX |
| **Initial Supply** | 1,000,000 TDEX |
| **Minimum Supply** | 100,000 TDEX (10% floor) |
| **Decimals** | 3 (internal scaling) |
| **Type** | Deflationary |

## Deflationary Mechanics

### 1. Transfer Burn (0.5%)
Every TDEX transfer automatically burns 0.5% of the transferred amount.

```
Transfer 1000 TDEX:
- Burn: 5 TDEX (0.5%)
- Recipient receives: 995 TDEX
- Supply reduced by: 5 TDEX
```

### 2. Swap Burn (0.3%)
Each DEX swap contributes 0.3% of trade value to the burn mechanism via the buyback pool.

### 3. Buyback and Burn
- 50% of DEX trading fees accumulate in the buyback pool
- When threshold is reached, pool buys TDEX from market
- All bought TDEX is immediately burned
- Creates consistent buy pressure + supply reduction

## Supply Dynamics

```
Initial: 1,000,000 TDEX
         ↓ (transfers burn 0.5%)
         ↓ (swaps contribute to buyback)
         ↓ (buyback burns TDEX)
Floor:   100,000 TDEX (minimum, burns stop here)
```

### Supply Floor Protection
- Minimum supply: 100,000 TDEX (10% of initial)
- Burns automatically stop when floor is reached
- Ensures token always has circulating supply

## Tau Specification Files

The TDEX token is formally verified using Tau Language specifications:

| Spec File | Purpose |
|-----------|---------|
| `tdex_token_v1.tau` | Core transfer with auto-burn |
| `tdex_supply_v1.tau` | Supply tracking and floor enforcement |
| `tdex_buyback_v1.tau` | Buyback pool and burn execution |
| `tdex_economics_v1.tau` | Complete tokenomics validator |

## Formal Verification

All token operations are validated through Tau specs that ensure:

1. **Conservation**: No tokens created from nothing
2. **Floor Protection**: Supply never goes below minimum
3. **Burn Correctness**: Exact 0.5% burned on transfers
4. **Buyback Validity**: Proper fee-to-burn conversion

## Economic Model

### Value Accrual Mechanism

```
DEX Usage → Trading Fees → Buyback Pool → Buy TDEX → Burn
                ↓
         Protocol Revenue
                ↓
         50% to Buyback (deflationary pressure)
         50% to Treasury (development)
```

### Deflationary Pressure Formula

```
Daily Burn Rate = (Transfer Volume * 0.5%) + (Swap Volume * 0.3% * 50%)
```

### Example Scenario

With $1M daily DEX volume and $100K TDEX transfers:
- Transfer burns: 500 TDEX
- Swap buyback burns: ~1500 TDEX (at current prices)
- **Total daily burn: ~2000 TDEX**

At this rate, supply reduces from 1M to 100K floor in ~450 days of sustained activity.

## Integration with Tau Net

TDEX operates on Tau Net using the formal specification system:

1. **State Validation**: All transfers validated by `tdex_token_v1.tau`
2. **Supply Tracking**: Real-time supply monitored by `tdex_supply_v1.tau`
3. **Buyback Execution**: Automated via `tdex_buyback_v1.tau`
4. **Economic Health**: Continuous monitoring via `tdex_economics_v1.tau`

## Governance

TDEX holders can participate in:
- Protocol parameter changes
- Fee structure modifications
- Treasury allocation decisions
- New feature proposals

## Security Properties

All TDEX operations satisfy these invariants:

1. `supply[t] <= supply[t-1]` (never inflationary)
2. `supply[t] >= min_supply` (floor protected)
3. `burn_amount = transfer_amount * 0.005` (exact burn rate)
4. `buyback_burn = bought_tokens` (all bought tokens burned)

## Getting Started

### For Developers

```python
# Validate a TDEX transfer
from tau_interpreter import validate_transfer

result = validate_transfer(
    sender_balance=10000,
    receiver_balance=5000,
    amount=1000,
    current_supply=900000,
    min_supply=100000
)
# Returns: {valid: True, burn: 5, net_transfer: 995}
```

### For Users

1. Acquire TDEX through DEX swaps
2. Hold to benefit from deflationary appreciation
3. Use for governance participation
4. Transfer with understanding of 0.5% burn

## Conclusion

TDEX creates a sustainable deflationary token economy where:
- **DEX usage drives value**: More trading = more burns
- **Floor prevents death spiral**: 10% minimum supply
- **Formal verification ensures safety**: All operations validated
- **Transparent mechanics**: Burn rates are fixed and verifiable
