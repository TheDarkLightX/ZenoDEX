# Deflationary DAC Ecosystem Strategy (Draft)

## Goal
Design a modular, economically sticky DEX + DAC ecosystem where value loops through protocol usage, long-term staking, and supply-constrained tokenomics.

## Key Economic Loops (Sticky Value)
1. **Usage -> Fees -> Buyback/Burn**
   - Trading fees accumulate and a fixed share funds buyback and burn.
   - Buyback reduces supply, aligning token value with usage.
2. **Usage -> Fees -> Treasury -> Incentives**
   - A treasury share funds liquidity incentives, audits, and growth.
   - Incentives are time/lock-weighted to reward committed participants.
3. **Usage -> Fees -> Rebates**
   - Rebates return value to heavy/loyal users, increasing retention.
4. **Staking -> Governance -> Parameter Control**
   - Stakers govern rate caps and floors; lock durations weight votes.

## Modular Spec Strategy (Lego Blocks)
Use Tau specs as validators for each economic module. A composite spec consumes their outputs and enforces “all must pass.”

### Core DEX Modules (existing)
- **Swap math**: `cpmm_v1.tau`, `swap_exact_in_v1.tau`, `swap_exact_out_v1.tau`
- **Settlement**: `settlement_v4_buyback_floor_rebate_lock.tau`

### Tokenomics Modules (new + existing)
- **Rate math (bps)**: `tokenomics_rate_bps_v1.tau`, `tokenomics_rate_bps_32_v1.tau`
- **Fee split**: `tokenomics_fee_split_32_v1.tau`
- **Transfer tax split**: `tokenomics_transfer_tax_split_v1.tau`, `tokenomics_transfer_tax_split_32_v1.tau`
- **Buyback + floor**: `tokenomics_buyback_floor_32_v1.tau`
- **Lock-weighted rewards**: `token_archetype_lock_weighted_rewards_32_v1.tau`
- **Vesting cliff**: `token_archetype_vesting_cliff_32_v1.tau`

## How to Connect Specs
1. **Compute** all derived values off-chain (or in a daemon): fees, buyback amounts, burns, rebates, caps.
2. **Validate** each module with Tau: every module emits an `ok` flag.
3. **Aggregate** into a composite policy spec: if any module fails, the step is invalid.
4. **Settle** state transitions only when all `ok` flags pass.

## Example Composition Flow
- User trade -> swap math -> fee computed
- Fee split -> buyback/treasury/rebate
- Buyback burn -> supply floor
- Lock-weighted rewards -> staking payout cap
- Composite policy -> final `settlement_ok`

## Risk Controls
- **Rate caps** on burns/rebates/incentives
- **Supply floor** to avoid infinite burn to zero
- **Time-weighted staking** to reduce mercenary capital
- **Governance timelocks** for parameter changes

## Suggested Next Composite Spec
Create a policy spec that takes:
- `swap_ok`, `fee_split_ok`, `buyback_floor_ok`, `rebate_ok`, `lock_weight_ok`, `token_transition_ok`
- Outputs: `dex_step_ok` = AND of all the above

## Notes on Scaling
- `bv[32]` modules include safe-range guards (<= 429,496 units) to prevent multiplication overflow.
- For large supplies, use 32-bit hi/lo limb patterns (like `protocol_token_v1.tau`).
