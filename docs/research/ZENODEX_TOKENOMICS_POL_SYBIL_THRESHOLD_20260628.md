# ZenoDEX Tokenomics POL Sybil Threshold - 2026-06-28

## Executive Result

Bounded exact wash-trade replay turns fee-gated identity rewards into minimum POL-share thresholds. Tau admits only the replayed threshold certificate facts.

Mechanism-design evidence only; reward activation remains controlled by deterministic reward-envelope and governance gates.

## Game Surface

- Players: `reward farmer, protocol reward program`
- Attacker action: choose a two-leg CPMM wash trade size and sybil identity count within the bounded model
- Payoff: `base_reward_per_identity_quote - minimum wash-trade cost at spot p0`
- Bounds: `{"max_trade_in_quote": 20000, "pol_share_bps": "0..10000", "reserve_base": 10000, "reserve_quote": 10000}`

## Threshold Cases

| case | protocol fee share bps | reward | min usage | threshold POL bps | cost below | cost at | envelope parity |
| --- | --- | --- | --- | --- | --- | --- | --- |
| `proto20_reward15` | `2000` | `15` | `10` | `1852` | `149977/10000` | `37501/2500` | `True/True` |
| `proto20_reward20` | `2000` | `20` | `10` | `3704` | `199981/10000` | `25001/1250` | `True/True` |
| `proto20_reward25` | `2000` | `25` | `10` | `5556` | `49997/2000` | `62503/2500` | `True/True` |
| `proto50_reward15` | `5000` | `15` | `10` | `5000` | `14999/1000` | `15/1` | `True/True` |
| `already_safe_proto50_reward10` | `5000` | `10` | `10` | `0` | `None` | `10/1` | `True/True` |
| `no_threshold_proto100_reward12` | `10000` | `12` | `10` | `None` | `None` | `11/1` | `False/True` |

Cases with `threshold POL bps = null` remain unsafe even at 100% POL under the bounded replay.

## Tau Certificate

- Spec: `src/tau_specs/recommended/tokenomics_pol_sybil_threshold_certificate_v1.tau`
- Latest Tau: `Tau Language Framework version 0.7.0-alpha (401d756b)`
- Tau cases: `6`
- Invalid accepts: `0`

## Non-Claims

- This is a bounded fee-gated identity reward model, not a general tokenomics proof.
- The threshold depends on the stated reserves, fee settings, usage threshold, reward amount, and max trade bound.
- Tau does not compute wash-trade economics; it admits host-replayed certificate facts only.
- This does not activate any reward program or governance change.

## Replay

```bash
python3 tools/zenodex_tokenomics_pol_sybil_threshold_20260628.py
```
