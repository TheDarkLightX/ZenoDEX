---
title: ZUSD_V1
type: note
permalink: autonomous-tau-dex-review/docs/derivatives/zusd-v1
---

# zUSD v1 (SimplexBorrow-Aligned)

`zUSD` is the protocol dollar for ZenoDex derivatives.

This module is Liquity-like, but it is not an exact Liquity V1 or Liquity V2
clone. See `docs/ZUSD_LIQUITY_PARITY_STATUS_2026_05_20.md` for the current
parity map, including the Liquity V2 5% liquidation-penalty gap.

## What a participant does

1. Deposit collateral.
2. Mint `zUSD` against that collateral (with deterministic borrow fee settings).
3. Use `zUSD` for perps margin and settlement.
4. Repay `zUSD` to reduce debt and unlock collateral.
5. Redeem `zUSD` for collateral (deterministic redemption fee; no pending-price mismatch/stale-oracle allowed).
6. If vault health falls below threshold, liquidation moves debt/collateral through the stability pool.

## How dollars are generated

- `mint_zusd` increases:
  - vault debt (`debt_e8`) by `principal + fee`
  - circulating debt (`free_debt_e8`) by `principal + fee`
- Protocol fee counters:
  - `protocol_revenue_zusd_cum_e8` tracks cumulative borrow fees.
  - `protocol_collateral_e8` tracks redemption-fee collateral reserve.
- Minting is blocked unless:
  - oracle is initialized and fresh,
  - pending oracle price equals active price (no freeze window),
  - system is not in recovery mode,
  - post-mint vault remains above MCR.

## Redemption behavior

- `redeem_zusd` burns free debt and vault debt (`debt_e8`, `free_debt_e8`) by redeemed amount.
- Redeemed collateral is computed at current price:
  - `gross_collateral = redeemed_zusd / price`
  - redemption fee is taken in collateral and routed to `protocol_collateral_e8`
  - redeemer receives `gross_collateral - fee`
- Redemption is blocked if:
  - pending oracle price differs from active price,
  - oracle is stale,
  - redemption would violate post-action MCR,
  - protocol collateral reserve would exceed cap.

## Safety model (from AutoLend / SimplexBorrow posture)

- **Pending/commit oracle:**
  - `oracle_report` moves `price_pending_e8` downward (non-increasing).
  - risky ops are frozen while `price_pending_e8 != price_e8`.
  - `oracle_commit` is allowed only if vault remains >= MCR at pending price.
- **Recovery mode:**
  - enabled when TCR < CCR.
  - blocks risky expansion operations (mint/withdraw/SP-withdraw).
- **Supply conservation:**
  - `free_debt_e8 + sp_debt_e8 == debt_e8`.
- **System solvency collateral includes reserves:**
  - invariants and TCR include `protocol_collateral_e8` in addition to vault + SP collateral.
- **Liquidation path:**
  - uses pending oracle price for under-MCR checks.
  - consumes `sp_debt_e8`, transfers collateral to `sp_coll_e8`, zeroes vault.
  - optional liquidation compensation can pay fixed collateral and/or a bps
    share to the liquidator before the remaining collateral is assigned to the
    stability pool. The defaults are zero for local deterministic tests. Public
    Tau Net materials describe `AGRS` as native gas, so live deployment should
    configure these once exact Tau fee accounting is pinned. The wallet API
    also passes through `tx_fee_limit` and reports native-balance coverage as a
    preflight signal for keepers.

## Implementation in this repo

- Kernel: `src/core/zusd.py`
- Tests:
  - `tests/core/test_zusd.py`
  - `tests/core/test_zusd_auth_strictness.py`
  - `tests/integration/test_zusd_monetary_wallet_api.py`

## Tau guard suite (execution-trace validated)

zUSD policy guards now exist as Tau specs in `src/tau_specs/recommended/`:
- `zusd_transfer_guard_v1.tau`
- `zusd_oracle_commit_guard_v1.tau`
- `zusd_oracle_commit_guard_v2.tau`
- `zusd_recovery_mode_gate_v1.tau`
- `zusd_liquidation_guard_v1.tau`
- `zusd_liquidation_guard_v2.tau`
- `zusd_supply_conservation_v1.tau`
- `zusd_supply_conservation_v2.tau`
- `zusd_mint_guard_v1.tau`
- `zusd_redeem_guard_v1.tau`
- `zusd_repay_guard_v1.tau`
- `zusd_withdraw_collateral_guard_v1.tau`
- `zusd_deposit_sp_guard_v1.tau`
- `zusd_withdraw_sp_guard_v1.tau`

Runtime fail-closed adapter (single-vault monetary model):
- `src/integration/zusd_tau_gate.py`
  - `step_with_tau(...)`

Execution-trace test coverage:
- `tests/tau/test_zusd_tau_specs.py`

## Excluded multi-vault prototype

The incomplete two-vault prototype was removed from shipped source. It lacked
the single-vault model's liquidation compensation and shutdown lifecycle, so it
must not be treated as an alternate production transition system. A future
multi-vault design requires a new complete specification and promotion packet;
the deleted prototype receives no release credit.

## How person-to-person zUSD transfer works on Tau Net

Current backend posture:
- zUSD is represented as a non-native `asset_id` in DEX balances (`(pubkey, asset) -> amount`).
- Tau transactions are authenticated by `tx_sender_pubkey`.
- The app bridge now supports a dedicated token op stream:
  - stream `"9"`, `module: "TauToken"`, actions: `transfer`, `mint`, `burn`.
  - per-sender replay protection via monotone u32 nonce (token-domain nonce key).
  - optional `deadline` fail-closed check.
  - `mint` is operator-gated (`TAU_DEX_TOKEN_OPERATOR_PUBKEY`, fallback `TAU_DEX_OPERATOR_PUBKEY`).

Interoperability note:
- This is app-level token handling inside the DEX snapshot model.
- Cross-app acceptance still requires either:
  - shared app-bridge semantics across apps, or
  - a canonical Tau-level token primitive/standard upstream.

Recommended next hardening step:
- gate `TauToken` transitions with `zusd_transfer_guard_v1.tau` + explicit auth/nonce witnesses,
- keep fail-closed behavior on auth, replay, and balance checks.
