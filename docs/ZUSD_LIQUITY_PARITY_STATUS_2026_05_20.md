# zUSD Liquity Parity Status

Checked: 2026-05-20.

Current authority correction (2026-08-28): this document records historical
donor implementation and tests. The current profile refuses the stream `11`
zUSD monetary wallet route and grants it no settlement or publication
authority. Statements below about mounted or live behavior describe the
2026-05-20 donor state.

## Historical 2026-05-20 answer

zUSD is Liquity-like and SimplexBorrow-aligned. It is not an exact Liquity V1
or Liquity V2 clone.

The 2026-05-20 donor implementation includes:

- 110% minimum collateral ratio (`mcr_bps = 11000`);
- 150% recovery-mode threshold (`ccr_bps = 15000`);
- oracle pending/commit freeze around risky actions;
- stability-pool debt absorption;
- min-open-debt floor enforcement;
- configurable borrow and redemption fee floors, caps, base-rate decay, and
  fixed base-rate bumps;
- zero-default liquidation compensation hooks for future Tau fee/gas or keeper
  bounty policy;
- transferable app-level zUSD balances for Tau app-state use.

The 2026-05-20 donor implementation does not include:

- Liquity V2's usual 5% primary liquidation penalty with borrower surplus
  collateral returned after the stability pool absorbs debt;
- Liquity V2's refundable gas deposit plus exact variable 0.5% liquidator
  compensation semantics. zUSD now has configurable hooks, but their defaults
  are zero and they are not yet Liquity-exact;
- Liquity V1's 200 LUSD liquidation reserve;
- Liquity V1's exact redemption ordering and redistribution behavior when the
  Stability Pool cannot fully absorb a liquidation;
- Liquity V1/V2's exact dynamic fee formula. zUSD has configurable hooks, but
  current defaults are zero floors and fixed bumps.

## Practical consequence

At a vault collateral ratio of 107%, current zUSD v1 liquidates the whole vault
collateral into stability-pool collateral accounting once the vault is below
MCR and the Stability Pool can absorb the debt. A Liquity V2-style 5% primary
liquidation penalty would transfer roughly 105% of the debt value to the
Stability Pool and leave the extra collateral claimable by the borrower.

That exact behavior is now pinned by:

```bash
pytest -q tests/core/test_zusd.py::test_liquidation_at_107_percent_cr_uses_current_full_collateral_policy
```

## Decision needed before parity work

If zUSD should track Liquity V2 closer, the next mechanism change should add an
explicit `liquidation_penalty_bps = 500` parameter plus borrower surplus
collateral accounting and a mounted claim path. That should land before broader
testnet promotion because it changes liquidation payoffs.

If zUSD should remain SimplexBorrow-aligned, keep the current policy and avoid
calling it Liquity-exact in docs, UI text, or release notes.

## Tau fee and gas posture

Public Tau Net materials describe Agoras (`AGRS`) as the native token and gas
for Tau Net activity. Source checked 2026-05-21: <https://tau.net/>. The exact
live fee accounting is still outside this repo's current local-node evidence.

The local Tau Testnet path used here carries `fee_limit` in the signed
transaction payload, but the current `createblock` path does not debit a native
transaction fee from account balances.

That local behavior should not be promoted as a permanent Tau Net gas or fee
assumption. zUSD therefore keeps liquidation keeper compensation configurable:

- `liquidation_gas_comp_fixed_collateral_e8`
- `liquidation_gas_comp_bps`

The core liquidation rule is:

```text
comp = min(liquidated_collateral, fixed_comp + ceil(liquidated_collateral * comp_bps / 10000))
```

The liquidator receives `comp` first; the remaining liquidated collateral is
assigned to stability-pool collateral gains.

The Tau app bridge accepts fee-named environment variables first:

- `TAU_DEX_ZUSD_LIQUIDATION_FEE_COMP_FIXED_COLLATERAL_E8`
- `TAU_DEX_ZUSD_LIQUIDATION_FEE_COMP_BPS`

For backwards compatibility, it also accepts the older gas-named aliases:

- `TAU_DEX_ZUSD_LIQUIDATION_GAS_COMP_FIXED_COLLATERAL_E8`
- `TAU_DEX_ZUSD_LIQUIDATION_GAS_COMP_BPS`

Both defaults are `0` for deterministic local tests. In the historical donor,
the parameter could turn compensation on without changing the action
vocabulary. The current profile keeps stream `11` unmounted. The donor parameter
pays the keeper from liquidated native collateral, independent of whether the
external Tau transaction fee is called gas, fee, or another chain-cost term.

The wallet API also carries a user-supplied `tx_fee_limit` into the signed Tau
transaction envelope and reports whether the current native balance appears to
cover that requested limit. This is a preflight posture check only; final fee
debit semantics remain a Tau Net host responsibility until pinned by live
testnet evidence.

Pinned app-bridge evidence:

```bash
pytest -q tests/integration/test_tau_testnet_dex_plugin.py::test_apply_app_tx_zusd_monetary_liquidation_compensation_pays_keeper
pytest -q tests/integration/test_tau_testnet_dex_plugin.py::test_zusd_monetary_liquidation_fee_comp_env_aliases_prefer_fee_names tests/integration/test_tau_testnet_dex_plugin.py::test_zusd_monetary_liquidation_fee_comp_env_aliases_accept_legacy_gas_names
pytest -q tests/integration/test_zusd_monetary_wallet_api.py::test_prepare_mint_uses_monetary_nonce_and_preflights_stream_11
pytest -q tests/integration/test_zusd_monetary_wallet_api.py::test_status_reports_zusd_monetary_state_from_wrapped_app_state
pytest -q tests/integration/test_zusd_monetary_wallet_ui_docker.py::test_zusd_monetary_wallet_ui_smoke_through_docker_tau_node -s
```

The historical Docker browser smoke covered zUSD minting and a follow-on perps
clearinghouse collateral deposit against a local Tau node. It recorded donor
UI and transaction-bridge behavior when the perps API signed and mined local
Tau transactions. It did not prove a live Tau Net fee-debit rule and does not
establish current route reachability.
