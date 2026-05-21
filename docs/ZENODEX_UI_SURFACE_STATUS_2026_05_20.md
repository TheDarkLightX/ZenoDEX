# ZenoDEX UI Surface Status (2026-05-20)

This note records the mounted ZenoDEX UI posture as of 2026-05-20.

## Mounted surfaces

| Surface | Mounted in UI | Default posture | Authoritative backend path | Browser evidence |
| --- | --- | --- | --- | --- |
| Swap / Pools | Yes | Live local/testnet spot lane | Yes, mounted spot path through local API and Tau-ledger flow | `tests/integration/test_dex_ui_live_bridge.py` |
| zUSD | Yes | Live Tau wallet plus monetary-vault lanes | Yes for stream `9` transfer/mint/burn transport and stream `11` collateral mint, repay, redeem, stability pool, liquidation, and SP collateral claims. | `tests/integration/test_zusd_tau_wallet_ui_bridge.py`, `tests/integration/test_zusd_tau_wallet_ui_docker.py`, `tests/integration/test_zusd_monetary_wallet_ui_bridge.py`, `tests/integration/test_zusd_monetary_wallet_ui_docker.py`, `tests/integration/test_tau_testnet_dex_plugin.py::test_apply_app_tx_zusd_monetary_stability_pool_liquidation_and_claim` |
| Oracle | Yes | Live local operator console | Yes for local read/write API routes, with browser evidence for dashboard reads and a write-enabled receipt flow. | `tests/integration/test_zeno_oracle_ui_bridge.py`, `tests/integration/test_zenodex_oracle_cli.py` |
| Perpetuals | Yes | Read-only preview plus live wallet panel in non-demo mode | Yes for stream `8` two-party clearinghouse init, collateral deposit/withdraw, signed position updates, epoch advance, oracle price publish, and settle through `/api/perps/wallet/*`. The mounted `/api/perps/*` path remains demo/development. | `tests/integration/test_perps_ui_preview_lock.py`, `tests/integration/test_perps_wallet_api.py`, `tests/integration/test_perps_wallet_ui_bridge.py`, `tests/integration/test_perps_stream8_resilience.py` |
| Strategy | Yes | Receipt-backed live-prepare panel in non-demo mode | Yes for local AutoTrader prepare through `/api/strategy/autotrader/*`, including explicit risk acknowledgement, `AUTOTRADER_LIVE_ALLOW_LOCAL_SIGNING=true`, policy compilation, guard checks, signed intent operations, Tau tx payload construction, and release certificates. Unattended execution and production chain submission remain non-claims. | `tests/integration/test_autotrader_live_api.py`, `tests/integration/test_autotrader_live_ui_bridge.py` |
| Confidential | Yes | Live operator-status and proof-context surface | Status-only via `GET /api/confidential/status` | `tests/integration/test_confidential_ui_bridge.py` |

## Interpretation

The mounted app is the intended ZenoDEX shell. The open gap is no longer shell
selection.

The next product-complete backend promotions still required are:

1. perps on a mounted live transaction path, using the existing signed app-bridge engine rather than the demo HTTP route;
2. strategy execution after the mounted receipt-backed prepare path;
3. any confidential execution lane beyond operator-status and proof posture.

Perps now has focused backend and browser evidence for a mounted live wallet
lane. Collateral-minted zUSD can be transferred and used as the quote collateral
asset for signed clearinghouse collateral deposits, and the UI can submit signed
stream `8` market init and oracle price publish actions through
`/api/perps/wallet/*`. The completion plan is recorded in
`docs/PERPS_BACKEND_COMPLETION_PLAN_2026_05_20.md`. The main blockers are now
full Docker zUSD-to-perps browser evidence, first-class typed Oracle adapter
fixtures, perps liquidation, and proof/ZK promotion.

The zUSD monetary lane is Liquity-like but does not claim exact Liquity V2
liquidation parity. The current 5% borrower-penalty gap is tracked in
`docs/ZUSD_LIQUITY_PARITY_STATUS_2026_05_20.md`.

## Current browser checks

Run these from repo root:

```bash
pytest -q \
  tests/integration/test_zusd_tau_wallet_ui_bridge.py \
  tests/integration/test_zusd_tau_wallet_ui_docker.py \
  tests/integration/test_zusd_monetary_wallet_ui_bridge.py \
  tests/integration/test_zusd_monetary_wallet_ui_docker.py \
  tests/integration/test_zeno_oracle_ui_bridge.py \
  tests/integration/test_perps_wallet_ui_bridge.py \
  tests/integration/test_autotrader_live_ui_bridge.py \
  tests/integration/test_perps_ui_preview_lock.py \
  tests/integration/test_confidential_ui_bridge.py
```

These checks prove:

- the mounted Oracle tab can bind to a real local Oracle service and execute a
  write-enabled local receipt flow when the service is started with
  `--allow-writes`;
- the mounted zUSD tab can submit through the Tau wallet bridge, including the local Docker Tau node lane;
- the mounted zUSD tab can submit stream `11` monetary-vault actions through the Tau-node-backed API, including the local Docker Tau node lane;
- the mounted perps tab fails closed to read-only preview by default for the demo trading grid in non-demo mode;
- the mounted perps wallet panel can submit signed stream `8` clearinghouse init
  and oracle price publish actions through the Tau-node-backed API;
- the mounted Strategy tab can prepare receipt-backed AutoTrader operations
  through the local API after explicit risk acknowledgement;
- the mounted confidential tab can load live operator posture from the stdlib API server.

Current backend-only perps bridge check:

```bash
pytest -q tests/integration/test_tau_testnet_dex_plugin.py::test_apply_app_tx_perps_accepts_zusd_token_as_quote_collateral
pytest -q tests/integration/test_tau_testnet_dex_plugin.py::test_apply_app_tx_zusd_monetary_mint_feeds_transferable_perps_collateral
pytest -q tests/integration/test_zusd_monetary_wallet_api.py
pytest -q tests/integration/test_perps_wallet_api.py
pytest -q tests/integration/test_perps_stream8_resilience.py
python3 tools/zenodex_live_cross_stream_stateful.py --format json
```

Current AutoTrader live-prepare checks:

```bash
pytest -q tests/integration/test_autotrader_live_api.py
pytest -q tests/integration/test_autotrader_live_ui_bridge.py -s
```

These prove the mounted strategy API requires explicit risk acknowledgement and
local-signing enablement, prepares a signed receipt-backed operation bundle, and
renders the result in the Strategy tab. They do not claim unattended production
strategy execution, production wallet key management, or production chain
submission.

Latest AutoTrader live-prepare pass on 2026-05-21:

```bash
python3 -m pytest -q tests/integration/test_autotrader_live_api.py
python3 -m pytest -q tests/integration/test_autotrader_live_ui_bridge.py -s
```

Results: `4 passed` and `1 passed`.

Latest local browser pass on 2026-05-20:

```bash
pytest -q tests/integration/test_zusd_tau_wallet_ui_bridge.py tests/integration/test_zusd_monetary_wallet_ui_bridge.py tests/integration/test_zeno_oracle_ui_bridge.py tests/integration/test_perps_ui_preview_lock.py tests/integration/test_confidential_ui_bridge.py
pytest -q tests/integration/test_dex_ui_live_bridge.py
```

Results: mounted non-spot browser checks `7 passed`; spot/pools browser checks
`2 passed`.

Latest perps live-wallet pass on 2026-05-20:

```bash
pytest -q tests/integration/test_perps_wallet_api.py
pytest -q tests/integration/test_perps_stream8_resilience.py
pytest -q tests/integration/test_perps_wallet_ui_bridge.py -s
```

Results: `4 passed`, `4 passed`, and `1 passed`.

Follow-on perps live-wallet pass on 2026-05-20:

```bash
pytest -q tests/integration/test_perps_wallet_api.py
pytest -q tests/integration/test_perps_stream8_resilience.py
pytest -q tests/integration/test_perps_wallet_ui_bridge.py -s
```

Results: `8 passed`, `5 passed`, and `2 passed`.

Oracle live-surface note: `tests/integration/test_zeno_oracle_ui_bridge.py`
now proves both the live dashboard read path and a write-enabled local receipt
flow from the mounted Oracle tab. The write smoke creates an identity,
registers and funds a query, registers and bonds a reporter, registers a
source, submits a report, builds aggregate/read/authorization receipts, and
pays rewards against a local `tools/zenodex-oracle serve --allow-writes`
instance.

Latest Oracle write-browser pass on 2026-05-21:

```bash
pytest -q tests/integration/test_zeno_oracle_ui_bridge.py::test_oracle_ui_smoke_runs_write_enabled_receipt_flow -s
```

Result: `1 passed`.

Latest cross-stream stateful replay pass on 2026-05-21:

```bash
python3 tools/zenodex_live_cross_stream_stateful.py --format json
pytest -q tests/integration/test_zenodex_live_cross_stream_stateful.py
```

Results: replay tool accepted `6` bounded scenarios plus `4` deterministic fuzz
seeds of `32` steps each; receipt tests `2 passed`. The covered disaster states
are duplicate zUSD replay side effects, cross-stream partial mutation, expired
zUSD deadline materialization, perps overdeposit materialization, missing Oracle
bridge settlement, balance drift after a zUSD-to-perps success path, and
long-horizon balance/nonce/atomicity drift.

## Economic-security status

Algorithmic game theory is required for value-moving actor surfaces before
promotion. The first bounded surfaces should be Oracle reporters/disputes,
perps liquidation and settlement keepers, AutoTrader delegation, proof-mining
rewards, and batch inclusion/routing games.

For each surface, record players, actions, timing, information, payoff, the
profitable-deviation query, bounded assumptions, and a replay lane such as
SMT/Z3, exact integer sweeps, TLA, ESSO/Tau, or Lean. A surface can move from
engineering evidence to an economic-security claim only after the same attack
query is replayed with positive and negative evidence.
