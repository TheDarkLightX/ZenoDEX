# ZenoDEX Live Feature Matrix, 2026-05-20

This matrix records what is live-wired on the integrated UI ledger bridge branch
and what still needs promotion work before it can be described as a live
testnet feature.

Primary UI evidence command:

```bash
pytest -q tests/integration/test_dex_ui_live_bridge.py
```

The browser test starts writer, forwarder, and readonly ledger nodes; starts the
Vite UI with live-mode proxy targets; submits actions through the rendered UI;
checks accepted writer receipts; checks readonly rejection text; and pulls the
writer live ledger into the readonly node for deterministic replay.

## Assurance Evidence, 2026-05-20

The current branch also has bounded disaster-state, chaos, symbolic/concolic,
and temporal evidence for the live ledger bridge:

| Lane | Command | Result |
| --- | --- | --- |
| Browser UI, local multi-node | `pytest -q tests/integration/test_dex_ui_live_bridge.py` | `3 passed, 1 skipped` |
| Browser UI, published Docker nodes | `ZENO_DEX_DOCKER_LIVE_TEST=1 pytest -q tests/integration/test_dex_ui_live_bridge.py::test_dex_ui_smoke_runs_against_published_docker_nodes` | `1 passed` |
| Live disaster-state search | `pytest -q tests/integration/test_zeno_ledger_live_disaster_state_search.py` | `1 passed`; `11` actions, `7` selected disasters unreachable under bound |
| Deterministic ledger chaos | `pytest -q tests/integration/test_zeno_ledger_chaos_harness.py` and `python3 tools/zeno_ledger_chaos_harness.py --json` | `4 passed`; `8` scenarios, zero errors |
| WES-ranked multi-Docker boundary search | `python3 tools/zeno_ledger_multidocker_wes_disaster_search.py --budget 64 --top-k 24 ...` | `28` candidates, `168` checker calls, zero disasters, zero invariant violations |
| TLA/TLC bounded models | `python3 tools/render_tla_claim_summary.py --check` and `python3 tools/run_tla_models.py --json --timeout-s 120` | `32` models, zero errors |
| Symbolic/concolic fast gate | `bash tools/run_acceptance_tcb_fuzz_gate.sh` | `58 passed` |
| Stateful deep fuzz gate | `PYTHON=/tmp/zenodex-deep-venv/bin/python bash tools/run_acceptance_tcb_fuzz_gate_deep.sh` | mypy clean; `113 passed` |

The WES lane is ranking only. The deterministic checker remains authoritative
for whether a candidate is accepted, rejected, or a disaster witness.

## Spot DEX Live Matrix

| Feature | Node endpoint | UI path | Receipt / error behavior | Follower replay | Status |
| --- | --- | --- | --- | --- | --- |
| Pool discovery | `GET /api/pools` on writer | Live console pool and quote display | Read-only response, no receipt | Not applicable | Wired |
| API swap | `POST /api/swap` on writer | Direct API test uses the same pool IDs as UI | Accepted receipt, `tx_accepted = true` | Covered by later replay when in writer live ledger | Wired |
| UI faucet | `POST /faucet` on writer | Faucet selected asset button and smoke script | Appends `testnet_faucet` block | Pulled into readonly node | Wired |
| UI exact-in swap | `POST /tx` with TauSwap `SWAP_EXACT_IN` | Submit swap button and smoke script | Accepted TauSwap receipt | Pulled into readonly node | Wired |
| UI add liquidity | `POST /tx` with TauSwap `ADD_LIQUIDITY` | Add liquidity button and smoke script | Accepted TauSwap receipt | Pulled into readonly node | Wired |
| UI remove liquidity | `POST /tx` with TauSwap `REMOVE_LIQUIDITY` | Remove liquidity button and smoke script | Accepted TauSwap receipt | Pulled into readonly node | Wired |
| Forwarder submission | Forwarder `POST /tx`, forwarded to writer | Smoke script submits through forwarder node target | Writer returns accepted receipt with `forwarded_to` context | Pulled into readonly node | Wired |
| Readonly rejection | Readonly `POST /tx` | Smoke script submits through readonly node target | Visible `testnet_intake_disabled` rejection, no writer append | Not applicable | Wired |
| Visible response state | UI `last-response`, run log, `smoke-status` | Browser DOM check | Accepted and rejected outcomes are visible | Not applicable | Wired |

## Live/Demo Boundary Audit

The mounted `tools/dex-ui/src/App.jsx` is currently a live spot-ledger test
console. It does not mount the older multi-tab product workbench. In live mode
(`VITE_DEMO_MODE=false`) the mounted console uses only the ledger proxy
endpoints configured by:

- `LEDGER_WRITER_TARGET`
- `LEDGER_FORWARDER_TARGET`
- `LEDGER_READONLY_TARGET`
- `API_PROXY_TARGET` for the compatibility `/api/*` proxy

The following product surfaces exist in the source tree but are not live-mounted
by the current `App.jsx`:

| Surface | Current posture | Missing promotion work |
| --- | --- | --- |
| ZenoOracle UI | `tools/dex-ui/src/components/ZenoOracleDashboard.jsx` exists, with local Oracle API documentation, but the current mounted app does not expose it. | Mount it deliberately, run a browser smoke against `tools/zenodex-oracle serve`, and label any preview data as local/demo. |
| Perps | `tools/dex-ui/src/lib/PerpProvider.jsx` can use demo state or `/api/perps/*` development routes. | Wire to a production ledger transaction path or keep it explicitly local/dev; add fail-closed live-mode labels and tests. |
| zUSD | `tools/dex-ui/src/components/ZUSDWorkbench.jsx` is a workbench/demo surface. | Wire mint/repay/redeem/liquidation to the production transaction path before claiming live support. |
| Strategy / AutoTrader | `tools/dex-ui/src/components/StrategyWorkbench.jsx` is static/demo workbench state. | Keep advisory strategy flows outside authoritative settlement and add live policy-submission receipts before promotion. |
| Confidential | `tools/dex-ui/src/components/ConfidentialWorkbench.jsx` can read `/api/confidential/status`; it is a status/beta posture surface. | Add explicit operator status wiring, disabled transaction controls in live mode, and receipt-backed beta evidence. |

## Remaining Work

1. Run the fresh-clone gate on another checkout after the next commit is pushed:

```bash
git clone --branch codex/ui-ledger-bridge-20260520 git@github.com:TheDarkLightX/Autonomous-Tau-DEX.git /tmp/zenodex-ui-fresh
cd /tmp/zenodex-ui-fresh
cd tools/dex-ui && npm ci && npm run build
cd ../..
pytest -q tests/integration/test_dex_ui_live_bridge.py
```

2. Re-run the multi-machine Docker scenario from a clean clone on the MacBook or
another host. The UI integration test proves local multi-node behavior, while
Docker still needs the host networking, image build, and cross-machine operator
path checked from the pushed branch.

3. Decide whether the next mounted UI should stay as a live spot test console or
restore a multi-tab app. If the multi-tab app returns, perps, zUSD, strategy,
confidential, and Oracle tabs need explicit live/demo labels and fail-closed
live-mode behavior.

4. Continue expanding disaster-state witness search beyond the current bounded
seed families. The branch now covers live role/auth/replay disasters, deterministic
chaos scenarios, WES-ranked multi-Docker boundary probes, symbolic/concolic
request and state surfaces, and bounded TLA models. Remaining depth work is WAN
fault injection, longer-running randomized campaigns, and product-surface
promotion for UI areas that remain demo-only.
