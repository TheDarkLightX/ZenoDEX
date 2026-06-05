# ZenoDEX Surface Status (2026-06-03)

Release-audit snapshot of every mounted ZenoDEX product surface, classified by
honest maturity. This is an evidence note, not a security attestation.

> **Product/testnet production posture: `production_security_claim = false`.**
> Every "LIVE" classification below means *local / loopback testnet* behaviour
> proven by a deterministic test. None of these mounted product surfaces is
> claimed to be production-secure. This dated product-surface note predates the
> spot-DEX CBC authority-surface closure and remains scoped to mounted
> local/testnet product behavior. Confidential runtime privacy, production
> Oracle authority exercise on a public testnet, hardware wallet custody,
> unattended strategy execution, and production ZK circuit soundness all remain
> explicit non-claims.

## Classification key

| Class | Meaning |
| --- | --- |
| **LIVE** | A mounted UI action drives a real backend transaction on a local / loopback testnet node and the result is verified by a deterministic test. Gating env flags (if any) are noted. |
| **DEMO-fixture** | The UI renders a clearly labelled demo/fixture surface that does not move authoritative state; the demo boundary is enforced and tested. |
| **PLACEHOLDER / bounded** | Only bounded metadata, receipts, or echo-bindings exist; the production capability is an explicit non-claim. |

## Surface matrix

| Surface | Class | Default posture | Authoritative backend module | Primary test(s) |
| --- | --- | --- | --- | --- |
| Swap | **LIVE** (local/testnet) | Signed spot swap through the Zeno ledger node `/api/swap` | `tools/zeno_ledger_node.py` (`_ui_swap_tx_v0`, `make_node_http_server_v0`) | `tests/integration/test_dex_ui_live_bridge.py`, `tests/integration/test_dex_live_adversarial.py` |
| Pools (add / remove / create) | **LIVE** (local/testnet) | Signed liquidity ops `/api/liquidity/{add,remove,create}` with a progressive LP-age lock | `tools/zeno_ledger_node.py` (`_ui_liquidity_tx_v0`, `_ui_create_pool_tx_v0`), `src/integration/lp_position_age_gate.py` | `tests/integration/test_dex_ui_live_bridge.py`, `tests/integration/test_dex_live_adversarial.py` |
| Perpetuals | **DEMO-fixture** grid + **LIVE** stream-8 wallet (gated, BLS) | Read-only preview by default; signed stream-8 clearinghouse via `/api/perps/wallet/*` when the gated API is enabled | `src/integration/perps_wallet_api.py`, `src/integration/perp_engine.py` | `tests/integration/test_perps_ui_preview_lock.py`, `tests/integration/test_perps_wallet_api.py`, `tests/integration/test_perps_wallet_ui_bridge.py`, `tests/integration/test_perps_stream8_resilience.py` |
| zUSD | **LIVE** (local/testnet, gated, BLS) | Stream-9 token transport + stream-11 monetary vault (collateral, mint, repay, redeem, stability pool, liquidation, SP claim) | `src/integration/zusd_monetary_wallet_api.py`, `src/integration/zusd_monetary_bridge.py`, `src/integration/zusd_tau_token.py` | `tests/integration/test_zusd_monetary_wallet_api.py`, `tests/integration/test_zusd_monetary_wallet_ui_bridge.py`, `tests/integration/test_zusd_tau_wallet_ui_bridge.py`, `*_ui_docker.py` |
| Oracle | **LIVE** (local operator console) | Local read/write API + dashboard; writes **disabled by default** (`--allow-writes` required); production authority exercise on a public testnet remains open | `tools/zenodex_oracle.py`, `src/integration/zeno_oracle_authority.py`, `src/integration/zeno_oracle_authorization.py` | `tests/integration/test_zeno_oracle_ui_bridge.py`, `tests/integration/test_zeno_oracle_authority.py`, `tests/integration/test_zenodex_oracle_cli.py` |
| Strategy / AutoTrader | **LIVE** (local/testnet, gated) | Receipt-backed prepare + gated submit / execute-once / bounded supervisor; **off by default** behind `AUTOTRADER_LIVE_ALLOW_LOCAL_SIGNING`, `AUTOTRADER_LIVE_ALLOW_TESTNET_SUBMISSION`, `AUTOTRADER_LIVE_EXECUTE_ONCE_ENABLED`, `AUTOTRADER_LIVE_SUPERVISOR_ENABLED` | `src/integration/autotrader_live_api.py`, `src/integration/autotrader_live.py`, `src/integration/autotrader_controller.py` | `tests/integration/test_autotrader_live_api.py`, `tests/integration/test_autotrader_live_ui_bridge.py` |
| Confidential | **LIVE** attestation + bounded redacted runtime receipt; **PLACEHOLDER** for runtime privacy | Status + external-verifier attestation + bounded runtime receipt via `/api/confidential/attestation/{verify,admit,execute}`; runtime confidential privacy is a non-claim | `src/integration/confidential_attestation_api.py`, `src/integration/confidential_attestation_verifier.py` | `tests/integration/test_confidential_ui_bridge.py`, `tests/integration/test_api_server_confidential.py`, `tests/integration/test_zenodex_live_cross_stream_stateful.py` |
| Proofs / ZK | **PLACEHOLDER / bounded** | Echo-bound verifier + circuit artifact metadata and proof-wrapper fail-closed gates only; production circuits and soundness evidence are non-claims | `src/integration/live_proof_wrapper.py`, `src/integration/proof_verifier.py` | `tests/integration/test_perps_wallet_api.py` (`*_rejected_zk_proof_blocks_sendtx`), `tests/integration/test_zusd_monetary_wallet_api.py` (`*_rejected_zk_proof_blocks_sendtx`) |

## Adversarial / fail-closed coverage (this audit)

`tests/integration/test_dex_live_adversarial.py` adds cross-cutting fail-closed
cases against the mounted live spot surfaces. Each case asserts a concrete
accept **or** a concrete reject (HTTP status + error string); no fabricated
success is permitted. Cases whose backend is BLS-gated (`py_ecc`), browser-gated
(Chrome), Docker-gated, or gated off by default are **skipped with an explicit
reason** rather than asserting an unverifiable outcome.

| # | Adversarial case | Reachable surface | Posture / reject |
| --- | --- | --- | --- |
| 1 | Trading with no wallet connected | `/api/swap` (no `senderPubkey`) | 400, `sender_pubkey is required` |
| 2 | Stale / empty balances | `/api/swap` from unfunded sender | 400, `balance_insufficient` |
| 3 | Stale oracle feed | perps settle/liquidate freshness (gated off) | skipped; covered by `test_perps_stream8_resilience.py` |
| 4 | Duplicate nonce / replay | signed `/api/swap` replay | py_ecc-gated; reject + no height advance |
| 5 | Mismatched sender | forged signed `/api/swap` | py_ecc-gated; 400 fail-closed |
| 6 | Wrong account role (LP lock) | signed add then early `/api/liquidity/remove` | py_ecc-gated; 400, `lp_position_locked`, no height advance |
| 7 | Expired intent | swap builder propagation + signed live submit | builder records past deadline (no clamp); engine rejects (`Intent expired`) at `dex_engine.py:736` |
| 8/9 | Wrong / missing proof | stream-8 / stream-11 proof-wrapper gate | binding-control anchors asserted; e2e reject covered by gated wallet API tests |
| 10 | API unavailable | POST to dead port | raises `URLError`/`OSError` (no fabricated success) |
| 11 | Unsigned swap | `/api/swap` without signature | 400, `missing_intent_signature` |
| 12 | Slippage breach | `/api/swap` with unreachable `minAmountOut` | 400, `slippage_min_amount_out` |

## Release-evidence gate

`python3 tools/check_dex_live_product_goal.py --json` audits the mounted-UI
direction, ZenoOracle live mount, live transaction surfaces beyond spot, and
browser/stateful/resilience evidence. Expected posture:

- `ok = true` (all anchor + forbidden checks pass);
- `code_goal_complete = true`;
- `operational_residual_limits_open = true`;
- `goal_complete = false` (operational limits remain open);
- `status = "code_evidence_complete_with_open_operational_limits"`.

The script itself emits `production_security_claim` only as `false` (e.g. the
faucet route), consistent with this note.

## Residual operational limits (open, by design)

Mirrors `RESIDUAL_LIMITS` in `tools/check_dex_live_product_goal.py`:

1. **production_oracle_authority** — public-testnet exercise of a signed
   production Oracle authority profile remains open.
2. **hardware_wallet_ux** — live OS prompt capture, hardware custody, and
   hardware-wallet execution remain open.
3. **zk_wrapping** — production circuit artifacts and soundness evidence remain
   open; only bounded echo-bound artifact bindings exist.
4. **production_autotrader** — unattended production execution remains a
   non-claim; only local/testnet execute-once + bounded supervisor.
5. **confidential_runtime** — runtime private-execution privacy remains a
   non-claim; only attestation receipts + bounded redacted runtime receipts.

## Interpretation

The mounted app is the intended ZenoDEX shell. Every surface above is either a
verified local/testnet LIVE lane, a clearly-labelled DEMO-fixture surface, or a
bounded PLACEHOLDER with the production capability stated as an explicit
non-claim. This note makes **no mounted product-surface production-security
claim** (`production_security_claim = false`) and should be read alongside
`docs/ZENODEX_UI_SURFACE_STATUS_2026_05_20.md` and
`docs/PERPS_BACKEND_COMPLETION_PLAN_2026_05_20.md`.
