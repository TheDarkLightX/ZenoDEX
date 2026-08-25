# N-Party Perps — Public Testnet Status

> **Status: FAKE-VALUE PUBLIC TESTNET. `production_security_claim = false` on every surface.**
> This document is the consolidated status of the many-account ("N-party")
> perpetuals clearinghouse path: what is built, what is verified, and what is
> deliberately deferred. It does not authorize any production or custody claim.

## Why this exists

Perps previously shipped only as a **fixed 2-party clearinghouse**: every market
was `init_market_2p(account_a, account_b)`, positions were coupled by
`position_base_a + position_base_b = 0`, and `set_position_pair` required *both*
counterparties to co-sign one transaction. A normal public wallet could only
**observe**. The N-party path replaces that with an **open, epoch-batched,
net-zero clearinghouse**: any wallet joins by depositing collateral and submits
**single-signed** intents; a deterministic largest-remainder matcher clears the
batch with `Σδ = 0`; settlement is at the oracle-signed clearing price.

## Task ledger

| # | Deliverable | State | Evidence |
|---|-------------|-------|----------|
| T1 | Promote the machine-verified N-party core into `src/core` | ✅ | `src/core/perp_np_matching.py` + `perp_np_clearinghouse.py` (byte-faithful promotion; provenance + SHA-256 in `src/core/perp_np_promotion.md`) |
| T2 | `PerpClearinghouseNpMarketState` + dynamic membership | ✅ | `src/core/perps.py` (`PERP_MARKET_KIND_CLEARINGHOUSE_NP_V1`; net-zero / two-ledger conservation / insurance enforced fail-closed in `__post_init__`) |
| T3 | Engine apply path through `apply_perp_ops` | ✅ | `src/integration/perp_engine.py` `_apply_chnp_op` (`init_market_np` / `join_market` / `deposit`/`withdraw_collateral` / `submit_intent` / `publish_clearing_price` / `run_epoch` / `advance_epoch`); reject-is-no-op |
| T4 | Single-signed, gated wallet API surface | ✅ | `src/integration/perps_wallet_api.py` (`_NP_ACTIONS`, `_NP_MARKET_PREFIX`, `_np_clearinghouse_enabled()`; default off). 108 API tests green |
| T5 | Bind oracle/index price to settlement | ✅ | oracle-signed `publish_clearing_price` (real BLS) → `run_epoch` settle; operator cannot supply the price; nonzero funding fail-closed |
| T6 | UI: 3-wallet participation (observer-trap fix) + tests | ✅ (unit) / ⏳ (browser) | `tools/dex-ui/src/lib/perpPosition.js` resolves ANY participant from `accounts[]` (was 2p-only); 5 unit tests (`perpPosition.test.mjs`, `npm run test:lib`). Live browser/e2e test deferred — NP trade surface is intentionally gated off until backend review (§ Deferred) |
| T7 | Release smoke: 3+ participants long/short/settle | ✅ | `tools/zenodex_perp_np_release_smoke.py` (3/4/5 wallets, two-sided, net-zero, conservation, **deterministic state-header agreement**, snapshot roundtrip) + CI gate `tests/integration/test_perp_np_release_smoke.py` |
| T8 | Keep `production_security_claim=false` + this report | ✅ | claim is false on every surface; hard validators reject non-false (see § Posture) |

## Real ZK (scoped, not a production claim)

A real RISC0 (risc0-zkvm 2.x) zkVM circuit proves N-party settle+match
transitions: `zk/state_proof_risc0/` — a unified guest (`ZenoDexProofInputV1` =
`Spot | PerpsNp`) re-derives participant-set / pre-state / post-state /
state-delta hashes and re-checks net-zero, two-ledger conservation, insurance
ledger, and per-account margin **inside the zkVM**, fail-closed.

- Smoke: `tools/zeno_ledger_perp_np_risc0_real_proof_smoke.py --case all` →
  real STARK proofs (4/5-wallet), Python-independent hash cross-check, strict
  verify, multi-field tamper rejection, and fail-closed negatives.
- Reviewed by Gemini + Codex (adversarial). Hardening applied: i128 margin
  intermediates (overflow), negative-ledger guard, `checked_add` epoch,
  explicit scope/domain + intent-auth-not-in-circuit docstrings, `pre_app_hash`
  binding. See `docs/zenodex_perps_np_state_proof_risc0_v1.md`.

The circuit certifies a **solvent, margin-healthy settle+match epoch**; it does
NOT prove intent *authorization* (intents are unsigned in-circuit; authorization
is an external precondition the runtime enforces), oracle *authenticity*
(carried, not verified), app-state linkage, funding (fail-closed to zero), or
liquidation/ADL. It is a fail-closed safety surface, **not** the consensus
state-advance gate.

## Posture — `production_security_claim = false`

- **No surface sets it true.** Hard validators reject any non-false value
  (`src/integration/zeno_ledger_tokenomics.py`,
  `perps_wallet_encrypted_sss_backup.py`); the release gate
  (`tools/check_public_testnet_v0_1_16_release_ready.py`) asserts the verifier
  reports `false` and proves a `true` claim is rejected.
- Fake-value only; the NP wallet API is gated off by default.
- The claim stays false until ALL hold: real in-circuit intent authorization +
  oracle authenticity + app-state↔root linkage, zUSD proof coverage, production
  custody, artifact binding, and the runtime release gates.

## Deferred / open (honest)

- **ZK design decisions** (flagged, owner: protocol author): bind an
  intent-batch-hash in-circuit (vs documented external-auth precondition);
  min-fill δ==0 survivor → rejected receipt + no nonce advance; make verifier
  `expected` bindings mandatory for testnet verification.
- **Mutable post-state ledgers + ADL** are in active development in the ZK guest
  (fee collection / insurance draws / auto-deleverage) — closes the
  conservation-with-fees and insolvency/liveness scope.
- **UI browser/e2e test** for the live 3-wallet trade surface: deferred until
  the NP UI surface is ungated (post-review). The trade form / "join market"
  affordance stay unreachable (action allow-list + market-kind gate), not merely
  hidden.

## GlobalSettlement margin accounting SHADOW slice

The newer `GlobalSettlementABI V1` work contains an independently versioned
subject-bound margin accounting core in `src/core/perps_margin_*_v1.py` and
`zk/global_settlement_abi_v1/src/perps_margin*.rs`. It selects only behavior
already common to the documented peer-to-peer perps posture:

- one profile-selected collateral asset per market;
- exact command-owner/context-subject equality and monotonically increasing
  nonce, with authentication and grant verification reserved for composition;
- exact account, perps accounting-location, and claimant-liability candidate
  deltas;
- position-carrying withdrawal at or above the integer
  maintenance-plus-depeg requirement, with a committed complete Oracle
  authority/occurrence/price binding; flat-account withdrawal requires no
  Oracle dependency;
- exact zero aggregate peer-to-peer position and a maximum of 64 canonically
  ordered accounts in this bounded module state;
- explicit `ACTIVE`, `DRAIN_ONLY`, and `HALTED` market states, where
  `DRAIN_ONLY` rejects deposits while preserving withdrawal and close;
- close only after position and collateral reach zero;
- a release/market/account-namespaced drained terminal obligation and permanent
  closed account ID after close.

The Rust and Python projections share frozen accepted-transition roots for the
pre-state, command, post-state, candidate effect plan, typed private port,
terminal table, and module receipt. They do not yet share one data-driven
rejection-vector corpus. The private port exposes the command and Oracle
dependency commitments needed by a future exact route composition. This slice
remains `SHADOW`. Its candidate effect plan deliberately has no global
asset-conservation row because no governed perps lane coordinator currently
binds it to complete pre/post ZenoLedger balances, supply, and terminal-table
updates or verifies its committed Oracle authority and exact price port. The
global state refiner therefore cannot admit it as a complete settlement. No
route, RISC0 guest, release activation, writer, API, or UI was added.

Funding, intent matching, epoch settlement, objective Oracle witness/price-port
verification, liquidation, insurance, ADL, bankruptcy, and whole-market
terminal closeout remain unresolved for the M6 `PERPS_MARKET` row. The legacy
proof workspace remains quarantined and is not relabeled by this slice.

The ABI label `CUSTODY` identifies a committed accounting location. It makes no
claim that a third party controls a user's keys or is a legal custodian.

## Reproduce

```bash
# Engine + core (3+ wallets through apply_perp_ops)
python3 -m pytest tests/integration/test_perp_np_engine.py \
  tests/integration/test_perp_np_engine_review_negatives.py \
  tests/core/test_perp_np_clearinghouse.py -q          # 34 passed

# Wallet API (single-signed, gated)
python3 -m pytest tests/integration/test_perps_wallet_api.py -q   # 108 passed

# Release smoke (3/4/5 wallets, long/short/settle, deterministic header)
python3 tools/zenodex_perp_np_release_smoke.py --scenario all
python3 -m pytest tests/integration/test_perp_np_release_smoke.py -q

# UI observer-trap resolver (3-wallet)
( cd tools/dex-ui && npm run test:lib )

# Real ZK proof (heavy; needs the risc0 toolchain on PATH)
python3 tools/zeno_ledger_perp_np_risc0_real_proof_smoke.py --case all --timeout 900
```
