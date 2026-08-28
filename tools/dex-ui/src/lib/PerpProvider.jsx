import { useReducer, useCallback, useLayoutEffect, useMemo, useRef } from 'react';
import { useDemoMode } from './DemoModeContext.jsx';
import { PerpContext } from './PerpContext.jsx';
import { PERP_DEMO_MARKETS, PERP_DEMO_POSITIONS, PERP_DEMO_HISTORY } from './perpMockData.js';
import {
    getRuntimeConfig,
    getRuntimeBooleanFlag,
    getRuntimeValueRoutePresentationV1,
    apiGetPerpsWalletStatus,
    apiPreparePerpsWallet,
    apiSubmitPerpsWallet,
} from './api.js';
import { buildSignedTauTransaction } from '../sdk/dexIntentSigner.js';
import {
    toBigInt,
    pnlQuote,
    liquidationPriceE8,
    effectiveLeverage,
    marginRatio,
    e8ToNumber,
} from './perpMath.js';

// ---- Live wallet bridge ------------------------------------------------------
// Maps a market summary from /api/perps/wallet/status (Tau-node-backed) into
// the shape PerpProvider / PerpOrderForm / PerpPositionPanel expect, and
// derives the connected wallet's position for that market.

function _normalizePubkey(value) {
    return String(value || '').toLowerCase().replace(/^0x/, '');
}

function _derivePhase(market) {
    // Open: epoch is collecting orders. PricePublished: clearing price is set
    // for this epoch (only apply_funding allowed). Settled: epoch closed
    // (advance_epoch required). The wallet status doesn't expose the phase
    // directly, but the epoch numbers do.
    const now = Number(market?.now_epoch ?? 0);
    const cpEpoch = Number(market?.clearing_price_epoch ?? 0);
    const cpE8 = Number(market?.clearing_price_e8 ?? 0);
    // A clearing price set for the CURRENT epoch means it has been published.
    if (cpEpoch === now && cpE8 > 0) return 'PricePublished';
    // SETTLED is intentionally NOT inferred here. The authoritative kernel rule
    // (src/core/perps.py `_infer_epoch_phase`) distinguishes SETTLED from
    // PRICE_PUBLISHED via a `clearing_price_seen`/settled flag that the wallet
    // /status payload does not expose — both phases share
    // clearing_price_epoch == now_epoch. Guessing from epoch arithmetic alone
    // (e.g. cpEpoch < now) would falsely label a freshly-advanced OPEN epoch as
    // Settled. The honest fix is backend: surface clearing_price_seen in the 2p
    // market summary, then resolve SETTLED here. Until then the stepper stops at
    // PRICE_PUBLISHED rather than showing a false SETTLED.
    return 'Open';
}

function mapWalletMarketToProviderShape(walletMarket) {
    if (!walletMarket || typeof walletMarket !== 'object') return null;
    const id = walletMarket.market_id || walletMarket.id;
    if (!id) return null;
    const kind = walletMarket.kind || 'unknown';
    const now = Number(walletMarket.now_epoch ?? 0);
    const oracleEpoch = Number(walletMarket.oracle_last_update_epoch ?? 0);
    const maintBps = Number(walletMarket.maintenance_margin_bps ?? 500);
    // Sensible defaults for fields the wallet status doesn't expose.
    // initialMarginBps is conventionally ~2x maintenance.
    const initBps = Math.max(maintBps * 2, 1_000);
    return {
        id,
        kind,
        quoteAsset: walletMarket.quote_asset || null,
        nowEpoch: now,
        oracleLastUpdateEpoch: oracleEpoch,
        oracleSeen: oracleEpoch === now,
        epochPhase: _derivePhase(walletMarket),
        indexPriceE8: Number(walletMarket.index_price_e8 ?? 0),
        clearingPriceE8: Number(walletMarket.clearing_price_e8 ?? 0),
        clearingPriceEpoch: Number(walletMarket.clearing_price_epoch ?? 0),
        maintenanceMarginBps: maintBps,
        initialMarginBps: initBps,
        depegBufferBps: 0,
        // Fields below are not exposed by wallet status — defaulted so the
        // existing components don't NaN. Replace when the wallet API surfaces
        // them or when a separate market-config endpoint is wired.
        maxPositionAbs: Number.MAX_SAFE_INTEGER,
        maxOracleStalenessEpochs: 4,
        breakerActive: false,
        // 2p-specific fields (preserved for PerpAccountSummary / debug):
        accountAPubkey: walletMarket.account_a_pubkey || null,
        accountBPubkey: walletMarket.account_b_pubkey || null,
        positionBaseA: Number(walletMarket.position_base_a ?? 0),
        positionBaseB: Number(walletMarket.position_base_b ?? 0),
        collateralE8A: Number(walletMarket.collateral_e8_a ?? 0),
        collateralE8B: Number(walletMarket.collateral_e8_b ?? 0),
        feePoolE8: Number(walletMarket.fee_pool_e8 ?? 0),
        feeIncome: nullableNumber(walletMarket.fee_income ?? walletMarket.fee_pool_quote),
        initialInsurance: nullableNumber(walletMarket.initial_insurance),
        insuranceBalance: nullableNumber(walletMarket.insurance_balance),
        claimsPaid: nullableNumber(walletMarket.claims_paid),
    };
}

function derivePositionFromWalletMarket(walletMarket, userPubkey) {
    // For a 2p clearinghouse market, the user's position is whichever
    // account_*_pubkey matches the connected wallet.
    if (!walletMarket || !userPubkey) return null;
    const u = _normalizePubkey(userPubkey);
    const a = _normalizePubkey(walletMarket.account_a_pubkey);
    const b = _normalizePubkey(walletMarket.account_b_pubkey);
    let positionBase = 0;
    let collateralQuote = 0;
    // `collateral_e8_*` is e8-scaled quote per the kernel (1e8 = 1 quote unit),
    // but `collateralQuote` is PLAIN integer quote everywhere downstream
    // (perpMath/perpValidation/position panel + demo data). Divide out the 1e8
    // scale here at the read boundary; trunc drops the sub-1-quote fraction for
    // display. The WRITE path (deposit/withdrawCollateral) stays unscaled —
    // perp_engine scales amount*1e8 server-side, so do NOT pre-scale there.
    if (u && u === a) {
        positionBase = Number(walletMarket.position_base_a ?? 0);
        collateralQuote = Math.trunc(Number(walletMarket.collateral_e8_a ?? 0) / 1e8);
    } else if (u && u === b) {
        positionBase = Number(walletMarket.position_base_b ?? 0);
        collateralQuote = Math.trunc(Number(walletMarket.collateral_e8_b ?? 0) / 1e8);
    } else {
        return null;
    }
    return {
        marketId: walletMarket.market_id,
        pubkey: userPubkey,
        positionBase,
        collateralQuote,
        // Entry price isn't tracked by the 2p market state — index price is the
        // best honest stand-in until a positions endpoint surfaces entry.
        entryPriceE8: Number(walletMarket.index_price_e8 ?? 0),
    };
}

/**
 * PerpContext - Shared state for the perpetuals trading interface.
 *
 * Uses useReducer for predictable state transitions.
 * Auto-detects demo mode via DemoModeContext.
 */

// -- State shape --------------------------------------------------------------

const initialState = {
    markets: [],
    selectedMarketId: null,
    positions: {},
    history: [],
    loading: false,
    error: null,
};

// -- Actions ------------------------------------------------------------------

const ACTIONS = {
    SET_MARKETS: 'SET_MARKETS',
    SELECT_MARKET: 'SELECT_MARKET',
    SET_POSITIONS: 'SET_POSITIONS',
    SET_HISTORY: 'SET_HISTORY',
    APPEND_HISTORY: 'APPEND_HISTORY',
    SET_LOADING: 'SET_LOADING',
    SET_ERROR: 'SET_ERROR',
    UPDATE_MARKET: 'UPDATE_MARKET',
    UPDATE_POSITION: 'UPDATE_POSITION',
    CLEAR_ACCOUNT: 'CLEAR_ACCOUNT',
};

function emptyPosition(pubkey, marketId) {
    return {
        marketId,
        pubkey: pubkey ?? 'demo',
        positionBase: 0,
        entryPriceE8: 0,
        collateralQuote: 0,
        fundingPaidCumulative: 0,
        fundingLastAppliedEpoch: 0,
    };
}

function asSafeInt(value) {
    const n = Number(value);
    if (!Number.isFinite(n)) return null;
    const i = Math.trunc(n);
    if (!Number.isSafeInteger(i)) return null;
    return i;
}

function nullableNumber(value) {
    if (value == null) return null;
    const n = Number(value);
    return Number.isFinite(n) ? n : null;
}

function createLocalTxId(prefix = 'perp') {
    const salt = Math.random().toString(16).slice(2, 10);
    return `${prefix}-${Date.now()}-${salt}`;
}

function createLocalTxHash() {
    const bytes = new Uint8Array(32);
    if (typeof globalThis !== 'undefined' && globalThis.crypto?.getRandomValues) {
        globalThis.crypto.getRandomValues(bytes);
    } else {
        for (let i = 0; i < bytes.length; i += 1) {
            bytes[i] = Math.floor(Math.random() * 256);
        }
    }
    const hex = Array.from(bytes, (b) => b.toString(16).padStart(2, '0')).join('');
    return `0x${hex}`;
}

function defaultPerpsDeadline() {
    return Math.floor(Date.now() / 1000) + 3600;
}

function externalTauSignerFromWallet(wallet) {
    for (const key of ['signTauTransactionPayload', 'signTauTransaction', 'signTauPayload']) {
        if (typeof wallet?.[key] === 'function') {
            return wallet[key].bind(wallet);
        }
    }
    return null;
}

function actionTitle(actionLabel, marketId) {
    if (actionLabel === 'set_position') return `Perps Position Update (${marketId || 'market'})`;
    if (actionLabel === 'deposit') return `Perps Collateral Deposit (${marketId || 'market'})`;
    if (actionLabel === 'withdraw') return `Perps Collateral Withdraw (${marketId || 'market'})`;
    if (actionLabel === 'deposit_insurance') return `Perps Insurance Deposit (${marketId || 'market'})`;
    return `Perps Action (${marketId || 'market'})`;
}

function applyDemoAction(endpoint, body, snapshot, callerPubkey) {
    const marketId = typeof body?.marketId === 'string' ? body.marketId : '';
    if (!marketId) {
        return { ok: false, error: 'missing_marketId' };
    }
    const market = snapshot.markets.find(m => m.id === marketId);
    if (!market) {
        return { ok: false, error: 'market_not_found' };
    }

    if (endpoint.includes('/collateral')) {
        const action = body?.action;
        if (action !== 'deposit' && action !== 'withdraw') {
            return { ok: false, error: 'invalid_action' };
        }
        const amount = asSafeInt(body?.amount);
        if (amount == null || amount <= 0) {
            return { ok: false, error: 'invalid_amount' };
        }
        const base = snapshot.positions[marketId] ?? emptyPosition(callerPubkey, marketId);
        const nextCollateral = action === 'deposit'
            ? Number(base.collateralQuote ?? 0) + amount
            : Number(base.collateralQuote ?? 0) - amount;
        if (nextCollateral < 0) {
            return { ok: false, error: 'guard_rejected', detail: 'insufficient_collateral' };
        }
        return {
            ok: true,
            demo: true,
            position: {
                ...base,
                marketId,
                pubkey: callerPubkey ?? 'demo',
                collateralQuote: nextCollateral,
            },
        };
    }

    if (endpoint.includes('/position')) {
        const newPositionBase = asSafeInt(body?.newPositionBase);
        if (newPositionBase == null) {
            return { ok: false, error: 'invalid_newPositionBase' };
        }
        const base = snapshot.positions[marketId] ?? emptyPosition(callerPubkey, marketId);
        return {
            ok: true,
            demo: true,
            position: {
                ...base,
                marketId,
                pubkey: callerPubkey ?? 'demo',
                positionBase: newPositionBase,
                entryPriceE8: newPositionBase === 0 ? 0 : Number(market.indexPriceE8 ?? 0),
            },
        };
    }

    if (endpoint.includes('/insurance')) {
        const amount = asSafeInt(body?.amount);
        if (amount == null || amount <= 0) {
            return { ok: false, error: 'invalid_amount' };
        }
        return {
            ok: true,
            demo: true,
            market: {
                id: marketId,
                insuranceBalance: Number(market.insuranceBalance ?? 0) + amount,
                initialInsurance: Number(market.initialInsurance ?? 0) + amount,
            },
        };
    }

    return { ok: false, error: 'unsupported_demo_action' };
}

function reducer(state, action) {
    switch (action.type) {
        case ACTIONS.SET_MARKETS:
            return {
                ...state,
                markets: action.payload,
                selectedMarketId: state.selectedMarketId || (action.payload[0]?.id ?? null),
                loading: false,
            };
        case ACTIONS.SELECT_MARKET:
            return { ...state, selectedMarketId: action.payload };
        case ACTIONS.SET_POSITIONS:
            return { ...state, positions: action.payload };
        case ACTIONS.SET_HISTORY:
            return { ...state, history: action.payload };
        case ACTIONS.SET_LOADING:
            return { ...state, loading: action.payload };
        case ACTIONS.SET_ERROR:
            return { ...state, error: action.payload, loading: false };
        case ACTIONS.UPDATE_MARKET:
            return {
                ...state,
                markets: state.markets.map(m =>
                    m.id === action.payload.id ? { ...m, ...action.payload } : m
                ),
            };
        case ACTIONS.UPDATE_POSITION:
            return {
                ...state,
                positions: {
                    ...state.positions,
                    [action.payload.marketId]: {
                        ...state.positions[action.payload.marketId],
                        ...action.payload.data,
                    },
                },
            };
        case ACTIONS.APPEND_HISTORY:
            return { ...state, history: [action.payload, ...state.history] };
        case ACTIONS.CLEAR_ACCOUNT:
            return { ...state, positions: {}, history: [] };
        default:
            return state;
    }
}

// -- Context ------------------------------------------------------------------

export function PerpProvider({ children, wallet, onTransaction }) {
    const { demoMode } = useDemoMode();
    const [state, dispatch] = useReducer(reducer, initialState);
    const runtimeConfig = getRuntimeConfig();
    const { perpsWalletEnabled } = getRuntimeValueRoutePresentationV1(runtimeConfig);
    const localTestnetWritesDefault = runtimeConfig.deployment === 'local-testnet'
        || String(runtimeConfig.chainId || '').includes('localtest')
        || String(runtimeConfig.chainId || '').includes('local-testnet');
    const perpsPreviewWritesRequested = useMemo(() => getRuntimeBooleanFlag({
        queryKey: 'perpsPreviewWrites',
        runtimeKey: 'perpsPreviewWrites',
        envKey: 'VITE_PERPS_PREVIEW_WRITES',
        defaultValue: localTestnetWritesDefault,
    }), [localTestnetWritesDefault]);
    const writeEnabled = demoMode || (perpsWalletEnabled && perpsPreviewWritesRequested);
    const writeLockReason = !demoMode && !perpsWalletEnabled
        ? 'Perpetuals value actions are quarantined in this release profile. The retired stream-8 route cannot be enabled by URL or build-time flags.'
        : !writeEnabled
            ? 'Trader writes require a production signer bridge or an explicitly admitted local-testnet route.'
            : '';
    const pubkey = wallet?.address ?? null;
    // Secure default: browser-held private keys are accepted only for local
    // testnet signing. Production paths must provide an external signed Tau
    // payload; raw private keys are never forwarded to the server.
    const walletPrivkey = wallet?.privkey ?? null;
    const browserHotSigningAllowed = Boolean(
        perpsWalletEnabled
        && walletPrivkey
        && wallet?.localTestnetGenerated
        && localTestnetWritesDefault,
    );
    const externalTauSigner = externalTauSignerFromWallet(wallet);
    // Forward ref so submitAction can refresh state after a live action
    // without forming a circular useCallback dependency.
    const loadMarketsRef = useRef(null);
    // Monotonic request counter to discard responses from stale loadMarkets calls.
    const loadSeqRef = useRef(0);
    // Track current pubkey for stale-action detection in submitAction.
    const pubkeyRef = useRef(pubkey);
    // Snapshot latest reducer state for synchronous demo-mode updates.
    const stateRef = useRef(state);
    // Track previous pubkey to detect wallet identity changes.
    const prevPubkeyRef = useRef(pubkey);

    useLayoutEffect(() => {
        pubkeyRef.current = pubkey;
    }, [pubkey]);

    useLayoutEffect(() => {
        stateRef.current = state;
    }, [state]);

    // Load market data
    const loadMarkets = useCallback(async () => {
        const seq = ++loadSeqRef.current;
        dispatch({ type: ACTIONS.SET_LOADING, payload: true });
        // Clear account data only when the wallet identity actually changed,
        // so optimistic updates from submitAction survive a same-wallet reload.
        if (pubkey !== prevPubkeyRef.current) {
            dispatch({ type: ACTIONS.CLEAR_ACCOUNT });
            prevPubkeyRef.current = pubkey;
        }
        try {
            if (demoMode) {
                if (seq !== loadSeqRef.current) return;
                dispatch({ type: ACTIONS.SET_MARKETS, payload: PERP_DEMO_MARKETS });
                dispatch({ type: ACTIONS.SET_POSITIONS, payload: PERP_DEMO_POSITIONS });
                dispatch({ type: ACTIONS.SET_HISTORY, payload: PERP_DEMO_HISTORY });
            } else if (!perpsWalletEnabled) {
                if (seq !== loadSeqRef.current) return;
                dispatch({ type: ACTIONS.SET_MARKETS, payload: [] });
                dispatch({ type: ACTIONS.SET_POSITIONS, payload: {} });
                dispatch({ type: ACTIONS.SET_HISTORY, payload: [] });
            } else {
                // Live mode: read from the Tau-node-backed wallet status. This
                // is the authoritative source. The legacy /api/perps/markets
                // demo endpoint is no longer consulted in live mode.
                // 12s budget: the Tau-node-backed status response can carry
                // wallet authority + signer ceremony evidence and routinely
                // takes 2–3 s on local-testnet, so a tighter cap shows the
                // user spurious "timeout" banners even when the call would
                // have finished in time.
                const statusResp = await apiGetPerpsWalletStatus({ timeoutMs: 12000 });
                if (seq !== loadSeqRef.current) return; // stale
                const status = statusResp?.status || {};
                const rawMarkets = Array.isArray(status.markets) ? status.markets : [];
                const summaries = rawMarkets
                    .map(mapWalletMarketToProviderShape)
                    .filter(Boolean);
                dispatch({ type: ACTIONS.SET_MARKETS, payload: summaries });

                // Positions are embedded in each 2p market (account_a/b pubkeys
                // + position_base_a/b). Derive a positions map keyed by marketId
                // for the connected wallet.
                if (pubkey) {
                    const positions = {};
                    for (const m of rawMarkets) {
                        const pos = derivePositionFromWalletMarket(m, pubkey);
                        if (pos) {
                            positions[pos.marketId] = pos;
                        }
                    }
                    if (seq !== loadSeqRef.current) return; // stale
                    dispatch({ type: ACTIONS.SET_POSITIONS, payload: positions });
                }
                // History: wallet status doesn't expose tx history. Leave empty
                // until a dedicated history endpoint is added — better to show
                // nothing than to show stale demo data.
                dispatch({ type: ACTIONS.SET_HISTORY, payload: [] });
                if (!status.node_reachable) {
                    dispatch({
                        type: ACTIONS.SET_ERROR,
                        payload: status.error || 'tau_node_unreachable',
                    });
                }
            }
            if (seq === loadSeqRef.current) {
                dispatch({ type: ACTIONS.SET_ERROR, payload: null });
            }
        } catch (err) {
            if (seq !== loadSeqRef.current) return; // stale
            dispatch({ type: ACTIONS.SET_ERROR, payload: err.message });
        }
    }, [demoMode, perpsWalletEnabled, pubkey]);

    // Keep the ref pointing at the latest loadMarkets so submitAction can
    // refetch authoritative state after a live action without depending on it.
    useLayoutEffect(() => {
        loadMarketsRef.current = loadMarkets;
    }, [loadMarkets]);

    // Select a market
    const selectMarket = useCallback((marketId) => {
        dispatch({ type: ACTIONS.SELECT_MARKET, payload: marketId });
    }, []);

    // (Live market detail is refreshed via loadMarkets — the wallet status
    // payload already includes every market's full state, so a per-market
    // detail fetch is no longer needed.)

    // Get the currently selected market
    const selectedMarket = useMemo(() => {
        return state.markets.find(m => m.id === state.selectedMarketId) || null;
    }, [state.markets, state.selectedMarketId]);

    // Get position for current market
    const currentPosition = useMemo(() => {
        if (!state.selectedMarketId) return null;
        return state.positions[state.selectedMarketId] || null;
    }, [state.positions, state.selectedMarketId]);

    // Compute derived position data (PnL, liq price, leverage, margin ratio)
    const positionDerived = useMemo(() => {
        if (!selectedMarket || !currentPosition || currentPosition.positionBase === 0) {
            return null;
        }

        const posBase = toBigInt(currentPosition.positionBase);
        const entryE8 = toBigInt(currentPosition.entryPriceE8);
        const indexE8 = toBigInt(selectedMarket.indexPriceE8);
        const collateral = toBigInt(currentPosition.collateralQuote);
        const maintBps = toBigInt(selectedMarket.maintenanceMarginBps);
        const depegBps = toBigInt(selectedMarket.depegBufferBps);

        const unrealizedPnl = pnlQuote(posBase, indexE8, entryE8);
        const liqPrice = liquidationPriceE8(posBase, collateral, indexE8, maintBps, depegBps);
        const leverage = effectiveLeverage(posBase, indexE8, collateral);
        const mRatio = marginRatio(posBase, indexE8, collateral, maintBps, depegBps);

        return {
            unrealizedPnl: Number(unrealizedPnl),
            unrealizedPnlE8: unrealizedPnl,
            liquidationPriceE8: liqPrice,
            liquidationPrice: liqPrice != null ? e8ToNumber(liqPrice) : null,
            leverage,
            marginRatio: mRatio,
            side: currentPosition.positionBase > 0 ? 'long' : 'short',
        };
    }, [selectedMarket, currentPosition]);

    // Submit a trader action.
    // - In demo mode: route through the in-memory demo state machine (unchanged).
    // - In live mode: translate into the stream-8 wallet action, prepare the
    //   exact Tau operation bundle, sign in the browser only for local testnet,
    //   then submit the externally signed payload. Production must use an
    //   external signer and never sends raw private keys to the backend.
    const submitAction = useCallback(async (request) => {
        if (!writeEnabled) {
            const error = !demoMode && !perpsWalletEnabled
                ? 'perps_route_quarantined'
                : 'perps_preview_only';
            dispatch({ type: ACTIONS.SET_ERROR, payload: error });
            return { ok: false, error };
        }
        const callerPubkey = pubkeyRef.current;
        const actionLabel = request.label || request.walletAction || 'perps_action';
        const txId = createLocalTxId('perp');
        const txHash = createLocalTxHash();
        onTransaction?.({
            id: txId,
            status: 'pending',
            product: 'perps',
            title: actionTitle(actionLabel, request.marketId),
            marketId: request.marketId || '',
            action: actionLabel,
            txHash,
            network: 'Tau Net Alpha',
            createdAt: Date.now(),
        });
        try {
            let result;
            if (demoMode) {
                result = applyDemoAction(
                    request.demoEndpoint,
                    request.demoBody || {},
                    stateRef.current,
                    callerPubkey,
                );
            } else {
                const deadline = request.deadline ?? defaultPerpsDeadline();
                const body = {
                    action: request.walletAction,
                    market_id: request.marketId,
                    chain_id: runtimeConfig.chainId || 'zeno-ledger-localtest-v0',
                    deadline,
                    account_pubkey: pubkey,
                    ...(request.walletExtra || {}),
                };
                let submitBody = null;
                if (request.signedTauTxPayload) {
                    submitBody = { ...body, signed_tau_tx_payload: request.signedTauTxPayload };
                } else if (walletPrivkey && !browserHotSigningAllowed) {
                    result = { ok: false, error: 'production_browser_hot_key_disabled' };
                } else {
                    const prepared = await apiPreparePerpsWallet(body, { timeoutMs: 8000 });
                    if (prepared?.ok === false) {
                        result = { ok: false, error: prepared.error || 'prepare_failed' };
                    } else if (browserHotSigningAllowed) {
                        const signedTauTxPayload = await buildSignedTauTransaction({
                            privkey: walletPrivkey,
                            sequence_number: prepared?.transport?.tx_sequence_number,
                            expiration_time: deadline,
                            operations: prepared?.report?.operations,
                            fee_limit: prepared?.transport?.tx_fee_limit ?? '0',
                        });
                        submitBody = { ...body, signed_tau_tx_payload: signedTauTxPayload };
                    } else if (externalTauSigner) {
                        const signedTauTxPayload = await externalTauSigner({
                            chainId: prepared?.transport?.chain_id || body.chain_id,
                            senderPubkey: prepared?.transport?.tx_sender_pubkey,
                            sender_pubkey: prepared?.transport?.tx_sender_pubkey,
                            sequenceNumber: prepared?.transport?.tx_sequence_number,
                            sequence_number: prepared?.transport?.tx_sequence_number,
                            expirationTime: deadline,
                            expiration_time: deadline,
                            operations: prepared?.report?.operations,
                            feeLimit: prepared?.transport?.tx_fee_limit ?? '0',
                            fee_limit: prepared?.transport?.tx_fee_limit ?? '0',
                            prepared,
                        });
                        if (!signedTauTxPayload || typeof signedTauTxPayload !== 'object') {
                            result = { ok: false, error: 'external_signer_returned_invalid_payload' };
                        } else {
                            submitBody = { ...body, signed_tau_tx_payload: signedTauTxPayload };
                        }
                    } else {
                        result = {
                            ok: false,
                            error: 'external_signer_required',
                            prepared,
                        };
                    }
                }
                const resp = submitBody
                    ? await apiSubmitPerpsWallet(submitBody, { timeoutMs: 8000 })
                    : null;
                if (resp?.ok === false) {
                    result = { ok: false, error: resp.error || 'submit_failed' };
                } else if (resp) {
                    result = {
                        ok: true,
                        txHash: resp?.tx_hash || resp?.receipt?.tx_hash || null,
                        receipt: resp?.receipt || null,
                        rawResponse: resp,
                    };
                }
            }
            if (pubkeyRef.current !== callerPubkey) return result;
            if (result.ok) {
                dispatch({ type: ACTIONS.SET_ERROR, payload: null });
                if (result.position && request.marketId) {
                    dispatch({
                        type: ACTIONS.UPDATE_POSITION,
                        payload: { marketId: request.marketId, data: result.position },
                    });
                }
                if (result.market) {
                    dispatch({ type: ACTIONS.UPDATE_MARKET, payload: result.market });
                }
                dispatch({
                    type: ACTIONS.APPEND_HISTORY,
                    payload: {
                        id: `local-${Date.now()}`,
                        timestamp: Date.now(),
                        market: request.marketId || '',
                        action: actionLabel,
                        side: null,
                        amount: request.amount ?? request.newPositionBase ?? null,
                        status: 'confirmed',
                    },
                });
                onTransaction?.({
                    id: txId,
                    status: 'confirmed',
                    txHash: result.txHash || txHash,
                    updatedAt: Date.now(),
                });
                // In live mode, refresh from authoritative state so subsequent
                // reads reflect what the Tau node now thinks.
                if (!demoMode) {
                    // Fire and forget — loadMarkets re-derives positions too.
                    loadMarketsRef.current?.();
                }
            } else if (result.error) {
                dispatch({ type: ACTIONS.SET_ERROR, payload: result.error });
                onTransaction?.({
                    id: txId,
                    status: 'failed',
                    error: String(result.error),
                    updatedAt: Date.now(),
                });
            }
            return result;
        } catch (err) {
            if (pubkeyRef.current !== callerPubkey) return { ok: false, error: 'stale' };
            dispatch({ type: ACTIONS.SET_ERROR, payload: err.message });
            onTransaction?.({
                id: txId,
                status: 'failed',
                error: err.message,
                updatedAt: Date.now(),
            });
            return { ok: false, error: err.message };
        }
    }, [
        browserHotSigningAllowed,
        demoMode,
        externalTauSigner,
        onTransaction,
        perpsWalletEnabled,
        pubkey,
        runtimeConfig.chainId,
        walletPrivkey,
        writeEnabled,
    ]);

    const depositCollateral = useCallback((marketId, amount) => {
        return submitAction({
            marketId,
            label: 'deposit_collateral',
            walletAction: 'deposit_collateral',
            walletExtra: { amount: Number(amount) },
            amount,
            // Demo fallback (in-memory path) keeps the original endpoint shape.
            demoEndpoint: '/api/perps/collateral',
            demoBody: { marketId, pubkey, action: 'deposit', amount },
        });
    }, [submitAction, pubkey]);

    const withdrawCollateral = useCallback((marketId, amount) => {
        return submitAction({
            marketId,
            label: 'withdraw_collateral',
            walletAction: 'withdraw_collateral',
            walletExtra: { amount: Number(amount) },
            amount,
            demoEndpoint: '/api/perps/collateral',
            demoBody: { marketId, pubkey, action: 'withdraw', amount },
        });
    }, [submitAction, pubkey]);

    // setPosition: translate "long N at Mx" / "short N at Mx" into the
    // stream-8 set_position_pair primitive. The trader UI calls this with
    // newPositionBase (signed: positive = long, negative = short). The
    // 2p market expects an explicit (position_a, position_b) pair; the
    // caller's account_a/b role determines which side the input applies to.
    const setPosition = useCallback((marketId, newPositionBase) => {
        const market = stateRef.current.markets.find((m) => m.id === marketId);
        const u = String(pubkey || '').toLowerCase().replace(/^0x/, '');
        const a = String(market?.accountAPubkey || '').toLowerCase().replace(/^0x/, '');
        const b = String(market?.accountBPubkey || '').toLowerCase().replace(/^0x/, '');
        let positionA = Number(market?.positionBaseA ?? 0);
        let positionB = Number(market?.positionBaseB ?? 0);
        if (u && u === a) {
            positionA = Number(newPositionBase);
            positionB = -positionA; // 2p invariant: a + b = 0
        } else if (u && u === b) {
            positionB = Number(newPositionBase);
            positionA = -positionB;
        } else {
            return Promise.resolve({
                ok: false,
                error: 'wallet_not_party_to_market',
            });
        }
        return submitAction({
            marketId,
            label: 'set_position_pair',
            walletAction: 'set_position_pair',
            walletExtra: {
                account_a_pubkey: market?.accountAPubkey,
                account_b_pubkey: market?.accountBPubkey,
                new_position_base_a: positionA,
                new_position_base_b: positionB,
            },
            newPositionBase,
            demoEndpoint: '/api/perps/position',
            demoBody: { marketId, pubkey, newPositionBase },
        });
    }, [submitAction, pubkey]);

    const depositInsurance = useCallback((marketId, amount) => {
        const market = stateRef.current.markets.find((m) => m.id === marketId);
        if (!demoMode && market?.kind !== 'isolated_v2') {
            const error = 'insurance_deposit_requires_isolated_market';
            dispatch({ type: ACTIONS.SET_ERROR, payload: error });
            return Promise.resolve({ ok: false, error });
        }
        return submitAction({
            marketId,
            label: 'deposit_insurance',
            walletAction: 'deposit_insurance',
            walletExtra: { amount: Number(amount) },
            amount,
            demoEndpoint: '/api/perps/insurance',
            demoBody: { marketId, pubkey, amount },
        });
    }, [demoMode, submitAction, pubkey]);

    const value = useMemo(() => ({
        ...state,
        selectedMarket,
        currentPosition,
        positionDerived,
        writeEnabled,
        writeLockReason,
        perpsWalletEnabled,
        perpsPreviewWritesRequested,
        loadMarkets,
        selectMarket,
        depositCollateral,
        withdrawCollateral,
        setPosition,
        depositInsurance,
    }), [state, selectedMarket, currentPosition, positionDerived, writeEnabled, writeLockReason, perpsWalletEnabled, perpsPreviewWritesRequested, loadMarkets, selectMarket, depositCollateral, withdrawCollateral, setPosition, depositInsurance]);

    return (
        <PerpContext.Provider value={value}>
            {children}
        </PerpContext.Provider>
    );
}
