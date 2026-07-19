import { useReducer, useCallback, useLayoutEffect, useMemo, useRef } from 'react';
import { PerpContext } from './PerpContext.jsx';
import {
    getRuntimeConfig,
    apiGetPerpsWalletStatus,
    apiPreparePerpsWallet,
    apiSubmitPerpsWallet,
} from './api.js';
import {
    toBigInt,
    pnlQuote,
    liquidationPriceE8,
    effectiveLeverage,
    marginRatio,
    e8ToNumber,
} from './perpMath.js';
import {
    deriveWalletPosition,
    hasAuthoritativePositionDerivationFacts,
    marketWriteReadinessError,
    normalizeWalletMarkets,
    SUPPORTED_PERP_MARKET_KIND,
} from './perpLiveState.js';

/**
 * PerpContext - Shared state for the perpetuals trading interface.
 *
 * Uses useReducer for predictable state transitions.
 * Uses the Tau-node-backed wallet status as its authoritative source.
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

function createClientTxId(prefix = 'perp') {
    const salt = Math.random().toString(16).slice(2, 10);
    return `${prefix}-${Date.now()}-${salt}`;
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

function reducer(state, action) {
    switch (action.type) {
        case ACTIONS.SET_MARKETS:
            return {
                ...state,
                markets: action.payload,
                selectedMarketId: action.payload.some((market) => market.id === state.selectedMarketId)
                    ? state.selectedMarketId
                    : (action.payload[0]?.id ?? null),
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
    const [state, dispatch] = useReducer(reducer, initialState);
    const runtimeConfig = getRuntimeConfig();
    const pubkey = wallet?.address ?? null;
    const externalTauSigner = externalTauSignerFromWallet(wallet);
    // Forward ref so submitAction can refresh state after a live action
    // without forming a circular useCallback dependency.
    const loadMarketsRef = useRef(null);
    // Monotonic request counter to discard responses from stale loadMarkets calls.
    const loadSeqRef = useRef(0);
    // Track current pubkey for stale-action detection in submitAction.
    const pubkeyRef = useRef(pubkey);
    // Snapshot latest reducer state for synchronous market-role calculations.
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
            // The wallet endpoint is the authoritative source. Missing fields
            // stay unknown; unsupported market kinds never enter trader state.
            const statusResp = await apiGetPerpsWalletStatus({ timeoutMs: 12000 });
            if (seq !== loadSeqRef.current) return; // stale
            const status = statusResp?.status || {};
            const rawMarkets = Array.isArray(status.markets) ? status.markets : [];
            const normalized = normalizeWalletMarkets(rawMarkets);
            dispatch({ type: ACTIONS.SET_MARKETS, payload: normalized.markets });

            const supportedIds = new Set(normalized.markets.map((market) => market.id));
            const positions = {};
            if (pubkey) {
                for (const rawMarket of rawMarkets) {
                    const marketId = String(rawMarket?.market_id ?? rawMarket?.id ?? '');
                    if (!supportedIds.has(marketId)) continue;
                    const position = deriveWalletPosition(rawMarket, pubkey);
                    if (position?.marketId) positions[position.marketId] = position;
                }
            }
            if (seq !== loadSeqRef.current) return; // stale
            dispatch({ type: ACTIONS.SET_POSITIONS, payload: positions });
            dispatch({ type: ACTIONS.SET_HISTORY, payload: [] });

            const nextError = status.node_reachable !== true
                ? (status.error || 'tau_node_unreachable')
                : (normalized.errors[0] || null);
            dispatch({ type: ACTIONS.SET_ERROR, payload: nextError });
        } catch (err) {
            if (seq !== loadSeqRef.current) return; // stale
            dispatch({ type: ACTIONS.SET_ERROR, payload: err.message });
        }
    }, [pubkey]);

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

    const selectedMarketWriteError = marketWriteReadinessError(selectedMarket);
    const writeEnabled = Boolean(pubkey && externalTauSigner && !selectedMarketWriteError);
    const writeLockReason = !pubkey
        ? 'Connect an externally signed wallet to submit perpetuals actions.'
        : !externalTauSigner
            ? 'Trader writes require an external signer bridge. The browser never receives private keys.'
            : selectedMarketWriteError
                ? `Writes locked: ${selectedMarketWriteError}`
                : '';

    // Compute derived position data (PnL, liq price, leverage, margin ratio)
    const positionDerived = useMemo(() => {
        if (!hasAuthoritativePositionDerivationFacts(selectedMarket, currentPosition)) {
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

    // Submit a trader action: translate into the stream-8 wallet action, prepare
    // the exact Tau operation bundle, obtain an external signature, then submit
    // the signed payload. The browser never receives raw private keys.
    const submitAction = useCallback(async (request) => {
        const callerPubkey = pubkeyRef.current;
        if (!callerPubkey) {
            const error = 'perps_wallet_required';
            dispatch({ type: ACTIONS.SET_ERROR, payload: error });
            return { ok: false, error };
        }
        if (!externalTauSigner) {
            const error = 'external_signer_required';
            dispatch({ type: ACTIONS.SET_ERROR, payload: error });
            return { ok: false, error };
        }
        const requestedMarket = stateRef.current.markets.find(
            (market) => market.id === request.marketId,
        );
        const readinessError = marketWriteReadinessError(requestedMarket);
        if (readinessError) {
            dispatch({ type: ACTIONS.SET_ERROR, payload: readinessError });
            return { ok: false, error: readinessError };
        }
        const actionLabel = request.label || request.walletAction || 'perps_action';
        const txId = createClientTxId('perp');
        onTransaction?.({
            id: txId,
            status: 'pending',
            product: 'perps',
            title: actionTitle(actionLabel, request.marketId),
            marketId: request.marketId || '',
            action: actionLabel,
            network: 'Tau Net Alpha',
            createdAt: Date.now(),
        });
        try {
            let result;
            const deadline = request.deadline ?? defaultPerpsDeadline();
                const chainId = String(runtimeConfig.chainId || '').trim();
                if (!chainId) {
                    throw new Error('chain_id_unavailable');
                }
                const body = {
                    action: request.walletAction,
                    market_id: request.marketId,
                    chain_id: chainId,
                    deadline,
                    account_pubkey: callerPubkey,
                    ...(request.walletExtra || {}),
                };
                let submitBody = null;
                if (request.signedTauTxPayload) {
                    submitBody = { ...body, signed_tau_tx_payload: request.signedTauTxPayload };
                } else {
                    const prepared = await apiPreparePerpsWallet(body, { timeoutMs: 8000 });
                    if (prepared?.ok === false) {
                        result = { ok: false, error: prepared.error || 'prepare_failed' };
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
            if (pubkeyRef.current !== callerPubkey) return result;
            if (result?.ok) {
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
                        id: `client-${Date.now()}`,
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
                    txHash: result.txHash || undefined,
                    updatedAt: Date.now(),
                });
                // Fire and forget — loadMarkets re-derives positions too.
                loadMarketsRef.current?.();
            } else if (result?.error) {
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
        externalTauSigner,
        onTransaction,
        runtimeConfig.chainId,
    ]);

    const depositCollateral = useCallback((marketId, amount) => {
        const parsedAmount = Number(amount);
        if (!Number.isSafeInteger(parsedAmount) || parsedAmount <= 0) {
            const error = 'perps_collateral_amount_must_be_positive_safe_integer';
            dispatch({ type: ACTIONS.SET_ERROR, payload: error });
            return Promise.resolve({ ok: false, error });
        }
        return submitAction({
            marketId,
            label: 'deposit_collateral',
            walletAction: 'deposit_collateral',
            walletExtra: { amount: parsedAmount },
            amount: parsedAmount,
        });
    }, [submitAction]);

    const withdrawCollateral = useCallback((marketId, amount) => {
        const parsedAmount = Number(amount);
        if (!Number.isSafeInteger(parsedAmount) || parsedAmount <= 0) {
            const error = 'perps_collateral_amount_must_be_positive_safe_integer';
            dispatch({ type: ACTIONS.SET_ERROR, payload: error });
            return Promise.resolve({ ok: false, error });
        }
        return submitAction({
            marketId,
            label: 'withdraw_collateral',
            walletAction: 'withdraw_collateral',
            walletExtra: { amount: parsedAmount },
            amount: parsedAmount,
        });
    }, [submitAction]);

    // setPosition: translate "long N at Mx" / "short N at Mx" into the
    // stream-8 set_position_pair primitive. The trader UI calls this with
    // newPositionBase (signed: positive = long, negative = short). The
    // 2p market expects an explicit (position_a, position_b) pair; the
    // caller's account_a/b role determines which side the input applies to.
    const setPosition = useCallback((marketId, newPositionBase) => {
        const market = stateRef.current.markets.find((m) => m.id === marketId);
        if (!market || market.kind !== SUPPORTED_PERP_MARKET_KIND) {
            const error = `unsupported_perps_market_kind:${marketId}:${market?.kind || 'unknown'}`;
            dispatch({ type: ACTIONS.SET_ERROR, payload: error });
            return Promise.resolve({ ok: false, error });
        }
        const targetPosition = Number(newPositionBase);
        if (!Number.isSafeInteger(targetPosition)) {
            const error = 'perps_position_must_be_safe_integer';
            dispatch({ type: ACTIONS.SET_ERROR, payload: error });
            return Promise.resolve({ ok: false, error });
        }
        const u = String(pubkeyRef.current || '').toLowerCase().replace(/^0x/, '');
        const a = String(market?.accountAPubkey || '').toLowerCase().replace(/^0x/, '');
        const b = String(market?.accountBPubkey || '').toLowerCase().replace(/^0x/, '');
        let positionA;
        let positionB;
        if (u && u === a) {
            positionA = targetPosition;
            positionB = -positionA; // 2p invariant: a + b = 0
        } else if (u && u === b) {
            positionB = targetPosition;
            positionA = -positionB;
        } else {
            const error = 'wallet_not_party_to_market';
            dispatch({ type: ACTIONS.SET_ERROR, payload: error });
            return Promise.resolve({ ok: false, error });
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
            newPositionBase: targetPosition,
        });
    }, [submitAction]);

    const depositInsurance = useCallback((marketId, amount) => {
        const market = stateRef.current.markets.find((m) => m.id === marketId);
        const error = `unsupported_perps_market_action:deposit_insurance:${market?.kind || 'unknown'}`;
        dispatch({ type: ACTIONS.SET_ERROR, payload: error });
        return Promise.resolve({ ok: false, error, amount });
    }, []);

    const value = useMemo(() => ({
        ...state,
        selectedMarket,
        currentPosition,
        positionDerived,
        writeEnabled,
        writeLockReason,
        perpsPreviewWritesRequested: false,
        loadMarkets,
        selectMarket,
        depositCollateral,
        withdrawCollateral,
        setPosition,
        depositInsurance,
    }), [state, selectedMarket, currentPosition, positionDerived, writeEnabled, writeLockReason, loadMarkets, selectMarket, depositCollateral, withdrawCollateral, setPosition, depositInsurance]);

    return (
        <PerpContext.Provider value={value}>
            {children}
        </PerpContext.Provider>
    );
}
