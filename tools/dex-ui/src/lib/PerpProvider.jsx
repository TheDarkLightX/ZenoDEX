import { useReducer, useCallback, useEffect, useLayoutEffect, useMemo, useRef } from 'react';
import { useDemoMode } from './DemoModeContext.jsx';
import { PerpContext } from './PerpContext.jsx';
import { PERP_DEMO_MARKETS, PERP_DEMO_POSITIONS, PERP_DEMO_HISTORY } from './perpMockData.js';
import { apiFetchJson } from './api.js';
import {
    toBigInt,
    pnlQuote,
    liquidationPriceE8,
    effectiveLeverage,
    marginRatio,
    e8ToNumber,
} from './perpMath.js';

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

function actionLabelFromRequest(endpoint, body) {
    return body.action
        || (endpoint.includes('/position') ? 'set_position'
        : endpoint.includes('/insurance') ? 'deposit_insurance'
        : 'trade');
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
    const pubkey = wallet?.address ?? null;
    // Monotonic request counter to discard responses from stale loadMarkets calls.
    const loadSeqRef = useRef(0);
    const marketDetailSeqRef = useRef(0);
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
            } else {
                const data = await apiFetchJson('/api/perps/markets');
                if (seq !== loadSeqRef.current) return; // stale
                const summaries = data.markets || [];
                dispatch({ type: ACTIONS.SET_MARKETS, payload: summaries });

                // Fetch full details for the currently selected market only
                // (summary already contains guard/math fields; detail is for richer panels).
                const selectedId = stateRef.current.selectedMarketId || (summaries[0]?.id ?? null);
                if (selectedId) {
                    try {
                        const detail = await apiFetchJson(`/api/perps/markets/${encodeURIComponent(selectedId)}`);
                        if (seq !== loadSeqRef.current) return; // stale
                        if (detail?.market) {
                            dispatch({ type: ACTIONS.UPDATE_MARKET, payload: detail.market });
                        }
                    } catch {
                        // Ignore detail fetch failure; UI can run on summary data.
                    }
                }

                // Fetch positions per-market for connected wallet.
                if (pubkey) {
                    try {
                        const posData = await apiFetchJson(`/api/perps/positions/${encodeURIComponent(pubkey)}`);
                        if (seq !== loadSeqRef.current) return; // stale
                        if (posData?.positions && typeof posData.positions === 'object') {
                            dispatch({ type: ACTIONS.SET_POSITIONS, payload: posData.positions });
                        }
                    } catch {
                        // Positions may not exist yet (or endpoint unavailable).
                    }

                    // Fetch and normalize history.
                    try {
                        const histData = await apiFetchJson(`/api/perps/history/${encodeURIComponent(pubkey)}`);
                        if (seq !== loadSeqRef.current) return; // stale
                        const raw = histData.history || [];
                        const normalized = raw.map((entry, i) => ({
                            id: entry.id || `htx-${i}`,
                            timestamp: (entry.ts || 0) * 1000, // seconds → ms
                            market: entry.marketId || entry.market || '',
                            action: entry.action || '',
                            side: entry.detail?.side ?? entry.side ?? null,
                            sizeAfter: entry.detail?.sizeAfter ?? entry.sizeAfter ?? null,
                            amount: entry.detail?.amount ?? entry.detail?.newPositionBase ?? entry.amount ?? null,
                            priceE8: entry.detail?.priceE8 ?? entry.priceE8 ?? null,
                            status: entry.status || 'confirmed',
                        }));
                        dispatch({ type: ACTIONS.SET_HISTORY, payload: normalized });
                    } catch {
                        // History may not exist yet.
                    }
                }
            }
            if (seq === loadSeqRef.current) {
                dispatch({ type: ACTIONS.SET_ERROR, payload: null });
            }
        } catch (err) {
            if (seq !== loadSeqRef.current) return; // stale
            dispatch({ type: ACTIONS.SET_ERROR, payload: err.message });
        }
    }, [demoMode, pubkey]);

    // Select a market
    const selectMarket = useCallback((marketId) => {
        dispatch({ type: ACTIONS.SELECT_MARKET, payload: marketId });
    }, []);

    // Keep full market detail fresh for the selected market (avoid N+1 detail fetches).
    useEffect(() => {
        if (demoMode) return;
        if (!state.selectedMarketId) return;
        const seq = ++marketDetailSeqRef.current;
        const marketId = state.selectedMarketId;
        (async () => {
            try {
                const detail = await apiFetchJson(`/api/perps/markets/${encodeURIComponent(marketId)}`);
                if (seq !== marketDetailSeqRef.current) return;
                if (detail?.market) {
                    dispatch({ type: ACTIONS.UPDATE_MARKET, payload: detail.market });
                }
            } catch {
                // Ignore detail refresh failure.
            }
        })();
    }, [demoMode, state.selectedMarketId]);

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

    // Submit actions (collateral, position).
    // On success, update local state so the UI reflects the change immediately.
    // Guards against stale dispatches if the wallet changed mid-flight.
    const submitAction = useCallback(async (endpoint, body) => {
        const callerPubkey = pubkeyRef.current;
        const actionLabel = actionLabelFromRequest(endpoint, body);
        const txId = createLocalTxId('perp');
        const txHash = createLocalTxHash();
        onTransaction?.({
            id: txId,
            status: 'pending',
            product: 'perps',
            title: actionTitle(actionLabel, body.marketId),
            marketId: body.marketId || '',
            action: actionLabel,
            txHash,
            network: 'Tau Net Alpha',
            createdAt: Date.now(),
        });
        try {
            const result = demoMode
                ? applyDemoAction(endpoint, body, stateRef.current, callerPubkey)
                : await apiFetchJson(endpoint, {
                    method: 'POST',
                    body: JSON.stringify(body),
                });
            // Discard if wallet changed while the request was in-flight.
            if (pubkeyRef.current !== callerPubkey) return result;
            // Apply server-returned position/market updates to local state.
            if (result.ok) {
                dispatch({ type: ACTIONS.SET_ERROR, payload: null });
                if (result.position && body.marketId) {
                    dispatch({
                        type: ACTIONS.UPDATE_POSITION,
                        payload: { marketId: body.marketId, data: result.position },
                    });
                }
                if (result.market) {
                    dispatch({ type: ACTIONS.UPDATE_MARKET, payload: result.market });
                }
                // Append a local history entry so the trade list updates immediately.
                dispatch({
                    type: ACTIONS.APPEND_HISTORY,
                    payload: {
                        id: `local-${Date.now()}`,
                        timestamp: Date.now(),
                        market: body.marketId || '',
                        action: actionLabel,
                        side: null,
                        amount: body.amount ?? body.newPositionBase ?? null,
                        status: 'confirmed',
                    },
                });
                onTransaction?.({
                    id: txId,
                    status: 'confirmed',
                    txHash: result.txHash || txHash,
                    updatedAt: Date.now(),
                });
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
    }, [demoMode, onTransaction]);

    const depositCollateral = useCallback((marketId, amount) => {
        return submitAction('/api/perps/collateral', {
            marketId,
            pubkey,
            action: 'deposit',
            amount,
        });
    }, [submitAction, pubkey]);

    const withdrawCollateral = useCallback((marketId, amount) => {
        return submitAction('/api/perps/collateral', {
            marketId,
            pubkey,
            action: 'withdraw',
            amount,
        });
    }, [submitAction, pubkey]);

    const setPosition = useCallback((marketId, newPositionBase) => {
        return submitAction('/api/perps/position', {
            marketId,
            pubkey,
            newPositionBase,
        });
    }, [submitAction, pubkey]);

    const depositInsurance = useCallback((marketId, amount) => {
        return submitAction('/api/perps/insurance', {
            marketId,
            pubkey,
            amount,
        });
    }, [submitAction, pubkey]);

    const value = useMemo(() => ({
        ...state,
        selectedMarket,
        currentPosition,
        positionDerived,
        loadMarkets,
        selectMarket,
        depositCollateral,
        withdrawCollateral,
        setPosition,
        depositInsurance,
    }), [state, selectedMarket, currentPosition, positionDerived, loadMarkets, selectMarket, depositCollateral, withdrawCollateral, setPosition, depositInsurance]);

    return (
        <PerpContext.Provider value={value}>
            {children}
        </PerpContext.Provider>
    );
}
