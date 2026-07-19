import { useState, useCallback, useEffect, useMemo } from 'react';
import { formatNumber } from '../lib/cpmm';
import { apiAddLiquidity, apiCreateLiquidityPool, apiGetPools, apiRemoveLiquidity, getRuntimeConfig } from '../lib/api.js';
import { compactAssetLabel, displaySymbolForAsset, isCanonicalAssetId, isCompactAssetLabel } from '../lib/swapData.js';
import { buildAndSignCreatePoolIntent, buildAndSignLiquidityIntent } from '../sdk/dexIntentSigner.js';
import AddLiquidityModal from './AddLiquidityModal';
import RemoveLiquidityModal from './RemoveLiquidityModal';
import './PoolDashboard.css';

const NA = 'N/A';

const TOKEN_ICONS = {
    ZDEX: '\u26a1',
    zUSD: '\u25c8',
    ZUSD: '\u25c8',
};

function safeFiniteNumber(value) {
    const n = Number(value);
    return Number.isFinite(n) ? n : null;
}

function tokenFromSymbol(symbol) {
    const normalized = String(symbol || '').trim();
    const display = displaySymbolForAsset(normalized);
    const upper = display.toUpperCase();
    return {
        symbol: display || NA,
        name: display || NA,
        icon: isCanonicalAssetId(normalized) || isCompactAssetLabel(display)
            ? '#'
            : TOKEN_ICONS[upper] || display.slice(0, 2).toUpperCase() || '?',
    };
}

function normalizeLivePool(row) {
    const token0 = tokenFromSymbol(row?.token0 || row?.asset0);
    const token1 = tokenFromSymbol(row?.token1 || row?.asset1);
    const lpSupply = safeFiniteNumber(row?.lpSupply ?? row?.lp_supply);
    const reserve0 = safeFiniteNumber(row?.reserve0);
    const reserve1 = safeFiniteNumber(row?.reserve1);
    const myLp = safeFiniteNumber(row?.accountLpBalance ?? row?.account_lp_balance);
    const reserveDepth = reserve0 == null || reserve1 == null ? null : reserve0 + reserve1;
    const accountShare = myLp != null && lpSupply != null && lpSupply > 0 ? myLp / lpSupply : null;
    const inputVolume0 = safeFiniteNumber(row?.inputVolume0_24h ?? row?.input_volume0_24h);
    const inputVolume1 = safeFiniteNumber(row?.inputVolume1_24h ?? row?.input_volume1_24h);
    const fee0 = safeFiniteNumber(row?.fee0_24h ?? row?.fee0_24h_units ?? row?.fee0_24hUnits);
    const fee1 = safeFiniteNumber(row?.fee1_24h ?? row?.fee1_24h_units ?? row?.fee1_24hUnits);
    const hasVolume = inputVolume0 != null || inputVolume1 != null;
    const hasFees = fee0 != null || fee1 != null;
    return {
        id: String(row?.poolId || row?.pool_id || row?.id || `${token0.symbol}-${token1.symbol}`),
        poolId: String(row?.poolId || row?.pool_id || row?.id || ''),
        asset0: String(row?.asset0 || ''),
        asset1: String(row?.asset1 || ''),
        token0,
        token1,
        reserve0,
        reserve1,
        reserveDepth,
        feeBps: safeFiniteNumber(row?.feeBps ?? row?.fee_bps),
        // No default: if the live feed omits the curve, we do NOT assume CPMM —
        // an unknown curve must not earn a "verified cpmm" chip (see isPoolVerified).
        curveTag: (row?.curve_tag ?? row?.curveTag) ? String(row.curve_tag ?? row.curveTag).toUpperCase() : '',
        lpSupply,
        totalLpSupply: lpSupply,
        tvl: null,
        volume24h: hasVolume ? (inputVolume0 || 0) + (inputVolume1 || 0) : null,
        inputVolume0_24h: inputVolume0,
        inputVolume1_24h: inputVolume1,
        fees24h: hasFees ? (fee0 || 0) + (fee1 || 0) : null,
        fee0_24h: fee0,
        fee1_24h: fee1,
        swapCount24h: safeFiniteNumber(row?.swapCount24h ?? row?.swap_count_24h),
        apy: null,
        myLp,
        accountShare,
        accountBalance0: safeFiniteNumber(row?.accountBalance0 ?? row?.account_balance0),
        accountBalance1: safeFiniteNumber(row?.accountBalance1 ?? row?.account_balance1),
        source: 'live',
        status: String(row?.status || ''),
    };
}

function formatOptionalNumber(value, { prefix = '', suffix = '', decimals = 6 } = {}) {
    if (value == null) return NA;
    return `${prefix}${formatNumber(value, decimals)}${suffix}`;
}

function formatSharePercent(value) {
    if (value == null) return NA;
    return `${(value * 100).toFixed(value > 0 && value < 0.0001 ? 6 : 4)}%`;
}

function formatReserves(pool) {
    if (pool.reserve0 == null || pool.reserve1 == null) return NA;
    return `${formatNumber(pool.reserve0)} ${pool.token0.symbol} / ${formatNumber(pool.reserve1)} ${pool.token1.symbol}`;
}

function formatPoolActivity(pool) {
    if (pool.volume24h == null && pool.swapCount24h == null) return NA;
    const swapText = pool.swapCount24h == null ? '' : ` (${formatNumber(pool.swapCount24h, 0)} swaps)`;
    return `${formatNumber(pool.volume24h || 0)} input units${swapText}`;
}

function formatPoolFees(pool) {
    if (pool.fees24h == null) return NA;
    return `${formatNumber(pool.fees24h)} fee units`;
}

// Curve families the settlement engine actually dispatches (amm_dispatch.py).
const KNOWN_CURVES = new Set(['CPMM', 'CUBIC_SUM_V1', 'SUM_BOOST_V1', 'QUARTIC_BLEND_V1', 'QUINTIC_BLEND_V1']);

// Short, honest label for a pool's actual curve (e.g. 'cpmm', 'cubic_sum').
function poolCurveLabel(pool) {
    const tag = String(pool?.curveTag || '').toUpperCase();
    if (!tag) return 'unknown curve';
    return tag.replace(/_V\d+$/, '').toLowerCase();
}

// A pool is "spec-verified" when it is routed through a curve the engine
// recognizes AND is in a well-formed, active state: real reserves + a bounded
// fee, status ACTIVE (or empty = the feed's default active state). FROZEN /
// DISABLED / malformed / unknown-curve pools are NOT counted. The chip names
// the ACTUAL curve (poolCurveLabel) — it never asserts a curve it didn't check
// or a spec version that does not exist.
function isPoolVerified(pool) {
    const status = String(pool?.status || '').toUpperCase();
    const statusOk = status === '' || status === 'ACTIVE';
    return pool?.reserve0 != null && pool?.reserve1 != null
        && pool?.feeBps != null && pool.feeBps <= 10000
        && statusOk
        && KNOWN_CURVES.has(String(pool?.curveTag || '').toUpperCase());
}

// Reserve-0 share of total reserves (for the composition bar). Null when reserves
// are unavailable; this is a pool-balance visual, not a price.
function poolCompositionShare(pool) {
    if (pool?.reserve0 == null || pool?.reserve1 == null) return null;
    const total = pool.reserve0 + pool.reserve1;
    if (!(total > 0)) return null;
    return pool.reserve0 / total;
}

function wholeAmount(value, name, { allowZero = false } = {}) {
    const n = Number(value);
    if (!Number.isFinite(n)) {
        throw new Error(`${name}_must_be_a_number`);
    }
    const amount = Math.floor(n);
    if (allowZero ? amount < 0 : amount <= 0) {
        throw new Error(`${name}_must_be_positive_whole_units`);
    }
    return amount;
}

function feeBpsAmount(value) {
    const amount = wholeAmount(value, 'fee_bps', { allowZero: true });
    if (amount > 10000) {
        throw new Error('fee_bps_must_be_at_most_10000');
    }
    return amount;
}

function deadlineOneHour() {
    return Math.floor(Date.now() / 1000) + 3600;
}

const LIQUIDITY_BACKOFF_MS = [250, 750, 1500];

function delayMs(ms) {
    return new Promise((resolve) => {
        window.setTimeout(resolve, ms);
    });
}

function errorMessage(err) {
    return String(err?.message || err || '');
}

function isTransientLiquidityError(err) {
    const msg = errorMessage(err).toLowerCase();
    return [
        'timeout',
        'failed to fetch',
        'network',
        'http_429',
        'http_502',
        'http_503',
        'http_504',
        'sendtx_retry_failed',
        'createblock',
        'mempool empty',
        'gateway',
        'service unavailable',
        'upstream',
    ].some((needle) => msg.includes(needle));
}

function findPoolById(rows, poolId) {
    const target = String(poolId || '');
    return rows.find((row) => String(row?.poolId || row?.pool_id || row?.id || '') === target) || rows[0] || null;
}

function poolLpBalance(pool) {
    return safeFiniteNumber(pool?.accountLpBalance ?? pool?.account_lp_balance ?? pool?.myLp) ?? 0;
}

async function probeLiquidityLanding({ account, poolId, nonce, beforeLpBalance, direction }) {
    let payload = null;
    try {
        payload = await apiGetPools({ timeoutMs: 5000, account });
    } catch {
        return { landed: false, ambiguous: false, payload: null, pool: null };
    }
    const rows = Array.isArray(payload?.pools) ? payload.pools : [];
    const pool = findPoolById(rows, poolId);
    const lastNonce = safeFiniteNumber(payload?.account_last_nonce);
    if (lastNonce == null || lastNonce < nonce || !pool) {
        return { landed: false, ambiguous: false, payload, pool };
    }
    const afterLpBalance = poolLpBalance(pool);
    if (direction === 'add' && afterLpBalance > beforeLpBalance) {
        return { landed: true, ambiguous: false, payload, pool };
    }
    if (direction === 'remove' && afterLpBalance < beforeLpBalance) {
        return { landed: true, ambiguous: false, payload, pool };
    }
    return { landed: false, ambiguous: true, payload, pool };
}

function walletForPool(wallet, pool) {
    if (!wallet) return null;
    return {
        ...wallet,
        balance: {
            ...(wallet.balance || {}),
            [pool.token0.symbol]: pool.accountBalance0 ?? wallet.balance?.[pool.token0.symbol] ?? 0,
            [pool.token1.symbol]: pool.accountBalance1 ?? wallet.balance?.[pool.token1.symbol] ?? 0,
        },
    };
}

function dexIntentSignerForWallet(wallet) {
    return wallet?.signDexIntentForEngine || wallet?.signDexIntent || null;
}

function canSignDexIntent(wallet) {
    return Boolean(dexIntentSignerForWallet(wallet));
}

function PoolDashboard({ wallet }) {
    const runtimeConfig = getRuntimeConfig();
    const [livePools, setLivePools] = useState([]);
    const [liveTokens, setLiveTokens] = useState([]);
    const [liveSource, setLiveSource] = useState('');
    const [poolError, setPoolError] = useState('');
    const [actionMessage, setActionMessage] = useState('');
    const [actionError, setActionError] = useState('');
    const [actionBusy, setActionBusy] = useState('');
    const [loadingPools, setLoadingPools] = useState(false);
    const [addPool, setAddPool] = useState(null);
    const [removePool, setRemovePool] = useState(null);
    const [poolSearch, setPoolSearch] = useState('');
    const [poolSort, setPoolSort] = useState({ key: 'reserveDepth', dir: 'desc' });
    const [accountLastNonce, setAccountLastNonce] = useState(null);
    const [createForm, setCreateForm] = useState({
        asset0: '',
        asset1: '',
        amount0: '2000',
        amount1: '2000',
        feeBps: '30',
    });
    const runtimeChainId = String(runtimeConfig.chainId || wallet?.chainId || '').trim();
    const walletDexSigner = dexIntentSignerForWallet(wallet);
    const walletCanSignDexIntent = canSignDexIntent(wallet);

    const loadLivePools = useCallback(async ({ showLoading = true } = {}) => {
        if (showLoading) setLoadingPools(true);
        try {
            const payload = await apiGetPools({ timeoutMs: 5000, account: wallet?.address || '' });
            const rows = Array.isArray(payload?.pools) ? payload.pools : [];
            setLivePools(rows.map(normalizeLivePool));
            setLiveTokens(Array.isArray(payload?.tokens) ? payload.tokens : []);
            setAccountLastNonce(safeFiniteNumber(payload?.account_last_nonce));
            setLiveSource(String(payload?.source || payload?.schema || 'live node'));
            setPoolError('');
        } catch (err) {
            setLivePools([]);
            setLiveTokens([]);
            setAccountLastNonce(null);
            setLiveSource('');
            setPoolError(err?.message || 'pool_feed_unavailable');
        } finally {
            if (showLoading) {
                setLoadingPools(false);
            }
        }
    }, [wallet?.address]);

    useEffect(() => {
        let cancelled = false;
        void loadLivePools().then(() => {
            if (cancelled) return;
        });
        return () => {
            cancelled = true;
        };
    }, [loadLivePools]);

    const pools = livePools;

    // PulseX/Uniswap-Info-style search + sort over the pools table. Sort keys are
    // limited to fields the node actually reports (reserves, LP, fee, volume) —
    // no fabricated USD TVL/APR. Default: deepest reserves first.
    const SORTABLE = {
        pair: (p) => `${p.token0.symbol}/${p.token1.symbol}`.toLowerCase(),
        reserveDepth: (p) => p.reserveDepth ?? -1,
        lpSupply: (p) => p.lpSupply ?? -1,
        feeBps: (p) => p.feeBps ?? -1,
        volume24h: (p) => p.volume24h ?? -1,
    };
    const displayPools = useMemo(() => {
        const q = poolSearch.trim().toLowerCase();
        const filtered = q
            ? pools.filter((p) => `${p.token0.symbol} ${p.token1.symbol}`.toLowerCase().includes(q)
                || String(p.poolId || p.id || '').toLowerCase().includes(q))
            : pools;
        const accessor = SORTABLE[poolSort.key] || SORTABLE.reserveDepth;
        const dir = poolSort.dir === 'asc' ? 1 : -1;
        return [...filtered].sort((a, b) => {
            const av = accessor(a);
            const bv = accessor(b);
            if (typeof av === 'string' || typeof bv === 'string') return String(av).localeCompare(String(bv)) * dir;
            return (av - bv) * dir;
        });
    // eslint-disable-next-line react-hooks/exhaustive-deps
    }, [pools, poolSearch, poolSort]);
    const toggleSort = useCallback((key) => {
        setPoolSort((prev) => prev.key === key
            ? { key, dir: prev.dir === 'asc' ? 'desc' : 'asc' }
            : { key, dir: key === 'pair' ? 'asc' : 'desc' });
    }, []);
    const sortIndicator = (key) => (poolSort.key === key ? (poolSort.dir === 'asc' ? ' ▲' : ' ▼') : '');

    const tokenOptions = useMemo(() => {
        const rows = Array.isArray(liveTokens) ? liveTokens : [];
        return rows
            .filter((row) => row && typeof row === 'object' && typeof row.asset_id === 'string')
            .map((row) => ({
                symbol: String(row.symbol || '').trim(),
                assetId: String(row.asset_id || '').trim(),
            }))
            .filter((row) => row.symbol && row.assetId)
            .sort((a, b) => a.symbol.localeCompare(b.symbol));
    }, [liveTokens]);
    const sourceLabel = liveSource ? `Live node: ${liveSource}` : 'Live node';

    const handleAddSubmit = useCallback(async (data) => {
        setActionError('');
        setActionMessage('');
        if (!wallet?.address) {
            setActionError('connect_wallet_first');
            return;
        }
        if (!walletCanSignDexIntent) {
            setActionError('wallet_signature_unavailable');
            return;
        }
        const poolId = data.pool.poolId || data.pool.id;
        setActionBusy(`add:${poolId}`);
        try {
            const amount0Desired = wholeAmount(data.amount0, 'amount0');
            const amount1Desired = wholeAmount(data.amount1, 'amount1');
            const maxAttempts = LIQUIDITY_BACKOFF_MS.length + 1;
            for (let attempt = 0; attempt < maxAttempts; attempt += 1) {
                let basePayload = null;
                let beforeLpBalance = 0;
                try {
                    const fresh = await apiGetPools({ timeoutMs: 5000, account: wallet.address });
                    const freshRows = Array.isArray(fresh?.pools) ? fresh.pools : [];
                    const freshPool = findPoolById(freshRows, poolId);
                    if (!freshPool) throw new Error('matching_pool_not_found');
                    beforeLpBalance = poolLpBalance(freshPool);
                    const now = Date.now();
                    basePayload = {
                        poolId,
                        asset0: freshPool.asset0 || data.pool.asset0,
                        asset1: freshPool.asset1 || data.pool.asset1,
                        amount0Desired,
                        amount1Desired,
                        amount0Min: 0,
                        amount1Min: 0,
                        senderPubkey: wallet.address,
                        recipient: wallet.address,
                        deadline: deadlineOneHour(),
                        nonce: (safeFiniteNumber(fresh?.account_last_nonce) ?? accountLastNonce ?? 0) + 1,
                        timeMs: now,
                        txId: `ui-add-liquidity-${poolId}-${now}-${attempt}`,
                    };
                    const signed = await buildAndSignLiquidityIntent({
                        kind: 'ADD_LIQUIDITY',
                        pool: freshPool,
                        payload: basePayload,
                        signDexIntent: walletDexSigner,
                        chainId: runtimeChainId,
                    });
                    const report = await apiAddLiquidity(
                        { ...basePayload, signature: signed.signature },
                        { timeoutMs: 10000 },
                    );
                    if (report?.tx_accepted !== true) {
                        throw new Error(report?.error || 'add_liquidity_rejected');
                    }
                    setActionMessage(`Liquidity added at height ${report.height}`);
                    await loadLivePools({ showLoading: false });
                    return;
                } catch (err) {
                    if (!basePayload || !isTransientLiquidityError(err) || attempt >= maxAttempts - 1) {
                        throw err;
                    }
                    const probe = await probeLiquidityLanding({
                        account: wallet.address,
                        poolId,
                        nonce: basePayload.nonce,
                        beforeLpBalance,
                        direction: 'add',
                    });
                    if (probe.landed) {
                        setActionMessage('Liquidity added after retry probe confirmed the signed nonce landed');
                        await loadLivePools({ showLoading: false });
                        return;
                    }
                    if (probe.ambiguous) {
                        throw new Error('add_liquidity_status_ambiguous_after_transient_failure');
                    }
                    setActionMessage(`Retrying add liquidity (${attempt + 2}/${maxAttempts})...`);
                    await delayMs(LIQUIDITY_BACKOFF_MS[attempt]);
                }
            }
        } catch (err) {
            setActionError(err?.message || 'add_liquidity_failed');
        } finally {
            setActionBusy('');
        }
    }, [accountLastNonce, loadLivePools, runtimeChainId, wallet?.address, walletCanSignDexIntent, walletDexSigner]);

    const handleRemoveSubmit = useCallback(async (data) => {
        setActionError('');
        setActionMessage('');
        if (!wallet?.address) {
            setActionError('connect_wallet_first');
            return;
        }
        if (!walletCanSignDexIntent) {
            setActionError('wallet_signature_unavailable');
            return;
        }
        const poolId = data.pool.poolId || data.pool.id;
        setActionBusy(`remove:${poolId}`);
        try {
            const lpAmount = wholeAmount(data.lpAmount, 'lp_amount');
            const amount0Min = wholeAmount(data.minAmount0 || 0, 'amount0_min', { allowZero: true });
            const amount1Min = wholeAmount(data.minAmount1 || 0, 'amount1_min', { allowZero: true });
            const maxAttempts = LIQUIDITY_BACKOFF_MS.length + 1;
            for (let attempt = 0; attempt < maxAttempts; attempt += 1) {
                let basePayload = null;
                let beforeLpBalance = 0;
                try {
                    const fresh = await apiGetPools({ timeoutMs: 5000, account: wallet.address });
                    const freshRows = Array.isArray(fresh?.pools) ? fresh.pools : [];
                    const freshPool = findPoolById(freshRows, poolId);
                    if (!freshPool) throw new Error('matching_pool_not_found');
                    beforeLpBalance = poolLpBalance(freshPool);
                    const now = Date.now();
                    basePayload = {
                        poolId,
                        lpAmount,
                        amount0Min,
                        amount1Min,
                        senderPubkey: wallet.address,
                        recipient: wallet.address,
                        deadline: deadlineOneHour(),
                        nonce: (safeFiniteNumber(fresh?.account_last_nonce) ?? accountLastNonce ?? 0) + 1,
                        timeMs: now,
                        txId: `ui-remove-liquidity-${poolId}-${now}-${attempt}`,
                    };
                    const signed = await buildAndSignLiquidityIntent({
                        kind: 'REMOVE_LIQUIDITY',
                        pool: freshPool,
                        payload: basePayload,
                        signDexIntent: walletDexSigner,
                        chainId: runtimeChainId,
                    });
                    const report = await apiRemoveLiquidity(
                        { ...basePayload, signature: signed.signature },
                        { timeoutMs: 10000 },
                    );
                    if (report?.tx_accepted !== true) {
                        throw new Error(report?.error || 'remove_liquidity_rejected');
                    }
                    setActionMessage(`Liquidity removed at height ${report.height}`);
                    await loadLivePools({ showLoading: false });
                    return;
                } catch (err) {
                    if (!basePayload || !isTransientLiquidityError(err) || attempt >= maxAttempts - 1) {
                        throw err;
                    }
                    const probe = await probeLiquidityLanding({
                        account: wallet.address,
                        poolId,
                        nonce: basePayload.nonce,
                        beforeLpBalance,
                        direction: 'remove',
                    });
                    if (probe.landed) {
                        setActionMessage('Liquidity removed after retry probe confirmed the signed nonce landed');
                        await loadLivePools({ showLoading: false });
                        return;
                    }
                    if (probe.ambiguous) {
                        throw new Error('remove_liquidity_status_ambiguous_after_transient_failure');
                    }
                    setActionMessage(`Retrying remove liquidity (${attempt + 2}/${maxAttempts})...`);
                    await delayMs(LIQUIDITY_BACKOFF_MS[attempt]);
                }
            }
        } catch (err) {
            setActionError(err?.message || 'remove_liquidity_failed');
        } finally {
            setActionBusy('');
        }
    }, [accountLastNonce, loadLivePools, runtimeChainId, wallet?.address, walletCanSignDexIntent, walletDexSigner]);

    const resolveCreateAsset = useCallback((value, name) => {
        const text = String(value || '').trim();
        if (!text) {
            throw new Error(`${name}_is_required`);
        }
        const known = tokenOptions.find((token) => token.symbol.toUpperCase() === text.toUpperCase());
        if (known) {
            return known.assetId;
        }
        if (isCanonicalAssetId(text)) {
            return `0x${text.replace(/^0x/i, '').toLowerCase()}`;
        }
        throw new Error(`${name}_must_be_known_symbol_or_32_byte_asset_id`);
    }, [tokenOptions]);

    const handleCreatePool = useCallback(async (event) => {
        event.preventDefault();
        setActionError('');
        setActionMessage('');
        if (!wallet?.address) {
            setActionError('connect_wallet_first');
            return;
        }
        if (!walletCanSignDexIntent) {
            setActionError('wallet_signature_unavailable');
            return;
        }
        setActionBusy('create:pool');
        try {
            const rawAsset0 = resolveCreateAsset(createForm.asset0, 'asset0');
            const rawAsset1 = resolveCreateAsset(createForm.asset1, 'asset1');
            if (rawAsset0 === rawAsset1) {
                throw new Error('assets_must_differ');
            }
            const amount0 = wholeAmount(createForm.amount0, 'amount0');
            const amount1 = wholeAmount(createForm.amount1, 'amount1');
            const feeBps = feeBpsAmount(createForm.feeBps);
            const now = Date.now();
            const fresh = await apiGetPools({ timeoutMs: 5000, account: wallet.address });
            const basePayload = {
                asset0: rawAsset0,
                asset1: rawAsset1,
                amount0,
                amount1,
                feeBps,
                senderPubkey: wallet.address,
                deadline: deadlineOneHour(),
                nonce: (safeFiniteNumber(fresh?.account_last_nonce) ?? accountLastNonce ?? 0) + 1,
                createdAt: Math.floor((now + 2) / 1000),
                timeMs: now + 2,
                txId: `ui-create-pool-${now}`,
            };
            const signed = await buildAndSignCreatePoolIntent({
                payload: basePayload,
                signDexIntent: walletDexSigner,
                chainId: runtimeChainId,
            });
            const report = await apiCreateLiquidityPool(
                { ...basePayload, signature: signed.signature },
                { timeoutMs: 10000 },
            );
            if (report?.tx_accepted !== true) {
                throw new Error(report?.error || 'create_pool_rejected');
            }
            setActionMessage(`Created pool at height ${report.height}`);
            // The read node indexes the new pool a beat after the write commits,
            // so a single immediate refetch can miss it. Retry with backoff until
            // the pool count grows (new pool landed), then stop.
            const preCount = livePools.length;
            let landed = false;
            for (const backoff of LIQUIDITY_BACKOFF_MS) {
                await delayMs(backoff);
                try {
                    const refreshed = await apiGetPools({ timeoutMs: 5000, account: wallet.address });
                    const rows = Array.isArray(refreshed?.pools) ? refreshed.pools : [];
                    setLivePools(rows.map(normalizeLivePool));
                    setLiveTokens(Array.isArray(refreshed?.tokens) ? refreshed.tokens : []);
                    setAccountLastNonce(safeFiniteNumber(refreshed?.account_last_nonce));
                    if (rows.length > preCount) { landed = true; break; }
                } catch {
                    // keep retrying within the backoff window
                }
            }
            if (!landed) await loadLivePools({ showLoading: false });
        } catch (err) {
            setActionError(err?.message || 'create_pool_failed');
        } finally {
            setActionBusy('');
        }
    }, [accountLastNonce, createForm, livePools.length, loadLivePools, resolveCreateAsset, runtimeChainId, wallet?.address, walletCanSignDexIntent, walletDexSigner]);

    const totals = useMemo(() => {
        const totalReserves = pools.reduce((sum, pool) => sum + (pool.reserveDepth || 0), 0);
        const volumePools = pools.filter((pool) => pool.volume24h != null);
        const feePools = pools.filter((pool) => pool.fees24h != null);
        return {
            totalTvl: totalReserves > 0 ? totalReserves : null,
            totalVol: volumePools.length > 0 ? volumePools.reduce((sum, pool) => sum + (pool.volume24h || 0), 0) : null,
            totalFees: feePools.length > 0 ? feePools.reduce((sum, pool) => sum + (pool.fees24h || 0), 0) : null,
            activePools: pools.filter((pool) => pool.status === 'ACTIVE' || pool.status === '').length,
            verifiedPools: pools.filter(isPoolVerified).length,
            poolCount: pools.length,
        };
    }, [pools]);

    const canOpenLiquidityModals = pools.length > 0 && Boolean(wallet?.address);
    const addModalWallet = addPool ? walletForPool(wallet, addPool) : wallet;
    const removeModalWallet = removePool ? walletForPool(wallet, removePool) : wallet;

    return (
        <div className="pool-dashboard">
            <div className="pool-header">
                <div>
                    <h2>Liquidity Pools</h2>
                    <p className="pool-source-line">{sourceLabel}</p>
                </div>
                <button
                    className="btn btn-primary"
                    onClick={() => canOpenLiquidityModals && setAddPool(pools[0])}
                    disabled={!canOpenLiquidityModals}
                    title={wallet?.address ? 'Add liquidity to a pool' : 'Connect a wallet to add liquidity'}
                >
                    Add Liquidity
                </button>
            </div>

            {poolError && (
                <div className="pool-honesty-banner" role="status">
                    Pool feed unavailable: {poolError}
                </div>
            )}

            {actionError && (
                <div className="pool-honesty-banner" role="status">
                    Liquidity action failed: {actionError}
                </div>
            )}

            {actionMessage && !actionError && (
                <div className="pool-honesty-banner pool-honesty-info" role="status">
                    {actionMessage}
                </div>
            )}

            {!poolError && (
                <div className="pool-honesty-banner pool-honesty-info" role="status">
                    <strong>Live mode.</strong> Add/remove liquidity posts to the writer through nginx token injection.
                    Reserves, LP supply, wallet balances, account LP, recent swap counts, input units, and fee units
                    are live ledger-derived fields. Price-indexed TVL and APY show <em>N/A</em> until price and reward
                    indexers exist.
                </div>
            )}

            <form className="pool-create-panel panel" onSubmit={handleCreatePool}>
                    <div className="pool-create-heading">
                        <div>
                            <h3>Create Pool</h3>
                            <p>Use a listed symbol or a canonical 32-byte asset ID.</p>
                        </div>
                    </div>
                    <datalist id="pool-token-options">
                        {tokenOptions.map((token) => (
                            <option key={token.assetId} value={token.symbol}>
                                {compactAssetLabel(token.assetId)}
                            </option>
                        ))}
                    </datalist>
                    <div className="pool-create-grid">
                        <label>
                            <span>Asset A</span>
                            <input
                                value={createForm.asset0}
                                onChange={(event) => setCreateForm((prev) => ({ ...prev, asset0: event.target.value }))}
                                list="pool-token-options"
                                autoComplete="off"
                            />
                        </label>
                        <label>
                            <span>Amount A</span>
                            <input
                                value={createForm.amount0}
                                onChange={(event) => setCreateForm((prev) => ({ ...prev, amount0: event.target.value }))}
                                inputMode="numeric"
                            />
                        </label>
                        <label>
                            <span>Asset B</span>
                            <input
                                value={createForm.asset1}
                                onChange={(event) => setCreateForm((prev) => ({ ...prev, asset1: event.target.value }))}
                                list="pool-token-options"
                                autoComplete="off"
                            />
                        </label>
                        <label>
                            <span>Amount B</span>
                            <input
                                value={createForm.amount1}
                                onChange={(event) => setCreateForm((prev) => ({ ...prev, amount1: event.target.value }))}
                                inputMode="numeric"
                            />
                        </label>
                        <label>
                            <span>Fee bps</span>
                            <input
                                value={createForm.feeBps}
                                onChange={(event) => setCreateForm((prev) => ({ ...prev, feeBps: event.target.value }))}
                                inputMode="numeric"
                            />
                        </label>
                        <button
                            className="btn btn-primary"
                            type="submit"
                            disabled={!wallet?.address || !walletCanSignDexIntent || Boolean(actionBusy)}
                            title={wallet?.address ? 'Create a signed live pool' : 'Connect a wallet with signing capability'}
                        >
                            Create Pool
                        </button>
                    </div>
            </form>

            <div className="pool-stats grid grid-4">
                <div className="stat panel animate-slide-up" style={{ animationDelay: '0ms' }}>
                    <span className="stat-label">Reserve Units</span>
                    <span className="stat-value">{formatOptionalNumber(totals.totalTvl)}</span>
                </div>
                <div className="stat panel animate-slide-up" style={{ animationDelay: '50ms' }}>
                    <span className="stat-label">Input Units</span>
                    <span className="stat-value">{formatOptionalNumber(totals.totalVol)}</span>
                </div>
                <div className="stat panel animate-slide-up" style={{ animationDelay: '100ms' }}>
                    <span className="stat-label">Fee Units</span>
                    <span className="stat-value">{formatOptionalNumber(totals.totalFees)}</span>
                </div>
                <div className="stat panel animate-slide-up pool-stat-verified" style={{ animationDelay: '150ms' }}>
                    <span className="stat-label">Verified pools</span>
                    <span className="stat-value">{loadingPools ? NA : `${totals.verifiedPools}/${totals.poolCount}`}</span>
                    <span className="pool-stat-sub">recognized curve · active</span>
                </div>
            </div>

            <div className="pool-table panel">
                <div className="pool-table-toolbar">
                    <input
                        className="input pool-search"
                        type="search"
                        placeholder="Search pools by live asset or pool ID"
                        value={poolSearch}
                        onChange={(e) => setPoolSearch(e.target.value)}
                        aria-label="Search pools by token"
                    />
                    <span className="pool-table-count">
                        {poolSearch ? `${displayPools.length} of ${pools.length}` : `${pools.length}`} pools
                    </span>
                </div>
                <table>
                    <thead>
                        <tr>
                            <th className="pool-th-sort" onClick={() => toggleSort('pair')}>Pool{sortIndicator('pair')}</th>
                            <th className="pool-th-sort" onClick={() => toggleSort('reserveDepth')}>Reserves{sortIndicator('reserveDepth')}</th>
                            <th className="pool-th-sort" onClick={() => toggleSort('lpSupply')}>LP Supply{sortIndicator('lpSupply')}</th>
                            <th className="pool-th-sort" onClick={() => toggleSort('feeBps')}>Fee{sortIndicator('feeBps')}</th>
                            <th className="pool-th-sort" onClick={() => toggleSort('volume24h')}>
                                Recent Activity{sortIndicator('volume24h')}
                            </th>
                            <th>Recent Fees</th>
                            <th>My Position</th>
                            <th></th>
                        </tr>
                    </thead>
                    <tbody>
                        {loadingPools && pools.length === 0 ? (
                            <tr>
                                <td colSpan={8} className="pool-empty-cell">Loading live pool feed...</td>
                            </tr>
                        ) : null}
                        {!loadingPools && pools.length === 0 ? (
                            <tr>
                                <td colSpan={8} className="pool-empty-cell">No live pools reported.</td>
                            </tr>
                        ) : null}
                        {!loadingPools && pools.length > 0 && displayPools.length === 0 ? (
                            <tr>
                                <td colSpan={8} className="pool-empty-cell">No pools match &ldquo;{poolSearch}&rdquo;.</td>
                            </tr>
                        ) : null}
                        {displayPools.map((pool, i) => (
                            <tr key={pool.id} className="animate-slide-up" style={{ animationDelay: `${i * 50}ms` }}>
                                <td>
                                    <div className="pool-pair">
                                        <div className="pool-icons">
                                            <span>{pool.token0.icon}</span>
                                            <span>{pool.token1.icon}</span>
                                        </div>
                                        <div className="pool-pair-meta">
                                            <span className="pool-name">{pool.token0.symbol} / {pool.token1.symbol}</span>
                                            {(() => {
                                                const verified = isPoolVerified(pool);
                                                const curve = poolCurveLabel(pool);
                                                return (
                                                    <span
                                                        className={`pool-verify ${verified ? 'is-verified' : 'is-unverified'}`}
                                                        title={verified
                                                            ? `Settles through the ${curve} curve on the Tau node — active and well-formed.`
                                                            : 'Not spec-verified: missing reserves/fee, an unknown curve, or a non-active status.'}
                                                    >
                                                        <span className="pool-verify-dot" aria-hidden="true" />
                                                        {verified ? curve : 'unverified'}
                                                    </span>
                                                );
                                            })()}
                                        </div>
                                    </div>
                                </td>
                                <td>
                                    <div className="pool-reserves-cell">
                                        <span>{formatReserves(pool)}</span>
                                        {(() => {
                                            const share = poolCompositionShare(pool);
                                            if (share == null) return null;
                                            const pctIn = Math.max(3, Math.min(97, share * 100));
                                            return (
                                                <div
                                                    className="pool-comp-bar"
                                                    title={`Reserve balance: ${(share * 100).toFixed(1)}% ${pool.token0.symbol} / ${(100 - share * 100).toFixed(1)}% ${pool.token1.symbol}`}
                                                >
                                                    <span className="pool-comp-in" style={{ width: `${pctIn}%` }} />
                                                    <span className="pool-comp-out" style={{ width: `${100 - pctIn}%` }} />
                                                </div>
                                            );
                                        })()}
                                    </div>
                                </td>
                                <td>{formatOptionalNumber(pool.lpSupply)}</td>
                                <td>{pool.feeBps == null ? NA : `${pool.feeBps} bps`}</td>
                                <td>{formatPoolActivity(pool)}</td>
                                <td>{formatPoolFees(pool)}</td>
                                <td>
                                    {pool.myLp != null && pool.myLp > 0 ? (
                                        <span className="pool-position">
                                            <span>{formatNumber(pool.myLp)} LP</span>
                                            <span>{formatSharePercent(pool.accountShare)}</span>
                                        </span>
                                    ) : (
                                        <span className="no-position">{NA}</span>
                                    )}
                                </td>
                                <td>
                                    <div className="pool-actions">
                                        <>
                                            <button
                                                className="btn btn-secondary"
                                                onClick={() => setAddPool(pool)}
                                                disabled={!wallet?.address || Boolean(actionBusy)}
                                                title={wallet?.address ? 'Add liquidity' : 'Connect a wallet first'}
                                            >
                                                Add
                                            </button>
                                            {(pool.myLp || 0) > 0 && (
                                                <button
                                                    className="btn btn-secondary"
                                                    onClick={() => setRemovePool(pool)}
                                                    disabled={!wallet?.address || Boolean(actionBusy)}
                                                >
                                                    Remove
                                                </button>
                                            )}
                                        </>
                                    </div>
                                </td>
                            </tr>
                        ))}
                    </tbody>
                </table>
            </div>

            <div className="pool-footer">
                <p>
                    Live mode shows on-chain pool and account fields exposed by /api/pools. Recent activity is derived
                    from accepted state-changing swap bodies and receipts over the ledger timestamp window.
                </p>
            </div>

            {addPool && (
                <AddLiquidityModal
                    pool={addPool}
                    wallet={addModalWallet}
                    onClose={() => setAddPool(null)}
                    onSubmit={handleAddSubmit}
                />
            )}

            {removePool && (
                <RemoveLiquidityModal
                    pool={removePool}
                    wallet={removeModalWallet}
                    lpBalance={removePool.myLp || 0}
                    onClose={() => setRemovePool(null)}
                    onSubmit={handleRemoveSubmit}
                />
            )}
        </div>
    );
}

export default PoolDashboard;
