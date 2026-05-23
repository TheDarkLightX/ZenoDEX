import { useState, useCallback, useEffect, useMemo } from 'react';
import { formatNumber, formatPercent } from '../lib/cpmm';
import { apiGetPools } from '../lib/api.js';
import { useDemoMode } from '../lib/DemoModeContext.jsx';
import { DEMO_POOLS } from '../lib/mockData.js';
import AddLiquidityModal from './AddLiquidityModal';
import RemoveLiquidityModal from './RemoveLiquidityModal';
import './PoolDashboard.css';

const NA = 'N/A';

const TOKEN_ICONS = {
    ZDEX: '\u26a1',
    zUSD: '\u25c8',
    ZUSD: '\u25c8',
    TASSET0: 'T\u2080',
    TASSET1: 'T\u2081',
    TZENO: 'TZ',
};

function safeFiniteNumber(value) {
    const n = Number(value);
    return Number.isFinite(n) ? n : null;
}

function tokenFromSymbol(symbol) {
    const normalized = String(symbol || '').trim();
    const upper = normalized.toUpperCase();
    return {
        symbol: normalized || NA,
        name: normalized || NA,
        icon: TOKEN_ICONS[upper] || normalized.slice(0, 2).toUpperCase() || '?',
    };
}

function normalizeLivePool(row) {
    const token0 = tokenFromSymbol(row?.token0 || row?.asset0);
    const token1 = tokenFromSymbol(row?.token1 || row?.asset1);
    return {
        id: String(row?.poolId || row?.pool_id || row?.id || `${token0.symbol}-${token1.symbol}`),
        token0,
        token1,
        reserve0: safeFiniteNumber(row?.reserve0),
        reserve1: safeFiniteNumber(row?.reserve1),
        feeBps: safeFiniteNumber(row?.feeBps ?? row?.fee_bps),
        lpSupply: safeFiniteNumber(row?.lpSupply ?? row?.lp_supply),
        tvl: null,
        volume24h: null,
        apy: null,
        myLp: null,
        source: 'live',
        status: String(row?.status || ''),
    };
}

function normalizeFallbackPool(row) {
    return {
        id: String(row.id),
        token0: row.token0,
        token1: row.token1,
        reserve0: safeFiniteNumber(row.reserve0),
        reserve1: safeFiniteNumber(row.reserve1),
        feeBps: safeFiniteNumber(row.feeBps ?? 30),
        lpSupply: safeFiniteNumber(row.totalLpSupply),
        tvl: safeFiniteNumber(row.tvl),
        volume24h: safeFiniteNumber(row.volume24h),
        apy: safeFiniteNumber(row.apy),
        myLp: safeFiniteNumber(row.myLp),
        source: 'fallback',
        status: 'FALLBACK',
    };
}

function formatOptionalNumber(value, { prefix = '', suffix = '', decimals = 6 } = {}) {
    if (value == null) return NA;
    return `${prefix}${formatNumber(value, decimals)}${suffix}`;
}

function formatOptionalPercent(value) {
    if (value == null) return NA;
    return formatPercent(value);
}

function formatReserves(pool) {
    if (pool.reserve0 == null || pool.reserve1 == null) return NA;
    return `${formatNumber(pool.reserve0)} ${pool.token0.symbol} / ${formatNumber(pool.reserve1)} ${pool.token1.symbol}`;
}

function PoolDashboard({ wallet }) {
    const { demoMode } = useDemoMode();
    const [livePools, setLivePools] = useState([]);
    const [liveSource, setLiveSource] = useState('');
    const [poolError, setPoolError] = useState('');
    const [loadingPools, setLoadingPools] = useState(false);
    const [demoPools, setDemoPools] = useState(() => DEMO_POOLS.map(normalizeFallbackPool));
    const [addPool, setAddPool] = useState(null);
    const [removePool, setRemovePool] = useState(null);

    useEffect(() => {
        let cancelled = false;
        if (demoMode) {
            setPoolError('');
            setLivePools([]);
            setLiveSource('');
            setLoadingPools(false);
            return () => {
                cancelled = true;
            };
        }

        async function loadLivePools() {
            setLoadingPools(true);
            try {
                const payload = await apiGetPools({ timeoutMs: 5000 });
                if (cancelled) return;
                const rows = Array.isArray(payload?.pools) ? payload.pools : [];
                setLivePools(rows.map(normalizeLivePool));
                setLiveSource(String(payload?.source || payload?.schema || 'live node'));
                setPoolError('');
            } catch (err) {
                if (cancelled) return;
                setLivePools([]);
                setLiveSource('');
                setPoolError(err?.message || 'pool_feed_unavailable');
            } finally {
                if (!cancelled) {
                    setLoadingPools(false);
                }
            }
        }

        void loadLivePools();
        return () => {
            cancelled = true;
        };
    }, [demoMode]);

    const pools = demoMode ? demoPools : livePools;
    const sourceLabel = demoMode
        ? 'Local fallback pools'
        : liveSource
            ? `Live node: ${liveSource}`
            : 'Live node';

    const handleAddSubmit = useCallback((data) => {
        if (!demoMode) return;
        setDemoPools((prev) =>
            prev.map((p) =>
                p.id === data.pool.id
                    ? { ...p, myLp: (p.myLp || 0) + (data.lpTokensExpected || 0) }
                    : p
            )
        );
    }, [demoMode]);

    const handleRemoveSubmit = useCallback((data) => {
        if (!demoMode) return;
        setDemoPools((prev) =>
            prev.map((p) =>
                p.id === data.pool.id
                    ? { ...p, myLp: Math.max(0, (p.myLp || 0) - (data.lpAmount || 0)) }
                    : p
            )
        );
    }, [demoMode]);

    const totals = useMemo(() => {
        if (!demoMode) {
            return {
                totalTvl: null,
                totalVol: null,
                totalFees: null,
                activePools: pools.filter((pool) => pool.status === 'ACTIVE' || pool.status === '').length,
            };
        }
        const totalTvl = pools.reduce((s, p) => s + (p.tvl || 0), 0);
        const totalVol = pools.reduce((s, p) => s + (p.volume24h || 0), 0);
        return {
            totalTvl,
            totalVol,
            totalFees: Math.round(totalVol * 0.003),
            activePools: pools.length,
        };
    }, [demoMode, pools]);

    const canUseDemoLiquidityModals = demoMode && pools.length > 0;

    return (
        <div className="pool-dashboard">
            <div className="pool-header">
                <div>
                    <h2>Liquidity Pools</h2>
                    <p className="pool-source-line">{sourceLabel}</p>
                </div>
                <button
                    className="btn btn-primary"
                    onClick={() => canUseDemoLiquidityModals && setAddPool(pools[0])}
                    disabled={!canUseDemoLiquidityModals}
                    title={demoMode ? 'Add liquidity to fallback pool' : 'Live add-liquidity UI endpoint is not wired yet'}
                >
                    Add Liquidity
                </button>
            </div>

            {poolError && (
                <div className="pool-honesty-banner" role="status">
                    Pool feed unavailable: {poolError}
                </div>
            )}

            <div className="pool-stats grid grid-4">
                <div className="stat panel animate-slide-up" style={{ animationDelay: '0ms' }}>
                    <span className="stat-label">Total TVL</span>
                    <span className="stat-value">{formatOptionalNumber(totals.totalTvl, { prefix: '$' })}</span>
                </div>
                <div className="stat panel animate-slide-up" style={{ animationDelay: '50ms' }}>
                    <span className="stat-label">24h Volume</span>
                    <span className="stat-value">{formatOptionalNumber(totals.totalVol, { prefix: '$' })}</span>
                </div>
                <div className="stat panel animate-slide-up" style={{ animationDelay: '100ms' }}>
                    <span className="stat-label">24h Fees</span>
                    <span className="stat-value">{formatOptionalNumber(totals.totalFees, { prefix: '$' })}</span>
                </div>
                <div className="stat panel animate-slide-up" style={{ animationDelay: '150ms' }}>
                    <span className="stat-label">Active Pools</span>
                    <span className="stat-value">{loadingPools ? NA : totals.activePools}</span>
                </div>
            </div>

            <div className="pool-table panel">
                <table>
                    <thead>
                        <tr>
                            <th>Pool</th>
                            <th>Reserves</th>
                            <th>LP Supply</th>
                            <th>Fee</th>
                            <th>TVL</th>
                            <th>24h Volume</th>
                            <th>APY</th>
                            <th>My Position</th>
                            <th></th>
                        </tr>
                    </thead>
                    <tbody>
                        {loadingPools && pools.length === 0 ? (
                            <tr>
                                <td colSpan="9" className="pool-empty-cell">Loading live pool feed...</td>
                            </tr>
                        ) : null}
                        {!loadingPools && pools.length === 0 ? (
                            <tr>
                                <td colSpan="9" className="pool-empty-cell">No live pools reported.</td>
                            </tr>
                        ) : null}
                        {pools.map((pool, i) => (
                            <tr key={pool.id} className="animate-slide-up" style={{ animationDelay: `${i * 50}ms` }}>
                                <td>
                                    <div className="pool-pair">
                                        <div className="pool-icons">
                                            <span>{pool.token0.icon}</span>
                                            <span>{pool.token1.icon}</span>
                                        </div>
                                        <span className="pool-name">{pool.token0.symbol} / {pool.token1.symbol}</span>
                                    </div>
                                </td>
                                <td>{formatReserves(pool)}</td>
                                <td>{formatOptionalNumber(pool.lpSupply)}</td>
                                <td>{pool.feeBps == null ? NA : `${pool.feeBps} bps`}</td>
                                <td>{formatOptionalNumber(pool.tvl, { prefix: '$' })}</td>
                                <td>{formatOptionalNumber(pool.volume24h, { prefix: '$' })}</td>
                                <td className={pool.apy == null ? 'pool-na-cell' : 'apy-cell'}>{formatOptionalPercent(pool.apy)}</td>
                                <td>
                                    {pool.myLp != null && pool.myLp > 0 ? (
                                        <span>{formatNumber(pool.myLp)} LP</span>
                                    ) : (
                                        <span className="no-position">{NA}</span>
                                    )}
                                </td>
                                <td>
                                    <div className="pool-actions">
                                        {demoMode ? (
                                            <>
                                                <button
                                                    className="btn btn-secondary"
                                                    onClick={() => setAddPool(pool)}
                                                >
                                                    Add
                                                </button>
                                                {pool.myLp > 0 && (
                                                    <button
                                                        className="btn btn-secondary"
                                                        onClick={() => setRemovePool(pool)}
                                                    >
                                                        Remove
                                                    </button>
                                                )}
                                            </>
                                        ) : (
                                            <span className="pool-action-unavailable">Not wired</span>
                                        )}
                                    </div>
                                </td>
                            </tr>
                        ))}
                    </tbody>
                </table>
            </div>

            <div className="pool-footer">
                <p>
                    Live mode shows only fields exposed by /api/pools. Price-indexed TVL, APY,
                    24h volume, and account LP balances remain N/A until the indexer endpoints exist.
                </p>
            </div>

            {addPool && demoMode && (
                <AddLiquidityModal
                    pool={addPool}
                    wallet={wallet}
                    onClose={() => setAddPool(null)}
                    onSubmit={handleAddSubmit}
                />
            )}

            {removePool && demoMode && (
                <RemoveLiquidityModal
                    pool={removePool}
                    wallet={wallet}
                    lpBalance={removePool.myLp || 0}
                    onClose={() => setRemovePool(null)}
                    onSubmit={handleRemoveSubmit}
                />
            )}
        </div>
    );
}

export default PoolDashboard;
