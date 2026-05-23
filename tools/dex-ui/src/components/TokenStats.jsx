import { useMemo } from 'react';
import { formatNumber, formatPercent } from '../lib/cpmm';
import { useDemoMode } from '../lib/DemoModeContext.jsx';
import { FALLBACK_BURN_HISTORY as DEMO_BURN_HISTORY, FALLBACK_ZDEX_STATS as DEMO_ZDEX_STATS } from '../lib/mockData.js';
import './TokenStats.css';

const INITIAL_SUPPLY = 1_000_000;
const MIN_SUPPLY = 100_000;
const BURN_RATE = 0.005;
const NA = 'N/A';

function finiteOrNull(value) {
    const n = Number(value);
    return Number.isFinite(n) ? n : null;
}

function formatValueOrNA(value) {
    if (value == null) return NA;
    return formatNumber(value);
}

function formatDollarOrNA(value) {
    if (value == null) return NA;
    return `$${formatNumber(value)}`;
}

function TokenStats() {
    const { demoMode } = useDemoMode();

    const demoCurrentSupply = finiteOrNull(DEMO_ZDEX_STATS?.currentSupply);
    const demoBurnedTotal = finiteOrNull(DEMO_ZDEX_STATS?.burnedTotal);
    const demoBuybackPool = finiteOrNull(DEMO_ZDEX_STATS?.buybackPool);
    const demoDailyVolume = finiteOrNull(DEMO_ZDEX_STATS?.dailyVolume);

    const currentSupply = demoMode ? demoCurrentSupply : null;
    const burnedTotal = demoMode ? demoBurnedTotal : null;
    const buybackPool = demoMode ? demoBuybackPool : null;
    const dailyVolume = demoMode ? demoDailyVolume : null;

    const stats = useMemo(() => {
        if (
            currentSupply == null
            || burnedTotal == null
            || buybackPool == null
            || dailyVolume == null
        ) {
            return {
                burnedPercent: null,
                remainingToBurn: null,
                daysToFloor: null,
                buybackPending: null,
                dailyBurnRate: null,
            };
        }
        const burnedPercent = burnedTotal / INITIAL_SUPPLY;
        const remainingToBurn = currentSupply - MIN_SUPPLY;
        const denominator = (dailyVolume * 0.003 * 0.5) + ((dailyVolume * 0.2) * BURN_RATE);
        const daysToFloor = denominator > 0 ? Math.round(remainingToBurn / denominator) : null;
        return {
            burnedPercent,
            remainingToBurn,
            daysToFloor,
            buybackPending: buybackPool,
            dailyBurnRate: dailyVolume * 0.003 * 0.5,
        };
    }, [currentSupply, burnedTotal, buybackPool, dailyVolume]);

    const burnHistory = demoMode ? DEMO_BURN_HISTORY : [];

    return (
        <div className="token-stats">
            <div className="stats-header">
                <h2>
                    <span className="zdex-logo-inline">Z</span>
                    ZDEX Token Analytics
                </h2>
                <div className="live-badge">
                    <span className="live-dot"></span>
                    {demoMode ? 'Local fallback' : 'Live data unavailable'}
                </div>
            </div>

            <div className="stats-grid grid grid-4">
                <div className="stat-card panel animate-slide-up" style={{ animationDelay: '0ms' }}>
                    <span className="stat-label">Current Supply</span>
                    <span className="stat-value">{formatValueOrNA(currentSupply)}</span>
                    <span className="stat-sub">of {formatNumber(INITIAL_SUPPLY)} initial</span>
                </div>
                <div className="stat-card panel animate-slide-up" style={{ animationDelay: '50ms' }}>
                    <span className="stat-label">Total Burned</span>
                    <span className="stat-value stat-burned">{formatValueOrNA(burnedTotal)}</span>
                    <span className="stat-sub">{stats.burnedPercent == null ? NA : `${formatPercent(stats.burnedPercent)} of initial`}</span>
                </div>
                <div className="stat-card panel animate-slide-up" style={{ animationDelay: '100ms' }}>
                    <span className="stat-label">Buyback Pool</span>
                    <span className="stat-value stat-pool">{formatDollarOrNA(buybackPool)}</span>
                    <span className="stat-sub">pending for burn</span>
                </div>
                <div className="stat-card panel animate-slide-up" style={{ animationDelay: '150ms' }}>
                    <span className="stat-label">Est. Days to Floor</span>
                    <span className="stat-value">{stats.daysToFloor == null ? NA : stats.daysToFloor}</span>
                    <span className="stat-sub">{demoMode ? 'at current volume' : 'requires live indexer feed'}</span>
                </div>
            </div>

            <div className="supply-progress panel animate-slide-up" style={{ animationDelay: '200ms' }}>
                <div className="progress-header">
                    <span>Supply Progression</span>
                    <span>
                        {currentSupply == null ? NA : formatNumber(currentSupply)}
                        {' -> '}{formatNumber(MIN_SUPPLY)} floor
                    </span>
                </div>
                {currentSupply == null || burnedTotal == null ? (
                    <p className="model-note">Live ZDEX supply metrics are not wired yet.</p>
                ) : (
                    <>
                        <div className="progress-bar-container">
                            <div
                                className="progress-bar burned"
                                style={{ width: `${(burnedTotal / INITIAL_SUPPLY) * 100}%` }}
                            ></div>
                            <div
                                className="progress-bar remaining"
                                style={{ width: `${((currentSupply - MIN_SUPPLY) / INITIAL_SUPPLY) * 100}%` }}
                            ></div>
                            <div
                                className="progress-bar floor"
                                style={{ width: `${(MIN_SUPPLY / INITIAL_SUPPLY) * 100}%` }}
                            ></div>
                        </div>
                        <div className="progress-legend">
                            <span><span className="legend-dot burned"></span> Burned ({formatPercent(burnedTotal / INITIAL_SUPPLY)})</span>
                            <span><span className="legend-dot remaining"></span> Burnable ({formatPercent((currentSupply - MIN_SUPPLY) / INITIAL_SUPPLY)})</span>
                            <span><span className="legend-dot floor"></span> Floor ({formatPercent(MIN_SUPPLY / INITIAL_SUPPLY)})</span>
                        </div>
                    </>
                )}
            </div>

            <div className="burn-mechanics grid grid-2">
                <div className="panel animate-slide-up" style={{ animationDelay: '250ms' }}>
                    <h3>Burn Mechanics</h3>
                    <div className="mechanic-list">
                        <div className="mechanic-item">
                            <span className="mechanic-label">Transfer Burn Rate</span>
                            <span className="mechanic-value">{formatPercent(BURN_RATE)}</span>
                        </div>
                        <div className="mechanic-item">
                            <span className="mechanic-label">Swap Buyback Rate</span>
                            <span className="mechanic-value">0.3%</span>
                        </div>
                        <div className="mechanic-item">
                            <span className="mechanic-label">Buyback to Burn</span>
                            <span className="mechanic-value">50%</span>
                        </div>
                        <div className="mechanic-item">
                            <span className="mechanic-label">Supply Floor</span>
                            <span className="mechanic-value">{formatNumber(MIN_SUPPLY)} ZDEX</span>
                        </div>
                    </div>
                </div>

                <div className="panel animate-slide-up" style={{ animationDelay: '300ms' }}>
                    <h3>Zeno Supply Model</h3>
                    <p className="model-desc">
                        ZDEX targets a decreasing supply that asymptotically approaches a floor.
                        Live values appear here once the supply indexer is wired.
                    </p>
                    <div className="formula">
                        <code>S(n) = S0 x (1 - p)^n</code>
                    </div>
                    <p className="model-note">
                        where p = 0.5% per transfer and n = number of transfers
                    </p>
                </div>
            </div>

            <div className="burn-chart panel animate-slide-up" style={{ animationDelay: '350ms' }}>
                <h3>Supply Over Time</h3>
                {burnHistory.length === 0 ? (
                    <p className="model-note">Live burn history is not wired yet.</p>
                ) : (
                    <div className="chart-container">
                        <div className="chart-y-axis">
                            <span>{formatNumber(INITIAL_SUPPLY)}</span>
                            <span>{formatNumber(MIN_SUPPLY)}</span>
                        </div>
                        <div className="chart-area">
                            {burnHistory.map((point, i) => (
                                <div
                                    key={point.day}
                                    className="chart-bar"
                                    style={{
                                        height: `${(point.supply / INITIAL_SUPPLY) * 100}%`,
                                        animationDelay: `${400 + i * 50}ms`,
                                    }}
                                    title={`Day ${point.day}: ${formatNumber(point.supply)} ZDEX`}
                                >
                                    <span className="chart-label">D{point.day}</span>
                                </div>
                            ))}
                        </div>
                    </div>
                )}
            </div>

            <div className="stats-footer">
                <p>
                    <span className="verified-badge">Tau-Verified</span>
                    Burn contracts are formally specified; analytics fields show N/A until live telemetry is exposed.
                </p>
            </div>
        </div>
    );
}

export default TokenStats;
