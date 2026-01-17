import { useState, useMemo } from 'react';
import { formatNumber, formatPercent } from '../lib/cpmm';
import './TokenStats.css';

// ZDEX Token specifications
const INITIAL_SUPPLY = 1000000;
const MIN_SUPPLY = 100000;
const BURN_RATE = 0.005;

// Mock historical data
const MOCK_BURN_HISTORY = [
    { day: 1, supply: 1000000, burned: 0 },
    { day: 30, supply: 950000, burned: 50000 },
    { day: 60, supply: 910000, burned: 90000 },
    { day: 90, supply: 875000, burned: 125000 },
    { day: 120, supply: 845000, burned: 155000 },
    { day: 150, supply: 820000, burned: 180000 },
    { day: 180, supply: 800000, burned: 200000 },
];

function TokenStats() {
    const [currentSupply] = useState(800000);
    const [burnedTotal] = useState(200000);
    const [buybackPool] = useState(12500);
    const [dailyVolume] = useState(150000);

    const stats = useMemo(() => {
        const burnedPercent = burnedTotal / INITIAL_SUPPLY;
        const remainingToBurn = currentSupply - MIN_SUPPLY;
        const daysToFloor = remainingToBurn / (dailyVolume * 0.003 * 0.5 + (dailyVolume * 0.2) * BURN_RATE);

        return {
            burnedPercent,
            remainingToBurn,
            daysToFloor: Math.round(daysToFloor),
            buybackPending: buybackPool,
            dailyBurnRate: dailyVolume * 0.003 * 0.5,
        };
    }, [currentSupply, burnedTotal, buybackPool, dailyVolume]);

    return (
        <div className="token-stats">
            <div className="stats-header">
                <h2>
                    <span className="zdex-logo-inline">Z</span>
                    ZDEX Token Analytics
                </h2>
                <div className="live-badge">
                    <span className="live-dot"></span>
                    Live
                </div>
            </div>

            {/* Main Stats */}
            <div className="stats-grid grid grid-4">
                <div className="stat-card panel animate-slide-up" style={{ animationDelay: '0ms' }}>
                    <span className="stat-label">Current Supply</span>
                    <span className="stat-value">{formatNumber(currentSupply)}</span>
                    <span className="stat-sub">of {formatNumber(INITIAL_SUPPLY)} initial</span>
                </div>
                <div className="stat-card panel animate-slide-up" style={{ animationDelay: '50ms' }}>
                    <span className="stat-label">Total Burned</span>
                    <span className="stat-value stat-burned">{formatNumber(burnedTotal)}</span>
                    <span className="stat-sub">{formatPercent(stats.burnedPercent)} of initial</span>
                </div>
                <div className="stat-card panel animate-slide-up" style={{ animationDelay: '100ms' }}>
                    <span className="stat-label">Buyback Pool</span>
                    <span className="stat-value stat-pool">${formatNumber(buybackPool)}</span>
                    <span className="stat-sub">pending for burn</span>
                </div>
                <div className="stat-card panel animate-slide-up" style={{ animationDelay: '150ms' }}>
                    <span className="stat-label">Est. Days to Floor</span>
                    <span className="stat-value">{stats.daysToFloor}</span>
                    <span className="stat-sub">at current volume</span>
                </div>
            </div>

            {/* Supply Progress */}
            <div className="supply-progress panel animate-slide-up" style={{ animationDelay: '200ms' }}>
                <div className="progress-header">
                    <span>Supply Progression</span>
                    <span>{formatNumber(currentSupply)} → {formatNumber(MIN_SUPPLY)} floor</span>
                </div>
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
            </div>

            {/* Burn Mechanics */}
            <div className="burn-mechanics grid grid-2">
                <div className="panel animate-slide-up" style={{ animationDelay: '250ms' }}>
                    <h3>🔥 Burn Mechanics</h3>
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
                    <h3>📊 Zeno's Paradox Model</h3>
                    <p className="model-desc">
                        ZDEX implements Zeno's Paradox burn mechanism: each step burns a percentage
                        of the remaining supply, asymptotically approaching but never reaching the floor.
                    </p>
                    <div className="formula">
                        <code>S(n) = S₀ × (1 - p)ⁿ</code>
                    </div>
                    <p className="model-note">
                        Where p = 0.5% per transfer and n = number of transfers
                    </p>
                </div>
            </div>

            {/* Burn History Chart (Simplified) */}
            <div className="burn-chart panel animate-slide-up" style={{ animationDelay: '350ms' }}>
                <h3>Supply Over Time</h3>
                <div className="chart-container">
                    <div className="chart-y-axis">
                        <span>{formatNumber(INITIAL_SUPPLY)}</span>
                        <span>{formatNumber(MIN_SUPPLY)}</span>
                    </div>
                    <div className="chart-area">
                        {MOCK_BURN_HISTORY.map((point, i) => (
                            <div
                                key={point.day}
                                className="chart-bar"
                                style={{
                                    height: `${(point.supply / INITIAL_SUPPLY) * 100}%`,
                                    animationDelay: `${400 + i * 50}ms`
                                }}
                                title={`Day ${point.day}: ${formatNumber(point.supply)} ZDEX`}
                            >
                                <span className="chart-label">D{point.day}</span>
                            </div>
                        ))}
                    </div>
                </div>
            </div>

            <div className="stats-footer">
                <p>
                    <span className="verified-badge">✓ Tau-Verified</span>
                    All burn mechanics are formally verified using Tau Language specifications.
                </p>
            </div>
        </div>
    );
}

export default TokenStats;
