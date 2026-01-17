import { formatNumber, formatPercent } from '../lib/cpmm';
import './PoolDashboard.css';

// Mock pool data with AGRS and ZDEX
const MOCK_POOLS = [
    {
        id: 'agrs-zdex',
        token0: { symbol: 'AGRS', name: 'Agoras', icon: '✦' },
        token1: { symbol: 'ZDEX', name: 'ZenoDEX', icon: '⚡' },
        reserve0: 1000000,
        reserve1: 500000,
        tvl: 2500000,
        volume24h: 150000,
        apy: 0.0847,
        myLp: 0,
    },
    {
        id: 'agrs-usdc',
        token0: { symbol: 'AGRS', name: 'Agoras', icon: '✦' },
        token1: { symbol: 'USDC', name: 'USD Coin', icon: '💵' },
        reserve0: 1000000,
        reserve1: 2500000,
        tvl: 5000000,
        volume24h: 320000,
        apy: 0.1234,
        myLp: 0,
    },
    {
        id: 'zdex-usdc',
        token0: { symbol: 'ZDEX', name: 'ZenoDEX', icon: '⚡' },
        token1: { symbol: 'USDC', name: 'USD Coin', icon: '💵' },
        reserve0: 500000,
        reserve1: 1250000,
        tvl: 2500000,
        volume24h: 89000,
        apy: 0.0654,
        myLp: 0,
    },
];

function PoolDashboard({ wallet }) {
    return (
        <div className="pool-dashboard">
            <div className="pool-header">
                <h2>Liquidity Pools</h2>
                <button className="btn btn-primary">
                    + Add Liquidity
                </button>
            </div>

            <div className="pool-stats grid grid-4">
                <div className="stat panel animate-slide-up" style={{ animationDelay: '0ms' }}>
                    <span className="stat-label">Total TVL</span>
                    <span className="stat-value">${formatNumber(10000000)}</span>
                </div>
                <div className="stat panel animate-slide-up" style={{ animationDelay: '50ms' }}>
                    <span className="stat-label">24h Volume</span>
                    <span className="stat-value">${formatNumber(559000)}</span>
                </div>
                <div className="stat panel animate-slide-up" style={{ animationDelay: '100ms' }}>
                    <span className="stat-label">24h Fees</span>
                    <span className="stat-value">${formatNumber(1677)}</span>
                </div>
                <div className="stat panel animate-slide-up" style={{ animationDelay: '150ms' }}>
                    <span className="stat-label">Active Pools</span>
                    <span className="stat-value">3</span>
                </div>
            </div>

            <div className="pool-table panel">
                <table>
                    <thead>
                        <tr>
                            <th>Pool</th>
                            <th>TVL</th>
                            <th>24h Volume</th>
                            <th>APY</th>
                            <th>My Position</th>
                            <th></th>
                        </tr>
                    </thead>
                    <tbody>
                        {MOCK_POOLS.map((pool, i) => (
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
                                <td>${formatNumber(pool.tvl)}</td>
                                <td>${formatNumber(pool.volume24h)}</td>
                                <td className="apy-cell">{formatPercent(pool.apy)}</td>
                                <td>
                                    {pool.myLp > 0 ? (
                                        <span>${formatNumber(pool.myLp)}</span>
	                                    ) : (
	                                        <span className="no-position">-</span>
	                                    )}
	                                </td>
                                <td>
                                    <div className="pool-actions">
                                        <button className="btn btn-secondary">Add</button>
                                        <button className="btn btn-secondary">Swap</button>
                                    </div>
                                </td>
                            </tr>
                        ))}
                    </tbody>
                </table>
            </div>

            <div className="pool-footer">
                <p>All pools are formally verified using Tau Language specifications.</p>
            </div>
        </div>
    );
}

export default PoolDashboard;
