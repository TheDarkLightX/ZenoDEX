/**
 * ZenoDEX - Mock Data for Demo Mode
 *
 * This file contains all mock data used when the app is in demo mode.
 * In production mode, this data is NOT used - real Tau Net data is fetched.
 */

// =============================================================================
// Tokens
// =============================================================================

export const DEMO_TOKENS = [
    { symbol: 'AGRS', name: 'Agoras', icon: '✦', decimals: 18 },
    { symbol: 'ZDEX', name: 'ZenoDEX', icon: '⚡', decimals: 18 },
    { symbol: 'USDC', name: 'USD Coin', icon: '💵', decimals: 6 },
    { symbol: 'WETH', name: 'Wrapped ETH', icon: '⟠', decimals: 18 },
];

// =============================================================================
// Pools
// =============================================================================

export const DEMO_POOLS = [
    {
        id: 'agrs-zdex',
        token0: { symbol: 'AGRS', name: 'Agoras', icon: '✦' },
        token1: { symbol: 'ZDEX', name: 'ZenoDEX', icon: '⚡' },
        reserve0: 1000000,
        reserve1: 500000,
        tvl: 2500000,
        volume24h: 150000,
        apy: 0.0847,
        totalLpSupply: 700000,
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
        totalLpSupply: 1500000,
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
        totalLpSupply: 750000,
        myLp: 0,
    },
];

export const DEMO_POOL_RESERVES = {
    'AGRS-USDC': { reserve0: 1000000, reserve1: 2500000 },
    'AGRS-WETH': { reserve0: 1000000, reserve1: 500 },
    'USDC-WETH': { reserve0: 2500000, reserve1: 1000 },
    'AGRS-ZDEX': { reserve0: 1000000, reserve1: 500000 },
};

// =============================================================================
// User Balances
// =============================================================================

export const DEMO_BALANCES = {
    AGRS: 1234.56,
    ZDEX: 5000.00,
    USDC: 5000.00,
    WETH: 2.5,
};

// =============================================================================
// Transactions
// =============================================================================

export const DEMO_TRANSACTIONS = [
    {
        id: 'tx-001',
        type: 'swap',
        timestamp: Date.now() - 3600000,
        tokenIn: { symbol: 'AGRS', icon: '✦', amount: 100 },
        tokenOut: { symbol: 'ZDEX', icon: '⚡', amount: 49.5 },
        status: 'confirmed',
        txHash: 'abc123def456789012345678901234567890abcdef',
    },
    {
        id: 'tx-002',
        type: 'add_liquidity',
        timestamp: Date.now() - 7200000,
        token0: { symbol: 'AGRS', icon: '✦', amount: 500 },
        token1: { symbol: 'USDC', icon: '💵', amount: 1250 },
        lpReceived: 750,
        pool: 'AGRS-USDC',
        status: 'confirmed',
        txHash: 'def456ghi789012345678901234567890abcdef12',
    },
    {
        id: 'tx-003',
        type: 'swap',
        timestamp: Date.now() - 86400000,
        tokenIn: { symbol: 'USDC', icon: '💵', amount: 500 },
        tokenOut: { symbol: 'AGRS', icon: '✦', amount: 200 },
        status: 'confirmed',
        txHash: 'ghi789jkl012345678901234567890abcdef1234',
    },
    {
        id: 'tx-004',
        type: 'remove_liquidity',
        timestamp: Date.now() - 172800000,
        token0: { symbol: 'ZDEX', icon: '⚡', amount: 100 },
        token1: { symbol: 'USDC', icon: '💵', amount: 250 },
        lpBurned: 150,
        pool: 'ZDEX-USDC',
        status: 'confirmed',
        txHash: 'jkl012mno345678901234567890abcdef123456',
    },
    {
        id: 'tx-005',
        type: 'swap',
        timestamp: Date.now() - 60000,
        tokenIn: { symbol: 'AGRS', icon: '✦', amount: 50 },
        tokenOut: { symbol: 'USDC', icon: '💵', amount: 125 },
        status: 'pending',
        txHash: 'mno345pqr678901234567890abcdef12345678',
    },
];

// =============================================================================
// ZDEX Token Stats
// =============================================================================

export const DEMO_ZDEX_STATS = {
    initialSupply: 1000000,
    minSupply: 100000,
    currentSupply: 800000,
    burnedTotal: 200000,
    buybackPool: 12500,
    dailyVolume: 150000,
    burnRate: 0.005,
};

export const DEMO_BURN_HISTORY = [
    { day: 1, supply: 1000000, burned: 0 },
    { day: 30, supply: 950000, burned: 50000 },
    { day: 60, supply: 910000, burned: 90000 },
    { day: 90, supply: 875000, burned: 125000 },
    { day: 120, supply: 845000, burned: 155000 },
    { day: 150, supply: 820000, burned: 180000 },
    { day: 180, supply: 800000, burned: 200000 },
];

// =============================================================================
// System Status
// =============================================================================

export const DEMO_SYSTEM_STATUS = {
    oracle: {
        status: 'healthy',
        lastUpdate: Date.now() - 30000,
        sources: 3,
        medianPrice: 2.50,
    },
    circuitBreaker: {
        status: 'normal',
        threshold: 0.10,
        currentVolatility: 0.03,
        triggered: false,
    },
    network: {
        status: 'connected',
        blockHeight: 12345678,
        latency: 45,
    },
};

// =============================================================================
// Demo Wallet Generator
// =============================================================================

export function generateDemoWallet() {
    const chars = '0123456789abcdef';
    const address = Array.from({ length: 96 }, () =>
        chars[Math.floor(Math.random() * 16)]
    ).join('');

    return {
        address,
        chainId: 'tau-alpha',
        balance: { ...DEMO_BALANCES },
    };
}
