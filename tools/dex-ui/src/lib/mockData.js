/**
 * Offline / illustrative fallbacks for the ZenoDEX UI.
 *
 * These values are used when the live Tau-node API is unreachable so the
 * UI can render coherent shells. Live data, when present, always takes
 * precedence. The token set matches the local testnet:
 * ZDEX, zUSD, tAGRS, TASSET0, TASSET1, TZENO.
 * (AGRS is the canonical production collateral for zUSD but is not yet
 * deployed on the local testnet; tAGRS is the value-less test stand-in.)
 */

// =============================================================================
// Tokens
// =============================================================================

export const FALLBACK_TOKENS = [
    { symbol: 'ZDEX', name: 'ZenoDEX', icon: '⚡', decimals: 18 },
    { symbol: 'zUSD', name: 'ZenoUSD', icon: '◈', decimals: 18 },
    { symbol: 'tAGRS', name: 'Test Agoras', icon: '✦', decimals: 18 },
    { symbol: 'TASSET0', name: 'Test Asset 0', icon: 'T₀', decimals: 18 },
    { symbol: 'TASSET1', name: 'Test Asset 1', icon: 'T₁', decimals: 18 },
    { symbol: 'TZENO', name: 'Test Zeno', icon: 'TZ', decimals: 18 },
];

// =============================================================================
// Pools
// =============================================================================

export const FALLBACK_POOLS = [
    {
        id: 'tasset0-zdex',
        token0: { symbol: 'TASSET0', name: 'Test Asset 0', icon: 'T₀' },
        token1: { symbol: 'ZDEX', name: 'ZenoDEX', icon: '⚡' },
        reserve0: 1_000_000,
        reserve1: 500_000,
        tvl: 0,
        volume24h: 0,
        apy: 0,
        totalLpSupply: 700_000,
        myLp: 0,
    },
    {
        id: 'tasset0-tasset1',
        token0: { symbol: 'TASSET0', name: 'Test Asset 0', icon: 'T₀' },
        token1: { symbol: 'TASSET1', name: 'Test Asset 1', icon: 'T₁' },
        reserve0: 1_000_000,
        reserve1: 1_000_000,
        tvl: 0,
        volume24h: 0,
        apy: 0,
        totalLpSupply: 1_000_000,
        myLp: 0,
    },
    {
        id: 'tasset1-tzeno',
        token0: { symbol: 'TASSET1', name: 'Test Asset 1', icon: 'T₁' },
        token1: { symbol: 'TZENO', name: 'Test Zeno', icon: 'TZ' },
        reserve0: 1_000_000,
        reserve1: 1_000_000,
        tvl: 0,
        volume24h: 0,
        apy: 0,
        totalLpSupply: 1_000_000,
        myLp: 0,
    },
];

export const FALLBACK_POOL_RESERVES = {
    'TASSET0-ZDEX': { reserve0: 1_000_000, reserve1: 500_000 },
    'TASSET0-TASSET1': { reserve0: 1_000_000, reserve1: 1_000_000 },
    'TASSET1-TZENO': { reserve0: 1_000_000, reserve1: 1_000_000 },
};

// =============================================================================
// User Balances
// =============================================================================

export const FALLBACK_BALANCES = {
    ZDEX: 1_000_000,
    zUSD: 0,
    tAGRS: 1_000_000,
    TASSET0: 1_000_000,
    TASSET1: 1_000_000,
    TZENO: 1_000_000,
};

// =============================================================================
// Transactions (illustrative — empty when no live history is loaded)
// =============================================================================

export const FALLBACK_TRANSACTIONS = [];

// =============================================================================
// ZDEX Token Stats
// =============================================================================

export const FALLBACK_ZDEX_STATS = {
    initialSupply: 1_000_000,
    minSupply: 100_000,
    currentSupply: 1_000_000,
    burnedTotal: 0,
    buybackPool: 0,
    dailyVolume: 0,
    burnRate: 0,
};

export const FALLBACK_BURN_HISTORY = [
    { day: 0, supply: 1_000_000, burned: 0 },
];

// =============================================================================
// System Status
// =============================================================================

export const FALLBACK_SYSTEM_STATUS = {
    oracle: {
        status: 'unknown',
        lastUpdate: 0,
        sources: 0,
        medianPrice: 0,
    },
    circuitBreaker: {
        status: 'unknown',
        threshold: 0.10,
        currentVolatility: 0,
        triggered: false,
    },
    network: {
        status: 'unknown',
        blockHeight: 0,
        latency: 0,
    },
};

// =============================================================================
// Backwards-compat aliases (so older imports keep working during the
// demo → live transition). Prefer the FALLBACK_* names in new code.
// =============================================================================

export const DEMO_TOKENS = FALLBACK_TOKENS;
export const DEMO_POOLS = FALLBACK_POOLS;
export const DEMO_POOL_RESERVES = FALLBACK_POOL_RESERVES;
export const DEMO_BALANCES = FALLBACK_BALANCES;
export const DEMO_TRANSACTIONS = FALLBACK_TRANSACTIONS;
export const DEMO_ZDEX_STATS = FALLBACK_ZDEX_STATS;
export const DEMO_BURN_HISTORY = FALLBACK_BURN_HISTORY;
export const DEMO_SYSTEM_STATUS = FALLBACK_SYSTEM_STATUS;
