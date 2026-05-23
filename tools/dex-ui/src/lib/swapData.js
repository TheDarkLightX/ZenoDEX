import { apiFetchJson } from './api.js';

// Offline fallback for when /api/pools is unreachable. The live token set
// and pools come from the local testnet via /api/pools.
// Canonical local testnet tokens: ZDEX, zUSD, TASSET0, TASSET1, TZENO.
export const FALLBACK_SWAP_POOLS = {
    'TASSET0-ZDEX': { token0: 'TASSET0', token1: 'ZDEX', asset0: 'TASSET0', asset1: 'ZDEX', reserve0: 1_000_000, reserve1: 500_000, feeBps: 30 },
    'TASSET0-TASSET1': { token0: 'TASSET0', token1: 'TASSET1', asset0: 'TASSET0', asset1: 'TASSET1', reserve0: 1_000_000, reserve1: 1_000_000, feeBps: 30 },
    'TASSET1-TZENO': { token0: 'TASSET1', token1: 'TZENO', asset0: 'TASSET1', asset1: 'TZENO', reserve0: 1_000_000, reserve1: 1_000_000, feeBps: 30 },
};

export const FALLBACK_SWAP_TOKENS = [
    { symbol: 'ZDEX', name: 'ZenoDEX', icon: '⚡', decimals: 18 },
    { symbol: 'zUSD', name: 'ZenoUSD', icon: '◈', decimals: 18 },
    { symbol: 'tAGRS', name: 'Test Agoras', icon: '✦', decimals: 18 },
    { symbol: 'TASSET0', name: 'Test Asset 0', icon: 'T₀', decimals: 18 },
    { symbol: 'TASSET1', name: 'Test Asset 1', icon: 'T₁', decimals: 18 },
    { symbol: 'TZENO', name: 'Test Zeno', icon: 'TZ', decimals: 18 },
];

export const FALLBACK_SWAP_BALANCES = {
    ZDEX: 1_000_000,
    zUSD: 0,
    tAGRS: 1_000_000,
    TASSET0: 1_000_000,
    TASSET1: 1_000_000,
    TZENO: 1_000_000,
};

function clonePools(pools) {
    return Object.fromEntries(
        Object.entries(pools).map(([k, v]) => [
            k,
            {
                token0: v.token0,
                token1: v.token1,
                asset0: v.asset0,
                asset1: v.asset1,
                poolId: v.poolId ?? v.pool_id ?? null,
                assetsBySymbol: v.assetsBySymbol || {
                    [String(v.token0 || '').toUpperCase()]: v.asset0,
                    [String(v.token1 || '').toUpperCase()]: v.asset1,
                },
                reserve0: Number(v.reserve0),
                reserve1: Number(v.reserve1),
                feeBps: Number(v.feeBps ?? 30),
            },
        ]),
    );
}

function toFiniteNumber(v) {
    const n = Number(v);
    return Number.isFinite(n) ? n : NaN;
}

function normalizeSymbol(value) {
    return String(value ?? '').trim().toUpperCase();
}

function defaultTokenForSymbol(symbol) {
    const normalized = normalizeSymbol(symbol);
    const known = FALLBACK_SWAP_TOKENS.find((token) => token.symbol === normalized);
    if (known) return known;
    return {
        symbol: normalized,
        name: normalized,
        icon: '◎',
        decimals: 0,
    };
}

function normalizePoolEntry(entry) {
    if (!entry || typeof entry !== 'object') return null;
    const token0 = normalizeSymbol(entry.token0 ?? entry.symbol0 ?? entry.base ?? entry.asset0);
    const token1 = normalizeSymbol(entry.token1 ?? entry.symbol1 ?? entry.quote ?? entry.asset1);
    const rawAsset0 = String(entry.asset0 ?? entry.token0 ?? entry.base ?? '').trim();
    const rawAsset1 = String(entry.asset1 ?? entry.token1 ?? entry.quote ?? '').trim();
    if (!token0 || !token1 || token0 === token1) return null;
    const reserve0 = toFiniteNumber(entry.reserve0 ?? entry.r0 ?? entry.baseReserve);
    const reserve1 = toFiniteNumber(entry.reserve1 ?? entry.r1 ?? entry.quoteReserve);
    if (!(reserve0 > 0) || !(reserve1 > 0)) return null;
    const feeRaw = toFiniteNumber(entry.feeBps ?? entry.fee_bps ?? entry.fee_bps_hint ?? 30);
    const feeBps = Number.isFinite(feeRaw) ? Math.max(0, Math.min(500, Math.round(feeRaw))) : 30;
    const [assetA, assetB] = [token0, token1].sort();
    const key = `${assetA}-${assetB}`;
    const aligned = token0 === assetA
        ? {
            reserve0,
            reserve1,
            asset0: rawAsset0 || token0,
            asset1: rawAsset1 || token1,
            token0,
            token1,
        }
        : {
            reserve0: reserve1,
            reserve1: reserve0,
            asset0: rawAsset1 || token1,
            asset1: rawAsset0 || token0,
            token0: token1,
            token1: token0,
        };
    return {
        key,
        poolId: entry.poolId ?? entry.pool_id ?? null,
        token0: aligned.token0,
        token1: aligned.token1,
        asset0: aligned.asset0,
        asset1: aligned.asset1,
        assetsBySymbol: {
            [token0]: rawAsset0 || token0,
            [token1]: rawAsset1 || token1,
        },
        reserve0: aligned.reserve0,
        reserve1: aligned.reserve1,
        feeBps,
    };
}

function normalizeTokens(payload, poolSymbols) {
    const bySymbol = new Map();
    for (const symbol of poolSymbols) {
        const token = defaultTokenForSymbol(symbol);
        bySymbol.set(token.symbol, token);
    }
    const rows = payload && typeof payload === 'object' && Array.isArray(payload.tokens)
        ? payload.tokens
        : [];
    for (const row of rows) {
        if (!row || typeof row !== 'object') continue;
        const symbol = normalizeSymbol(row.symbol);
        if (!symbol || !bySymbol.has(symbol)) continue;
        bySymbol.set(symbol, {
            ...defaultTokenForSymbol(symbol),
            symbol,
            name: String(row.name ?? row.purpose ?? symbol),
            assetId: row.asset_id ?? row.assetId ?? null,
            decimals: Number.isFinite(Number(row.decimals)) ? Number(row.decimals) : 0,
        });
    }
    return Array.from(bySymbol.values()).sort((a, b) => a.symbol.localeCompare(b.symbol));
}

function normalizePoolsPayload(payload) {
    if (!payload) return { pools: {}, tokens: [] };

    const rows = Array.isArray(payload)
        ? payload
        : Array.isArray(payload.pools)
            ? payload.pools
            : [];

    if (rows.length > 0) {
        const out = {};
        for (const row of rows) {
            const normalized = normalizePoolEntry(row);
            if (!normalized) continue;
            out[normalized.key] = {
                poolId: normalized.poolId,
                token0: normalized.token0,
                token1: normalized.token1,
                asset0: normalized.asset0,
                asset1: normalized.asset1,
                assetsBySymbol: normalized.assetsBySymbol,
                reserve0: normalized.reserve0,
                reserve1: normalized.reserve1,
                feeBps: normalized.feeBps,
            };
        }
        const poolSymbols = Array.from(
            new Set(Object.values(out).flatMap((pool) => [pool.token0, pool.token1]).filter(Boolean)),
        );
        return { pools: out, tokens: normalizeTokens(payload, poolSymbols) };
    }

    // Map payload form:
    // { "ZDEX-TASSET0": { reserve0, reserve1, feeBps } }
    const out = {};
    for (const [pair, value] of Object.entries(payload)) {
        if (!value || typeof value !== 'object') continue;
        const reserve0 = toFiniteNumber(value.reserve0);
        const reserve1 = toFiniteNumber(value.reserve1);
        if (!(reserve0 > 0) || !(reserve1 > 0)) continue;
        const feeBps = Number.isFinite(toFiniteNumber(value.feeBps)) ? Math.round(value.feeBps) : 30;
        const [token0 = '', token1 = ''] = String(pair).split('-').map(normalizeSymbol);
        out[pair] = {
            token0,
            token1,
            asset0: token0,
            asset1: token1,
            assetsBySymbol: { [token0]: token0, [token1]: token1 },
            reserve0,
            reserve1,
            feeBps,
        };
    }
    const poolSymbols = Array.from(
        new Set(Object.values(out).flatMap((pool) => [pool.token0, pool.token1]).filter(Boolean)),
    );
    return { pools: out, tokens: normalizeTokens(payload, poolSymbols) };
}

export async function loadSwapPools({ timeoutMs = 2500 } = {}) {
    try {
        const payload = await apiFetchJson('/api/pools', { method: 'GET', timeoutMs });
        const { pools, tokens } = normalizePoolsPayload(payload);
        if (Object.keys(pools).length === 0) {
            throw new Error('empty_pool_set');
        }
        return {
            source: 'api',
            pools,
            tokens,
            error: null,
        };
    } catch (err) {
        return {
            source: 'fallback',
            pools: clonePools(FALLBACK_SWAP_POOLS),
            tokens: [...FALLBACK_SWAP_TOKENS],
            error: err?.message || 'pool_feed_unavailable',
        };
    }
}

export function resolveWalletTokenBalance(wallet, symbol) {
    if (!wallet) return null;
    const balances = wallet?.balance || {};
    const raw = String(symbol || '');
    // Try exact, upper, and lower-case keys so symbols like `zUSD` resolve
    // whether wallets store them mixed-case or normalized.
    const candidates = [raw, raw.toUpperCase(), raw.toLowerCase()];
    for (const key of candidates) {
        if (key in balances) {
            const v = Number(balances[key]);
            if (Number.isFinite(v)) return v;
        }
    }
    return null;
}
