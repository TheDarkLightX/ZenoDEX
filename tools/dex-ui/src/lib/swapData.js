import { apiFetchJson } from './api.js';

function toFiniteNumber(v) {
    const n = Number(v);
    return Number.isFinite(n) ? n : NaN;
}

function normalizeSymbol(value) {
    return String(value ?? '').trim().toUpperCase();
}

export function isCanonicalAssetId(value) {
    return /^0x[0-9a-f]{64}$/i.test(String(value || '').trim());
}

export function isCompactAssetLabel(value) {
    return /^Asset [0-9a-f]{4}\.\.\.[0-9a-f]{4}$/i.test(String(value || '').trim());
}

export function compactAssetLabel(value) {
    const text = String(value || '').trim();
    if (!isCanonicalAssetId(text)) return normalizeSymbol(text);
    return `Asset ${text.slice(2, 6).toUpperCase()}...${text.slice(-4).toUpperCase()}`;
}

export function displaySymbolForAsset(value) {
    const text = String(value || '').trim();
    if (isCanonicalAssetId(text)) return compactAssetLabel(text);
    if (isCompactAssetLabel(text)) {
        const match = /^Asset ([0-9a-f]{4})\.\.\.([0-9a-f]{4})$/i.exec(text);
        return `Asset ${match[1].toUpperCase()}...${match[2].toUpperCase()}`;
    }
    return normalizeSymbol(text);
}

function defaultTokenForSymbol(symbol) {
    const normalized = displaySymbolForAsset(symbol);
    return {
        symbol: normalized,
        name: normalized,
        icon: isCanonicalAssetId(symbol) || isCompactAssetLabel(normalized) ? '#' : '◎',
        decimals: 0,
    };
}

function normalizePoolEntry(entry) {
    if (!entry || typeof entry !== 'object') return null;
    const rawAsset0 = String(entry.asset0 ?? entry.token0 ?? entry.base ?? '').trim();
    const rawAsset1 = String(entry.asset1 ?? entry.token1 ?? entry.quote ?? '').trim();
    const token0 = displaySymbolForAsset(entry.token0 ?? entry.symbol0 ?? entry.base ?? entry.asset0);
    const token1 = displaySymbolForAsset(entry.token1 ?? entry.symbol1 ?? entry.quote ?? entry.asset1);
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
        const symbol = displaySymbolForAsset(row.symbol);
        if (!symbol || !bySymbol.has(symbol)) continue;
        bySymbol.set(symbol, {
            ...defaultTokenForSymbol(symbol),
            symbol,
            name: String(row.name ?? row.purpose ?? symbol),
            assetId: row.asset_id ?? row.assetId ?? null,
            decimals: Number.isFinite(Number(row.decimals)) ? Number(row.decimals) : 0,
        });
    }
    return Array.from(bySymbol.values()).sort((a, b) => {
        const aIsUnhinted = a.symbol.startsWith('Asset ') || a.symbol.startsWith('0x');
        const bIsUnhinted = b.symbol.startsWith('Asset ') || b.symbol.startsWith('0x');
        if (aIsUnhinted && !bIsUnhinted) return 1;
        if (!aIsUnhinted && bIsUnhinted) return -1;
        return a.symbol.localeCompare(b.symbol);
    });
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
    // { "POOL_ID": { reserve0, reserve1, feeBps } }
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

export async function loadSwapPools({ timeoutMs = 2500, account = '' } = {}) {
    try {
        const query = account ? `?account=${encodeURIComponent(account)}` : '';
        const payload = await apiFetchJson(`/api/pools${query}`, { method: 'GET', timeoutMs });
        const { pools, tokens } = normalizePoolsPayload(payload);
        if (Object.keys(pools).length === 0) {
            throw new Error('empty_pool_set');
        }
        const rawLastNonce = payload && Object.prototype.hasOwnProperty.call(payload, 'account_last_nonce')
            ? Number(payload.account_last_nonce)
            : NaN;
        return {
            source: 'api',
            pools,
            tokens,
            account: payload?.account || null,
            accountLastNonce: Number.isSafeInteger(rawLastNonce) ? rawLastNonce : null,
            error: null,
        };
    } catch (err) {
        return {
            source: 'unavailable',
            pools: {},
            tokens: [],
            account: account || null,
            accountLastNonce: null,
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
