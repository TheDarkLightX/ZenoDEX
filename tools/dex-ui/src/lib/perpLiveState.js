const SUPPORTED_MARKET_KIND = 'clearinghouse_2p_v1';

const AUTHORITATIVE_WRITE_FIELDS = Object.freeze([
    'epochPhase',
    'nowEpoch',
    'oracleLastUpdateEpoch',
    'oracleSeen',
    'indexPriceE8',
    'maintenanceMarginBps',
    'initialMarginBps',
    'depegBufferBps',
    'maxPositionAbs',
    'maxOracleStalenessEpochs',
    'breakerActive',
]);

const KNOWN_EPOCH_PHASES = new Set(['Open', 'PricePublished', 'Settled']);

function nullableSafeInteger(value) {
    if (value == null || value === '') return null;
    const parsed = Number(value);
    return Number.isSafeInteger(parsed) ? parsed : null;
}

function nullableBoolean(value) {
    return typeof value === 'boolean' ? value : null;
}

function nullableString(value) {
    if (value == null) return null;
    const parsed = String(value).trim();
    return parsed || null;
}

function normalizePubkey(value) {
    return String(value || '').toLowerCase().replace(/^0x/, '');
}

function explicitEpochPhase(walletMarket) {
    const phase = nullableString(walletMarket.epoch_phase ?? walletMarket.phase);
    return phase && KNOWN_EPOCH_PHASES.has(phase) ? phase : 'Unknown';
}

function missingAuthoritativeWriteFields(market) {
    return AUTHORITATIVE_WRITE_FIELDS.filter((field) => {
        if (field === 'epochPhase') return !KNOWN_EPOCH_PHASES.has(market?.epochPhase);
        return market?.[field] == null;
    });
}

/**
 * Normalize a wallet-status market without manufacturing protocol facts.
 *
 * Only the production 2-party clearinghouse is supported by this trader view.
 * Unknown market kinds are excluded so a sparse payload can never masquerade
 * as a tradeable market.
 */
export function normalizeWalletMarket(walletMarket) {
    if (!walletMarket || typeof walletMarket !== 'object' || Array.isArray(walletMarket)) {
        return { ok: false, error: 'invalid_perps_market_summary' };
    }

    const id = nullableString(walletMarket.market_id ?? walletMarket.id);
    const kind = nullableString(walletMarket.kind);
    if (!id) return { ok: false, error: 'perps_market_id_missing' };
    if (kind !== SUPPORTED_MARKET_KIND) {
        return {
            ok: false,
            error: `unsupported_perps_market_kind:${id}:${kind || 'unknown'}`,
        };
    }

    const nowEpoch = nullableSafeInteger(walletMarket.now_epoch);
    const oracleLastUpdateEpoch = nullableSafeInteger(walletMarket.oracle_last_update_epoch);
    const explicitOracleSeen = nullableBoolean(walletMarket.oracle_seen);
    const oracleSeen = explicitOracleSeen ?? (
        nowEpoch != null && oracleLastUpdateEpoch != null
            ? oracleLastUpdateEpoch === nowEpoch
            : null
    );

    const market = {
        id,
        kind,
        quoteAsset: nullableString(walletMarket.quote_asset),
        nowEpoch,
        oracleLastUpdateEpoch,
        oracleSeen,
        epochPhase: explicitEpochPhase(walletMarket),
        indexPriceE8: nullableSafeInteger(walletMarket.index_price_e8),
        clearingPriceE8: nullableSafeInteger(walletMarket.clearing_price_e8),
        clearingPriceEpoch: nullableSafeInteger(walletMarket.clearing_price_epoch),
        maintenanceMarginBps: nullableSafeInteger(walletMarket.maintenance_margin_bps),
        initialMarginBps: nullableSafeInteger(walletMarket.initial_margin_bps),
        depegBufferBps: nullableSafeInteger(walletMarket.depeg_buffer_bps),
        maxPositionAbs: nullableSafeInteger(walletMarket.max_position_abs),
        maxOracleStalenessEpochs: nullableSafeInteger(walletMarket.max_oracle_staleness_epochs),
        breakerActive: nullableBoolean(walletMarket.breaker_active),
        breakerLastTriggerEpoch: nullableSafeInteger(walletMarket.breaker_last_trigger_epoch),
        fundingRateBps: nullableSafeInteger(walletMarket.funding_rate_bps),
        accountAPubkey: nullableString(walletMarket.account_a_pubkey),
        accountBPubkey: nullableString(walletMarket.account_b_pubkey),
        positionBaseA: nullableSafeInteger(walletMarket.position_base_a),
        positionBaseB: nullableSafeInteger(walletMarket.position_base_b),
        collateralE8A: nullableSafeInteger(walletMarket.collateral_e8_a),
        collateralE8B: nullableSafeInteger(walletMarket.collateral_e8_b),
        entryPriceE8A: nullableSafeInteger(walletMarket.entry_price_e8_a),
        entryPriceE8B: nullableSafeInteger(walletMarket.entry_price_e8_b),
        feePoolE8: nullableSafeInteger(walletMarket.fee_pool_e8),
        feeIncome: nullableSafeInteger(walletMarket.fee_income ?? walletMarket.fee_pool_quote),
        initialInsurance: nullableSafeInteger(walletMarket.initial_insurance),
        insuranceBalance: nullableSafeInteger(walletMarket.insurance_balance),
        claimsPaid: nullableSafeInteger(walletMarket.claims_paid),
    };
    const missing = missingAuthoritativeWriteFields(market);
    return {
        ok: true,
        market: {
            ...market,
            authoritativeWriteFactsReady: missing.length === 0,
            missingAuthoritativeWriteFacts: Object.freeze(missing),
        },
    };
}

export function normalizeWalletMarkets(walletMarkets) {
    const markets = [];
    const errors = [];
    const seenIds = new Set();
    for (const walletMarket of Array.isArray(walletMarkets) ? walletMarkets : []) {
        const result = normalizeWalletMarket(walletMarket);
        if (!result.ok) {
            errors.push(result.error);
            continue;
        }
        if (seenIds.has(result.market.id)) {
            errors.push(`duplicate_perps_market_id:${result.market.id}`);
            continue;
        }
        seenIds.add(result.market.id);
        markets.push(result.market);
    }
    return { markets, errors };
}

export function deriveWalletPosition(walletMarket, userPubkey) {
    if (!walletMarket || !userPubkey) return null;
    const user = normalizePubkey(userPubkey);
    const accountA = normalizePubkey(walletMarket.account_a_pubkey);
    const accountB = normalizePubkey(walletMarket.account_b_pubkey);

    let positionBase = null;
    let collateralE8 = null;
    let entryPriceE8 = null;
    if (user && user === accountA) {
        positionBase = nullableSafeInteger(walletMarket.position_base_a);
        collateralE8 = nullableSafeInteger(walletMarket.collateral_e8_a);
        entryPriceE8 = nullableSafeInteger(walletMarket.entry_price_e8_a);
    } else if (user && user === accountB) {
        positionBase = nullableSafeInteger(walletMarket.position_base_b);
        collateralE8 = nullableSafeInteger(walletMarket.collateral_e8_b);
        entryPriceE8 = nullableSafeInteger(walletMarket.entry_price_e8_b);
    } else {
        return null;
    }

    const collateralQuote = collateralE8 != null && collateralE8 % 100_000_000 === 0
        ? collateralE8 / 100_000_000
        : null;
    const missing = [];
    if (positionBase == null) missing.push('positionBase');
    if (collateralQuote == null) missing.push('collateralQuote');
    if (positionBase !== 0 && entryPriceE8 == null) missing.push('entryPriceE8');

    return {
        marketId: nullableString(walletMarket.market_id ?? walletMarket.id),
        pubkey: userPubkey,
        positionBase,
        collateralE8,
        collateralQuote,
        entryPriceE8,
        authoritativePositionFactsReady: missing.length === 0,
        missingAuthoritativePositionFacts: Object.freeze(missing),
    };
}

export function marketWriteReadinessError(market) {
    if (!market) return 'perps_authoritative_market_unavailable';
    if (market.kind !== SUPPORTED_MARKET_KIND) {
        return `unsupported_perps_market_kind:${market.id || 'unknown'}:${market.kind || 'unknown'}`;
    }
    const missing = missingAuthoritativeWriteFields(market);
    if (missing.length > 0) {
        return `perps_authoritative_facts_unavailable:${market.id}:${missing.join(',')}`;
    }
    return null;
}

export function hasAuthoritativePositionDerivationFacts(market, position) {
    if (!market || !position || position.positionBase === 0) return false;
    return position.positionBase != null
        && position.collateralQuote != null
        && position.entryPriceE8 != null
        && market.indexPriceE8 != null
        && market.maintenanceMarginBps != null
        && market.depegBufferBps != null;
}

export const SUPPORTED_PERP_MARKET_KIND = SUPPORTED_MARKET_KIND;
