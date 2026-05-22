/**
 * ZenoDEX - Perpetuals Mock Data for Demo Mode
 *
 * This file contains all mock data used when the perps UI is in demo mode.
 * In production mode, real data is fetched from the perps API.
 *
 * All e8 prices and BigInt values are stored as regular Numbers here
 * and converted to BigInt at the boundary (PerpContext).
 */

import { EpochPhase } from './perpValidation.js';

// =============================================================================
// Markets
// =============================================================================

export const PERP_DEMO_MARKETS = [
    {
        id: 'BTC-USD',
        baseSymbol: 'BTC',
        quoteSymbol: 'USD',
        quoteAsset: 'USD',
        icon: '\u20BF',
        indexPriceE8: 4_200_000_000_000, // $42,000.00
        clearingPriceE8: 4_198_500_000_000,
        fundingRateBps: 3, // 0.03%
        nowEpoch: 1042,
        epochPhase: EpochPhase.OPEN,
        breakerActive: false,
        oracleSeen: true,
        oracleLastUpdateEpoch: 1042,
        // Control params
        maxOracleStalenessEpochs: 100,
        maxOracleMoveBps: 500,
        initialMarginBps: 1000,  // 10%
        maintenanceMarginBps: 500,  // 5%
        depegBufferBps: 100,  // 1%
        liquidationPenaltyBps: 50,
        maxPositionAbs: 1_000_000,
        fundingCapBps: 100,
        // Insurance
        insuranceBalance: 5_000_000_000,
        feeIncome: 1_200_000_000,
        claimsPaid: 200_000_000,
        // Aggregate stats
        openInterest: 125_000_000,
        volume24h: 890_000_000,
    },
    {
        id: 'ETH-USD',
        baseSymbol: 'ETH',
        quoteSymbol: 'USD',
        quoteAsset: 'USD',
        icon: '\u039E',
        indexPriceE8: 220_000_000_000, // $2,200.00
        clearingPriceE8: 219_850_000_000,
        fundingRateBps: -2, // -0.02%
        nowEpoch: 1042,
        epochPhase: EpochPhase.OPEN,
        breakerActive: false,
        oracleSeen: true,
        oracleLastUpdateEpoch: 1042,
        maxOracleStalenessEpochs: 100,
        maxOracleMoveBps: 500,
        initialMarginBps: 1000,
        maintenanceMarginBps: 500,
        depegBufferBps: 100,
        liquidationPenaltyBps: 50,
        maxPositionAbs: 10_000_000,
        fundingCapBps: 100,
        insuranceBalance: 3_000_000_000,
        feeIncome: 800_000_000,
        claimsPaid: 100_000_000,
        openInterest: 95_000_000,
        volume24h: 620_000_000,
    },
    {
        id: 'TAU-USD',
        baseSymbol: 'TAU',
        quoteSymbol: 'USD',
        quoteAsset: 'USD',
        icon: '\u03C4',
        indexPriceE8: 250_000_000, // $2.50
        clearingPriceE8: 249_500_000,
        fundingRateBps: 8, // 0.08%
        nowEpoch: 1042,
        epochPhase: EpochPhase.OPEN,
        breakerActive: false,
        oracleSeen: true,
        oracleLastUpdateEpoch: 1041,
        maxOracleStalenessEpochs: 100,
        maxOracleMoveBps: 500,
        initialMarginBps: 2000,  // 20% (higher for altcoin)
        maintenanceMarginBps: 1000,  // 10%
        depegBufferBps: 200,
        liquidationPenaltyBps: 100,
        maxPositionAbs: 100_000_000,
        fundingCapBps: 200,
        insuranceBalance: 1_000_000_000,
        feeIncome: 300_000_000,
        claimsPaid: 50_000_000,
        openInterest: 45_000_000,
        volume24h: 210_000_000,
    },
];

// =============================================================================
// Positions (per account per market)
// =============================================================================

export const PERP_DEMO_POSITIONS = {
    'BTC-USD': {
        positionBase: 5000, // 0.00005 BTC long
        entryPriceE8: 4_150_000_000_000,
        collateralQuote: 500_000_000, // $5,000 in quote units
        feePoolQuote: 25_000_000,
        fundingPaidCumulative: -1_200_000,
    },
    'ETH-USD': {
        positionBase: -100_000, // 0.001 ETH short
        entryPriceE8: 225_000_000_000,
        collateralQuote: 200_000_000,
        feePoolQuote: 10_000_000,
        fundingPaidCumulative: 500_000,
    },
    'TAU-USD': {
        positionBase: 0, // no position
        entryPriceE8: 0,
        collateralQuote: 100_000_000,
        feePoolQuote: 0,
        fundingPaidCumulative: 0,
    },
};

// =============================================================================
// Trade History
// =============================================================================

export const PERP_DEMO_HISTORY = [
    {
        id: 'ptx-001',
        timestamp: Date.now() - 600_000,
        market: 'BTC-USD',
        action: 'set_position',
        side: 'long',
        sizeBefore: 0,
        sizeAfter: 5000,
        priceE8: 4_150_000_000_000,
        pnlQuote: 0,
        status: 'confirmed',
    },
    {
        id: 'ptx-002',
        timestamp: Date.now() - 1_200_000,
        market: 'BTC-USD',
        action: 'deposit_collateral',
        side: null,
        amount: 500_000_000,
        status: 'confirmed',
    },
    {
        id: 'ptx-003',
        timestamp: Date.now() - 3_600_000,
        market: 'ETH-USD',
        action: 'set_position',
        side: 'short',
        sizeBefore: 0,
        sizeAfter: -100_000,
        priceE8: 225_000_000_000,
        pnlQuote: 0,
        status: 'confirmed',
    },
    {
        id: 'ptx-004',
        timestamp: Date.now() - 7_200_000,
        market: 'ETH-USD',
        action: 'deposit_collateral',
        side: null,
        amount: 200_000_000,
        status: 'confirmed',
    },
    {
        id: 'ptx-005',
        timestamp: Date.now() - 86_400_000,
        market: 'TAU-USD',
        action: 'deposit_collateral',
        side: null,
        amount: 100_000_000,
        status: 'confirmed',
    },
];

// =============================================================================
// Price History (for mini charts, last 24 data points)
// =============================================================================

function generatePriceHistory(basePriceE8, volatilityPct, points = 24) {
    const history = [];
    let price = basePriceE8;
    const now = Date.now();
    const interval = 3_600_000; // 1 hour

    for (let i = points; i >= 0; i--) {
        const change = 1 + (Math.random() - 0.5) * 2 * volatilityPct;
        price = Math.round(price * change);
        history.push({
            timestamp: now - i * interval,
            priceE8: price,
        });
    }
    return history;
}

export const PERP_DEMO_PRICE_HISTORY = {
    'BTC-USD': generatePriceHistory(4_200_000_000_000, 0.005),
    'ETH-USD': generatePriceHistory(220_000_000_000, 0.008),
    'TAU-USD': generatePriceHistory(250_000_000, 0.015),
};
