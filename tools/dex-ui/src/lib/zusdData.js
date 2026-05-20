/**
 * Demo data for the zUSD stablecoin tab.
 * Models the backend zUSD system: vaults, stability pool, oracle, redemption.
 */

export const ZUSD_SUMMARY = {
  totalDebt: 2_450_000,
  totalCollateral: 5_250_000,
  globalCR: 214.3,
  stabilityPoolSize: 820_000,
  baseRateBps: 50,
  minCollRatio: 110,
  oraclePrice: 2.50,
  oracleAsset: 'AGRS',
  oracleStale: false,
  lastOracleEpoch: 1238,
};

export const ZUSD_OPERATIONS = [
  {
    id: 'mint',
    label: 'Mint zUSD',
    description: 'Deposit AGRS collateral to mint new zUSD stablecoins.',
    action: 'Deposit collateral, receive zUSD',
    minCR: '110%',
  },
  {
    id: 'repay',
    label: 'Repay Debt',
    description: 'Burn zUSD to reduce vault debt and free collateral.',
    action: 'Burn zUSD, withdraw collateral',
    minCR: 'N/A',
  },
  {
    id: 'redeem',
    label: 'Redeem',
    description: 'Exchange zUSD 1:1 for collateral from the riskiest vaults.',
    action: '1 zUSD = $1 of AGRS',
    minCR: 'N/A',
  },
  {
    id: 'deposit_sp',
    label: 'Stability Pool',
    description: 'Deposit zUSD to absorb liquidations and earn collateral rewards.',
    action: 'Earn liquidation discounts',
    minCR: 'N/A',
  },
];

export const DEMO_VAULTS = [
  {
    id: 'vault_001',
    owner: '0xabc1...f234',
    collateral: 10000,
    debt: 4000,
    cr: 250.0,
    status: 'healthy',
  },
  {
    id: 'vault_002',
    owner: '0xdef5...6789',
    collateral: 5500,
    debt: 4200,
    cr: 130.9,
    status: 'warning',
  },
  {
    id: 'vault_003',
    owner: '0x1234...abcd',
    collateral: 3000,
    debt: 2500,
    cr: 120.0,
    status: 'danger',
  },
  {
    id: 'vault_004',
    owner: '0x5678...ef01',
    collateral: 25000,
    debt: 8000,
    cr: 312.5,
    status: 'healthy',
  },
  {
    id: 'vault_005',
    owner: '0x9abc...2345',
    collateral: 8000,
    debt: 3200,
    cr: 250.0,
    status: 'healthy',
  },
];

export const ZUSD_GUARDS = [
  {
    id: 'ceil_div_fee',
    label: 'Ceiling Division Fee Safety',
    detail: 'Borrow and redemption fees use ceil_div to prevent rounding bypass.',
    proof: 'ZUSDCeilDivAlgebra.lean',
    status: 'proved',
  },
  {
    id: 'debt_homomorphism',
    label: 'Debt Conservation Homomorphism',
    detail: 'Net debt flow is additive: \u0394(s\u2081 + s\u2082) = \u0394(s\u2081) + \u0394(s\u2082).',
    proof: 'ZUSDDebtHomomorphism.lean',
    status: 'proved',
  },
  {
    id: 'dual_conservation',
    label: 'Dual Conservation',
    detail: 'Collateral and debt balances are jointly conserved across operations.',
    proof: 'ZUSDDualConservation.lean',
    status: 'proved',
  },
  {
    id: 'mcr_headroom',
    label: 'MCR Headroom Safety',
    detail: 'Minimum collateral ratio headroom prevents cliff-edge liquidations.',
    proof: 'ZUSDMCRHeadroom.lean',
    status: 'proved',
  },
  {
    id: 'sp_convexity',
    label: 'Stability Pool Convexity',
    detail: 'Stability pool deposits have convex returns from liquidation absorption.',
    proof: 'ZUSDSPConvexity.lean',
    status: 'proved',
  },
  {
    id: 'collateral_flow',
    label: 'Collateral Flow Algebra',
    detail: 'Collateral movements (deposit, withdraw, liquidation) form a closed system.',
    proof: 'ZUSDCollateralFlowAlgebra.lean',
    status: 'proved',
  },
  {
    id: 'fee_pipeline',
    label: 'Fee Pipeline Correctness',
    detail: 'Fees flow through borrow, redeem, and liquidation without leakage.',
    proof: 'ZUSDFeePipeline.lean',
    status: 'proved',
  },
];

export const ZUSD_RISK_PARAMS = [
  { param: 'Minimum Collateral Ratio', value: '110%', note: 'Below triggers liquidation' },
  { param: 'Critical Collateral Ratio', value: '150%', note: 'Below triggers recovery mode' },
  { param: 'Liquidation Reserve', value: '200 zUSD', note: 'Gas compensation for liquidators' },
  { param: 'Borrow Fee Range', value: '0.5% - 5%', note: 'Dynamic based on base rate' },
  { param: 'Redemption Fee Range', value: '0.5% - 5%', note: 'Dynamic based on base rate' },
  { param: 'Oracle Staleness Limit', value: '4 epochs', note: 'Fail-closed on stale price' },
];
