/**
 * Reference data for the zUSD stablecoin tab.
 * Models the backend zUSD system: vaults, stability pool, oracle, redemption.
 * Live values come from the network /api/zusd/* endpoints when reachable.
 *
 * Collateral asset: AGRS (Agoras) is the canonical production collateral.
 */

export const ZUSD_COLLATERAL = {
  canonicalSymbol: 'AGRS',
  testSymbol: 'AGRS',
  testnetNote: 'AGRS collateral backs zUSD vault operations.',
};

export const ZUSD_SUMMARY = {
  totalDebt: 0,
  totalCollateral: 0,
  globalCR: 0,
  stabilityPoolSize: 0,
  baseRateBps: 50,
  minCollRatio: 110,
  oraclePrice: 1.0,
  oracleAsset: ZUSD_COLLATERAL.testSymbol,
  oracleStale: false,
  lastOracleEpoch: 0,
  collateralAvailable: true,
};

export const ZUSD_OPERATIONS = [
  {
    id: 'mint',
    label: 'Mint zUSD',
    description: 'Deposit AGRS collateral to mint new zUSD stablecoins.',
    action: 'Deposit AGRS, receive zUSD',
    minCR: '110%',
  },
  {
    id: 'repay',
    label: 'Repay Debt',
    description: 'Burn zUSD to reduce vault debt and free collateral.',
    action: 'Burn zUSD, withdraw AGRS',
    minCR: 'N/A',
  },
  {
    id: 'redeem',
    label: 'Redeem',
    description: 'Exchange zUSD 1:1 for AGRS from the riskiest vaults.',
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

export const DEMO_VAULTS = [];

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
    detail: 'Net debt flow is additive: Δ(s₁ + s₂) = Δ(s₁) + Δ(s₂).',
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
  { param: 'Keeper Compensation', value: 'Configurable', note: 'Tau gas and liquidation incentives are live parameters' },
  { param: 'Borrow Fee Range', value: '0.5% - 5%', note: 'Dynamic based on base rate' },
  { param: 'Redemption Fee Range', value: '0.5% - 5%', note: 'Dynamic based on base rate' },
  { param: 'Oracle Staleness Limit', value: '4 epochs', note: 'Fail-closed on stale price' },
];
