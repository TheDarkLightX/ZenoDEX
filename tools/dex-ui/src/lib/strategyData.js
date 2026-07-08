/**
 * Demo data for the AutoTrader Strategy tab.
 * Mirrors the backend StrategyIR, policy guards, and decision certificate models.
 */

export const STRATEGY_TEMPLATES = [
  {
    id: 'dca',
    label: 'DCA',
    description: 'Dollar-cost average into a target asset over a fixed window.',
    allowedActions: ['place_swap_exact_in'],
    requiredParams: ['fixed_order_size', 'cadence_epochs', 'asset_in', 'asset_out'],
  },
  {
    id: 'limit_ladder',
    label: 'Limit Ladder',
    description: 'Place layered limit orders at decreasing price levels.',
    allowedActions: ['place_order_intent'],
    requiredParams: ['ladder_levels', 'per_level_size', 'asset_in', 'asset_out'],
  },
  {
    id: 'stop_loss',
    label: 'Stop Loss',
    description: 'Trigger a market sell when price drops below a threshold.',
    allowedActions: ['place_order_intent'],
    requiredParams: ['trigger_price', 'fixed_order_size', 'asset_in', 'asset_out'],
  },
  {
    id: 'take_profit',
    label: 'Take Profit',
    description: 'Trigger a market sell when price rises above a threshold.',
    allowedActions: ['place_order_intent'],
    requiredParams: ['trigger_price', 'fixed_order_size', 'asset_in', 'asset_out'],
  },
];

export const TAU_POLICY_GUARDS = [
  {
    id: 'signal_provenance',
    label: 'Signal Provenance',
    spec: 'autotrader_signal_provenance_guard_v1',
    detail: 'External signals must be signed by a registered source and pass freshness checks.',
    status: 'verified',
  },
  {
    id: 'ext_signal_registry',
    label: 'Signal Source Registry',
    spec: 'autotrader_external_signal_source_registry_guard_v1',
    detail: 'Only allow-listed data feeds can trigger strategy decisions.',
    status: 'verified',
  },
  {
    id: 'route_sanity',
    label: 'Route Economic Sanity',
    spec: 'autotrader_route_economic_sanity_guard_v1',
    detail: 'Compiled route must satisfy slippage bounds and minimum output.',
    status: 'verified',
  },
  {
    id: 'oracle_freshness',
    label: 'Oracle Freshness',
    spec: 'autotrader_oracle_freshness_guard_v1',
    detail: 'Oracle price must not be staler than max_oracle_staleness_epochs.',
    status: 'verified',
  },
  {
    id: 'execution_guard',
    label: 'Execution Guard',
    spec: 'autotrader_execution_guard_v1',
    detail: 'Prevents double-execution within the same epoch window.',
    status: 'verified',
  },
  {
    id: 'budget_guard',
    label: 'Budget Guard',
    spec: 'autotrader_budget_guard_v1',
    detail: 'Enforces per-order, per-window, and lifetime notional caps.',
    status: 'verified',
  },
  {
    id: 'session_state',
    label: 'Session State',
    spec: 'autotrader_session_state_guard_v1',
    detail: 'Session must be active and within valid epoch window.',
    status: 'verified',
  },
  {
    id: 'session_capability',
    label: 'Session Capability',
    spec: 'autotrader_session_capability_binding_guard_v1',
    detail: 'Session capability token must bind to the strategy and wallet.',
    status: 'verified',
  },
  {
    id: 'wallet_capability',
    label: 'Wallet Capability',
    spec: 'autotrader_wallet_capability_guard_v1',
    detail: 'Wallet must authorize the strategy to submit intents on its behalf.',
    status: 'verified',
  },
  {
    id: 'nonce_guard',
    label: 'Nonce Guard',
    spec: 'autotrader_nonce_guard_v1',
    detail: 'Each emitted intent nonce must be strictly monotonic (no replays).',
    status: 'verified',
  },
];

// Demo strategy fixtures — only shown when demoMode is active.
// Not shown by default in the UI to avoid confusing users with fake data.
export const DEMO_STRATEGIES = [
  {
    strategyId: 'strat_dca_eth_tau_01',
    template: 'dca',
    assetIn: 'TAU',
    assetOut: 'ETH',
    status: 'active',
    policyBackend: 'tau',
    notionalCaps: { perOrder: 500, perWindow: 2000, lifetime: 50000 },
    riskLimits: { maxSlippageBps: 100, maxOracleStale: 3, requireQuoteReceipts: true },
    window: { from: 1200, until: 2400, spacing: 10 },
    controls: { killSwitch: true, maxLiveOrders: 1 },
    executionHistory: [
      { epoch: 1210, action: 'place_swap_exact_in', amount: 500, status: 'settled' },
      { epoch: 1220, action: 'place_swap_exact_in', amount: 500, status: 'settled' },
      { epoch: 1230, action: 'place_swap_exact_in', amount: 500, status: 'settled' },
      { epoch: 1240, action: 'place_swap_exact_in', amount: 500, status: 'pending' },
    ],
    guardsPassed: 10,
    guardsTotal: 10,
    decisionModel: 'autotrader-binary-v1',
    lastDecision: { epoch: 1240, candidate: 'emit_compiled_intent', admissible: true },
  },
  {
    strategyId: 'strat_limit_zdex_zusd_02',
    template: 'limit_ladder',
    assetIn: 'zUSD',
    assetOut: 'ZDEX',
    status: 'active',
    policyBackend: 'tau',
    notionalCaps: { perOrder: 1000, perWindow: 5000, lifetime: 100000 },
    riskLimits: { maxSlippageBps: 50, maxOracleStale: 2, requireQuoteReceipts: true },
    window: { from: 1100, until: 3000, spacing: 5 },
    controls: { killSwitch: true, maxLiveOrders: 3 },
    executionHistory: [
      { epoch: 1105, action: 'place_order_intent', amount: 1000, status: 'settled' },
      { epoch: 1110, action: 'place_order_intent', amount: 1000, status: 'settled' },
    ],
    guardsPassed: 10,
    guardsTotal: 10,
    decisionModel: 'autotrader-binary-v1',
    lastDecision: { epoch: 1110, candidate: 'emit_compiled_intent', admissible: true },
  },
  {
    strategyId: 'strat_stop_loss_tasset0_03',
    template: 'stop_loss',
    assetIn: 'TASSET0',
    assetOut: 'zUSD',
    status: 'paused',
    policyBackend: 'local',
    notionalCaps: { perOrder: 2000, perWindow: 2000, lifetime: 10000 },
    riskLimits: { maxSlippageBps: 200, maxOracleStale: 1, requireQuoteReceipts: true },
    window: { from: 1000, until: 5000, spacing: 0 },
    controls: { killSwitch: false, maxLiveOrders: 1 },
    executionHistory: [],
    guardsPassed: 8,
    guardsTotal: 10,
    decisionModel: 'autotrader-binary-v1',
    lastDecision: { epoch: 0, candidate: 'no_op', admissible: true },
  },
];

export const FORMAL_PROOFS = [
  {
    id: 'binary_decision',
    label: 'Binary Decision Binding',
    file: 'ZenoDEXAutoTraderBinaryDecision.lean',
    status: 'proved',
  },
  {
    id: 'decision_binding',
    label: 'Decision Commitment Binding',
    file: 'ZenoDEXAutoTraderDecisionBinding.lean',
    status: 'proved',
  },
  {
    id: 'stage_certificate',
    label: 'Stage Certificate Correctness',
    file: 'ZenoDEXAutoTraderStageCertificate.lean',
    status: 'proved',
  },
  {
    id: 'live_release',
    label: 'Live Release Certificate',
    file: 'ZenoDEXAutoTraderLiveReleaseCertificate.lean',
    status: 'proved',
  },
];
