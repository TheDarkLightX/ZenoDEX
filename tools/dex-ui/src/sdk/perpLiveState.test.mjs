import assert from 'node:assert/strict';
import { test } from 'node:test';
import {
  deriveWalletPosition,
  hasAuthoritativePositionDerivationFacts,
  marketWriteReadinessError,
  normalizeWalletMarket,
  normalizeWalletMarkets,
} from '../lib/perpLiveState.js';

const ACCOUNT_A = `0x${'11'.repeat(48)}`;
const ACCOUNT_B = `0x${'22'.repeat(48)}`;

function walletMarket(overrides = {}) {
  return {
    market_id: 'BTC-USD-PERP',
    kind: 'clearinghouse_2p_v1',
    quote_asset: 'zUSD',
    now_epoch: 9,
    oracle_last_update_epoch: 9,
    index_price_e8: 6_000_000_000_000,
    clearing_price_e8: 5_990_000_000_000,
    clearing_price_epoch: 9,
    maintenance_margin_bps: 500,
    account_a_pubkey: ACCOUNT_A,
    account_b_pubkey: ACCOUNT_B,
    position_base_a: 2,
    position_base_b: -2,
    collateral_e8_a: 1_000_000_000_000,
    collateral_e8_b: 1_000_000_000_000,
    ...overrides,
  };
}

test('perps live state keeps absent risk facts unknown and locks writes', () => {
  const result = normalizeWalletMarket(walletMarket());
  assert.equal(result.ok, true);
  assert.equal(result.market.epochPhase, 'Unknown');
  assert.equal(result.market.initialMarginBps, null);
  assert.equal(result.market.depegBufferBps, null);
  assert.equal(result.market.maxPositionAbs, null);
  assert.equal(result.market.maxOracleStalenessEpochs, null);
  assert.equal(result.market.breakerActive, null);
  assert.equal(result.market.authoritativeWriteFactsReady, false);
  assert.match(marketWriteReadinessError(result.market), /initialMarginBps/);
  assert.match(marketWriteReadinessError(result.market), /breakerActive/);
});

test('perps live state accepts only an explicitly complete authoritative market', () => {
  const result = normalizeWalletMarket(walletMarket({
    epoch_phase: 'Open',
    initial_margin_bps: 1_000,
    depeg_buffer_bps: 25,
    max_position_abs: 100,
    max_oracle_staleness_epochs: 4,
    breaker_active: false,
  }));
  assert.equal(result.ok, true);
  assert.equal(result.market.authoritativeWriteFactsReady, true);
  assert.equal(marketWriteReadinessError(result.market), null);
});

test('perps live state excludes unsupported and sparse market models with an explicit error', () => {
  const result = normalizeWalletMarkets([
    walletMarket(),
    walletMarket({ market_id: 'ETH-ISO', kind: 'isolated_v2' }),
    walletMarket({ market_id: 'SOL-NP', kind: 'clearinghouse_np_v1' }),
  ]);
  assert.deepEqual(result.markets.map((market) => market.id), ['BTC-USD-PERP']);
  assert.deepEqual(result.errors, [
    'unsupported_perps_market_kind:ETH-ISO:isolated_v2',
    'unsupported_perps_market_kind:SOL-NP:clearinghouse_np_v1',
  ]);
});

test('perps position derivation never substitutes the current index for entry price', () => {
  const raw = walletMarket();
  const normalized = normalizeWalletMarket(raw).market;
  const position = deriveWalletPosition(raw, ACCOUNT_A);
  assert.equal(position.entryPriceE8, null);
  assert.equal(position.collateralQuote, 10_000);
  assert.equal(position.authoritativePositionFactsReady, false);
  assert.equal(hasAuthoritativePositionDerivationFacts(normalized, position), false);
});

test('perps position derivation rejects lossy fractional quote conversion', () => {
  const position = deriveWalletPosition(walletMarket({
    collateral_e8_a: 100_000_001,
    entry_price_e8_a: 5_500_000_000_000,
  }), ACCOUNT_A);
  assert.equal(position.collateralE8, 100_000_001);
  assert.equal(position.collateralQuote, null);
  assert.equal(position.authoritativePositionFactsReady, false);
});
