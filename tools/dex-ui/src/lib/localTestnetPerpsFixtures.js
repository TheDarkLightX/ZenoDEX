import { getRuntimeConfig } from './api.js';

function canonicalPubkey(value) {
  const text = String(value || '').trim().toLowerCase();
  if (!text) return '';
  return text.startsWith('0x') ? text : `0x${text}`;
}

function toTrader(raw) {
  if (!raw || typeof raw !== 'object' || Array.isArray(raw)) {
    return null;
  }
  const address = canonicalPubkey(raw.address || raw.pubkey || raw.publicKey);
  const privkey = String(raw.privkey || raw.privateKey || '').trim();
  if (!address || !privkey) {
    return null;
  }
  return {
    id: String(raw.id || raw.roleId || raw.role || address),
    label: String(raw.label || raw.name || raw.roleLabel || 'Test Trader').trim() || 'Test Trader',
    address,
    privkey,
    role: String(raw.role || raw.id || '').trim(),
  };
}

export function getLocalTestnetPerpsFixtures(runtimeConfig = getRuntimeConfig()) {
  const raw = runtimeConfig?.localTestnetPerpsFixtures;
  if (!raw || typeof raw !== 'object' || Array.isArray(raw)) {
    return { enabled: false, traders: [], warning: '', marketMode: '' };
  }
  const traders = Array.isArray(raw.traders) ? raw.traders.map(toTrader).filter(Boolean) : [];
  return {
    enabled: raw.enabled !== false && traders.length >= 2,
    traders,
    warning: String(raw.warning || '').trim(),
    marketMode: String(raw.marketMode || '').trim(),
  };
}

export function findLocalTestnetPerpsTrader(fixtures, walletAddress) {
  const address = canonicalPubkey(walletAddress);
  if (!address) return null;
  return (fixtures?.traders || []).find((trader) => trader.address === address) || null;
}

export function getLocalTestnetPerpsCounterpartySigning(fixtures, market) {
  const traders = Array.isArray(fixtures?.traders) ? fixtures.traders : [];
  const accountA = canonicalPubkey(market?.accountAPubkey);
  const accountB = canonicalPubkey(market?.accountBPubkey);
  if (!accountA || !accountB) {
    return null;
  }
  const traderA = traders.find((trader) => trader.address === accountA);
  const traderB = traders.find((trader) => trader.address === accountB);
  if (!traderA?.privkey || !traderB?.privkey) {
    return null;
  }
  return {
    account_a_privkey: traderA.privkey,
    account_b_privkey: traderB.privkey,
  };
}

export function buildLocalTestnetPerpsTraderWallet(trader, { chainId }) {
  if (!trader) return null;
  return {
    address: trader.address,
    privkey: trader.privkey,
    chainId: String(chainId || 'zeno-ledger-localtest-v0'),
    signerProvider: 'local-testnet-perps-fixture',
    browserLastResort: true,
    localTestnetGenerated: true,
    testnetFixtureTrader: true,
    fixtureRole: trader.role || trader.id,
    fixtureLabel: trader.label,
    balance: {},
  };
}
