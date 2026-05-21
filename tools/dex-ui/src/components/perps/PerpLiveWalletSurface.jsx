import { useEffect, useMemo, useRef, useState } from 'react';
import {
  apiBuildPerpsOracleBridge,
  apiGetPerpsWalletStatus,
  apiPreparePerpsWallet,
  apiSubmitPerpsWallet,
} from '../../lib/api.js';

const EMPTY_FORM = {
  action: 'init_market_2p',
  market_id: 'perp:ch2p:local',
  quote_asset: '',
  account_a_pubkey: '',
  account_b_pubkey: '',
  account_pubkey: '',
  account_a_privkey: '',
  account_b_privkey: '',
  account_privkey: '',
  operator_privkey: '',
  oracle_pubkey: '',
  oracle_privkey: '',
  amount: '1000',
  delta: '1',
  price_e8: '100000000',
  oracle_adapter_bridge: '',
  new_position_base_a: '1',
  new_position_base_b: '-1',
  fraction_bps: '2500',
  tx_fee_limit: '0',
  deadline: '',
  use_oracle_fixture: false,
};

const ACTIONS = [
  ['init_market_2p', 'Init 2P Market'],
  ['deposit_collateral', 'Deposit Collateral'],
  ['withdraw_collateral', 'Withdraw Collateral'],
  ['set_position_pair', 'Set Position Pair'],
  ['advance_epoch', 'Advance Epoch'],
  ['publish_clearing_price', 'Publish Price'],
  ['settle_epoch', 'Settle Epoch'],
  ['partial_liquidate', 'Partial Liquidate'],
];

function readSmokeConfig() {
  if (typeof window === 'undefined') {
    return null;
  }
  const params = new URLSearchParams(window.location.search);
  if (params.get('zenodexUiSmokePerpsWallet') !== '1') {
    return null;
  }
  return {
    action: params.get('perpsWalletAction') || 'init_market_2p',
    market_id: params.get('marketId') || params.get('market_id') || 'perp:ch2p:ui',
    quote_asset: params.get('quoteAsset') || params.get('quote_asset') || '',
    account_a_pubkey: params.get('accountAPubkey') || params.get('account_a_pubkey') || '',
    account_b_pubkey: params.get('accountBPubkey') || params.get('account_b_pubkey') || '',
    account_pubkey: params.get('accountPubkey') || params.get('account_pubkey') || '',
    account_a_privkey: params.get('accountAPrivkey') || params.get('account_a_privkey') || '',
    account_b_privkey: params.get('accountBPrivkey') || params.get('account_b_privkey') || '',
    account_privkey: params.get('accountPrivkey') || params.get('account_privkey') || '',
    operator_privkey: params.get('operatorPrivkey') || params.get('operator_privkey') || '',
    oracle_pubkey: params.get('oraclePubkey') || params.get('oracle_pubkey') || '',
    oracle_privkey: params.get('oraclePrivkey') || params.get('oracle_privkey') || '',
    amount: params.get('amount') || '1000',
    delta: params.get('delta') || '1',
    price_e8: params.get('priceE8') || params.get('price_e8') || '100000000',
    oracle_adapter_bridge: params.get('oracleAdapterBridge') || params.get('oracle_adapter_bridge') || '',
    new_position_base_a: params.get('positionA') || params.get('new_position_base_a') || '1',
    new_position_base_b: params.get('positionB') || params.get('new_position_base_b') || '-1',
    fraction_bps: params.get('fractionBps') || params.get('fraction_bps') || '2500',
    tx_fee_limit: params.get('perpsTxFeeLimit') || params.get('txFeeLimit') || params.get('tx_fee_limit') || '0',
    deadline: params.get('perpsDeadline') || params.get('deadline') || '',
    use_oracle_fixture: params.get('perpsUseOracleFixture') === '1'
      || params.get('useOracleFixture') === '1'
      || params.get('oracleFixture') === '1',
  };
}

function parseIntOrNull(raw) {
  const value = Number.parseInt(String(raw || '').trim(), 10);
  return Number.isFinite(value) ? value : null;
}

function actionSupportsOracleFixture(action) {
  return action === 'settle_epoch' || action === 'partial_liquidate';
}

function buildPayload(form) {
  const action = form.action;
  const payload = {
    action,
    market_id: form.market_id.trim(),
  };
  const deadline = parseIntOrNull(form.deadline);
  if (deadline != null && deadline >= 0) {
    payload.deadline = deadline;
  }
  if (String(form.tx_fee_limit || '').trim()) {
    payload.tx_fee_limit = String(form.tx_fee_limit).trim();
  }
  if (action === 'init_market_2p' || action === 'set_position_pair') {
    if (form.account_a_pubkey.trim()) payload.account_a_pubkey = form.account_a_pubkey.trim();
    if (form.account_b_pubkey.trim()) payload.account_b_pubkey = form.account_b_pubkey.trim();
    if (form.account_a_privkey.trim()) payload.account_a_privkey = form.account_a_privkey.trim();
    if (form.account_b_privkey.trim()) payload.account_b_privkey = form.account_b_privkey.trim();
  }
  if (action === 'init_market_2p' && form.quote_asset.trim()) {
    payload.quote_asset = form.quote_asset.trim();
  }
  if (action === 'deposit_collateral' || action === 'withdraw_collateral') {
    if (form.account_pubkey.trim()) payload.account_pubkey = form.account_pubkey.trim();
    if (form.account_privkey.trim()) payload.account_privkey = form.account_privkey.trim();
    payload.amount = parseIntOrNull(form.amount) ?? 0;
  }
  if (action === 'partial_liquidate') {
    if (form.account_pubkey.trim()) payload.account_pubkey = form.account_pubkey.trim();
    if (form.account_privkey.trim()) payload.account_privkey = form.account_privkey.trim();
    payload.fraction_bps = parseIntOrNull(form.fraction_bps) ?? 0;
    if (form.oracle_adapter_bridge.trim()) {
      payload.oracle_adapter_bridge = form.oracle_adapter_bridge.trim();
    }
  }
  if (action === 'advance_epoch') {
    payload.delta = parseIntOrNull(form.delta) ?? 1;
    if (form.operator_privkey.trim()) payload.operator_privkey = form.operator_privkey.trim();
  }
  if (action === 'publish_clearing_price') {
    payload.price_e8 = parseIntOrNull(form.price_e8) ?? 0;
    if (form.oracle_pubkey.trim()) payload.oracle_pubkey = form.oracle_pubkey.trim();
    if (form.oracle_privkey.trim()) payload.oracle_privkey = form.oracle_privkey.trim();
  }
  if (action === 'settle_epoch') {
    if (form.operator_privkey.trim()) payload.operator_privkey = form.operator_privkey.trim();
    if (form.oracle_adapter_bridge.trim()) {
      payload.oracle_adapter_bridge = form.oracle_adapter_bridge.trim();
    }
  }
  if (action === 'set_position_pair') {
    payload.new_position_base_a = parseIntOrNull(form.new_position_base_a) ?? 0;
    payload.new_position_base_b = parseIntOrNull(form.new_position_base_b) ?? 0;
  }
  return payload;
}

function PerpLiveWalletSurface() {
  const [status, setStatus] = useState(null);
  const [statusError, setStatusError] = useState('');
  const [form, setForm] = useState(() => readSmokeConfig() || EMPTY_FORM);
  const [result, setResult] = useState(null);
  const [error, setError] = useState('');
  const [oracleFixture, setOracleFixture] = useState(null);
  const [busy, setBusy] = useState(false);
  const smokeRan = useRef(false);

  const needsTwoParty = form.action === 'init_market_2p' || form.action === 'set_position_pair';
  const needsCollateral = form.action === 'deposit_collateral' || form.action === 'withdraw_collateral';
  const needsAccountBound = needsCollateral || form.action === 'partial_liquidate';
  const needsPosition = form.action === 'set_position_pair';
  const needsOperator = form.action === 'advance_epoch' || form.action === 'settle_epoch';
  const needsOracle = form.action === 'publish_clearing_price';

  async function loadStatus() {
    try {
      const payload = await apiGetPerpsWalletStatus({ timeoutMs: 8000 });
      setStatus(payload?.status || null);
      setStatusError('');
    } catch (err) {
      setStatus(null);
      setStatusError(err?.message || 'status_unavailable');
    }
  }

  useEffect(() => {
    loadStatus();
  }, []);

  async function handlePrepare() {
    setBusy(true);
    setError('');
    try {
      const payload = await apiPreparePerpsWallet(buildPayload(form), { timeoutMs: 15000 });
      setResult(payload);
    } catch (err) {
      setResult(null);
      setError(err?.message || 'prepare_failed');
    } finally {
      setBusy(false);
    }
  }

  async function handleSubmit() {
    setBusy(true);
    setError('');
    try {
      const payload = await apiSubmitPerpsWallet(buildPayload(form), { timeoutMs: 20000 });
      setResult(payload);
      await loadStatus();
    } catch (err) {
      setResult(null);
      setError(err?.message || 'submit_failed');
    } finally {
      setBusy(false);
    }
  }

  async function buildOracleFixturePayload(sourceForm) {
    const action = sourceForm.action === 'partial_liquidate' ? 'partial_liquidate' : 'settle_epoch';
    const request = {
      action,
      market_id: sourceForm.market_id.trim(),
    };
    if (action === 'partial_liquidate') {
      if (sourceForm.account_pubkey.trim()) request.account_pubkey = sourceForm.account_pubkey.trim();
      if (sourceForm.account_privkey.trim()) request.account_privkey = sourceForm.account_privkey.trim();
      request.fraction_bps = parseIntOrNull(sourceForm.fraction_bps) ?? 0;
    }
    const payload = await apiBuildPerpsOracleBridge(
      request,
      { timeoutMs: 15000 },
    );
    const bridgeText = JSON.stringify(payload.bridge, null, 2);
    setOracleFixture(payload);
    setForm((current) => ({ ...current, ...sourceForm, oracle_adapter_bridge: bridgeText }));
    return { ...sourceForm, oracle_adapter_bridge: bridgeText };
  }

  async function handleUseOracleFixture() {
    setBusy(true);
    setError('');
    try {
      await buildOracleFixturePayload(form);
    } catch (err) {
      setOracleFixture(null);
      setError(err?.message || 'oracle_fixture_failed');
    } finally {
      setBusy(false);
    }
  }

  useEffect(() => {
    const smoke = readSmokeConfig();
    if (!smoke || smokeRan.current || busy) {
      return;
    }
    if (status?.node_reachable !== true) {
      return;
    }
    smokeRan.current = true;
    setForm((current) => ({ ...current, ...smoke }));
    async function runSmoke() {
      let nextForm = { ...EMPTY_FORM, ...smoke };
      if (actionSupportsOracleFixture(nextForm.action) && nextForm.use_oracle_fixture) {
        nextForm = await buildOracleFixturePayload(nextForm);
      }
      const payload = await apiSubmitPerpsWallet(buildPayload(nextForm), { timeoutMs: 20000 });
      setResult(payload);
      setError('');
      await loadStatus();
      return payload;
    }
    void runSmoke()
      .then((payload) => {
        if (payload) {
          setResult(payload);
        }
      })
      .catch((err) => {
        setResult(null);
        setError(err?.message || 'submit_failed');
      });
  }, [busy, status]);

  const preflight = result?.report?.preflight;
  const markets = useMemo(() => status?.markets || result?.post_submit?.markets || [], [status, result]);
  const selectedMarket = useMemo(
    () => markets.find((market) => market?.market_id === form.market_id.trim()) || null,
    [markets, form.market_id],
  );
  const selectedAccount = useMemo(() => {
    const accounts = Array.isArray(selectedMarket?.accounts) ? selectedMarket.accounts : [];
    if (!accounts.length) return null;
    const accountPubkey = form.account_pubkey.trim().toLowerCase();
    if (accountPubkey) {
      const match = accounts.find((account) => String(account?.account_pubkey || '').toLowerCase() === accountPubkey);
      if (match) return match;
    }
    return accounts[0];
  }, [selectedMarket, form.account_pubkey]);
  const feeCovered = result?.transport?.fee_limit_native_balance_ok;

  return (
    <section className="perp-live-wallet panel" aria-label="Live perps wallet">
      <div className="perp-live-wallet-header">
        <div>
          <h3 className="perp-section-title">Live Perps Wallet</h3>
          <p className="perp-live-wallet-copy">
            Stream-8 clearinghouse transactions with BLS-signed market init and position updates.
          </p>
        </div>
        <span className="perp-posture-chip">{status?.node_reachable ? 'Tau node connected' : 'Tau node required'}</span>
      </div>

      <div className="perp-live-wallet-grid">
        <div className="perp-live-wallet-meta">
          <div><span>Chain</span><span>{status?.chain_id || 'unknown'}</span></div>
          <div><span>Stream</span><span>{result?.transport?.stream_key || '8'}</span></div>
          <div><span>Markets</span><span>{status?.market_count ?? markets.length ?? 0}</span></div>
          <div><span>Signing</span><span>{status?.allow_local_signing ? 'enabled' : 'prepare only'}</span></div>
          <div><span>Oracle Bridge</span><span>{status?.require_oracle_adapter_for_clearinghouse_settle_epoch ? 'required' : 'optional'}</span></div>
          <div><span>Isolated</span><span>{status?.allow_isolated_markets ? 'enabled' : 'disabled'}</span></div>
        </div>

        <div className="perp-live-wallet-form">
          <label className="label" htmlFor="perps-wallet-action">Action</label>
          <select
            id="perps-wallet-action"
            className="input"
            value={form.action}
            onChange={(event) => setForm((current) => ({ ...current, action: event.target.value }))}
          >
            {ACTIONS.map(([value, label]) => (
              <option key={value} value={value}>{label}</option>
            ))}
          </select>

          <label className="label" htmlFor="perps-wallet-market">Market ID</label>
          <input
            id="perps-wallet-market"
            className="input"
            value={form.market_id}
            onChange={(event) => setForm((current) => ({ ...current, market_id: event.target.value }))}
            placeholder="perp:ch2p:..."
          />

          <label className="label" htmlFor="perps-wallet-fee-limit">Tau Fee Limit</label>
          <input
            id="perps-wallet-fee-limit"
            className="input"
            inputMode="numeric"
            value={form.tx_fee_limit}
            onChange={(event) => setForm((current) => ({ ...current, tx_fee_limit: event.target.value }))}
            placeholder="native units"
          />

          {form.action === 'init_market_2p' ? (
            <>
              <label className="label" htmlFor="perps-wallet-quote">Quote Asset</label>
              <input
                id="perps-wallet-quote"
                className="input"
                value={form.quote_asset}
                onChange={(event) => setForm((current) => ({ ...current, quote_asset: event.target.value }))}
                placeholder="default zUSD asset"
              />
            </>
          ) : null}

          {needsTwoParty ? (
            <>
              <label className="label" htmlFor="perps-wallet-a-priv">Account A Privkey</label>
              <input
                id="perps-wallet-a-priv"
                className="input"
                value={form.account_a_privkey}
                onChange={(event) => setForm((current) => ({ ...current, account_a_privkey: event.target.value }))}
                placeholder="local test key"
              />
              <label className="label" htmlFor="perps-wallet-b-priv">Account B Privkey</label>
              <input
                id="perps-wallet-b-priv"
                className="input"
                value={form.account_b_privkey}
                onChange={(event) => setForm((current) => ({ ...current, account_b_privkey: event.target.value }))}
                placeholder="local test key"
              />
            </>
          ) : null}

          {needsAccountBound ? (
            <>
              <label className="label" htmlFor="perps-wallet-account-priv">Account Privkey</label>
              <input
                id="perps-wallet-account-priv"
                className="input"
                value={form.account_privkey}
                onChange={(event) => setForm((current) => ({ ...current, account_privkey: event.target.value }))}
                placeholder="local test key"
              />
              {needsCollateral ? (
                <>
                  <label className="label" htmlFor="perps-wallet-amount">Amount</label>
                  <input
                    id="perps-wallet-amount"
                    className="input"
                    inputMode="numeric"
                    value={form.amount}
                    onChange={(event) => setForm((current) => ({ ...current, amount: event.target.value }))}
                  />
                </>
              ) : null}
              {form.action === 'partial_liquidate' ? (
                <>
                  <label className="label" htmlFor="perps-wallet-fraction">Liquidation Fraction Bps (0 auto)</label>
                  <input
                    id="perps-wallet-fraction"
                    className="input"
                    inputMode="numeric"
                    value={form.fraction_bps}
                    onChange={(event) => setForm((current) => ({ ...current, fraction_bps: event.target.value }))}
                  />
                  <label className="label" htmlFor="perps-wallet-liquidation-oracle-bridge">Oracle Adapter Bridge</label>
                  <textarea
                    id="perps-wallet-liquidation-oracle-bridge"
                    className="input perp-live-wallet-textarea"
                    value={form.oracle_adapter_bridge}
                    onChange={(event) => setForm((current) => ({ ...current, oracle_adapter_bridge: event.target.value }))}
                    placeholder="optional JSON bridge"
                  />
                  <button
                    className="btn btn-secondary"
                    type="button"
                    onClick={handleUseOracleFixture}
                    disabled={busy || !form.market_id.trim() || (!form.account_pubkey.trim() && !form.account_privkey.trim())}
                  >
                    Build Oracle Bridge
                  </button>
                </>
              ) : null}
            </>
          ) : null}

          {needsOperator ? (
            <>
              <label className="label" htmlFor="perps-wallet-operator-priv">Operator Privkey</label>
              <input
                id="perps-wallet-operator-priv"
                className="input"
                value={form.operator_privkey}
                onChange={(event) => setForm((current) => ({ ...current, operator_privkey: event.target.value }))}
                placeholder="local test key"
              />
            </>
          ) : null}

          {form.action === 'advance_epoch' ? (
            <>
              <label className="label" htmlFor="perps-wallet-delta">Delta</label>
              <input
                id="perps-wallet-delta"
                className="input"
                inputMode="numeric"
                value={form.delta}
                onChange={(event) => setForm((current) => ({ ...current, delta: event.target.value }))}
              />
            </>
          ) : null}

          {needsOracle ? (
            <>
              <label className="label" htmlFor="perps-wallet-oracle-priv">Oracle Privkey</label>
              <input
                id="perps-wallet-oracle-priv"
                className="input"
                value={form.oracle_privkey}
                onChange={(event) => setForm((current) => ({ ...current, oracle_privkey: event.target.value }))}
                placeholder="local test key"
              />
              <label className="label" htmlFor="perps-wallet-price">Price E8</label>
              <input
                id="perps-wallet-price"
                className="input"
                inputMode="numeric"
                value={form.price_e8}
                onChange={(event) => setForm((current) => ({ ...current, price_e8: event.target.value }))}
              />
            </>
          ) : null}

          {form.action === 'settle_epoch' ? (
            <>
              <label className="label" htmlFor="perps-wallet-oracle-bridge">Oracle Adapter Bridge</label>
              <textarea
                id="perps-wallet-oracle-bridge"
                className="input perp-live-wallet-textarea"
                value={form.oracle_adapter_bridge}
                onChange={(event) => setForm((current) => ({ ...current, oracle_adapter_bridge: event.target.value }))}
                placeholder="optional JSON bridge"
              />
              <button
                className="btn btn-secondary"
                type="button"
                onClick={handleUseOracleFixture}
                disabled={busy || !form.market_id.trim()}
              >
                Build Oracle Bridge
              </button>
            </>
          ) : null}

          {needsPosition ? (
            <div className="perp-live-wallet-two">
              <label className="label" htmlFor="perps-wallet-pos-a">Position A</label>
              <input
                id="perps-wallet-pos-a"
                className="input"
                inputMode="numeric"
                value={form.new_position_base_a}
                onChange={(event) => setForm((current) => ({ ...current, new_position_base_a: event.target.value }))}
              />
              <label className="label" htmlFor="perps-wallet-pos-b">Position B</label>
              <input
                id="perps-wallet-pos-b"
                className="input"
                inputMode="numeric"
                value={form.new_position_base_b}
                onChange={(event) => setForm((current) => ({ ...current, new_position_base_b: event.target.value }))}
              />
            </div>
          ) : null}

          <div className="perp-live-wallet-actions">
            <button className="btn btn-secondary" type="button" onClick={handlePrepare} disabled={busy}>
              Prepare
            </button>
            <button className="btn btn-primary" type="button" onClick={handleSubmit} disabled={busy}>
              Submit
            </button>
            <button className="btn btn-ghost" type="button" onClick={loadStatus} disabled={busy}>
              Refresh
            </button>
          </div>
        </div>
      </div>

      {statusError ? <p className="perp-live-wallet-error">Status error: {statusError}</p> : null}
      {error ? <p className="perp-live-wallet-error">Action error: {error}</p> : null}
      {selectedMarket ? (
        <div className="perp-live-wallet-result" aria-label="Selected perps market summary">
          <span>market {selectedMarket.market_id}</span>
          <span>quote A {selectedMarket.account_a_quote_balance ?? 0}</span>
          <span>quote B {selectedMarket.account_b_quote_balance ?? 0}</span>
          <span>posted A {selectedMarket.collateral_e8_a ?? 0}</span>
          <span>posted B {selectedMarket.collateral_e8_b ?? 0}</span>
          {selectedMarket.account_count != null ? <span>accounts {selectedMarket.account_count}</span> : null}
          {selectedAccount?.position_base != null ? <span>position {selectedAccount.position_base}</span> : null}
          {selectedAccount?.collateral_quote != null ? <span>collateral {selectedAccount.collateral_quote}</span> : null}
          {selectedAccount?.liquidated_this_step != null ? (
            <span>isolated liquidated {selectedAccount.liquidated_this_step ? 'yes' : 'no'}</span>
          ) : null}
        </div>
      ) : null}
      {result ? (
        <div className="perp-live-wallet-result" role="status">
          <span>{result.submission ? 'submit accepted' : 'prepare ready'}</span>
          <span>{preflight?.ok ? 'preflight ok' : `preflight failed: ${preflight?.error || 'unknown'}`}</span>
          <span>fee limit {result.transport?.tx_fee_limit ?? '0'}</span>
          <span>fee covered {feeCovered == null ? 'unknown' : feeCovered ? 'yes' : 'no'}</span>
          <span>{result.transport?.app_hash || 'no app hash'}</span>
          {oracleFixture?.target?.profile_id ? <span>oracle bridge {oracleFixture.target.profile_id}</span> : null}
          {selectedMarket?.liquidated_this_step != null ? (
            <span>liquidated {selectedMarket.liquidated_this_step ? 'yes' : 'no'}</span>
          ) : null}
          {selectedMarket?.fee_pool_e8 != null ? <span>fee pool {selectedMarket.fee_pool_e8}</span> : null}
          {selectedMarket?.position_base_a != null && selectedMarket?.position_base_b != null ? (
            <span>positions {selectedMarket.position_base_a}/{selectedMarket.position_base_b}</span>
          ) : null}
          {result?.report?.operation?.action === 'partial_liquidate' ? (
            <span>partial liquidation fraction {result.report.operation.fraction_bps} bps</span>
          ) : null}
          {result.transport?.fee_limit_warning ? <span>{result.transport.fee_limit_warning}</span> : null}
        </div>
      ) : null}
    </section>
  );
}

export default PerpLiveWalletSurface;
