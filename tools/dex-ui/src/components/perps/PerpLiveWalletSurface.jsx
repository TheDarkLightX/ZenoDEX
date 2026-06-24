import { useEffect, useMemo, useRef, useState } from 'react';
import {
  apiBuildPerpsOracleBridge,
  apiGetPerpsWalletStatus,
  apiGetZenoOracleDashboard,
  apiInspectPerpsOracleBridge,
  apiMintPerpsWalletTestnetFaucet,
  apiPreparePerpsWallet,
  apiSubmitPerpsWallet,
  isLocalTestnetDeployment,
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
  signed_tau_tx_payload: '',
  new_position_base_a: '1',
  new_position_base_b: '-1',
  fraction_bps: '2500',
  tx_fee_limit: '0',
  deadline: '',
  zk_proof_json: '',
  use_oracle_fixture: false,
};

const ACTIONS = [
  ['init_market_2p', 'Init 2P Market'],
  ['deposit_collateral', 'Deposit Collateral'],
  ['withdraw_collateral', 'Withdraw Collateral'],
  ['set_position_pair', 'Set Position Pair'],
  ['advance_epoch', 'Advance Epoch'],
  ['publish_clearing_price', 'Publish Price'],
  ['settle_epoch', 'Epoch Settlement'],
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
    account_a_privkey: readLocalSmokeFragmentSecret(['accountAPrivkey', 'account_a_privkey']),
    account_b_privkey: readLocalSmokeFragmentSecret(['accountBPrivkey', 'account_b_privkey']),
    account_privkey: readLocalSmokeFragmentSecret(['accountPrivkey', 'account_privkey']),
    operator_privkey: readLocalSmokeFragmentSecret(['operatorPrivkey', 'operator_privkey']),
    oracle_pubkey: params.get('oraclePubkey') || params.get('oracle_pubkey') || '',
    oracle_privkey: readLocalSmokeFragmentSecret(['oraclePrivkey', 'oracle_privkey']),
    amount: params.get('amount') || '1000',
    delta: params.get('delta') || '1',
    price_e8: params.get('priceE8') || params.get('price_e8') || '100000000',
    oracle_adapter_bridge: params.get('oracleAdapterBridge') || params.get('oracle_adapter_bridge') || '',
    signed_tau_tx_payload: params.get('signedTauTxPayload') || params.get('signed_tau_tx_payload') || '',
    new_position_base_a: params.get('positionA') || params.get('new_position_base_a') || '1',
    new_position_base_b: params.get('positionB') || params.get('new_position_base_b') || '-1',
    fraction_bps: params.get('fractionBps') || params.get('fraction_bps') || '2500',
    tx_fee_limit: params.get('perpsTxFeeLimit') || params.get('txFeeLimit') || params.get('tx_fee_limit') || '0',
    deadline: params.get('perpsDeadline') || params.get('deadline') || '',
    zk_proof_json: params.get('perpsZkProofJson') || params.get('zkProofJson') || '',
    use_oracle_fixture: params.get('perpsUseOracleFixture') === '1'
      || params.get('useOracleFixture') === '1'
      || params.get('oracleFixture') === '1',
    load_oracle_evidence: params.get('perpsLoadOracleEvidence') === '1'
      || params.get('loadOracleEvidence') === '1',
  };
}

function readLocalSmokeFragmentSecret(names) {
  if (!isLocalTestnetDeployment() || typeof window === 'undefined') {
    return '';
  }
  const fragment = String(window.location.hash || '').replace(/^#/, '');
  if (!fragment) {
    return '';
  }
  const fragmentParams = new URLSearchParams(fragment);
  for (const name of Array.isArray(names) ? names : [names]) {
    const value = fragmentParams.get(name);
    if (value) {
      return value;
    }
  }
  return '';
}

function parseIntOrNull(raw) {
  const value = Number.parseInt(String(raw || '').trim(), 10);
  return Number.isFinite(value) ? value : null;
}

function parseJsonObject(raw, label) {
  const text = String(raw || '').trim();
  if (!text) return null;
  try {
    const parsed = JSON.parse(text);
    if (!parsed || typeof parsed !== 'object' || Array.isArray(parsed)) {
      throw new Error(`${label}_must_be_object`);
    }
    return parsed;
  } catch (err) {
    throw new Error(`${label}_invalid_json: ${err?.message || err}`);
  }
}

function actionSupportsOracleFixture(action) {
  return action === 'settle_epoch' || action === 'partial_liquidate';
}

function expectedOracleActionKind(action) {
  if (action === 'settle_epoch') return 'settle_epoch';
  if (action === 'partial_liquidate') return 'liquidate_account';
  return '';
}

function hasLocalSigningCredential(form) {
  return Boolean(
    form.signed_tau_tx_payload.trim() ||
    form.account_a_privkey.trim() ||
    form.account_b_privkey.trim() ||
    form.account_privkey.trim() ||
    form.operator_privkey.trim() ||
    form.oracle_privkey.trim(),
  );
}

function compactId(value) {
  if (!value) return 'none';
  const text = String(value);
  if (text.length <= 18) return text;
  return `${text.slice(0, 10)}...${text.slice(-6)}`;
}

function valueOrNA(value) {
  return value == null || value === '' ? 'N/A' : value;
}

function oracleDashboardCandidates(snapshot, targetAction = '') {
  const authorizations = Array.isArray(snapshot?.recent_authorizations) ? snapshot.recent_authorizations : [];
  const reads = Array.isArray(snapshot?.recent_accepted_reads) ? snapshot.recent_accepted_reads : [];
  const aggregates = Array.isArray(snapshot?.recent_aggregates) ? snapshot.recent_aggregates : [];
  const candidates = [
    ...authorizations.map((bundle) => {
      const auth = bundle?.authorization || {};
      return {
        id: bundle?.authorization_id || auth?.authorization_id || auth?.action_id,
        kind: 'authorization',
        consumer: auth?.consumer_module || 'consumer',
        action: auth?.action_kind || 'action',
        queryId: auth?.query_id || '',
        valueE8: auth?.value_e8,
        evidenceClass: auth?.evidence_class || 'O3',
        epoch: auth?.observed_epoch,
      };
    }),
    ...reads.map((read) => ({
      id: read?.read_id || read?.aggregate_id,
      kind: 'accepted read',
      consumer: read?.consumer_module || 'consumer',
      action: read?.profile_id || 'read',
      queryId: read?.query_id || '',
      valueE8: read?.value_e8,
      evidenceClass: read?.evidence_class || 'O3',
      epoch: read?.observed_epoch,
    })),
    ...aggregates.map((aggregate) => ({
      id: aggregate?.aggregate_id,
      kind: 'aggregate',
      consumer: 'oracle',
      action: 'aggregate',
      queryId: aggregate?.query_id || '',
      valueE8: aggregate?.value_e8,
      evidenceClass: aggregate?.evidence_class || 'O3',
      epoch: aggregate?.observed_epoch,
    })),
  ].filter((candidate) => candidate.id);
  if (!targetAction) {
    return candidates;
  }
  return [...candidates].sort((left, right) => {
    const leftMatch = left.action === targetAction ? 1 : 0;
    const rightMatch = right.action === targetAction ? 1 : 0;
    return rightMatch - leftMatch;
  });
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
  const zkProof = parseJsonObject(form.zk_proof_json, 'zk_proof_json');
  if (zkProof) {
    payload.zk_proof = zkProof;
  }
  if (form.signed_tau_tx_payload.trim()) {
    payload.signed_tau_tx_payload = form.signed_tau_tx_payload.trim();
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
  const [result, setResult] = useState(() => {
    if (typeof window !== 'undefined') {
      return window.__zenodex_perps_smoke_result || null;
    }
    return null;
  });
  const [error, setError] = useState('');
  const [oracleFixture, setOracleFixture] = useState(null);
  const [oracleInspection, setOracleInspection] = useState(null);
  const [oracleEvidence, setOracleEvidence] = useState(null);
  const [selectedOracleEvidence, setSelectedOracleEvidence] = useState(null);
  const [faucetResult, setFaucetResult] = useState(null);
  const [busy, setBusy] = useState(false);
  const [faucetBusy, setFaucetBusy] = useState(false);
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

  async function handleFundTestnetQuote() {
    const targetPubkey = localFaucetTargetPubkey();
    const quoteAsset = localFaucetQuoteAsset();
    const signerPrivkey =
      form.operator_privkey.trim() ||
      form.account_privkey.trim() ||
      form.account_a_privkey.trim() ||
      form.account_b_privkey.trim();
    if (!targetPubkey || !quoteAsset) {
      setError('faucet_target_unavailable');
      return;
    }
    if (!signerPrivkey) {
      setError('faucet_signer_required');
      return;
    }
    setFaucetBusy(true);
    setError('');
    try {
      const amount = Math.max(parseIntOrNull(form.amount) ?? 0, 1000);
      const payload = await apiMintPerpsWalletTestnetFaucet(
        {
          to_pubkey: targetPubkey,
          asset: quoteAsset,
          amount,
          signer_privkey: signerPrivkey,
          deadline: parseIntOrNull(form.deadline) || Math.floor(Date.now() / 1000) + 3600,
          tx_fee_limit: form.tx_fee_limit || '0',
        },
        { timeoutMs: 15000 },
      );
      setFaucetResult(payload);
      await loadStatus();
    } catch (err) {
      setFaucetResult(null);
      setError(err?.message || 'faucet_failed');
    } finally {
      setFaucetBusy(false);
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
    const inspection = await apiInspectPerpsOracleBridge(
      { oracle_adapter_bridge: payload.bridge },
      { timeoutMs: 15000 },
    );
    setOracleInspection(inspection);
    return { ...sourceForm, oracle_adapter_bridge: bridgeText };
  }

  async function inspectOracleBridgePayload(sourceForm) {
    const bridgeText = sourceForm.oracle_adapter_bridge.trim();
    if (!bridgeText) {
      throw new Error('oracle_adapter_bridge_required');
    }
    const inspection = await apiInspectPerpsOracleBridge(
      { oracle_adapter_bridge: bridgeText },
      { timeoutMs: 15000 },
    );
    setOracleInspection(inspection);
    return inspection;
  }

  async function loadOracleEvidenceCandidates(sourceForm = form) {
    const snapshot = await apiGetZenoOracleDashboard({ timeoutMs: 10000 });
    const targetAction = expectedOracleActionKind(sourceForm.action);
    const candidates = oracleDashboardCandidates(snapshot, targetAction);
    const selected = candidates.find((candidate) => candidate.action === targetAction) || candidates[0] || null;
    const payload = {
      ok: snapshot?.ok === true,
      production_authority: snapshot?.production_authority === true,
      replay_ok: snapshot?.summary?.replay_ok === true,
      accepted_read_count: snapshot?.summary?.accepted_read_count ?? 0,
      authorization_count: snapshot?.summary?.authorization_count ?? 0,
      aggregate_count: snapshot?.summary?.aggregate_count ?? candidates.filter((candidate) => candidate.kind === 'aggregate').length,
      target_action: targetAction,
      candidates,
    };
    setOracleEvidence(payload);
    setSelectedOracleEvidence(selected);
    return payload;
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

  async function handleInspectOracleBridge() {
    setBusy(true);
    setError('');
    try {
      await inspectOracleBridgePayload(form);
    } catch (err) {
      setOracleInspection(null);
      setError(err?.message || 'oracle_bridge_inspect_failed');
    } finally {
      setBusy(false);
    }
  }

  async function handleLoadOracleEvidence() {
    setBusy(true);
    setError('');
    try {
      await loadOracleEvidenceCandidates(form);
    } catch (err) {
      setOracleEvidence(null);
      setSelectedOracleEvidence(null);
      setError(err?.message || 'oracle_evidence_load_failed');
    } finally {
      setBusy(false);
    }
  }

  useEffect(() => {
    const smoke = readSmokeConfig();
    if (!smoke || smokeRan.current || busy || (typeof window !== 'undefined' && window.__zenodex_perps_smoke_ran)) {
      return;
    }
    if (status?.node_reachable !== true) {
      return;
    }
    smokeRan.current = true;
    async function runSmoke() {
      let nextForm = { ...EMPTY_FORM, ...smoke };
      setForm((current) => ({ ...current, ...nextForm }));
      if (nextForm.load_oracle_evidence) {
        await loadOracleEvidenceCandidates(nextForm);
      }
      if (actionSupportsOracleFixture(nextForm.action) && nextForm.use_oracle_fixture) {
        nextForm = await buildOracleFixturePayload(nextForm);
      } else if (nextForm.oracle_adapter_bridge.trim()) {
        await inspectOracleBridgePayload(nextForm);
      }
      if (!hasLocalSigningCredential(nextForm)) {
        throw new Error('smoke signing credential required');
      }
      const payload = await apiSubmitPerpsWallet(buildPayload(nextForm), { timeoutMs: 20000 });
      if (typeof window !== 'undefined') {
        window.__zenodex_perps_smoke_ran = true;
        window.__zenodex_perps_smoke_result = payload;
      }
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
  const proofProfile = result?.proof?.profile || status?.proof_profile || null;
  const proofReceipt = result?.proof?.intent_receipt || null;
  const oracleAuthorityExercise = result?.proof?.oracle_authority_exercise || proofReceipt?.oracle_authority_exercise || null;
  const stateDeltaWitness = proofReceipt?.state_delta_witness || result?.post_submit?.state_delta_witness || null;
  const walletAuthority = status?.wallet_authority || null;
  const walletRecoveryExercise = walletAuthority?.recovery_exercise || null;
  const walletRotationExercise = walletAuthority?.rotation_exercise || null;
  const walletDeviceApprovalExercise = walletAuthority?.device_approval_exercise || null;
  const walletSignerDeviceIntegration = walletAuthority?.signer_device_integration || null;
  const walletSignerPromptCapture = walletAuthority?.signer_prompt_capture || null;
  const walletSignerExecutionExercise = walletAuthority?.signer_execution_exercise || null;
  const walletSignerCeremony = walletAuthority?.signer_ceremony || null;
  const walletHardwareCustody = walletAuthority?.hardware_custody || null;
  const oracleAuthority = status?.oracle_authority || null;
  const oracleBridgePosture = (
    status?.require_oracle_adapter_for_clearinghouse_settle_epoch
    && status?.require_oracle_adapter_for_isolated_partial_liquidate
  )
    ? 'settlement+partial required'
    : status?.require_oracle_adapter_for_clearinghouse_settle_epoch
      ? 'settlement required'
      : status?.require_oracle_adapter_for_isolated_partial_liquidate
        ? 'partial required'
        : 'optional';

  function localFaucetQuoteAsset() {
    return String(selectedMarket?.quote_asset || form.quote_asset || status?.quote_asset_default || '').trim();
  }

  function localFaucetTargetPubkey() {
    return String(
      form.account_pubkey
      || selectedAccount?.account_pubkey
      || selectedMarket?.account_a_pubkey
      || form.account_a_pubkey
      || '',
    ).trim();
  }

  const localFaucetTarget = localFaucetTargetPubkey();
  const localFaucetAsset = localFaucetQuoteAsset();

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
          <div><span>Oracle Bridge</span><span>{oracleBridgePosture}</span></div>
          <div><span>Isolated</span><span>{status?.allow_isolated_markets ? 'enabled' : 'disabled'}</span></div>
          <div><span>Proof profile</span><span>{proofProfile?.profile_id || 'unassigned'}</span></div>
          <div><span>ZK proof</span><span>{proofProfile?.zk_proof_verified ? 'verified' : 'pending'}</span></div>
          <div><span>ZK Artifacts</span><span>{proofProfile?.artifact_binding_complete ? 'ready' : 'pending'}</span></div>
          <div><span>Wallet Authority</span><span>{walletAuthority?.production_wallet_authority ? 'ready' : 'blocked'}</span></div>
          <div><span>Wallet Signers</span><span>{walletAuthority ? `${walletAuthority.active_signer_count}/${walletAuthority.threshold || '?'}` : 'unknown'}</span></div>
          <div><span>Wallet Recovery</span><span>{walletAuthority ? `${walletAuthority.recoverable_active_key_count ?? 0}/${walletAuthority.active_signer_count ?? 0}` : 'unknown'}</span></div>
          <div><span>Recovery Exercise</span><span>{walletRecoveryExercise ? walletRecoveryExercise.status : 'not loaded'}</span></div>
          <div><span>Recovery Signed Quorum</span><span>{walletRecoveryExercise?.guardian_signature_quorum ? `${walletRecoveryExercise.guardian_signature_quorum.accepted_weight ?? 0}/${walletRecoveryExercise.guardian_signature_quorum.threshold ?? 0}` : 'unknown'}</span></div>
          <div><span>Rotation Signed Quorum</span><span>{walletRotationExercise?.guardian_signature_quorum ? `${walletRotationExercise.guardian_signature_quorum.accepted_weight ?? 0}/${walletRotationExercise.guardian_signature_quorum.threshold ?? 0}` : 'unknown'}</span></div>
          <div><span>Device Approval</span><span>{walletDeviceApprovalExercise ? walletDeviceApprovalExercise.status : 'not loaded'}</span></div>
          <div><span>Device Sign Admission</span><span>{walletDeviceApprovalExercise?.sign_admission_receipt ? `${walletDeviceApprovalExercise.sign_admission_receipt.ok ? 'ok' : 'blocked'} ${walletDeviceApprovalExercise.sign_admission_receipt.payload_nonce ?? 'unknown'}` : 'unknown'}</span></div>
          <div><span>Signer Device</span><span>{walletSignerDeviceIntegration ? walletSignerDeviceIntegration.status : 'not loaded'}</span></div>
          <div><span>Signer Backend</span><span>{walletSignerDeviceIntegration?.backend_kind || 'unknown'}</span></div>
          <div><span>Signer Prompt Capture</span><span>{walletSignerPromptCapture ? walletSignerPromptCapture.status : 'not loaded'}</span></div>
          <div><span>Prompt Capture Source</span><span>{walletSignerPromptCapture?.capture_source || 'unknown'}</span></div>
          <div><span>Signer Execution</span><span>{walletSignerExecutionExercise ? walletSignerExecutionExercise.status : 'not loaded'}</span></div>
          <div><span>Signer Prompt</span><span>{walletSignerExecutionExercise?.prompt_reference || 'unknown'}</span></div>
          <div><span>Signer Ceremony</span><span>{walletSignerCeremony ? walletSignerCeremony.status : 'not loaded'}</span></div>
          <div><span>Ceremony Execution Ref</span><span>{walletSignerCeremony?.execution_reference || 'unknown'}</span></div>
          <div><span>Oracle Authority</span><span>{oracleAuthority?.production_authority ? 'ready' : 'blocked'}</span></div>
          <div><span>Oracle Signers</span><span>{oracleAuthority ? `${oracleAuthority.active_signer_count}/${oracleAuthority.threshold || '?'}` : 'unknown'}</span></div>
          <div><span>Oracle Signed Quorum</span><span>{oracleAuthority?.signature_quorum ? `${oracleAuthority.signature_quorum.accepted_weight ?? 0}/${oracleAuthority.signature_quorum.threshold ?? oracleAuthority.threshold ?? 0}` : 'unknown'}</span></div>
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
              <button
                className="btn btn-secondary"
                type="button"
                onClick={handleInspectOracleBridge}
                disabled={busy || !form.oracle_adapter_bridge.trim()}
              >
                Inspect Oracle Bridge
              </button>
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

          <details className="perp-advanced-options" style={{ marginTop: 'var(--space-md)', padding: 'var(--space-md)', border: '1px solid var(--border-subtle)', borderRadius: 'var(--radius-md)' }}>
            <summary style={{ cursor: 'pointer', fontWeight: 600, color: 'var(--text-secondary)' }}>Advanced Testnet Parameters</summary>
            <div className="perp-live-wallet-form" style={{ marginTop: 'var(--space-md)' }}>
              <label className="label" htmlFor="perps-wallet-fee-limit">Tau Fee Limit</label>
              <input
                id="perps-wallet-fee-limit"
                className="input"
                inputMode="numeric"
                value={form.tx_fee_limit}
                onChange={(event) => setForm((current) => ({ ...current, tx_fee_limit: event.target.value }))}
                placeholder="native units"
              />

              <label className="label" htmlFor="perps-wallet-signed-tx">Signed Tau Tx Payload</label>
              <textarea
                id="perps-wallet-signed-tx"
                className="input perp-live-wallet-textarea"
                value={form.signed_tau_tx_payload}
                onChange={(event) => setForm((current) => ({ ...current, signed_tau_tx_payload: event.target.value }))}
                placeholder="external signer JSON"
              />

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
                </>
              ) : null}
            </div>
          </details>

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
              <button
                className="btn btn-secondary"
                type="button"
                onClick={handleInspectOracleBridge}
                disabled={busy || !form.oracle_adapter_bridge.trim()}
              >
                Inspect Oracle Bridge
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
            <button className="btn btn-secondary" type="button" onClick={handleLoadOracleEvidence} disabled={busy}>
              Load Oracle Evidence
            </button>
            <button
              className="btn btn-secondary"
              type="button"
              onClick={handleFundTestnetQuote}
              disabled={busy || faucetBusy || !localFaucetTarget || !localFaucetAsset}
            >
              Fund {localFaucetAsset ? compactId(localFaucetAsset) : 'Quote'}
            </button>
          </div>
        </div>
      </div>

      {statusError ? <p className="perp-live-wallet-error">Status error: {statusError}</p> : null}
      {error ? <p className="perp-live-wallet-error">Action error: {error}</p> : null}
      {selectedMarket ? (
        <div className="perp-live-wallet-result" aria-label="Selected perps market summary">
          <span>market {selectedMarket.market_id}</span>
          <span>quote A {valueOrNA(selectedMarket.account_a_quote_balance)}</span>
          <span>quote B {valueOrNA(selectedMarket.account_b_quote_balance)}</span>
          <span>faucet target {compactId(localFaucetTarget)}</span>
          <span>faucet asset {compactId(localFaucetAsset)}</span>
          <span>posted A {valueOrNA(selectedMarket.collateral_e8_a)}</span>
          <span>posted B {valueOrNA(selectedMarket.collateral_e8_b)}</span>
          {selectedMarket.account_count != null ? <span>accounts {selectedMarket.account_count}</span> : null}
          {selectedAccount?.position_base != null ? <span>position {selectedAccount.position_base}</span> : null}
          {selectedAccount?.collateral_quote != null ? <span>collateral {selectedAccount.collateral_quote}</span> : null}
          {selectedAccount?.liquidated_this_step != null ? (
            <span>isolated liquidated {selectedAccount.liquidated_this_step ? 'yes' : 'no'}</span>
          ) : null}
        </div>
      ) : null}
      {faucetResult ? (
        <div className="perp-live-wallet-result" role="status">
          <span>faucet accepted {faucetResult.ok ? 'yes' : 'no'}</span>
          <span>height {faucetResult.height ?? 'pending'}</span>
          <span>{faucetResult.tx_id || 'no tx id'}</span>
        </div>
      ) : null}
      {result ? (
        <div className="perp-live-wallet-result" role="status">
          <span>{result.submission ? 'submit accepted' : 'prepare ready'}</span>
          <span>{preflight?.ok ? 'preflight ok' : `preflight failed: ${preflight?.error || 'unknown'}`}</span>
          <span>fee limit {result.transport?.tx_fee_limit ?? '0'}</span>
          <span>fee covered {feeCovered == null ? 'unknown' : feeCovered ? 'yes' : 'no'}</span>
          <span>signing {result.transport?.signing_mode || 'prepare_only'}</span>
          <span>{result.transport?.app_hash || 'no app hash'}</span>
          <span>proof profile {proofProfile?.profile_id || 'unassigned'}</span>
          <span>proof receipt {compactId(proofReceipt?.receipt_hash)}</span>
          <span>zk proof {proofProfile?.zk_proof_verified ? 'verified' : 'pending'}</span>
          <span>zk artifacts {proofProfile?.artifact_binding_complete ? 'ready' : 'pending'}</span>
          <span>zk binding {compactId(result?.proof?.zk_wrapper?.artifact_binding?.binding_hash)}</span>
          <span>delta witness {stateDeltaWitness ? stateDeltaWitness.changed_markets?.length ?? 0 : 'pending'}</span>
          <span>wallet authority {walletAuthority?.production_wallet_authority ? 'ready' : 'blocked'}</span>
          <span>wallet keys {walletAuthority?.key_ref_count ?? 0}</span>
          <span>wallet recovery {walletAuthority ? `${walletAuthority.recoverable_active_key_count ?? 0}/${walletAuthority.active_signer_count ?? 0}` : 'unknown'}</span>
          {walletRecoveryExercise ? (
            <>
              <span>recovery exercise {walletRecoveryExercise.recovery_exercise_ready ? 'ready' : 'blocked'}</span>
              <span>recovery signed quorum {walletRecoveryExercise.guardian_signature_quorum ? `${walletRecoveryExercise.guardian_signature_quorum.accepted_weight ?? 0}/${walletRecoveryExercise.guardian_signature_quorum.threshold ?? 0}` : 'unknown'}</span>
              <span>recovery receipt {compactId(walletRecoveryExercise.status_hash)}</span>
            </>
          ) : null}
          {walletRotationExercise ? (
            <>
              <span>rotation exercise {walletRotationExercise.rotation_exercise_ready ? 'ready' : 'blocked'}</span>
              <span>rotation signed quorum {walletRotationExercise.guardian_signature_quorum ? `${walletRotationExercise.guardian_signature_quorum.accepted_weight ?? 0}/${walletRotationExercise.guardian_signature_quorum.threshold ?? 0}` : 'unknown'}</span>
              <span>rotation receipt {compactId(walletRotationExercise.status_hash)}</span>
            </>
          ) : null}
          {walletDeviceApprovalExercise ? (
            <>
              <span>device approval {walletDeviceApprovalExercise.device_approval_ready ? 'ready' : 'blocked'}</span>
              <span>device sign admission {walletDeviceApprovalExercise.sign_admission_receipt?.ok ? 'ok' : 'blocked'}</span>
              <span>device approval receipt {compactId(walletDeviceApprovalExercise.status_hash)}</span>
            </>
          ) : null}
          {walletSignerDeviceIntegration ? (
            <>
              <span>signer device {walletSignerDeviceIntegration.signer_device_ready ? 'ready' : 'blocked'}</span>
              <span>signer backend {walletSignerDeviceIntegration.backend_kind || 'unknown'}</span>
              <span>signer device receipt {compactId(walletSignerDeviceIntegration.status_hash)}</span>
            </>
          ) : null}
          {walletSignerPromptCapture ? (
            <>
              <span>signer prompt capture {walletSignerPromptCapture.signer_prompt_capture_ready ? 'ready' : 'blocked'}</span>
              <span>prompt capture source {walletSignerPromptCapture.capture_source || 'unknown'}</span>
              <span>signer prompt capture receipt {compactId(walletSignerPromptCapture.status_hash)}</span>
            </>
          ) : null}
          {walletSignerExecutionExercise ? (
            <>
              <span>signer execution {walletSignerExecutionExercise.signer_execution_ready ? 'ready' : 'blocked'}</span>
              <span>signer prompt {walletSignerExecutionExercise.prompt_reference || 'unknown'}</span>
              <span>signer execution receipt {compactId(walletSignerExecutionExercise.status_hash)}</span>
            </>
          ) : null}
          {walletSignerCeremony ? (
            <>
              <span>signer ceremony {walletSignerCeremony.signer_ceremony_ready ? 'ready' : 'blocked'}</span>
              <span>ceremony execution {walletSignerCeremony.execution_reference || 'unknown'}</span>
              <span>signer ceremony receipt {compactId(walletSignerCeremony.status_hash)}</span>
            </>
          ) : null}
          {walletHardwareCustody ? (
            <>
              <span>hardware device {walletHardwareCustody.hardware_custody_ready ? 'ready' : 'blocked'}</span>
              <span>hardware backend {walletHardwareCustody.backend_kind || 'unknown'}</span>
              <span>hardware device receipt {compactId(walletHardwareCustody.status_hash)}</span>
            </>
          ) : null}
          <span>oracle authority {oracleAuthority?.production_authority ? 'ready' : 'blocked'}</span>
          <span>oracle signers {oracleAuthority ? `${oracleAuthority.active_signer_count}/${oracleAuthority.threshold || '?'}` : 'unknown'}</span>
          <span>oracle signed quorum {oracleAuthority?.signature_quorum ? `${oracleAuthority.signature_quorum.accepted_weight ?? 0}/${oracleAuthority.signature_quorum.threshold ?? oracleAuthority.threshold ?? 0}` : 'unknown'}</span>
          {oracleAuthorityExercise ? (
            <>
              <span>oracle authority exercised {oracleAuthorityExercise.authority_exercised ? 'yes' : 'no'}</span>
              <span>oracle authority receipt {compactId(oracleAuthorityExercise.exercise_hash)}</span>
            </>
          ) : null}
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
      {oracleInspection ? (
        <div className="perp-live-wallet-result" aria-label="Oracle bridge inspection">
          <span>oracle evidence {oracleInspection.ok ? 'accepted' : 'rejected'}</span>
          <span>oracle action {oracleInspection.summary?.action_kind || 'unknown'}</span>
          <span>oracle profile {oracleInspection.summary?.profile_id || 'unknown'}</span>
          <span>oracle query {oracleInspection.summary?.query_id || 'unknown'}</span>
          <span>oracle value {oracleInspection.summary?.value_e8 ?? 'unknown'}</span>
          <span>oracle epoch {oracleInspection.summary?.observed_epoch ?? 'unknown'}</span>
          <span>oracle reports {oracleInspection.summary?.report_count ?? 'unknown'}</span>
          <span>oracle production {oracleInspection.production_authority ? 'yes' : 'local'}</span>
        </div>
      ) : null}
      {oracleEvidence ? (
        <div className="perp-live-wallet-result" aria-label="Live Oracle evidence candidates">
          <span>oracle service {oracleEvidence.ok ? 'connected' : 'warning'}</span>
          <span>oracle replay {oracleEvidence.replay_ok ? 'ok' : 'warning'}</span>
          <span>oracle accepted reads {oracleEvidence.accepted_read_count}</span>
          <span>oracle authorizations {oracleEvidence.authorization_count}</span>
          <span>oracle candidates {oracleEvidence.candidates.length}</span>
          <span>oracle target {oracleEvidence.target_action || 'any'}</span>
          <span>oracle network {oracleEvidence.production_authority ? 'production' : 'local'}</span>
          {selectedOracleEvidence ? (
            <>
              <span>oracle selected {selectedOracleEvidence.kind}</span>
              <span>oracle selected id {compactId(selectedOracleEvidence.id)}</span>
              <span>oracle selected action {selectedOracleEvidence.action}</span>
              <span>oracle selected value {selectedOracleEvidence.valueE8 ?? 'unknown'}</span>
            </>
          ) : null}
          {oracleEvidence.candidates.slice(0, 3).map((candidate) => (
            <button
              key={`${candidate.kind}:${candidate.id}`}
              className="btn btn-ghost"
              type="button"
              onClick={() => setSelectedOracleEvidence(candidate)}
            >
              {candidate.kind} {compactId(candidate.id)}
            </button>
          ))}
        </div>
      ) : null}
    </section>
  );
}

export default PerpLiveWalletSurface;
