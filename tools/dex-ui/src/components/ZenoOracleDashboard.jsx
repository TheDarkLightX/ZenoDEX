// Copyright DarkLightX/Dana Edwards
// ZenoOracle dashboard — v3 layout (3 tabs: Monitor / Resolve / Admin).
// Redesigned after 3 rounds of UX review. Replaces the 8-tab layout with
// a persistent status bar, context-aware detail rail, and progressive disclosure.

import { useEffect, useMemo, useRef, useState } from 'react';
import {
  ORACLE_DISPUTES,
  ORACLE_FEEDS,
  ORACLE_REPORTERS,
  ORACLE_REWARDS,
} from './ZenoOracleDashboardData';
import { useDemoMode } from '../lib/DemoModeContext.jsx';
import Modal from './Modal.jsx';
import './oracle/OracleSection.css';
import {
  zenoOracleApiUrl,
  snapshotToDashboardData,
  parsePositiveIntParam,
  runOracleWriteSmokeFlow,
} from '../lib/oracleUtils.js';
import { useOracleTab } from './oracle/useOracleTab.js';
import OracleTabs from './oracle/OracleTabs.jsx';
import OracleStatusBar from './oracle/OracleStatusBar.jsx';
import MonitorTab from './oracle/MonitorTab.jsx';
import ResolveTab from './oracle/ResolveTab.jsx';
import AdminTab from './oracle/AdminTab.jsx';
import { FeedCreationPanel } from './oracle/FeedPanels.jsx';
import { ReporterOnboardingPanel } from './oracle/ReporterPanels.jsx';
import { ReceiptBuilderPanel } from './oracle/EvidencePanels.jsx';

function ZenoOracleDashboard() {
  const { demoMode } = useDemoMode();
  const [tab, setTab] = useOracleTab();
  const [selectedFeedId, setSelectedFeedId] = useState('');
  const [verifyReceiptId, setVerifyReceiptId] = useState('');
  const [remoteData, setRemoteData] = useState(null);
  const [apiState, setApiState] = useState('Static preview');
  const [, setOracleSmokeStatus] = useState('');
  const [authorityExerciseResult, setAuthorityExerciseResult] = useState(null);
  const [localDisputes, setLocalDisputes] = useState([]);
  const [authorityExerciseState, setAuthorityExerciseState] = useState('');
  const [authorityExerciseBusy, setAuthorityExerciseBusy] = useState(false);
  const [showFeedCreationModal, setShowFeedCreationModal] = useState(false);
  const [showReporterOnboardingModal, setShowReporterOnboardingModal] = useState(false);
  const [showReceiptBuilderModal, setShowReceiptBuilderModal] = useState(false);
  const oracleSmokeRan = useRef(false);
  const oracleAuthorityExerciseSmokeRan = useRef(false);

  // Disputes can be added locally (e.g. from smoke tests or demo mode)
  const handleAddDispute = (newDispute) => {
    setLocalDisputes((prev) => [...prev, newDispute]);
  };
  void handleAddDispute;

  async function postOracle(path, payload) {
    const response = await fetch(zenoOracleApiUrl(path), {
      method: 'POST',
      headers: { 'Content-Type': 'application/json' },
      body: JSON.stringify(payload),
    });
    const body = await response.json();
    if (!response.ok || body.ok === false) {
      throw new Error(body.error || `HTTP ${response.status}`);
    }
    return body;
  }

  async function runAuthorityExercise(options = {}) {
    const targetNetwork = String(options.targetNetwork || 'local');
    const publicBroadcastReference = String(options.publicBroadcastReference || '').trim();
    const publicSettlementReference = String(options.publicSettlementReference || '').trim();
    const publicBroadcastHeight = Number.isInteger(options.publicBroadcastHeight) && options.publicBroadcastHeight > 0
      ? options.publicBroadcastHeight
      : undefined;
    const publicSettlementHeight = Number.isInteger(options.publicSettlementHeight) && options.publicSettlementHeight > 0
      ? options.publicSettlementHeight
      : undefined;
    setAuthorityExerciseBusy(true);
    setAuthorityExerciseState('Running security check');
    try {
      const flow = await runOracleWriteSmokeFlow(postOracle);
      const requestBody = {
        target_network: targetNetwork,
        current_epoch: 12,
        operator_service_url: zenoOracleApiUrl('/api/oracle/dashboard'),
        query_id: flow.queryId,
        report_id: flow.submitted.report_id,
        aggregate_id: flow.aggregate.aggregate_id,
        read_id: flow.read.read_id,
        authorization_id: flow.authorization.authorization_id,
        reward_receipt_id: flow.reward.receipt_id || flow.reward.reward_receipt_id || flow.reward.payment_id || 'reward:local',
      };
      if (publicBroadcastReference) {
        requestBody.public_broadcast_reference = publicBroadcastReference;
      }
      if (publicSettlementReference) {
        requestBody.public_settlement_reference = publicSettlementReference;
      }
      if (publicBroadcastHeight !== undefined) {
        requestBody.public_broadcast_height = publicBroadcastHeight;
      }
      if (publicSettlementHeight !== undefined) {
        requestBody.public_settlement_height = publicSettlementHeight;
      }
      const payload = await postOracle('/api/oracle/authority/exercise/evaluate', requestBody);
      setAuthorityExerciseResult(payload);
      setAuthorityExerciseState(`Security check accepted ${payload.authority_exercise_status?.exercise_hash || ''}`.trim());
    } catch (error) {
      setAuthorityExerciseState(`Security check failed ${error?.message || 'unknown'}`);
      throw error;
    } finally {
      setAuthorityExerciseBusy(false);
    }
  }

  useEffect(() => {
    const controller = new AbortController();
    async function loadDashboard() {
      try {
        const response = await fetch(zenoOracleApiUrl('/api/oracle/dashboard'), {
          signal: controller.signal,
        });
        if (!response.ok) {
          throw new Error(`HTTP ${response.status}`);
        }
        const snapshot = await response.json();
        setRemoteData(snapshotToDashboardData(snapshot));
        setApiState(snapshot?.summary?.replay_ok ? 'Connected' : 'Sync warning');
      } catch (error) {
        if (error.name !== 'AbortError') {
          setApiState('Offline');
        }
      }
    }
    loadDashboard();
    const timer = window.setInterval(loadDashboard, 15000);
    return () => {
      controller.abort();
      window.clearInterval(timer);
    };
  }, []);

  useEffect(() => {
    if (typeof window === 'undefined') {
      return;
    }
    const params = new URLSearchParams(window.location.search);
    if (params.get('zenodexUiSmokeOracleWrites') !== '1' || oracleSmokeRan.current) {
      return;
    }
    oracleSmokeRan.current = true;
    const storageKey = 'zenodex.uiSmokeOracleWrites.submitted';
    if (window.sessionStorage.getItem(storageKey) === '1') {
      return;
    }
    window.sessionStorage.setItem(storageKey, '1');

    async function runSmoke() {
      setOracleSmokeStatus('Test run running');
      const flow = await runOracleWriteSmokeFlow(postOracle);
      setOracleSmokeStatus(
        `Test run accepted ${flow.identity.reporter_id} ${flow.submitted.report_id} ${flow.authorization.authorization_id}`,
      );
    }

    void runSmoke().catch((error) => {
      setOracleSmokeStatus(`Test run failed ${error?.message || 'unknown'}`);
    });
  }, []);

  useEffect(() => {
    if (typeof window === 'undefined') {
      return;
    }
    const params = new URLSearchParams(window.location.search);
    if (params.get('zenodexUiSmokeOracleAuthorityExercise') !== '1' || oracleAuthorityExerciseSmokeRan.current) {
      return;
    }
    oracleAuthorityExerciseSmokeRan.current = true;
    const storageKey = 'zenodex.uiSmokeOracleAuthorityExercise.submitted';
    if (window.sessionStorage.getItem(storageKey) === '1') {
      return;
    }
    window.sessionStorage.setItem(storageKey, '1');
    const smokeTargetNetwork = String(params.get('zenodexUiSmokeOracleAuthorityExerciseTarget') || 'local').trim();
    const usePublicTestnetEvidence = params.get('zenodexUiSmokeOracleAuthorityExercisePublicTestnet') === '1'
      || smokeTargetNetwork === 'public_testnet';
    const smokeOptions = usePublicTestnetEvidence
      ? {
        targetNetwork: 'public_testnet',
        publicBroadcastReference:
          String(params.get('zenodexUiSmokeOraclePublicBroadcastReference') || ''),
        publicSettlementReference:
          String(params.get('zenodexUiSmokeOraclePublicSettlementReference') || ''),
        publicBroadcastHeight: parsePositiveIntParam(params.get('zenodexUiSmokeOracleBroadcastHeight'), undefined),
        publicSettlementHeight: parsePositiveIntParam(params.get('zenodexUiSmokeOracleSettlementHeight'), undefined),
      }
      : { targetNetwork: smokeTargetNetwork || 'local' };
    void runAuthorityExercise(smokeOptions).catch(() => {});
    // eslint-disable-next-line react-hooks/exhaustive-deps
  }, []);

  // ─── Derived data (same logic as v1, preserved for compatibility) ───
  const feeds = useMemo(
    () => (remoteData?.feeds?.length ? remoteData.feeds : (demoMode ? ORACLE_FEEDS : [])),
    [remoteData?.feeds, demoMode],
  );
  const reporters = remoteData?.reporters?.length ? remoteData.reporters : (demoMode ? ORACLE_REPORTERS : []);
  const disputes = [
    ...(remoteData?.disputes?.length ? remoteData.disputes : (demoMode ? ORACLE_DISPUTES : [])),
    ...localDisputes,
  ];
  const sources = remoteData?.sources?.length ? remoteData.sources : [];
  const rewards = remoteData?.rewards?.length ? remoteData.rewards : (demoMode ? ORACLE_REWARDS : []);
  const authorizationTrail = remoteData?.authorizationTrail || [];
  const authorityStatus = remoteData?.authorityStatus || null;
  const authorityReady = authorityStatus?.production_authority === true;
  const authorityGaps = Array.isArray(authorityStatus?.readiness_gaps)
    ? authorityStatus.readiness_gaps
    : [];
  void authorityGaps;

  const summary = remoteData?.summary || {};
  const aggregationStatus = summary.aggregation_ok === true
    ? 'ok'
    : summary.aggregation_ok === false
      ? 'down'
      : 'unknown';

  const emptyFeed = {
    id: 'placeholder',
    feed: 'Waiting for network...',
    domain: '—',
    value: 'N/A',
    unit: '',
    change24h: '—',
    evidenceClass: '—',
    freshness: '—',
    status: 'stale',
  };
  const selectedFeed = feeds.find((feed) => feed.id === selectedFeedId) || feeds[0] || (demoMode ? ORACLE_FEEDS[0] : emptyFeed);
  const hasRealFeed = Boolean(selectedFeed) && selectedFeed.id !== 'placeholder';

  const handleVerifyReceipt = (receiptId) => {
    const id = String(receiptId || '').trim();
    if (!id) return;
    setVerifyReceiptId(id);
    setTab('resolve');
  };

  return (
    <div className="oracle-section">
      {/* ─── Persistent status bar (all tabs) ─── */}
      <OracleStatusBar
        feeds={feeds}
        disputes={disputes}
        reporters={reporters}
        authorityReady={authorityReady}
        aggregationStatus={aggregationStatus}
        apiState={apiState}
        lastUpdateLabel={summary.last_update_label || ''}
        onViewDisputes={() => setTab('resolve')}
      />

      {/* ─── Safety context line (1 line, not a hero) ─── */}
      <div className="oracle-context-line" role="note">
        Oracle feeds price Perps &amp; zUSD. Stale or wrong data can trigger liquidations.
      </div>

      {/* ─── Task tabs ─── */}
      <OracleTabs activeTab={tab} onTabChange={setTab} />

      {/* ─── Tab content ─── */}
      {tab === 'monitor' && (
        <MonitorTab
          feeds={feeds}
          selectedFeedId={selectedFeed.id}
          onSelectFeed={setSelectedFeedId}
          onCreateFeed={() => setShowFeedCreationModal(true)}
          onBuildReceipt={() => setShowReceiptBuilderModal(true)}
          onOpenDispute={() => setTab('resolve')}
          onVerifyReceipt={handleVerifyReceipt}
          onViewAllReceipts={() => setTab('resolve')}
          onRegisterReporter={() => setShowReporterOnboardingModal(true)}
          reporters={reporters}
          disputes={disputes}
          remoteData={remoteData}
          demoMode={demoMode}
          postOracle={postOracle}
        />
      )}

      {tab === 'resolve' && (
        <ResolveTab
          disputes={disputes}
          selectedFeed={hasRealFeed ? selectedFeed : null}
          onVerifyReceipt={handleVerifyReceipt}
          verifyReceiptId={verifyReceiptId}
          authorizationTrail={authorizationTrail}
          remoteData={remoteData}
          demoMode={demoMode}
          postOracle={postOracle}
        />
      )}

      {tab === 'admin' && (
        <AdminTab
          feeds={feeds}
          selectedFeed={hasRealFeed ? selectedFeed : null}
          reporters={reporters}
          rewards={rewards}
          sources={sources}
          authorityStatus={authorityStatus}
          authorityExerciseResult={authorityExerciseResult}
          authorityExerciseState={authorityExerciseState}
          authorityExerciseBusy={authorityExerciseBusy}
          onRunAuthorityExercise={() => { void runAuthorityExercise().catch(() => {}); }}
          onCreateFeed={() => setShowFeedCreationModal(true)}
          demoMode={demoMode}
        />
      )}

      {/* ─── Modals (write flows kept behind modals for calm UI) ─── */}
      <Modal
        open={showFeedCreationModal}
        onClose={() => setShowFeedCreationModal(false)}
        title="Create feed"
        description="Register a new query so reporters can submit values against it."
        size="lg"
      >
        <FeedCreationPanel />
      </Modal>
      <Modal
        open={showReporterOnboardingModal}
        onClose={() => setShowReporterOnboardingModal(false)}
        title="Register reporter"
        description="Onboard a new reporter and bond them to a query."
        size="lg"
      >
        <ReporterOnboardingPanel selectedFeed={selectedFeed} />
      </Modal>
      <Modal
        open={showReceiptBuilderModal}
        onClose={() => setShowReceiptBuilderModal(false)}
        title="Build receipt"
        description="Aggregate, read, or authorize. Downloads a JSON receipt."
        size="lg"
      >
        <ReceiptBuilderPanel feed={selectedFeed} />
      </Modal>
    </div>
  );
}

export default ZenoOracleDashboard;
