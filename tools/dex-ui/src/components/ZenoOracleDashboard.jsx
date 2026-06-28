// Copyright DarkLightX/Dana Edwards
// ZenoOracle dashboard — main orchestrator component.
import { useEffect, useMemo, useRef, useState } from 'react';
import {
  ORACLE_DISPUTES,
  ORACLE_FEEDS,
  ORACLE_NETWORK_SUMMARY,
  ORACLE_REPORTERS,
  ORACLE_REWARDS,
} from './ZenoOracleDashboardData';
import { useDemoMode } from '../lib/DemoModeContext.jsx';
import Modal from './Modal.jsx';
import SharedStatusPill from './StatusPill.jsx';
import './ZenoOracleDashboard.css';
import {
  zenoOracleApiUrl,
  snapshotToDashboardData,
  getInitialOracleSection,
  parsePositiveIntParam,
  compactId,
  runOracleWriteSmokeFlow,
  ORACLE_SECTIONS,
} from '../lib/oracleUtils.js';
import {
  FeedTable,
  FeedStatusPanel,
  FeedCreationPanel,
  FeedDetailInspector,
} from './oracle/FeedPanels.jsx';
import {
  ReporterOnboardingPanel,
  ReporterPanel,
} from './oracle/ReporterPanels.jsx';
import {
  AuthorityProfilePanel,
  AuthorityExercisePanel,
} from './oracle/AuthorityPanels.jsx';
import {
  EvidencePanel,
  VerifyPanel,
  LatestRead,
  ReceiptBuilderPanel,
} from './oracle/EvidencePanels.jsx';
import {
  MetricCard,
  HealthPanel,
  FeatureStrip,
  ServicesPanel,
  EventsPanel,
} from './oracle/StatusPanels.jsx';
import { DisputesPanel } from './oracle/DisputePanels.jsx';
import {
  RewardsPanel,
  SourceDiversityPanel,
  AuthorizationTrailPanel,
  ConsumerProfilePanel,
} from './oracle/RewardPanels.jsx';

const ZENO_ORACLE_ICON = `${import.meta.env.BASE_URL}branding/zeno-oracle/zeno_oracle_icon_256.png`;

const ORACLE_SECTION_COPY = {
  Overview: 'Real-time local status for feeds, reporters, evidence, and receipts.',
  Feeds: 'Create and inspect feed policies, freshness state, and source requirements.',
  Reports: 'Submit reports, inspect admitted reads, and monitor source provenance.',
  Reporters: 'Review reporter liveness, bonds, rewards, and slash state.',
  Disputes: 'Open, resolve, and audit disputes that can quarantine oracle inputs.',
  Receipts: 'Build and inspect aggregate, read, and action-authorization receipts.',
  Verify: 'Replay receipt artifacts and local verifier state before critical use.',
  Governance: 'Inspect consumer profiles, service posture, and policy readiness.',
};

function ZenoOracleDashboard({ wallet = null } = {}) {
  const { demoMode } = useDemoMode();
  const [selectedFeedId, setSelectedFeedId] = useState('');
  const [feedFilter, setFeedFilter] = useState('all');
  const [timeRange, setTimeRange] = useState('24h');
  const [activeSection, setActiveSection] = useState(getInitialOracleSection);
  const [verifyReceiptId, setVerifyReceiptId] = useState('');
  const [remoteData, setRemoteData] = useState(null);
  const [apiState, setApiState] = useState('Static preview');
  const [oracleSmokeStatus, setOracleSmokeStatus] = useState('');
  const [authorityExerciseResult, setAuthorityExerciseResult] = useState(null);
  const [localDisputes, setLocalDisputes] = useState([]);
  const [isRailCollapsed, setIsRailCollapsed] = useState(false);

  const handleAddDispute = (newDispute) => {
    setLocalDisputes((prev) => [...prev, newDispute]);
  };
  const [authorityExerciseState, setAuthorityExerciseState] = useState('');
  const [authorityExerciseBusy, setAuthorityExerciseBusy] = useState(false);
  // Modal visibility flags for the demoted write-flow forms. Each modal
  // is a thin wrapper around the existing inline panel component, so
  // the form logic stays identical — we only changed how the user
  // reaches it (inline panel → "+ Create" CTA → modal).
  const [showFeedCreationModal, setShowFeedCreationModal] = useState(false);
  const [showReporterOnboardingModal, setShowReporterOnboardingModal] = useState(false);
  const [showReceiptBuilderModal, setShowReceiptBuilderModal] = useState(false);
  const oracleSmokeRan = useRef(false);
  const oracleAuthorityExerciseSmokeRan = useRef(false);

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
    setAuthorityExerciseState('oracle authority exercise running');
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
      setAuthorityExerciseState(`oracle authority exercise accepted ${payload.authority_exercise_status?.exercise_hash || ''}`.trim());
    } catch (error) {
      setAuthorityExerciseState(`oracle authority exercise failed ${error?.message || 'unknown'}`);
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
        setApiState(snapshot?.summary?.replay_ok ? 'Local API connected' : 'Local API replay warning');
      } catch (error) {
        if (error.name !== 'AbortError') {
          setApiState('Local API offline');
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
      setOracleSmokeStatus('oracle write smoke running');
      const flow = await runOracleWriteSmokeFlow(postOracle);
      setOracleSmokeStatus(
        `oracle write smoke accepted ${flow.identity.reporter_id} ${flow.submitted.report_id} ${flow.authorization.authorization_id}`,
      );
    }

    void runSmoke().catch((error) => {
      setOracleSmokeStatus(`oracle write smoke failed ${error?.message || 'unknown'}`);
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

  const emptyMetrics = ORACLE_NETWORK_SUMMARY.map(m => ({ ...m, value: 'N/A', delta: '—', tone: 'neutral' }));
  const feeds = useMemo(
    () => (remoteData?.feeds?.length ? remoteData.feeds : (demoMode ? ORACLE_FEEDS : [])),
    [remoteData?.feeds, demoMode],
  );
  const reporters = remoteData?.reporters?.length ? remoteData.reporters : (demoMode ? ORACLE_REPORTERS : []);
  const disputes = [
    ...(remoteData?.disputes?.length ? remoteData.disputes : (demoMode ? ORACLE_DISPUTES : [])),
    ...localDisputes
  ];
  const metrics = remoteData?.metrics?.length ? remoteData.metrics : (demoMode ? ORACLE_NETWORK_SUMMARY : emptyMetrics);
  const sources = remoteData?.sources?.length ? remoteData.sources : [];
  const rewards = remoteData?.rewards?.length ? remoteData.rewards : (demoMode ? ORACLE_REWARDS : []);
  const authorizationTrail = remoteData?.authorizationTrail || [];
  const authorityStatus = remoteData?.authorityStatus || null;
  const authorityReady = authorityStatus?.production_authority === true;
  const authorityGaps = Array.isArray(authorityStatus?.readiness_gaps)
    ? authorityStatus.readiness_gaps
    : [];
  const authorityLabel = authorityStatus
    ? authorityReady
      ? 'Production authority ready'
      : 'Authority blocked'
    : 'Authority unverified';
  const authorityTitle = authorityGaps.length ? authorityGaps.join('; ') : authorityLabel;

  const visibleFeeds = useMemo(() => {
    if (feedFilter === 'all') {
      return feeds;
    }
    return feeds.filter((feed) => feed.status === feedFilter);
  }, [feeds, feedFilter]);

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
  // True only when a real feed exists; the placeholder fallback must NOT drive
  // the Feed Detail Inspector / Latest Read / Feed Status panels (they would show
  // fabricated "Waiting…/N/A/—" fields for a feed that does not exist).
  const hasRealFeed = Boolean(selectedFeed) && selectedFeed.id !== 'placeholder';
  const sectionCopy = ORACLE_SECTION_COPY[activeSection] || ORACLE_SECTION_COPY.Overview;
  const handleVerifyReceipt = (receiptId) => {
    const id = String(receiptId || '').trim();
    if (!id) {
      return;
    }
    setVerifyReceiptId(id);
    setActiveSection('Verify');
  };

  const coreContent = (() => {
    if (activeSection === 'Feeds') {
      return (
        <>
          <section className="panel zor-panel zor-feeds-panel">
            <div className="zor-section-header">
              <div>
                <h2>Feed Catalogue</h2>
                <p>{timeRange} feed state with evidence, freshness, and critical-use posture.</p>
              </div>
              <span className="zor-subtle-chip">{visibleFeeds.length} feeds</span>
            </div>
            <FeedTable
              feeds={visibleFeeds}
              selectedFeedId={selectedFeed.id}
              onSelectFeed={setSelectedFeedId}
              onCreate={() => setShowFeedCreationModal(true)}
            />
          </section>
          {hasRealFeed && (
            <FeedDetailInspector
              key={selectedFeed?.receiptId || selectedFeed?.feed || 'feed-detail'}
              feed={selectedFeed}
              reporters={reporters}
              disputes={disputes}
              onAddDispute={handleAddDispute}
              demoMode={demoMode}
            />
          )}
          <div className="zor-two-up">
            <FeedCreationPanel />
            <FeedStatusPanel feed={selectedFeed} />
          </div>
          <SourceDiversityPanel sources={sources} />
          <ConsumerProfilePanel />
        </>
      );
    }
    if (activeSection === 'Reports') {
      return (
        <>
          <div className="zor-two-up">
            <ReporterOnboardingPanel selectedFeed={selectedFeed} />
            <LatestRead feed={selectedFeed} onVerifyReceipt={handleVerifyReceipt} onViewAll={() => setActiveSection("Receipts")} />
          </div>
          <AuthorizationTrailPanel items={authorizationTrail} />
          <SourceDiversityPanel sources={sources} />
          <EventsPanel events={authorizationTrail} demoMode={demoMode} />
        </>
      );
    }
    if (activeSection === 'Reporters') {
      return (
        <>
          <ReporterPanel reporters={reporters} />
          <RewardsPanel rewards={rewards} />
          <ReporterOnboardingPanel selectedFeed={selectedFeed} />
        </>
      );
    }
    if (activeSection === 'Disputes') {
      return (
        <>
          <DisputesPanel disputes={disputes} />
          <SourceDiversityPanel sources={sources} />
          <EventsPanel events={authorizationTrail} demoMode={demoMode} />
        </>
      );
    }
    if (activeSection === 'Receipts') {
      return (
        <>
          <div className="zor-two-up">
            <ReceiptBuilderPanel feed={selectedFeed} />
            <LatestRead feed={selectedFeed} onVerifyReceipt={handleVerifyReceipt} onViewAll={() => setActiveSection("Receipts")} />
          </div>
          <AuthorizationTrailPanel items={authorizationTrail} />
          <EvidencePanel summary={remoteData?.summary} reads={remoteData?.acceptedReads} demoMode={demoMode} />
        </>
      );
    }
    if (activeSection === 'Verify') {
      return (
        <>
          <div className="zor-two-up">
            <VerifyPanel key={verifyReceiptId || 'verify'} initialReceiptId={verifyReceiptId} />
            <ServicesPanel summary={remoteData?.summary} authorityStatus={remoteData?.authorityStatus} demoMode={demoMode} />
          </div>
          <AuthorizationTrailPanel items={authorizationTrail} />
          <ConsumerProfilePanel />
        </>
      );
    }
    if (activeSection === 'Governance') {
      return (
        <>
          <AuthorityProfilePanel authorityStatus={authorityStatus} />
          <AuthorityExercisePanel
            authorityStatus={authorityStatus}
            authorityExerciseResult={authorityExerciseResult}
            authorityExerciseState={authorityExerciseState}
            authorityExerciseBusy={authorityExerciseBusy}
            onRunAuthorityExercise={() => {
              void runAuthorityExercise().catch(() => {});
            }}
          />
          <ConsumerProfilePanel />
          <div className="zor-two-up">
            <FeedCreationPanel />
            <ServicesPanel summary={remoteData?.summary} authorityStatus={remoteData?.authorityStatus} demoMode={demoMode} />
          </div>
          <RewardsPanel rewards={rewards} />
        </>
      );
    }
    // Overview: status hero → compact metric ribbon → top 5 feeds →
    // network health → action CTAs → Diagnostics (collapsed by default).
    // Heavy write-flow forms now live behind modals to keep the page calm.
    const visibleFeedCount = visibleFeeds.length;
    const TOP_FEED_LIMIT = 5;
    const topFeeds = visibleFeeds.slice(0, TOP_FEED_LIMIT);

    // Derive a single dominant status from the metrics. Replay-OK +
    // zero open disputes = healthy; replay-fail OR open disputes = warn;
    // explicit replay-fail with disputes = err.
    const summaryForHero = remoteData?.summary || {};
    const openDisputeCount = Number(summaryForHero.open_dispute_count
      || (remoteData?.disputes ? remoteData.disputes.filter((d) => d.status === 'open').length : 0)) || 0;
    const replayOk = summaryForHero.replay_ok !== false;
    const acceptedReadCount = Number(summaryForHero.accepted_read_count || 0);
    const dataPlaneIdle = visibleFeedCount === 0 && acceptedReadCount === 0;
    let heroTone = 'ok';
    let heroHeadline = 'All systems operational';
    let heroLede = `${visibleFeedCount} active feed${visibleFeedCount === 1 ? '' : 's'} · replay verified · 0 open disputes.`;
    if (dataPlaneIdle && replayOk && openDisputeCount === 0) {
      // Authority + replay are up, but no feeds/reads have been reported yet.
      // Don't claim "all systems operational" over an empty data plane.
      heroTone = 'neutral';
      heroHeadline = 'Authority ready · awaiting feeds';
      heroLede = 'Replay verifier OK and authority ready, but no feeds or accepted reads have been reported yet. Register a feed to begin.';
    } else if (!replayOk && openDisputeCount > 0) {
      heroTone = 'err';
      heroHeadline = 'Attention required';
      heroLede = `Replay verification failed and ${openDisputeCount} dispute${openDisputeCount === 1 ? '' : 's'} open.`;
    } else if (!replayOk) {
      heroTone = 'warn';
      heroHeadline = 'Replay verification failing';
      heroLede = 'Acceptance gates remain bounded but replay needs operator attention.';
    } else if (openDisputeCount > 0) {
      heroTone = 'warn';
      heroHeadline = `${openDisputeCount} open dispute${openDisputeCount === 1 ? '' : 's'}`;
      heroLede = `Network is replay-verified; ${openDisputeCount} report${openDisputeCount === 1 ? '' : 's'} awaiting resolution.`;
    }
    const heroPillLabel = heroTone === 'ok' ? 'Healthy'
      : heroTone === 'neutral' ? 'Standby'
      : heroTone === 'warn' ? 'Action needed'
      : 'Critical';

    // Idle data plane: authority ready, replay OK, nothing reported yet. In this
    // state the Overview condenses the wall of empty panels into one guiding
    // readiness card + promoted get-started actions, instead of ~8 "nothing yet"
    // boxes. Populated state (!idleOverview) keeps the full dashboard.
    const idleOverview = dataPlaneIdle && replayOk && openDisputeCount === 0;
    const authForCard = remoteData?.authorityStatus || {};
    const authoritySignerCount = Number(authForCard.active_signer_count ?? authForCard.signer_count ?? 2);
    const authorityReady = authForCard.production_authority === true || authForCard.status === 'ready';
    const readinessAwaiting = [
      ['Active feeds', Number(summaryForHero.active_feed_count || 0)],
      ['Accepted reads', Number(summaryForHero.accepted_read_count || 0)],
      ['Reporters', Number(summaryForHero.reporter_count || 0)],
      ['Sources', Number(summaryForHero.source_count || 0)],
      ['Open disputes', Number(summaryForHero.open_dispute_count || 0)],
    ];

    return (
      <>
        {/* ─── Status hero: the ONE thing the operator should see first. */}
        <section className="zor-hero panel">
          <div className="zor-hero-main">
            <SharedStatusPill tone={heroTone} label={heroPillLabel} />
            <div className="zor-hero-title-row" style={{ display: 'flex', alignItems: 'center', gap: 'var(--space-md)', margin: 'var(--space-xs) 0' }}>
              <img src={ZENO_ORACLE_ICON} alt="Zeno Oracle Logo" className="zor-hero-logo" style={{ width: '48px', height: '48px', borderRadius: '50%' }} />
              <h2 className="zor-hero-headline" style={{ margin: 0 }}>{heroHeadline}</h2>
            </div>
            <p className="zor-hero-lede">{heroLede}</p>
            {idleOverview && (
              <div className="zor-hero-cta-row">
                <button type="button" className="btn btn-primary zor-action-cta" onClick={() => setShowFeedCreationModal(true)}>
                  + Create feed
                </button>
                <button type="button" className="btn btn-secondary zor-action-cta" onClick={() => setShowReporterOnboardingModal(true)}>
                  + Register reporter
                </button>
                <button type="button" className="btn btn-secondary zor-action-cta" onClick={() => setShowReceiptBuilderModal(true)}>
                  + Build receipt
                </button>
              </div>
            )}
          </div>
          <div className="zor-hero-aside">
            {idleOverview ? (
              <div className="zor-hero-stat">
                <span className="zor-hero-stat-label">Replay verifier</span>
                <span className="zor-hero-stat-value" style={{ color: 'var(--accent-green)' }}>OK</span>
              </div>
            ) : (
              <>
                <div className="zor-hero-stat">
                  <span className="zor-hero-stat-label">Active feeds</span>
                  <span className="zor-hero-stat-value">{visibleFeedCount.toLocaleString()}</span>
                </div>
                <div className="zor-hero-stat">
                  <span className="zor-hero-stat-label">Open disputes</span>
                  <span className="zor-hero-stat-value">{openDisputeCount.toLocaleString()}</span>
                </div>
              </>
            )}
          </div>
        </section>

        {idleOverview ? (
          /* ─── Idle: one guiding readiness card replaces the empty-panel wall. */
          <section className="panel zor-panel zor-readiness-card">
            <div className="zor-section-header">
              <div>
                <h2>Oracle readiness</h2>
                <p>The authority is live; the data plane is awaiting its first feed.</p>
              </div>
              <span className="zor-subtle-chip zor-chip-ok">Authority ready</span>
            </div>
            <div className="zor-readiness-grid">
              <div>
                <h3 className="zor-readiness-subhead">Ready</h3>
                <div className="zor-health-list">
                  <div className="zor-health-row"><span>Replay verifier</span><strong style={{ color: 'var(--accent-green)' }}>OK</strong></div>
                  <div className="zor-health-row"><span>Authority</span><strong>{authorityReady ? 'Production ready' : 'Pending'}</strong></div>
                  <div className="zor-health-row"><span>Active signers</span><strong>{authoritySignerCount}</strong></div>
                </div>
              </div>
              <div>
                <h3 className="zor-readiness-subhead">Awaiting first feed</h3>
                <div className="zor-health-list">
                  {readinessAwaiting.map(([label, value]) => (
                    <div className="zor-health-row" key={label}>
                      <span>{label}</span>
                      <strong className={value > 0 ? '' : 'zor-muted'}>{value}</strong>
                    </div>
                  ))}
                </div>
              </div>
            </div>
          </section>
        ) : (
          <>
            {/* ─── Compact metric ribbon (kept; reduced visual weight by
                  following the hero, not preceding it). */}
            <div className="zor-metrics">
              {metrics.map((metric) => (
                <MetricCard key={metric.id} metric={metric} />
              ))}
            </div>

            {/* ─── Top feeds — paginated to 5 with "View all" link. */}
            <section className="panel zor-panel zor-feeds-panel">
              <div className="zor-section-header">
                <div>
                  <h2>Top Feeds</h2>
                  <p>{timeRange} operational view with evidence and freshness state.</p>
                </div>
                <div className="zor-section-actions">
                  <span className="zor-subtle-chip">{visibleFeedCount} feeds</span>
                  {visibleFeedCount > TOP_FEED_LIMIT && (
                    <button
                      type="button"
                      className="zor-link-button"
                      onClick={() => setActiveSection('Feeds')}
                    >
                      View all →
                    </button>
                  )}
                </div>
              </div>
              <FeedTable
                feeds={topFeeds}
                selectedFeedId={selectedFeed.id}
                onSelectFeed={setSelectedFeedId}
                onCreate={() => setShowFeedCreationModal(true)}
              />
            </section>

            <div className="zor-two-up">
              <HealthPanel summary={remoteData?.summary} demoMode={demoMode} />
              <EvidencePanel summary={remoteData?.summary} reads={remoteData?.acceptedReads} demoMode={demoMode} />
            </div>
            <AuthorizationTrailPanel items={authorizationTrail} />
            <SourceDiversityPanel sources={sources} />

            {/* ─── Write-flow CTAs: each opens a focus-trapped modal so the
                  landing page stays calm. */}
            <section className="zor-action-row">
              <button
                type="button"
                className="btn btn-secondary zor-action-cta"
                onClick={() => setShowFeedCreationModal(true)}
              >
                + Create feed
              </button>
              <button
                type="button"
                className="btn btn-secondary zor-action-cta"
                onClick={() => setShowReporterOnboardingModal(true)}
              >
                + Register reporter
              </button>
              <button
                type="button"
                className="btn btn-secondary zor-action-cta"
                onClick={() => setShowReceiptBuilderModal(true)}
              >
                + Build receipt
              </button>
            </section>
          </>
        )}

        {/* ─── Diagnostics — all of the deep panels behind one disclosure
              so the operator sees them only on demand. */}
        <details className="zor-diagnostics panel">
          <summary className="zor-diagnostics-summary">
            <span className="zor-diagnostics-title">Diagnostics</span>
            <span className="zor-diagnostics-hint">
              Reporters · rewards · consumer profiles · events
            </span>
          </summary>
          <div className="zor-diagnostics-body">
            <ReporterPanel reporters={reporters} />
            <RewardsPanel rewards={rewards} />
            <ConsumerProfilePanel />
            <EventsPanel events={authorizationTrail} demoMode={demoMode} />
          </div>
        </details>
      </>
    );
  })();

  return (
    <div className="zor-shell">
      <section className="zor-dashboard">
        {/* Section tab strip + live posture chips. No duplicate brand
            lockup, no placeholder "Connect Wallet" or "D" theme button —
            the main app header handles wallet + theme. */}
        <div className="zor-section-bar">
          <nav className="zor-product-nav" aria-label="ZenoOracle sections">
            {ORACLE_SECTIONS.map((item) => (
              <button
                key={item}
                className={item === activeSection ? 'zor-product-nav-active' : ''}
                onClick={() => setActiveSection(item)}
                type="button"
              >
                {item}
              </button>
            ))}
          </nav>
          <div className="zor-section-bar-meta">
            <span className="zor-env">
              <span />
              {apiState}
            </span>
            <span
              className={`zor-authority-chip ${authorityReady ? 'zor-authority-ready' : 'zor-authority-blocked'}`}
              title={authorityTitle}
            >
              {authorityLabel}
            </span>
            {oracleSmokeStatus ? <span className="zor-subtle-chip">{oracleSmokeStatus}</span> : null}
            <button
              className="btn btn-secondary btn-xs"
              type="button"
              onClick={() => setIsRailCollapsed(!isRailCollapsed)}
              style={{ display: 'inline-flex', alignItems: 'center', gap: '4px', whiteSpace: 'nowrap' }}
            >
              {isRailCollapsed ? 'Show Action Rail →' : '← Hide Action Rail'}
            </button>
            <span className="zor-subtle-chip" title="Wallet controls live in the main header">
              {wallet?.address ? `Wallet ${compactId(wallet.address)}` : 'Wallet in header'}
            </span>
          </div>
        </div>

        <div className="zor-workspace" style={isRailCollapsed ? { gridTemplateColumns: 'minmax(0, 1fr)' } : {}}>
          <div className="zor-core-column">
            <div className="zor-overview-heading">
              <div>
                <h2>{activeSection === 'Overview' ? 'Oracle Overview' : activeSection}</h2>
                <p>{sectionCopy}</p>
              </div>
              <div className="zor-overview-controls">
                <select
                  className="input"
                  value={feedFilter}
                  onChange={(event) => setFeedFilter(event.target.value)}
                  aria-label="Feed status filter"
                >
                  <option value="all">All feeds</option>
                  <option value="fresh">Fresh</option>
                  <option value="devnet-only">Devnet only</option>
                  <option value="high-uncertainty">High uncertainty</option>
                </select>
                <select
                  className="input"
                  value={timeRange}
                  onChange={(event) => setTimeRange(event.target.value)}
                  aria-label="Time range"
                >
                  <option>1h</option>
                  <option>6h</option>
                  <option>24h</option>
                  <option>7d</option>
                  <option>30d</option>
                </select>
              </div>
            </div>
            {coreContent}
            {activeSection === 'Overview' && hasRealFeed && (
              <FeedDetailInspector
                key={selectedFeed?.receiptId || selectedFeed?.feed || 'feed-detail'}
                feed={selectedFeed}
                reporters={reporters}
                disputes={disputes}
                onAddDispute={handleAddDispute}
                demoMode={demoMode}
              />
            )}
          </div>

          {!isRailCollapsed && (
            <aside className="zor-side-rail" aria-label="Oracle action rail">
              {hasRealFeed ? (
                <>
                  {activeSection === 'Receipts' || activeSection === 'Reports' ? null : (
                    <LatestRead feed={selectedFeed} onVerifyReceipt={handleVerifyReceipt} onViewAll={() => setActiveSection("Receipts")} />
                  )}
                  <FeedStatusPanel feed={selectedFeed} />
                </>
              ) : (
                <section className="panel zor-panel">
                  <div className="zor-empty-state zor-empty-compact" role="status">
                    <strong>No feed selected</strong>
                    <p>Create a feed to inspect its accepted reads, fund its budget, and verify receipts.</p>
                  </div>
                </section>
              )}
              <VerifyPanel key={verifyReceiptId || 'verify'} initialReceiptId={verifyReceiptId} />
              <ServicesPanel summary={remoteData?.summary} authorityStatus={remoteData?.authorityStatus} demoMode={demoMode} />
            </aside>
          )}
        </div>
        <FeatureStrip />
      </section>

      {/* ─── Modals — opened from the action CTAs on the Overview tab.
            Each wraps an existing inline panel component verbatim, so
            the form logic stays identical. */}
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
        description="Aggregate, read, or authorize. The build flow is identical to the side-rail form; it just lives here so the dashboard stays calm."
        size="lg"
      >
        <ReceiptBuilderPanel feed={selectedFeed} />
      </Modal>
    </div>
  );
}

export default ZenoOracleDashboard;
