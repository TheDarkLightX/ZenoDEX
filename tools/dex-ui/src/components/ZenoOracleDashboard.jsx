import { useEffect, useMemo, useRef, useState } from 'react';
import {
  ORACLE_CONSUMER_PROFILES,
  ORACLE_DISPUTES,
  ORACLE_EVENTS,
  ORACLE_EVIDENCE_DISTRIBUTION,
  ORACLE_FEEDS,
  ORACLE_HEALTH_METRICS,
  ORACLE_NETWORK_SUMMARY,
  ORACLE_REPORTERS,
  ORACLE_REWARDS,
  ORACLE_SYSTEM_SERVICES,
} from './ZenoOracleDashboardData';
import { getRuntimeConfig } from '../lib/api.js';
import './ZenoOracleDashboard.css';

const ZENO_ORACLE_ICON = `${import.meta.env.BASE_URL}branding/zeno-oracle/zeno_oracle_icon_256.png`;
const DEFAULT_ZENO_ORACLE_API_BASE = 'http://127.0.0.1:8787';

function normalizeOracleApiBase(raw) {
  const value = (raw ?? '').toString().trim();
  if (!value) {
    return '';
  }
  return value.endsWith('/') ? value.slice(0, -1) : value;
}

function zenoOracleApiUrl(path) {
  const runtimeBase = normalizeOracleApiBase(getRuntimeConfig().zenoOracleApiBase);
  const envBase = normalizeOracleApiBase(import.meta.env.VITE_ZENO_ORACLE_API_URL);
  return `${runtimeBase || envBase || DEFAULT_ZENO_ORACLE_API_BASE}${path}`;
}

const STATUS_COPY = {
  fresh: 'Fresh',
  stale: 'Stale',
  disputed: 'Disputed',
  'devnet-only': 'Devnet only',
  'high-uncertainty': 'High uncertainty',
};

const ORACLE_SECTIONS = [
  'Overview',
  'Feeds',
  'Reports',
  'Reporters',
  'Disputes',
  'Receipts',
  'Verify',
  'Governance',
];

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

const ORACLE_FEATURES = [
  {
    id: 'proof_bound',
    title: 'Proof-Bound',
    detail: 'Values stay tied to provenance, policy, and receipts.',
  },
  {
    id: 'action_specific',
    title: 'Action-Specific',
    detail: 'One authorization is valid for one exact action.',
  },
  {
    id: 'verifiable',
    title: 'Verifiable',
    detail: 'Consumers can replay reads and terminal receipts.',
  },
  {
    id: 'economic',
    title: 'Economically Secure',
    detail: 'Critical profiles bind value to attack-cost envelopes.',
  },
  {
    id: 'permissionless',
    title: 'Permissionless',
    detail: 'Report, dispute, and earn through bounded work.',
  },
];

const ORACLE_PALETTE = [
  { name: 'Primary', value: '#8B5CF6' },
  { name: 'Secondary', value: '#6366F1' },
  { name: 'Success', value: '#22C55E' },
  { name: 'Warning', value: '#F59E0B' },
  { name: 'Danger', value: '#EF4444' },
  { name: 'Info', value: '#06B6D4' },
  { name: 'Neutral', value: '#94A3B8' },
];

const ORACLE_SPACING = ['4', '8', '12', '16', '24', '32', '48', '64', '96'];
const ORACLE_RADII = ['4px', '8px', '12px', '16px', '24px'];
const ORACLE_ICON_GLYPHS = ['S', 'V', 'T', 'C', 'W', 'R', 'P', 'G', 'Q', 'A', 'D', 'K'];

function compactId(value) {
  if (!value) return 'none';
  const text = String(value);
  if (text.length <= 18) return text;
  return `${text.slice(0, 10)}...${text.slice(-6)}`;
}

function formatE8(value, digits = 4) {
  if (value === null || value === undefined) return 'No value';
  return (Number(value) / 100000000).toLocaleString(undefined, {
    maximumFractionDigits: digits,
  });
}

function formatTokenE8(value, symbol = 'ZORACLE') {
  return `${formatE8(value, 2)} ${symbol}`;
}

function demoHash(seed) {
  return `sha256:${seed.repeat(64)}`;
}

function getInitialOracleSection() {
  if (typeof window === 'undefined') {
    return 'Overview';
  }
  const requested = new URLSearchParams(window.location.search).get('oracleView');
  return ORACLE_SECTIONS.find((section) => section.toLowerCase() === String(requested || '').toLowerCase())
    || 'Overview';
}

function primaryStatus(labels = []) {
  if (labels.includes('disputed')) return 'disputed';
  if (labels.includes('high-uncertainty')) return 'high-uncertainty';
  if (labels.includes('stale')) return 'stale';
  if (labels.includes('fresh')) return 'fresh';
  if (labels.includes('devnet-only')) return 'devnet-only';
  return labels[0] || 'stale';
}

function snapshotToDashboardData(snapshot) {
  const summary = snapshot.summary || {};
  const feedStatuses = Array.isArray(snapshot.feed_statuses) ? snapshot.feed_statuses : [];
  const reporters = Array.isArray(snapshot.reporters) ? snapshot.reporters : [];
  const sources = Array.isArray(snapshot.sources) ? snapshot.sources : [];
  const disputes = Array.isArray(snapshot.disputes) ? snapshot.disputes : [];
  const rewards = Array.isArray(snapshot.rewards) ? snapshot.rewards : [];
  const acceptedReads = Array.isArray(snapshot.recent_accepted_reads) ? snapshot.recent_accepted_reads : [];
  const authorizations = Array.isArray(snapshot.recent_authorizations) ? snapshot.recent_authorizations : [];
  const rewardReceipts = Array.isArray(snapshot.recent_reward_receipts) ? snapshot.recent_reward_receipts : [];
  const slashReceipts = Array.isArray(snapshot.recent_slash_receipts) ? snapshot.recent_slash_receipts : [];
  const authorityStatus = snapshot.authority_status || {
    production_authority: snapshot.production_authority === true,
    status: snapshot.production_authority === true ? 'ready' : 'blocked',
    readiness_gaps: [],
  };

  return {
    authorityStatus,
    feeds: feedStatuses.map((feed) => {
      const pair = `${feed.base_asset || 'UNKNOWN'}/${feed.quote_asset || 'UNKNOWN'}`;
      const status = primaryStatus(feed.status || []);
      return {
        id: feed.query_id,
        feed: pair,
        domain: `${feed.asset_class || 'crypto'} / ${feed.query_type || 'spot_price'}`,
        queryId: feed.query_id,
        value: formatE8(feed.latest_value_e8),
        unit: feed.quote_asset || '',
        reference: feed.feed_id || pair,
        change24h: '+0.00%',
        evidenceClass: feed.evidence_floor || 'O3',
        freshness:
          feed.expires_at_epoch === null || feed.expires_at_epoch === undefined
            ? 'no accepted read'
            : `${Math.max(0, Number(feed.expires_at_epoch) - Number(feed.now_epoch || 0))} epoch window`,
        status,
        confidence: feed.confidence_e8 === null || feed.confidence_e8 === undefined
          ? 'n/a'
          : `+/-${formatE8(feed.confidence_e8)}`,
        deviationBps: feed.deviation_bps ?? 0,
        receiptId: compactId(feed.latest_read_id || feed.latest_aggregate_id),
        receiptFullId: feed.latest_read_id || feed.latest_aggregate_id || '',
        actionUse: feed.source_policy_id || 'source policy pending',
      };
    }),
    reporters: reporters.map((reporter) => ({
      id: compactId(reporter.reporter_id),
      status: reporter.slash_state === 'slashed' ? 'quarantined' : reporter.active ? 'active' : 'pending',
      bond: `${formatE8(reporter.bond_amount_e8, 2)} ${reporter.bond_asset || 'ZORACLE'}`,
      requiredBond: `${formatE8(reporter.required_bond_e8, 2)} ${reporter.bond_asset || 'ZORACLE'}`,
      accepted: reporter.last_sequence || 0,
      missed: 0,
      rewards: 'ledger-backed',
      controlGroup: reporter.control_group_id || reporter.reporter_id,
    })),
    disputes: disputes.map((dispute) => ({
      id: compactId(dispute.dispute_id),
      feed: compactId(dispute.report_id),
      target: compactId(dispute.report_id),
      reporter: compactId(dispute.reporter_id),
      bond: `${formatE8(dispute.bond_e8, 2)} ZORACLE`,
      age: dispute.opened_epoch ? `epoch ${dispute.opened_epoch}` : 'unknown',
      status: dispute.status === 'open' ? 'open' : dispute.status === 'upheld' ? 'quarantined' : 'closed',
    })),
    rewards: rewards.map((reward) => ({
      id: compactId(reward.reporter_id),
      reporter: compactId(reward.reporter_id),
      pending: formatTokenE8(reward.pending_rewards_e8),
      paid: formatTokenE8(reward.paid_rewards_e8),
      slashed: formatTokenE8(reward.slashed_rewards_e8),
      accepted: reward.accepted_report_count || 0,
      status: Number(reward.slashed_rewards_e8 || 0) > 0 || Number(reward.slash_debt_e8 || 0) > 0
        ? 'quarantined'
        : Number(reward.pending_rewards_e8 || 0) > 0
          ? 'payable'
          : 'settled',
    })),
    sources: sources.map((source) => ({
      id: compactId(source.source_id),
      sourceId: source.source_id,
      kind: source.source_kind || 'source',
      assurance: source.assurance_class || 'S0',
      controlGroup: source.source_control_group_id || 'unregistered',
      venue: source.venue_id || 'venue pending',
      dataFamily: source.data_family_id || 'data policy pending',
      transport: source.transport_id || 'transport pending',
      jurisdiction: source.jurisdiction || 'global',
      status: source.active ? 'fresh' : 'stale',
      queryCount: Array.isArray(source.query_ids) ? source.query_ids.length : 0,
    })),
    authorizationTrail: [
      ...authorizations.slice(-6).map((bundle) => ({
        id: compactId(bundle.authorization_id),
        kind: bundle.authorization?.action_kind || 'authorization',
        consumer: bundle.authorization?.consumer_module || 'consumer',
        queryId: compactId(bundle.authorization?.query_id),
        value: formatE8(bundle.authorization?.value_e8),
        evidenceClass: bundle.authorization?.evidence_class || 'O3',
        epoch: bundle.authorization?.observed_epoch ?? 'n/a',
        root: compactId(bundle.authorization?.receipt_graph_root),
        status: 'fresh',
      })),
      ...acceptedReads.slice(-6).map((read) => ({
        id: compactId(read.read_id),
        kind: 'accepted read',
        consumer: read.consumer_module || 'consumer',
        queryId: compactId(read.query_id),
        value: formatE8(read.value_e8),
        evidenceClass: read.evidence_class || 'O3',
        epoch: read.observed_epoch ?? 'n/a',
        root: compactId(read.aggregate_id),
        status: 'devnet-only',
      })),
      ...rewardReceipts.slice(-6).map((receipt) => ({
        id: compactId(receipt.reward_entry_id),
        kind: 'reward receipt',
        consumer: compactId(receipt.reporter_id),
        queryId: 'reward ledger',
        value: formatTokenE8(receipt.pending_rewards_e8),
        evidenceClass: null,
        epoch: 'n/a',
        root: compactId(receipt.reward_entry_id),
        status: 'fresh',
      })),
      ...slashReceipts.slice(-6).map((receipt) => ({
        id: compactId(receipt.slash_settlement_id),
        kind: 'slash receipt',
        consumer: compactId(receipt.reporter_id),
        queryId: compactId(receipt.dispute_id),
        value: formatTokenE8(receipt.slash_e8),
        evidenceClass: null,
        epoch: receipt.resolved_epoch ?? 'n/a',
        root: compactId(receipt.slash_settlement_id),
        status: 'disputed',
      })),
    ].slice(0, 8),
    metrics: [
      {
        id: 'accepted_reads',
        label: 'Accepted Reads',
        value: String(summary.accepted_read_count || 0),
        delta: `${summary.o3_plus_read_count || 0} O3+`,
        tone: 'positive',
        detail: 'Replay-bound reads',
      },
      {
        id: 'active_feeds',
        label: 'Active Feeds',
        value: String(summary.active_feed_count || 0),
        delta: `${summary.feed_status_count || 0} tracked`,
        tone: 'positive',
        detail: 'Local query registry',
      },
      {
        id: 'reporters',
        label: 'Reporters',
        value: String(summary.reporter_count || 0),
        delta: `${summary.active_reporter_count || 0} active`,
        tone: 'positive',
        detail: 'Bonded registry state',
      },
      {
        id: 'sources',
        label: 'Sources',
        value: String(summary.source_count || 0),
        delta: `${summary.active_source_count || 0} active`,
        tone: 'neutral',
        detail: 'Registered source policy',
      },
      {
        id: 'open_disputes',
        label: 'Open Disputes',
        value: String(summary.open_dispute_count || 0),
        delta: `${summary.upheld_dispute_count || 0} upheld`,
        tone: summary.open_dispute_count ? 'warning' : 'positive',
        detail: 'Quarantine-aware',
      },
      {
        id: 'replay',
        label: 'Replay',
        value: summary.replay_ok ? 'OK' : 'Fail',
        delta: summary.authorization_count ? `${summary.authorization_count} auth` : 'local',
        tone: summary.replay_ok ? 'positive' : 'warning',
        detail: 'Deterministic verifier',
      },
    ],
  };
}

function EvidenceBadge({ value }) {
  return <span className={`zor-evidence zor-evidence-${value}`}>{value}</span>;
}

function StatusPill({ status }) {
  return <span className={`zor-status zor-status-${status}`}>{STATUS_COPY[status] || status}</span>;
}

function MetricSparkline({ tone }) {
  const points = tone === 'warning'
    ? '2,22 15,19 27,20 38,14 50,18 61,12 72,16 84,7 94,10'
    : '2,24 14,21 25,23 37,14 48,17 58,11 70,15 82,7 94,9';

  return (
    <svg className={`zor-sparkline zor-sparkline-${tone}`} viewBox="0 0 96 28" aria-hidden="true">
      <polyline points={points} />
    </svg>
  );
}

function MetricCard({ metric }) {
  return (
    <article className={`zor-metric zor-metric-${metric.tone}`}>
      <span className="zor-metric-label">{metric.label}</span>
      <strong>{metric.value}</strong>
      <span className="zor-metric-delta">{metric.delta}</span>
      <MetricSparkline tone={metric.tone} />
      <span className="zor-metric-detail">{metric.detail}</span>
    </article>
  );
}

function FeedTable({ feeds, selectedFeedId, onSelectFeed }) {
  return (
    <div className="zor-table-wrap" role="region" aria-label="Oracle feeds">
      <div className="zor-feed-head">
        <span>Feed</span>
        <span>Value</span>
        <span>24h</span>
        <span>Evidence</span>
        <span>Freshness</span>
        <span>Status</span>
      </div>
      {feeds.map((feed) => (
        <button
          key={feed.id}
          type="button"
          className={`zor-feed-row ${selectedFeedId === feed.id ? 'zor-feed-row-active' : ''}`}
          onClick={() => onSelectFeed(feed.id)}
        >
          <span>
            <strong>{feed.feed}</strong>
            <small>{feed.domain}</small>
          </span>
          <span>
            <strong>{feed.value}</strong>
            <small>{feed.unit}</small>
          </span>
          <span className={feed.change24h.startsWith('-') ? 'zor-red' : 'zor-green'}>
            {feed.change24h}
          </span>
          <EvidenceBadge value={feed.evidenceClass} />
          <span>{feed.freshness}</span>
          <StatusPill status={feed.status} />
        </button>
      ))}
    </div>
  );
}

function HealthPanel() {
  return (
    <section className="panel zor-panel">
      <div className="zor-section-header">
        <div>
          <h2>Network Health</h2>
          <p>Critical services must stay replayable before reads become usable.</p>
        </div>
        <span className="zor-subtle-chip">98.7%</span>
      </div>
      <div className="zor-health-layout">
        <div className="zor-health-ring" aria-label="Network health 98.7 percent">
          <span>98.7%</span>
          <small>Excellent</small>
        </div>
        <div className="zor-health-list">
          {ORACLE_HEALTH_METRICS.map((metric) => (
            <div key={metric.id} className="zor-health-row">
              <span>{metric.label}</span>
              <strong>{metric.value.toFixed(1)}%</strong>
            </div>
          ))}
        </div>
      </div>
    </section>
  );
}

function LatestRead({ feed, onVerifyReceipt }) {
  return (
    <section className="panel zor-panel">
      <div className="zor-section-header">
        <div>
          <h2>Latest Accepted Read</h2>
          <p>Bound to query, value hash, policy roots, and receipt graph.</p>
        </div>
        <button className="zor-text-button" type="button">View all</button>
      </div>
      <div className="zor-read-grid">
        <div>
          <span className="zor-label">Feed</span>
          <strong>{feed.feed}</strong>
        </div>
        <div>
          <span className="zor-label">Value</span>
          <strong>{feed.value}</strong>
        </div>
        <div>
          <span className="zor-label">Confidence</span>
          <strong>{feed.confidence}</strong>
        </div>
        <div>
          <span className="zor-label">Deviation</span>
          <strong>{feed.deviationBps} bps</strong>
        </div>
      </div>
      <div className="zor-receipt-box">
        <span>Receipt</span>
        <code>{feed.receiptId}</code>
      </div>
      <div className="zor-read-foot">
        <span>
          <small>Evidence</small>
          <EvidenceBadge value={feed.evidenceClass} />
        </span>
        <span>
          <small>Action use</small>
          <strong>{feed.actionUse}</strong>
        </span>
      </div>
      <button
        className="btn btn-primary zor-wide-btn"
        type="button"
        onClick={() => onVerifyReceipt?.(feed.receiptFullId || feed.receiptId)}
        disabled={!feed.receiptFullId && !feed.receiptId}
      >
        Verify Receipt
      </button>
    </section>
  );
}

function VerifyPanel({ initialReceiptId = '' }) {
  const [receiptId, setReceiptId] = useState(initialReceiptId);
  const [status, setStatus] = useState(initialReceiptId ? 'Ready to replay' : 'Waiting for receipt ID');

  useEffect(() => {
    const nextId = String(initialReceiptId || '').trim();
    if (!nextId || nextId === receiptId) {
      return;
    }
    setReceiptId(nextId);
    setStatus('Ready to replay');
  }, [initialReceiptId, receiptId]);

  async function verifyReceipt() {
    const id = receiptId.trim();
    if (id.length <= 8) {
      setStatus('Waiting for receipt ID');
      return;
    }
    setStatus('Replaying...');
    try {
      const response = await fetch(
        zenoOracleApiUrl(`/api/oracle/verify-receipt?id=${encodeURIComponent(id)}`),
      );
      const payload = await response.json();
      if (!response.ok || payload.ok === false) {
        const error = payload.error || payload.receipt_check?.errors?.[0] || 'Verification failed';
        setStatus(error);
        return;
      }
      setStatus(`${payload.receipt_check.receipt_kind} OK`);
    } catch {
      setStatus('Start local API to verify receipts');
    }
  }

  return (
    <section className="panel zor-panel">
      <div className="zor-section-header">
        <div>
          <h2>Quick Verify</h2>
          <p>Replay a receipt or action-specific authorization locally.</p>
        </div>
        <span className="zor-subtle-chip">deterministic</span>
      </div>
      <div className="zor-drop-zone">
        <span className="zor-drop-mark">RX</span>
        <strong>Drop receipt JSON</strong>
        <small>Accepted read, aggregate, dispute, reward, or authorization bundle</small>
      </div>
      <div className="zor-inline-form">
        <input
          className="input"
          type="text"
          value={receiptId}
          onChange={(event) => {
            setReceiptId(event.target.value);
            setStatus(event.target.value.trim().length > 8 ? 'Ready to replay' : 'Waiting for receipt ID');
          }}
          placeholder="Enter receipt ID"
          aria-label="Receipt ID"
        />
        <button
          className="btn btn-primary"
          type="button"
          onClick={verifyReceipt}
          disabled={receiptId.trim().length <= 8}
        >
          Verify
        </button>
      </div>
      <span className="zor-verify-state">{status}</span>
    </section>
  );
}

function DisputesPanel({ disputes }) {
  const [reportId, setReportId] = useState('');
  const [reporterId, setReporterId] = useState('');
  const [disputeId, setDisputeId] = useState('');
  const [slashAmount, setSlashAmount] = useState('100000000');
  const [status, setStatus] = useState('Ready');

  async function post(path, payload) {
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

  async function openDispute() {
    setStatus('Opening dispute...');
    try {
      const payload = await post('/api/oracle/dispute/open', {
        report_id: reportId,
        reporter_id: reporterId,
        bond_e8: 10000000,
        reason: 'operator-review',
      });
      setDisputeId(payload.dispute_id || '');
      setStatus(`Opened ${compactId(payload.dispute_id)}`);
    } catch (error) {
      setStatus(String(error.message || error));
    }
  }

  async function resolveDispute(outcome) {
    setStatus(`Resolving ${outcome}...`);
    try {
      const payload = {
        dispute_id: disputeId,
        outcome,
      };
      if (outcome === 'upheld') {
        payload.slash_e8 = Number(slashAmount || 0);
      }
      await post('/api/oracle/dispute/resolve', payload);
      setStatus(`${outcome} ${compactId(disputeId)}`);
    } catch (error) {
      setStatus(String(error.message || error));
    }
  }

  return (
    <section className="panel zor-panel">
      <div className="zor-section-header">
        <div>
          <h2>Active Disputes</h2>
          <p>Open disputes can quarantine critical consumers.</p>
        </div>
        <span className="zor-subtle-chip">{disputes.length} open</span>
      </div>
      <div className="zor-dispute-list">
        {disputes.map((dispute) => (
          <article key={dispute.id} className="zor-dispute-row">
            <div>
              <strong>{dispute.feed}</strong>
              <small>{dispute.target}</small>
            </div>
            <div>
              <span>{dispute.bond}</span>
              <small>{dispute.age}</small>
            </div>
            <span className={`zor-status zor-dispute-${dispute.status}`}>{dispute.status}</span>
          </article>
        ))}
      </div>
      <div className="zor-dispute-form">
        <input
          className="input"
          value={reportId}
          onChange={(event) => setReportId(event.target.value)}
          placeholder="Report ID"
          aria-label="Dispute report ID"
        />
        <input
          className="input"
          value={reporterId}
          onChange={(event) => setReporterId(event.target.value)}
          placeholder="Reporter ID"
          aria-label="Dispute reporter ID"
        />
        <button
          className="btn btn-secondary"
          type="button"
          onClick={openDispute}
          disabled={!reportId.trim() || !reporterId.trim()}
        >
          Open
        </button>
        <input
          className="input"
          value={disputeId}
          onChange={(event) => setDisputeId(event.target.value)}
          placeholder="Dispute ID"
          aria-label="Resolve dispute ID"
        />
        <input
          className="input"
          inputMode="numeric"
          value={slashAmount}
          onChange={(event) => setSlashAmount(event.target.value)}
          aria-label="Slash amount e8"
        />
        <div className="zor-button-row zor-button-row-tight">
          <button
            className="btn btn-secondary"
            type="button"
            onClick={() => resolveDispute('rejected')}
            disabled={!disputeId.trim()}
          >
            Reject
          </button>
          <button
            className="btn btn-primary"
            type="button"
            onClick={() => resolveDispute('upheld')}
            disabled={!disputeId.trim()}
          >
            Uphold
          </button>
        </div>
      </div>
      <span className="zor-action-state">{status}</span>
    </section>
  );
}

function FeedStatusPanel({ feed }) {
  const [fundAmount, setFundAmount] = useState('100000000');
  const [fundState, setFundState] = useState('Ready to fund');

  async function fundSelectedFeed() {
    setFundState('Funding...');
    try {
      const response = await fetch(zenoOracleApiUrl('/api/oracle/query/fund'), {
        method: 'POST',
        headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify({
          query_id: feed.queryId,
          amount_e8: Number(fundAmount || 0),
        }),
      });
      const payload = await response.json();
      if (!response.ok || payload.ok === false) {
        setFundState(payload.error || 'Write disabled');
        return;
      }
      setFundState(`Budget ${formatTokenE8(payload.reward_budget_e8)}`);
    } catch {
      setFundState('Start local API with --allow-writes');
    }
  }

  return (
    <section className="panel zor-panel">
      <div className="zor-section-header">
        <div>
          <h2>Feed Status</h2>
          <p>Selected feed readiness for critical or advisory consumers.</p>
        </div>
        <StatusPill status={feed.status} />
      </div>
      <div className="zor-feed-detail-grid">
        <div>
          <span className="zor-label">Query</span>
          <strong>{compactId(feed.queryId)}</strong>
        </div>
        <div>
          <span className="zor-label">Evidence</span>
          <EvidenceBadge value={feed.evidenceClass} />
        </div>
        <div>
          <span className="zor-label">Freshness</span>
          <strong>{feed.freshness}</strong>
        </div>
        <div>
          <span className="zor-label">Deviation</span>
          <strong>{feed.deviationBps} bps</strong>
        </div>
        <div>
          <span className="zor-label">Confidence</span>
          <strong>{feed.confidence}</strong>
        </div>
        <div>
          <span className="zor-label">Consumer use</span>
          <strong>{feed.actionUse}</strong>
        </div>
      </div>
      <div className="zor-inline-form">
        <input
          className="input"
          inputMode="numeric"
          value={fundAmount}
          onChange={(event) => setFundAmount(event.target.value)}
          aria-label="Query budget funding amount e8"
        />
        <button className="btn btn-secondary" type="button" onClick={fundSelectedFeed}>
          Fund
        </button>
      </div>
      <span className="zor-action-state">{fundState}</span>
    </section>
  );
}

function ReceiptBuilderPanel({ feed }) {
  const [aggregateId, setAggregateId] = useState('');
  const [readId, setReadId] = useState('');
  const [consumerModule, setConsumerModule] = useState('zenodex.zusd');
  const [profileId, setProfileId] = useState('critical-zusd-v1');
  const [actionKind, setActionKind] = useState('mint');
  const [status, setStatus] = useState('Ready');

  async function post(path, payload) {
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

  async function buildAggregate() {
    setStatus('Building aggregate...');
    try {
      const payload = await post('/api/oracle/aggregate/build', {
        query_id: feed.queryId,
      });
      setAggregateId(payload.aggregate_id || '');
      setStatus(`Aggregate ${compactId(payload.aggregate_id)}`);
    } catch (error) {
      setStatus(String(error.message || error));
    }
  }

  async function acceptRead() {
    setStatus('Accepting read...');
    try {
      const payload = await post('/api/oracle/read/accept', {
        aggregate_id: aggregateId,
        consumer_module: consumerModule,
        profile_id: profileId,
      });
      setReadId(payload.read_id || '');
      setStatus(`Read ${compactId(payload.read_id)}`);
    } catch (error) {
      setStatus(String(error.message || error));
    }
  }

  async function buildAuthorization() {
    setStatus('Building authorization...');
    try {
      const payload = await post('/api/oracle/authorization/build', {
        read_id: readId,
        action_kind: actionKind,
        action_id: demoHash('2'),
        action_facts_hash: demoHash('3'),
        pre_state_hash: demoHash('4'),
        min_evidence_class: 'O3',
      });
      setStatus(`Authorization ${compactId(payload.authorization_id)}`);
    } catch (error) {
      setStatus(String(error.message || error));
    }
  }

  return (
    <section className="panel zor-panel">
      <div className="zor-section-header">
        <div>
          <h2>Receipt Builder</h2>
          <p>Build aggregate, accepted read, and typed authorization receipts.</p>
        </div>
        <span className="zor-subtle-chip">local</span>
      </div>
      <div className="zor-dispute-form">
        <button className="btn btn-secondary" type="button" onClick={buildAggregate}>
          Build Aggregate
        </button>
        <input
          className="input"
          value={aggregateId}
          onChange={(event) => setAggregateId(event.target.value)}
          placeholder="Aggregate ID"
          aria-label="Aggregate ID"
        />
        <input
          className="input"
          value={consumerModule}
          onChange={(event) => setConsumerModule(event.target.value)}
          aria-label="Consumer module"
        />
        <input
          className="input"
          value={profileId}
          onChange={(event) => setProfileId(event.target.value)}
          aria-label="Consumer profile ID"
        />
        <button
          className="btn btn-secondary"
          type="button"
          onClick={acceptRead}
          disabled={!aggregateId.trim()}
        >
          Accept Read
        </button>
        <input
          className="input"
          value={readId}
          onChange={(event) => setReadId(event.target.value)}
          placeholder="Read ID"
          aria-label="Read ID"
        />
        <input
          className="input"
          value={actionKind}
          onChange={(event) => setActionKind(event.target.value)}
          aria-label="Action kind"
        />
        <button
          className="btn btn-primary"
          type="button"
          onClick={buildAuthorization}
          disabled={!readId.trim()}
        >
          Build Authorization
        </button>
      </div>
      <span className="zor-action-state">{status}</span>
    </section>
  );
}

function FeedCreationPanel() {
  const [assetPair, setAssetPair] = useState('AGRS/ZDEX');
  const [evidenceFloor, setEvidenceFloor] = useState('O3');
  const [freshness, setFreshness] = useState('2');
  const [reportReward, setReportReward] = useState('1000000');
  const [rewardBudget, setRewardBudget] = useState('100000000');
  const [saveState, setSaveState] = useState('Draft only');
  const policyStatus = evidenceFloor === 'O2' ? 'Devnet only' : 'Critical-use eligible after review';

  async function saveDraftFeed() {
    const [baseAsset, quoteAsset] = assetPair.split('/').map((part) => part.trim().toUpperCase());
    if (!baseAsset || !quoteAsset) {
      setSaveState('Use BASE/QUOTE');
      return;
    }
    setSaveState('Saving...');
    try {
      const response = await fetch(zenoOracleApiUrl('/api/oracle/query/register'), {
        method: 'POST',
        headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify({
          base_asset: baseAsset,
          quote_asset: quoteAsset,
          evidence_floor: evidenceFloor,
          freshness_window_epochs: Number(freshness || 1),
          source_policy_id:
            evidenceFloor === 'O2'
              ? 'source-policy:declared-diverse-v1'
              : 'source-policy:registered-diverse-v1',
          min_reporters: evidenceFloor === 'O2' ? 1 : 3,
          report_reward_e8: Number(reportReward || 0),
          reward_budget_e8: Number(rewardBudget || 0),
        }),
      });
      const payload = await response.json();
      if (!response.ok || payload.ok === false) {
        setSaveState(payload.error || 'Write disabled');
        return;
      }
      setSaveState(`Saved ${compactId(payload.query_id)}`);
    } catch {
      setSaveState('Start local API with --allow-writes');
    }
  }

  return (
    <section className="panel zor-panel zor-form-panel">
      <div className="zor-section-header">
        <div>
          <h2>Create Feed</h2>
          <p>Draft a query policy before reporters can earn from it.</p>
        </div>
        <span className="zor-subtle-chip">proposal</span>
      </div>
      <div className="zor-form-grid">
        <label>
          <span className="label">Pair or reference</span>
          <input
            className="input"
            value={assetPair}
            onChange={(event) => setAssetPair(event.target.value)}
          />
        </label>
        <label>
          <span className="label">Evidence floor</span>
          <select
            className="input"
            value={evidenceFloor}
            onChange={(event) => setEvidenceFloor(event.target.value)}
          >
            <option>O2</option>
            <option>O3</option>
            <option>O4</option>
            <option>O5</option>
          </select>
        </label>
        <label>
          <span className="label">Freshness window</span>
          <input
            className="input"
            type="number"
            min="1"
            max="24"
            value={freshness}
            onChange={(event) => setFreshness(event.target.value)}
          />
        </label>
        <label>
          <span className="label">Report reward e8</span>
          <input
            className="input"
            inputMode="numeric"
            value={reportReward}
            onChange={(event) => setReportReward(event.target.value)}
          />
        </label>
        <label>
          <span className="label">Initial budget e8</span>
          <input
            className="input"
            inputMode="numeric"
            value={rewardBudget}
            onChange={(event) => setRewardBudget(event.target.value)}
          />
        </label>
      </div>
      <div className="zor-policy-preview">
        <span>{assetPair}</span>
        <strong>{policyStatus}</strong>
        <small>
          {freshness || 0} epoch max age, {evidenceFloor === 'O2' ? 'declared' : 'registered'} source policy,
          {' '}reward {formatTokenE8(reportReward || 0)}, budget {formatTokenE8(rewardBudget || 0)}
        </small>
      </div>
      <button className="btn btn-secondary zor-wide-btn" type="button" onClick={saveDraftFeed}>
        Save Draft Feed
      </button>
      <span className="zor-action-state">{saveState}</span>
    </section>
  );
}

function ReporterOnboardingPanel({ selectedFeed }) {
  const [status, setStatus] = useState('Ready');
  const [reportPrice, setReportPrice] = useState('123456789');
  const [sourceId, setSourceId] = useState('source:manual');
  const steps = [
    { id: 'identity', label: 'Create identity', status: 'available' },
    { id: 'register', label: 'Register reporter', status: 'available' },
    { id: 'bond', label: 'Post bond', status: 'required' },
    { id: 'submit', label: 'Submit signed reports', status: 'required' },
  ];

  async function post(path, payload) {
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

  async function createIdentity() {
    setStatus('Creating identity...');
    try {
      const payload = await post('/api/oracle/identity/create', {});
      setStatus(`Identity ${compactId(payload.reporter_id)}`);
    } catch (error) {
      setStatus(String(error.message || error));
    }
  }

  async function registerAndBond() {
    setStatus('Registering reporter...');
    try {
      await post('/api/oracle/reporter/register', {
        query_id: selectedFeed.queryId,
        required_bond_e8: 100000000,
      });
      await post('/api/oracle/reporter/bond', { amount_e8: 100000000 });
      setStatus(`Bonded for ${selectedFeed.feed}`);
    } catch (error) {
      setStatus(String(error.message || error));
    }
  }

  async function submitReport() {
    setStatus('Submitting report...');
    try {
      const payload = await post('/api/oracle/report/submit', {
        query_id: selectedFeed.queryId,
        price_e8: Number(reportPrice),
        source_observed_epoch: Math.max(1, Math.floor(Date.now() / 1000)),
        source_id: sourceId,
      });
      setStatus(`Report ${compactId(payload.report_id)}`);
    } catch (error) {
      setStatus(String(error.message || error));
    }
  }

  return (
    <section className="panel zor-panel">
      <div className="zor-section-header">
        <div>
          <h2>Reporter Onboarding</h2>
          <p>Rewards are earned work payouts from funded query budgets.</p>
        </div>
        <span className="zor-subtle-chip">CLI-backed</span>
      </div>
      <div className="zor-step-list">
        {steps.map((step, index) => (
          <div key={step.id} className="zor-step-row">
            <span className="zor-step-index">{index + 1}</span>
            <strong>{step.label}</strong>
            <small>{step.status}</small>
          </div>
        ))}
      </div>
      <div className="zor-button-row">
        <button className="btn btn-secondary" type="button" onClick={createIdentity}>
          Create Identity
        </button>
        <button className="btn btn-primary" type="button" onClick={registerAndBond}>
          Register + Bond
        </button>
      </div>
      <div className="zor-report-submit-grid">
        <label>
          <span className="label">Source ID</span>
          <input
            className="input"
            value={sourceId}
            onChange={(event) => setSourceId(event.target.value)}
          />
        </label>
        <label>
          <span className="label">Price e8</span>
          <input
            className="input"
            inputMode="numeric"
            value={reportPrice}
            onChange={(event) => setReportPrice(event.target.value)}
          />
        </label>
        <button className="btn btn-secondary" type="button" onClick={submitReport}>
          Submit Report
        </button>
      </div>
      <span className="zor-action-state">{status}</span>
    </section>
  );
}

function ReporterPanel({ reporters }) {
  return (
    <section className="panel zor-panel">
      <div className="zor-section-header">
        <div>
          <h2>Reporter Health</h2>
          <p>Bond, liveness, and control-group state for active reporters.</p>
        </div>
        <span className="zor-subtle-chip">{reporters.length} sampled</span>
      </div>
      <div className="zor-reporter-table">
        <div className="zor-reporter-head">
          <span>Reporter</span>
          <span>Bond</span>
          <span>Accepted</span>
          <span>Missed</span>
          <span>Status</span>
        </div>
        {reporters.map((reporter) => (
          <div key={reporter.id} className="zor-reporter-row">
            <span>
              <strong>{reporter.id}</strong>
              <small>{reporter.controlGroup}</small>
            </span>
            <span>{reporter.bond}</span>
            <span>{reporter.accepted}</span>
            <span>{reporter.missed}</span>
            <span className={`zor-status zor-reporter-${reporter.status}`}>{reporter.status}</span>
          </div>
        ))}
      </div>
    </section>
  );
}

function RewardsPanel({ rewards }) {
  const [payAmount, setPayAmount] = useState('');
  const [payState, setPayState] = useState('Ready');

  async function payLocalRewards() {
    setPayState('Paying...');
    try {
      const payload = {};
      if (payAmount.trim()) {
        payload.amount_e8 = Number(payAmount);
      }
      const response = await fetch(zenoOracleApiUrl('/api/oracle/rewards/pay'), {
        method: 'POST',
        headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify(payload),
      });
      const body = await response.json();
      if (!response.ok || body.ok === false) {
        setPayState(body.error || 'Write disabled');
        return;
      }
      setPayState(`Paid ${formatTokenE8(body.paid_now_e8)} / ${compactId(body.reward_receipt?.reward_entry_id)}`);
    } catch {
      setPayState('Start local API with --allow-writes');
    }
  }

  return (
    <section className="panel zor-panel">
      <div className="zor-section-header">
        <div>
          <h2>Rewards Ledger</h2>
          <p>Reporter payouts, pending work rewards, and slashed balances.</p>
        </div>
        <span className="zor-subtle-chip">{rewards.length} reporters</span>
      </div>
      <div className="zor-rewards-table">
        <div className="zor-rewards-head">
          <span>Reporter</span>
          <span>Pending</span>
          <span>Paid</span>
          <span>Slashed</span>
          <span>Status</span>
        </div>
        {rewards.length ? (
          rewards.map((reward) => (
            <div key={reward.id} className="zor-rewards-row">
              <span>
                <strong>{reward.reporter}</strong>
                <small>{reward.accepted} accepted reports</small>
              </span>
              <span>{reward.pending}</span>
              <span>{reward.paid}</span>
              <span>{reward.slashed}</span>
              <span className={`zor-status zor-reward-${reward.status}`}>{reward.status}</span>
            </div>
          ))
        ) : (
          <div className="zor-empty-state">No reward ledger entries yet</div>
        )}
      </div>
      <div className="zor-inline-form">
        <input
          className="input"
          inputMode="numeric"
          value={payAmount}
          onChange={(event) => setPayAmount(event.target.value)}
          placeholder="Amount e8, blank pays all"
          aria-label="Reward payout amount e8"
        />
        <button className="btn btn-secondary" type="button" onClick={payLocalRewards}>
          Pay Pending
        </button>
      </div>
      <span className="zor-action-state">{payState}</span>
    </section>
  );
}

function SourceDiversityPanel({ sources }) {
  return (
    <section className="panel zor-panel">
      <div className="zor-section-header">
        <div>
          <h2>Source Diversity</h2>
          <p>Registered source dimensions used by O3 aggregate policies.</p>
        </div>
        <span className="zor-subtle-chip">{sources.length} sources</span>
      </div>
      <div className="zor-source-list">
        {sources.length ? (
          sources.map((source) => (
            <article key={source.sourceId || source.id} className="zor-source-row">
              <div>
                <strong>{source.id}</strong>
                <small>{source.kind} / {source.jurisdiction}</small>
              </div>
              <div>
                <span>{source.controlGroup}</span>
                <small>{source.venue}</small>
              </div>
              <div>
                <span>{source.dataFamily}</span>
                <small>{source.transport}</small>
              </div>
              <div className="zor-source-badges">
                <span className="zor-source-assurance">{source.assurance}</span>
                <StatusPill status={source.status} />
              </div>
            </article>
          ))
        ) : (
          <div className="zor-empty-state">No registered sources yet</div>
        )}
      </div>
    </section>
  );
}

function AuthorizationTrailPanel({ items }) {
  return (
    <section className="panel zor-panel">
      <div className="zor-section-header">
        <div>
          <h2>Receipt Trail</h2>
          <p>Recent reads, authorizations, reward receipts, and slash receipts.</p>
        </div>
        <span className="zor-subtle-chip">{items.length} entries</span>
      </div>
      <div className="zor-trail-list">
        {items.length ? (
          items.map((item) => (
            <article key={`${item.kind}-${item.id}`} className="zor-trail-row">
              <div>
                <strong>{item.kind}</strong>
                <small>{item.consumer}</small>
              </div>
              <div>
                <span>{item.value}</span>
                <small>{item.queryId}</small>
              </div>
              {item.evidenceClass ? (
                <EvidenceBadge value={item.evidenceClass} />
              ) : (
                <span className="zor-receipt-kind">receipt</span>
              )}
              <div>
                <span>epoch {item.epoch}</span>
                <small>{item.root}</small>
              </div>
            </article>
          ))
        ) : (
          <div className="zor-empty-state">No accepted reads or authorizations yet</div>
        )}
      </div>
    </section>
  );
}

function ConsumerProfilePanel() {
  return (
    <section className="panel zor-panel">
      <div className="zor-section-header">
        <div>
          <h2>Consumer Profiles</h2>
          <p>Critical actions must bind to profile, value, state, and receipt root.</p>
        </div>
        <span className="zor-subtle-chip">binding map</span>
      </div>
      <div className="zor-profile-list">
        {ORACLE_CONSUMER_PROFILES.map((profile) => (
          <article key={profile.id} className="zor-profile-row">
            <div>
              <strong>{profile.label}</strong>
              <small>{profile.valueBinding}</small>
            </div>
            <EvidenceBadge value={profile.evidenceFloor} />
            <span>{profile.maxFreshness}</span>
            <span className={`zor-status zor-profile-${profile.status}`}>{profile.status}</span>
          </article>
        ))}
      </div>
    </section>
  );
}

function EvidencePanel() {
  return (
    <section className="panel zor-panel">
      <div className="zor-section-header">
        <div>
          <h2>Evidence Distribution</h2>
          <p>Critical-use floor is O3 until proof-backed lanes are live.</p>
        </div>
        <span className="zor-subtle-chip">1,248 total</span>
      </div>
      <div className="zor-evidence-layout">
        <div className="zor-evidence-donut" aria-label="Evidence distribution">
          <span>O3+</span>
          <small>accepted</small>
        </div>
        <div className="zor-evidence-bars">
          {ORACLE_EVIDENCE_DISTRIBUTION.map((item) => (
            <div key={item.id} className="zor-evidence-bar-row">
              <span>{item.label}</span>
              <div className="zor-evidence-bar">
                <div style={{ width: `${item.percent}%` }} />
              </div>
              <strong>{item.percent}%</strong>
            </div>
          ))}
        </div>
      </div>
    </section>
  );
}

function EventsPanel() {
  return (
    <section className="panel zor-panel zor-events-panel">
      <div className="zor-section-header">
        <div>
          <h2>Recent Oracle Events</h2>
          <p>Ledger events should remain replayable after restart.</p>
        </div>
        <span className="zor-subtle-chip">live tail</span>
      </div>
      <div className="zor-event-strip">
        {ORACLE_EVENTS.map((event) => (
          <article key={event.id} className={`zor-event-card zor-event-${event.tone}`}>
            <span className="zor-event-dot" />
            <strong>{event.kind}</strong>
            <small>{event.feed}</small>
            <span>{event.detail}</span>
            <em>{event.age}</em>
          </article>
        ))}
      </div>
    </section>
  );
}

function ServicesPanel() {
  return (
    <section className="panel zor-panel">
      <div className="zor-section-header">
        <div>
          <h2>System Status</h2>
          <p>Service posture for the pre-MVP oracle console.</p>
        </div>
        <span className="zor-system-ok">All systems operational</span>
      </div>
      <div className="zor-service-list">
        {ORACLE_SYSTEM_SERVICES.map((service) => (
          <div key={service.id} className="zor-service-row">
            <span>{service.label}</span>
            <strong className={service.status === 'Roadmap' ? 'zor-muted' : 'zor-green'}>
              {service.status}
            </strong>
          </div>
        ))}
      </div>
    </section>
  );
}

function AuthorityProfilePanel({ authorityStatus }) {
  const status = authorityStatus || {};
  const keyRefs = Array.isArray(status.key_refs) ? status.key_refs : [];
  const activeSigners = Array.isArray(status.active_signers) ? status.active_signers : [];
  const signerByKey = new Map(activeSigners.map((signer) => [signer.key_id, signer]));
  const gaps = Array.isArray(status.readiness_gaps) ? status.readiness_gaps : [];
  const walletUx = status.wallet_ux || {};
  const proofProfile = status.proof_profile || {};
  const controls = [
    ['External signer', walletUx.external_signer_required],
    ['Key manager', walletUx.key_manager_required],
    ['Device approval', walletUx.device_approval_required],
    ['Proof required', proofProfile.zk_or_proof_required],
    ['Receipt replay', proofProfile.oracle_receipt_replay_required],
  ];
  const ready = status.production_authority === true;

  return (
    <section className="panel zor-panel zor-authority-panel">
      <div className="zor-section-header">
        <div>
          <h2>Authority Profile</h2>
          <p>Public key-manager, signer quorum, wallet approval, and proof posture.</p>
        </div>
        <span className={`zor-authority-chip ${ready ? 'zor-authority-ready' : 'zor-authority-blocked'}`}>
          {ready ? 'Production authority ready' : 'Authority blocked'}
        </span>
      </div>
      <div className="zor-authority-summary">
        <div>
          <small>Authority</small>
          <strong>{status.authority_id || 'missing profile'}</strong>
        </div>
        <div>
          <small>Chain</small>
          <strong>{status.chain_id || 'unbound'}</strong>
        </div>
        <div>
          <small>Signer quorum</small>
          <strong>{status.active_signer_count || 0}/{status.threshold || 0}</strong>
        </div>
        <div>
          <small>Key refs</small>
          <strong>{status.key_ref_count || keyRefs.length}</strong>
        </div>
        <div>
          <small>Runtime proof</small>
          <strong>{proofProfile.runtime_proof_profile || 'missing'}</strong>
        </div>
        <div>
          <small>Authority hash</small>
          <strong>{compactId(status.authority_hash)}</strong>
        </div>
      </div>
      <div className="zor-authority-controls">
        {controls.map(([label, ok]) => (
          <span key={label} className={ok ? 'zor-control-ok' : 'zor-control-missing'}>
            {label}
          </span>
        ))}
      </div>
      <div className="zor-key-manager-table">
        <div className="zor-key-manager-head">
          <span>Key Manager</span>
          <span>Status</span>
          <span>Signer</span>
          <span>Public key</span>
        </div>
        {keyRefs.length ? (
          keyRefs.map((keyRef) => {
            const signer = signerByKey.get(keyRef.key_id);
            return (
              <div key={keyRef.key_id} className="zor-key-manager-row">
                <span>
                  <strong>{keyRef.key_id}</strong>
                  <small>{keyRef.origin || 'unknown origin'}</small>
                </span>
                <span className={keyRef.status === 'active' ? 'zor-status zor-reporter-active' : 'zor-status zor-stale'}>
                  {keyRef.status || 'unknown'}
                </span>
                <span>{signer ? `${signer.signer_id} / weight ${signer.weight}` : 'unmapped'}</span>
                <span>{compactId(keyRef.public_key)}</span>
              </div>
            );
          })
        ) : (
          <div className="zor-empty-state">No key-manager refs loaded</div>
        )}
      </div>
      {gaps.length ? (
        <div className="zor-authority-gaps">
          {gaps.slice(0, 5).map((gap) => (
            <span key={gap}>{gap}</span>
          ))}
        </div>
      ) : null}
    </section>
  );
}

function FeatureStrip() {
  return (
    <div className="zor-feature-strip" aria-label="ZenoOracle properties">
      {ORACLE_FEATURES.map((feature, index) => (
        <article key={feature.id} className="zor-feature-item">
          <span>{index + 1}</span>
          <div>
            <strong>{feature.title}</strong>
            <small>{feature.detail}</small>
          </div>
        </article>
      ))}
    </div>
  );
}

function DesignSystemRail() {
  return (
    <aside className="zor-design-rail" aria-label="ZenoOracle design system">
      <div className="zor-design-brand">
        <img src={ZENO_ORACLE_ICON} alt="" aria-hidden="true" />
        <div>
          <h2>ZenoOracle</h2>
          <p>Proof-Bound Oracle Network</p>
        </div>
      </div>

      <section className="zor-design-section">
        <h3>Design System</h3>
        <p>Visual language for transparent, verifiable, action-specific oracle infrastructure.</p>
      </section>

      <section className="zor-design-section">
        <h4>Color Palette</h4>
        <div className="zor-swatch-grid">
          {ORACLE_PALETTE.map((color) => (
            <div key={color.name} className="zor-swatch">
              <span style={{ background: color.value }} />
              <strong>{color.name}</strong>
              <small>{color.value}</small>
            </div>
          ))}
        </div>
      </section>

      <section className="zor-design-section">
        <h4>Typography</h4>
        <div className="zor-type-sample">
          <strong>Aa</strong>
          <span>Inter</span>
        </div>
        <div className="zor-type-scale">
          <span>H1</span><strong>32/40</strong>
          <span>H2</span><strong>24/32</strong>
          <span>H3</span><strong>18/28</strong>
          <span>Body</span><strong>14/22</strong>
          <span>Mono</span><strong>12/16</strong>
        </div>
      </section>

      <section className="zor-design-section">
        <h4>Spacing</h4>
        <div className="zor-token-row">
          {ORACLE_SPACING.map((size) => <span key={size}>{size}</span>)}
        </div>
      </section>

      <section className="zor-design-section">
        <h4>Border Radius</h4>
        <div className="zor-radius-row">
          {ORACLE_RADII.map((size) => <span key={size}>{size}</span>)}
        </div>
      </section>

      <section className="zor-design-section">
        <h4>Components</h4>
        <div className="zor-demo-buttons">
          <button className="btn btn-primary" type="button">Primary</button>
          <button className="btn btn-secondary" type="button">Secondary</button>
        </div>
        <div className="zor-demo-badges">
          <EvidenceBadge value="O3" />
          <EvidenceBadge value="O4" />
          <EvidenceBadge value="O5" />
          <StatusPill status="disputed" />
          <StatusPill status="stale" />
        </div>
        <div className="zor-demo-card-grid">
          <span>Normal content</span>
          <span>All checks passed</span>
          <span>Attention needed</span>
          <span>Action required</span>
        </div>
      </section>

      <section className="zor-design-section">
        <h4>Inputs</h4>
        <div className="zor-design-inputs">
          <input className="input" placeholder="Input text" aria-label="Design sample input" />
          <select className="input" aria-label="Design sample select" defaultValue="">
            <option value="" disabled>Select option</option>
            <option>O3 policy</option>
          </select>
        </div>
      </section>

      <section className="zor-design-section">
        <h4>Icons</h4>
        <div className="zor-icon-grid" aria-hidden="true">
          {ORACLE_ICON_GLYPHS.map((glyph) => <span key={glyph}>{glyph}</span>)}
        </div>
      </section>
    </aside>
  );
}

function ZenoOracleDashboard() {
  const [selectedFeedId, setSelectedFeedId] = useState(ORACLE_FEEDS[0].id);
  const [feedFilter, setFeedFilter] = useState('all');
  const [timeRange, setTimeRange] = useState('24h');
  const [activeSection, setActiveSection] = useState(getInitialOracleSection);
  const [verifyReceiptId, setVerifyReceiptId] = useState('');
  const [remoteData, setRemoteData] = useState(null);
  const [apiState, setApiState] = useState('Static preview');
  const [oracleSmokeStatus, setOracleSmokeStatus] = useState('');
  const oracleSmokeRan = useRef(false);

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
          setApiState('Static preview');
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

    async function post(path, payload) {
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

    async function runSmoke() {
      setOracleSmokeStatus('oracle write smoke running');
      const queryId = 'sha256:' + '1'.repeat(64);
      const actionId = 'sha256:' + '2'.repeat(64);
      const actionFactsHash = 'sha256:' + '3'.repeat(64);
      const preStateHash = 'sha256:' + '4'.repeat(64);
      const identity = await post('/api/oracle/identity/create', { force: true });
      await post('/api/oracle/query/register', {
        base_asset: 'AGRS',
        quote_asset: 'ZDEX',
        query_id: queryId,
        source_policy_id: 'source-policy:registered-diverse-v1',
        min_reporters: 1,
        report_reward_e8: 17,
        force: true,
      });
      await post('/api/oracle/query/fund', { query_id: queryId, amount_e8: 20 });
      await post('/api/oracle/reporter/register', { query_id: queryId, required_bond_e8: 1, force: true });
      await post('/api/oracle/reporter/bond', { amount_e8: 1 });
      await post('/api/oracle/source/register', {
        source_id: 'source:ui-smoke',
        source_kind: 'cex',
        control_group_id: 'control:ui-smoke',
        venue_id: 'venue:ui-smoke',
        data_family_id: 'price:cex-last-trade',
        transport_id: 'api:https:ui-smoke',
        asset_class: 'crypto',
        query_id: queryId,
        assurance_class: 'S3',
        force: true,
      });
      const submitted = await post('/api/oracle/report/submit', {
        query_id: queryId,
        price_e8: 123456789,
        source_observed_epoch: 12,
        source_id: 'source:ui-smoke',
      });
      const aggregate = await post('/api/oracle/aggregate/build', { query_id: queryId, epoch: 12 });
      const read = await post('/api/oracle/read/accept', {
        aggregate_id: aggregate.aggregate_id,
        consumer_module: 'zenodex.zusd',
        profile_id: 'critical-zusd-v1',
      });
      const authorization = await post('/api/oracle/authorization/build', {
        read_id: read.read_id,
        action_kind: 'mint',
        action_id: actionId,
        action_facts_hash: actionFactsHash,
        pre_state_hash: preStateHash,
        now_epoch: 12,
      });
      await post('/api/oracle/rewards/pay', { amount_e8: 5 });
      setOracleSmokeStatus(
        `oracle write smoke accepted ${identity.reporter_id} ${submitted.report_id} ${authorization.authorization_id}`,
      );
    }

    void runSmoke().catch((error) => {
      setOracleSmokeStatus(`oracle write smoke failed ${error?.message || 'unknown'}`);
    });
  }, []);

  const feeds = remoteData?.feeds?.length ? remoteData.feeds : ORACLE_FEEDS;
  const reporters = remoteData?.reporters || ORACLE_REPORTERS;
  const disputes = remoteData?.disputes || ORACLE_DISPUTES;
  const metrics = remoteData?.metrics || ORACLE_NETWORK_SUMMARY;
  const sources = remoteData?.sources || [];
  const rewards = remoteData?.rewards || ORACLE_REWARDS;
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

  const selectedFeed = feeds.find((feed) => feed.id === selectedFeedId) || feeds[0] || ORACLE_FEEDS[0];
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
            />
          </section>
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
            <LatestRead feed={selectedFeed} onVerifyReceipt={handleVerifyReceipt} />
          </div>
          <AuthorizationTrailPanel items={authorizationTrail} />
          <SourceDiversityPanel sources={sources} />
          <EventsPanel />
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
          <EventsPanel />
        </>
      );
    }
    if (activeSection === 'Receipts') {
      return (
        <>
          <div className="zor-two-up">
            <ReceiptBuilderPanel feed={selectedFeed} />
            <LatestRead feed={selectedFeed} onVerifyReceipt={handleVerifyReceipt} />
          </div>
          <AuthorizationTrailPanel items={authorizationTrail} />
          <EvidencePanel />
        </>
      );
    }
    if (activeSection === 'Verify') {
      return (
        <>
          <div className="zor-two-up">
            <VerifyPanel initialReceiptId={verifyReceiptId} />
            <ServicesPanel />
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
          <ConsumerProfilePanel />
          <div className="zor-two-up">
            <FeedCreationPanel />
            <ServicesPanel />
          </div>
          <RewardsPanel rewards={rewards} />
        </>
      );
    }
    return (
      <>
        <div className="zor-metrics">
          {metrics.map((metric) => (
            <MetricCard key={metric.id} metric={metric} />
          ))}
        </div>

        <section className="panel zor-panel zor-feeds-panel">
          <div className="zor-section-header">
            <div>
              <h2>Top Feeds</h2>
              <p>{timeRange} operational view with evidence and freshness state.</p>
            </div>
            <span className="zor-subtle-chip">{visibleFeeds.length} feeds</span>
          </div>
          <FeedTable
            feeds={visibleFeeds}
            selectedFeedId={selectedFeed.id}
            onSelectFeed={setSelectedFeedId}
          />
        </section>

        <div className="zor-two-up">
          <HealthPanel />
          <EvidencePanel />
        </div>
        <AuthorizationTrailPanel items={authorizationTrail} />
        <SourceDiversityPanel sources={sources} />
        <div className="zor-two-up">
          <FeedCreationPanel />
          <ReporterOnboardingPanel selectedFeed={selectedFeed} />
        </div>
        <ReporterPanel reporters={reporters} />
        <RewardsPanel rewards={rewards} />
        <ConsumerProfilePanel />
        <EventsPanel />
      </>
    );
  })();

  return (
    <div className="zor-shell">
      <DesignSystemRail />
      <section className="zor-dashboard">
        <div className="zor-topbar panel">
          <div className="zor-brand-lockup">
            <img src={ZENO_ORACLE_ICON} alt="ZenoOracle" />
            <div>
              <h1>ZenoOracle</h1>
              <p>Proof-bound oracle network</p>
            </div>
          </div>
          <div className="zor-toolbar">
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
          </div>
          <div className="zor-top-actions">
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
            <button className="zor-icon-button" type="button" aria-label="Toggle dark mode">
              D
            </button>
            <button className="btn btn-primary zor-connect-button" type="button">
              Connect Wallet
            </button>
          </div>
        </div>

        <div className="zor-workspace">
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
          </div>

          <aside className="zor-side-rail" aria-label="Oracle action rail">
            <LatestRead feed={selectedFeed} onVerifyReceipt={handleVerifyReceipt} />
            <FeedStatusPanel feed={selectedFeed} />
            <ReceiptBuilderPanel feed={selectedFeed} />
            <DisputesPanel disputes={disputes} />
            <VerifyPanel initialReceiptId={verifyReceiptId} />
            <ServicesPanel />
          </aside>
        </div>
        <FeatureStrip />
      </section>
    </div>
  );
}

export default ZenoOracleDashboard;
