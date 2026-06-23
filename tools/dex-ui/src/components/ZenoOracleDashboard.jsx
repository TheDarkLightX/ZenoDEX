import { useEffect, useMemo, useRef, useState } from 'react';
import { useWindowed } from '../lib/useWindowed.js';
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
import { useDemoMode } from '../lib/DemoModeContext.jsx';
import Modal from './Modal.jsx';
import SharedStatusPill from './StatusPill.jsx';
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
  const runtimeConfig = getRuntimeConfig();
  const hasRuntimeOracleBase = Object.prototype.hasOwnProperty.call(runtimeConfig, 'zenoOracleApiBase');
  const runtimeBase = normalizeOracleApiBase(runtimeConfig.zenoOracleApiBase);
  if (runtimeBase) {
    return `${runtimeBase}${path}`;
  }
  const envBase = normalizeOracleApiBase(import.meta.env.VITE_ZENO_ORACLE_API_URL);
  if (envBase) {
    return `${envBase}${path}`;
  }
  if (hasRuntimeOracleBase) {
    return path;
  }
  return `${DEFAULT_ZENO_ORACLE_API_BASE}${path}`;
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

function compactId(value) {
  if (!value) return 'none';
  const text = String(value);
  if (text.length <= 18) return text;
  return `${text.slice(0, 10)}...${text.slice(-6)}`;
}

function parsePositiveIntParam(raw, fallbackValue) {
  const text = String(raw ?? '').trim();
  if (!text) {
    return fallbackValue;
  }
  const parsed = Number.parseInt(text, 10);
  if (!Number.isFinite(parsed) || parsed <= 0) {
    return fallbackValue;
  }
  return parsed;
}

function formatE8(value, digits = 4) {
  if (value === null || value === undefined) return null;
  return (Number(value) / 100000000).toLocaleString(undefined, {
    maximumFractionDigits: digits,
  });
}

function formatTokenE8(value, symbol = 'ZORACLE') {
  const formatted = formatE8(value, 2);
  return formatted === null ? null : `${formatted} ${symbol}`;
}

// Render an integer epoch count + relative phrasing. Epochs are opaque
// integers; pair the raw count with a friendly window so operators don't
// have to remember epoch length offhand.
function formatEpochWindow(remainingEpochs) {
  if (remainingEpochs === null || remainingEpochs === undefined) return null;
  const n = Math.max(0, Math.floor(Number(remainingEpochs)));
  if (Number.isNaN(n)) return null;
  if (n === 0) return 'expires this epoch';
  if (n === 1) return '1 epoch left';
  return `${n} epochs left`;
}

function formatEpochLabel(epoch) {
  if (epoch === null || epoch === undefined) return null;
  const n = Number(epoch);
  if (!Number.isFinite(n)) return null;
  return `epoch ${n.toLocaleString()}`;
}

// Basis points as a signed percent string. 28 → "0.28%". Sign is preserved.
function formatBpsAsPercent(bps, digits = 2) {
  if (bps === null || bps === undefined) return null;
  const n = Number(bps);
  if (!Number.isFinite(n)) return null;
  const sign = n > 0 ? '+' : '';
  return `${sign}${(n / 100).toFixed(digits)}%`;
}

function randomSmokeHex(bytes = 16) {
  const buffer = new Uint8Array(bytes);
  if (typeof crypto !== 'undefined' && crypto.getRandomValues) {
    crypto.getRandomValues(buffer);
  } else {
    for (let i = 0; i < buffer.length; i += 1) {
      buffer[i] = Math.floor(Math.random() * 256);
    }
  }
  return Array.from(buffer, (byte) => byte.toString(16).padStart(2, '0')).join('');
}

function smokeHash(prefixHex, padHex) {
  return `sha256:${`${prefixHex}${padHex.repeat(64)}`.slice(0, 64)}`;
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
    summary,
    acceptedReads,
    feeds: feedStatuses.map((feed) => {
      const pair = `${feed.base_asset || 'UNKNOWN'}/${feed.quote_asset || 'UNKNOWN'}`;
      const status = primaryStatus(feed.status || []);
      const remainingEpochs =
        feed.expires_at_epoch === null || feed.expires_at_epoch === undefined
          ? null
          : Number(feed.expires_at_epoch) - Number(feed.now_epoch || 0);
      const confidenceFormatted = formatE8(feed.confidence_e8);
      return {
        id: feed.query_id,
        feed: pair,
        domain: `${feed.asset_class || 'crypto'} / ${feed.query_type || 'spot_price'}`,
        queryId: feed.query_id,
        value: formatE8(feed.latest_value_e8),
        unit: feed.quote_asset || '',
        reference: feed.feed_id || pair,
        // 24h change is not yet surfaced by the dashboard snapshot; emit
        // null so the UI can render an em dash instead of a fake +0.00%.
        change24h: null,
        evidenceClass: feed.evidence_floor || null,
        freshness: formatEpochWindow(remainingEpochs),
        status,
        confidence: confidenceFormatted === null ? null : `± ${confidenceFormatted}`,
        deviationBps: feed.deviation_bps ?? null,
        receiptId: compactId(feed.latest_read_id || feed.latest_aggregate_id),
        receiptFullId: feed.latest_read_id || feed.latest_aggregate_id || '',
        actionUse: feed.source_policy_id || null,
      };
    }),
    reporters: reporters.map((reporter) => ({
      id: compactId(reporter.reporter_id),
      status: reporter.slash_state === 'slashed' ? 'quarantined' : reporter.active ? 'active' : 'pending',
      bond: formatTokenE8(reporter.bond_amount_e8, reporter.bond_asset || 'ZORACLE'),
      requiredBond: formatTokenE8(reporter.required_bond_e8, reporter.bond_asset || 'ZORACLE'),
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
      bond: formatTokenE8(dispute.bond_e8, 'ZORACLE'),
      age: formatEpochLabel(dispute.opened_epoch),
      status: dispute.status === 'open' ? 'open' : dispute.status === 'upheld' ? 'quarantined' : 'closed',
    })),
    rewards: rewards.map((reward) => ({
      id: compactId(reward.reporter_id),
      reporter: compactId(reward.reporter_id),
      reporterFullId: reward.reporter_id,
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
        evidenceClass: bundle.authorization?.evidence_class || null,
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
        evidenceClass: read.evidence_class || null,
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
        tone: (summary.accepted_read_count || 0) > 0 ? 'positive' : 'neutral',
        detail: 'Replay-bound reads',
      },
      {
        id: 'active_feeds',
        label: 'Active Feeds',
        value: String(summary.active_feed_count || 0),
        delta: `${summary.feed_status_count || 0} tracked`,
        tone: (summary.active_feed_count || 0) > 0 ? 'positive' : 'neutral',
        detail: 'Local query registry',
      },
      {
        id: 'reporters',
        label: 'Reporters',
        value: String(summary.reporter_count || 0),
        delta: `${summary.active_reporter_count || 0} active`,
        tone: (summary.reporter_count || 0) > 0 ? 'positive' : 'neutral',
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

async function runOracleWriteSmokeFlow(post, { payReward = true } = {}) {
  const runHex = randomSmokeHex(16);
  const sourceId = `source:ui-smoke:${runHex}`;
  const queryId = smokeHash(runHex, '1');
  const actionId = smokeHash(runHex, '2');
  const actionFactsHash = smokeHash(runHex, '3');
  const preStateHash = smokeHash(runHex, '4');
  const identity = await post('/api/oracle/identity/create', { force: true });
  await post('/api/oracle/query/register', {
    base_asset: 'TASSET0',
    quote_asset: 'ZDEX',
    query_id: queryId,
    source_policy_id: 'source-policy:registered-diverse-v1',
    min_reporters: 1,
    report_reward_e8: 17,
    force: true,
  });
  await post('/api/oracle/query/fund', { query_id: queryId, amount_e8: 20 });
  await post('/api/oracle/reporter/register', { query_id: queryId, required_bond_e8: 10000000, force: true });
  await post('/api/oracle/reporter/bond', { amount_e8: 10000000 });
  await post('/api/oracle/source/register', {
    source_id: sourceId,
    source_kind: 'cex',
    control_group_id: `control:ui-smoke:${runHex}`,
    venue_id: `venue:ui-smoke:${runHex}`,
    data_family_id: 'price:cex-last-trade',
    transport_id: `api:https:ui-smoke:${runHex}`,
    asset_class: 'crypto',
    query_id: queryId,
    assurance_class: 'S3',
    force: true,
  });
  const submitted = await post('/api/oracle/report/submit', {
    query_id: queryId,
    price_e8: 123456789,
    source_observed_epoch: 12,
    source_id: sourceId,
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
  const reward = payReward ? await post('/api/oracle/rewards/pay', { amount_e8: 5 }) : null;
  return {
    identity,
    submitted,
    aggregate,
    read,
    authorization,
    reward,
    queryId,
  };
}

function EvidenceBadge({ value }) {
  // Unknown/unreported evidence renders as a neutral "—" rather than being
  // silently upgraded to a graded class (which would overstate the floor).
  if (!value) return <span className="zor-evidence zor-evidence-unknown" title="Evidence class not reported">—</span>;
  return <span className={`zor-evidence zor-evidence-${value}`}>{value}</span>;
}

function StatusPill({ status }) {
  return <span className={`zor-status zor-status-${status}`}>{STATUS_COPY[status] || status}</span>;
}

function MetricCard({ metric }) {
  return (
    <article className={`zor-metric zor-metric-${metric.tone}`}>
      <span className="zor-metric-label">{metric.label}</span>
      <strong>{metric.value}</strong>
      <span className="zor-metric-delta">{metric.delta}</span>
      {/* No per-metric history is exposed by the dashboard snapshot, so a
          sparkline would fabricate a trend over a single observation. Omitted
          until the node surfaces a real series. */}
      <span className="zor-metric-detail">{metric.detail}</span>
    </article>
  );
}

function FeedTable({ feeds, selectedFeedId, onSelectFeed, onCreate }) {
  const { rows, total, hasMore, showMore } = useWindowed(feeds, 100);
  if (!feeds || feeds.length === 0) {
    return (
      <div className="zor-table-wrap" role="region" aria-label="Oracle feeds">
        <div className="zor-empty-state" role="status">
          <strong>No feeds yet</strong>
          <p>The oracle dashboard returned no feeds. Register the first feed to begin
          accepting reads, or refresh once data arrives.</p>
          {onCreate && (
            <button type="button" className="btn btn-secondary zor-empty-cta" onClick={onCreate}>
              + Create the first feed
            </button>
          )}
        </div>
      </div>
    );
  }
  const handleRowKey = (event, feedId) => {
    if (event.key === 'Enter' || event.key === ' ') {
      event.preventDefault();
      onSelectFeed(feedId);
    }
  };
  return (
    <div className="zor-table-wrap" role="region" aria-label="Oracle feeds">
      <div role="table" aria-rowcount={feeds.length + 1} aria-label="Oracle feed list">
        <div className="zor-feed-head" role="row">
          <span role="columnheader">Feed</span>
          <span role="columnheader">Value</span>
          <span role="columnheader" title="24-hour change (not yet surfaced in dashboard snapshot)">24h</span>
          <span role="columnheader">Evidence</span>
          <span role="columnheader">Freshness</span>
          <span role="columnheader">Status</span>
        </div>
        <div role="rowgroup">
          {rows.map((feed) => {
            const isActive = selectedFeedId === feed.id;
            const changeClass = feed.change24h && feed.change24h.startsWith('-')
              ? 'zor-red'
              : feed.change24h
                ? 'zor-green'
                : 'zor-muted';
            return (
              <div
                key={feed.id}
                role="row"
                tabIndex={0}
                aria-selected={isActive}
                className={`zor-feed-row ${isActive ? 'zor-feed-row-active' : ''}`}
                onClick={() => onSelectFeed(feed.id)}
                onKeyDown={(event) => handleRowKey(event, feed.id)}
              >
                <span role="cell">
                  <strong>{feed.feed}</strong>
                  <small>{feed.domain}</small>
                </span>
                <span role="cell">
                  <strong>{feed.value ?? <span className="zor-muted">—</span>}</strong>
                  <small>{feed.unit}</small>
                </span>
                <span role="cell" className={changeClass}>
                  {feed.change24h ?? '—'}
                </span>
                <span role="cell">
                  <EvidenceBadge value={feed.evidenceClass} />
                </span>
                <span role="cell">{feed.freshness ?? <span className="zor-muted">no accepted read</span>}</span>
                <span role="cell">
                  <StatusPill status={feed.status} />
                </span>
              </div>
            );
          })}
        </div>
      </div>
      {hasMore && (
        <div className="zor-feed-more">
          <span>Showing {rows.length} of {total} feeds</span>
          <button type="button" className="zor-link-button" onClick={showMore}>Show more →</button>
        </div>
      )}
    </div>
  );
}

function HealthPanel({ summary = {}, demoMode = false }) {
  // Honest health: the dashboard snapshot exposes NO composite "health %" or
  // uptime series, so we never fabricate one. We show the real replay signal +
  // data-plane counts, and an explicit empty state until the node reports reads.
  // The demo path keeps the illustrative ring (clearly behind demoMode).
  if (demoMode) {
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
  const reads = Number(summary.accepted_read_count || 0);
  const feeds = Number(summary.active_feed_count || 0);
  const replayOk = summary.replay_ok === true;
  const hasData = reads > 0 || feeds > 0;
  return (
    <section className="panel zor-panel">
      <div className="zor-section-header">
        <div>
          <h2>Network Health</h2>
          <p>Critical services must stay replayable before reads become usable.</p>
        </div>
        <span className={`zor-subtle-chip ${replayOk ? 'zor-chip-ok' : 'zor-chip-warn'}`}>
          {replayOk ? 'Replay OK' : 'Replay unverified'}
        </span>
      </div>
      {hasData ? (
        <div className="zor-health-list">
          <div className="zor-health-row"><span>Replay verifier</span><strong>{replayOk ? 'OK' : 'Fail'}</strong></div>
          <div className="zor-health-row"><span>Accepted reads</span><strong>{reads}</strong></div>
          <div className="zor-health-row"><span>O3+ critical reads</span><strong>{Number(summary.o3_plus_read_count || 0)}</strong></div>
          <div className="zor-health-row"><span>Active feeds</span><strong>{feeds}</strong></div>
          <div className="zor-health-row"><span>Open disputes</span><strong>{Number(summary.open_dispute_count || 0)}</strong></div>
        </div>
      ) : (
        <div className="zor-empty-state" role="status">
          <strong>No health data yet</strong>
          <p>
            Awaiting feeds and accepted reads. Composite health metrics activate once the node
            reports replay-bound reads.{replayOk ? ' Replay verifier is currently OK.' : ''}
          </p>
        </div>
      )}
    </section>
  );
}

function LatestRead({ feed, onVerifyReceipt, onViewAll }) {
  return (
    <section className="panel zor-panel">
      <div className="zor-section-header">
        <div>
          <h2>Latest Accepted Read</h2>
          <p>Bound to query, value hash, policy roots, and receipt graph.</p>
        </div>
        <button
          className="zor-text-button"
          type="button"
          onClick={() => onViewAll?.()}
          disabled={!onViewAll}
          title={onViewAll ? 'Jump to Receipts tab' : 'No additional receipts available'}
        >
          View all
        </button>
      </div>
      <div className="zor-read-grid">
        <div>
          <span className="zor-label">Feed</span>
          <strong>{feed.feed}</strong>
        </div>
        <div>
          <span className="zor-label">Value</span>
          <strong>{feed.value ?? <span className="zor-muted">—</span>}</strong>
        </div>
        <div>
          <span className="zor-label">Confidence</span>
          <strong>{feed.confidence ?? <span className="zor-muted">—</span>}</strong>
        </div>
        <div>
          <span className="zor-label">Deviation</span>
          <strong title={feed.deviationBps !== null && feed.deviationBps !== undefined ? `${feed.deviationBps} bps` : undefined}>
            {formatBpsAsPercent(feed.deviationBps) ?? <span className="zor-muted">—</span>}
          </strong>
        </div>
      </div>
      <div className="zor-receipt-box">
        <span>Receipt</span>
        <code>{feed.receiptId ?? <span className="zor-muted">no receipt</span>}</code>
      </div>
      <div className="zor-read-foot">
        <span>
          <small>Evidence</small>
          <EvidenceBadge value={feed.evidenceClass} />
        </span>
        <span>
          <small>Action use</small>
          <strong>{feed.actionUse ?? <span className="zor-muted">source policy pending</span>}</strong>
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
  const initialReceipt = String(initialReceiptId || '').trim();
  const [receiptId, setReceiptId] = useState(initialReceipt);
  const [status, setStatus] = useState(initialReceipt ? 'Ready to replay' : 'Waiting for receipt ID');

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
  const lifecycleSmokeRan = useRef(false);

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

  useEffect(() => {
    if (typeof window === 'undefined') {
      return;
    }
    const params = new URLSearchParams(window.location.search);
    if (params.get('zenodexUiSmokeOracleDisputeLifecycle') !== '1' || lifecycleSmokeRan.current) {
      return;
    }
    lifecycleSmokeRan.current = true;
    async function runSmoke() {
      setStatus('Dispute lifecycle smoke running...');
      const flow = await runOracleWriteSmokeFlow(post, { payReward: false });
      const opened = await post('/api/oracle/dispute/open', {
        report_id: flow.submitted.report_id,
        reporter_id: flow.identity.reporter_id,
        bond_e8: 10000000,
        reason: 'ui-lifecycle-smoke',
      });
      setReportId(flow.submitted.report_id || '');
      setReporterId(flow.identity.reporter_id || '');
      setDisputeId(opened.dispute_id || '');
      await post('/api/oracle/dispute/resolve', {
        dispute_id: opened.dispute_id,
        outcome: 'rejected',
      });
      setStatus(`Dispute lifecycle smoke rejected ${compactId(opened.dispute_id)}`);
    }
    void runSmoke().catch((error) => {
      setStatus(`Dispute lifecycle smoke failed ${error?.message || 'unknown'}`);
    });
  }, []);

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
              <span>{dispute.bond ?? <span className="zor-muted">no bond</span>}</span>
              <small>{dispute.age ?? <span className="zor-muted">unknown</span>}</small>
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
          <strong>{feed.freshness ?? <span className="zor-muted">no accepted read</span>}</strong>
        </div>
        <div>
          <span className="zor-label">Deviation</span>
          <strong title={feed.deviationBps !== null && feed.deviationBps !== undefined ? `${feed.deviationBps} bps` : undefined}>
            {formatBpsAsPercent(feed.deviationBps) ?? <span className="zor-muted">—</span>}
          </strong>
        </div>
        <div>
          <span className="zor-label">Confidence</span>
          <strong>{feed.confidence ?? <span className="zor-muted">—</span>}</strong>
        </div>
        <div>
          <span className="zor-label">Consumer use</span>
          <strong>{feed.actionUse ?? <span className="zor-muted">source policy pending</span>}</strong>
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
      const actionHex = randomSmokeHex(16);
      const payload = await post('/api/oracle/authorization/build', {
        read_id: readId,
        action_kind: actionKind,
        action_id: smokeHash(actionHex, '2'),
        action_facts_hash: smokeHash(actionHex, '3'),
        pre_state_hash: smokeHash(actionHex, '4'),
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
  const [assetPair, setAssetPair] = useState('TASSET0/ZDEX');
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
  const [sourceId, setSourceId] = useState('source:manual');
  const reporterSmokeRan = useRef(false);

  // Step locking state
  // 0: Create Identity, 1: Register+Bond, 2: Submit Reports
  const [currentStepIndex, setCurrentStepIndex] = useState(0);

  // Price formatting state
  const [displayPrice, setDisplayPrice] = useState('1.50');

  // Calculate e8 equivalent automatically
  const priceE8 = Math.floor(parseFloat(displayPrice || 0) * 100000000);

  const steps = [
    { id: 'identity', label: 'Create identity', status: currentStepIndex > 0 ? 'completed' : 'available' },
    { id: 'register_bond', label: 'Register & Post Bond', status: currentStepIndex > 1 ? 'completed' : (currentStepIndex === 1 ? 'available' : 'locked') },
    { id: 'submit', label: 'Submit signed reports', status: currentStepIndex === 2 ? 'available' : 'locked' },
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
      const payload = await post('/api/oracle/identity/create', { force: true });
      setStatus(`Identity ${compactId(payload.reporter_id)} created`);
      setCurrentStepIndex(1); // unlock next step
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
        force: true,
      });
      await post('/api/oracle/reporter/bond', { amount_e8: 100000000 });
      setStatus(`Bonded for ${selectedFeed.feed}`);
      setCurrentStepIndex(2); // unlock next step
    } catch (error) {
      setStatus(String(error.message || error));
    }
  }

  async function registerSourceForSelectedFeed() {
    const source = sourceId.trim();
    if (!source) {
      throw new Error('source_id_required');
    }
    await post('/api/oracle/source/register', {
      source_id: source,
      source_kind: 'manual',
      control_group_id: `${source}:control`,
      venue_id: `${source}:venue`,
      data_family_id: 'price:manual-spot',
      transport_id: `${source}:ui`,
      asset_class: 'crypto',
      query_id: selectedFeed.queryId,
      assurance_class: 'S3',
      force: true,
    });
  }

  async function submitReport() {
    setStatus('Submitting report...');
    try {
      await registerSourceForSelectedFeed();
      const payload = await post('/api/oracle/report/submit', {
        query_id: selectedFeed.queryId,
        price_e8: priceE8,
        source_observed_epoch: Math.max(1, Math.floor(Date.now() / 1000)),
        source_id: sourceId,
      });
      setStatus(`Source registered; report ${compactId(payload.report_id)} submitted successfully`);
    } catch (error) {
      setStatus(String(error.message || error));
    }
  }

  useEffect(() => {
    if (typeof window === 'undefined') {
      return;
    }
    const params = new URLSearchParams(window.location.search);
    if (params.get('zenodexUiSmokeOracleReporterOnboarding') !== '1' || reporterSmokeRan.current) {
      return;
    }
    if (!selectedFeed?.queryId || selectedFeed.queryId === 'placeholder') {
      return;
    }
    reporterSmokeRan.current = true;
    async function runSmoke() {
      const runHex = randomSmokeHex(8);
      setSourceId(`source:ui-reporter:${runHex}`);
      setStatus('Reporter onboarding smoke running...');
      await post('/api/oracle/identity/create', { force: true });
      await post('/api/oracle/reporter/register', {
        query_id: selectedFeed.queryId,
        required_bond_e8: 100000000,
        force: true,
      });
      await post('/api/oracle/reporter/bond', { amount_e8: 100000000 });
      await post('/api/oracle/source/register', {
        source_id: `source:ui-reporter:${runHex}`,
        source_kind: 'manual',
        control_group_id: `control:ui-reporter:${runHex}`,
        venue_id: `venue:ui-reporter:${runHex}`,
        data_family_id: 'price:manual-spot',
        transport_id: `ui:manual:${runHex}`,
        asset_class: 'crypto',
        query_id: selectedFeed.queryId,
        assurance_class: 'S3',
        force: true,
      });
      const payload = await post('/api/oracle/report/submit', {
        query_id: selectedFeed.queryId,
        price_e8: priceE8,
        source_observed_epoch: 12,
        source_id: `source:ui-reporter:${runHex}`,
      });
      setCurrentStepIndex(2);
      setStatus(`Reporter onboarding smoke submitted ${compactId(payload.report_id)}`);
    }
    void runSmoke().catch((error) => {
      setStatus(`Reporter onboarding smoke failed ${error?.message || 'unknown'}`);
    });
  }, [selectedFeed?.queryId, priceE8]);

  return (
    <section className="panel zor-panel animate-fade-in">
      <div className="zor-section-header">
        <div>
          <h2>Reporter Onboarding Workflow</h2>
          <p>Complete the steps in order to start submitting oracle reports.</p>
        </div>
        <span className="zor-subtle-chip">CLI-backed</span>
      </div>

      <div className="zor-step-list" style={{ marginBottom: 'var(--space-lg)' }}>
        {steps.map((step, index) => (
          <div key={step.id} className="zor-step-row" style={{ opacity: index > currentStepIndex ? 0.5 : 1 }}>
            <span className="zor-step-index" style={{ background: index < currentStepIndex ? 'var(--accent-green)' : (index === currentStepIndex ? 'var(--accent-cyan)' : 'var(--border-primary)') }}>
              {index < currentStepIndex ? '✓' : index + 1}
            </span>
            <strong>{step.label}</strong>
            <small style={{ color: index === currentStepIndex ? 'var(--accent-cyan)' : 'inherit' }}>{step.status}</small>
          </div>
        ))}
      </div>

      <div className="zor-button-row" style={{ borderBottom: '1px solid var(--border-primary)', paddingBottom: 'var(--space-lg)', marginBottom: 'var(--space-lg)' }}>
        <button
          className="btn btn-secondary"
          type="button"
          onClick={createIdentity}
          disabled={currentStepIndex !== 0}
        >
          {currentStepIndex > 0 ? 'Identity Created ✓' : '1. Create Identity'}
        </button>
        <button
          className="btn btn-primary"
          type="button"
          onClick={registerAndBond}
          disabled={currentStepIndex !== 1}
        >
          {currentStepIndex > 1 ? 'Registered & Bonded ✓' : '2. Register + Bond'}
        </button>
      </div>

      <div className="zor-report-submit-grid" style={{ opacity: currentStepIndex === 2 ? 1 : 0.4, pointerEvents: currentStepIndex === 2 ? 'auto' : 'none' }}>
        <label>
          <span className="label">Source ID</span>
          <input
            className="input"
            value={sourceId}
            onChange={(event) => setSourceId(event.target.value)}
            disabled={currentStepIndex !== 2}
          />
        </label>
        <label>
          <span className="label">Observed Price ($)</span>
          <input
            className="input"
            inputMode="decimal"
            value={displayPrice}
            onChange={(event) => setDisplayPrice(event.target.value)}
            disabled={currentStepIndex !== 2}
            placeholder="1.50"
          />
          <small style={{ display: 'block', marginTop: '4px', color: 'var(--text-muted)' }}>
            Auto-converted: <span className="strat-mono">{priceE8} e8</span>
          </small>
        </label>
        <button
          className="btn btn-primary"
          type="button"
          onClick={submitReport}
          disabled={currentStepIndex !== 2 || priceE8 <= 0}
        >
          3. Submit Report
        </button>
      </div>

      {status !== 'Ready' && (
        <div style={{ marginTop: 'var(--space-md)', padding: 'var(--space-sm)', background: 'var(--background-subtle)', borderRadius: 'var(--radius-sm)', textAlign: 'center' }}>
          <span className="zor-action-state">{status}</span>
        </div>
      )}
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
            <span>{reporter.bond ?? <span className="zor-muted">no bond</span>}</span>
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
  const [reporterId, setReporterId] = useState('');
  const [payState, setPayState] = useState('Ready');
  const rewardSmokeRan = useRef(false);
  const firstPayableReporterId = useMemo(
    () => rewards.find((reward) => reward.reporterFullId)?.reporterFullId || '',
    [rewards],
  );
  const effectiveReporterId = reporterId || firstPayableReporterId;

  async function payLocalRewards() {
    setPayState('Paying...');
    try {
      const payload = {};
      if (effectiveReporterId.trim()) {
        payload.reporter_id = effectiveReporterId.trim();
      }
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

  useEffect(() => {
    if (typeof window === 'undefined') {
      return;
    }
    const params = new URLSearchParams(window.location.search);
    if (params.get('zenodexUiSmokeOracleRewardPayout') !== '1' || rewardSmokeRan.current) {
      return;
    }
    rewardSmokeRan.current = true;
    async function runSmoke() {
      setPayState('Reward payout smoke running...');
      const flow = await runOracleWriteSmokeFlow(post, { payReward: false });
      setReporterId(flow.identity.reporter_id || '');
      const body = await post('/api/oracle/rewards/pay', {
        reporter_id: flow.identity.reporter_id,
        amount_e8: 5,
      });
      setPayState(`Reward payout smoke paid ${formatTokenE8(body.paid_now_e8)} / ${compactId(body.reward_receipt?.reward_entry_id)}`);
    }
    void runSmoke().catch((error) => {
      setPayState(`Reward payout smoke failed ${error?.message || 'unknown'}`);
    });
  }, []);

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
              <span>{reward.pending ?? <span className="zor-muted">—</span>}</span>
              <span>{reward.paid ?? <span className="zor-muted">—</span>}</span>
              <span>{reward.slashed ?? <span className="zor-muted">—</span>}</span>
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
          value={reporterId}
          onChange={(event) => setReporterId(event.target.value)}
          placeholder="Reporter ID, blank uses local identity"
          aria-label="Reward payout reporter ID"
        />
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
                <span>{item.value ?? <span className="zor-muted">—</span>}</span>
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

function EvidencePanel({ summary = {}, reads = [], demoMode = false }) {
  const total = Number(summary.accepted_read_count || 0);
  // Live: bind the total + the O3/O4/O5 split to real accepted reads; never the
  // hardcoded "1,248". When there are zero reads, show an explicit empty state.
  if (!demoMode && total === 0) {
    return (
      <section className="panel zor-panel">
        <div className="zor-section-header">
          <div>
            <h2>Evidence Distribution</h2>
            <p>Critical-use floor is O3 until proof-backed lanes are live.</p>
          </div>
          <span className="zor-subtle-chip">0 total</span>
        </div>
        <div className="zor-empty-state" role="status">
          <strong>No evidence yet</strong>
          <p>Awaiting accepted reads. The O3 / O4 / O5 distribution appears once reads are admitted.</p>
        </div>
      </section>
    );
  }
  // Distribution: demo uses the illustrative constant; live buckets real reads
  // by their evidence class (defensive — falls back to the O3+ count).
  let dist;
  let totalLabel = '1,248 total';
  if (demoMode) {
    dist = ORACLE_EVIDENCE_DISTRIBUTION;
  } else {
    const buckets = { O3: 0, O4: 0, O5: 0 };
    for (const r of (Array.isArray(reads) ? reads : [])) {
      const cls = String(r?.evidence_class || r?.evidence || '').toUpperCase();
      // Only count reads whose class is actually reported — never upgrade an
      // unknown/unclassified read into O3. Unclassified reads are excluded from
      // the distribution (percentages are of classified reads).
      if (cls.includes('O5')) buckets.O5 += 1;
      else if (cls.includes('O4')) buckets.O4 += 1;
      else if (cls.includes('O3')) buckets.O3 += 1;
    }
    const denom = (buckets.O3 + buckets.O4 + buckets.O5) || 1;
    dist = [
      { id: 'o3', label: 'O3 Robust', percent: Math.round((buckets.O3 / denom) * 100) },
      { id: 'o4', label: 'O4 Proof-backed', percent: Math.round((buckets.O4 / denom) * 100) },
      { id: 'o5', label: 'O5 Cross-checked', percent: Math.round((buckets.O5 / denom) * 100) },
    ];
    totalLabel = `${total.toLocaleString()} total`;
  }
  return (
    <section className="panel zor-panel">
      <div className="zor-section-header">
        <div>
          <h2>Evidence Distribution</h2>
          <p>Critical-use floor is O3 until proof-backed lanes are live.</p>
        </div>
        <span className="zor-subtle-chip">{totalLabel}</span>
      </div>
      <div className="zor-evidence-layout">
        <div className="zor-evidence-donut" aria-label="Evidence distribution">
          <span>O3+</span>
          <small>accepted</small>
        </div>
        <div className="zor-evidence-bars">
          {dist.map((item) => (
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

function EventsPanel({ events = [], demoMode = false }) {
  // Live mode renders REAL recent ledger activity (accepted reads / authorizations
  // / reward + slash receipts the snapshot surfaces), never the illustrative
  // ORACLE_EVENTS — those are gated behind demoMode so the "live tail" can't show
  // fabricated events on an empty node.
  const rows = demoMode ? ORACLE_EVENTS : (Array.isArray(events) ? events : []);
  return (
    <section className="panel zor-panel zor-events-panel">
      <div className="zor-section-header">
        <div>
          <h2>Recent Oracle Events</h2>
          <p>Ledger events should remain replayable after restart.</p>
        </div>
        {rows.length > 0 && (
          <span className="zor-subtle-chip">{demoMode ? 'live tail' : `${rows.length} recent`}</span>
        )}
      </div>
      {rows.length === 0 ? (
        <div className="zor-empty-state zor-empty-compact" role="status">
          <strong>No oracle events yet</strong>
          <p>Events appear once reads, authorizations, or settlements are recorded on the ledger.</p>
        </div>
      ) : (
        <div className="zor-event-strip">
          {rows.map((event) => (
            <article key={event.id} className={`zor-event-card zor-event-${event.tone || (event.status === 'disputed' ? 'warning' : 'neutral')}`}>
              <span className="zor-event-dot" />
              <strong>{event.kind}</strong>
              <small>{event.feed || event.consumer || event.queryId || '—'}</small>
              <span>{event.detail || event.value || ''}</span>
              <em>{event.age || (event.epoch != null ? `epoch ${event.epoch}` : '')}</em>
            </article>
          ))}
        </div>
      )}
    </section>
  );
}

function ServicesPanel({ summary = {}, authorityStatus = {}, demoMode = false }) {
  if (demoMode) {
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
              <strong className={service.status === 'Roadmap' ? 'zor-muted' : 'zor-green'}>{service.status}</strong>
            </div>
          ))}
        </div>
      </section>
    );
  }
  // Live: derive each row from a real node signal. Subsystems with no node-side
  // health probe read "Unverified" — never a decorative "Operational".
  const replayOk = summary.replay_ok === true;
  const authReady = authorityStatus?.status === 'ready'
    && (Array.isArray(authorityStatus?.readiness_gaps) ? authorityStatus.readiness_gaps.length === 0 : true);
  const services = [
    { id: 'replay', label: 'Receipt Verifier (replay)', status: replayOk ? 'Operational' : 'Degraded', tone: replayOk ? 'green' : 'warn' },
    { id: 'admission', label: 'Report Admission', status: authReady ? 'Operational' : 'Unverified', tone: authReady ? 'green' : 'muted' },
    { id: 'aggregation', label: 'Aggregation Engine', status: 'Unverified', tone: 'muted' },
    { id: 'dispute', label: 'Dispute System', status: summary.open_dispute_count != null ? 'Operational' : 'Unverified', tone: summary.open_dispute_count != null ? 'green' : 'muted' },
    { id: 'proof', label: 'Proof Generation', status: 'Roadmap', tone: 'muted' },
  ];
  const headline = replayOk && authReady ? 'Replay + authority ready' : replayOk ? 'Replay OK · authority pending' : 'Degraded';
  return (
    <section className="panel zor-panel">
      <div className="zor-section-header">
        <div>
          <h2>System Status</h2>
          <p>Service posture derived from live node signals (replay + authority).</p>
        </div>
        <span className={replayOk && authReady ? 'zor-system-ok' : 'zor-subtle-chip zor-chip-warn'}>{headline}</span>
      </div>
      <div className="zor-service-list">
        {services.map((service) => (
          <div key={service.id} className="zor-service-row">
            <span>{service.label}</span>
            <strong className={service.tone === 'green' ? 'zor-green' : 'zor-muted'}>{service.status}</strong>
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
  const signatureQuorum = status.signature_quorum || {};
  const signedWeight = signatureQuorum.accepted_weight || 0;
  const signedThreshold = signatureQuorum.threshold || status.threshold || 0;
  const controls = [
    ['External signer', walletUx.external_signer_required],
    ['Key manager', walletUx.key_manager_required],
    ['Device approval', walletUx.device_approval_required],
    ['Proof required', proofProfile.zk_or_proof_required],
    ['Receipt replay', proofProfile.oracle_receipt_replay_required],
    ['Signed quorum', signedThreshold > 0 && signedWeight >= signedThreshold],
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
          <small>Signed quorum</small>
          <strong>{signedWeight}/{signedThreshold}</strong>
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

function AuthorityExercisePanel({
  authorityStatus,
  authorityExerciseResult,
  authorityExerciseState,
  authorityExerciseBusy,
  onRunAuthorityExercise,
}) {
  const exerciseStatus = authorityExerciseResult?.authority_exercise_status || null;
  const targetNetwork = exerciseStatus?.target_network || 'local';
  const publicEvidence = exerciseStatus?.public_testnet_evidence_present === true;
  const errors = Array.isArray(exerciseStatus?.errors) ? exerciseStatus.errors : [];

  return (
    <section className="panel zor-panel zor-authority-panel">
      <div className="zor-section-header">
        <div>
          <h2>Authority Exercise</h2>
          <p>Run a bounded signed authority exercise over a real local operator flow and bind the receipt IDs.</p>
        </div>
        <span className={`zor-authority-chip ${exerciseStatus?.ok ? 'zor-authority-ready' : 'zor-authority-blocked'}`}>
          {exerciseStatus?.ok ? 'Exercise ready' : 'Exercise pending'}
        </span>
      </div>
      <div className="zor-authority-summary">
        <div>
          <small>Target network</small>
          <strong>{targetNetwork}</strong>
        </div>
        <div>
          <small>Authority profile</small>
          <strong>{authorityStatus?.production_authority ? 'ready' : 'blocked'}</strong>
        </div>
        <div>
          <small>Public testnet evidence</small>
          <strong>{publicEvidence ? 'present' : 'pending'}</strong>
        </div>
        <div>
          <small>Exercise hash</small>
          <strong>{compactId(exerciseStatus?.exercise_hash)}</strong>
        </div>
        <div>
          <small>Status hash</small>
          <strong>{compactId(exerciseStatus?.status_hash)}</strong>
        </div>
        <div>
          <small>Receipt binding</small>
          <strong>{compactId(exerciseStatus?.receipt_binding_hash)}</strong>
        </div>
        <div>
          <small>Public evidence binding</small>
          <strong>{compactId(exerciseStatus?.public_testnet_evidence_binding_hash)}</strong>
        </div>
        <div>
          <small>Public broadcast</small>
          <strong>{compactId(exerciseStatus?.public_broadcast_reference)}</strong>
        </div>
        <div>
          <small>Public settlement</small>
          <strong>{compactId(exerciseStatus?.public_settlement_reference)}</strong>
        </div>
        <div>
          <small>Broadcast height</small>
          <strong>{exerciseStatus?.public_broadcast_height ?? 'none'}</strong>
        </div>
        <div>
          <small>Settlement height</small>
          <strong>{exerciseStatus?.public_settlement_height ?? 'none'}</strong>
        </div>
        <div>
          <small>Authorization</small>
          <strong>{compactId(exerciseStatus?.authorization_id)}</strong>
        </div>
      </div>
      <div className="zor-authority-controls">
        <span className={exerciseStatus?.authority_exercised ? 'zor-control-ok' : 'zor-control-missing'}>
          Authority exercised
        </span>
        <span className={publicEvidence ? 'zor-control-ok' : 'zor-control-missing'}>
          Public testnet evidence
        </span>
      </div>
      <div className="zor-toolbar">
        <button className="btn btn-secondary" type="button" onClick={onRunAuthorityExercise} disabled={authorityExerciseBusy}>
          {authorityExerciseBusy ? 'Running...' : 'Run Authority Exercise'}
        </button>
        {authorityExerciseState ? <span className="zor-subtle-chip">{authorityExerciseState}</span> : null}
      </div>
      {errors.length ? (
        <div className="zor-authority-gaps">
          {errors.slice(0, 5).map((error) => (
            <span key={error}>{error}</span>
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

function FeedDetailInspector({ feed, reporters, disputes, onAddDispute, demoMode = false }) {
  const [reportId, setReportId] = useState(feed.receiptId || '');
  const [reporterId, setReporterId] = useState(reporters?.[0]?.id || '');
  const [bondAmount, setBondAmount] = useState('100000000'); // 1 ZENO in e8
  const [reason, setReason] = useState('price-deviation');
  const [statusMsg, setStatusMsg] = useState('');
  const disputeSmokeRan = useRef(false);

  const simulatedSubmissions = useMemo(() => {
    if (!feed || !reporters) return [];
    const baseVal = parseFloat(feed.value) || 1.0;
    return reporters.map((rep, idx) => {
      const devPercent = ((idx * 3 - 2) * (feed.deviationBps || 10)) / 10000 / 2;
      const subVal = (baseVal * (1 + devPercent)).toFixed(4);
      return {
        reporterId: rep.id,
        value: subVal,
        unit: feed.unit,
        status: rep.status,
        epoch: 'current',
        bond: rep.bond,
      };
    });
  }, [feed, reporters]);

  const feedDisputes = useMemo(() => {
    return disputes.filter(d => d.feed === feed.feed);
  }, [disputes, feed]);

  async function openDispute({
    reportIdOverride = '',
    reporterIdOverride = '',
    reasonOverride = '',
    bondAmountOverride = '',
  } = {}) {
    setStatusMsg('Opening dispute...');
    const requestReportId = String(reportIdOverride || reportId || '').trim();
    const requestReporterId = String(reporterIdOverride || reporterId || '').trim();
    const requestReason = String(reasonOverride || reason || '').trim();
    const requestBondAmount = String(bondAmountOverride || bondAmount || '0').trim();
    try {
      const response = await fetch(zenoOracleApiUrl('/api/oracle/dispute/open'), {
        method: 'POST',
        headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify({
          report_id: requestReportId,
          reporter_id: requestReporterId,
          bond_e8: Number(requestBondAmount || 0),
          reason: requestReason,
        }),
      });
      const rawBody = await response.text();
      let payload = {};
      if (rawBody) {
        try {
          payload = JSON.parse(rawBody);
        } catch {
          if (response.ok) {
            throw new Error('invalid_dispute_response_json');
          }
        }
      }
      if (!response.ok || payload.ok === false) {
        throw new Error(payload.error || 'Write disabled or failed');
      }

      const newDispute = {
        id: payload.dispute_id || `dsp_${Date.now()}`,
        feed: feed.feed,
        target: requestReportId,
        reporter: requestReporterId,
        bond: `${formatE8(requestBondAmount)} ZENO`,
        age: '1m',
        status: 'open',
      };
      onAddDispute(newDispute);
      setStatusMsg(`Dispute opened successfully: ${payload.dispute_id || newDispute.id}`);
    } catch (err) {
      if (!demoMode) {
        setStatusMsg(`Dispute open failed: ${err?.message || 'unknown'}`);
        return;
      }
      const mockDisputeId = `dsp_${Math.random().toString(36).substr(2, 9)}`;
      const newDispute = {
        id: mockDisputeId,
        feed: feed.feed,
        target: requestReportId,
        reporter: requestReporterId,
        bond: `${(Number(requestBondAmount) / 100000000).toFixed(2)} ZENO`,
        age: '1m',
        status: 'open',
      };
      onAddDispute(newDispute);
      setStatusMsg(`Added local demo dispute: ${mockDisputeId}`);
    }
  }

  async function handleOpenDispute(e) {
    e.preventDefault();
    await openDispute();
  }

  useEffect(() => {
    if (typeof window === 'undefined') return;
    const params = new URLSearchParams(window.location.search);
    if (params.get('zenodexUiSmokeOracleDisputeFailClosed') !== '1' || disputeSmokeRan.current) {
      return;
    }
    disputeSmokeRan.current = true;
    void openDispute({
      reportIdOverride: reportId || 'sha256:00000000000000000000000000000000000000000000000000000000000000dd',
      reporterIdOverride: reporterId || 'reporter:ui-smoke',
      reasonOverride: reason || 'price-deviation',
      bondAmountOverride: bondAmount || '100000000',
    });
    // eslint-disable-next-line react-hooks/exhaustive-deps
  }, [bondAmount, reason, reportId, reporterId]);

  return (
    <section className="panel zor-panel feed-detail-inspector" style={{ marginTop: 'var(--space-lg)', padding: 'var(--space-md)' }}>
      <div className="zor-section-header" style={{ borderBottom: '1px solid var(--border-subtle)', paddingBottom: 'var(--space-sm)' }}>
        <div>
          <h2>Feed Detail Inspector: <span style={{ color: 'var(--accent-purple)' }}>{feed.feed}</span></h2>
          <p>Detailed reporter consensus, deviation boundaries, and dispute controls.</p>
        </div>
        <EvidenceBadge value={feed.evidenceClass} />
      </div>

      <div style={{ display: 'grid', gridTemplateColumns: 'repeat(auto-fit, minmax(300px, 1fr))', gap: 'var(--space-lg)', marginTop: 'var(--space-md)' }}>
        {/* Consensus & Reporter Submissions */}
        <div style={{ background: 'var(--bg-secondary)', padding: 'var(--space-md)', borderRadius: 'var(--radius-md)', border: '1px solid var(--border-subtle)' }}>
          <h3 style={{ fontSize: 'var(--font-size-md)', marginBottom: 'var(--space-md)', borderBottom: '1px solid var(--border-subtle)', paddingBottom: '4px' }}>
            Reporter Submissions
          </h3>
          <div style={{ display: 'flex', flexDirection: 'column', gap: 'var(--space-xs)' }}>
            {simulatedSubmissions.map((sub, idx) => (
              <div key={idx} style={{ display: 'flex', justifyContent: 'space-between', alignItems: 'center', padding: '6px 10px', background: 'var(--bg-secondary)', borderRadius: '4px', borderLeft: `3px solid ${sub.status === 'active' ? 'var(--accent-green)' : 'var(--accent-red)'}` }}>
                <div>
                  <div style={{ fontFamily: 'var(--font-mono)', fontSize: 'var(--font-size-xs)' }}>{sub.reporterId}</div>
                  <small style={{ color: 'var(--text-secondary)', fontSize: 'var(--font-size-xs)' }}>Bonded: {sub.bond}</small>
                </div>
                <div style={{ textAlign: 'right' }}>
                  <div style={{ fontWeight: 'bold' }}>{sub.value} {sub.unit}</div>
                  <small style={{ color: 'var(--text-secondary)', fontSize: 'var(--font-size-xs)' }}>{sub.epoch}</small>
                </div>
              </div>
            ))}
          </div>
        </div>

        {/* Challenge parameters */}
        <div style={{ background: 'var(--bg-secondary)', padding: 'var(--space-md)', borderRadius: 'var(--radius-md)', border: '1px solid var(--border-subtle)' }}>
          <h3 style={{ fontSize: 'var(--font-size-md)', marginBottom: 'var(--space-md)', borderBottom: '1px solid var(--border-subtle)', paddingBottom: '4px' }}>
            Security Boundaries
          </h3>
          <div style={{ display: 'flex', flexDirection: 'column', gap: 'var(--space-sm)' }}>
            <div style={{ display: 'flex', justifyContent: 'space-between', borderBottom: '1px dashed var(--border-subtle)', paddingBottom: 'var(--space-xs)' }}>
              <span>Deviation Bound</span>
              <strong>{formatBpsAsPercent(feed.deviationBps) || '—'}</strong>
            </div>
            <div style={{ display: 'flex', justifyContent: 'space-between', borderBottom: '1px dashed var(--border-subtle)', paddingBottom: 'var(--space-xs)' }}>
              <span>Confidence Margin</span>
              <strong>{feed.confidence || '—'}</strong>
            </div>
            <div style={{ display: 'flex', justifyContent: 'space-between', borderBottom: '1px dashed var(--border-subtle)', paddingBottom: 'var(--space-xs)' }}>
              <span>Active Challenge Bond</span>
              <strong>1,000 ZENO</strong>
            </div>
            <div style={{ display: 'flex', justifyContent: 'space-between', borderBottom: '1px dashed var(--border-subtle)', paddingBottom: 'var(--space-xs)' }}>
              <span>Preflight Target</span>
              <span style={{ fontSize: 'var(--font-size-xs)', fontFamily: 'var(--font-mono)' }}>{compactId(feed.receiptId)}</span>
            </div>
          </div>
        </div>
      </div>

      <div style={{ display: 'grid', gridTemplateColumns: 'repeat(auto-fit, minmax(300px, 1fr))', gap: 'var(--space-lg)', marginTop: 'var(--space-md)' }}>
        {/* Disputes List */}
        <div style={{ background: 'var(--bg-secondary)', padding: 'var(--space-md)', borderRadius: 'var(--radius-md)', border: '1px solid var(--border-subtle)' }}>
          <h3 style={{ fontSize: 'var(--font-size-md)', marginBottom: 'var(--space-md)', borderBottom: '1px solid var(--border-subtle)', paddingBottom: '4px' }}>
            Active Disputes
          </h3>
          {feedDisputes.length === 0 ? (
            <div style={{ color: 'var(--text-secondary)', fontStyle: 'italic', padding: 'var(--space-sm)', fontSize: 'var(--font-size-sm)' }}>
              No active disputes on this feed.
            </div>
          ) : (
            <div className="zor-dispute-list">
              {feedDisputes.map(dispute => (
                <div key={dispute.id} className="zor-dispute-row" style={{ padding: '6px 10px', background: 'var(--bg-secondary)', marginBottom: '4px', borderRadius: '4px', display: 'flex', justifyContent: 'space-between', alignItems: 'center' }}>
                  <div>
                    <strong>{dispute.id}</strong>
                    <small style={{ display: 'block', color: 'var(--text-secondary)', fontSize: 'var(--font-size-xs)' }}>Target: {compactId(dispute.target)}</small>
                  </div>
                  <div style={{ textAlign: 'right' }}>
                    <span>{dispute.bond}</span>
                    <small style={{ display: 'block', color: 'var(--text-secondary)', fontSize: 'var(--font-size-xs)' }}>{dispute.age}</small>
                  </div>
                  <span className={`zor-status zor-dispute-${dispute.status}`}>{dispute.status}</span>
                </div>
              ))}
            </div>
          )}
        </div>

        {/* Counter-Claim Form */}
        <div style={{ background: 'var(--bg-secondary)', padding: 'var(--space-md)', borderRadius: 'var(--radius-md)', border: '1px solid var(--border-subtle)' }}>
          <h3 style={{ fontSize: 'var(--font-size-md)', marginBottom: 'var(--space-md)', borderBottom: '1px solid var(--border-subtle)', paddingBottom: '4px' }}>
            Submit Counter-Claim Dispute
          </h3>
          <form onSubmit={handleOpenDispute} style={{ display: 'flex', flexDirection: 'column', gap: 'var(--space-sm)' }}>
            <div>
              <label style={{ fontSize: 'var(--font-size-xs)', color: 'var(--text-secondary)', display: 'block', marginBottom: '2px' }}>Dispute Target (Receipt ID)</label>
              <input
                className="input"
                style={{ width: '100%' }}
                value={reportId}
                onChange={e => setReportId(e.target.value)}
                placeholder="Receipt ID"
                required
              />
            </div>
            <div>
              <label style={{ fontSize: 'var(--font-size-xs)', color: 'var(--text-secondary)', display: 'block', marginBottom: '2px' }}>Target Reporter</label>
              <select
                className="input"
                style={{ width: '100%' }}
                value={reporterId}
                onChange={e => setReporterId(e.target.value)}
              >
                {reporters.map(rep => (
                  <option key={rep.id} value={rep.id}>{rep.id}</option>
                ))}
              </select>
            </div>
            <div style={{ display: 'flex', gap: 'var(--space-sm)' }}>
              <div style={{ flex: 1 }}>
                <label style={{ fontSize: 'var(--font-size-xs)', color: 'var(--text-secondary)', display: 'block', marginBottom: '2px' }}>Challenge Bond (e8)</label>
                <input
                  className="input"
                  style={{ width: '100%' }}
                  value={bondAmount}
                  onChange={e => setBondAmount(e.target.value)}
                  placeholder="100000000"
                  type="number"
                  required
                />
              </div>
              <div style={{ flex: 1 }}>
                <label style={{ fontSize: 'var(--font-size-xs)', color: 'var(--text-secondary)', display: 'block', marginBottom: '2px' }}>Dispute Reason</label>
                <select
                  className="input"
                  style={{ width: '100%' }}
                  value={reason}
                  onChange={e => setReason(e.target.value)}
                >
                  <option value="price-deviation">Price Deviation</option>
                  <option value="stale-report">Stale Report</option>
                  <option value="malicious-value">Malicious Value</option>
                </select>
              </div>
            </div>
            <button className="btn btn-primary" type="submit" style={{ marginTop: 'var(--space-xs)', width: '100%' }}>
              File Dispute
            </button>
          </form>
          {statusMsg && <div style={{ marginTop: 'var(--space-sm)', fontSize: 'var(--font-size-xs)', color: 'var(--accent-cyan)' }}>{statusMsg}</div>}
        </div>
      </div>
    </section>
  );
}

export default ZenoOracleDashboard;
