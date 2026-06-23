// Copyright DarkLightX/Dana Edwards
// Oracle dashboard utility functions — pure helpers with no JSX.
import { getRuntimeConfig } from './api.js';

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

export {
  normalizeOracleApiBase,
  zenoOracleApiUrl,
  compactId,
  parsePositiveIntParam,
  formatE8,
  formatTokenE8,
  formatEpochWindow,
  formatEpochLabel,
  formatBpsAsPercent,
  randomSmokeHex,
  smokeHash,
  getInitialOracleSection,
  primaryStatus,
  snapshotToDashboardData,
  runOracleWriteSmokeFlow,
  ORACLE_SECTIONS,
  DEFAULT_ZENO_ORACLE_API_BASE,
};
