// Copyright DarkLightX/Dana Edwards
// Oracle status pills, metric cards, health, feature strip, services, events panels.
import { ORACLE_HEALTH_METRICS, ORACLE_EVENTS, ORACLE_SYSTEM_SERVICES } from '../ZenoOracleDashboardData.js';

const STATUS_COPY = {
  fresh: 'Fresh',
  stale: 'Stale',
  disputed: 'Disputed',
  'devnet-only': 'Devnet only',
  'high-uncertainty': 'High uncertainty',
};

const ORACLE_FEATURES = [
  {
    id: 'proof_bound',
    title: 'Verified',
    detail: 'Values are verified and traceable.',
  },
  {
    id: 'action_specific',
    title: 'Single-use',
    detail: 'Each approval is for one specific action.',
  },
  {
    id: 'verifiable',
    title: 'Checkable',
    detail: 'Records can be independently verified.',
  },
  {
    id: 'economic',
    title: 'Financially protected',
    detail: 'High-value actions require strong security.',
  },
  {
    id: 'permissionless',
    title: 'Open to all',
    detail: 'Anyone can report, flag errors, and earn rewards.',
  },
];

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
            <p>Services must be verifiable before data is used.</p>
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
          <p>Services must be verifiable before data is used.</p>
        </div>
        <span className={`zor-subtle-chip ${replayOk ? 'zor-chip-ok' : 'zor-chip-warn'}`}>
          {replayOk ? 'Verified' : 'Not verified'}
        </span>
      </div>
      {hasData ? (
        <div className="zor-health-list">
          <div className="zor-health-row"><span>Verification system</span><strong>{replayOk ? 'OK' : 'Fail'}</strong></div>
          <div className="zor-health-row"><span>Accepted updates</span><strong>{reads}</strong></div>
          <div className="zor-health-row"><span>High-quality updates</span><strong>{Number(summary.o3_plus_read_count || 0)}</strong></div>
          <div className="zor-health-row"><span>Active feeds</span><strong>{feeds}</strong></div>
          <div className="zor-health-row"><span>Flagged reports</span><strong>{Number(summary.open_dispute_count || 0)}</strong></div>
        </div>
      ) : (
        <div className="zor-empty-state" role="status">
          <strong>No health data yet</strong>
          <p>
            Awaiting feeds and accepted reads. Composite health metrics activate once the node
            reports replay-bound reads.{replayOk ? ' Verification system is currently OK.' : ''}
          </p>
        </div>
      )}
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
          <p>Records should remain verifiable after restart.</p>
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
            <p>System status.</p>
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
    { id: 'replay', label: 'Record verifier', status: replayOk ? 'Operational' : 'Degraded', tone: replayOk ? 'green' : 'warn' },
    { id: 'admission', label: 'Data acceptance', status: authReady ? 'Operational' : 'Unverified', tone: authReady ? 'green' : 'muted' },
    { id: 'aggregation', label: 'Data processing', status: 'Unverified', tone: 'muted' },
    { id: 'dispute', label: 'Flagging system', status: summary.open_dispute_count != null ? 'Operational' : 'Unverified', tone: summary.open_dispute_count != null ? 'green' : 'muted' },
    { id: 'proof', label: 'Verification system', status: 'Roadmap', tone: 'muted' },
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

export {
  StatusPill,
  MetricCard,
  HealthPanel,
  FeatureStrip,
  ServicesPanel,
  EventsPanel,
};
