// Copyright DarkLightX/Dana Edwards
// Persistent status bar — feeds, reporters, authority, aggregation, disputes
// Shows a single glanceable health state across all tabs.

export default function OracleStatusBar({
  feeds = [],
  disputes = [],
  reporters = [],
  authorityReady = false,
  aggregationStatus = 'unknown',
  apiState = 'Static preview',
  lastUpdateLabel = '',
  onViewDisputes = null,
}) {
  const healthyCount = feeds.filter((f) => f.status === 'fresh').length;
  const staleCount = feeds.filter((f) => f.status === 'stale').length;
  const disputedCount = disputes.filter((d) => d.status === 'open').length;
  const activeReporters = reporters.filter((r) => r.status === 'active').length;
  const feedTotal = feeds.length;

  // Derive overall status: DOWN > STALE > WARN > LIVE
  let statusKey = 'live';
  let statusLabel = 'LIVE';
  if (apiState === 'Offline') {
    statusKey = 'down';
    statusLabel = 'DOWN';
  } else if (staleCount > 0) {
    statusKey = 'stale';
    statusLabel = 'STALE';
  } else if (disputedCount > 0 || aggregationStatus === 'down') {
    statusKey = 'warn';
    statusLabel = 'WARN';
  }

  // Aggregation chip
  const aggChipClass = aggregationStatus === 'ok'
    ? 'ok'
    : aggregationStatus === 'down'
      ? 'err'
      : aggregationStatus === 'warn'
        ? 'warn'
        : 'unknown';
  const aggLabel = aggregationStatus === 'ok'
    ? 'OK'
    : aggregationStatus === 'down'
      ? 'down'
      : aggregationStatus === 'warn'
        ? 'warn'
        : 'unknown';

  // Feed summary: when no feeds configured, show "0 feeds configured" not 3 zero counts
  const feedSummary = feedTotal === 0
    ? '0 feeds configured'
    : `${healthyCount} healthy / ${staleCount} stale / ${disputedCount} disputed`;

  return (
    <div className="oracle-status-bar" role="status" aria-live="polite">
      <div className="oracle-status-row">
        <span className={`oracle-status-dot ${statusKey}`} aria-hidden="true"></span>
        <span className={`oracle-status-label ${statusKey}`}>{statusLabel}</span>
        <span className="oracle-status-meta">
          Feeds: {feedSummary}
          {lastUpdateLabel ? ` | Updated: ${lastUpdateLabel}` : ''}
        </span>
        <span className="oracle-status-meta">
          Data sources: {activeReporters} active
          {' | Security: '}
          <span style={{ color: authorityReady ? '#34d399' : '#facc15' }}>
            {authorityReady ? 'ready' : 'pending'}
          </span>
          {' | Data processing: '}
          <span className={`oracle-status-chip ${aggChipClass}`}>{aggLabel}</span>
        </span>
        {disputedCount > 0 && onViewDisputes && (
          <button
            className="oracle-status-action"
            type="button"
            onClick={onViewDisputes}
          >
            View dispute →
          </button>
        )}
      </div>
    </div>
  );
}
