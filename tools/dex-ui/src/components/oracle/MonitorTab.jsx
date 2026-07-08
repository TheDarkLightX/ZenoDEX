// Copyright DarkLightX/Dana Edwards
// Monitor tab — feed table (master) + feed detail rail (detail) +
// inline submit panel + system health (auto-expand on unknown/down).

import { useMemo, useState } from 'react';

const STATUS_ORDER = { fresh: 0, stale: 1, disputed: 2, down: 3 };

export default function MonitorTab({
  feeds = [],
  selectedFeedId = '',
  onSelectFeed = () => {},
  onCreateFeed = () => {},
  onBuildReceipt = () => {},
  onOpenDispute = () => {},
  onRegisterReporter = () => {},
  remoteData = null,
  postOracle = null,
}) {
  const [searchQuery, setSearchQuery] = useState('');
  const [statusFilter, setStatusFilter] = useState('all');
  const [showSubmitPanel, setShowSubmitPanel] = useState(false);
  const [submitValue, setSubmitValue] = useState('');
  const [submitState, setSubmitState] = useState('empty');
  const [healthExpanded, setHealthExpanded] = useState(false);
  const [railCollapsed, setRailCollapsed] = useState(false);

  const selectedFeed = feeds.find((f) => f.id === selectedFeedId) || feeds[0] || null;
  const hasRealFeed = Boolean(selectedFeed) && selectedFeed.id !== 'placeholder';

  const filteredFeeds = useMemo(() => {
    let result = feeds;
    if (statusFilter !== 'all') {
      result = result.filter((f) => f.status === statusFilter);
    }
    if (searchQuery.trim()) {
      const q = searchQuery.toLowerCase();
      result = result.filter((f) => (f.feed || '').toLowerCase().includes(q));
    }
    return result;
  }, [feeds, statusFilter, searchQuery]);

  // System health: auto-expand if any service is unknown or down
  const summary = remoteData?.summary || {};
  const aggregationStatus = summary.aggregation_ok === true
    ? 'ok'
    : summary.aggregation_ok === false
      ? 'down'
      : 'unknown';
  const replayStatus = summary.replay_ok === true
    ? 'ok'
    : summary.replay_ok === false
      ? 'down'
      : 'unknown';
  const authorityStatus = remoteData?.authorityStatus?.production_authority === true
    ? 'ok'
    : 'unknown';
  const keyMgrStatus = remoteData?.authorityStatus?.key_manager_count > 0
    ? 'ok'
    : 'unknown';

  const hasUnknownHealth = aggregationStatus === 'unknown' || replayStatus === 'unknown'
    || authorityStatus === 'unknown' || keyMgrStatus === 'unknown';
  const isHealthExpanded = healthExpanded || hasUnknownHealth;

  // Submit deviation check
  const submitDeviation = (() => {
    if (!submitValue || !selectedFeed) return null;
    const submitted = parseFloat(submitValue);
    if (!Number.isFinite(submitted)) return null;
    const currentVal = parseFloat(selectedFeed.value);
    if (!Number.isFinite(currentVal) || currentVal === 0) return null;
    return Math.abs((submitted - currentVal) / currentVal) * 100;
  })();

  const submitDeviationState = submitDeviation === null
    ? 'empty'
    : submitDeviation > 1.0
      ? 'blocked'
      : 'pass';

  const handleRailToggle = () => setRailCollapsed(!railCollapsed);

  return (
    <div className="oracle-tab-panel">
      {/* Filter bar */}
      <div className="oracle-filter-bar">
        <input
          className="oracle-search-input"
          type="text"
          placeholder="Search feeds..."
          value={searchQuery}
          onChange={(e) => setSearchQuery(e.target.value)}
          aria-label="Search feeds"
        />
        <select
          className="oracle-search-input"
          style={{ flex: '0 0 auto', minWidth: 'auto' }}
          value={statusFilter}
          onChange={(e) => setStatusFilter(e.target.value)}
          aria-label="Filter by status"
        >
          <option value="all">All statuses</option>
          <option value="fresh">Live</option>
          <option value="stale">Outdated</option>
          <option value="disputed">Flagged</option>
        </select>
        <button
          className="oracle-feed-detail-btn"
          type="button"
          onClick={handleRailToggle}
          style={{ flex: '0 0 auto' }}
        >
          {railCollapsed ? 'Show detail →' : '← Hide detail'}
        </button>
      </div>

      {/* Master-detail layout */}
      <div className={`oracle-monitor-layout ${railCollapsed ? 'rail-collapsed' : ''}`}>
        {/* Feed table (master) */}
        <div>
          <div className="oracle-feed-table">
            <div className="oracle-feed-table-head">
              <span>Feed</span>
              <span>Price</span>
              <span>Reliability</span>
              <span>Status</span>
              <span>Age</span>
            </div>
            {filteredFeeds.length === 0 ? (
              <div className="oracle-feed-empty">
                <div className="oracle-feed-empty-title">No feeds configured.</div>
                <div className="oracle-feed-empty-hint">
                  Trader? Ask your admin to configure oracle feeds.<br />
                  Admin? Create your first feed to start receiving price data.
                </div>
                <div className="oracle-feed-empty-actions">
                  <button
                    className="btn btn-primary"
                    type="button"
                    onClick={onCreateFeed}
                  >
                    + Create first feed
                  </button>
                </div>
              </div>
            ) : (
              filteredFeeds.map((feed) => (
                <div
                  key={feed.id}
                  className={`oracle-feed-row ${selectedFeed?.id === feed.id ? 'selected' : ''}`}
                  onClick={() => onSelectFeed(feed.id)}
                  role="row"
                  tabIndex={0}
                  onKeyDown={(e) => {
                    if (e.key === 'Enter' || e.key === ' ') {
                      e.preventDefault();
                      onSelectFeed(feed.id);
                    }
                  }}
                >
                  <span>{feed.feed}</span>
                  <span>{feed.value}{feed.unit ? ` ${feed.unit}` : ''}</span>
                  <span style={{ opacity: 0.6 }}>{feed.confidence || '—'}</span>
                  <span className={`oracle-feed-status ${feed.status === 'fresh' ? 'live' : feed.status === 'stale' ? 'stale' : feed.status === 'disputed' ? 'disputed' : 'down'}`}>
                    <span className="dot" aria-hidden="true"></span>
                    {feed.status === 'fresh' ? 'live' : feed.status === 'stale' ? 'outdated' : feed.status === 'disputed' ? 'flagged' : feed.status === 'down' ? 'offline' : feed.status}
                  </span>
                  <span style={{ opacity: 0.5 }}>{feed.freshness || '—'}</span>
                </div>
              ))
            )}
          </div>
          {/* Status legend */}
          <div className="oracle-status-legend">
            <span className="oracle-status-legend-item">
              <span className="oracle-status-dot live" style={{ width: 6, height: 6 }}></span>
              live
            </span>
            <span className="oracle-status-legend-item">
              <span className="oracle-status-dot stale" style={{ width: 6, height: 6 }}></span>
              outdated
            </span>
            <span className="oracle-status-legend-item">
              <span className="oracle-status-dot down" style={{ width: 6, height: 6 }}></span>
              offline
            </span>
            <span className="oracle-status-legend-item">
              <span className="oracle-status-dot warn" style={{ width: 6, height: 6 }}></span>
              flagged
            </span>
          </div>
        </div>

        {/* Feed detail rail */}
        {!railCollapsed && (
          <div className="oracle-feed-detail">
            {hasRealFeed ? (
              <>
                <div className="oracle-feed-detail-title">{selectedFeed.feed}</div>
                <div className="oracle-feed-detail-grid">
                  <div className="oracle-feed-detail-row">
                    <span className="oracle-feed-detail-label">Price</span>
                    <span className="oracle-feed-detail-value">
                      {selectedFeed.value}{selectedFeed.unit ? ` ${selectedFeed.unit}` : ''}
                    </span>
                  </div>
                  <div className="oracle-feed-detail-row">
                    <span className="oracle-feed-detail-label">Freshness</span>
                    <span className="oracle-feed-detail-value">{selectedFeed.freshness || '—'}</span>
                  </div>
                  <div className="oracle-feed-detail-row">
                    <span className="oracle-feed-detail-label">Confidence</span>
                    <span className="oracle-feed-detail-value">{selectedFeed.confidence || '—'}</span>
                  </div>
                  <div className="oracle-feed-detail-row">
                    <span className="oracle-feed-detail-label">Evidence</span>
                    <span className="oracle-feed-detail-value">{selectedFeed.evidenceClass || '—'}</span>
                  </div>
                  <div className="oracle-feed-detail-row">
                    <span className="oracle-feed-detail-label">24h change</span>
                    <span className="oracle-feed-detail-value">{selectedFeed.change24h || '—'}</span>
                  </div>
                </div>

                <div className="oracle-feed-detail-actions">
                  <button
                    className="oracle-feed-detail-btn primary"
                    type="button"
                    onClick={() => setShowSubmitPanel(!showSubmitPanel)}
                  >
                    {showSubmitPanel ? '▼ Cancel submit' : '→ Submit value'}
                  </button>
                  <button
                    className="oracle-feed-detail-btn"
                    type="button"
                    onClick={onBuildReceipt}
                  >
                    → Build receipt
                  </button>
                  <button
                    className="oracle-feed-detail-btn danger"
                    type="button"
                    onClick={onOpenDispute}
                  >
                    → Open dispute
                  </button>
                </div>

                {/* Inline submit panel */}
                {showSubmitPanel && (
                  <div className="oracle-submit-panel">
                    <div className="oracle-submit-panel-title">
                      Submit Value — {selectedFeed.feed}
                    </div>
                    <div className="oracle-submit-field">
                      <span className="oracle-submit-label">Value</span>
                      <input
                        className="oracle-submit-input"
                        type="text"
                        inputMode="decimal"
                        placeholder="0.00"
                        value={submitValue}
                        onChange={(e) => {
                          setSubmitValue(e.target.value);
                          setSubmitState('empty');
                        }}
                        aria-label="Submit value"
                      />
                    </div>
                    {submitDeviation !== null && (
                      <div className={`oracle-submit-deviation ${submitDeviationState}`}>
                        {submitDeviationState === 'pass'
                          ? `✓ Deviation ${submitDeviation.toFixed(3)}% — within threshold`
                          : `✕ Deviation ${submitDeviation.toFixed(2)}% EXCEEDS threshold — BLOCKED. Submitting risks bond slash + dispute.`}
                      </div>
                    )}
                    <div className="oracle-submit-bond">
                      Bond: locked — <span className="slash-warn">slashed if overturned</span>
                    </div>
                    <button
                      className="oracle-submit-btn"
                      type="button"
                      disabled={submitDeviationState === 'blocked' || !submitValue}
                      onClick={() => {
                        if (!postOracle) return;
                        setSubmitState('loading');
                        postOracle('/api/oracle/report', {
                          query_id: selectedFeed.queryId || selectedFeed.id,
                          value_e8: Math.round(parseFloat(submitValue) * 1e8),
                        })
                          .then(() => setSubmitState('pass'))
                          .catch((err) => setSubmitState(`error: ${err.message}`));
                      }}
                    >
                      {submitState === 'loading' ? 'Submitting...' : 'SUBMIT VALUE'}
                    </button>
                    {submitState.startsWith('error') && (
                      <div style={{ fontSize: '0.72em', color: '#f87171', marginTop: 6 }}>
                        {submitState}
                      </div>
                    )}
                    <div className="oracle-submit-register">
                      First time?{' '}
                      <a onClick={onRegisterReporter}>Register as reporter →</a>
                    </div>
                  </div>
                )}
              </>
            ) : (
              <div className="oracle-empty">
                <strong>No feed selected</strong>
                <p style={{ marginTop: 8 }}>
                  Create a feed to inspect its price, submit values, and build receipts.
                </p>
              </div>
            )}
          </div>
        )}
      </div>

      {/* System health (auto-expanded if any unknown) */}
      <div className="oracle-health">
        <div
          className="oracle-health-toggle"
          onClick={() => setHealthExpanded(!healthExpanded)}
          role="button"
          tabIndex={0}
          aria-expanded={isHealthExpanded}
          onKeyDown={(e) => { if (e.key === 'Enter' || e.key === ' ') { e.preventDefault(); setHealthExpanded(!healthExpanded); } }}
        >
          <span>{isHealthExpanded ? '▼' : '▶'}</span>
          <span>System Health</span>
        </div>
        {isHealthExpanded && (
          <div className="oracle-health-body">
            <div className="oracle-health-item">
              <span>Authority:</span>
              <span className={`status ${authorityStatus}`}>{authorityStatus === 'ok' ? 'ready' : 'unknown'}</span>
            </div>
            <div className="oracle-health-item">
              <span>Replay:</span>
              <span className={`status ${replayStatus}`}>{replayStatus === 'ok' ? 'OK' : replayStatus === 'down' ? 'failing' : 'unknown'}</span>
            </div>
            <div className="oracle-health-item">
              <span>Key mgr:</span>
              <span className={`status ${keyMgrStatus}`}>{keyMgrStatus === 'ok' ? 'OK' : 'unknown'}</span>
            </div>
            <div className="oracle-health-item">
              <span>Aggregation:</span>
              <span className={`status ${aggregationStatus}`}>
                {aggregationStatus === 'ok' ? 'OK' : aggregationStatus === 'down' ? 'offline' : 'unknown'}
                {aggregationStatus === 'unknown' && ' (!)'}
              </span>
            </div>
          </div>
        )}
      </div>
    </div>
  );
}
