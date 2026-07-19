import { useEffect, useMemo, useState } from 'react';
import { getRuntimeConfig } from '../lib/api.js';
import './ZenoOracleDashboard.css';

const REFRESH_MS = 15_000;

function normalizeApiBase(raw) {
  const value = String(raw || '').trim();
  return value.endsWith('/') ? value.slice(0, -1) : value;
}

function oracleApiUrl(path) {
  const config = getRuntimeConfig();
  const base = normalizeApiBase(config.zenoOracleApiBase);
  return base ? `${base}${path}` : path;
}

function compactId(value) {
  const text = String(value || '');
  if (!text) return '—';
  return text.length > 24 ? `${text.slice(0, 12)}…${text.slice(-8)}` : text;
}

function listFrom(snapshot, ...keys) {
  for (const key of keys) {
    if (Array.isArray(snapshot?.[key])) return snapshot[key];
  }
  return [];
}

function metric(label, value) {
  return { label, value: value == null ? '—' : String(value) };
}

function ZenoOracleDashboard({ wallet = null } = {}) {
  const [snapshot, setSnapshot] = useState(null);
  const [status, setStatus] = useState('Loading live Oracle state…');
  const [error, setError] = useState('');

  useEffect(() => {
    const controller = new AbortController();
    let timer = null;

    async function load() {
      try {
        const response = await fetch(oracleApiUrl('/api/oracle/dashboard'), {
          cache: 'no-store',
          signal: controller.signal,
        });
        const body = await response.json();
        if (!response.ok || body?.ok === false) {
          throw new Error(body?.error || `HTTP ${response.status}`);
        }
        setSnapshot(body);
        setError('');
        setStatus('Live Oracle state');
      } catch (err) {
        if (err?.name !== 'AbortError') {
          setSnapshot(null);
          setError(String(err?.message || 'oracle_dashboard_unavailable'));
          setStatus('Oracle state unavailable');
        }
      } finally {
        if (!controller.signal.aborted) timer = window.setTimeout(load, REFRESH_MS);
      }
    }

    void load();
    return () => {
      controller.abort();
      if (timer) window.clearTimeout(timer);
    };
  }, []);

  const summary = snapshot?.summary && typeof snapshot.summary === 'object' ? snapshot.summary : {};
  const authority = snapshot?.authority_status && typeof snapshot.authority_status === 'object'
    ? snapshot.authority_status
    : snapshot?.authorityStatus && typeof snapshot.authorityStatus === 'object'
      ? snapshot.authorityStatus
      : {};
  const feeds = useMemo(
    () => listFrom(snapshot, 'feeds', 'feed_statuses', 'recent_aggregates'),
    [snapshot],
  );
  const reads = useMemo(
    () => listFrom(snapshot, 'recent_accepted_reads', 'accepted_reads'),
    [snapshot],
  );
  const authorizations = useMemo(
    () => listFrom(snapshot, 'recent_authorizations', 'authorizations'),
    [snapshot],
  );
  const metrics = [
    metric('Active feeds', summary.active_feed_count ?? summary.feed_count),
    metric('Accepted reads', summary.accepted_read_count),
    metric('Authorizations', summary.authorization_count),
    metric('Open disputes', summary.open_dispute_count),
  ];
  const authorityReady = snapshot?.production_authority === true || authority.production_authority === true;
  const readinessGaps = Array.isArray(authority.readiness_gaps)
    ? authority.readiness_gaps
    : Array.isArray(snapshot?.readiness_gaps)
      ? snapshot.readiness_gaps
      : [];

  return (
    <div className="zor-shell">
      <section className="zor-dashboard">
        <div className="zor-hero panel panel-glass">
          <div>
            <p className="zor-eyebrow">Oracle authority</p>
            <h1>ZenoOracle</h1>
            <p>Read-only, ledger-backed Oracle status. This surface never synthesizes or submits reports.</p>
          </div>
          <div className="zor-hero-meta">
            <span className="zor-subtle-chip">{status}</span>
            <span className={`zor-authority-chip ${authorityReady ? 'zor-authority-ready' : 'zor-authority-blocked'}`}>
              {authorityReady ? 'Production authority ready' : 'Authority unverified'}
            </span>
            <span className="zor-subtle-chip" title="Wallet controls live in the main header">
              {wallet?.address ? `Wallet ${compactId(wallet.address)}` : 'Wallet in header'}
            </span>
          </div>
        </div>

        {error && (
          <div className="zor-empty-state panel" role="alert">
            <strong>Live Oracle feed unavailable</strong>
            <p>{error}</p>
          </div>
        )}

        <div className="zor-metric-grid">
          {metrics.map((item) => (
            <article className="panel zor-metric-card" key={item.label}>
              <span>{item.label}</span>
              <strong>{item.value}</strong>
            </article>
          ))}
        </div>

        <div className="zor-two-up">
          <section className="panel zor-panel">
            <div className="zor-section-header">
              <div>
                <h2>Accepted Reads</h2>
                <p>Recent reads reported by the live dashboard endpoint.</p>
              </div>
              <span className="zor-subtle-chip">{reads.length}</span>
            </div>
            {reads.length === 0 ? (
              <div className="zor-empty-state"><strong>No accepted reads reported</strong></div>
            ) : reads.slice(0, 12).map((read, index) => (
              <div className="zor-service-row" key={read.read_id || read.id || index}>
                <span>{compactId(read.read_id || read.id)}</span>
                <strong>{read.evidence_class || read.profile_id || 'accepted'}</strong>
              </div>
            ))}
          </section>

          <section className="panel zor-panel">
            <div className="zor-section-header">
              <div>
                <h2>Action Authorizations</h2>
                <p>Recent action-bound authorizations reported by the node.</p>
              </div>
              <span className="zor-subtle-chip">{authorizations.length}</span>
            </div>
            {authorizations.length === 0 ? (
              <div className="zor-empty-state"><strong>No authorizations reported</strong></div>
            ) : authorizations.slice(0, 12).map((authorization, index) => (
              <div className="zor-service-row" key={authorization.authorization_id || authorization.id || index}>
                <span>{compactId(authorization.authorization_id || authorization.id)}</span>
                <strong>{authorization.action_kind || 'bound'}</strong>
              </div>
            ))}
          </section>
        </div>

        <section className="panel zor-panel">
          <div className="zor-section-header">
            <div>
              <h2>Feed State</h2>
              <p>Only feed rows returned by the live node are displayed.</p>
            </div>
            <span className="zor-subtle-chip">{feeds.length}</span>
          </div>
          {feeds.length === 0 ? (
            <div className="zor-empty-state"><strong>No feeds reported</strong></div>
          ) : feeds.slice(0, 20).map((feed, index) => (
            <div className="zor-service-row" key={feed.query_id || feed.aggregate_id || feed.id || index}>
              <span>{compactId(feed.query_id || feed.aggregate_id || feed.id)}</span>
              <strong>{feed.status || feed.evidence_class || 'reported'}</strong>
            </div>
          ))}
        </section>

        {!authorityReady && readinessGaps.length > 0 && (
          <section className="panel zor-panel" role="status">
            <div className="zor-section-header"><h2>Authority readiness gaps</h2></div>
            <div className="zor-authority-gaps">
              {readinessGaps.map((gap) => <span key={String(gap)}>{String(gap)}</span>)}
            </div>
          </section>
        )}
      </section>
    </div>
  );
}

export default ZenoOracleDashboard;
