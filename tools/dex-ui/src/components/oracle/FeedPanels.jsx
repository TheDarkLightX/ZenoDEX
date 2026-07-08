// Copyright DarkLightX/Dana Edwards
// Oracle feed table, feed status, feed creation, and feed detail inspector panels.
import { useEffect, useMemo, useRef, useState } from 'react';
import { useWindowed } from '../../lib/useWindowed.js';
import { zenoOracleApiUrl, compactId, formatE8, formatTokenE8, formatBpsAsPercent } from '../../lib/oracleUtils.js';
import { EvidenceBadge } from './EvidencePanels.jsx';
import { StatusPill } from './StatusPanels.jsx';

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
          <span role="columnheader">Data quality</span>
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
          <span className="zor-label">Data quality</span>
          <EvidenceBadge value={feed.evidenceClass} />
        </div>
        <div>
          <span className="zor-label">Freshness</span>
          <strong>{feed.freshness ?? <span className="zor-muted">no accepted read</span>}</strong>
        </div>
        <div>
          <span className="zor-label">Price difference</span>
          <strong title={feed.deviationBps !== null && feed.deviationBps !== undefined ? `${feed.deviationBps} bps` : undefined}>
            {formatBpsAsPercent(feed.deviationBps) ?? <span className="zor-muted">—</span>}
          </strong>
        </div>
        <div>
          <span className="zor-label">Reliability</span>
          <strong>{feed.confidence ?? <span className="zor-muted">—</span>}</strong>
        </div>
        <div>
          <span className="zor-label">Usage</span>
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

function FeedCreationPanel() {
  const [assetPair, setAssetPair] = useState('TASSET0/ZDEX');
  const [evidenceFloor, setEvidenceFloor] = useState('O3');
  const [freshness, setFreshness] = useState('2');
  const [reportReward, setReportReward] = useState('1000000');
  const [rewardBudget, setRewardBudget] = useState('100000000');
  const [saveState, setSaveState] = useState('Draft only');
  const policyStatus = evidenceFloor === 'O2' ? 'Test network only' : 'Ready for review';

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
          <span className="label">Minimum quality level</span>
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
          <span className="label">Update frequency</span>
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

export {
  FeedTable,
  FeedStatusPanel,
  FeedCreationPanel,
  FeedDetailInspector,
};
