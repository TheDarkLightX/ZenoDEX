// Copyright DarkLightX/Dana Edwards
// Oracle evidence, verify, latest-read, and receipt-builder panels.
import { useState } from 'react';
import { zenoOracleApiUrl, compactId, formatBpsAsPercent, randomSmokeHex, smokeHash } from '../../lib/oracleUtils.js';
import { ORACLE_EVIDENCE_DISTRIBUTION } from '../ZenoOracleDashboardData.js';

function EvidenceBadge({ value }) {
  // Unknown/unreported evidence renders as a neutral "—" rather than being
  // silently upgraded to a graded class (which would overstate the floor).
  if (!value) return <span className="zor-evidence zor-evidence-unknown" title="Evidence class not reported">—</span>;
  return <span className={`zor-evidence zor-evidence-${value}`}>{value}</span>;
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

export {
  EvidenceBadge,
  LatestRead,
  VerifyPanel,
  ReceiptBuilderPanel,
  EvidencePanel,
};
