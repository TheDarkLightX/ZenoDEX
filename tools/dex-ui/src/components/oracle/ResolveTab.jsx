// Copyright DarkLightX/Dana Edwards
// Resolve tab — active disputes (per-dispute resolve, no batch) +
// receipt builder (warns if disputed read) + receipt history + quick verify.

import { useState } from 'react';
import { DisputesPanel } from './DisputePanels.jsx';
import { ReceiptBuilderPanel, VerifyPanel, EvidencePanel } from './EvidencePanels.jsx';
import { AuthorizationTrailPanel } from './RewardPanels.jsx';

export default function ResolveTab({
  disputes = [],
  selectedFeed = null,
  verifyReceiptId = '',
  authorizationTrail = [],
  remoteData = null,
  demoMode = false,
}) {
  const [expandedDispute, setExpandedDispute] = useState(null);

  const openDisputes = disputes.filter((d) => d.status === 'open');

  return (
    <div className="oracle-tab-panel">
      {/* Active disputes — per-dispute resolve, NO "Resolve all" */}
      <div className="oracle-resolve-section">
        <div className="oracle-resolve-header">
          <span className="oracle-resolve-title">Flagged Reports</span>
          <span className="oracle-resolve-count">{openDisputes.length} open</span>
        </div>
        {openDisputes.length === 0 ? (
          <div className="oracle-empty">No active disputes</div>
        ) : (
          <div className="oracle-feed-table">
            <div className="oracle-feed-table-head" style={{ gridTemplateColumns: '1.5fr 1fr 1fr 0.8fr 0.8fr' }}>
              <span>Feed</span>
              <span>Value</span>
              <span>Flagged by</span>
              <span>Age</span>
              <span>Action</span>
            </div>
            {openDisputes.map((dispute) => (
              <div key={dispute.id || dispute.feed}>
                <div
                  className="oracle-feed-row"
                  style={{ gridTemplateColumns: '1.5fr 1fr 1fr 0.8fr 0.8fr' }}
                  onClick={() => setExpandedDispute(expandedDispute === dispute.id ? null : dispute.id)}
                  role="row"
                  tabIndex={0}
                  onKeyDown={(e) => { if (e.key === 'Enter') setExpandedDispute(expandedDispute === dispute.id ? null : dispute.id); }}
                >
                  <span>{dispute.feed || dispute.target || '—'}</span>
                  <span>{dispute.value || '—'}</span>
                  <span style={{ opacity: 0.6 }}>{dispute.reporter || dispute.disputedBy || '—'}</span>
                  <span style={{ opacity: 0.5 }}>{dispute.age || '—'}</span>
                  <span>
                    <button className="oracle-feed-detail-btn" type="button" style={{ padding: '2px 8px', fontSize: '0.78em' }}>
                      Review →
                    </button>
                  </span>
                </div>
                {expandedDispute === dispute.id && (
                  <div style={{ padding: '12px', background: 'rgba(255,255,255,0.02)', borderBottom: '1px solid rgba(255,255,255,0.04)' }}>
                    <div style={{ fontSize: '0.78em', opacity: 0.6, marginBottom: 8 }}>
                      Submitted: {dispute.value || '—'} | Sources: {dispute.sources || '—'}
                    </div>
                    <div style={{ display: 'flex', gap: 8 }}>
                      <button className="btn btn-secondary" type="button" style={{ fontSize: '0.8em' }}>Accept</button>
                      <button className="btn btn-secondary" type="button" style={{ fontSize: '0.8em' }}>Reject</button>
                      <button className="btn btn-secondary" type="button" style={{ fontSize: '0.8em' }}>Request more data</button>
                    </div>
                  </div>
                )}
              </div>
            ))}
          </div>
        )}
      </div>

      {/* Dispute form (open/resolve) */}
      <div className="oracle-resolve-section">
        <DisputesPanel disputes={disputes} />
      </div>

      {/* Receipt builder — warns if selected read is disputed */}
      <div className="oracle-resolve-section">
        <div className="oracle-resolve-header">
          <span className="oracle-resolve-title">Record Builder</span>
        </div>
        {selectedFeed && openDisputes.some((d) => d.feed === selectedFeed.feed) && (
          <div style={{
            fontSize: '0.75em',
            padding: '6px 10px',
            borderRadius: 6,
            background: 'rgba(250,204,21,0.08)',
            color: '#facc15',
            marginBottom: 8,
          }}>
            ⚠ The latest read for {selectedFeed.feed} is disputed. Building a receipt for it will record the contested value.
          </div>
        )}
        <ReceiptBuilderPanel feed={selectedFeed} />
      </div>

      {/* Receipt history */}
      <div className="oracle-resolve-section">
        <div className="oracle-resolve-header">
          <span className="oracle-resolve-title">Record History</span>
          <span className="oracle-resolve-count">{authorizationTrail.length} entries</span>
        </div>
        <AuthorizationTrailPanel items={authorizationTrail} />
      </div>

      {/* Evidence distribution */}
      <div className="oracle-resolve-section">
        <EvidencePanel
          summary={remoteData?.summary}
          reads={remoteData?.acceptedReads}
          demoMode={demoMode}
        />
      </div>

      {/* Quick verify */}
      <div className="oracle-resolve-section">
        <div className="oracle-resolve-header">
          <span className="oracle-resolve-title">Quick Verify</span>
        </div>
        <VerifyPanel
          key={verifyReceiptId || 'verify'}
          initialReceiptId={verifyReceiptId}
        />
      </div>
    </div>
  );
}
