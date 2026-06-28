// Copyright DarkLightX/Dana Edwards
// Oracle disputes panel.
import { useEffect, useRef, useState } from 'react';
import { zenoOracleApiUrl, compactId, runOracleWriteSmokeFlow } from '../../lib/oracleUtils.js';

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

export {
  DisputesPanel,
};
