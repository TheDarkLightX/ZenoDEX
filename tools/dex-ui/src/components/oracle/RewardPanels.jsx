// Copyright DarkLightX/Dana Edwards
// Oracle rewards, source diversity, authorization trail, and consumer profile panels.
import { useEffect, useMemo, useRef, useState } from 'react';
import { zenoOracleApiUrl, compactId, formatTokenE8, runOracleWriteSmokeFlow } from '../../lib/oracleUtils.js';
import { ORACLE_CONSUMER_PROFILES } from '../ZenoOracleDashboardData.js';
import { EvidenceBadge } from './EvidencePanels.jsx';
import { StatusPill } from './StatusPanels.jsx';

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

export {
  RewardsPanel,
  SourceDiversityPanel,
  AuthorizationTrailPanel,
  ConsumerProfilePanel,
};
