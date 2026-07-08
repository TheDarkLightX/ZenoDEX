// Copyright DarkLightX/Dana Edwards
// System status bar — API, wallet, automation, risk, env, emergency stop

import { useEffect, useState } from 'react';
import { apiGetAutotraderStatus } from '../../lib/api.js';

export default function StrategyStatusBar({ onPauseAll, activeCount }) {
  const [status, setStatus] = useState(null);
  const [apiOnline, setApiOnline] = useState(true);

  useEffect(() => {
    let cancelled = false;
    async function fetchStatus() {
      try {
        const payload = await apiGetAutotraderStatus({ timeoutMs: 5000 });
        if (cancelled) return;
        setStatus(payload?.status || null);
        setApiOnline(true);
      } catch {
        if (cancelled) return;
        setApiOnline(false);
      }
    }
    fetchStatus();
    const interval = setInterval(fetchStatus, 15000);
    return () => { cancelled = true; clearInterval(interval); };
  }, []);

  const automationEnabled = status?.automation_enabled !== false;
  const walletLabel = status?.wallet_label || 'test-key';
  const envLabel = status?.env || 'local-testnet';

  return (
    <div className="strategy-system-bar">
      <div className="strategy-system-row">
        <span className={`strategy-system-dot ${apiOnline ? 'online' : 'offline'}`} aria-hidden="true"></span>
        <span className="strategy-system-meta">
          {apiOnline ? 'API online' : 'API offline'}
          {' | Wallet: '}{walletLabel}
          {' | Automation: '}{automationEnabled ? 'enabled' : 'disabled'}
          {activeCount != null && ` | Active: ${activeCount}`}
        </span>
        <button
          className="strategy-pause-all-btn"
          type="button"
          onClick={onPauseAll}
          disabled={!apiOnline || !automationEnabled || activeCount === 0}
          title="Pause all running strategies"
        >
          ⏸ Pause all
        </button>
      </div>
      <div className="strategy-risk-notice">
        ⚠ Experimental. Unattended transactions may fail.
        Never enable with funds you can't afford to lose.
      </div>
      <div className="strategy-env-notice">
        Env: {envLabel} (no real value at risk)
      </div>
    </div>
  );
}
