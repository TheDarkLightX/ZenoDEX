// Copyright DarkLightX/Dana Edwards
// Sticky vault health bar — 6 states:
// disconnected / healthy / stale / warning / liquidatable / error

import { useEffect, useState } from 'react';
import { formatZusdStatusIssue } from './statusCopy.js';

const STALE_THRESHOLD_MS = 60_000;

export default function ZUSDHealthBar({
  status = null,
  statusError = '',
  walletConnected = false,
  lastFetchTs = 0,
  onRefresh = () => {},
  onRetry = () => {},
}) {
  const [now, setNow] = useState(() => Date.now());

  // Re-render every 5s to update the age indicator
  useEffect(() => {
    const timer = window.setInterval(() => setNow(Date.now()), 5000);
    return () => window.clearInterval(timer);
  }, []);

  const ageMs = lastFetchTs ? now - lastFetchTs : 0;
  const ageLabel = lastFetchTs
    ? ageMs < 1000 ? 'now'
      : ageMs < 60_000 ? `${Math.floor(ageMs / 1000)}s ago`
      : `${Math.floor(ageMs / 60_000)}m ago`
    : '';

  const isStale = lastFetchTs > 0 && ageMs > STALE_THRESHOLD_MS;
  const statusIssue = formatZusdStatusIssue(statusError);

  // Derive vault state
  const E8 = 100_000_000;
  const collateralAmt = Number(status?.core?.collateral_e8 ?? 0) / E8;
  const debtAmt = Number(status?.core?.debt_e8 ?? 0) / E8;
  const oraclePrice = status?.core?.price_e8 ? Number(status.core.price_e8) / E8 : 100;
  const collateralValue = collateralAmt * oraclePrice;
  const currentCR = debtAmt > 0 ? (collateralValue / debtAmt) * 100 : Infinity;
  const mcrPct = status?.core?.mcr_bps ? Number(status.core.mcr_bps) / 100 : 110;
  const ccrPct = status?.core?.ccr_bps ? Number(status.core.ccr_bps) / 100 : 150;
  const liquidationPrice = debtAmt > 0 && collateralAmt > 0
    ? (debtAmt * (mcrPct / 100)) / collateralAmt
    : 0;

  // Determine state
  let stateKey = 'disconnected';
  let stateLabel = 'Connect wallet';
  if (!walletConnected) {
    stateKey = 'disconnected';
    stateLabel = 'Connect wallet';
  } else if (statusError) {
    stateKey = 'error';
    stateLabel = 'Local testnet unavailable';
  } else if (isStale && debtAmt > 0) {
    stateKey = 'stale';
    stateLabel = 'Outdated';
  } else if (debtAmt > 0 && currentCR < mcrPct) {
    stateKey = 'danger';
    stateLabel = 'At risk';
  } else if (debtAmt > 0 && currentCR < ccrPct) {
    stateKey = 'warning';
    stateLabel = 'Low buffer';
  } else if (debtAmt > 0) {
    stateKey = 'safe';
    stateLabel = 'Safe';
  } else if (status) {
    stateKey = 'safe';
    stateLabel = 'No debt';
  }

  const num = (v, d = 2) => (Number.isFinite(v) ? v.toLocaleString(undefined, { maximumFractionDigits: d }) : '—');

  return (
    <div className="zusd-health-bar" role="status" aria-live="polite">
      <div className="zusd-health-row">
        <span className={`zusd-health-dot ${stateKey}`} aria-hidden="true"></span>
        <span className={`zusd-health-label ${stateKey}`}>{stateLabel}</span>

        {stateKey === 'error' ? (
          <>
            <span className="zusd-health-meta">{statusIssue}</span>
            <button className="zusd-health-action" type="button" onClick={onRetry}>
              Retry
            </button>
          </>
        ) : stateKey === 'disconnected' ? (
          <span className="zusd-health-meta">Connect wallet to view your vault</span>
        ) : (
          <>
            {debtAmt > 0 && Number.isFinite(currentCR) && (
              <span className="zusd-health-meta">
                Ratio: {num(currentCR, 1)}%
                {isStale && <span className="zusd-health-stale"> ⚠ outdated ({Math.floor(ageMs / 1000)}s)</span>}
              </span>
            )}
            {liquidationPrice > 0 && (
              <span className="zusd-health-meta">Liquidation: ${num(liquidationPrice)}</span>
            )}
            {debtAmt > 0 && (
              <span className="zusd-health-meta">Debt: {num(debtAmt)} zUSD</span>
            )}
            {ageLabel && <span className="zusd-health-age">{ageLabel}</span>}
            <button className="zusd-health-action" type="button" onClick={onRefresh} aria-label="Refresh status">
              ↻
            </button>
          </>
        )}
      </div>
    </div>
  );
}
