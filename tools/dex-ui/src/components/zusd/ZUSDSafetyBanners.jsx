// Copyright DarkLightX/Dana Edwards
// Conditional safety banners: recovery mode, oracle stale, shutdown

export default function ZUSDSafetyBanners({ status = null, onJumpToTab = () => {} }) {
  const banners = [];

  // Recovery mode — computed client-side: TCR < CCR
  const E8 = 100_000_000;
  const branchTcrBps = status?.branch_tcr_bps;
  const ccrBps = status?.core?.ccr_bps;
  if (branchTcrBps != null && ccrBps != null) {
    const tcrPct = Number(branchTcrBps) / 100;
    const ccrPct = Number(ccrBps) / 100;
    if (tcrPct < ccrPct) {
      banners.push(
        <div key="recovery" className="zusd-banner zusd-banner-amber" role="alert">
          ⚠ System in recovery mode (total ratio {tcrPct.toFixed(1)}% &lt; target ratio {ccrPct.toFixed(1)}%).
          Only vaults below {ccrPct.toFixed(0)}% ratio can be liquidated.{' '}
          <a onClick={() => onJumpToTab('keeper')}>Learn more →</a>
        </div>,
      );
    }
  }

  // Oracle stale — oracle_seen === false and status loaded
  if (status?.core && status.core.oracle_seen === false) {
    banners.push(
      <div key="oracle" className="zusd-banner zusd-banner-amber" role="alert">
        ⚠ Price feed may be outdated. The system may reject your transaction.
      </div>,
    );
  }

  // Shutdown settlement — check for shutdown_claim_available flag
  const shutdownOpen = status?.shutdown_claim_available || status?.sp_shutdown_claim_available;
  if (shutdownOpen) {
    banners.push(
      <div key="shutdown" className="zusd-banner zusd-banner-red" role="alert">
        🔴 System shutdown initiated. Payout mode is open.{' '}
        <a onClick={() => onJumpToTab('vault')}>Claim vault collateral →</a>{' '}
        <a onClick={() => onJumpToTab('pool')}>Claim Stability Pool collateral →</a>
      </div>,
    );
  }

  return banners.length > 0 ? <div className="zusd-banners">{banners}</div> : null;
}
