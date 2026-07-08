// Copyright DarkLightX/Dana Edwards
// Safety verdict banner — answers "Are my keys safe? Do I need to do anything?"

export default function SafetyVerdict({
  isTestnet,
  recoveryConfigured,
  recoveryTested,
  activeKeysCount,
  signatureThreshold,
  lastChecked,
  authLoading,
  onSetUpRecovery,
}) {
  const needsRecovery = !recoveryConfigured;
  const allClear = recoveryConfigured && recoveryTested;

  const verdict = allClear ? 'safe' : needsRecovery ? 'needs-setup' : 'needs-test';
  const verdictCls = `safety-verdict-${verdict}`;

  const headline = allClear
    ? 'Recovery backup verified'
    : needsRecovery
      ? 'Recovery not set up'
      : 'Recovery backup set up, not tested';

  const explanation = allClear
    ? 'Your wallet has a recovery backup and it has been tested. You can regain access if a trusted device is lost.'
    : needsRecovery
      ? `This wallet requires ${signatureThreshold} of ${activeKeysCount} trusted devices to sign. If either device is lost, you may be unable to access this wallet until recovery is configured.`
      : 'Your recovery backup is configured but has not been tested. Run a recovery test to confirm you can restore access.';

  const ctaLabel = allClear
    ? 'Review Recovery'
    : needsRecovery
      ? 'Set Up Recovery Backup'
      : 'Test Recovery';

  return (
    <div className={`safety-verdict-banner ${verdictCls}`} role="alert" aria-live="polite">
      <div className="safety-verdict-headline">
        {isTestnet && <span className="safety-testnet-badge">Testnet only: no real funds at risk</span>}
        <span className="safety-verdict-status">{authLoading ? 'Checking…' : headline}</span>
      </div>
      <p className="safety-verdict-explanation">{authLoading ? 'Loading wallet status…' : explanation}</p>
      <div className="safety-verdict-actions">
        <button className="btn btn-primary safety-cta" type="button" onClick={onSetUpRecovery} disabled={authLoading}>
          {ctaLabel}
        </button>
        <span className="safety-last-checked">
          {authLoading ? 'Checking…' : `Configuration checked ${lastChecked || 'recently'}`}
        </span>
      </div>
    </div>
  );
}
