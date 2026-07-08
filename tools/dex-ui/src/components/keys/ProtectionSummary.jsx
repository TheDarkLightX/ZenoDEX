// Copyright DarkLightX/Dana Edwards
// Protection summary — compact status panel showing key counts, threshold, backup state

function SummaryRow({ label, value, warn, authLoading }) {
  return (
    <div className={`prot-summary-row ${warn ? 'prot-summary-warn' : ''}`}>
      <span className="prot-summary-label">{label}</span>
      <span className="prot-summary-value">{authLoading ? '…' : value}</span>
    </div>
  );
}

export default function ProtectionSummary({
  trustedDevicesCount,
  requiredToSign,
  recoveryBackupStatus,
  lastRecoveryTest,
  authLoading,
}) {
  const noSafetyNet = recoveryBackupStatus === 'not-set-up';

  return (
    <div className="protection-summary-panel" role="region" aria-label="Protection summary">
      <h3>Protection Summary</h3>
      <SummaryRow label="Trusted devices" value={trustedDevicesCount} authLoading={authLoading} />
      <SummaryRow label="Devices needed to approve" value={`${requiredToSign} of ${trustedDevicesCount}`} authLoading={authLoading} />
      <SummaryRow
        label="Recovery backup"
        value={recoveryBackupStatus === 'not-set-up' ? 'Not set up' : recoveryBackupStatus === 'configured' ? 'Configured' : 'Verified'}
        warn={noSafetyNet}
        authLoading={authLoading}
      />
      <SummaryRow label="Last recovery test" value={lastRecoveryTest || 'Never'} warn={lastRecoveryTest === 'Never'} authLoading={authLoading} />
      {noSafetyNet && (
        <div className="prot-summary-risk">
          <strong>No recovery safety net</strong>
          <p>Losing either trusted device can block access.</p>
        </div>
      )}
    </div>
  );
}
