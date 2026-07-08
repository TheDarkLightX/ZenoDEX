// Copyright DarkLightX/Dana Edwards
// Recovery backup, simplified status card. Pipeline details stay in Advanced.

const DEFAULT_STORAGE_OPTIONS = ['Recovery email', 'Dropbox or Box', 'Offline export'];

function providerLabel(providerKind) {
  if (providerKind === 'recovery_email') return 'Recovery email';
  if (providerKind === 'cloud_drive') return 'Dropbox or Box';
  if (providerKind === 'offline_export') return 'Offline export';
  return String(providerKind || '').replaceAll('_', ' ');
}

export default function RecoveryBackup({
  configured,
  threshold,
  shareCount,
  providerKinds,
  onSetUp,
  onLearnMore,
}) {
  const storageOptions = providerKinds && providerKinds.length > 0
    ? providerKinds.map(providerLabel)
    : DEFAULT_STORAGE_OPTIONS;

  return (
    <div className="recovery-backup-panel" role="region" aria-label="Recovery backup">
      <h3>Recovery Backup</h3>
      <div className="recovery-backup-status">
        {configured ? (
          <p className="recovery-backup-configured">
            Backup configured, {threshold} of {shareCount} backup pieces stored in separate places.
          </p>
        ) : (
          <>
            <p className="recovery-backup-not-configured">Not configured</p>
            <p className="recovery-backup-recommendation">
              Recommended: {threshold || 3} of {shareCount || 5} backup pieces stored in separate places.
            </p>
          </>
        )}
      </div>
      <div className="recovery-backup-providers" aria-label={configured ? 'Configured backup storage' : 'Available backup storage options'}>
        {storageOptions.map((provider) => (
          <span key={provider} className="recovery-provider-chip">{provider}</span>
        ))}
      </div>
      <p className="recovery-backup-boundary">
        Each location stores encrypted backup material only. Email or cloud access alone cannot move funds.
      </p>
      <div className="recovery-backup-actions">
        <button className="btn btn-secondary recovery-backup-cta" type="button" onClick={onSetUp}>
          {configured ? 'Review Backup' : 'Set Up Recovery Backup'}
        </button>
        <button className="btn btn-ghost btn-sm" type="button" onClick={onLearnMore}>
          Learn what this means
        </button>
      </div>
    </div>
  );
}
