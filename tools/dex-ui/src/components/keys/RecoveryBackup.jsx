// Copyright DarkLightX/Dana Edwards
// Recovery Backup — simplified status card. Pipeline details in Advanced.

export default function RecoveryBackup({
  configured,
  threshold,
  shareCount,
  providerKinds,
  onSetUp,
  onLearnMore,
}) {
  return (
    <div className="recovery-backup-panel" role="region" aria-label="Recovery backup">
      <h3>Recovery Backup</h3>
      <div className="recovery-backup-status">
        {configured ? (
          <p className="recovery-backup-configured">
            Backup configured — {threshold} of {shareCount} backup pieces stored in separate places.
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
      <div className="recovery-backup-actions">
        <button className="btn btn-secondary recovery-backup-cta" type="button" onClick={onSetUp}>
          {configured ? 'Review Backup' : 'Set Up Recovery Backup'}
        </button>
        <button className="btn btn-ghost btn-sm" type="button" onClick={onLearnMore}>
          Learn what this means
        </button>
      </div>
      {configured && providerKinds && providerKinds.length > 0 && (
        <div className="recovery-backup-providers">
          {providerKinds.map((p) => (
            <span key={p} className="recovery-provider-chip">{p}</span>
          ))}
        </div>
      )}
    </div>
  );
}
