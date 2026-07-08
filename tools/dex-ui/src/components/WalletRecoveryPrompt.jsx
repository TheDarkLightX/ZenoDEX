import './WalletRecoveryPrompt.css';

const RECOVERY_STEPS = [
  {
    label: 'Recovery contacts',
    detail: 'Require more than one trusted approver for account recovery.',
  },
  {
    label: 'Trusted device',
    detail: 'Keep a device-held key or passkey available if the main signer is lost.',
  },
  {
    label: 'Encrypted backup',
    detail: 'Use recovery email, Dropbox, Box, or offline export when providers are configured.',
  },
];

function WalletRecoveryPrompt({ compact = false, onOpenKeys = null, className = '' }) {
  const classes = [
    'wallet-recovery-prompt',
    compact ? 'wallet-recovery-prompt-compact' : '',
    className,
  ].filter(Boolean).join(' ');

  return (
    <section className={classes} aria-label="Wallet recovery setup recommendation">
      <div className="wallet-recovery-copy">
        <div className="wallet-recovery-head">
          <p className="wallet-recovery-kicker">Recovery check</p>
          <span className="wallet-recovery-status">Recommended before deposits</span>
        </div>
        <h2>Protect this wallet</h2>
        <p>
          Add recovery contacts, a trusted device, and an encrypted backup before depositing meaningful funds.
        </p>
      </div>

      <div className="wallet-recovery-steps" aria-label="Recommended recovery layers">
        {RECOVERY_STEPS.map((step) => (
          <div className="wallet-recovery-step" key={step.label}>
            <strong>{step.label}</strong>
            <span>{step.detail}</span>
          </div>
        ))}
      </div>

      <div className="wallet-recovery-actions">
        {onOpenKeys && (
          <button className="btn btn-primary wallet-recovery-cta" type="button" onClick={onOpenKeys}>
            Set up recovery
          </button>
        )}
        <p className="wallet-recovery-boundary">
          Cloud or email access alone cannot move funds.
        </p>
      </div>
    </section>
  );
}

export default WalletRecoveryPrompt;
