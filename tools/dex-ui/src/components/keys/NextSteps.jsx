// Copyright DarkLightX/Dana Edwards
// Recommended next steps — action-oriented panel with locked/conditional states

function StepRow({ number, title, description, actionLabel, actionState, onAction }) {
  const stateCls = actionState === 'locked' ? 'step-locked' : actionState === 'available' ? 'step-available' : 'step-secondary';
  const isLocked = actionState === 'locked';

  return (
    <div className={`next-step-row ${stateCls}`}>
      <div className="next-step-number">{number}</div>
      <div className="next-step-body">
        <div className="next-step-title">{title}</div>
        <div className="next-step-desc">{description}</div>
      </div>
      <button
        className={`btn ${isLocked ? 'btn-disabled' : 'btn-secondary'} btn-sm next-step-action`}
        type="button"
        onClick={isLocked ? undefined : onAction}
        disabled={isLocked}
        aria-label={`${title} — ${isLocked ? 'locked' : actionLabel}`}
      >
        {isLocked ? '🔒 Locked' : actionLabel}
      </button>
    </div>
  );
}

export default function NextSteps({
  recoveryConfigured,
  recoveryTested,
  onSetUpRecovery,
  onTestRecovery,
  onReplaceDevice,
}) {
  return (
    <div className="next-steps-panel" role="region" aria-label="Recommended next steps">
      <h3>Recommended Next Steps</h3>
      <StepRow
        number={1}
        title="Set up recovery backup"
        description={recoveryConfigured ? 'Backup is configured.' : 'Required before recovery can be tested.'}
        actionLabel={recoveryConfigured ? 'Review' : 'Start'}
        actionState={recoveryConfigured ? 'secondary' : 'available'}
        onAction={onSetUpRecovery}
      />
      <StepRow
        number={2}
        title="Test recovery"
        description={recoveryConfigured ? (recoveryTested ? 'Recovery has been tested.' : 'Confirm you can restore access.') : 'Available after backup is configured.'}
        actionLabel="Run test"
        actionState={recoveryConfigured ? 'available' : 'locked'}
        onAction={onTestRecovery}
      />
      <StepRow
        number={3}
        title="Replace a lost device"
        description="Recovery options depend on whether backup is configured."
        actionLabel="Details"
        actionState="secondary"
        onAction={onReplaceDevice}
      />
    </div>
  );
}
