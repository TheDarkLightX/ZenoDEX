// Copyright DarkLightX/Dana Edwards
// Oracle authority profile and authority exercise panels.
import { compactId } from '../../lib/oracleUtils.js';

function AuthorityProfilePanel({ authorityStatus }) {
  const status = authorityStatus || {};
  const keyRefs = Array.isArray(status.key_refs) ? status.key_refs : [];
  const activeSigners = Array.isArray(status.active_signers) ? status.active_signers : [];
  const signerByKey = new Map(activeSigners.map((signer) => [signer.key_id, signer]));
  const gaps = Array.isArray(status.readiness_gaps) ? status.readiness_gaps : [];
  const walletUx = status.wallet_ux || {};
  const proofProfile = status.proof_profile || {};
  const signatureQuorum = status.signature_quorum || {};
  const signedWeight = signatureQuorum.accepted_weight || 0;
  const signedThreshold = signatureQuorum.threshold || status.threshold || 0;
  const controls = [
    ['External signer', walletUx.external_signer_required],
    ['Key manager', walletUx.key_manager_required],
    ['Device approval', walletUx.device_approval_required],
    ['Proof required', proofProfile.zk_or_proof_required],
    ['Receipt replay', proofProfile.oracle_receipt_replay_required],
    ['Signed quorum', signedThreshold > 0 && signedWeight >= signedThreshold],
  ];
  const ready = status.production_authority === true;

  return (
    <section className="panel zor-panel zor-authority-panel">
      <div className="zor-section-header">
        <div>
          <h2>Authority Profile</h2>
          <p>Public key-manager, signer quorum, wallet approval, and proof posture.</p>
        </div>
        <span className={`zor-authority-chip ${ready ? 'zor-authority-ready' : 'zor-authority-blocked'}`}>
          {ready ? 'Production authority ready' : 'Authority blocked'}
        </span>
      </div>
      <div className="zor-authority-summary">
        <div>
          <small>Authority</small>
          <strong>{status.authority_id || 'missing profile'}</strong>
        </div>
        <div>
          <small>Chain</small>
          <strong>{status.chain_id || 'unbound'}</strong>
        </div>
        <div>
          <small>Signer quorum</small>
          <strong>{status.active_signer_count || 0}/{status.threshold || 0}</strong>
        </div>
        <div>
          <small>Signed quorum</small>
          <strong>{signedWeight}/{signedThreshold}</strong>
        </div>
        <div>
          <small>Key refs</small>
          <strong>{status.key_ref_count || keyRefs.length}</strong>
        </div>
        <div>
          <small>Runtime proof</small>
          <strong>{proofProfile.runtime_proof_profile || 'missing'}</strong>
        </div>
        <div>
          <small>Authority hash</small>
          <strong>{compactId(status.authority_hash)}</strong>
        </div>
      </div>
      <div className="zor-authority-controls">
        {controls.map(([label, ok]) => (
          <span key={label} className={ok ? 'zor-control-ok' : 'zor-control-missing'}>
            {label}
          </span>
        ))}
      </div>
      <div className="zor-key-manager-table">
        <div className="zor-key-manager-head">
          <span>Key Manager</span>
          <span>Status</span>
          <span>Signer</span>
          <span>Public key</span>
        </div>
        {keyRefs.length ? (
          keyRefs.map((keyRef) => {
            const signer = signerByKey.get(keyRef.key_id);
            return (
              <div key={keyRef.key_id} className="zor-key-manager-row">
                <span>
                  <strong>{keyRef.key_id}</strong>
                  <small>{keyRef.origin || 'unknown origin'}</small>
                </span>
                <span className={keyRef.status === 'active' ? 'zor-status zor-reporter-active' : 'zor-status zor-stale'}>
                  {keyRef.status || 'unknown'}
                </span>
                <span>{signer ? `${signer.signer_id} / weight ${signer.weight}` : 'unmapped'}</span>
                <span>{compactId(keyRef.public_key)}</span>
              </div>
            );
          })
        ) : (
          <div className="zor-empty-state">No key-manager refs loaded</div>
        )}
      </div>
      {gaps.length ? (
        <div className="zor-authority-gaps">
          {gaps.slice(0, 5).map((gap) => (
            <span key={gap}>{gap}</span>
          ))}
        </div>
      ) : null}
    </section>
  );
}

function AuthorityExercisePanel({
  authorityStatus,
  authorityExerciseResult,
  authorityExerciseState,
  authorityExerciseBusy,
  onRunAuthorityExercise,
}) {
  const exerciseStatus = authorityExerciseResult?.authority_exercise_status || null;
  const targetNetwork = exerciseStatus?.target_network || 'local';
  const publicEvidence = exerciseStatus?.public_testnet_evidence_present === true;
  const errors = Array.isArray(exerciseStatus?.errors) ? exerciseStatus.errors : [];

  return (
    <section className="panel zor-panel zor-authority-panel">
      <div className="zor-section-header">
        <div>
          <h2>Authority Exercise</h2>
          <p>Run a bounded signed authority exercise over a real local operator flow and bind the receipt IDs.</p>
        </div>
        <span className={`zor-authority-chip ${exerciseStatus?.ok ? 'zor-authority-ready' : 'zor-authority-blocked'}`}>
          {exerciseStatus?.ok ? 'Exercise ready' : 'Exercise pending'}
        </span>
      </div>
      <div className="zor-authority-summary">
        <div>
          <small>Target network</small>
          <strong>{targetNetwork}</strong>
        </div>
        <div>
          <small>Authority profile</small>
          <strong>{authorityStatus?.production_authority ? 'ready' : 'blocked'}</strong>
        </div>
        <div>
          <small>Public testnet evidence</small>
          <strong>{publicEvidence ? 'present' : 'pending'}</strong>
        </div>
        <div>
          <small>Exercise hash</small>
          <strong>{compactId(exerciseStatus?.exercise_hash)}</strong>
        </div>
        <div>
          <small>Status hash</small>
          <strong>{compactId(exerciseStatus?.status_hash)}</strong>
        </div>
        <div>
          <small>Receipt binding</small>
          <strong>{compactId(exerciseStatus?.receipt_binding_hash)}</strong>
        </div>
        <div>
          <small>Public evidence binding</small>
          <strong>{compactId(exerciseStatus?.public_testnet_evidence_binding_hash)}</strong>
        </div>
        <div>
          <small>Public broadcast</small>
          <strong>{compactId(exerciseStatus?.public_broadcast_reference)}</strong>
        </div>
        <div>
          <small>Public settlement</small>
          <strong>{compactId(exerciseStatus?.public_settlement_reference)}</strong>
        </div>
        <div>
          <small>Broadcast height</small>
          <strong>{exerciseStatus?.public_broadcast_height ?? 'none'}</strong>
        </div>
        <div>
          <small>Settlement height</small>
          <strong>{exerciseStatus?.public_settlement_height ?? 'none'}</strong>
        </div>
        <div>
          <small>Authorization</small>
          <strong>{compactId(exerciseStatus?.authorization_id)}</strong>
        </div>
      </div>
      <div className="zor-authority-controls">
        <span className={exerciseStatus?.authority_exercised ? 'zor-control-ok' : 'zor-control-missing'}>
          Authority exercised
        </span>
        <span className={publicEvidence ? 'zor-control-ok' : 'zor-control-missing'}>
          Public testnet evidence
        </span>
      </div>
      <div className="zor-toolbar">
        <button className="btn btn-secondary" type="button" onClick={onRunAuthorityExercise} disabled={authorityExerciseBusy}>
          {authorityExerciseBusy ? 'Running...' : 'Run Authority Exercise'}
        </button>
        {authorityExerciseState ? <span className="zor-subtle-chip">{authorityExerciseState}</span> : null}
      </div>
      {errors.length ? (
        <div className="zor-authority-gaps">
          {errors.slice(0, 5).map((error) => (
            <span key={error}>{error}</span>
          ))}
        </div>
      ) : null}
    </section>
  );
}

export {
  AuthorityProfilePanel,
  AuthorityExercisePanel,
};
