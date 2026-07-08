import { useEffect, useMemo, useState, useRef } from 'react';
import SafetyVerdict from './keys/SafetyVerdict.jsx';
import ProtectionSummary from './keys/ProtectionSummary.jsx';
import NextSteps from './keys/NextSteps.jsx';
import TrustedDevices from './keys/TrustedDevices.jsx';
import RecoveryBackup from './keys/RecoveryBackup.jsx';
import './keys/KeysSection.css';
import {
  apiGetPerpsWalletStatus,
  apiEvaluatePerpsRecovery,
  apiEvaluatePerpsRotation,
  apiEvaluatePerpsDeviceApproval,
  apiEvaluatePerpsSignerDevice,
  apiEvaluatePerpsSignerPromptCapture,
  apiEvaluatePerpsSignerExecution,
  apiEvaluatePerpsSignerCeremony,
  apiEvaluatePerpsHardwareCustody,
  apiEvaluatePerpsEncryptedSssBackup,
  apiDeliverPerpsEncryptedSssBackup,
  getRuntimeConfig,
} from '../lib/api.js';
import './PerpsGovernanceSurface.css';

function redactSensitive(obj) {
  if (!obj || typeof obj !== 'object') {
    return obj;
  }
  if (Array.isArray(obj)) {
    return obj.map(redactSensitive);
  }
  const redacted = {};
  for (const [key, val] of Object.entries(obj)) {
    if (
      key.toLowerCase().includes('key') ||
      key.toLowerCase().includes('hash') ||
      key.toLowerCase().includes('signature') ||
      key.toLowerCase().includes('secret') ||
      key.toLowerCase().includes('proof') ||
      key.toLowerCase().includes('token')
    ) {
      if (typeof val === 'string') {
        redacted[key] = val.length > 12 ? `${val.slice(0, 6)}...[REDACTED]...${val.slice(-6)}` : '[REDACTED]';
      } else {
        redacted[key] = '[REDACTED]';
      }
    } else {
      redacted[key] = redactSensitive(val);
    }
  }
  return redacted;
}

function compactId(value) {
  if (!value) return 'N/A';
  const text = String(value);
  if (text.length <= 18) return text;
  return `${text.slice(0, 10)}...${text.slice(-6)}`;
}

export default function PerpsGovernanceSurface() {
  const [status, setStatus] = useState(null);
  const [loading, setLoading] = useState(true);
  const [error, setError] = useState(null);
  const [evaluating, setEvaluating] = useState({});
  const [evalError, setEvalError] = useState('');
  const [smokeStatus, setSmokeStatus] = useState('');
  const [deliveredSssStatus, setDeliveredSssStatus] = useState(null);
  const [deliveredSssBackup, setDeliveredSssBackup] = useState(null);

  // Intuitive enhancements state
  const [showRaw, setShowRaw] = useState(false);
  const [expandedFixture, setExpandedFixture] = useState(null);
  const [activeForm, setActiveForm] = useState(null); // 'deviceApproval' | 'signerDevice' | 'recovery' | 'rotation'

  // Device Enrollment Form State (Step 1 & 2)
  const [deviceKeyId, setDeviceKeyId] = useState('perps-wallet-a');
  const [deviceLabel, setDeviceLabel] = useState('Local-Testnet Hardware Wallet A');
  const [deviceMode, setDeviceMode] = useState('hardware_key');
  const [userPresence, setUserPresence] = useState(true);
  const [rollbackProtection, setRollbackProtection] = useState(true);
  const [deviceNonce, setDeviceNonce] = useState(14);
  const [devicePcr0, setDevicePcr0] = useState('');

  // Key Management Form State (Step 3)
  const [subjectKeyId, setSubjectKeyId] = useState('perps-wallet-a');
  const [policyId, setPolicyId] = useState('recovery-perps-wallet-a');
  const [requestedEpoch, setRequestedEpoch] = useState(10);
  const [currentEpoch, setCurrentEpoch] = useState(13);
  const [guardianList, setGuardianList] = useState('guardian-a, guardian-b');
  const [sigEnvelopesJson, setSigEnvelopesJson] = useState('');

  // Key Rotation Form State (Step 4)
  const [rotatedKeyId, setRotatedKeyId] = useState('perps-wallet-a');
  const [replacementKeyId, setReplacementKeyId] = useState('perps-wallet-c');
  const [rotationPolicyId, setRotationPolicyId] = useState('recovery-perps-wallet-a');
  const [broadcastEpoch, setBroadcastEpoch] = useState(13);
  const [rotationGuardianList, setRotationGuardianList] = useState('guardian-a, guardian-b');
  const [rotationSigEnvelopesJson, setRotationSigEnvelopesJson] = useState('');
  const [nextProfileJson, setNextProfileJson] = useState('');

  const smokeRan = useRef(false);

  const runtimeConfig = getRuntimeConfig();
  const fixtures = useMemo(
    () => runtimeConfig.localTestnetGovernanceFixtures || {},
    [runtimeConfig.localTestnetGovernanceFixtures],
  );
  const fixturePreview = expandedFixture
    ? (fixtures[`${expandedFixture}Exercise`] || fixtures[expandedFixture])
    : null;
  const zkPosture = runtimeConfig.localTestnetZkPosture || {};

  async function loadStatus() {
    try {
      const res = await apiGetPerpsWalletStatus({ timeoutMs: 8000 });
      if (res && res.ok && res.status) {
        setStatus(res.status);
        setError(null);
      } else {
        setStatus(null);
        setError(res?.error || 'No status returned from backend');
      }
    } catch (err) {
      setStatus(null);
      setError(err?.message || 'Failed to fetch status');
    } finally {
      setLoading(false);
    }
  }

  useEffect(() => {
    loadStatus();
  }, []);

  // Sync Form state with fixtures once loaded
  useEffect(() => {
    if (fixtures.deviceApprovalExercise) {
      const dev = fixtures.deviceApprovalExercise;
      if (dev.key_id) setDeviceKeyId(dev.key_id);
      if (dev.environment) {
        if (dev.environment.environment_kind) setDeviceMode(dev.environment.environment_kind);
        if (dev.environment.rollback_protection_confirmed !== undefined) setRollbackProtection(dev.environment.rollback_protection_confirmed);
        if (dev.environment.local_user_presence_confirmed !== undefined) setUserPresence(dev.environment.local_user_presence_confirmed);
        if (dev.environment.pcr0) setDevicePcr0(dev.environment.pcr0);
      }
      if (dev.payload && dev.payload.nonce !== undefined) {
        setDeviceNonce(dev.payload.nonce);
      }
    }
    if (fixtures.signerDeviceIntegration) {
      const sig = fixtures.signerDeviceIntegration;
      if (sig.device_label) setDeviceLabel(sig.device_label);
    }
    if (fixtures.recoveryExercise) {
      const rec = fixtures.recoveryExercise;
      if (rec.subject_key_id) setSubjectKeyId(rec.subject_key_id);
      if (rec.policy_id) setPolicyId(rec.policy_id);
      if (rec.requested_at_epoch !== undefined) setRequestedEpoch(rec.requested_at_epoch);
      if (rec.current_epoch !== undefined) setCurrentEpoch(rec.current_epoch);
      if (rec.approvals) setGuardianList(rec.approvals.join(', '));
      if (rec.signature_envelopes) setSigEnvelopesJson(JSON.stringify(rec.signature_envelopes, null, 2));
    }
    if (fixtures.rotationExercise) {
      const rot = fixtures.rotationExercise;
      if (rot.rotated_key_id) setRotatedKeyId(rot.rotated_key_id);
      if (rot.replacement_key_id) setReplacementKeyId(rot.replacement_key_id);
      if (rot.policy_id) setRotationPolicyId(rot.policy_id);
      if (rot.broadcast_at_epoch !== undefined) setBroadcastEpoch(rot.broadcast_at_epoch);
      if (rot.approvals) setRotationGuardianList(rot.approvals.join(', '));
      if (rot.signature_envelopes) setRotationSigEnvelopesJson(JSON.stringify(rot.signature_envelopes, null, 2));
      if (rot.next_wallet_authority_profile) setNextProfileJson(JSON.stringify(rot.next_wallet_authority_profile, null, 2));
    }
  }, [fixtures]);

  // Smoke Mode triggers
  useEffect(() => {
    if (typeof window === 'undefined') return;
    const params = new URLSearchParams(window.location.search);
    const isSmoke = params.get('zenodexUiSmokeGovernance') === '1';
    const smokeSssDelivery = params.get('zenodexUiSmokeSssDelivery') === '1';
    if (!isSmoke || smokeRan.current) return;

    const runSmoke = async () => {
      smokeRan.current = true;
      setSmokeStatus('evaluating fixtures...');
      try {
        await loadStatus();

        if (fixtures.recoveryExercise) {
          await apiEvaluatePerpsRecovery(fixtures.recoveryExercise);
        }
        if (fixtures.rotationExercise) {
          await apiEvaluatePerpsRotation(fixtures.rotationExercise);
        }
        if (fixtures.deviceApprovalExercise) {
          await apiEvaluatePerpsDeviceApproval(fixtures.deviceApprovalExercise);
        }
        if (fixtures.signerDeviceIntegration) {
          await apiEvaluatePerpsSignerDevice(fixtures.signerDeviceIntegration);
        }
        if (fixtures.signerPromptCapture) {
          await apiEvaluatePerpsSignerPromptCapture(fixtures.signerPromptCapture);
        }
        if (fixtures.signerExecutionExercise) {
          await apiEvaluatePerpsSignerExecution(fixtures.signerExecutionExercise);
        }
        if (fixtures.signerCeremony) {
          await apiEvaluatePerpsSignerCeremony(fixtures.signerCeremony);
        }
        if (fixtures.hardwareCustody) {
          await apiEvaluatePerpsHardwareCustody(fixtures.hardwareCustody);
        }
        if (fixtures.encryptedSssBackup) {
          await apiEvaluatePerpsEncryptedSssBackup(fixtures.encryptedSssBackup);
        }
        if (smokeSssDelivery && fixtures.encryptedSssBackup) {
          try {
            const res = await apiDeliverPerpsEncryptedSssBackup({
              backup: fixtures.encryptedSssBackup,
              chain_id: runtimeConfig.chainId,
            });
            if (res && res.ok && res.encrypted_sss_backup) {
              setDeliveredSssStatus(res.encrypted_sss_backup);
              setDeliveredSssBackup(fixtures.encryptedSssBackup);
            } else {
              setEvalError(res?.error || 'Recovery backup delivery failed');
            }
          } catch (err) {
            setEvalError(err?.message || 'Recovery backup delivery failed');
          }
        }

        await loadStatus();
        setSmokeStatus('smoke mode complete');
      } catch (err) {
        console.error('Smoke evaluation failed', err);
        setSmokeStatus(`smoke mode failed: ${err.message}`);
      }
    };

    void runSmoke();
    // eslint-disable-next-line react-hooks/exhaustive-deps
  }, [fixtures]);

  async function handleEvaluate(key, apiFn, fixture) {
    if (!fixture) return;
    setEvaluating((prev) => ({ ...prev, [key]: true }));
    setEvalError('');
    try {
      const res = await apiFn(fixture);
      if (res && res.ok) {
        await loadStatus();
      } else {
        setEvalError(res?.error || res?.status || `Evaluation of ${key} failed`);
      }
    } catch (err) {
      setEvalError(err?.message || `Failed to evaluate ${key}`);
    } finally {
      setEvaluating((prev) => ({ ...prev, [key]: false }));
    }
  }

  function handleDownloadEncryptedSssBackup() {
    const backup = deliveredSssBackup || fixtures.encryptedSssBackup;
    if (!backup) {
      setEvalError('Encrypted recovery backup is unavailable');
      return;
    }
    const backupId = String(backup.backup_id || 'localtest').replace(/[^a-zA-Z0-9._-]/g, '-');
    const body = JSON.stringify(backup, null, 2);
    const blob = new Blob([body], { type: 'application/json' });
    const url = URL.createObjectURL(blob);
    const link = document.createElement('a');
    link.href = url;
    link.download = `zenodex-encrypted-recovery-backup-${backupId}.json`;
    document.body.appendChild(link);
    link.click();
    link.remove();
    URL.revokeObjectURL(url);
  }

  async function handleDeliverEncryptedSssBackup() {
    const backup = deliveredSssBackup || fixtures.encryptedSssBackup;
    if (!backup) {
      setEvalError('Encrypted recovery backup is unavailable');
      return;
    }
    setEvaluating((prev) => ({ ...prev, encryptedSssDelivery: true }));
    setEvalError('');
    try {
      const res = await apiDeliverPerpsEncryptedSssBackup({ backup, chain_id: runtimeConfig.chainId });
      if (res && res.ok && res.encrypted_sss_backup) {
        setDeliveredSssStatus(res.encrypted_sss_backup);
        setDeliveredSssBackup(backup);
      } else {
        setEvalError(res?.error || 'Recovery backup delivery failed');
      }
    } catch (err) {
      setEvalError(err?.message || 'Recovery backup delivery failed');
    } finally {
      setEvaluating((prev) => ({ ...prev, encryptedSssDelivery: false }));
    }
  }

  const walletAuth = status?.wallet_authority;
  const isAuthReady = walletAuth?.production_wallet_authority === true;
  const recoveryReady = walletAuth?.recovery_exercise?.recovery_exercise_ready === true;
  const rotationReady = walletAuth?.rotation_exercise?.rotation_exercise_ready === true;
  const deviceApprovalReady = walletAuth?.device_approval_exercise?.device_approval_ready === true;
  const signerDeviceReady = walletAuth?.signer_device_integration?.signer_device_ready === true;
  const signerCeremonyReady = walletAuth?.signer_ceremony?.signer_ceremony_ready === true;
  const hardwareCustodyReady = walletAuth?.hardware_custody?.hardware_custody_ready === true;
  const productionHardwareCustodyReady = walletAuth?.hardware_custody?.production_hardware_custody_ready === true;
  const encryptedSssBackup = deliveredSssStatus || walletAuth?.encrypted_sss_backup || null;
  const encryptedSssReady = encryptedSssBackup?.encrypted_sss_backup_ready === true;
  const sssProviderKinds = Array.isArray(encryptedSssBackup?.storage_provider_kinds)
    ? encryptedSssBackup.storage_provider_kinds
    : [];
  const sssProviderIds = Array.isArray(encryptedSssBackup?.storage_provider_ids)
    ? encryptedSssBackup.storage_provider_ids
    : [];
  const sssDeliveryModes = Array.isArray(encryptedSssBackup?.delivery_modes)
    ? encryptedSssBackup.delivery_modes
    : [];
  const sssProviderDeliveryReady = encryptedSssBackup?.provider_delivery_ready === true;
  const sssLiveProviderDeliveryReady = encryptedSssBackup?.live_provider_delivery_ready === true;
  const externalAuditReady = encryptedSssBackup?.external_audit_ready === true;
  const sssHasLiveMode = (mode) => sssDeliveryModes.includes(mode);
  const sssCanSubmitDelivery = Boolean(fixtures.encryptedSssBackup);
  const sssDeliveryActionLabel = 'Deliver';
  const sssDeliveryActionTitle = 'Send this backup to your storage provider and confirm delivery';
  const sssDeliveryConnectors = [
    {
      key: 'recovery-email',
      label: 'Recovery email',
      liveMode: 'smtp',
      configured: sssProviderKinds.includes('recovery_email'),
      ready: sssHasLiveMode('smtp'),
      blockedLabel: 'Connection needed',
      readyLabel: 'Email delivery ready',
      actionAvailable: sssCanSubmitDelivery,
      actionLabel: sssDeliveryActionLabel,
      actionTitle: sssDeliveryActionTitle,
      onClick: () => handleDeliverEncryptedSssBackup(),
    },
    {
      key: 'dropbox',
      label: 'Dropbox',
      liveMode: 'dropbox',
      configured: sssProviderIds.some((providerId) => String(providerId).startsWith('dropbox:')),
      ready: sssHasLiveMode('dropbox'),
      blockedLabel: 'Connection needed',
      readyLabel: 'Dropbox external receipt ready',
      actionAvailable: sssCanSubmitDelivery,
      actionLabel: sssDeliveryActionLabel,
      actionTitle: sssDeliveryActionTitle,
      onClick: () => handleDeliverEncryptedSssBackup(),
    },
    {
      key: 'box',
      label: 'Box',
      liveMode: 'box',
      configured: sssProviderIds.some((providerId) => String(providerId).startsWith('box:')),
      ready: sssHasLiveMode('box'),
      blockedLabel: 'Connection needed',
      readyLabel: 'Box external receipt ready',
      actionAvailable: sssCanSubmitDelivery,
      actionLabel: sssDeliveryActionLabel,
      actionTitle: sssDeliveryActionTitle,
      onClick: () => handleDeliverEncryptedSssBackup(),
    },
    {
      key: 'offline-export',
      label: 'Offline export',
      liveMode: 'offline_export',
      configured: sssProviderKinds.includes('offline_export'),
      ready: sssHasLiveMode('offline_export'),
      blockedLabel: 'Connection needed',
      readyLabel: 'Offline export external receipt ready',
      actionAvailable: sssCanSubmitDelivery,
      actionLabel: sssDeliveryActionLabel,
      actionTitle: sssDeliveryActionTitle,
      onClick: () => handleDeliverEncryptedSssBackup(),
    },
  ];
  const zkEffectiveMode = zkPosture?.zk_mode_effective || 'N/A';
  const zkRequestedMode = zkPosture?.zk_mode_requested || 'N/A';
  const zkStrictReady = zkPosture?.zk_required === true && zkEffectiveMode === 'strict';

  const oracleAuth = status?.oracle_authority || null;
  const oracleAuthStatus = oracleAuth ? oracleAuth.status : 'N/A';

  // The wallet-status fetch takes ~3s. While it is in flight (no status yet)
  // the authority fields must read as LOADING, not fail-closed "N/A" — an empty
  // load is not the same as an unconfigured authority. `authLoading` drives a
  // skeleton/placeholder; genuine absence (loaded but missing) reads as "—".
  const authLoading = loading && !walletAuth;
  const authField = (value) => {
    if (authLoading) return <span className="gov-loading">Loading…</span>;
    return value ?? '—';
  };

  // Calculate signature progress metrics
  const activeKeysCount = walletAuth?.key_ref_count ?? null;
  const signatureThreshold = walletAuth?.threshold ?? null;
  const thresholdKnown = activeKeysCount != null && signatureThreshold != null && signatureThreshold > 0;
  const thresholdPercentage = thresholdKnown
    ? Math.min(100, Math.max(0, (activeKeysCount / signatureThreshold) * 100))
    : 0;

  // Rich governance rosters (node-reported). The panel previously showed only
  // counts; surface the actual signer set, their key refs (algorithm + status),
  // and the recovery policies so this reads as an inspectable governance console.
  const activeSigners = Array.isArray(walletAuth?.active_signers) ? walletAuth.active_signers : [];
  const keyRefs = Array.isArray(walletAuth?.key_refs) ? walletAuth.key_refs : [];
  const keyRefById = new Map(keyRefs.map((k) => [k.key_id, k]));
  const recoveryPolicies = Array.isArray(walletAuth?.recovery_policies) ? walletAuth.recovery_policies : [];
  const shortAlgo = (a) => String(a || '').replace(/-release.*$/, '').replace(/^bls12-381-/, 'BLS ');

  return (
    <section className="perps-governance-surface animate-fade-in" id="perps-governance-surface">
      <div className="gov-hero panel panel-glass">
        <div>
          <h1>Keys &amp; Recovery</h1>
          <p className="gov-subtitle">
            Protect account access, replace lost devices, and test recovery.
          </p>
        </div>
        <div className="gov-hero-meta">
          <span className="gov-chip gov-chip-accent">Testnet only</span>
        </div>
      </div>

      {smokeStatus && (
        <div className="smoke-status-banner panel" id="smoke-status-banner">
          <span className="smoke-status-pulse"></span>
          <span>Smoke mode: <strong>{smokeStatus}</strong></span>
        </div>
      )}

      {evalError && (
        <div className="gov-error-banner panel">
          <strong>Error:</strong> {evalError}
        </div>
      )}
      {error && (
        <div className="gov-error-banner panel">
          <strong>Status:</strong> {error}
        </div>
      )}

      {/* Safety verdict — answers "Are my keys safe? Do I need to do anything?" */}
      <SafetyVerdict
        isTestnet={true}
        recoveryConfigured={encryptedSssReady}
        recoveryTested={encryptedSssBackup?.recovery_drill_ready === true}
        thresholdKnown={thresholdKnown}
        activeKeysCount={activeKeysCount}
        signatureThreshold={signatureThreshold}
        lastChecked={loading ? undefined : 'recently'}
        authLoading={authLoading}
        onSetUpRecovery={() => setActiveForm('recovery')}
      />

      {/* Protection summary + recommended next steps */}
      <div className="keys-two-col">
        <ProtectionSummary
          trustedDevicesCount={activeKeysCount}
          requiredToSign={signatureThreshold}
          recoveryBackupStatus={encryptedSssReady ? 'configured' : 'not-set-up'}
          lastRecoveryTest={encryptedSssBackup?.recovery_drill_ready ? 'tested' : 'Never'}
          authLoading={authLoading}
        />
        <NextSteps
          recoveryConfigured={encryptedSssReady}
          recoveryTested={encryptedSssBackup?.recovery_drill_ready === true}
          onSetUpRecovery={() => setActiveForm('recovery')}
          onTestRecovery={() => handleEvaluate('encryptedSssBackup', apiEvaluatePerpsEncryptedSssBackup, fixtures.encryptedSssBackup)}
          onReplaceDevice={() => setActiveForm('rotation')}
        />
      </div>

      {/* Trusted devices — simplified table, details on click */}
      <TrustedDevices
        activeSigners={activeSigners}
        keyRefs={keyRefs}
        onAddDevice={() => setActiveForm('deviceApproval')}
      />

      {/* Recovery backup — simplified status */}
      <RecoveryBackup
        configured={encryptedSssReady}
        threshold={encryptedSssBackup?.threshold}
        shareCount={encryptedSssBackup?.share_count}
        providerKinds={sssProviderKinds}
        onSetUp={() => setActiveForm('recovery')}
        onLearnMore={() => setExpandedFixture('encryptedSssBackup')}
      />

      {/* Configuration forms — shown when a step is activated */}
      {activeForm && (
      <div className="gov-grid">
          <div className="panel gov-card gov-collapsible-body">
          <div className="gov-section-header">
            <h2>Wallet Authority</h2>
            <span className="gov-section-badge">Core Profile</span>
          </div>

          <div className="gov-status-list">
            <div className="gov-kv">
              <span>Authority Status</span>
              <span
                className={`gov-status-value ${authLoading ? '' : isAuthReady ? 'status-ready' : 'status-blocked'}`}
                id="wallet-authority-status"
              >
                {authLoading ? <span className="gov-loading">Loading…</span> : isAuthReady ? 'Wallet authority ready' : walletAuth?.status || 'Not configured'}
              </span>
            </div>
            <div className="gov-kv">
              <span>Security ID</span>
              <span className="gov-mono">{authLoading ? <span className="gov-loading">Loading…</span> : compactId(walletAuth?.wallet_authority_hash)}</span>
            </div>

            {/* Threshold progress visualizer */}
            <div className="gov-threshold-visualizer">
              <div className="gov-threshold-labels">
                <span>Approval progress</span>
                <span className="gov-mono">{thresholdKnown ? `${activeKeysCount} / ${signatureThreshold} Keys` : authLoading ? 'Loading…' : '— / — Keys'}</span>
              </div>
              <div className="gov-progress-bar-bg">
                <div
                  className={`gov-progress-bar-fill ${!thresholdKnown ? 'fill-pending' : activeKeysCount >= signatureThreshold ? 'fill-ready' : 'fill-pending'}`}
                  style={{ '--threshold-pct': `${thresholdPercentage}%`, width: `${thresholdPercentage}%` }}
                ></div>
              </div>
            </div>

            <div className="gov-kv">
              <span>Recovery Policies</span>
              <span>{authField(walletAuth?.recovery_policy_count)}</span>
            </div>
            <div className="gov-kv">
              <span>Recoverable Active Keys</span>
              <span>{authField(walletAuth?.recoverable_active_key_count)}</span>
            </div>
            <div className="gov-kv">
              <span>Price feed status</span>
              <span className={`gov-status-value ${authLoading ? '' : oracleAuth?.status === 'ready' ? 'status-ready' : ''}`}>
                {authLoading ? <span className="gov-loading">Loading…</span> : oracleAuthStatus}
              </span>
            </div>
            {oracleAuth?.authority_hash && (
              <div className="gov-kv">
                <span>Price feed ID</span>
                <span className="gov-mono">{compactId(oracleAuth.authority_hash)}</span>
              </div>
            )}
          </div>

          {/* Signer roster + recovery policies — the real governance set, not just counts. */}
          {(activeSigners.length > 0 || recoveryPolicies.length > 0) && (
            <details className="gov-roster" open>
              <summary className="gov-roster-summary">
                Trusted devices &amp; recovery rules
                <span className="gov-roster-hint">{activeSigners.length} signer{activeSigners.length === 1 ? '' : 's'} · {recoveryPolicies.length} polic{recoveryPolicies.length === 1 ? 'y' : 'ies'}</span>
              </summary>
              {activeSigners.length > 0 && (
                <div className="gov-roster-block">
                  <div className="gov-roster-title">Authorized devices <span className="gov-mono">({activeKeysCount ?? activeSigners.length}-of-{signatureThreshold ?? '?'})</span></div>
                  <table className="gov-roster-table">
                    <thead><tr><th>Signer</th><th>Key</th><th>Key type</th><th className="num">Power</th><th>Status</th></tr></thead>
                    <tbody>
                      {activeSigners.map((s) => {
                        const ref = keyRefById.get(s.key_id);
                        return (
                          <tr key={s.signer_id || s.key_id}>
                            <td>{s.signer_id || '—'}</td>
                            <td className="gov-mono">{s.key_id}</td>
                            <td>{ref ? shortAlgo(ref.algorithm) : '—'}</td>
                            <td className="num">{s.weight ?? 1}</td>
                            <td><span className={`gov-status-value ${ref?.status === 'active' ? 'status-ready' : ''}`}>{ref?.status || 'unknown'}</span></td>
                          </tr>
                        );
                      })}
                    </tbody>
                  </table>
                </div>
              )}
              {recoveryPolicies.length > 0 && (
                <div className="gov-roster-block">
                  <div className="gov-roster-title">Recovery policies</div>
                  <table className="gov-roster-table">
                    <thead><tr><th>Policy</th><th>Protected key</th><th className="num">Required approvals</th><th className="num">Trusted contacts</th><th className="num">Waiting period</th></tr></thead>
                    <tbody>
                      {recoveryPolicies.map((pol) => (
                        <tr key={pol.policy_id}>
                          <td className="gov-mono">{pol.policy_id}</td>
                          <td className="gov-mono">{pol.subject_key_id}</td>
                          <td className="num">{pol.threshold ?? '—'}</td>
                          <td className="num">{pol.guardian_count ?? '—'}</td>
                          <td className="num">{pol.delay_epochs != null ? `${pol.delay_epochs} periods` : '—'}</td>
                        </tr>
                      ))}
                    </tbody>
                  </table>
                </div>
              )}
            </details>
          )}

          <button className="btn btn-secondary gov-refresh-btn" type="button" onClick={loadStatus} disabled={loading}>
            {loading ? 'Refreshing...' : 'Refresh Status'}
          </button>
          </div>

        {/* Exercises & Evaluations (Sequenced Layout) */}
        <div className="panel gov-card" id="card-exercises">
          <div className="gov-section-header">
            <h2>Configuration Forms</h2>
            <span className="gov-section-badge">Step {activeForm}</span>
          </div>

          <div className="gov-exercise-list sequenced-list">
            {/* Step 1: Device Approval */}
            <div className={`gov-exercise-row step-card ${deviceApprovalReady ? 'step-done' : 'step-next'}`} id="device-approval-row">
              <div className="step-number">1</div>
              <div className="gov-exercise-info">
                <h3>Device Approval</h3>
                <p>Register and authorize physical security environments.</p>
                <div className="gov-status-badges">
                  {deviceApprovalReady ? (
                    <span className="gov-badge-ready" id="device-approval-ready-badge">Device approval ready</span>
                  ) : (
                    <span className="gov-badge-blocked">Device approval blocked</span>
                  )}
                  <span className="env-badge">Security verification required</span>
                </div>
              </div>
              <div className="gov-exercise-action-group">
                <button
                  className="btn btn-ghost btn-xs"
                  type="button"
                  onClick={() => setActiveForm(activeForm === 'deviceApproval' ? null : 'deviceApproval')}
                >
                  {activeForm === 'deviceApproval' ? 'Close Config' : 'Configure Form'}
                </button>
                <button
                  className="btn btn-primary"
                  type="button"
                  onClick={() => handleEvaluate('deviceApproval', apiEvaluatePerpsDeviceApproval, fixtures.deviceApprovalExercise)}
                  disabled={evaluating.deviceApproval || deviceApprovalReady}
                >
                  {evaluating.deviceApproval ? 'Evaluating...' : deviceApprovalReady ? 'Evaluated' : 'Evaluate'}
                </button>
              </div>
            </div>

            {/* Device Approval Inline Form */}
            {activeForm === 'deviceApproval' && (
              <div className="gov-form-panel animate-fade-in">
                <h4>Device approval &amp; verification</h4>
                <div className="gov-form-grid">
                  <label className="label">
                    <span>Device ID</span>
                    <input className="input" value={deviceKeyId} onChange={(e) => setDeviceKeyId(e.target.value)} />
                  </label>
                  <label className="label">
                    <span>Device name</span>
                    <input className="input" value={deviceLabel} onChange={(e) => setDeviceLabel(e.target.value)} />
                  </label>
                </div>
                <div className="gov-form-grid">
                  <label className="label">
                    <span>Device Mode</span>
                    <select className="input" value={deviceMode} onChange={(e) => setDeviceMode(e.target.value)}>
                      <option value="hardware_key">Hardware Key</option>
                      <option value="software_key">Software Key</option>
                      <option value="tee_enclave">TEE Enclave</option>
                    </select>
                  </label>
                  <label className="label">
                    <span>Request ID</span>
                    <input className="input" type="number" value={deviceNonce} onChange={(e) => setDeviceNonce(parseInt(e.target.value, 10) || 0)} />
                  </label>
                </div>
                {deviceMode === 'tee_enclave' && (
                  <label className="label gov-form-label">
                    <span>Hardware fingerprint</span>
                    <input className="input" value={devicePcr0} onChange={(e) => setDevicePcr0(e.target.value)} placeholder="0x..." />
                  </label>
                )}
                <div className="gov-form-row">
                  <label className="gov-checkbox-label">
                    <input type="checkbox" checked={userPresence} onChange={(e) => setUserPresence(e.target.checked)} />
                    <span>Confirm User Presence</span>
                  </label>
                  <label className="gov-checkbox-label">
                    <input type="checkbox" checked={rollbackProtection} onChange={(e) => setRollbackProtection(e.target.checked)} />
                    <span>Anti-rollback protection</span>
                  </label>
                </div>
                <button
                  className="btn btn-primary btn-sm"
                  type="button"
                  onClick={() => {
                    const base = fixtures.deviceApprovalExercise ? JSON.parse(JSON.stringify(fixtures.deviceApprovalExercise)) : {};
                    base.key_id = deviceKeyId;
                    if (!base.environment) base.environment = {};
                    base.environment.environment_kind = deviceMode;
                    base.environment.rollback_protection_confirmed = rollbackProtection;
                    base.environment.local_user_presence_confirmed = userPresence;
                    if (deviceMode === 'tee_enclave') base.environment.pcr0 = devicePcr0;
                    if (!base.payload) base.payload = {};
                    base.payload.nonce = deviceNonce;
                    void handleEvaluate('deviceApproval', apiEvaluatePerpsDeviceApproval, base);
                  }}
                >
                  Submit Device Approval
                </button>
              </div>
            )}

            {/* Step 2: Signer Device Integration */}
            <div className={`gov-exercise-row step-card ${signerDeviceReady ? 'step-done' : 'step-next'}`} id="signer-device-row">
              <div className="step-number">2</div>
              <div className="gov-exercise-info">
                <h3>Device setup</h3>
                <p>Verify device connection, security verification, and physical presence.</p>
                <div className="gov-status-badges">
                  {signerDeviceReady ? (
                    <span className="gov-badge-ready" id="signer-device-ready-badge">Signer device ready</span>
                  ) : (
                    <span className="gov-badge-blocked">Signer device blocked</span>
                  )}
                  <span className="env-badge env-attested">Secure environment</span>
                </div>
              </div>
              <div className="gov-exercise-action-group">
                <button
                  className="btn btn-ghost btn-xs"
                  type="button"
                  onClick={() => setActiveForm(activeForm === 'signerDevice' ? null : 'signerDevice')}
                >
                  {activeForm === 'signerDevice' ? 'Close Config' : 'Configure Form'}
                </button>
                <button
                  className="btn btn-primary"
                  type="button"
                  onClick={() => handleEvaluate('signerDevice', apiEvaluatePerpsSignerDevice, fixtures.signerDeviceIntegration)}
                  disabled={evaluating.signerDevice || signerDeviceReady}
                >
                  {evaluating.signerDevice ? 'Evaluating...' : signerDeviceReady ? 'Evaluated' : 'Evaluate'}
                </button>
              </div>
            </div>

            {/* Signer Device Inline Form */}
            {activeForm === 'signerDevice' && (
              <div className="gov-form-panel animate-fade-in">
                <h4>Device setup</h4>
                <div className="gov-form-grid">
                  <label className="label">
                    <span>Device ID</span>
                    <input className="input" value={deviceKeyId} onChange={(e) => setDeviceKeyId(e.target.value)} />
                  </label>
                  <label className="label">
                    <span>Device name</span>
                    <input className="input" value={deviceLabel} onChange={(e) => setDeviceLabel(e.target.value)} />
                  </label>
                </div>
                <div className="gov-form-grid">
                  <label className="label">
                    <span>Device Mode (Kind)</span>
                    <select className="input" value={deviceMode} onChange={(e) => setDeviceMode(e.target.value)}>
                      <option value="hardware_key">Hardware Key</option>
                      <option value="software_key">Software Key</option>
                      <option value="tee_enclave">TEE Enclave</option>
                    </select>
                  </label>
                  <label className="label">
                    <span>Request ID</span>
                    <input className="input" type="number" value={deviceNonce} onChange={(e) => setDeviceNonce(parseInt(e.target.value, 10) || 0)} />
                  </label>
                </div>
                {deviceMode === 'tee_enclave' && (
                  <label className="label gov-form-label">
                    <span>Hardware fingerprint</span>
                    <input className="input" value={devicePcr0} onChange={(e) => setDevicePcr0(e.target.value)} placeholder="0x..." />
                  </label>
                )}
                <div className="gov-form-row">
                  <label className="gov-checkbox-label">
                    <input type="checkbox" checked={userPresence} onChange={(e) => setUserPresence(e.target.checked)} />
                    <span>Confirm User Presence</span>
                  </label>
                  <label className="gov-checkbox-label">
                    <input type="checkbox" checked={rollbackProtection} onChange={(e) => setRollbackProtection(e.target.checked)} />
                    <span>Anti-rollback protection</span>
                  </label>
                </div>
                <div className="gov-form-row">
                  <button
                    className="btn btn-primary btn-sm"
                    type="button"
                    onClick={() => {
                      const base = fixtures.deviceApprovalExercise ? JSON.parse(JSON.stringify(fixtures.deviceApprovalExercise)) : {};
                      base.key_id = deviceKeyId;
                      if (!base.environment) base.environment = {};
                      base.environment.environment_kind = deviceMode;
                      base.environment.rollback_protection_confirmed = rollbackProtection;
                      base.environment.local_user_presence_confirmed = userPresence;
                      if (deviceMode === 'tee_enclave') base.environment.pcr0 = devicePcr0;
                      if (!base.payload) base.payload = {};
                      base.payload.nonce = deviceNonce;
                      void handleEvaluate('deviceApproval', apiEvaluatePerpsDeviceApproval, base);
                    }}
                  >
                    Submit Device Approval
                  </button>
                  <button
                    className="btn btn-secondary btn-sm"
                    type="button"
                    onClick={() => {
                      const base = fixtures.signerDeviceIntegration ? JSON.parse(JSON.stringify(fixtures.signerDeviceIntegration)) : {};
                      base.key_id = deviceKeyId;
                      base.device_label = deviceLabel;
                      if (!base.environment) base.environment = {};
                      base.environment.environment_kind = deviceMode;
                      base.environment.rollback_protection_confirmed = rollbackProtection;
                      base.environment.local_user_presence_confirmed = userPresence;
                      if (deviceMode === 'tee_enclave') base.environment.pcr0 = devicePcr0;
                      void handleEvaluate('signerDevice', apiEvaluatePerpsSignerDevice, base);
                    }}
                  >
                    Submit Signer Integration
                  </button>
                </div>
              </div>
            )}

            {/* Step 3: Social Recovery */}
            <div className={`gov-exercise-row step-card ${recoveryReady ? 'step-done' : 'step-next'}`} id="recovery-row">
              <div className="step-number">3</div>
              <div className="gov-exercise-info">
                <h3>Trusted contact recovery</h3>
                <p>Verify backup restoration using social recovery guardian signatures.</p>
                <div className="gov-status-badges">
                  {recoveryReady ? (
                    <span className="gov-badge-ready" id="recovery-ready-badge">Recovery evaluation ready</span>
                  ) : (
                    <span className="gov-badge-blocked">Recovery evaluation blocked</span>
                  )}
                </div>
              </div>
              <div className="gov-exercise-action-group">
                <button
                  className="btn btn-ghost btn-xs"
                  type="button"
                  onClick={() => setActiveForm(activeForm === 'recovery' ? null : 'recovery')}
                >
                  {activeForm === 'recovery' ? 'Close Config' : 'Configure Form'}
                </button>
                <button
                  className="btn btn-primary"
                  type="button"
                  onClick={() => handleEvaluate('recovery', apiEvaluatePerpsRecovery, fixtures.recoveryExercise)}
                  disabled={evaluating.recovery || recoveryReady}
                >
                  {evaluating.recovery ? 'Evaluating...' : recoveryReady ? 'Evaluated' : 'Evaluate'}
                </button>
              </div>
            </div>

            {/* Recovery Inline Form */}
            {activeForm === 'recovery' && (
              <div className="gov-form-panel animate-fade-in">
                <h4>Key Management &amp; Social Recovery Setup</h4>
                <div className="gov-form-grid">
                  <label className="label">
                    <span>Subject Key ID</span>
                    <input className="input" value={subjectKeyId} onChange={(e) => setSubjectKeyId(e.target.value)} />
                  </label>
                  <label className="label">
                    <span>Recovery Policy ID</span>
                    <input className="input" value={policyId} onChange={(e) => setPolicyId(e.target.value)} />
                  </label>
                </div>
                <div className="gov-form-grid">
                  <label className="label">
                    <span>Request time</span>
                    <input className="input" type="number" value={requestedEpoch} onChange={(e) => setRequestedEpoch(parseInt(e.target.value, 10) || 0)} />
                  </label>
                  <label className="label">
                    <span>Current period</span>
                    <input className="input" type="number" value={currentEpoch} onChange={(e) => setCurrentEpoch(parseInt(e.target.value, 10) || 0)} />
                  </label>
                </div>
                <label className="label gov-form-label">
                  <span>Trusted contacts (comma separated)</span>
                  <input className="input" value={guardianList} onChange={(e) => setGuardianList(e.target.value)} />
                </label>
                <label className="label gov-form-label">
                  <span>Approvals (JSON format)</span>
                  <textarea className="input mono" rows={3} value={sigEnvelopesJson} onChange={(e) => setSigEnvelopesJson(e.target.value)} />
                </label>
                <button
                  className="btn btn-primary btn-sm"
                  type="button"
                  onClick={() => {
                    const base = fixtures.recoveryExercise ? JSON.parse(JSON.stringify(fixtures.recoveryExercise)) : {};
                    base.subject_key_id = subjectKeyId;
                    base.policy_id = policyId;
                    base.requested_at_epoch = requestedEpoch;
                    base.current_epoch = currentEpoch;
                    base.approvals = guardianList.split(',').map(g => g.trim()).filter(Boolean);
                    try {
                      base.signature_envelopes = JSON.parse(sigEnvelopesJson);
                    } catch {
                      setEvalError('Invalid Signature Envelopes JSON structure');
                      return;
                    }
                    void handleEvaluate('recovery', apiEvaluatePerpsRecovery, base);
                  }}
                >
                  Submit Social Recovery
                </button>
              </div>
            )}

            {/* Step 4: Key Rotation */}
            <div className={`gov-exercise-row step-card ${rotationReady ? 'step-done' : 'step-next'}`} id="rotation-row">
              <div className="step-number">4</div>
              <div className="gov-exercise-info">
                <h3>Replace key</h3>
                <p>Replace keys using pre-configured recovery rules.</p>
                <div className="gov-status-badges">
                  {rotationReady ? (
                    <span className="gov-badge-ready" id="rotation-ready-badge">Rotation evaluation ready</span>
                  ) : (
                    <span className="gov-badge-blocked">Rotation evaluation blocked</span>
                  )}
                </div>
              </div>
              <div className="gov-exercise-action-group">
                <button
                  className="btn btn-ghost btn-xs"
                  type="button"
                  onClick={() => setActiveForm(activeForm === 'rotation' ? null : 'rotation')}
                >
                  {activeForm === 'rotation' ? 'Close Config' : 'Configure Form'}
                </button>
                <button
                  className="btn btn-primary"
                  type="button"
                  onClick={() => handleEvaluate('rotation', apiEvaluatePerpsRotation, fixtures.rotationExercise)}
                  disabled={evaluating.rotation || rotationReady}
                >
                  {evaluating.rotation ? 'Evaluating...' : rotationReady ? 'Evaluated' : 'Evaluate'}
                </button>
              </div>
            </div>

            {/* Rotation Inline Form */}
            {activeForm === 'rotation' && (
              <div className="gov-form-panel animate-fade-in">
                <h4>Key Rotation Parameters</h4>
                <div className="gov-form-grid">
                  <label className="label">
                    <span>Key to replace</span>
                    <input className="input" value={rotatedKeyId} onChange={(e) => setRotatedKeyId(e.target.value)} />
                  </label>
                  <label className="label">
                    <span>New key ID</span>
                    <input className="input" value={replacementKeyId} onChange={(e) => setReplacementKeyId(e.target.value)} />
                  </label>
                </div>
                <div className="gov-form-grid">
                  <label className="label">
                    <span>Policy ID</span>
                    <input className="input" value={rotationPolicyId} onChange={(e) => setRotationPolicyId(e.target.value)} />
                  </label>
                  <label className="label">
                    <span>Announcement time</span>
                    <input className="input" type="number" value={broadcastEpoch} onChange={(e) => setBroadcastEpoch(parseInt(e.target.value, 10) || 0)} />
                  </label>
                </div>
                <label className="label gov-form-label">
                  <span>Trusted contacts (comma separated)</span>
                  <input className="input" value={rotationGuardianList} onChange={(e) => setRotationGuardianList(e.target.value)} />
                </label>
                <label className="label gov-form-label">
                  <span>Approvals (JSON format)</span>
                  <textarea className="input mono" rows={2} value={rotationSigEnvelopesJson} onChange={(e) => setRotationSigEnvelopesJson(e.target.value)} />
                </label>
                <label className="label gov-form-label">
                  <span>New wallet configuration (JSON)</span>
                  <textarea className="input mono" rows={3} value={nextProfileJson} onChange={(e) => setNextProfileJson(e.target.value)} />
                </label>
                <button
                  className="btn btn-primary btn-sm"
                  type="button"
                  onClick={() => {
                    const base = fixtures.rotationExercise ? JSON.parse(JSON.stringify(fixtures.rotationExercise)) : {};
                    base.rotated_key_id = rotatedKeyId;
                    base.replacement_key_id = replacementKeyId;
                    base.policy_id = rotationPolicyId;
                    base.broadcast_at_epoch = broadcastEpoch;
                    base.approvals = rotationGuardianList.split(',').map(g => g.trim()).filter(Boolean);
                    try {
                      base.signature_envelopes = JSON.parse(rotationSigEnvelopesJson);
                    } catch {
                      setEvalError('Invalid Signature Envelopes JSON structure');
                      return;
                    }
                    try {
                      base.next_wallet_authority_profile = JSON.parse(nextProfileJson);
                    } catch {
                      setEvalError('Invalid Next Wallet Authority Profile JSON');
                      return;
                    }
                    void handleEvaluate('rotation', apiEvaluatePerpsRotation, base);
                  }}
                >
                  Submit Key Rotation
                </button>
              </div>
            )}
          </div>
        </div>
      </div>
      )}

      {/* Advanced — collapsed panels for power users */}
      <details className="gov-collapsible-panel" id="advanced-security-policy">
        <summary className="gov-collapsible-summary">
          <span className="gov-collapsible-title">Advanced — Security policy</span>
          <span className="gov-collapsible-hint">Threshold, governance details, cryptographic IDs</span>
        </summary>
        <div className="gov-collapsible-body">
          <div className="gov-wide-grid">
            <div className="panel gov-card" id="card-encrypted-sss-backup">
          <div className="gov-section-header">
            <h2>Encrypted backup</h2>
            <span className="gov-section-badge">Key Backup</span>
          </div>
          <div className="gov-status-list">
            <div className="gov-kv">
              <span>Backup Status</span>
              <span className={`gov-status-value ${encryptedSssReady ? 'status-ready' : 'status-blocked'}`} id="encrypted-sss-ready-status">
                {encryptedSssReady ? 'Encrypted backup ready' : encryptedSssBackup?.status || 'N/A'}
              </span>
            </div>
            <div className="gov-kv">
              <span>Required</span>
              <span>{encryptedSssBackup?.threshold ?? 'N/A'} / {encryptedSssBackup?.share_count ?? 'N/A'} backup parts</span>
            </div>
            <div className="gov-kv">
              <span>Recovery test</span>
              <span className={`gov-status-value ${encryptedSssBackup?.recovery_drill_ready ? 'status-ready' : 'status-blocked'}`}>
                {encryptedSssBackup?.recovery_drill_ready ? 'ready' : 'blocked'}
              </span>
            </div>
            <div className="gov-kv">
              <span>Security tests</span>
              <span className={`gov-status-value ${encryptedSssBackup?.hostile_share_tests_ready ? 'status-ready' : 'status-blocked'}`}>
                {encryptedSssBackup?.hostile_share_tests_ready ? 'ready' : 'blocked'}
              </span>
            </div>
            <div className="gov-kv">
              <span>Provider Delivery</span>
              <span className={`gov-status-value ${sssProviderDeliveryReady ? 'status-ready' : 'status-blocked'}`}>
                {sssProviderDeliveryReady ? 'fixture evidence ready' : 'blocked'}
              </span>
            </div>
            <div className="gov-kv">
              <span>Live Providers</span>
              <span className={`gov-status-value ${sssLiveProviderDeliveryReady ? 'status-ready' : 'status-blocked'}`}>
                {sssLiveProviderDeliveryReady ? 'external delivery ready' : 'provider adapter required'}
              </span>
            </div>
            <div className="gov-kv">
              <span>External Audit</span>
              <span className={`gov-status-value ${externalAuditReady ? 'status-ready' : 'status-blocked'}`}>
                {externalAuditReady ? 'ready' : encryptedSssBackup?.audit_status || 'pending'}
              </span>
            </div>
            <div className="gov-kv">
              <span>Server Reconstitution</span>
              <span>{encryptedSssBackup?.server_side_reconstitution ? 'enabled' : 'disabled'}</span>
            </div>
            <div className="gov-kv">
              <span>Backup Hash</span>
              <span className="gov-mono">{compactId(encryptedSssBackup?.backup_hash)}</span>
            </div>
          </div>
          <div className="gov-provider-chip-list" aria-label="Backup storage types">
            {sssProviderKinds.length ? sssProviderKinds.map((kind) => (
              <span className="gov-provider-chip" key={kind}>{kind}</span>
            )) : <span className="gov-no-fixture">Provider N/A</span>}
          </div>
          <div className="gov-provider-list" aria-label="Backup providers">
            {sssProviderIds.slice(0, 6).map((providerId) => (
              <span className="gov-provider-id" key={providerId}>{providerId}</span>
            ))}
          </div>
          <div className="gov-provider-chip-list" aria-label="Delivery methods">
            {sssDeliveryModes.map((mode) => (
              <span className="gov-provider-chip gov-provider-chip-muted" key={mode}>{mode}</span>
            ))}
          </div>
          {!sssLiveProviderDeliveryReady && (
            <div className="gov-inline-warning" id="encrypted-sss-live-delivery-warning">
              Encrypted recovery delivery is wired to the backend. Configure recovery email, Dropbox, Box, or offline export, then use Deliver to capture external delivery receipts.
            </div>
          )}
          <div className="gov-connector-grid" aria-label="Backup delivery options">
            {sssDeliveryConnectors.map((connector) => (
              <div className="gov-connector-row" key={connector.key}>
                <div>
                  <span className="gov-connector-label">{connector.label}</span>
                  <span className="gov-connector-mode">{connector.liveMode}</span>
                </div>
                <button
                  className={`btn btn-secondary btn-xs gov-connector-btn ${connector.ready || connector.actionAvailable ? 'connector-ready' : ''}`}
                  type="button"
                  disabled={!connector.ready && !connector.actionAvailable}
                  aria-disabled={!connector.ready && !connector.actionAvailable}
                  onClick={connector.actionAvailable ? connector.onClick : undefined}
                  title={
                    connector.ready
                      ? `${connector.label} has live delivery evidence`
                      : connector.actionAvailable
                        ? connector.actionTitle
                      : `${connector.label} delivery requires a configured external provider adapter`
                  }
                >
                  {connector.ready ? connector.readyLabel : connector.actionAvailable ? connector.actionLabel : connector.blockedLabel}
                </button>
                {!connector.configured && (
                  <span className="gov-connector-missing">provider missing</span>
                )}
              </div>
            ))}
          </div>
          <button
            className="btn btn-secondary gov-refresh-btn"
            type="button"
            onClick={() => handleEvaluate('encryptedSssBackup', apiEvaluatePerpsEncryptedSssBackup, fixtures.encryptedSssBackup)}
            disabled={evaluating.encryptedSssBackup || !fixtures.encryptedSssBackup}
          >
            {evaluating.encryptedSssBackup ? 'Evaluating...' : 'Evaluate Fixture Backup'}
          </button>
          <button
            className="btn btn-secondary gov-refresh-btn"
            type="button"
            onClick={handleDownloadEncryptedSssBackup}
            disabled={!fixtures.encryptedSssBackup && !deliveredSssBackup}
          >
            Download Fixture Backup
          </button>
        </div>

        <div className="panel gov-card" id="card-production-readiness">
          <div className="gov-section-header">
            <h2>Production Evidence</h2>
            <span className="gov-section-badge">Fail Closed</span>
          </div>
          <div className="gov-status-list">
            <div className="gov-kv">
              <span>Privacy mode</span>
              <span className={`gov-status-value ${zkStrictReady ? 'status-ready' : 'status-blocked'}`} id="zk-posture-status">
                {zkEffectiveMode} requested {zkRequestedMode}
              </span>
            </div>
            <div className="gov-kv">
              <span>Verifier Kind</span>
              <span>{zkPosture?.proof_verifier_kind || 'N/A'}</span>
            </div>
            <div className="gov-kv">
              <span>Production Hardware</span>
              <span className={`gov-status-value ${productionHardwareCustodyReady ? 'status-ready' : 'status-blocked'}`}>
                {productionHardwareCustodyReady ? 'ready' : 'fixture or unverified'}
              </span>
            </div>
            <div className="gov-kv">
              <span>Local Hardware Gate</span>
              <span className={`gov-status-value ${hardwareCustodyReady ? 'status-ready' : 'status-blocked'}`}>
                {hardwareCustodyReady ? 'ready' : 'blocked'}
              </span>
            </div>
            <div className="gov-kv">
              <span>Signer Ceremony</span>
              <span className={`gov-status-value ${signerCeremonyReady ? 'status-ready' : 'status-blocked'}`}>
                {signerCeremonyReady ? 'ready' : 'blocked'}
              </span>
            </div>
            <div className="gov-kv">
              <span>Production Claim</span>
              <span>{(zkPosture?.production_security_claim === true || encryptedSssBackup?.production_security_claim === true) ? 'true' : 'false'}</span>
            </div>
          </div>
          {zkPosture?.zk_fallback_reason && (
            <div className="gov-inline-warning" id="zk-fallback-reason">
              {zkPosture.zk_fallback_reason}
            </div>
          )}
        </div>
          </div>
          </div>
        </details>

      {/* Advanced — Developer diagnostics */}
      <details className="gov-collapsible-panel" id="advanced-developer-diagnostics">
        <summary className="gov-collapsible-summary">
          <span className="gov-collapsible-title">Advanced — Developer diagnostics</span>
          <span className="gov-collapsible-hint">Testnet evidence, logs, raw JSON, pipeline status</span>
        </summary>
        <div className="gov-collapsible-body">

      {/* Fixture inspection panel if active */}
      {expandedFixture && fixturePreview ? (
        <div className="panel gov-card gov-fixture-drawer animate-fade-in">
          <div className="gov-section-header">
            <h3>Test data preview: {expandedFixture}</h3>
            <button className="btn btn-ghost btn-xs" type="button" onClick={() => setExpandedFixture(null)}>Close Preview</button>
          </div>
          <pre className="gov-redacted-json">
            {JSON.stringify(redactSensitive(fixturePreview), null, 2)}
          </pre>
        </div>
      ) : null}

      {/* Redacted JSON Status Details */}
      <div className="panel gov-card gov-details-card">
        <div className="gov-section-header">
          <h2>Status Logs</h2>
          <div className="gov-header-actions">
            <button
              className={`btn ${showRaw ? 'btn-warn' : 'btn-secondary'} btn-xs`}
              type="button"
              onClick={() => setShowRaw(!showRaw)}
            >
              {showRaw ? 'Hide sensitive data' : 'Show raw data'}
            </button>
            <span className="gov-section-badge">Developer View</span>
          </div>
        </div>
        <p className="gov-disclaimer">
          {showRaw ? (
            <strong className="gov-warning-text">WARNING: Sensitive data is visible. Do not share this screen.</strong>
          ) : (
            'Notice: Test environment. Sensitive data has been hidden.'
          )}
        </p>
        <details className="gov-status-logs-details">
          <summary className="btn btn-secondary btn-xs gov-status-logs-summary">
            Show/hide status details
          </summary>
          <pre className="gov-redacted-json">
            {status
              ? JSON.stringify(showRaw ? status : redactSensitive(status), null, 2)
              : 'Status not loaded'}
          </pre>
        </details>
      </div>
        </div>
      </details>
    </section>
  );
}
