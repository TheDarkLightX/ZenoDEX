// Copyright (c) DarkLightX/Dana Edwards. All rights reserved.

import { getRuntimeConfig } from '../lib/api.js';
import { useDemoMode } from '../lib/DemoModeContext.jsx';

function normalizeText(value, fallback) {
  const text = String(value ?? '').trim();
  return text || fallback;
}

function proofPostureLabel(runtimeConfig) {
  const posture = runtimeConfig.localTestnetZkPosture || {};
  const effectiveMode = normalizeText(posture.zk_mode_effective, '');
  const requestedMode = normalizeText(posture.zk_mode_requested, '');
  const verifierKind = normalizeText(posture.proof_verifier_kind, '');
  if (posture.zk_required === true && effectiveMode === 'strict') {
    return verifierKind ? `strict ${verifierKind}` : 'strict';
  }
  if (effectiveMode || requestedMode || verifierKind) {
    const mode = effectiveMode || requestedMode || 'available';
    return verifierKind ? `${mode} ${verifierKind}` : mode;
  }
  return 'not reported';
}

export default function ClaimBoundaryStrip({ activeTab, wallet, uiSurfaceVersion }) {
  const { demoMode } = useDemoMode();
  const runtimeConfig = getRuntimeConfig();
  const chainId = normalizeText(runtimeConfig.chainId, wallet?.chainId || 'local-testnet');
  const mode = demoMode ? 'demo data' : 'live local-testnet';
  const signer = wallet?.address ? 'connected' : 'not connected';

  return (
    <div className="claim-boundary-strip" role="status" aria-label="Runtime claim boundary">
      <div className="claim-boundary-inner">
        <span className="claim-boundary-chip claim-boundary-primary">
          {activeTab}
        </span>
        <span className="claim-boundary-chip">
          Runtime: {mode}
        </span>
        <span className="claim-boundary-chip">
          Chain: {chainId}
        </span>
        <span className="claim-boundary-chip">
          Proofs: {proofPostureLabel(runtimeConfig)}
        </span>
        <span className="claim-boundary-chip">
          Signer: {signer}
        </span>
        <span className="claim-boundary-chip">
          Acceptance: receipt-gated
        </span>
        <span className="claim-boundary-version">
          {uiSurfaceVersion}
        </span>
      </div>
    </div>
  );
}
