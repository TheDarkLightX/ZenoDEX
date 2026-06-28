// Copyright (c) DarkLightX/Dana Edwards. All rights reserved.

import { formatNumber, formatPercent } from '../../lib/cpmm';
import CopyHash from '../CopyHash.jsx';

export function SwapProofPanel({
    proofEnforced,
    postureKnown,
    zkPosture,
    advancedMode,
    certificateCheck,
    activePreview,
    impactSeverity,
    envHasBounds,
    envPos,
    toToken,
    submittedSwap,
}) {
    return (
        <aside className="swap-proof panel" aria-label="Execution proof">
            <div className="swap-rail-head">
                <span className="swap-rail-eyebrow">Execution proof</span>
                <h3 className="swap-rail-title">Verification</h3>
            </div>

            <div className={`swap-proof-posture ${proofEnforced ? 'is-enforced' : 'is-advisory'}`}>
                <div className="swap-proof-posture-head">
                    <span className="swap-proof-posture-dot" aria-hidden="true" />
                    <span className="swap-proof-posture-label">
                        {proofEnforced
                            ? 'Proof-wrapper active'
                            : (postureKnown ? 'Spec-checked · proofs off' : 'Posture unavailable')}
                    </span>
                </div>
                <p className="swap-proof-posture-detail">
                    {proofEnforced ? (
                        <>This stack has the <code>{zkPosture.proof_verifier_kind}</code> proof verifier active for mounted live write gates (zk {zkPosture.zk_mode_effective}). Spot swap math is validated by Tau spec <code>cpmm_v1</code>; this is runtime posture, not a production spot ZK proof.</>
                    ) : (
                        <>Tau spec <code>cpmm_v1</code> defines the math, but this environment runs zk <code>{zkPosture.zk_mode_effective || 'unknown'}</code> with proof verification <strong>disabled</strong>. Treat green checks as spec conformance, not a production proof.</>
                    )}
                </p>
            </div>

            <div className="swap-proof-evidence" role="list">
                <span className="swap-proof-ev" role="listitem">
                    <span className={`swap-proof-ev-dot ${proofEnforced ? 'ev-on' : 'ev-off'}`} aria-hidden="true" />
                    Proof verifier {proofEnforced ? 'active' : 'off'}
                </span>
                <span className="swap-proof-ev" role="listitem">
                    <span className="swap-proof-ev-dot ev-on" aria-hidden="true" />
                    Tau spec cpmm_v1
                </span>
                <span className="swap-proof-ev" role="listitem">
                    <span className={`swap-proof-ev-dot ${(!advancedMode || certificateCheck.ok) ? 'ev-on' : 'ev-off'}`} aria-hidden="true" />
                    {advancedMode ? (certificateCheck.ok ? 'Quote cert verified' : 'Quote cert stale') : 'Deterministic quote'}
                </span>
            </div>

            {activePreview ? (
                <div className="swap-proof-envelope">
                    <div className="swap-proof-envelope-head">
                        <span>Execution envelope</span>
                        <span className={`impact-${impactSeverity}`}>{formatPercent(activePreview.priceImpact)} impact</span>
                    </div>
                    {envHasBounds ? (
                        <>
                            <div className="swap-proof-envelope-bar" aria-hidden="true">
                                <span className="swap-proof-envelope-mid" style={{ left: `${envPos}%` }} />
                            </div>
                            <div className="swap-proof-envelope-legend mono">
                                <span>min {formatNumber(activePreview.amountOutWorstCase)}</span>
                                <span>exp {formatNumber(activePreview.output)}</span>
                                <span>max {formatNumber(activePreview.amountOutBestCase)}</span>
                            </div>
                        </>
                    ) : (
                        <div className="swap-proof-envelope-legend mono single">
                            <span>min received</span>
                            <span>{formatNumber(activePreview.minOutput)} {toToken.symbol}</span>
                        </div>
                    )}
                </div>
            ) : (
                <div className="swap-rail-empty">
                    <p className="swap-rail-empty-hint">Enter an amount to compute the deterministic execution envelope and minimum received.</p>
                </div>
            )}

            {submittedSwap?.receipt?.receipt_hash && (
                <div className="swap-proof-receipt">
                    <div className="swap-proof-receipt-head">
                        <span className="swap-proof-receipt-dot" aria-hidden="true" />
                        Settlement receipt
                    </div>
                    <div className="swap-proof-receipt-row">
                        <span>Hash</span>
                        <CopyHash value={submittedSwap.receipt.receipt_hash} label="receipt hash" />
                    </div>
                    {submittedSwap.receipt.body?.schema && (
                        <div className="swap-proof-receipt-row">
                            <span>Schema</span>
                            <span className="mono swap-proof-receipt-schema">{submittedSwap.receipt.body.schema}</span>
                        </div>
                    )}
                    <div className="swap-proof-receipt-row">
                        <span>Canonical route</span>
                        <span className={submittedSwap.receipt.body?.canonical_route_certificate ? 'impact-low' : 'impact-medium'}>
                            {submittedSwap.receipt.body?.canonical_route_certificate ? 'certified winner' : 'not attached'}
                        </span>
                    </div>
                </div>
            )}
        </aside>
    );
}
