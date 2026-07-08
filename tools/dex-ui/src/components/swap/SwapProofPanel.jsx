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
        <aside className="swap-proof panel" aria-label="Swap verification">
            <div className="swap-rail-head">
                <span className="swap-rail-eyebrow">Swap verification</span>
                <h3 className="swap-rail-title">Verification</h3>
            </div>

            <div className={`swap-proof-posture ${proofEnforced ? 'is-enforced' : 'is-advisory'}`}>
                <div className="swap-proof-posture-head">
                    <span className="swap-proof-posture-dot" aria-hidden="true" />
                    <span className="swap-proof-posture-label">
                        {proofEnforced
                            ? 'Proof verification active'
                            : (postureKnown ? 'Math verified · proofs off' : 'Verification unavailable')}
                    </span>
                </div>
                <p className="swap-proof-posture-detail">
                    {proofEnforced ? (
                        <>The <code>{zkPosture.proof_verifier_kind}</code> proof verifier is active. Swap math is verified by the mathematical proof system; this is runtime verification, not a production ZK proof.</>
                    ) : (
                        <>Swap math follows the specification, but proof verification is <strong>disabled</strong> in this environment. Green checks indicate spec conformance, not a production proof.</>
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
                    Verified math
                </span>
                <span className="swap-proof-ev" role="listitem">
                    <span className={`swap-proof-ev-dot ${(!advancedMode || certificateCheck.ok) ? 'ev-on' : 'ev-off'}`} aria-hidden="true" />
                    {advancedMode ? (certificateCheck.ok ? 'Quote verified' : 'Quote stale') : 'Consistent quote'}
                </span>
            </div>

            {activePreview ? (
                <div className="swap-proof-envelope">
                    <div className="swap-proof-envelope-head">
                        <span>Output range</span>
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
                    <p className="swap-rail-empty-hint">Enter an amount to see your expected output range and minimum received.</p>
                </div>
            )}

            {submittedSwap?.receipt?.receipt_hash && (
                <div className="swap-proof-receipt">
                    <div className="swap-proof-receipt-head">
                        <span className="swap-proof-receipt-dot" aria-hidden="true" />
                        Settlement record
                    </div>
                    <div className="swap-proof-receipt-row">
                        <span>Hash</span>
                        <CopyHash value={submittedSwap.receipt.receipt_hash} label="record hash" />
                    </div>
                    {submittedSwap.receipt.body?.schema && (
                        <div className="swap-proof-receipt-row">
                            <span>Schema</span>
                            <span className="mono swap-proof-receipt-schema">{submittedSwap.receipt.body.schema}</span>
                        </div>
                    )}
                    <div className="swap-proof-receipt-row">
                        <span>Swap path</span>
                        <span className={submittedSwap.receipt.body?.canonical_route_certificate ? 'impact-low' : 'impact-medium'}>
                            {submittedSwap.receipt.body?.canonical_route_certificate ? 'verified' : 'not attached'}
                        </span>
                    </div>
                </div>
            )}
        </aside>
    );
}
