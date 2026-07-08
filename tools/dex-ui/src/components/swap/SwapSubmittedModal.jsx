// Copyright (c) DarkLightX/Dana Edwards. All rights reserved.

import Modal from '../Modal.jsx';
import { shortHash } from '../../lib/swapUtils';

export function SwapSubmittedModal({ submittedSwap, onClose }) {
    if (!submittedSwap) return null;
    const accepted = submittedSwap.status === 'confirmed';
    return (
        <Modal open onClose={onClose} title={accepted ? 'Accepted by runtime' : 'Submitted, awaiting receipt'} size="sm">
                <p className="submitted-copy">
                    {accepted
                        ? 'The runtime reported acceptance for this submission.'
                        : 'A transaction hash is a submission reference. Acceptance requires tx_accepted=true or receipt.accepted=true from the API.'}
                </p>
                <div className="submitted-status-row">
                    <span className={`tx-status-badge ${submittedSwap.status}`}>
                        {accepted ? 'Accepted' : 'Awaiting receipt'}
                    </span>
                    <span className="submitted-time">
                        {new Date(submittedSwap.submittedAt).toLocaleTimeString()}
                    </span>
                </div>
                <div className="confirm-details">
                    <div className="confirm-row">
                        <span>Tx Hash:</span>
                        <span className="tx-hash mono">{shortHash(submittedSwap.txHash)}</span>
                    </div>
                    <div className="confirm-row">
                        <span>Network:</span>
                        <span>{submittedSwap.network}</span>
                    </div>
                    <div className="confirm-row">
                        <span>Submission:</span>
                        <span>{submittedSwap.submitPath === 'local-fallback' ? 'Local fallback' : 'Network relay'}</span>
                    </div>
                    <div className="confirm-row">
                        <span>Acceptance:</span>
                        <span>{accepted ? submittedSwap.acceptanceEvidence || 'runtime accepted' : 'awaiting API evidence'}</span>
                    </div>
                    {submittedSwap.receiptHash && (
                        <div className="confirm-row">
                            <span>Receipt:</span>
                            <span className="tx-hash mono">{shortHash(submittedSwap.receiptHash)}</span>
                        </div>
                    )}
                    {submittedSwap.height !== null && submittedSwap.height !== undefined && (
                        <div className="confirm-row">
                            <span>Block height:</span>
                            <span>{submittedSwap.height}</span>
                        </div>
                    )}
                    <div className="confirm-row">
                        <span>You pay:</span>
                        <span>{submittedSwap.amountIn} {submittedSwap.fromSymbol}</span>
                    </div>
                    <div className="confirm-row">
                        <span>You receive:</span>
                        <span>{submittedSwap.amountOut} {submittedSwap.toSymbol}</span>
                    </div>
                    <div className="confirm-row">
                        <span>Minimum received:</span>
                        <span>{submittedSwap.minOutput} {submittedSwap.toSymbol}</span>
                    </div>
                    {submittedSwap.advanced && (
                        <>
                            <div className="confirm-row">
                                <span>Route:</span>
                                <span>{submittedSwap.routePath}</span>
                            </div>
                            <div className="confirm-row">
                                <span>Profile:</span>
                                <span>{submittedSwap.profileLabel}</span>
                            </div>
                            <div className="confirm-row">
                                <span>Quote certificate:</span>
                                <span>Valid ({submittedSwap.certSeconds}s)</span>
                            </div>
                        </>
                    )}
                </div>
                <div className="confirm-actions">
                    <a
                        className="btn btn-secondary"
                        href={`https://explorer.tau.net/tx/${submittedSwap.txHash}`}
                        target="_blank"
                        rel="noopener noreferrer"
                    >
                        View Explorer
                    </a>
                    <button className="btn btn-primary" onClick={onClose}>
                        Done
                    </button>
                </div>
        </Modal>
    );
}
