// Copyright (c) DarkLightX/Dana Edwards. All rights reserved.

import Modal from '../Modal.jsx';
import { shortHash } from '../../lib/swapUtils';

export function SwapSubmittedModal({ submittedSwap, onClose }) {
    if (!submittedSwap) return null;
    return (
        <Modal open onClose={onClose} title={submittedSwap.status === 'pending' ? 'Transaction Pending' : 'Swap Confirmed'} size="sm">
                <p className="submitted-copy">
                    {submittedSwap.status === 'pending'
                        ? 'Broadcasting transaction to Tau Net Alpha...'
                        : 'Wallet submission confirmed; on-chain status tracking is ready.'}
                </p>
                <div className="submitted-status-row">
                    <span className={`tx-status-badge ${submittedSwap.status}`}>
                        {submittedSwap.status === 'pending' ? 'Pending' : 'Confirmed'}
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
                                <span>Verified ({submittedSwap.certSeconds}s)</span>
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
