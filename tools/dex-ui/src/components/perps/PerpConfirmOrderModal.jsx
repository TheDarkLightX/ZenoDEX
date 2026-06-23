import { useState, useCallback } from 'react';
import Modal from '../Modal.jsx';
import './PerpConfirmOrderModal.css';

/**
 * PerpConfirmOrderModal - Graduated friction confirmation
 *
 * Risk tiers:
 * - High (5-10x): Confirmation modal with details
 * - Extreme (>10x): Must type "CONFIRM" to proceed
 */
function PerpConfirmOrderModal({ order, market, onConfirm, onClose }) {
    const [confirmText, setConfirmText] = useState('');

    const isExtreme = order?.riskTier?.tier === 'extreme';
    const canConfirm = isExtreme ? confirmText === 'CONFIRM' : true;

    const handleConfirm = useCallback(() => {
        if (!canConfirm) return;
        onConfirm?.({ marketId: market?.id, newPositionBase: order.newPositionBase });
        onClose();
    }, [canConfirm, order, market, onConfirm, onClose]);

    if (!order) return null;

    return (
        <Modal open onClose={onClose} title={isExtreme ? 'Extreme Risk Order' : 'Confirm Order'} size="sm">
                <div className="perp-confirm-body">
                    {/* Risk Banner */}
                    <div
                        className="perp-confirm-risk-banner"
                        style={{
                            borderColor: order.riskTier?.color,
                            background: `${order.riskTier?.color}15`,
                        }}
                    >
                        <span className="perp-confirm-risk-label">
                            {order.riskTier?.label}
                        </span>
                        <span className="perp-confirm-risk-leverage">
                            {order.leverage?.toFixed(1)}x leverage
                        </span>
                    </div>

                    {/* Order Details */}
                    <div className="perp-confirm-details">
                        <div className="perp-confirm-row">
                            <span>Direction</span>
                            <span className={`perp-confirm-side perp-confirm-side--${order.side}`}>
                                {order.side?.toUpperCase()}
                            </span>
                        </div>
                        <div className="perp-confirm-row">
                            <span>Market</span>
                            <span>{market?.id}</span>
                        </div>
                        <div className="perp-confirm-row">
                            <span>Size</span>
                            <span>{order.size?.toLocaleString()} base</span>
                        </div>
                        <div className="perp-confirm-row">
                            <span>Leverage</span>
                            <span style={{ color: order.riskTier?.color }}>
                                {order.leverage?.toFixed(1)}x
                            </span>
                        </div>
                    </div>

                    {/* Extreme: type CONFIRM */}
                    {isExtreme && (
                        <div className="perp-confirm-extreme">
                            <p className="perp-confirm-extreme-text">
                                This is an extremely high-risk trade. Type <strong>CONFIRM</strong> to proceed.
                            </p>
                            <input
                                type="text"
                                className="input perp-confirm-input"
                                placeholder='Type "CONFIRM"'
                                value={confirmText}
                                onChange={e => setConfirmText(e.target.value)}
                                autoFocus
                            />
                        </div>
                    )}
                </div>

                <div className="perp-confirm-footer">
                    <button className="btn btn-secondary" onClick={onClose}>
                        Cancel
                    </button>
                    <button
                        className={`btn perp-confirm-submit ${order.side === 'long' ? 'perp-submit-long' : 'perp-submit-short'}`}
                        onClick={handleConfirm}
                        disabled={!canConfirm}
                    >
                        {isExtreme ? 'Prepare Trade' : 'Confirm Trade'}
                    </button>
                </div>
        </Modal>
    );
}

export default PerpConfirmOrderModal;
