import { EpochPhase } from '../../lib/perpValidation.js';
import './PerpEpochIndicator.css';

/**
 * PerpEpochIndicator - Epoch lifecycle visualization
 *
 * Shows the 3-step epoch lifecycle unique to ZenoDex:
 * OPEN -> PRICE_PUBLISHED -> SETTLED
 *
 * Visual progress indicator with active step highlighted.
 */
function PerpEpochIndicator({ market }) {
    if (!market) return null;

    const steps = [
        { phase: EpochPhase.OPEN, label: 'Open', description: 'Trading active' },
        { phase: EpochPhase.PRICE_PUBLISHED, label: 'Price Published', description: 'Settlement pending' },
        { phase: EpochPhase.SETTLED, label: 'Settled', description: 'PnL realized' },
    ];

    const currentIndex = steps.findIndex(s => s.phase === market.epochPhase);

    return (
        <div className="perp-epoch-indicator">
            <div className="perp-epoch-header">
                <span className="perp-epoch-label">
                    {market.nowEpoch != null ? `Epoch #${market.nowEpoch}` : 'Epoch unknown'}
                </span>
            </div>
            <div className="perp-epoch-steps">
                {steps.map((step, idx) => {
                    const isDone = idx < currentIndex;
                    const isActive = idx === currentIndex;
                    const className = isDone ? 'done' : isActive ? 'active' : 'pending';

                    return (
                        <div key={step.phase} className="perp-epoch-step-wrapper">
                            {idx > 0 && (
                                <div className={`perp-epoch-connector ${isDone || isActive ? 'filled' : ''}`} />
                            )}
                            <div className={`perp-epoch-step ${className}`}>
                                <div className="perp-epoch-dot">
                                    {isDone ? '\u2713' : (idx + 1)}
                                </div>
                                <div className="perp-epoch-step-text">
                                    <span className="perp-epoch-step-label">{step.label}</span>
                                    <span className="perp-epoch-step-desc">{step.description}</span>
                                </div>
                            </div>
                        </div>
                    );
                })}
            </div>
        </div>
    );
}

export default PerpEpochIndicator;
