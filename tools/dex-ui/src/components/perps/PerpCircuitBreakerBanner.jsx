import './PerpCircuitBreakerBanner.css';

/**
 * PerpCircuitBreakerBanner - Full-width warning banner when circuit breaker is active
 *
 * Displays a prominent red banner at the top of the perps area indicating
 * that reduce-only mode is enforced. Hidden when breaker is inactive.
 */
function PerpCircuitBreakerBanner({ breakerActive, breakerLastTriggerEpoch }) {
    if (!breakerActive) return null;

    return (
        <div className="perp-breaker-banner" role="alert">
            <div className="perp-breaker-banner-content">
                <div className="perp-breaker-banner-icon">&#x26A0;</div>
                <div className="perp-breaker-banner-text">
                    <span className="perp-breaker-banner-title">CIRCUIT BREAKER ACTIVE</span>
                    <span className="perp-breaker-banner-desc">
                        Reduce-only mode enforced. No new positions or increases allowed.
                    </span>
                </div>
                <div className="perp-breaker-banner-epoch">
                    {breakerLastTriggerEpoch != null
                        ? `Triggered at epoch #${breakerLastTriggerEpoch}`
                        : 'Trigger epoch unavailable'}
                </div>
            </div>
        </div>
    );
}

export default PerpCircuitBreakerBanner;
