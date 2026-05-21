import { useState, useEffect, useCallback } from 'react';
import { usePerps } from '../../lib/PerpContext.jsx';
import PerpMarketSelector from './PerpMarketSelector.jsx';
import PerpPriceTicker from './PerpPriceTicker.jsx';
import PerpEpochIndicator from './PerpEpochIndicator.jsx';
import PerpOrderForm from './PerpOrderForm.jsx';
import PerpConfirmOrderModal from './PerpConfirmOrderModal.jsx';
import PerpPositionPanel from './PerpPositionPanel.jsx';
import PerpCollateralModal from './PerpCollateralModal.jsx';
import PerpAccountSummary from './PerpAccountSummary.jsx';
import PerpCircuitBreakerBanner from './PerpCircuitBreakerBanner.jsx';
import PerpInsuranceFundPanel from './PerpInsuranceFundPanel.jsx';
import PerpTradeHistory from './PerpTradeHistory.jsx';
import PerpLiveWalletSurface from './PerpLiveWalletSurface.jsx';
import { useDemoMode } from '../../lib/DemoModeContext.jsx';
import './PerpTradingView.css';

/**
 * PerpTradingView - Main perpetuals trading layout
 *
 * 3-column grid (desktop):
 * [Order Form] [Price Panel + Epoch] [Account Panel]
 *
 * Collapses to single column on mobile.
 * Wires all perps components via PerpContext.
 */
function PerpTradingView({ wallet }) {
    const { demoMode } = useDemoMode();
    const {
        markets,
        selectedMarket,
        selectedMarketId,
        currentPosition,
        positionDerived,
        positions,
        history,
        loading,
        error,
        writeEnabled,
        writeLockReason,
        perpsPreviewWritesRequested,
        loadMarkets,
        selectMarket,
        setPosition,
        depositCollateral,
        withdrawCollateral,
    } = usePerps();

    const [showConfirmOrder, setShowConfirmOrder] = useState(null);
    const [showCollateralModal, setShowCollateralModal] = useState(false);

    // Load markets on mount
    useEffect(() => {
        loadMarkets();
    }, [loadMarkets]);

    const handleOrderSubmit = useCallback((order) => {
        setPosition(order.marketId, order.newPositionBase);
    }, [setPosition]);

    const handleShowConfirm = useCallback((orderDetails) => {
        setShowConfirmOrder(orderDetails);
    }, []);

    const handleConfirmOrder = useCallback((order) => {
        setPosition(order.marketId, order.newPositionBase);
        setShowConfirmOrder(null);
    }, [setPosition]);

    const postureLabel = demoMode
        ? 'Demo market replay'
        : writeEnabled
            ? 'Local preview writes'
            : 'Read-only preview';
    const postureDetail = demoMode
        ? 'Uses bundled market, position, and history data. Orders stay inside the UI state model.'
        : writeEnabled
            ? 'Uses the mounted /api/perps surface for local preview writes. This lane is still a development surface and not an authoritative settlement path.'
            : 'Uses the mounted /api/perps surface for market data preview only. Write actions stay locked until an authoritative perps transaction path is mounted.';

    if (loading && markets.length === 0) {
        return (
            <div className="perp-trading-view">
                <div className="perp-loading">Loading perpetuals data...</div>
            </div>
        );
    }

    return (
        <div className="perp-trading-view">
            {/* Circuit Breaker Banner */}
            {selectedMarket?.breakerActive && (
                <PerpCircuitBreakerBanner
                    breakerActive={true}
                    breakerLastTriggerEpoch={selectedMarket.breakerLastTriggerEpoch ?? 0}
                />
            )}

            {/* Error Banner */}
            {error && (
                <div className="perp-error-banner">Error: {error}</div>
            )}

            {/* Market Selector */}
            <div className="perp-market-bar">
                <div className="perp-market-header">
                    <div>
                        <h2 className="perp-title">Perpetuals</h2>
                        <p className="perp-subtitle">{postureDetail}</p>
                    </div>
                    <span className="perp-posture-chip">{postureLabel}</span>
                </div>
                <PerpMarketSelector
                    markets={markets}
                    selectedMarketId={selectedMarketId}
                    onSelect={selectMarket}
                />
            </div>

            {!demoMode && !writeEnabled && (
                <div className="perp-preview-lock" role="status">
                    <div className="perp-preview-lock-title">Preview writes disabled</div>
                    <p className="perp-preview-lock-text">{writeLockReason}</p>
                </div>
            )}

            {!demoMode && writeEnabled && perpsPreviewWritesRequested && (
                <div className="perp-preview-lock perp-preview-lock-open" role="status">
                    <div className="perp-preview-lock-title">Local preview writes enabled</div>
                    <p className="perp-preview-lock-text">
                        This lane is for controlled local UI development. It does not prove authoritative perps settlement.
                    </p>
                </div>
            )}

            {!demoMode && (
                <PerpLiveWalletSurface />
            )}

            {/* Account Summary */}
            {wallet && (
                <PerpAccountSummary
                    markets={markets}
                    positions={positions}
                />
            )}

            {/* 3-Column Trading Grid */}
            <div className="perp-grid">
                {/* Left: Order Form */}
                <div className="perp-col perp-col-order">
                    <div className="panel">
                        <h3 className="perp-section-title">Trade</h3>
                        <PerpOrderForm
                            market={selectedMarket}
                            position={currentPosition}
                            wallet={wallet}
                            writeEnabled={writeEnabled}
                            writeLockReason={writeLockReason}
                            onSubmit={handleOrderSubmit}
                            onShowConfirm={handleShowConfirm}
                        />
                    </div>

                    {/* Collateral Button */}
                    <button
                        className="btn btn-secondary perp-collateral-btn"
                        onClick={() => setShowCollateralModal(true)}
                        disabled={!wallet || !writeEnabled}
                    >
                        Manage Collateral
                    </button>
                </div>

                {/* Center: Price + Epoch + Insurance */}
                <div className="perp-col perp-col-price">
                    <div className="panel">
                        <h3 className="perp-section-title">Market Data</h3>
                        <PerpPriceTicker market={selectedMarket} />
                    </div>
                    <PerpEpochIndicator market={selectedMarket} />
                    <PerpInsuranceFundPanel
                        market={selectedMarket}
                        wallet={wallet}
                        writeEnabled={writeEnabled}
                        writeLockReason={writeLockReason}
                    />
                </div>

                {/* Right: Account */}
                <div className="perp-col perp-col-account">
                    <div className="panel">
                        <PerpPositionPanel
                            market={selectedMarket}
                            position={currentPosition}
                            derived={positionDerived}
                        />
                    </div>
                </div>
            </div>

            {/* Trade History */}
            <PerpTradeHistory history={history} />

            {/* Modals */}
            {showConfirmOrder && (
                <PerpConfirmOrderModal
                    order={showConfirmOrder}
                    market={selectedMarket}
                    onConfirm={handleConfirmOrder}
                    onClose={() => setShowConfirmOrder(null)}
                />
            )}

            {showCollateralModal && (
                <PerpCollateralModal
                    market={selectedMarket}
                    position={currentPosition}
                    wallet={wallet}
                    onDeposit={depositCollateral}
                    onWithdraw={withdrawCollateral}
                    onClose={() => setShowCollateralModal(false)}
                />
            )}
        </div>
    );
}

export default PerpTradingView;
