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
import VerifiedBySpec from '../VerifiedBySpec.jsx';
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

    // The Perpetuals tab contains the trader-facing UI (preview grid) and a
    // low-level operator console (Live Wallet). The trader surface is the
    // headline in both modes. The operator console only appears in live mode,
    // tucked behind a disclosure so it isn't mistaken for the trader UI.
    const previewLabel = demoMode
        ? 'Demo market replay'
        : writeEnabled
            ? 'Live · writes enabled'
            : 'Live · read-only';
    const previewDetail = demoMode
        ? 'Uses bundled market, position, and history data. Orders stay inside the UI state model.'
        : writeEnabled
            ? 'Reads from the Tau node. Order writes still route through the operator console below.'
            : 'Reads from the Tau node. Order writes are exposed in the Operator console disclosure below.';

    if (loading && markets.length === 0) {
        return (
            <div className="perp-trading-view">
                <div className="perp-loading">Loading perpetuals data...</div>
            </div>
        );
    }

    // Build the preview grid as a reusable fragment so it can either be
    // rendered as the main surface (demo mode) or tucked inside a
    // collapsible disclosure (live mode).
    const previewGrid = (
        <>
            <div className="perp-market-bar">
                <div className="perp-market-header">
                    <div className="perp-title-block">
                        <h2 className="perp-title">{demoMode ? 'Perpetuals (demo)' : 'Perpetuals'}</h2>
                        <VerifiedBySpec
                            spec="perp_epoch_isolated_v3"
                            kind="esso"
                            title="Perpetuals margin and epoch lifecycle are verified by ESSO state machine perp_epoch_isolated_v3 (Z3 + CVC5)."
                        />
                        <p className="perp-subtitle">{previewDetail}</p>
                    </div>
                    <span className="perp-posture-chip">{previewLabel}</span>
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

            {/* Account Summary */}
            {wallet && (
                <PerpAccountSummary
                    markets={markets}
                    positions={positions}
                />
            )}

            {/* 3-Column Trading Grid */}
            <div className="perp-grid">
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
                    <button
                        className="btn btn-secondary perp-collateral-btn"
                        onClick={() => setShowCollateralModal(true)}
                        disabled={!wallet || !writeEnabled}
                    >
                        Manage Collateral
                    </button>
                </div>

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
        </>
    );

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

            {/* Headline in both modes: the trader-facing perps grid.
                In live mode the raw stream-8 operator console is available
                behind a disclosure for market makers / operators. */}
            {previewGrid}
            {!demoMode && (
                <details className="perp-preview-disclosure">
                    <summary className="perp-preview-disclosure-summary">
                        <span className="perp-preview-disclosure-label">Operator console</span>
                        <span className="perp-preview-disclosure-hint">
                            Raw stream-8 protocol primitives — init 2P market, advance epoch,
                            publish clearing price, settle epoch, partial liquidate. For market
                            operators, not normal traders.
                        </span>
                    </summary>
                    <div className="perp-preview-disclosure-body">
                        <PerpLiveWalletSurface />
                    </div>
                </details>
            )}

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
