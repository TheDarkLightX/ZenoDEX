import { useState, useEffect, useCallback, useMemo } from 'react';
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

    const friendlyError = (() => {
        if (!error) return null;
        const raw = String(error);
        if (raw === 'timeout') {
            return 'Perpetuals data took too long to load. The local Tau node may be busy — try again in a moment.';
        }
        if (raw === 'tau_node_unreachable') {
            return 'The local Tau node is unreachable. Make sure the local-testnet stack is running, then retry.';
        }
        return `Could not load perpetuals data: ${raw}`;
    })();

    const [showConfirmOrder, setShowConfirmOrder] = useState(null);
    const [showCollateralModal, setShowCollateralModal] = useState(false);

    // The live 2-party clearinghouse market is operator-provisioned: only the two
    // counterparty pubkeys (account A/B) can trade it. A normal connected wallet
    // is an OBSERVER — surface that honestly instead of a silent dead-end CTA.
    const isObserver = useMemo(() => {
        if (demoMode || !wallet?.address || !selectedMarket) return false;
        if (selectedMarket.kind !== 'clearinghouse_2p_v1') return false;
        const norm = (v) => String(v || '').toLowerCase().replace(/^0x/, '');
        const w = norm(wallet.address);
        if (!w) return false;
        return w !== norm(selectedMarket.accountAPubkey) && w !== norm(selectedMarket.accountBPubkey);
    }, [demoMode, wallet, selectedMarket]);

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
    const liveSurfaceLabel = selectedMarket?.kind === 'clearinghouse_np_v1'
        ? 'Multi-party market'
        : 'Trading wallet';
    const riskKernelLabel = selectedMarket?.kind === 'clearinghouse_np_v1'
        ? 'Clearinghouse market'
        : 'Perpetuals market';
    const previewLabel = demoMode
        ? 'Demo market replay'
        : writeEnabled
            ? `${liveSurfaceLabel} · Trading enabled`
            : `${liveSurfaceLabel} · Wallet signature required`;
    const previewDetail = demoMode
        ? 'Uses sample data. Orders are simulated and not sent to the blockchain.'
        : writeEnabled
            ? 'Connects to the local blockchain. Trading is enabled.'
            : 'Connects to the local blockchain. Submissions require wallet approval.';

    // While the wallet status round-trip is in flight we used to early-return
    // a full-page spinner, which left the user staring at a blank screen for
    // ~3–6 s on local-testnet. Render the page layout immediately and show
    // an inline loading hint instead; the form/panels handle the empty-market
    // case on their own.
    const showInlineLoading = loading && markets.length === 0;

    // Build the preview grid as a reusable fragment so it can either be
    // rendered as the main surface (demo mode) or tucked inside a
    // collapsible disclosure (live mode).
    const previewGrid = (
        <>
            <div className="perp-market-bar">
                <div className="perp-market-header">
                    <div className="perp-title-block">
                        <h2 className="perp-title">{demoMode ? 'Perpetuals (demo)' : 'Perpetuals'}</h2>
                        <div className="perp-surface-badges" aria-label="Perpetuals surface scope">
                            <span className="perp-surface-badge">Market type: {liveSurfaceLabel}</span>
                            <span className="perp-surface-badge">Risk system: {riskKernelLabel}</span>
                            {!demoMode && (
                                <span className="perp-surface-badge perp-surface-badge-np">
                                    Privacy proof: requires separate testing
                                </span>
                            )}
                        </div>
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
                    <div className="perp-preview-lock-title">Wallet signature required</div>
                    <p className="perp-preview-lock-text">{writeLockReason}</p>
                </div>
            )}

            {!demoMode && writeEnabled && perpsPreviewWritesRequested && (
                <div className="perp-preview-lock perp-preview-lock-open" role="status">
                    <div className="perp-preview-lock-title">Local trading enabled</div>
                    <p className="perp-preview-lock-text">
                        Transactions are submitted to the local blockchain for processing.
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
                            isObserver={isObserver}
                        />
                    </div>
                    <button
                        className="btn btn-secondary perp-collateral-btn"
                        onClick={() => setShowCollateralModal(true)}
                        disabled={!wallet || isObserver || !writeEnabled}
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
                            isObserver={isObserver}
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

            {showInlineLoading && (
                <div className="perp-loading" role="status">Loading perpetuals data…</div>
            )}

            {/* Error Banner */}
            {error && (
                <div className="perp-error-banner" role="alert">
                    <span className="perp-error-banner-text">{friendlyError}</span>
                    <button
                        type="button"
                        className="perp-error-banner-retry"
                        onClick={() => loadMarkets()}
                    >
                        Retry
                    </button>
                </div>
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
