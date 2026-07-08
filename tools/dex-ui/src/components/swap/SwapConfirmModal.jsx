// Copyright DarkLightX/Dana Edwards
import Modal from '../Modal.jsx';
import { formatNumber, formatPercent } from '../../lib/cpmm';

/**
 * SwapConfirmModal — poka-yoke confirmation dialog for high-impact swaps.
 *
 * Receives a single `ctx` object bundling all the confirm/pokayoke state
 * from the parent, plus callbacks. This avoids 31+ individual props.
 */
function SwapConfirmModal({
    open,
    activePreview,
    amountIn,
    fromToken,
    toToken,
    advancedMode,
    effectiveProfileLabel,
    confirmConfig,
    typedConfirmText,
    onTypedConfirmTextChange,
    pokayokeEnabled,
    apiSlippageAdvice,
    slippage,
    onApplySlippage,
    pokayokeSuggesting,
    onFindSaferAmount,
    pokayokeHeavySuggesting,
    onFindSaferAmountDeep,
    pokayokeSuggestError,
    pokayokeSuggestions,
    pokayokeHeavySuggestError,
    pokayokeHeavySuggestions,
    onApplySuggestedAmount,
    onClose,
    onProceed,
    isSubmitting,
}) {
    if (!open || !activePreview) return null;

    const closeAndReset = () => {
        onTypedConfirmTextChange('');
        onClose();
    };

    return (
        <Modal
            open
            onClose={closeAndReset}
            title={confirmConfig?.title || 'Confirm Swap'}
            size="sm"
        >
            <p>This swap has a <strong className="impact-high">{formatPercent(activePreview.priceImpact)}</strong> price impact.</p>
            <div className="confirm-details">
                <div className="confirm-row">
                    <span>You pay:</span>
                    <span>{amountIn} {fromToken.symbol}</span>
                </div>
                <div className="confirm-row">
                    <span>You receive (min):</span>
                    <span>{formatNumber(activePreview.minOutput)} {toToken.symbol}</span>
                </div>
                <div className="confirm-row">
                    <span>Route:</span>
                    <span>{activePreview.routePath}</span>
                </div>
                {advancedMode && (
                    <div className="confirm-row">
                        <span>Profile:</span>
                        <span>{effectiveProfileLabel}</span>
                    </div>
                )}
            </div>
            {Array.isArray(confirmConfig?.messages) && confirmConfig.messages.length > 0 && (
                <div className="confirm-warning">
                    {confirmConfig.messages.map((m, idx) => (
                        <p key={`${idx}-${String(m).slice(0, 24)}`}>{String(m)}</p>
                    ))}
                </div>
            )}
            {confirmConfig?.requireTyped && (
                <div className="confirm-typed">
                    <p className="confirm-warning">
                        Type <strong>{confirmConfig.typedPhrase}</strong> to proceed.
                    </p>
                    <input
                        type="text"
                        value={typedConfirmText}
                        onChange={(e) => onTypedConfirmTextChange(e.target.value)}
                        placeholder={String(confirmConfig.typedPhrase || 'PROCEED')}
                    />
                </div>
            )}

            {!advancedMode && pokayokeEnabled && (
                <div className="confirm-suggest">
                    <div className="confirm-suggest-actions">
                        {(() => {
                            const reasons = Array.isArray(confirmConfig?.reasons) ? confirmConfig.reasons : [];
                            const recRevert = Number(apiSlippageAdvice?.recommendedSlippageBpsRevertSafe);
                            const recMev = Number(apiSlippageAdvice?.recommendedSlippageBpsMevSafe);
                            const userSlippageBps = Math.max(0, Math.min(10_000, Math.round(Number(slippage || 0) * 10_000)));
                            const actions = [];
                            if (reasons.includes('slippage_below_revert_safe') && Number.isFinite(recRevert) && recRevert >= 0 && recRevert <= 10_000) {
                                actions.push({
                                    key: 'use_revert_safe_slippage',
                                    label: `Apply revert-bound slippage (${(recRevert / 100).toFixed(2)}%)`,
                                    onClick: () => onApplySlippage(recRevert / 10_000),
                                });
                            }
                            if (reasons.includes('slippage_above_mev_safe') && Number.isFinite(recMev) && recMev >= 0 && recMev <= 10_000 && userSlippageBps > recMev) {
                                actions.push({
                                    key: 'use_mev_safe_slippage',
                                    label: `Use safer price protection (${(recMev / 100).toFixed(2)}%)`,
                                    onClick: () => onApplySlippage(recMev / 10_000),
                                });
                            }
                            if (actions.length === 0) return null;
                            return actions.map((a) => (
                                <button
                                    key={a.key}
                                    className="btn btn-secondary"
                                    type="button"
                                    onClick={a.onClick}
                                >
                                    {a.label}
                                </button>
                            ));
                        })()}
                        <button
                            className="btn btn-secondary"
                            type="button"
                            onClick={onFindSaferAmount}
                            disabled={pokayokeSuggesting}
                        >
                            {pokayokeSuggesting ? 'Calculating...' : 'Calculate Smaller Amount'}
                        </button>
                        {(() => {
                            const reasons = Array.isArray(confirmConfig?.reasons) ? confirmConfig.reasons : [];
                            const showDeep = reasons.includes('mev_conflict') || reasons.includes('inconclusive_mev');
                            if (!showDeep) return null;
                            return (
                                <button
                                    className="btn btn-secondary"
                                    type="button"
                                    onClick={onFindSaferAmountDeep}
                                    disabled={pokayokeHeavySuggesting}
                                >
                                    {pokayokeHeavySuggesting ? 'Calculating...' : 'Advanced Safety Analysis'}
                                </button>
                            );
                        })()}
                    </div>
                    {pokayokeSuggestError && (
                        <div className="swap-notice">{pokayokeSuggestError}</div>
                    )}
                    {pokayokeSuggestions && (() => {
                        const reasons = Array.isArray(confirmConfig?.reasons) ? confirmConfig.reasons : [];
                        const roundedIn = Math.max(1, Math.round(Number.parseFloat(amountIn || '0') || 0));
                        const items = [];
                        const addItem = (key, label) => {
                            const s = pokayokeSuggestions?.[key];
                            const amt = s?.suggested_amount_in;
                            if (!s || String(s.status) !== 'ok' || amt === null || amt === undefined) return;
                            const a = Number(amt);
                            if (!Number.isFinite(a) || a <= 0 || a >= roundedIn) return;
                            items.push({ key, label, amount: Math.trunc(a) });
                        };
                        if (reasons.includes('high_price_impact') || reasons.includes('legacy_high_impact')) {
                            addItem('impact_lt_500_bps', 'Reduce impact <5%');
                        }
                        if (reasons.includes('moderate_price_impact')) {
                            addItem('impact_lt_100_bps', 'Reduce impact <1%');
                        }
                        if (reasons.includes('slippage_below_revert_safe') || reasons.includes('no_revert_safe_option')) {
                            addItem('required_slippage_le_user_bps', 'Match your slippage');
                            addItem('required_slippage_le_max_option_bps', 'Match max option slippage');
                        }
                        // If no reason-specific row matches, show the primary impact-bound amount as a fallback.
                        if (items.length === 0) {
                            addItem('impact_lt_500_bps', 'Reduce impact <5%');
                        }
                        if (items.length === 0) return null;
                        return (
                            <div className="confirm-suggest-items">
                                {items.map((it) => (
                                    <button
                                        key={it.key}
                                        className="btn btn-secondary"
                                        type="button"
                                        onClick={() => onApplySuggestedAmount(it.amount)}
                                    >
                                        {it.label}: {it.amount}
                                    </button>
                                ))}
                            </div>
                        );
                    })()}
                    {pokayokeHeavySuggestError && (
                        <div className="swap-notice">{pokayokeHeavySuggestError}</div>
                    )}
                    {pokayokeHeavySuggestions && (() => {
                        if (!Array.isArray(pokayokeHeavySuggestions)) return null;
                        const roundedIn = Math.max(1, Math.round(Number.parseFloat(amountIn || '0') || 0));
                        const items = [];
                        for (const row of pokayokeHeavySuggestions) {
                            if (!row || String(row.status) !== 'ok') continue;
                            const amt = row.suggested_amount_in;
                            if (amt === null || amt === undefined) continue;
                            const a = Number(amt);
                            if (!Number.isFinite(a) || a <= 0 || a >= roundedIn) continue;
                            const ta = String(row.target_action || '').trim().toLowerCase();
                            if (ta !== 'confirm' && ta !== 'allow') continue;
                            const label = ta === 'allow' ? 'Deep: Reduce to Allow' : 'Deep: Reduce to Confirm';
                            items.push({ key: `deep-${ta}`, label, amount: Math.trunc(a) });
                        }
                        if (items.length === 0) return null;
                        return (
                            <div className="confirm-suggest-items">
                                {items.map((it) => (
                                    <button
                                        key={it.key}
                                        className="btn btn-secondary"
                                        type="button"
                                        onClick={() => onApplySuggestedAmount(it.amount)}
                                    >
                                        {it.label}: {it.amount}
                                    </button>
                                ))}
                            </div>
                        );
                    })()}
                </div>
            )}
            <div className="confirm-actions">
                <button
                    className="btn btn-secondary"
                    onClick={closeAndReset}
                >
                    Cancel
                </button>
                <button
                    className="btn btn-primary btn-warning"
                    onClick={onProceed}
                    disabled={
                        isSubmitting ||
                        (confirmConfig?.requireTyped && String(typedConfirmText || '').trim().toUpperCase() !== String(confirmConfig?.typedPhrase || '').trim().toUpperCase())
                    }
                >
                    {isSubmitting ? 'Submitting...' : (confirmConfig?.proceedText || 'Proceed Anyway')}
                </button>
            </div>
        </Modal>
    );
}

export default SwapConfirmModal;
