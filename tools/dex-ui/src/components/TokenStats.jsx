import { useCallback, useEffect, useMemo, useState } from 'react';
import { apiClaimTokenomicsActiveParticipantReward, apiGetTokenomicsStatus } from '../lib/api';
import { formatNumber, formatPercent } from '../lib/cpmm';
import './TokenStats.css';

const NA = 'N/A';

function finiteOrNull(value) {
    if (value == null || typeof value === 'boolean') return null;
    if (typeof value === 'string' && value.trim() === '') return null;
    const n = Number(value);
    return Number.isFinite(n) ? n : null;
}

function hasOwn(value, key) {
    return value != null && Object.prototype.hasOwnProperty.call(value, key);
}

function formatValueOrNA(value) {
    if (value == null) return NA;
    return formatNumber(value);
}

function formatBpsOrNA(value) {
    const n = finiteOrNull(value);
    if (n == null) return NA;
    return `${formatPercent(n / 10_000)} (${formatNumber(n, 0)} bps)`;
}

function shortHex(value) {
    const text = String(value || '');
    return text.length > 18 ? `${text.slice(0, 10)}...${text.slice(-6)}` : text;
}

function humanizeId(value) {
    return String(value || '')
        .replace(/_/g, ' ')
        .replace(/\b\w/g, (m) => m.toUpperCase());
}

function TokenStats() {
    const [liveState, setLiveState] = useState({ loading: false, data: null, error: null });
    const [claimState, setClaimState] = useState({ loading: false, data: null, error: null });

    useEffect(() => {
        const controller = new AbortController();
        const handle = window.setTimeout(() => {
            setLiveState((prev) => ({ ...prev, loading: true, error: null }));
            apiGetTokenomicsStatus({ signal: controller.signal, timeoutMs: 10_000 })
                .then((data) => {
                    if (!controller.signal.aborted) {
                        setLiveState({ loading: false, data, error: null });
                    }
                })
                .catch((err) => {
                    if (!controller.signal.aborted) {
                        setLiveState({ loading: false, data: null, error: err?.message || String(err) });
                    }
                });
        }, 0);
        return () => {
            controller.abort();
            window.clearTimeout(handle);
        };
    }, []);

    const liveStatus = liveState.data?.status || null;
    const initialSupply = finiteOrNull(liveStatus?.initial_supply);
    const minSupply = finiteOrNull(liveStatus?.supply_floor);
    const currentSupply = finiteOrNull(liveStatus?.current_supply);
    const burnedTotal = finiteOrNull(liveStatus?.burned_total);
    const tokenSymbol = liveStatus?.token_symbol || 'ZDEX';
    const checks = liveStatus?.checks && typeof liveStatus.checks === 'object' ? liveStatus.checks : {};
    const buybackMarket = liveStatus?.buyback_market_purchase && typeof liveStatus.buyback_market_purchase === 'object'
        ? liveStatus.buyback_market_purchase
        : null;
    const protocolFeeCapture = liveStatus?.protocol_fee_capture && typeof liveStatus.protocol_fee_capture === 'object'
        ? liveStatus.protocol_fee_capture
        : {};
    const buybackTotalSwapFee = finiteOrNull(liveStatus?.buyback_total_swap_fee);
    const buybackBurnedTotal = finiteOrNull(liveStatus?.buyback_burned_total);
    const buybackCarryAfter = finiteOrNull(liveStatus?.buyback_carry_after);
    const buybackEventCount = finiteOrNull(liveStatus?.buyback_event_count);
    const buybackShareBps = finiteOrNull(liveStatus?.buyback_share_bps);
    const protocolFeeShareBps = finiteOrNull(protocolFeeCapture?.share_bps);
    const buybackRuntimeEnabled = Boolean(
        buybackMarket?.runtime_enabled || checks.buyback_market_purchase_runtime_enabled,
    );
    const buybackRouteAvailable = Boolean(
        buybackMarket?.route_available || checks.buyback_market_route_available || buybackMarket?.available,
    );
    const buybackRuntimeBlocker = typeof buybackMarket?.runtime_blocker === 'string'
        ? buybackMarket.runtime_blocker
        : '';
    const buybackRuntimeMode = typeof buybackMarket?.runtime_mode === 'string'
        && buybackMarket.runtime_mode.trim()
        ? buybackMarket.runtime_mode.trim()
        : null;
    const hasBuybackMarketStatus = Boolean(
        (buybackMarket && [
            'runtime_enabled',
            'route_available',
            'available',
            'runtime_mode',
        ].some((key) => hasOwn(buybackMarket, key)))
        || hasOwn(checks, 'buyback_market_purchase_runtime_enabled')
        || hasOwn(checks, 'buyback_market_route_available'),
    );
    const marketPurchaseLabel = !hasBuybackMarketStatus
        ? NA
        : buybackRuntimeEnabled
            ? 'Enabled'
            : buybackRouteAvailable
                ? 'Route only'
                : 'Treasury burn only';

    const allocationRows = useMemo(
        () => (Array.isArray(liveStatus?.allocation_rows) ? liveStatus.allocation_rows : []),
        [liveStatus],
    );
    const programRows = useMemo(
        () => (Array.isArray(liveStatus?.active_participant_programs) ? liveStatus.active_participant_programs : []),
        [liveStatus],
    );
    const bootstrapRecipient = allocationRows.find((row) => row.id === 'liquidity_bootstrap_market_making')?.recipient_pubkey || '';
    const programById = useCallback(
        (programId) => programRows.find((row) => row.id === programId) || null,
        [programRows],
    );

    const submitRewardClaim = useCallback(async (programOrId = 'lp_liquidity_provider_rewards') => {
        const program = typeof programOrId === 'object' && programOrId !== null
            ? programOrId
            : programById(programOrId);
        const programId = program?.id || String(programOrId || 'lp_liquidity_provider_rewards');
        const eligibilityReceipts = Array.isArray(program?.eligibility_receipts)
            ? program.eligibility_receipts.filter(Boolean)
            : [];
        const defaultReceiptKind = eligibilityReceipts[0] || 'add_liquidity';
        const programClaimAmount = finiteOrNull(program?.claim_amount);
        setClaimState((prev) => ({ ...prev, loading: true, error: null }));
        const body = {
            program_id: programId,
            receipt_kind: defaultReceiptKind,
            time_ms: Date.now(),
            tx_id: `ui-tokenomics-claim-${Date.now()}`,
        };
        if (programClaimAmount != null) {
            body.amount = programClaimAmount;
        }
        if (bootstrapRecipient) {
            body.recipient_pubkey = bootstrapRecipient;
        }
        try {
            const data = await apiClaimTokenomicsActiveParticipantReward(body, { timeoutMs: 15_000 });
            setClaimState({ loading: false, data, error: null });
            apiGetTokenomicsStatus({ timeoutMs: 10_000 })
                .then((fresh) => setLiveState({ loading: false, data: fresh, error: null }))
                .catch(() => undefined);
        } catch (err) {
            setClaimState({ loading: false, data: null, error: err?.message || String(err) });
        }
    }, [bootstrapRecipient, programById]);

    const stats = useMemo(() => {
        return {
            burnedPercent: burnedTotal == null || initialSupply == null || initialSupply <= 0
                ? null
                : burnedTotal / initialSupply,
        };
    }, [burnedTotal, initialSupply]);

    const badgeText = liveState.loading
        ? 'Loading'
        : liveState.error
            ? 'Live error'
            : liveStatus
                ? 'Live network'
                : 'Live unavailable';

    return (
        <div className="token-stats">
            <div className="stats-header">
                <h2>
                    <span className="zdex-logo-inline">Z</span>
                    {tokenSymbol} Token Analytics
                </h2>
                <div className="live-badge">
                    <span className="live-dot"></span>
                    {badgeText}
                </div>
            </div>

            <div className="stats-honesty-banner" role="status">
                    {!liveStatus ? (
                        <>
                            <strong>Tokenomics endpoint unavailable.</strong>{' '}
                            {liveState.error || (liveState.loading ? 'Waiting for a live response.' : 'No live status was returned.')}
                            {' '}No bundled supply values are substituted.
                        </>
                    ) : (
                        <>
                            <strong>Live mode.</strong> {tokenSymbol} supply and allocation rows come from
                            ZenoLedger state. Active-participant reward claims are receipt-gated
                            transfers from the rewards controller. Buyback/burn rows are replayed
                            from accepted swap sidecars; market-purchase buyback is
                            {' '}{marketPurchaseLabel === NA ? 'unavailable' : marketPurchaseLabel.toLowerCase()} in this stack.
                        </>
                    )}
            </div>

            <div className="stats-grid grid grid-4">
                <div className="stat-card panel animate-slide-up" style={{ animationDelay: '0ms' }}>
                    <span className="stat-label">Current Supply</span>
                    <span className="stat-value">{formatValueOrNA(currentSupply)}</span>
                    <span className="stat-sub">of {formatValueOrNA(initialSupply)} initial</span>
                </div>
                <div className="stat-card panel animate-slide-up" style={{ animationDelay: '50ms' }}>
                    <span className="stat-label">Total Burned</span>
                    <span className="stat-value stat-burned">{formatValueOrNA(burnedTotal)}</span>
                    <span className="stat-sub">
                        {burnedTotal === 0
                            ? `no burns yet · height ${liveStatus?.height ?? '—'}`
                            : (stats.burnedPercent == null ? NA : `${formatPercent(stats.burnedPercent)} of initial`)}
                    </span>
                </div>
                <div className="stat-card panel animate-slide-up" style={{ animationDelay: '100ms' }}>
                    <span className="stat-label">Buyback Fee Pool</span>
                    <span className="stat-value stat-pool">{formatValueOrNA(buybackTotalSwapFee)}</span>
                    <span className="stat-sub">cumulative swap fee feeding buyback</span>
                </div>
                <div className="stat-card panel animate-slide-up" style={{ animationDelay: '150ms' }}>
                    <span className="stat-label">Buyback Events</span>
                    <span className="stat-value">{formatValueOrNA(buybackEventCount)}</span>
                    <span className="stat-sub">accepted burn sidecars</span>
                </div>
            </div>

            <div className="supply-progress panel animate-slide-up" style={{ animationDelay: '200ms' }}>
                <div className="progress-header">
                    <span>Supply Progression</span>
                    <span>
                        {currentSupply == null ? NA : formatNumber(currentSupply)}
                        {' -> '}{formatValueOrNA(minSupply)} floor
                    </span>
                </div>
                {currentSupply == null || burnedTotal == null || initialSupply == null
                || initialSupply <= 0 || minSupply == null ? (
                    <p className="model-note">Live {tokenSymbol} supply metrics are waiting for the network endpoint.</p>
                ) : (
                    <>
                        <div className="progress-bar-container">
                            <div
                                className="progress-bar burned"
                                style={{ width: `${Math.max(0, Math.min(100, (burnedTotal / initialSupply) * 100))}%` }}
                            ></div>
                            <div
                                className="progress-bar remaining"
                                style={{ width: `${Math.max(0, Math.min(100, ((currentSupply - minSupply) / initialSupply) * 100))}%` }}
                            ></div>
                            <div
                                className="progress-bar floor"
                                style={{ width: `${Math.max(0, Math.min(100, (minSupply / initialSupply) * 100))}%` }}
                            ></div>
                        </div>
                        <div className="progress-legend">
                            <span><span className="legend-dot burned"></span> Burned ({formatPercent(burnedTotal / initialSupply)})</span>
                            <span><span className="legend-dot remaining"></span> Burnable ({formatPercent(Math.max(0, currentSupply - minSupply) / initialSupply)})</span>
                            <span><span className="legend-dot floor"></span> Floor ({formatPercent(minSupply / initialSupply)})</span>
                        </div>
                    </>
                )}
            </div>

            {allocationRows.length > 0 && (
                <div className="tokenomics-ledger panel animate-slide-up" style={{ animationDelay: '240ms' }}>
                    <div className="tokenomics-ledger-header">
                        <h3>Network Distribution</h3>
                        <span className={checks.tau_policy_flags_all_pass ? 'check-ok' : 'check-warn'}>
                            Tau guard {checks.tau_policy_flags_all_pass ? 'passed' : 'pending'}
                        </span>
                    </div>
                    <div className="allocation-table" role="table" aria-label="Token allocation balances">
                        <div className="allocation-row allocation-head" role="row">
                            <span>Bucket</span>
                            <span>Controller</span>
                            <span>Initial</span>
                            <span>Current</span>
                        </div>
                        {allocationRows.map((row) => (
                            <div className="allocation-row" role="row" key={row.id}>
                                <span>
                                    <strong>{humanizeId(row.id)}</strong>
                                    <small>{humanizeId(row.category)}</small>
                                </span>
                                <span title={row.recipient_pubkey}>{row.recipient_role} · {shortHex(row.recipient_pubkey)}</span>
                                <span>{formatValueOrNA(finiteOrNull(row.initial_amount))}</span>
                                <span>{formatValueOrNA(finiteOrNull(row.current_balance))}</span>
                            </div>
                        ))}
                    </div>
                </div>
            )}

            {programRows.length > 0 && (
                <div className="tokenomics-ledger panel animate-slide-up" style={{ animationDelay: '260ms' }}>
                    <div className="tokenomics-ledger-header">
                        <h3>Active-Participant Reward Budgets</h3>
                        <span className={checks.active_participant_programs_sum_to_pool ? 'check-ok' : 'check-warn'}>
                            Budget sum {checks.active_participant_programs_sum_to_pool ? 'valid' : 'pending'}
                        </span>
                    </div>
                    <div className="program-grid">
                        {programRows.map((row) => {
                            const budgetAmount = finiteOrNull(row.budget_amount);
                            const claimedAmount = finiteOrNull(row.claimed_amount);
                            const remainingAmount = finiteOrNull(row.remaining_amount);
                            const claimAmount = finiteOrNull(row.claim_amount);
                            return (
                                <div className="program-item" key={row.id}>
                                    <span>{humanizeId(row.category)}</span>
                                    <strong>{formatValueOrNA(budgetAmount)} {tokenSymbol}</strong>
                                    <span className="program-claim-line">
                                        {formatValueOrNA(claimedAmount)} claimed · {formatValueOrNA(remainingAmount)} remaining
                                    </span>
                                    {claimAmount != null && (
                                        <span className="program-claim-line">
                                            {formatNumber(claimAmount)} per eligible receipt
                                        </span>
                                    )}
                                    <small>{(row.eligibility_receipts || []).map(humanizeId).join(', ')}</small>
                                    <button
                                        type="button"
                                        className="claim-button"
                                        disabled={claimState.loading || remainingAmount == null || remainingAmount <= 0}
                                        onClick={() => submitRewardClaim(row)}
                                    >
                                        {claimState.loading ? 'Claiming' : 'Claim next eligible receipt'}
                                    </button>
                                </div>
                            );
                        })}
                    </div>
                    {(claimState.data || claimState.error) && (
                        <div className={claimState.error ? 'claim-status claim-error' : 'claim-status claim-ok'} role="status">
                            {claimState.error ? claimState.error : `Claim accepted at height ${claimState.data?.height}`}
                        </div>
                    )}
                </div>
            )}

            <div className="burn-mechanics grid grid-2">
                <div className="panel animate-slide-up" style={{ animationDelay: '300ms' }}>
                    <h3>Live Buyback/Burn Ledger</h3>
                    <div className="mechanic-list">
                        <div className="mechanic-item">
                            <span className="mechanic-label">Protocol Fee Capture</span>
                            <span className="mechanic-value">{formatBpsOrNA(protocolFeeShareBps)}</span>
                        </div>
                        <div className="mechanic-item">
                            <span className="mechanic-label">Buyback Burn Share</span>
                            <span className="mechanic-value">{formatBpsOrNA(buybackShareBps)}</span>
                        </div>
                        <div className="mechanic-item">
                            <span className="mechanic-label">Burned From Buyback</span>
                            <span className="mechanic-value">{formatValueOrNA(buybackBurnedTotal)}</span>
                        </div>
                        <div className="mechanic-item">
                            <span className="mechanic-label">Carry After</span>
                            <span className="mechanic-value">{formatValueOrNA(buybackCarryAfter)}</span>
                        </div>
                        <div className="mechanic-item">
                            <span className="mechanic-label">Market Purchase</span>
                            <span className="mechanic-value">{marketPurchaseLabel}</span>
                        </div>
                    </div>
                </div>

                <div className="panel animate-slide-up" style={{ animationDelay: '340ms' }}>
                    <h3>Zeno Supply Model</h3>
                    <p className="model-desc">
                        {tokenSymbol} supply, buyback carry, and burn totals are read from ZenoLedger.{' '}
                        {buybackRuntimeMode
                            ? `This network reports ${buybackRuntimeMode} for buyback accounting${buybackRuntimeBlocker ? ` (${buybackRuntimeBlocker})` : ''}.`
                            : 'The live buyback accounting mode is unavailable.'}
                    </p>
                    <dl className="model-params">
                        <div className="model-param">
                            <dt>Buyback share</dt>
                            <dd className="mono">{buybackShareBps != null ? `${(buybackShareBps / 100).toFixed(2)}%` : '—'} of protocol fees</dd>
                        </div>
                        <div className="model-param">
                            <dt>Protocol fee capture</dt>
                            <dd className="mono">{protocolFeeShareBps != null ? `${(protocolFeeShareBps / 100).toFixed(2)}%` : '—'}</dd>
                        </div>
                        <div className="model-param">
                            <dt>Supply floor</dt>
                            <dd className="mono">{formatValueOrNA(minSupply)} {tokenSymbol}</dd>
                        </div>
                        <div className="model-param">
                            <dt>Carry after buyback</dt>
                            <dd className="mono">{buybackCarryAfter != null ? formatNumber(buybackCarryAfter) : '—'}</dd>
                        </div>
                    </dl>
                    <p className="model-note">
                        Supply contracts via fee-funded buyback-and-burn (not a per-transfer tax), floored at the protected supply floor. Burn totals are read from ZenoLedger.
                    </p>
                </div>
            </div>

            <div className="burn-chart panel animate-slide-up" style={{ animationDelay: '380ms' }}>
                <h3>Supply Over Time</h3>
                <p className="model-note">
                    Live chart buckets are pending. Current burn totals and buyback event counts are shown from
                    accepted ledger sidecars above.
                </p>
            </div>

            <div className="stats-footer">
                <p>
                    {!liveStatus ? (
                        <>
                            <span className="verified-badge verified-badge-advisory">Tau status unavailable</span>
                            No policy-enforcement claim is made without live network status.
                        </>
                    ) : liveStatus.tau_policy?.mode !== 'host_computed_flags' ? (
                        <>
                            <span className="verified-badge">Tau-Gated</span>
                            Distribution manifest and network reward-claim rails are guarded.
                        </>
                    ) : (
                        <>
                            <span className="verified-badge verified-badge-advisory">Tau-Gated (host-computed)</span>
                            Distribution and reward-claim guard flags are host-computed from network state against
                            spec <code>{liveStatus?.tau_policy?.policy_id || 'protocol_token_distribution_guard_v1'}</code> — not Tau-runtime-enforced in this environment.
                        </>
                    )}
                </p>
            </div>
        </div>
    );
}

export default TokenStats;
