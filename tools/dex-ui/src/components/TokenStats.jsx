import { useCallback, useEffect, useMemo, useState } from 'react';
import { apiClaimTokenomicsActiveParticipantReward, apiGetTokenomicsStatus } from '../lib/api';
import { formatNumber, formatPercent } from '../lib/cpmm';
import { useDemoMode } from '../lib/DemoModeContext.jsx';
import { FALLBACK_BURN_HISTORY as DEMO_BURN_HISTORY, FALLBACK_ZDEX_STATS as DEMO_ZDEX_STATS } from '../lib/mockData.js';
import './TokenStats.css';

const DEFAULT_INITIAL_SUPPLY = 1_000_000;
const DEFAULT_MIN_SUPPLY = 100_000;
const BURN_RATE = 0.005;
const NA = 'N/A';

function finiteOrNull(value) {
    const n = Number(value);
    return Number.isFinite(n) ? n : null;
}

function formatValueOrNA(value) {
    if (value == null) return NA;
    return formatNumber(value);
}

function formatDollarOrNA(value) {
    if (value == null) return NA;
    return `$${formatNumber(value)}`;
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

function queryValue(name) {
    if (typeof window === 'undefined') return null;
    const params = new URLSearchParams(window.location.search);
    return params.get(name);
}

function TokenStats() {
    const { demoMode } = useDemoMode();
    const [liveState, setLiveState] = useState({ loading: false, data: null, error: null });
    const [claimState, setClaimState] = useState({ loading: false, data: null, error: null, smokeStarted: false });

    useEffect(() => {
        if (demoMode) {
            const handle = window.setTimeout(() => {
                setLiveState({ loading: false, data: null, error: null });
            }, 0);
            return () => window.clearTimeout(handle);
        }
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
    }, [demoMode]);

    const liveStatus = liveState.data?.status || null;
    const demoCurrentSupply = finiteOrNull(DEMO_ZDEX_STATS?.currentSupply);
    const demoBurnedTotal = finiteOrNull(DEMO_ZDEX_STATS?.burnedTotal);
    const demoBuybackPool = finiteOrNull(DEMO_ZDEX_STATS?.buybackPool);
    const demoDailyVolume = finiteOrNull(DEMO_ZDEX_STATS?.dailyVolume);

    const initialSupply = demoMode ? DEFAULT_INITIAL_SUPPLY : (finiteOrNull(liveStatus?.initial_supply) ?? DEFAULT_INITIAL_SUPPLY);
    const minSupply = demoMode ? DEFAULT_MIN_SUPPLY : (finiteOrNull(liveStatus?.supply_floor) ?? DEFAULT_MIN_SUPPLY);
    const currentSupply = demoMode ? demoCurrentSupply : finiteOrNull(liveStatus?.current_supply);
    const burnedTotal = demoMode ? demoBurnedTotal : finiteOrNull(liveStatus?.burned_total);
    const buybackPool = demoMode ? demoBuybackPool : null;
    const dailyVolume = demoMode ? demoDailyVolume : null;
    const tokenSymbol = demoMode ? 'ZDEX' : (liveStatus?.token_symbol || 'ZDEX');
    const checks = liveStatus?.checks && typeof liveStatus.checks === 'object' ? liveStatus.checks : {};
    const buybackMarket = liveStatus?.buyback_market_purchase && typeof liveStatus.buyback_market_purchase === 'object'
        ? liveStatus.buyback_market_purchase
        : {};
    const protocolFeeCapture = liveStatus?.protocol_fee_capture && typeof liveStatus.protocol_fee_capture === 'object'
        ? liveStatus.protocol_fee_capture
        : {};
    const buybackTotalSwapFee = demoMode ? null : finiteOrNull(liveStatus?.buyback_total_swap_fee);
    const buybackBurnedTotal = demoMode ? null : finiteOrNull(liveStatus?.buyback_burned_total);
    const buybackCarryAfter = demoMode ? null : finiteOrNull(liveStatus?.buyback_carry_after);
    const buybackEventCount = demoMode ? null : finiteOrNull(liveStatus?.buyback_event_count);
    const buybackShareBps = demoMode ? 5000 : finiteOrNull(liveStatus?.buyback_share_bps);
    const protocolFeeShareBps = demoMode ? 3000 : finiteOrNull(protocolFeeCapture?.share_bps);
    const buybackRuntimeEnabled = Boolean(
        buybackMarket?.runtime_enabled || checks.buyback_market_purchase_runtime_enabled,
    );
    const buybackRouteAvailable = Boolean(
        buybackMarket?.route_available || checks.buyback_market_route_available || buybackMarket?.available,
    );
    const buybackRuntimeBlocker = typeof buybackMarket?.runtime_blocker === 'string'
        ? buybackMarket.runtime_blocker
        : '';

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
        if (demoMode) return;
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
        const sourceHeight = queryValue('rewardSourceHeight');
        const rewardRecipient = queryValue('rewardRecipient');
        const rewardAmount = queryValue('rewardAmount');
        const body = {
            program_id: programId,
            receipt_kind: queryValue('rewardReceiptKind') || defaultReceiptKind,
            time_ms: Date.now(),
            tx_id: `ui-tokenomics-claim-${Date.now()}`,
        };
        if (rewardAmount != null) {
            body.amount = Number(rewardAmount);
        } else if (programClaimAmount != null) {
            body.amount = programClaimAmount;
        }
        if (sourceHeight) {
            body.source_height = Number(sourceHeight);
            body.source_tx_index = Number(queryValue('rewardSourceTxIndex') || 0);
            const recipient = rewardRecipient || bootstrapRecipient;
            body.recipient_pubkey = recipient;
        } else if (rewardRecipient) {
            body.recipient_pubkey = rewardRecipient;
        }
        try {
            const data = await apiClaimTokenomicsActiveParticipantReward(body, { timeoutMs: 15_000 });
            setClaimState({ loading: false, data, error: null, smokeStarted: true });
            apiGetTokenomicsStatus({ timeoutMs: 10_000 })
                .then((fresh) => setLiveState({ loading: false, data: fresh, error: null }))
                .catch(() => undefined);
        } catch (err) {
            setClaimState({ loading: false, data: null, error: err?.message || String(err), smokeStarted: true });
        }
    }, [bootstrapRecipient, demoMode, programById]);

    useEffect(() => {
        if (demoMode || claimState.smokeStarted || !liveStatus) return;
        if (queryValue('zenodexUiSmokeTokenomicsClaim') !== '1') return;
        const programId = queryValue('rewardProgramId') || 'lp_liquidity_provider_rewards';
        const handle = window.setTimeout(() => {
            submitRewardClaim(programById(programId) || programId);
        }, 0);
        return () => window.clearTimeout(handle);
    }, [demoMode, claimState.smokeStarted, liveStatus, programById, submitRewardClaim]);

    const stats = useMemo(() => {
        if (!demoMode) {
            return {
                burnedPercent: burnedTotal == null ? null : burnedTotal / initialSupply,
                remainingToBurn: currentSupply == null ? null : Math.max(0, currentSupply - minSupply),
                daysToFloor: null,
                buybackPending: buybackCarryAfter,
                dailyBurnRate: buybackTotalSwapFee,
            };
        }
        if (
            currentSupply == null
            || burnedTotal == null
            || buybackPool == null
            || dailyVolume == null
        ) {
            return {
                burnedPercent: burnedTotal == null ? null : burnedTotal / initialSupply,
                remainingToBurn: currentSupply == null ? null : Math.max(0, currentSupply - minSupply),
                daysToFloor: null,
                buybackPending: buybackPool,
                dailyBurnRate: null,
            };
        }
        const burnedPercent = burnedTotal / initialSupply;
        const remainingToBurn = Math.max(0, currentSupply - minSupply);
        const denominator = (dailyVolume * 0.003 * 0.5) + ((dailyVolume * 0.2) * BURN_RATE);
        const daysToFloor = denominator > 0 ? Math.round(remainingToBurn / denominator) : null;
        return {
            burnedPercent,
            remainingToBurn,
            daysToFloor,
            buybackPending: buybackPool,
            dailyBurnRate: dailyVolume * 0.003 * 0.5,
        };
    }, [buybackCarryAfter, buybackPool, buybackTotalSwapFee, burnedTotal, currentSupply, dailyVolume, demoMode, initialSupply, minSupply]);

    const burnHistory = demoMode ? DEMO_BURN_HISTORY : [];
    const badgeText = demoMode
        ? 'Local fallback'
        : liveState.loading
            ? 'Loading'
            : liveState.error
                ? 'Live error'
                : 'Live local testnet';

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

            {!demoMode && (
                <div className="stats-honesty-banner" role="status">
                    {liveState.error ? (
                        <>
                            <strong>Tokenomics endpoint unavailable.</strong> {liveState.error}
                        </>
                    ) : (
                        <>
                            <strong>Live mode.</strong> {tokenSymbol} supply and allocation rows come from
                            ZenoLedger local-testnet state. Active-participant reward claims are receipt-gated
                            local-testnet transfers from the rewards controller. Buyback/burn rows are replayed
                            from accepted swap sidecars; market-purchase buyback is
                            {' '}{buybackRuntimeEnabled ? 'enabled' : 'not enabled'} in this stack.
                        </>
                    )}
                </div>
            )}

            <div className="stats-grid grid grid-4">
                <div className="stat-card panel animate-slide-up" style={{ animationDelay: '0ms' }}>
                    <span className="stat-label">Current Supply</span>
                    <span className="stat-value">{formatValueOrNA(currentSupply)}</span>
                    <span className="stat-sub">of {formatNumber(initialSupply)} initial</span>
                </div>
                <div className="stat-card panel animate-slide-up" style={{ animationDelay: '50ms' }}>
                    <span className="stat-label">Total Burned</span>
                    <span className="stat-value stat-burned">{formatValueOrNA(burnedTotal)}</span>
                    <span className="stat-sub">
                        {!demoMode && burnedTotal === 0
                            ? `no burns yet · height ${liveStatus?.height ?? '—'}`
                            : (stats.burnedPercent == null ? NA : `${formatPercent(stats.burnedPercent)} of initial`)}
                    </span>
                </div>
                <div className="stat-card panel animate-slide-up" style={{ animationDelay: '100ms' }}>
                    <span className="stat-label">{demoMode ? 'Buyback Pool' : 'Fee Pool for Buyback'}</span>
                    <span className="stat-value stat-pool">{demoMode ? formatDollarOrNA(buybackPool) : formatValueOrNA(buybackTotalSwapFee)}</span>
                    <span className="stat-sub">{demoMode ? 'pending for burn' : 'total fees collected for buyback'}</span>
                </div>
                <div className="stat-card panel animate-slide-up" style={{ animationDelay: '150ms' }}>
                    <span className="stat-label">{demoMode ? 'Est. Days to Floor' : 'Buyback Transactions'}</span>
                    <span className="stat-value">{demoMode ? (stats.daysToFloor == null ? NA : stats.daysToFloor) : formatValueOrNA(buybackEventCount)}</span>
                    <span className="stat-sub">{demoMode ? 'at current volume' : 'completed buyback transactions'}</span>
                </div>
            </div>

            <div className="supply-progress panel animate-slide-up" style={{ animationDelay: '200ms' }}>
                <div className="progress-header">
                    <span>Supply Progression</span>
                    <span>
                        {currentSupply == null ? NA : formatNumber(currentSupply)}
                        {' -> '}{formatNumber(minSupply)} floor
                    </span>
                </div>
                {currentSupply == null || burnedTotal == null ? (
                    <p className="model-note">Live {tokenSymbol} supply metrics are waiting for network data.</p>
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
                        <h3>Token Distribution</h3>
                        <span className={checks.tau_policy_flags_all_pass ? 'check-ok' : 'check-warn'}>
                            Policy check {checks.tau_policy_flags_all_pass ? 'passed' : 'pending'}
                        </span>
                    </div>
                    <div className="allocation-table" role="table" aria-label="Token allocation balances">
                        <div className="allocation-row allocation-head" role="row">
                            <span>Category</span>
                            <span>Manager</span>
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
                                <span>{formatNumber(row.initial_amount)}</span>
                                <span>{formatNumber(row.current_balance)}</span>
                            </div>
                        ))}
                    </div>
                </div>
            )}

            {programRows.length > 0 && (
                <div className="tokenomics-ledger panel animate-slide-up" style={{ animationDelay: '260ms' }}>
                    <div className="tokenomics-ledger-header">
                        <h3>Reward Programs</h3>
                        <span className={checks.active_participant_programs_sum_to_pool ? 'check-ok' : 'check-warn'}>
                            Total budget {checks.active_participant_programs_sum_to_pool ? 'valid' : 'pending'}
                        </span>
                    </div>
                    <div className="program-grid">
                        {programRows.map((row) => (
                            <div className="program-item" key={row.id}>
                                <span>{humanizeId(row.category)}</span>
                                <strong>{formatNumber(row.budget_amount)} {tokenSymbol}</strong>
                                <span className="program-claim-line">
                                    {formatNumber(row.claimed_amount || 0)} claimed · {formatNumber(row.remaining_amount ?? row.budget_amount)} remaining
                                </span>
                                {row.claim_amount != null && (
                                    <span className="program-claim-line">
                                        {formatNumber(row.claim_amount)} per eligible action
                                    </span>
                                )}
                                <small>{(row.eligibility_receipts || []).map(humanizeId).join(', ')}</small>
                                {!demoMode && (
                                <button
                                    type="button"
                                    className="claim-button"
                                    disabled={claimState.loading || Number(row.remaining_amount ?? row.budget_amount) <= 0}
                                    onClick={() => submitRewardClaim(row)}
                                >
                                    {claimState.loading ? 'Claiming' : 'Claim next reward'}
                                </button>
                            )}
                        </div>
                        ))}
                    </div>
                    {!demoMode && (claimState.data || claimState.error) && (
                        <div className={claimState.error ? 'claim-status claim-error' : 'claim-status claim-ok'} role="status">
                            {claimState.error ? claimState.error : `Claim accepted at block ${claimState.data?.height}`}
                        </div>
                    )}
                </div>
            )}

            <div className="burn-mechanics grid grid-2">
                <div className="panel animate-slide-up" style={{ animationDelay: '300ms' }}>
                    <h3>{demoMode ? 'Burn Mechanics' : 'Live Buyback/Burn Ledger'}</h3>
                    <div className="mechanic-list">
                        <div className="mechanic-item">
                            <span className="mechanic-label">{demoMode ? 'Transfer Burn Rate' : 'Protocol Fee Rate'}</span>
                            <span className="mechanic-value">{demoMode ? formatPercent(BURN_RATE) : formatBpsOrNA(protocolFeeShareBps)}</span>
                        </div>
                        <div className="mechanic-item">
                            <span className="mechanic-label">{demoMode ? 'Swap Buyback Rate' : 'Buyback Portion'}</span>
                            <span className="mechanic-value">{demoMode ? '0.3%' : formatBpsOrNA(buybackShareBps)}</span>
                        </div>
                        <div className="mechanic-item">
                            <span className="mechanic-label">{demoMode ? 'Buyback to Burn' : 'Tokens Burned'}</span>
                            <span className="mechanic-value">{demoMode ? '50%' : formatValueOrNA(buybackBurnedTotal)}</span>
                        </div>
                        <div className="mechanic-item">
                            <span className="mechanic-label">{demoMode ? 'Supply Floor' : 'Remaining Supply'}</span>
                            <span className="mechanic-value">{demoMode ? `${formatNumber(minSupply)} ${tokenSymbol}` : formatValueOrNA(buybackCarryAfter)}</span>
                        </div>
                        <div className="mechanic-item">
                            <span className="mechanic-label">Buyback Status</span>
                            <span className="mechanic-value">
                                {demoMode ? 'Modeled' : (buybackRuntimeEnabled ? 'Enabled' : buybackRouteAvailable ? 'Route only' : 'Treasury burn only')}
                            </span>
                        </div>
                    </div>
                </div>

                <div className="panel animate-slide-up" style={{ animationDelay: '340ms' }}>
                    <h3>Zeno Supply Model</h3>
                    <p className="model-desc">
                        {demoMode
                            ? `${tokenSymbol} targets a decreasing supply that approaches a protected floor.`
                            : `${tokenSymbol} supply, buyback carry, and burn totals are read from ZenoLedger. This local stack uses ${buybackMarket?.runtime_mode || 'treasury_allocation_burn_only'} for buyback accounting${buybackRuntimeBlocker ? ` (${buybackRuntimeBlocker})` : ''}.`}
                    </p>
                    {demoMode ? (
                        <>
                            <div className="formula">
                                <code>S(n) = S0 x (1 - p)^n</code>
                            </div>
                            <p className="model-note">
                                where p = 0.5% per transfer and n = number of transfers
                            </p>
                        </>
                    ) : (
                        <>
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
                                    <dd className="mono">{formatNumber(minSupply)} {tokenSymbol}</dd>
                                </div>
                                <div className="model-param">
                                    <dt>Carry after buyback</dt>
                                    <dd className="mono">{buybackCarryAfter != null ? formatNumber(buybackCarryAfter) : '—'}</dd>
                                </div>
                            </dl>
                            <p className="model-note">
                                Supply contracts via fee-funded buyback-and-burn (not a per-transfer tax), floored at the protected supply floor. Burn totals are read from ZenoLedger.
                            </p>
                        </>
                    )}
                </div>
            </div>

            <div className="burn-chart panel animate-slide-up" style={{ animationDelay: '380ms' }}>
                <h3>Supply Over Time</h3>
                {burnHistory.length === 0 ? (
                    <p className="model-note">
                        Live chart buckets are pending. Current burn totals and buyback event counts are shown from
                        accepted ledger sidecars above.
                    </p>
                ) : (
                    <div className="chart-container">
                        <div className="chart-y-axis">
                            <span>{formatNumber(initialSupply)}</span>
                            <span>{formatNumber(minSupply)}</span>
                        </div>
                        <div className="chart-area">
                            {burnHistory.map((point, i) => (
                                <div
                                    key={point.day}
                                    className="chart-bar"
                                    style={{
                                        height: `${(point.supply / initialSupply) * 100}%`,
                                        animationDelay: `${400 + i * 50}ms`,
                                    }}
                                    title={`Day ${point.day}: ${formatNumber(point.supply)} ${tokenSymbol}`}
                                >
                                    <span className="chart-label">D{point.day}</span>
                                </div>
                            ))}
                        </div>
                    </div>
                )}
            </div>

            <div className="stats-footer">
                <p>
                    {demoMode || liveStatus?.tau_policy?.mode !== 'host_computed_flags' ? (
                        <>
                            <span className="verified-badge">Tau-Gated</span>
                            Distribution manifest rails and local reward-claim rails are guarded.
                        </>
                    ) : (
                        <>
                            <span className="verified-badge verified-badge-advisory">Tau-Gated (host-computed)</span>
                            Distribution and reward-claim guard flags are host-computed from local-testnet state against
                            spec <code>{liveStatus?.tau_policy?.policy_id || 'protocol_token_distribution_guard_v1'}</code> — not Tau-runtime-enforced in this environment.
                        </>
                    )}
                </p>
            </div>
        </div>
    );
}

export default TokenStats;
