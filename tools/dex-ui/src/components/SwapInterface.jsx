import { useState, useMemo, useEffect, useCallback, useRef } from 'react';
import { calcSwapOutput, calcPriceImpact, formatNumber, formatPercent } from '../lib/cpmm';
import { validateSwap, getSlippageOptions, getPriceImpactSeverity } from '../lib/validation';
import { apiDexImpactPreview, apiDexSlippageAdvice, apiDexPokayokeSwapSuggest, apiDexPokayokeSwapSuggestHeavy, apiSwap } from '../lib/api';
import { createQuoteDagCache, computeSwapQuotePreviewIncremental } from '../lib/incrementalQuoteDag';
import {
    deriveAutoProfile,
    getProfileById,
    listRouteProfiles,
    profileFromSlider,
    sliderValueForProfile,
} from '../lib/routeProfiles';
import { createQuoteCertificate, verifyQuoteCertificate } from '../lib/quoteCertificate';
import { useTransactionCenter } from '../lib/TransactionCenterContext.jsx';
import {
    FALLBACK_SWAP_POOLS,
    loadSwapPools,
    resolveWalletTokenBalance,
} from '../lib/swapData.js';
import './SwapInterface.css';

// Token data (AGRS is the native Tau Net token)
const TOKENS = [
    { symbol: 'AGRS', name: 'Agoras', icon: '✦', decimals: 18 },
    { symbol: 'USDC', name: 'USD Coin', icon: '💵', decimals: 6 },
    { symbol: 'WETH', name: 'Wrapped ETH', icon: '⟠', decimals: 18 },
];

// Tooltip component
function Tooltip({ text, children }) {
    const [show, setShow] = useState(false);
    return (
        <span
            className="tooltip-container"
            onMouseEnter={() => setShow(true)}
            onMouseLeave={() => setShow(false)}
        >
            {children}
            {show && <span className="tooltip-text">{text}</span>}
        </span>
    );
}

function createMockTxHash() {
    const bytes = new Uint8Array(32);
    if (typeof globalThis !== 'undefined' && globalThis.crypto?.getRandomValues) {
        globalThis.crypto.getRandomValues(bytes);
    } else {
        for (let i = 0; i < bytes.length; i += 1) {
            bytes[i] = Math.floor(Math.random() * 256);
        }
    }
    const hex = Array.from(bytes, (byte) => byte.toString(16).padStart(2, '0')).join('');
    return `0x${hex}`;
}

function shortHash(hash) {
    if (!hash) return '';
    return `${hash.slice(0, 10)}...${hash.slice(-8)}`;
}

function clamp(value, lo, hi) {
    return Math.min(hi, Math.max(lo, value));
}

function estimateRoutePendingVolumes({ amountIn, routeType, profileId, gateDecision, hopOutputs = [] }) {
    const baseByProfile = {
        latency: 0.04,
        balanced: 0.10,
        quality: 0.16,
        legacy: 0.06,
    };
    const base = baseByProfile[String(profileId || '').toLowerCase()] ?? 0.10;
    const stress = clamp(Number(gateDecision?.stress ?? 0), 0, 2);
    const pressure = clamp(Number(gateDecision?.pressure ?? 1), 0, 4);
    const gateBoost = gateDecision?.considerTwoHop ? 0.03 : 0;
    const multiplier = base + gateBoost;
    const scale = 1 + (0.35 * stress) + (0.2 * Math.max(0, pressure - 1));

    const pending1 = Math.max(0, Math.round(Number(amountIn || 0) * multiplier * scale));
    if (String(routeType) !== 'two-hop') {
        return [pending1];
    }

    const hopInput2 = Math.max(0, Number(hopOutputs?.[0] ?? 0));
    const pending2 = Math.max(0, Math.round(hopInput2 * multiplier * 0.8 * scale));
    return [pending1, pending2];
}

function SwapInterface({ wallet }) {
    const { upsertTransaction } = useTransactionCenter();
    const [fromToken, setFromToken] = useState(TOKENS[0]);
    const [toToken, setToToken] = useState(TOKENS[1]);
    const [amountIn, setAmountIn] = useState('');
    const [slippage, setSlippage] = useState(0.005);
    const [showSettings, setShowSettings] = useState(false);
    const [showConfirm, setShowConfirm] = useState(false);
    const [confirmConfig, setConfirmConfig] = useState(null);
    const [typedConfirmText, setTypedConfirmText] = useState('');
    const [pokayokeSuggesting, setPokayokeSuggesting] = useState(false);
    const [pokayokeSuggestions, setPokayokeSuggestions] = useState(null);
    const [pokayokeSuggestError, setPokayokeSuggestError] = useState('');
    const [pokayokeHeavySuggesting, setPokayokeHeavySuggesting] = useState(false);
    const [pokayokeHeavySuggestions, setPokayokeHeavySuggestions] = useState(null);
    const [pokayokeHeavySuggestError, setPokayokeHeavySuggestError] = useState('');
    const [submittedSwap, setSubmittedSwap] = useState(null);
    const [pokayokeEnabled, setPokayokeEnabled] = useState(() => {
        if (typeof window === 'undefined') return true;
        const v = window.localStorage.getItem('dex.swap.pokayokeV1');
        return v !== '0';
    });
    const [advancedMode, setAdvancedMode] = useState(() => {
        if (typeof window === 'undefined') return false;
        return window.localStorage.getItem('dex.swap.advancedMode') === '1';
    });
    const [isRefreshing, setIsRefreshing] = useState(false);
    const [profileSlider, setProfileSlider] = useState(50);
    const [autoProfile, setAutoProfile] = useState(true);
    const [quoteError, setQuoteError] = useState('');
    const [isSubmitting, setIsSubmitting] = useState(false);
    const [apiImpactPreview, setApiImpactPreview] = useState(null);
    const [routeApiImpactPreview, setRouteApiImpactPreview] = useState(null);
    const [apiSlippageAdvice, setApiSlippageAdvice] = useState(null);
    const [poolFeed, setPoolFeed] = useState({
        source: 'fallback',
        pools: FALLBACK_SWAP_POOLS,
        error: null,
    });
    const [nowMs, setNowMs] = useState(Date.now());

    const quoteDagRef = useRef(createQuoteDagCache());
    const tokenSymbols = useMemo(() => TOKENS.map((token) => token.symbol), []);

    // Auto-refresh prices every 15 seconds
    useEffect(() => {
        let refreshTimeout = null;
        const interval = setInterval(() => {
            setIsRefreshing(true);
            if (refreshTimeout) clearTimeout(refreshTimeout);
            refreshTimeout = setTimeout(() => setIsRefreshing(false), 500);
        }, 15000);
        return () => {
            clearInterval(interval);
            if (refreshTimeout) clearTimeout(refreshTimeout);
        };
    }, []);

    // Certificate freshness ticker
    useEffect(() => {
        const interval = setInterval(() => setNowMs(Date.now()), 1000);
        return () => clearInterval(interval);
    }, []);

    // Persist experimental pokayoke toggle
    useEffect(() => {
        if (typeof window === 'undefined') return;
        window.localStorage.setItem('dex.swap.pokayokeV1', pokayokeEnabled ? '1' : '0');
    }, [pokayokeEnabled]);

    useEffect(() => {
        if (typeof window !== 'undefined') {
            window.localStorage.setItem('dex.swap.advancedMode', advancedMode ? '1' : '0');
        }
        if (!advancedMode) {
            setQuoteError('');
            setShowConfirm(false);
            setSubmittedSwap(null);
            setRouteApiImpactPreview(null);
        }
    }, [advancedMode]);

    useEffect(() => {
        let cancelled = false;
        let timer = null;
        const scheduleNext = (delayMs) => {
            if (cancelled) return;
            timer = setTimeout(runLoad, delayMs);
        };
        const runLoad = async () => {
            const next = await loadSwapPools({ timeoutMs: 2200 });
            if (!cancelled) {
                setPoolFeed(next);
                // Back off when API is unavailable to reduce noisy retries in local-only mode.
                scheduleNext(next.source === 'api' ? 30_000 : 180_000);
            }
        };
        runLoad();
        return () => {
            cancelled = true;
            if (timer) clearTimeout(timer);
        };
    }, []);

    useEffect(() => {
        if (!submittedSwap || submittedSwap.status !== 'pending') return undefined;
        const timeout = setTimeout(() => {
            setSubmittedSwap((prev) => {
                if (!prev || prev.txHash !== submittedSwap.txHash) return prev;
                const confirmedAt = Date.now();
                upsertTransaction({
                    id: prev.txId,
                    status: 'confirmed',
                    confirmedAt,
                    updatedAt: confirmedAt,
                });
                return { ...prev, status: 'confirmed', confirmedAt };
            });
        }, 2200);
        return () => clearTimeout(timeout);
    }, [submittedSwap, upsertTransaction]);

    // Get pool key
    const poolKey = useMemo(() => {
        const sorted = [fromToken.symbol, toToken.symbol].sort();
        return `${sorted[0]}-${sorted[1]}`;
    }, [fromToken, toToken]);

    // Get reserves (considering direction)
    const reserves = useMemo(() => {
        const pool = poolFeed.pools[poolKey];
        if (!pool) return null;
        const isForward = [fromToken.symbol, toToken.symbol].sort()[0] === fromToken.symbol;
        return isForward
            ? { reserveIn: pool.reserve0, reserveOut: pool.reserve1 }
            : { reserveIn: pool.reserve1, reserveOut: pool.reserve0 };
    }, [poolKey, fromToken, toToken, poolFeed.pools]);

    const directMetrics = useMemo(() => {
        if (!amountIn || !reserves) return null;
        const input = parseFloat(amountIn);
        if (!Number.isFinite(input) || input <= 0) return null;
        const feeBps = Number(poolFeed.pools[poolKey]?.feeBps ?? 30);
        const feeRate = feeBps / 10_000;
        const output = calcSwapOutput(reserves.reserveIn, reserves.reserveOut, input, feeRate);
        if (output <= 0) return null;
        return {
            input,
            output,
            stress: input / reserves.reserveIn,
            pressure: input / output,
            priceImpact: calcPriceImpact(reserves.reserveIn, reserves.reserveOut, input),
            feeBps,
        };
    }, [amountIn, reserves, poolKey, poolFeed.pools]);

    useEffect(() => {
        let cancelled = false;
        const controller = new AbortController();
        const run = async () => {
            if (advancedMode) {
                setApiImpactPreview(null);
                return;
            }
            if (!amountIn || !reserves) {
                setApiImpactPreview(null);
                return;
            }
            const input = parseFloat(amountIn);
            if (!Number.isFinite(input) || input <= 0) {
                setApiImpactPreview(null);
                return;
            }
            const feeBps = Number(poolFeed.pools[poolKey]?.feeBps ?? 30);
            try {
                const resp = await apiDexImpactPreview(
                    {
                        reserveIn: Math.max(1, Math.round(reserves.reserveIn)),
                        reserveOut: Math.max(1, Math.round(reserves.reserveOut)),
                        amountIn: Math.max(1, Math.round(input)),
                        feeBps: Math.max(0, Math.round(feeBps)),
                        pendingVolumeSameDirection: 0,
                        confidenceBps: 9500,
                    },
                    { timeoutMs: 1400, signal: controller.signal },
                );
                const p = resp?.preview;
                if (!cancelled && resp?.ok && p) {
                    setApiImpactPreview({
                        amountOutIsolated: Number(p.amount_out_isolated),
                        feeAmount: Number(p.fee_amount),
                        priceImpactBps: Number(p.price_impact_bps),
                        spotPriceE8: Number(p.spot_price_e8),
                        amountOutBestCase: Number(p.amount_out_best_case),
                        amountOutWorstCase: Number(p.amount_out_worst_case),
                        recommendedMinOut: Number(p.recommended_min_out),
                    });
                }
            } catch (err) {
                const name = err && typeof err === 'object' ? err.name : '';
                if (!cancelled && name !== 'AbortError') {
                    setApiImpactPreview(null);
                }
            }
        };
        run();
        return () => {
            cancelled = true;
            controller.abort();
        };
    }, [amountIn, reserves, poolKey, poolFeed.pools, advancedMode]);

    useEffect(() => {
        let cancelled = false;
        const controller = new AbortController();
        const run = async () => {
            if (advancedMode) {
                setApiSlippageAdvice(null);
                return;
            }
            if (!amountIn || !reserves) {
                setApiSlippageAdvice(null);
                return;
            }
            const input = parseFloat(amountIn);
            if (!Number.isFinite(input) || input <= 0) {
                setApiSlippageAdvice(null);
                return;
            }

            const feeBps = Number(poolFeed.pools[poolKey]?.feeBps ?? 30);
            const optsBps = getSlippageOptions()
                .map((o) => Math.round(Number(o.value) * 10_000))
                .filter((v) => Number.isFinite(v) && v >= 0 && v <= 10_000);
            optsBps.sort((a, b) => a - b);
            const uniqOpts = Array.from(new Set(optsBps));

            try {
                const resp = await apiDexSlippageAdvice(
                    {
                        reserveIn: Math.max(1, Math.round(reserves.reserveIn)),
                        reserveOut: Math.max(1, Math.round(reserves.reserveOut)),
                        amountIn: Math.max(1, Math.round(input)),
                        feeBps: Math.max(0, Math.round(feeBps)),
                        pendingVolumeSameDirection: 0,
                        confidenceBps: 9500,
                        slippageOptionsBps: uniqOpts,
                        maxAttackerAmountIn: 2000,
                        userSlippageBps: Math.max(0, Math.min(10_000, Math.round(Number(slippage || 0) * 10_000))),
                    },
                    { timeoutMs: 1800, signal: controller.signal },
                );
                const a = resp?.advice;
                if (!cancelled && resp?.ok && a) {
                    setApiSlippageAdvice({
                        status: String(a.status || ''),
                        priceImpactBps: a.price_impact_bps,
                        recommendedSlippageBps: a.recommended_slippage_bps,
                        recommendedSlippageBpsRevertSafe: a.recommended_slippage_bps_revert_safe,
                        recommendedSlippageBpsMevSafe: a.recommended_slippage_bps_mev_safe,
                        requiredSlippageBps: a.required_slippage_bps,
                        options: Array.isArray(a.options) ? a.options : [],
                        pokayoke: a.pokayoke || null,
                    });
                }
            } catch (err) {
                const name = err && typeof err === 'object' ? err.name : '';
                if (!cancelled && name !== 'AbortError') {
                    setApiSlippageAdvice(null);
                }
            }
        };
        run();
        return () => {
            cancelled = true;
            controller.abort();
        };
    }, [amountIn, reserves, poolKey, poolFeed.pools, advancedMode, slippage]);

    const legacyPreview = useMemo(() => {
        if (!directMetrics || !reserves) return null;
        const feeRate = directMetrics.feeBps / 10_000;
        const directPath = `${fromToken.symbol} -> ${toToken.symbol}`;
        const hasApiPreview = Boolean(apiImpactPreview);
        const apiSpotPrice = hasApiPreview ? (apiImpactPreview.spotPriceE8 / 100_000_000) : null;
        return {
            output: hasApiPreview ? apiImpactPreview.amountOutIsolated : directMetrics.output,
            spotPrice: hasApiPreview && Number.isFinite(apiSpotPrice) ? apiSpotPrice : (reserves.reserveOut / reserves.reserveIn),
            priceImpact: hasApiPreview ? (apiImpactPreview.priceImpactBps / 10_000) : directMetrics.priceImpact,
            minOutput: hasApiPreview ? apiImpactPreview.recommendedMinOut : (directMetrics.output * (1 - slippage)),
            feePaidEstimate: hasApiPreview ? apiImpactPreview.feeAmount : (directMetrics.input * feeRate),
            amountOutWorstCase: hasApiPreview ? apiImpactPreview.amountOutWorstCase : null,
            amountOutBestCase: hasApiPreview ? apiImpactPreview.amountOutBestCase : null,
            previewSource: hasApiPreview ? 'api' : 'local',
            routePath: directPath,
            routeType: 'direct',
            profileId: 'legacy',
            profileLabel: 'Legacy',
            policy: 'direct',
            gateDecision: {
                stress: directMetrics.stress,
                pressure: directMetrics.pressure,
                considerTwoHop: false,
            },
            quoteCallCount: 1,
        };
    }, [directMetrics, reserves, slippage, fromToken.symbol, toToken.symbol, apiImpactPreview]);

    const manualProfile = useMemo(() => profileFromSlider(profileSlider), [profileSlider]);
    const autoDerivedProfile = useMemo(
        () => deriveAutoProfile({
            stress: directMetrics?.stress ?? 0,
            pressure: directMetrics?.pressure ?? 0,
            priceImpact: directMetrics?.priceImpact ?? 0,
        }),
        [directMetrics],
    );
    const effectiveProfile = autoProfile ? autoDerivedProfile : manualProfile;
    const effectiveProfileConfig = useMemo(
        () => getProfileById(effectiveProfile.id),
        [effectiveProfile.id],
    );
    const profileSignature = useMemo(
        () => JSON.stringify({ id: effectiveProfileConfig.id, policy: effectiveProfileConfig.policy, config: effectiveProfileConfig.config }),
        [effectiveProfileConfig],
    );

    // Get user balance for from token
    const fromBalance = wallet ? resolveWalletTokenBalance(wallet, fromToken.symbol) : 0;
    const toBalance = wallet ? resolveWalletTokenBalance(wallet, toToken.symbol) : 0;

    // Incremental quote DAG (performance-oriented quote path)
    const swapQuote = useMemo(() => {
        if (!advancedMode) return null;
        if (!amountIn) return null;
        const input = parseFloat(amountIn);
        if (!Number.isFinite(input) || input <= 0) return null;
        return computeSwapQuotePreviewIncremental(
            {
                amountIn: input,
                fromSymbol: fromToken.symbol,
                toSymbol: toToken.symbol,
                pools: poolFeed.pools,
                tokenSymbols,
                slippage,
                profile: effectiveProfileConfig,
            },
            quoteDagRef.current,
        );
    }, [amountIn, fromToken.symbol, toToken.symbol, slippage, tokenSymbols, effectiveProfileConfig, advancedMode, poolFeed.pools]);

    const swapPreview = advancedMode ? (swapQuote?.preview || null) : legacyPreview;

    useEffect(() => {
        let cancelled = false;
        const controller = new AbortController();
        const run = async () => {
            if (!advancedMode || !swapPreview) {
                setRouteApiImpactPreview(null);
                return;
            }
            const routeEdges = Array.isArray(swapPreview.routeEdges) ? swapPreview.routeEdges : [];
            if (routeEdges.length === 0) {
                setRouteApiImpactPreview(null);
                return;
            }
            const amountInNum = Number(amountIn || 0);
            if (!Number.isFinite(amountInNum) || amountInNum <= 0) {
                setRouteApiImpactPreview(null);
                return;
            }

            const pendingVolumes = estimateRoutePendingVolumes({
                amountIn: amountInNum,
                routeType: swapPreview.routeType,
                profileId: swapPreview.profileId,
                gateDecision: swapPreview.gateDecision,
                hopOutputs: swapPreview.hopOutputs,
            });

            const callHop = async ({ edge, hopAmountIn, pendingVolume, confidenceBps = 9500 }) => {
                const resp = await apiDexImpactPreview(
                    {
                        reserveIn: Math.max(1, Math.round(Number(edge.reserveIn || 0))),
                        reserveOut: Math.max(1, Math.round(Number(edge.reserveOut || 0))),
                        amountIn: Math.max(1, Math.round(Number(hopAmountIn || 0))),
                        feeBps: Math.max(0, Math.round(Number(edge.feeBps || 0))),
                        pendingVolumeSameDirection: Math.max(0, Math.round(Number(pendingVolume || 0))),
                        confidenceBps,
                    },
                    { timeoutMs: 1600, signal: controller.signal },
                );
                if (!resp?.ok || !resp?.preview) {
                    throw new Error('route_impact_preview_error');
                }
                return resp.preview;
            };

            try {
                if (swapPreview.routeType !== 'two-hop' || routeEdges.length < 2) {
                    const p = await callHop({
                        edge: routeEdges[0],
                        hopAmountIn: amountInNum,
                        pendingVolume: pendingVolumes[0] || 0,
                    });
                    if (cancelled) return;
                    setRouteApiImpactPreview({
                        source: 'api-route',
                        amountOutBestCase: Number(p.amount_out_best_case),
                        amountOutWorstCase: Number(p.amount_out_worst_case),
                        recommendedMinOut: Number(p.recommended_min_out),
                        feeAmount: Number(p.fee_amount),
                    });
                    return;
                }

                // Two-hop: propagate bounds through both hops.
                const p1 = await callHop({
                    edge: routeEdges[0],
                    hopAmountIn: amountInNum,
                    pendingVolume: pendingVolumes[0] || 0,
                });
                const p2Best = await callHop({
                    edge: routeEdges[1],
                    hopAmountIn: Number(p1.amount_out_best_case),
                    pendingVolume: pendingVolumes[1] || 0,
                });
                const p2Worst = await callHop({
                    edge: routeEdges[1],
                    hopAmountIn: Number(p1.amount_out_worst_case),
                    pendingVolume: pendingVolumes[1] || 0,
                });
                if (cancelled) return;
                setRouteApiImpactPreview({
                    source: 'api-route',
                    amountOutBestCase: Number(p2Best.amount_out_best_case),
                    amountOutWorstCase: Number(p2Worst.amount_out_worst_case),
                    recommendedMinOut: Number(p2Worst.recommended_min_out),
                    feeAmount: Number(p1.fee_amount) + Number(p2Best.fee_amount),
                });
            } catch (err) {
                const name = err && typeof err === 'object' ? err.name : '';
                if (!cancelled && name !== 'AbortError') {
                    setRouteApiImpactPreview(null);
                }
            }
        };
        run();
        return () => {
            cancelled = true;
            controller.abort();
        };
    }, [advancedMode, swapPreview, amountIn]);

    const activePreview = useMemo(() => {
        if (!swapPreview) return null;
        if (!advancedMode || !routeApiImpactPreview) return swapPreview;
        const minOutFromRouteApi = Number(routeApiImpactPreview.recommendedMinOut);
        const nextMinOut = Number.isFinite(minOutFromRouteApi)
            ? Math.min(Number(swapPreview.minOutput || 0), minOutFromRouteApi)
            : swapPreview.minOutput;
        return {
            ...swapPreview,
            minOutput: nextMinOut,
            amountOutBestCase: Number(routeApiImpactPreview.amountOutBestCase),
            amountOutWorstCase: Number(routeApiImpactPreview.amountOutWorstCase),
            feePaidEstimate: Number.isFinite(routeApiImpactPreview.feeAmount)
                ? routeApiImpactPreview.feeAmount
                : swapPreview.feePaidEstimate,
            previewSource: 'api-route',
        };
    }, [swapPreview, advancedMode, routeApiImpactPreview]);

    const quotePayload = useMemo(() => {
        if (!advancedMode) return null;
        if (!activePreview) return null;
        return {
            fromSymbol: fromToken.symbol,
            toSymbol: toToken.symbol,
            amountIn: Number(amountIn || 0),
            amountOut: activePreview.output,
            minOutput: activePreview.minOutput,
            slippageBps: Math.round(slippage * 10_000),
            routePath: activePreview.routePath,
            routeType: activePreview.routeType,
            profileId: activePreview.profileId,
            policy: activePreview.policy,
            quoteCallCount: activePreview.quoteCallCount,
        };
    }, [activePreview, fromToken.symbol, toToken.symbol, amountIn, slippage, advancedMode]);

    const quoteCertificate = useMemo(() => {
        if (!advancedMode) return null;
        if (!quotePayload) return null;
        return createQuoteCertificate(quotePayload, { nowMs, ttlMs: 25000 });
    }, [quotePayload, nowMs, advancedMode]);

    const certificateCheck = useMemo(() => {
        if (!advancedMode) {
            return { ok: true, reason: 'advanced_mode_disabled', remainingMs: 0 };
        }
        if (!quotePayload || !quoteCertificate) {
            return { ok: false, reason: 'missing_quote', remainingMs: 0 };
        }
        return verifyQuoteCertificate(quoteCertificate, quotePayload, { nowMs });
    }, [quotePayload, quoteCertificate, nowMs, advancedMode]);

    // Validation with helpful messages
    const validation = useMemo(() => {
        if (!amountIn) return { ok: false, error: '' };
        const input = parseFloat(amountIn);

        if (isNaN(input) || input <= 0) {
            return { ok: false, error: 'Enter a valid amount' };
        }

        if (wallet && input > fromBalance) {
            return { ok: false, error: `Insufficient ${fromToken.symbol} balance` };
        }

        if (!reserves) {
            return { ok: false, error: 'Pool not found' };
        }

        if (!activePreview) return { ok: false, error: '' };

        return validateSwap({
            amountIn: input,
            amountOut: activePreview.output,
            reserveIn: reserves?.reserveIn ?? 1,
            reserveOut: reserves?.reserveOut ?? 1,
            maxSlippage: slippage,
            priceImpact: activePreview.priceImpact,
        });
    }, [amountIn, reserves, activePreview, slippage, wallet, fromBalance, fromToken.symbol]);

    // Auto-calculate a slippage default from deterministic preview bounds when available.
    // We map the required slippage to the nearest *available* option so the UI stays simple.
    const suggestedSlippage = useMemo(() => {
        const opts = getSlippageOptions().map((o) => Number(o.value)).filter((v) => Number.isFinite(v));
        opts.sort((a, b) => a - b);
        const pickOption = (required) => {
            if (opts.length === 0) return 0.005;
            const r = Number(required);
            if (!Number.isFinite(r) || r <= 0) return opts[0];
            for (const v of opts) {
                if (v >= r) return v;
            }
            return opts[opts.length - 1];
        };

        // Prefer API slippage bounds among discrete options.
        const advice = advancedMode ? null : apiSlippageAdvice;
        if (advice && advice.recommendedSlippageBps !== null && advice.recommendedSlippageBps !== undefined) {
            const bps = Number(advice.recommendedSlippageBps);
            if (Number.isFinite(bps) && bps >= 0) {
                return pickOption(bps / 10_000);
            }
        }

        // Prefer API-derived bounds (includes confidence-adjusted pending volume).
        const bound = advancedMode ? routeApiImpactPreview : apiImpactPreview;
        if (bound) {
            const best = Number(bound.amountOutBestCase ?? bound.amountOutIsolated ?? 0);
            const minOut = Number(bound.recommendedMinOut ?? 0);
            if (Number.isFinite(best) && best > 0 && Number.isFinite(minOut) && minOut >= 0) {
                const required = Math.max(0, (best - minOut) / best);
                return pickOption(required);
            }
        }

        // Fallback: crude impact-based buckets.
        if (!activePreview) return 0.005;
        if (activePreview.priceImpact > 0.05) return 0.03;
        if (activePreview.priceImpact > 0.01) return 0.01;
        return 0.005;
    }, [activePreview, advancedMode, apiImpactPreview, routeApiImpactPreview, apiSlippageAdvice]);

    const slippageAdviceNotice = useMemo(() => {
        if (advancedMode) return null;
        const st = String(apiSlippageAdvice?.status || '').trim();
        if (!st || st === 'ok') return null;
        if (st === 'mev_conflict') {
            return {
                kind: 'warning',
                text: 'MEV/revert conflict: smallest revert-safe slippage appears sandwich-profitable under the bounded model.',
            };
        }
        if (st === 'inconclusive_mev') {
            return {
                kind: 'notice',
                text: 'MEV risk is inconclusive under the scan cap. Treat as unknown (fail-closed).',
            };
        }
        if (st === 'no_revert_safe_option') {
            return {
                kind: 'warning',
                text: 'No provided slippage option is revert-safe at the confidence bound; the swap may revert.',
            };
        }
        return { kind: 'notice', text: `Slippage advisor status: ${st}` };
    }, [advancedMode, apiSlippageAdvice]);

    useEffect(() => {
        if (advancedMode) {
            setQuoteError('');
        }
    }, [amountIn, fromToken.symbol, toToken.symbol, slippage, profileSignature, autoProfile, advancedMode]);

    const handleSwapTokens = () => {
        setFromToken(toToken);
        setToToken(fromToken);
        setAmountIn('');
        setQuoteError('');
    };

    const handleMaxAmount = () => {
        if (wallet && fromBalance > 0) {
            // Leave a small amount for gas if native token
            const maxAmount = fromToken.symbol === 'AGRS'
                ? Math.max(0, fromBalance - 0.01)
                : fromBalance;
            setAmountIn(maxAmount.toString());
            setQuoteError('');
        }
    };

    const handleSwapClick = () => {
        if (!validation.ok || !wallet || isSubmitting) return;
        if (advancedMode && !certificateCheck.ok) {
            setQuoteError(`Quote verification failed: ${certificateCheck.reason}`);
            return;
        }

        // Experimental poka-yoke interlocks (UX-only).
        const gate = (!advancedMode && pokayokeEnabled) ? apiSlippageAdvice?.pokayoke : null;
        if (gate && String(gate.action) === 'block') {
            const msg = Array.isArray(gate.messages) && gate.messages.length > 0
                ? gate.messages[0]
                : 'Blocked by safety interlock';
            setQuoteError(msg);
            return;
        }
        if (gate && (String(gate.action) === 'confirm' || String(gate.action) === 'typed_confirm')) {
            setTypedConfirmText('');
            setPokayokeSuggestions(null);
            setPokayokeSuggestError('');
            setPokayokeHeavySuggestions(null);
            setPokayokeHeavySuggestError('');
            setConfirmConfig({
                title: '⚠️ Confirm Swap',
                messages: Array.isArray(gate.messages) ? gate.messages : [],
                reasons: Array.isArray(gate.reasons) ? gate.reasons : [],
                requireTyped: String(gate.action) === 'typed_confirm',
                typedPhrase: gate.typed_confirm_phrase ? String(gate.typed_confirm_phrase) : 'PROCEED',
                proceedText: String(gate.action) === 'typed_confirm' ? 'Proceed (Typed Confirm)' : 'Proceed Anyway',
            });
            setShowConfirm(true);
            return;
        }

        // Fallback: confirm on high price impact (legacy poka-yoke).
        if (activePreview && activePreview.priceImpact > 0.01) {
            setTypedConfirmText('');
            setPokayokeSuggestions(null);
            setPokayokeSuggestError('');
            setPokayokeHeavySuggestions(null);
            setPokayokeHeavySuggestError('');
            setConfirmConfig({
                title: '⚠️ Confirm Swap',
                messages: ['High price impact. Consider trading a smaller amount or adding liquidity.'],
                reasons: ['legacy_high_impact'],
                requireTyped: false,
                typedPhrase: null,
                proceedText: 'Proceed Anyway',
            });
            setShowConfirm(true);
            return;
        }
        executeSwap();
    };

    const executeSwap = useCallback(async () => {
        setShowConfirm(false);
        setConfirmConfig(null);
        setTypedConfirmText('');
        setPokayokeSuggestions(null);
        setPokayokeSuggestError('');
        setPokayokeHeavySuggestions(null);
        setPokayokeHeavySuggestError('');
        if (!activePreview) {
            setQuoteError('Missing quote preview');
            return;
        }
        let submitted = null;
        if (advancedMode) {
            if (!quotePayload || !quoteCertificate) {
                setQuoteError('Missing quote certificate');
                return;
            }
            const check = verifyQuoteCertificate(quoteCertificate, quotePayload, { nowMs: Date.now() });
            if (!check.ok) {
                setQuoteError(`Quote verification failed: ${check.reason}`);
                return;
            }
            submitted = {
                amountIn,
                fromSymbol: fromToken.symbol,
                amountOut: formatNumber(activePreview.output),
                toSymbol: toToken.symbol,
                minOutput: formatNumber(activePreview.minOutput),
                routePath: activePreview.routePath,
                profileLabel: effectiveProfileConfig.label,
                policy: activePreview.policy,
                certSeconds: Math.floor(check.remainingMs / 1000),
                advanced: true,
            };
        } else {
            submitted = {
                amountIn,
                fromSymbol: fromToken.symbol,
                amountOut: formatNumber(activePreview.output),
                toSymbol: toToken.symbol,
                minOutput: formatNumber(activePreview.minOutput),
                advanced: false,
            };
        }
        setIsSubmitting(true);
        try {
            const submittedAt = Date.now();
            const txId = `swap-${submittedAt}-${Math.random().toString(16).slice(2, 8)}`;
            let txHash = createMockTxHash();
            let submitPath = 'local';
            try {
                const maybeRemote = await apiSwap(
                    {
                        from: fromToken.symbol,
                        to: toToken.symbol,
                        amountIn: Number(amountIn),
                    },
                    { timeoutMs: 3500 },
                );
                if (maybeRemote?.txHash) {
                    txHash = String(maybeRemote.txHash);
                }
                submitPath = maybeRemote?.ok === false ? 'local-fallback' : 'api-or-local';
            } catch {
                submitPath = 'local-fallback';
            }

            setSubmittedSwap({
                ...submitted,
                txId,
                txHash,
                network: 'Tau Net Alpha',
                status: 'pending',
                submitPath,
                submittedAt,
            });
            upsertTransaction({
                id: txId,
                status: 'pending',
                product: 'swap',
                title: `Swap ${fromToken.symbol} -> ${toToken.symbol}`,
                routePath: submitted.routePath,
                txHash,
                network: 'Tau Net Alpha',
                createdAt: submittedAt,
            });
            setAmountIn('');
            setQuoteError('');
        } finally {
            setIsSubmitting(false);
        }
    }, [amountIn, fromToken, toToken, activePreview, quotePayload, quoteCertificate, effectiveProfileConfig.label, advancedMode, upsertTransaction]);

    const handleFindSaferAmount = useCallback(async () => {
        if (advancedMode) return;
        if (!pokayokeEnabled) return;
        if (!reserves || !amountIn) return;
        const input = parseFloat(amountIn);
        if (!Number.isFinite(input) || input <= 0) return;
        const feeBps = Number(poolFeed.pools[poolKey]?.feeBps ?? 30);
        const optsBps = getSlippageOptions()
            .map((o) => Math.round(Number(o.value) * 10_000))
            .filter((v) => Number.isFinite(v) && v >= 0 && v <= 10_000);
        optsBps.sort((a, b) => a - b);
        const uniqOpts = Array.from(new Set(optsBps));
        const userSlippageBps = Math.max(0, Math.min(10_000, Math.round(Number(slippage || 0) * 10_000)));

        setPokayokeSuggesting(true);
        setPokayokeSuggestError('');
        setPokayokeSuggestions(null);
        try {
            const resp = await apiDexPokayokeSwapSuggest(
                {
                    reserveIn: Math.max(1, Math.round(reserves.reserveIn)),
                    reserveOut: Math.max(1, Math.round(reserves.reserveOut)),
                    amountIn: Math.max(1, Math.round(input)),
                    feeBps: Math.max(0, Math.round(feeBps)),
                    pendingVolumeSameDirection: 0,
                    confidenceBps: 9500,
                    slippageOptionsBps: uniqOpts,
                    userSlippageBps,
                },
                { timeoutMs: 4500 },
            );
            if (resp?.ok && resp?.suggestions) {
                setPokayokeSuggestions(resp.suggestions);
            } else {
                setPokayokeSuggestError('Calculation unavailable');
            }
        } catch (err) {
            const msg = err && typeof err === 'object' ? String(err.message || 'suggest_error') : 'suggest_error';
            setPokayokeSuggestError(msg);
        } finally {
            setPokayokeSuggesting(false);
        }
    }, [advancedMode, pokayokeEnabled, reserves, amountIn, poolFeed.pools, poolKey, slippage]);

    const handleFindSaferAmountDeep = useCallback(async () => {
        if (advancedMode) return;
        if (!pokayokeEnabled) return;
        if (!reserves || !amountIn) return;
        const input = parseFloat(amountIn);
        if (!Number.isFinite(input) || input <= 0) return;
        const feeBps = Number(poolFeed.pools[poolKey]?.feeBps ?? 30);
        const optsBps = getSlippageOptions()
            .map((o) => Math.round(Number(o.value) * 10_000))
            .filter((v) => Number.isFinite(v) && v >= 0 && v <= 10_000);
        optsBps.sort((a, b) => a - b);
        const uniqOpts = Array.from(new Set(optsBps));
        const userSlippageBps = Math.max(0, Math.min(10_000, Math.round(Number(slippage || 0) * 10_000)));

        setPokayokeHeavySuggesting(true);
        setPokayokeHeavySuggestError('');
        setPokayokeHeavySuggestions(null);
        try {
            const resp = await apiDexPokayokeSwapSuggestHeavy(
                {
                    reserveIn: Math.max(1, Math.round(reserves.reserveIn)),
                    reserveOut: Math.max(1, Math.round(reserves.reserveOut)),
                    amountIn: Math.max(1, Math.round(input)),
                    feeBps: Math.max(0, Math.round(feeBps)),
                    pendingVolumeSameDirection: 0,
                    confidenceBps: 9500,
                    slippageOptionsBps: uniqOpts,
                    userSlippageBps,
                    maxAttackerAmountIn: 5000,
                    maxEvals: 20,
                    targetActions: ['confirm', 'allow'],
                },
                { timeoutMs: 12_000 },
            );
            if (resp?.ok && Array.isArray(resp?.suggestions)) {
                setPokayokeHeavySuggestions(resp.suggestions);
            } else {
                setPokayokeHeavySuggestError('Deep calculation unavailable');
            }
        } catch (err) {
            const msg = err && typeof err === 'object' ? String(err.message || 'suggest_error') : 'suggest_error';
            setPokayokeHeavySuggestError(msg);
        } finally {
            setPokayokeHeavySuggesting(false);
        }
    }, [advancedMode, pokayokeEnabled, reserves, amountIn, poolFeed.pools, poolKey, slippage]);

    const getButtonText = () => {
        if (!wallet) return 'Connect Wallet';
        if (isSubmitting) return 'Submitting...';
        if (!amountIn) return 'Enter Amount';
        if (advancedMode && quoteError) return quoteError;
        if (advancedMode && activePreview && !certificateCheck.ok) return 'Quote Not Certified';
        if (validation.error) return validation.error;
        if (!validation.ok) return 'Invalid Swap';
        return 'Swap';
    };

    const impactSeverity = activePreview ? getPriceImpactSeverity(activePreview.priceImpact) : 'low';
    const routeProfiles = listRouteProfiles();

    return (
        <div className="swap-panel panel">
            <div className="swap-header">
                <h2>Swap</h2>
                <div className="swap-header-actions">
                    <span className={`refresh-indicator ${isRefreshing ? 'active' : ''}`} title="Prices refresh every 15s">
                        🔄
                    </span>
                    <button
                        className="settings-btn"
                        onClick={() => setShowSettings(!showSettings)}
                        title="Transaction settings"
                    >
                        ⚙️
                    </button>
                </div>
            </div>

            {showSettings && (
                <div className="settings-panel animate-slide-up">
                    <div className="settings-row">
                        <span className="label">
                            <Tooltip text="Maximum price movement you're willing to accept">
                                Slippage Tolerance ℹ️
                            </Tooltip>
                        </span>
                        {suggestedSlippage !== slippage && (
                            <button
                                className="suggested-btn"
                                onClick={() => setSlippage(suggestedSlippage)}
                            >
                                Use calculated ({formatPercent(suggestedSlippage)})
                            </button>
                        )}
                    </div>
                    <div className="slippage-options">
                        {getSlippageOptions().map(opt => (
                            <button
                                key={opt.value}
                                className={`slippage-btn ${slippage === opt.value ? 'active' : ''}`}
                                onClick={() => setSlippage(opt.value)}
                            >
                                {opt.label}
                            </button>
                        ))}
                    </div>

                    {slippageAdviceNotice && (
                        <div className={slippageAdviceNotice.kind === 'warning' ? 'swap-warning' : 'swap-notice'}>
                            {slippageAdviceNotice.text}
                        </div>
                    )}

                    <div className="settings-row">
                        <span className="label">
                            <Tooltip text="Enable experimental mistake-proofing interlocks (confirm/typed confirm) driven by deterministic MEV + revert-safety signals">
                                Safety Interlocks (Experimental) ℹ️
                            </Tooltip>
                        </span>
                        <button
                            className={`automation-toggle ${pokayokeEnabled ? 'enabled' : ''}`}
                            onClick={() => setPokayokeEnabled((prev) => !prev)}
                            type="button"
                        >
                            {pokayokeEnabled ? 'Enabled' : 'Disabled'}
                        </button>
                    </div>

                    <div className="settings-row">
                        <span className="label">
                            <Tooltip text="Enable experimental route optimization and quote certificates">
                                Advanced Mode ℹ️
                            </Tooltip>
                        </span>
                        <button
                            className={`automation-toggle ${advancedMode ? 'enabled' : ''}`}
                            onClick={() => setAdvancedMode((prev) => !prev)}
                            type="button"
                        >
                            {advancedMode ? 'Enabled' : 'Disabled'}
                        </button>
                    </div>

                    {advancedMode && (
                        <>
                            <div className="settings-divider" />
                            <div className="settings-row">
                                <span className="label">
                                    <Tooltip text="Deterministic route policy frontier: Latency ↔ Quality">
                                        Route Profile ℹ️
                                    </Tooltip>
                                </span>
                                <button
                                    className={`automation-toggle ${autoProfile ? 'enabled' : ''}`}
                                    onClick={() => setAutoProfile((prev) => !prev)}
                                    type="button"
                                >
                                    {autoProfile ? 'Auto On' : 'Auto Off'}
                                </button>
                            </div>
                            <div className="profile-slider-wrap">
                                <input
                                    type="range"
                                    min="0"
                                    max="100"
                                    value={autoProfile ? sliderValueForProfile(effectiveProfileConfig.id) : profileSlider}
                                    onChange={(e) => setProfileSlider(Number(e.target.value))}
                                    disabled={autoProfile}
                                    className="profile-slider"
                                />
                                <div className="profile-labels">
                                    {routeProfiles.map((profile) => (
                                        <span
                                            key={profile.id}
                                            className={`profile-chip ${effectiveProfileConfig.id === profile.id ? 'active' : ''}`}
                                        >
                                            {profile.label}
                                        </span>
                                    ))}
                                </div>
                            </div>
                            <div className="profile-description">
                                <strong>{effectiveProfileConfig.label}</strong>: {effectiveProfileConfig.description}
                            </div>
                        </>
                    )}
                </div>
            )}

            {/* From Token */}
            <div className={`swap-input-container ${validation.error && amountIn ? 'has-error' : ''}`}>
                <div className="swap-input-header">
                    <span className="label">From</span>
                    <span className="balance" onClick={handleMaxAmount} style={{ cursor: wallet ? 'pointer' : 'default' }}>
                        Balance: {wallet ? formatNumber(fromBalance) : '-'}
                        {wallet && fromBalance > 0 && <span className="max-label"> (MAX)</span>}
                    </span>
                </div>
                <div className="swap-input-row">
                    <input
                        type="number"
                        className="input input-large swap-amount-input"
                        placeholder="0.0"
                        value={amountIn}
                        onChange={(e) => setAmountIn(e.target.value)}
                        min="0"
                        step="any"
                    />
                    <div className="token-selector">
                        <span className="token-icon-small">{fromToken.icon}</span>
                        <span>{fromToken.symbol}</span>
                    </div>
                </div>
                {validation.error && amountIn && (
                    <div className="input-error-hint">{validation.error}</div>
                )}
            </div>

            {/* Swap Direction Button */}
            <div className="swap-direction">
                <button className="swap-direction-btn" onClick={handleSwapTokens} title="Swap tokens">
                    ↕️
                </button>
            </div>

            {/* To Token */}
            <div className="swap-input-container">
                <div className="swap-input-header">
                    <span className="label">To (estimated)</span>
                    <span className="balance">Balance: {wallet ? formatNumber(toBalance) : '-'}</span>
                </div>
                <div className="swap-input-row">
                    <input
                        type="text"
                        className="input input-large swap-amount-input"
                        placeholder="0.0"
                        value={activePreview ? formatNumber(activePreview.output) : ''}
                        readOnly
                    />
                    <div className="token-selector">
                        <span className="token-icon-small">{toToken.icon}</span>
                        <span>{toToken.symbol}</span>
                    </div>
                </div>
            </div>

            {/* Swap Details */}
            {activePreview && (
                <div className="swap-details animate-fade-in">
                    <div className="swap-detail-row">
                        <Tooltip text="Current exchange rate between tokens">
                            <span>Rate</span>
                        </Tooltip>
                        <span>1 {fromToken.symbol} = {formatNumber(activePreview.spotPrice, 4)} {toToken.symbol}</span>
                    </div>
                    <div className="swap-detail-row">
                        <Tooltip text="Difference between market price and execution price due to trade size">
                            <span>Price Impact</span>
                        </Tooltip>
                        <span className={`impact-${impactSeverity}`}>
                            {formatPercent(activePreview.priceImpact)}
                            {impactSeverity === 'high' && ' ⚠️'}
                        </span>
                    </div>
                    <div className="swap-detail-row">
                        <Tooltip text="Minimum you'll receive after slippage">
                            <span>Minimum Received</span>
                        </Tooltip>
                        <span>{formatNumber(activePreview.minOutput)} {toToken.symbol}</span>
                    </div>
                    <div className="swap-detail-row">
                        <Tooltip text="Fee paid to liquidity providers">
                            <span>Fee (est.)</span>
                        </Tooltip>
                        <span>{formatNumber(activePreview.feePaidEstimate)} {fromToken.symbol}</span>
                    </div>
                    {Number.isFinite(activePreview.amountOutWorstCase) && Number.isFinite(activePreview.amountOutBestCase) && (
                        <div className="swap-detail-row">
                            <Tooltip text="Deterministic execution envelope given current pool state">
                                <span>Execution Bounds</span>
                            </Tooltip>
                            <span>
                                {formatNumber(activePreview.amountOutWorstCase)} - {formatNumber(activePreview.amountOutBestCase)} {toToken.symbol}
                            </span>
                        </div>
                    )}
                    <div className="swap-detail-row">
                        <Tooltip text="Pool reserve feed source for quote computation">
                            <span>Price Feed</span>
                        </Tooltip>
                        <span className={poolFeed.source === 'api' ? 'impact-low' : 'impact-medium'}>
                            {poolFeed.source === 'api' ? 'Live API' : 'Reference Snapshot'}
                        </span>
                    </div>
                    {advancedMode && (
                        <>
                            <div className="swap-detail-row">
                                <Tooltip text="Selected deterministic route and profile policy">
                                    <span>Route</span>
                                </Tooltip>
                                <span>{activePreview.routePath} ({activePreview.profileLabel})</span>
                            </div>
                            <div className="swap-detail-row">
                                <Tooltip text="Two-hop gate signals used by policy">
                                    <span>Gate Signals</span>
                                </Tooltip>
                                <span>
                                    S={formatNumber(activePreview.gateDecision.stress, 3)} / P={formatNumber(activePreview.gateDecision.pressure, 3)}
                                    {activePreview.gateDecision.considerTwoHop ? ' (2-hop check on)' : ' (2-hop check off)'}
                                </span>
                            </div>
                            <div className="swap-detail-row">
                                <Tooltip text="Client verifies deterministic quote certificate before submission">
                                    <span>Quote Cert</span>
                                </Tooltip>
                                <span className={certificateCheck.ok ? 'impact-low' : 'impact-high'}>
                                    {certificateCheck.ok
                                        ? `Verified (${Math.floor(certificateCheck.remainingMs / 1000)}s)`
                                        : `Invalid (${certificateCheck.reason})`}
                                </span>
                            </div>
                            <div className="swap-detail-row">
                                <Tooltip text="Incremental DAG stats: fewer recomputes = better UI performance">
                                    <span>Quote Compute</span>
                                </Tooltip>
                                <span>
                                    calls={activePreview.quoteCallCount}, hits={swapQuote?.diagnostics?.hitsDelta ?? 0}, recomputes={swapQuote?.diagnostics?.recomputesDelta ?? 0}
                                    {activePreview.previewSource ? `, source=${activePreview.previewSource}` : ''}
                                </span>
                            </div>
                        </>
                    )}
                </div>
            )}

            {/* High Impact Warning */}
            {activePreview && impactSeverity === 'high' && (
                <div className="swap-warning">
                    ⚠️ High price impact! Consider trading a smaller amount or adding liquidity.
                </div>
            )}

            {/* Medium Impact Notice */}
            {activePreview && impactSeverity === 'medium' && (
                <div className="swap-notice">
                    ℹ️ Moderate price impact ({formatPercent(activePreview.priceImpact)})
                </div>
            )}

            {poolFeed.source !== 'api' && (
                <div className="swap-notice">
                    ℹ️ Live pool feed unavailable. Using a reference reserve snapshot for preview quotes.
                </div>
            )}

            {advancedMode && activePreview && !certificateCheck.ok && (
                <div className="swap-warning">
                    ⚠️ Quote certificate check failed: {certificateCheck.reason}. Refresh quote before swapping.
                </div>
            )}

            {quoteError && (
                <div className="swap-warning">
                    ⚠️ {quoteError}
                </div>
            )}

            {/* Swap Button */}
            <button
                className={`btn btn-primary btn-large swap-btn ${impactSeverity === 'high' ? 'btn-warning' : ''}`}
                onClick={handleSwapClick}
                disabled={isSubmitting || !wallet || !validation.ok || (advancedMode && Boolean(activePreview) && !certificateCheck.ok)}
            >
                {getButtonText()}
            </button>

            {/* Confirmation Modal (Poka-yoke interlocks) */}
            {showConfirm && activePreview && (
                <div
                    className="confirm-overlay"
                    onClick={() => {
                        setShowConfirm(false);
                        setConfirmConfig(null);
                        setTypedConfirmText('');
                        setPokayokeSuggestions(null);
                        setPokayokeSuggestError('');
                        setPokayokeHeavySuggestions(null);
                        setPokayokeHeavySuggestError('');
                    }}
                >
                    <div className="confirm-modal animate-slide-up" onClick={e => e.stopPropagation()}>
                        <h3>{confirmConfig?.title || '⚠️ Confirm Swap'}</h3>
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
                                    <span>{effectiveProfileConfig.label}</span>
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
                                    onChange={(e) => setTypedConfirmText(e.target.value)}
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
                                                onClick: () => {
                                                    setSlippage(recRevert / 10_000);
                                                    setShowConfirm(false);
                                                    setConfirmConfig(null);
                                                    setTypedConfirmText('');
                                                    setPokayokeSuggestions(null);
                                                    setPokayokeSuggestError('');
                                                },
                                            });
                                        }
                                        if (reasons.includes('slippage_above_mev_safe') && Number.isFinite(recMev) && recMev >= 0 && recMev <= 10_000 && userSlippageBps > recMev) {
                                            actions.push({
                                                key: 'use_mev_safe_slippage',
                                                label: `Apply MEV ceiling (${(recMev / 100).toFixed(2)}%)`,
                                                onClick: () => {
                                                    setSlippage(recMev / 10_000);
                                                    setShowConfirm(false);
                                                    setConfirmConfig(null);
                                                    setTypedConfirmText('');
                                                    setPokayokeSuggestions(null);
                                                    setPokayokeSuggestError('');
                                                },
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
                                        onClick={handleFindSaferAmount}
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
                                                onClick={handleFindSaferAmountDeep}
                                                disabled={pokayokeHeavySuggesting}
                                            >
                                                {pokayokeHeavySuggesting ? 'Calculating...' : 'Deep Calculation (MEV/Unknown)'}
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
                                                    onClick={() => {
                                                        setAmountIn(String(it.amount));
                                                        setShowConfirm(false);
                                                        setConfirmConfig(null);
                                                        setTypedConfirmText('');
                                                        setPokayokeSuggestions(null);
                                                        setPokayokeSuggestError('');
                                                    }}
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
                                                    onClick={() => {
                                                        setAmountIn(String(it.amount));
                                                        setShowConfirm(false);
                                                        setConfirmConfig(null);
                                                        setTypedConfirmText('');
                                                        setPokayokeSuggestions(null);
                                                        setPokayokeSuggestError('');
                                                        setPokayokeHeavySuggestions(null);
                                                        setPokayokeHeavySuggestError('');
                                                    }}
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
                                onClick={() => {
                                    setShowConfirm(false);
                                    setConfirmConfig(null);
                                    setTypedConfirmText('');
                                    setPokayokeSuggestions(null);
                                    setPokayokeSuggestError('');
                                    setPokayokeHeavySuggestions(null);
                                    setPokayokeHeavySuggestError('');
                                }}
                            >
                                Cancel
                            </button>
                            <button
                                className="btn btn-primary btn-warning"
                                onClick={executeSwap}
                                disabled={
                                    isSubmitting ||
                                    (confirmConfig?.requireTyped && String(typedConfirmText || '').trim().toUpperCase() !== String(confirmConfig?.typedPhrase || '').trim().toUpperCase())
                                }
                            >
                                {isSubmitting ? 'Submitting...' : (confirmConfig?.proceedText || 'Proceed Anyway')}
                            </button>
                        </div>
                    </div>
                </div>
            )}

            {/* Submitted Modal */}
            {submittedSwap && (
                <div className="confirm-overlay" onClick={() => setSubmittedSwap(null)}>
                    <div className="confirm-modal submitted-modal animate-slide-up" onClick={e => e.stopPropagation()}>
                        <h3>{submittedSwap.status === 'pending' ? 'Transaction Pending' : 'Swap Confirmed'}</h3>
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
                            <button className="btn btn-primary" onClick={() => setSubmittedSwap(null)}>
                                Done
                            </button>
                        </div>
                    </div>
                </div>
            )}

            <div className="swap-footer">
                <span className="verified-badge">✓ Tau-Verified</span>
                <span className="network-badge">Tau Net Alpha</span>
            </div>
        </div>
    );
}

export default SwapInterface;
