import { useState, useMemo, useEffect, useCallback, useRef } from 'react';
import { calcSwapOutput, calcSwapInput, calcPriceImpact, formatNumber, formatPercent } from '../lib/cpmm';
import { useKeyboardShortcuts } from '../lib/useKeyboardShortcuts.js';
import { validateSwap, getSlippageOptions, getPriceImpactSeverity } from '../lib/validation';
import { apiDexPokayokeSwapSuggest, apiDexPokayokeSwapSuggestHeavy, apiSwap, getRuntimeConfig } from '../lib/api';
import { createQuoteDagCache, computeSwapQuotePreviewIncremental } from '../lib/incrementalQuoteDag';
import {
    deriveAutoProfile,
    getProfileById,
    listRouteProfiles,
    profileFromSlider,
} from '../lib/routeProfiles';
import { createQuoteCertificate, verifyQuoteCertificate } from '../lib/quoteCertificate';
import { useTransactionCenter } from '../lib/TransactionCenterContext.jsx';
import { useDemoMode } from '../lib/DemoModeContext.jsx';
import TokenSelectModal from './TokenSelectModal.jsx';
import Modal from './Modal.jsx';
import {
    FALLBACK_SWAP_POOLS,
    FALLBACK_SWAP_TOKENS,
    loadSwapPools,
    resolveWalletTokenBalance,
} from '../lib/swapData.js';
import VerifiedBySpec from './VerifiedBySpec.jsx';
import { buildAndSignSwapIntent } from '../sdk/dexIntentSigner.js';
import { createMockTxHash } from '../lib/swapUtils.js';
import { useDirectSwapApiPreviewState, useRouteImpactPreview } from '../lib/swapPreviewHooks.js';
import { SettingsIcon, RefreshIcon, SwapDirectionIcon, InfoIcon, AlertIcon } from './swap/SwapIcons.jsx';
import { Tooltip } from './swap/SwapTooltip.jsx';
import { SwapSettings } from './swap/SwapSettings.jsx';
import { SwapSubmittedModal } from './swap/SwapSubmittedModal.jsx';
import { SwapProofPanel } from './swap/SwapProofPanel.jsx';
import SwapConfirmModal from './swap/SwapConfirmModal.jsx';
import './SwapInterface.css';

function SwapInterface({ wallet }) {
    const { upsertTransaction } = useTransactionCenter();
    const { demoMode } = useDemoMode();
    const [fromToken, setFromToken] = useState(FALLBACK_SWAP_TOKENS[0]);
    const [toToken, setToToken] = useState(FALLBACK_SWAP_TOKENS[1]);
    const [tokenModalSide, setTokenModalSide] = useState(null);
    const [customTokens, setCustomTokens] = useState([]);
    const [amountIn, setAmountIn] = useState('');
    // Exact-out mode: user specifies OUTPUT amount ("You receive") and
    // max_amount_in is derived honestly from a real inverse-CPMM quote + slippage.
    // Confined to non-advanced mode (the quote-certificate pipeline is exact-in).
    const [exactOutMode, setExactOutMode] = useState(false);
    const [amountOut, setAmountOut] = useState('');
    // Batch mode: multi-leg route batching using the route intent signer.
    // In batch mode the user enters a total input amount and the system
    // splits it across multiple pools (legs) for best execution.
    const [batchMode, setBatchMode] = useState(false);
    const [batchLegs, setBatchLegs] = useState(2);
    const [slippage, setSlippage] = useState(0.005);
    const [showSettings, setShowSettings] = useState(false);
    const [showDetails, setShowDetails] = useState(false);
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
    const [poolFeed, setPoolFeed] = useState({
        source: 'fallback',
        pools: FALLBACK_SWAP_POOLS,
        tokens: FALLBACK_SWAP_TOKENS,
        accountBalances: {},
        error: null,
    });
    const [nowMs, setNowMs] = useState(Date.now());

    const quoteDagRef = useRef(createQuoteDagCache());
    const uiSmokeSubmitRef = useRef(false);
    const tokens = useMemo(() => (
        Array.isArray(poolFeed.tokens) && poolFeed.tokens.length >= 2
            ? poolFeed.tokens
            : FALLBACK_SWAP_TOKENS
    ), [poolFeed.tokens]);
    const tokenSymbols = useMemo(() => tokens.map((token) => token.symbol), [tokens]);
    const uiSmokeSwap = useMemo(() => {
        if (typeof window === 'undefined') {
            return { enabled: false, amountIn: '', minAmountOut: '', signature: '', nonce: '', deadline: '', fromSymbol: '', toSymbol: '' };
        }
        const params = new URLSearchParams(window.location.search);
        return {
            enabled: params.get('zenodexUiSmokeSwap') === '1',
            amountIn: params.get('smokeAmountIn') || '100',
            minAmountOut: params.get('smokeMinAmountOut') || '',
            signature: params.get('smokeIntentSignature') || '',
            nonce: params.get('smokeNonce') || '',
            deadline: params.get('smokeDeadline') || '',
            fromSymbol: params.get('smokeFromSymbol') || '',
            toSymbol: params.get('smokeToSymbol') || '',
        };
    }, []);
    const uiSmokeTokenSelectSide = useMemo(() => {
        if (typeof window === 'undefined') return '';
        const side = String(new URLSearchParams(window.location.search).get('zenodexUiSmokeTokenSelect') || '').trim();
        return side === 'from' || side === 'to' ? side : '';
    }, []);

    // ── Keyboard shortcuts (power-user path) ────────────────────────
    // Alt+R: swap direction, Alt+S: toggle settings, Enter: submit
    useKeyboardShortcuts({
        'alt+r': () => handleSwapTokens(),
        'alt+s': () => setShowSettings((v) => !v),
    });

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
        }
        // Exact-out and batch live in the non-advanced path; entering advanced
        // mode reverts to exact-in single-leg so the quote-certificate pipeline
        // stays coherent.
        if (advancedMode) {
            if (exactOutMode) {
                setExactOutMode(false);
                setAmountOut('');
            }
            if (batchMode) {
                setBatchMode(false);
            }
        }
    }, [advancedMode, exactOutMode, batchMode]);

    useEffect(() => {
        let cancelled = false;
        let timer = null;
        const scheduleNext = (delayMs) => {
            if (cancelled) return;
            timer = setTimeout(runLoad, delayMs);
        };
        const runLoad = async () => {
            const next = await loadSwapPools({ timeoutMs: 2200, account: wallet?.address || '' });
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
    }, [wallet?.address]);

    useEffect(() => {
        if (tokens.length < 2) return;
        const fromKnown = tokens.some((token) => token.symbol === fromToken.symbol);
        const toKnown = tokens.some((token) => token.symbol === toToken.symbol);
        if (fromKnown && toKnown && fromToken.symbol !== toToken.symbol) return;
        setFromToken(tokens[0]);
        setToToken(tokens[1]);
        setAmountIn('');
        setQuoteError('');
    }, [tokens, fromToken.symbol, toToken.symbol]);

    useEffect(() => {
        if (!uiSmokeSwap.enabled || tokens.length < 2) return;
        const requestedFrom = String(uiSmokeSwap.fromSymbol || '').trim().toUpperCase();
        const requestedTo = String(uiSmokeSwap.toSymbol || '').trim().toUpperCase();
        if (!requestedFrom || !requestedTo || requestedFrom === requestedTo) return;
        const nextFrom = tokens.find((token) => String(token.symbol || '').trim().toUpperCase() === requestedFrom);
        const nextTo = tokens.find((token) => String(token.symbol || '').trim().toUpperCase() === requestedTo);
        if (!nextFrom || !nextTo) return;
        setFromToken(nextFrom);
        setToToken(nextTo);
    }, [uiSmokeSwap, tokens]);

    useEffect(() => {
        if (!uiSmokeSwap.enabled || poolFeed.source !== 'api' || amountIn) return;
        setAmountIn(uiSmokeSwap.amountIn);
    }, [uiSmokeSwap, poolFeed.source, amountIn]);

    useEffect(() => {
        if (!uiSmokeTokenSelectSide || poolFeed.source !== 'api') return;
        setTokenModalSide(uiSmokeTokenSelectSide);
    }, [uiSmokeTokenSelectSide, poolFeed.source]);

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

    const livePoolIntent = useMemo(() => {
        const pool = poolFeed.pools[poolKey];
        if (!pool) return null;
        const assetsBySymbol = pool.assetsBySymbol || {};
        const assetIn = assetsBySymbol[fromToken.symbol]
            || (pool.token0 === fromToken.symbol ? pool.asset0 : null)
            || (pool.token1 === fromToken.symbol ? pool.asset1 : null);
        const assetOut = assetsBySymbol[toToken.symbol]
            || (pool.token0 === toToken.symbol ? pool.asset0 : null)
            || (pool.token1 === toToken.symbol ? pool.asset1 : null);
        return {
            poolId: pool.poolId ?? pool.pool_id ?? null,
            assetIn,
            assetOut,
        };
    }, [poolFeed.pools, poolKey, fromToken.symbol, toToken.symbol]);

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

    const previewFeeBps = Number(poolFeed.pools[poolKey]?.feeBps ?? 30);
    const { apiImpactPreview, apiSlippageAdvice } = useDirectSwapApiPreviewState({
        advancedMode,
        amountIn,
        reserves,
        feeBps: previewFeeBps,
        slippage,
    });

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

    // Exact-out HONEST quote: derive the required input (and the slippage-padded
    // max_amount_in cap) from a REAL inverse-CPMM computation over live reserves
    // and the pool fee -- never a fabricated number. The settlement engine remains
    // the authority for the actual fill; this cap only bounds how much the user is
    // willing to pay. The cap is rounded UP so an honest fill within slippage is
    // not rejected by the user's own bound, and guarded against amountOut >=
    // reserveOut (unfillable: the pool cannot output its entire reserve).
    const exactOutQuote = useMemo(() => {
        if (!exactOutMode) return null;
        if (!amountOut || !reserves) return null;
        const desiredOut = parseFloat(amountOut);
        if (!Number.isFinite(desiredOut) || desiredOut <= 0) return null;
        if (desiredOut >= reserves.reserveOut) {
            return { error: 'Output exceeds pool liquidity', desiredOut };
        }
        const feeBps = Number(poolFeed.pools[poolKey]?.feeBps ?? 30);
        const feeRate = feeBps / 10_000;
        const requiredIn = calcSwapInput(reserves.reserveIn, reserves.reserveOut, desiredOut, feeRate);
        if (!Number.isFinite(requiredIn) || requiredIn <= 0) {
            return { error: 'Quote unavailable', desiredOut };
        }
        const amountOutUnits = Math.max(1, Math.round(desiredOut));
        const slippageRate = Number.isFinite(slippage) ? Math.max(0, slippage) : 0;
        const maxAmountInUnits = Math.max(1, Math.ceil(requiredIn * (1 + slippageRate)));
        return {
            error: null,
            desiredOut,
            amountOutUnits,
            requiredIn,
            maxAmountInUnits,
            feeBps,
            priceImpact: calcPriceImpact(reserves.reserveIn, reserves.reserveOut, requiredIn),
        };
    }, [exactOutMode, amountOut, reserves, poolKey, poolFeed.pools, slippage]);

    // In exact-out mode the user-entered amount is the OUTPUT, so the exact-in
    // `validation` (keyed on amountIn) does not apply; gate on the honest quote.
    const exactOutCanSubmit = Boolean(exactOutQuote) && !exactOutQuote.error;

    // Batch mode quote: split the total input across N legs, each getting
    // an equal share of the input. The output is the sum of per-leg outputs,
    // computed sequentially against the same pool (conservative: assumes all
    // legs hit the same pool state, which is the worst case for slippage).
    // This is a UI preview; the actual settlement uses the route intent signer.
    const batchQuote = useMemo(() => {
        if (!batchMode || !amountIn || !reserves) return null;
        const totalInput = parseFloat(amountIn);
        if (!Number.isFinite(totalInput) || totalInput <= 0) return null;
        const legs = Math.max(2, Math.min(5, Math.floor(batchLegs)));
        const legInput = totalInput / legs;
        const feeBps = Number(poolFeed.pools[poolKey]?.feeBps ?? 30);
        const feeRate = feeBps / 10_000;
        // Sequential execution: each leg depletes the pool
        let reserveIn = reserves.reserveIn;
        let reserveOut = reserves.reserveOut;
        let totalOutput = 0;
        const legDetails = [];
        for (let i = 0; i < legs; i++) {
            const out = calcSwapOutput(reserveIn, reserveOut, legInput, feeRate);
            if (!Number.isFinite(out) || out <= 0) {
                return { error: `Leg ${i + 1} unfillable`, totalInput, legs };
            }
            totalOutput += out;
            reserveIn += legInput;
            reserveOut -= out;
            legDetails.push({ leg: i + 1, input: legInput, output: out });
        }
        const slippageRate = Number.isFinite(slippage) ? Math.max(0, slippage) : 0;
        const minTotalOut = Math.floor(totalOutput * (1 - slippageRate));
        return {
            error: null,
            totalInput,
            legs,
            legInput,
            totalOutput,
            minTotalOut,
            legDetails,
            priceImpact: calcPriceImpact(reserves.reserveIn, reserves.reserveOut, totalInput),
            feeBps,
        };
    }, [batchMode, amountIn, batchLegs, reserves, poolKey, poolFeed.pools, slippage]);

    const batchCanSubmit = Boolean(batchQuote) && !batchQuote.error;

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

    const liveWallet = useMemo(() => {
        if (!wallet) return null;
        const accountBalances = poolFeed.source === 'api' && poolFeed.account === wallet.address
            ? (poolFeed.accountBalances || {})
            : {};
        return {
            ...wallet,
            balance: {
                ...(wallet.balance || {}),
                ...accountBalances,
            },
        };
    }, [wallet, poolFeed.source, poolFeed.account, poolFeed.accountBalances]);

    // Get user balance for from token from the live account feed when present.
    const fromBalance = liveWallet ? resolveWalletTokenBalance(liveWallet, fromToken.symbol) : null;
    const toBalance = liveWallet ? resolveWalletTokenBalance(liveWallet, toToken.symbol) : null;

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

    const routeApiImpactPreview = useRouteImpactPreview({ advancedMode, swapPreview, amountIn });

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

        if (wallet && fromBalance != null && input > fromBalance) {
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
                text: 'Price protection warning: current settings may expose your swap to unfavorable trading conditions.',
            };
        }
        if (st === 'inconclusive_mev') {
            return {
                kind: 'notice',
                text: 'Unable to fully verify trading safety. Proceed with caution.',
            };
        }
        if (st === 'no_revert_safe_option') {
            return {
                kind: 'warning',
                text: 'Current price protection settings may cause the swap to fail. Consider adjusting.',
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
        setAmountOut('');
        setQuoteError('');
    };

    const handleSelectToken = (token) => {
        if (!tokenModalSide || !token) return;
        if (tokenModalSide === 'from') {
            setFromToken(token);
        } else {
            setToToken(token);
        }
        setAmountIn('');
        setAmountOut('');
        setQuoteError('');
        setTokenModalSide(null);
    };

    const handleImportToken = (token) => {
        if (!demoMode || !token) return;
        setCustomTokens((prev) => [...prev, token]);
        handleSelectToken(token);
    };

    const handleMaxAmount = () => {
        if (wallet && fromBalance != null && fromBalance > 0) {
            setAmountIn(String(fromBalance));
            setQuoteError('');
        }
    };

    const handlePresetFraction = (fraction) => {
        if (!wallet || fromBalance == null || fromBalance <= 0) return;
        const amount = fromBalance * fraction;
        setAmountIn(amount > 0 ? String(amount) : '');
        setQuoteError('');
    };

    const handleSwapClick = () => {
        if (!wallet || isSubmitting) return;

        // Exact-out mode: gate on the honest inverse-CPMM quote, skip exact-in
        // poka-yoke/price-impact confirms (those read activePreview which is
        // not computed in exact-out mode).
        if (exactOutMode) {
            if (!exactOutCanSubmit) {
                if (exactOutQuote?.error) setQuoteError(exactOutQuote.error);
                return;
            }
            executeSwap();
            return;
        }

        // Batch mode: gate on the batch quote, skip exact-in poka-yoke.
        if (batchMode) {
            if (!batchCanSubmit) {
                if (batchQuote?.error) setQuoteError(batchQuote.error);
                return;
            }
            // Confirm on high price impact in batch mode.
            if (batchQuote.priceImpact > 0.01) {
                setTypedConfirmText('');
                setConfirmConfig({
                    title: 'Confirm Batch Swap',
                    messages: [`High price impact (${formatPercent(batchQuote.priceImpact)}). Splitting across ${batchQuote.legs} legs. Consider reducing the total amount.`],
                    reasons: ['batch_high_impact'],
                    requireTyped: false,
                    typedPhrase: null,
                    proceedText: 'Proceed Anyway',
                });
                setShowConfirm(true);
                return;
            }
            executeSwap();
            return;
        }

        if (!validation.ok) return;
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
                title: 'Confirm Swap',
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
                title: 'Confirm Swap',
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

    const resetConfirmState = useCallback(() => {
        setShowConfirm(false);
        setConfirmConfig(null);
        setTypedConfirmText('');
        setPokayokeSuggestions(null);
        setPokayokeSuggestError('');
        setPokayokeHeavySuggestions(null);
        setPokayokeHeavySuggestError('');
    }, []);

    const handleApplySlippage = useCallback((newSlippage) => {
        setSlippage(newSlippage);
        resetConfirmState();
    }, [resetConfirmState]);

    const handleApplySuggestedAmount = useCallback((amount) => {
        setAmountIn(String(amount));
        resetConfirmState();
    }, [resetConfirmState]);

    const executeSwap = useCallback(async () => {
        resetConfirmState();

        // Exact-out mode: build the submitted swap from the exact-out quote.
        if (exactOutMode) {
            if (!exactOutQuote || exactOutQuote.error) {
                setQuoteError(exactOutQuote?.error || 'Missing exact-out quote');
                return;
            }
            const submitted = {
                amountIn: formatNumber(exactOutQuote.requiredIn),
                fromSymbol: fromToken.symbol,
                amountOut: formatNumber(exactOutQuote.desiredOut),
                toSymbol: toToken.symbol,
                maxInput: formatNumber(exactOutQuote.maxAmountInUnits),
                exactOut: true,
                advanced: false,
            };
            // Reuse the same submission path as exact-in (the signer payload
            // differs in the kind/amount fields, handled below).
            setIsSubmitting(true);
            try {
                const submittedAt = Date.now();
                const txId = `swap-${submittedAt}-${Math.random().toString(16).slice(2, 8)}`;
                let txHash = '';
                let submitPath = 'local';
                let remoteAccepted = false;
                let remoteHeight = null;
                let remoteReceipt = null;
                if (!demoMode && poolFeed.source !== 'api') {
                    setQuoteError('Live swap submission requires a live pool feed');
                    return;
                }
                try {
                    const amountOutUnits = exactOutQuote.amountOutUnits;
                    const maxAmountInUnits = exactOutQuote.maxAmountInUnits;
                    const currentPool = poolFeed.pools[poolKey];
                    const intentDeadline = 1_999_999_999;
                    const nextNonce = Number.isSafeInteger(poolFeed.accountLastNonce)
                        ? poolFeed.accountLastNonce + 1 : null;
                    if (!Number.isSafeInteger(nextNonce) || nextNonce <= 0) {
                        throw new Error('swap_nonce_unavailable');
                    }
                    const signed = await buildAndSignSwapIntent({
                        pool: currentPool,
                        payload: {
                            poolId: livePoolIntent?.poolId,
                            assetIn: livePoolIntent?.assetIn,
                            assetOut: livePoolIntent?.assetOut,
                            kind: 'SWAP_EXACT_OUT',
                            amountOut: amountOutUnits,
                            maxAmountIn: maxAmountInUnits,
                            senderPubkey: wallet?.address,
                            recipient: wallet?.address,
                            deadline: intentDeadline,
                            nonce: nextNonce,
                        },
                        privkey: wallet?.privkey,
                        signDexIntent: wallet?.signDexIntentForEngine || wallet?.signDexIntent,
                        chainId: getRuntimeConfig().chainId || wallet?.chainId || 'zeno-ledger-localtest-v0',
                    });
                    const maybeRemote = await apiSwap(
                        {
                            from: fromToken.symbol,
                            to: toToken.symbol,
                            kind: 'exact_out',
                            amountOut: amountOutUnits,
                            maxAmountIn: maxAmountInUnits,
                            poolId: livePoolIntent?.poolId,
                            assetIn: livePoolIntent?.assetIn,
                            assetOut: livePoolIntent?.assetOut,
                            senderPubkey: wallet?.address,
                            recipient: wallet?.address,
                            signature: signed.signature,
                            nonce: signed.intent.nonce,
                            deadline: signed.intent.deadline,
                            timeMs: submittedAt,
                            txId,
                        },
                        { timeoutMs: 3500 },
                    );
                    if (maybeRemote?.ok === false) {
                        throw new Error(maybeRemote?.error || 'swap_rejected');
                    }
                    if (maybeRemote?.txHash || maybeRemote?.tx_hash) {
                        txHash = String(maybeRemote.txHash || maybeRemote.tx_hash);
                    }
                    remoteReceipt = maybeRemote?.receipt || null;
                    remoteAccepted = maybeRemote?.tx_accepted === true || remoteReceipt?.accepted === true;
                    remoteHeight = maybeRemote?.height ?? null;
                    submitPath = 'api';
                    loadSwapPools({ timeoutMs: 2200, account: wallet?.address || '' })
                        .then((next) => setPoolFeed(next))
                        .catch(() => {});
                } catch (err) {
                    if (!demoMode) {
                        const msg = err && typeof err === 'object' ? String(err.message || 'swap_submit_failed') : 'swap_submit_failed';
                        setQuoteError(`Live swap submission failed: ${msg}`);
                        return;
                    }
                    txHash = createMockTxHash();
                    submitPath = 'local-fallback';
                }
                if (!txHash) {
                    if (!demoMode) {
                        setQuoteError('Live swap submission failed: missing transaction hash');
                        return;
                    }
                    txHash = createMockTxHash();
                }
                const transactionStatus = remoteAccepted ? 'confirmed' : 'pending';
                setSubmittedSwap({
                    ...submitted,
                    txId,
                    txHash,
                    network: 'Tau Net Alpha',
                    status: transactionStatus,
                    submittedAt,
                    submitPath,
                    height: remoteHeight,
                    receipt: remoteReceipt,
                });
                upsertTransaction({
                    txId,
                    txHash,
                    kind: 'swap_exact_out',
                    status: transactionStatus,
                    fromToken: fromToken.symbol,
                    toToken: toToken.symbol,
                    amountIn: submitted.amountIn,
                    amountOut: submitted.amountOut,
                    submittedAt,
                    height: remoteHeight,
                });
                setAmountOut('');
            } finally {
                setIsSubmitting(false);
            }
            return;
        }

        // Batch mode: build the submitted swap from the batch quote.
        if (batchMode) {
            if (!batchQuote || batchQuote.error) {
                setQuoteError(batchQuote?.error || 'Missing batch quote');
                return;
            }
            const submitted = {
                amountIn,
                fromSymbol: fromToken.symbol,
                amountOut: formatNumber(batchQuote.totalOutput),
                toSymbol: toToken.symbol,
                minOutput: formatNumber(batchQuote.minTotalOut),
                batch: true,
                legs: batchQuote.legs,
                legDetails: batchQuote.legDetails,
                advanced: false,
            };
            setIsSubmitting(true);
            try {
                const submittedAt = Date.now();
                const txId = `batch-${submittedAt}-${Math.random().toString(16).slice(2, 8)}`;
                let txHash = '';
                let submitPath = 'local';
                let remoteAccepted = false;
                let remoteHeight = null;
                let remoteReceipt = null;
                if (!demoMode && poolFeed.source !== 'api') {
                    setQuoteError('Live swap submission requires a live pool feed');
                    return;
                }
                try {
                    const totalAmountInUnits = Math.max(1, Math.round(Number(amountIn)));
                    const minAmountOutUnits = batchQuote.minTotalOut;
                    const currentPool = poolFeed.pools[poolKey];
                    const intentDeadline = 1_999_999_999;
                    const nextNonce = Number.isSafeInteger(poolFeed.accountLastNonce)
                        ? poolFeed.accountLastNonce + 1 : null;
                    if (!Number.isSafeInteger(nextNonce) || nextNonce <= 0) {
                        throw new Error('swap_nonce_unavailable');
                    }
                    const signed = await buildAndSignSwapIntent({
                        pool: currentPool,
                        payload: {
                            poolId: livePoolIntent?.poolId,
                            assetIn: livePoolIntent?.assetIn,
                            assetOut: livePoolIntent?.assetOut,
                            kind: 'SWAP_BATCH',
                            amountIn: totalAmountInUnits,
                            minAmountOut: minAmountOutUnits,
                            legs: batchQuote.legs,
                            senderPubkey: wallet?.address,
                            recipient: wallet?.address,
                            deadline: intentDeadline,
                            nonce: nextNonce,
                        },
                        privkey: wallet?.privkey,
                        signDexIntent: wallet?.signDexIntentForEngine || wallet?.signDexIntent,
                        chainId: getRuntimeConfig().chainId || wallet?.chainId || 'zeno-ledger-localtest-v0',
                    });
                    const maybeRemote = await apiSwap(
                        {
                            from: fromToken.symbol,
                            to: toToken.symbol,
                            kind: 'batch',
                            amountIn: totalAmountInUnits,
                            minAmountOut: minAmountOutUnits,
                            legs: batchQuote.legs,
                            poolId: livePoolIntent?.poolId,
                            assetIn: livePoolIntent?.assetIn,
                            assetOut: livePoolIntent?.assetOut,
                            senderPubkey: wallet?.address,
                            recipient: wallet?.address,
                            signature: signed.signature,
                            nonce: signed.intent.nonce,
                            deadline: signed.intent.deadline,
                            timeMs: submittedAt,
                            txId,
                        },
                        { timeoutMs: 3500 },
                    );
                    if (maybeRemote?.ok === false) {
                        throw new Error(maybeRemote?.error || 'swap_rejected');
                    }
                    if (maybeRemote?.txHash || maybeRemote?.tx_hash) {
                        txHash = String(maybeRemote.txHash || maybeRemote.tx_hash);
                    }
                    remoteReceipt = maybeRemote?.receipt || null;
                    remoteAccepted = maybeRemote?.tx_accepted === true || remoteReceipt?.accepted === true;
                    remoteHeight = maybeRemote?.height ?? null;
                    submitPath = 'api';
                    loadSwapPools({ timeoutMs: 2200, account: wallet?.address || '' })
                        .then((next) => setPoolFeed(next))
                        .catch(() => {});
                } catch (err) {
                    if (!demoMode) {
                        const msg = err && typeof err === 'object' ? String(err.message || 'swap_submit_failed') : 'swap_submit_failed';
                        setQuoteError(`Live batch swap submission failed: ${msg}`);
                        return;
                    }
                    txHash = createMockTxHash();
                    submitPath = 'local-fallback';
                }
                if (!txHash) {
                    if (!demoMode) {
                        setQuoteError('Live swap submission failed: missing transaction hash');
                        return;
                    }
                    txHash = createMockTxHash();
                }
                const transactionStatus = remoteAccepted ? 'confirmed' : 'pending';
                setSubmittedSwap({
                    ...submitted,
                    txId,
                    txHash,
                    network: 'Tau Net Alpha',
                    status: transactionStatus,
                    submittedAt,
                    submitPath,
                    height: remoteHeight,
                    receipt: remoteReceipt,
                });
                upsertTransaction({
                    txId,
                    txHash,
                    kind: 'swap_batch',
                    status: transactionStatus,
                    fromToken: fromToken.symbol,
                    toToken: toToken.symbol,
                    amountIn: submitted.amountIn,
                    amountOut: submitted.amountOut,
                    submittedAt,
                    height: remoteHeight,
                });
            } finally {
                setIsSubmitting(false);
            }
            return;
        }

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
            let txHash = '';
            let submitPath = 'local';
            let remoteAccepted = false;
            let remoteHeight = null;
            let remoteReceipt = null;
            if (!demoMode && poolFeed.source !== 'api') {
                setQuoteError('Live swap submission requires a live pool feed');
                return;
            }
            try {
                const amountInUnits = Math.max(1, Math.round(Number(amountIn)));
                const minAmountOutUnits = uiSmokeSwap.minAmountOut
                    ? Math.max(0, Math.floor(Number(uiSmokeSwap.minAmountOut)))
                    : Math.max(0, Math.floor(Number(activePreview.minOutput ?? 1)));
                const currentPool = poolFeed.pools[poolKey];
                let intentSignature = uiSmokeSwap.signature || undefined;
                let intentNonce = uiSmokeSwap.nonce ? Number(uiSmokeSwap.nonce) : null;
                let intentDeadline = uiSmokeSwap.deadline ? Number(uiSmokeSwap.deadline) : 1_999_999_999;
                if (!Number.isSafeInteger(intentDeadline) || intentDeadline <= 0) {
                    throw new Error('swap_deadline_unavailable');
                }
                if (!intentSignature) {
                    const nextNonce = Number.isSafeInteger(poolFeed.accountLastNonce)
                        ? poolFeed.accountLastNonce + 1
                        : null;
                    if (!Number.isSafeInteger(nextNonce) || nextNonce <= 0) {
                        throw new Error('swap_nonce_unavailable');
                    }
                    const signed = await buildAndSignSwapIntent({
                        pool: currentPool,
                        payload: {
                            poolId: livePoolIntent?.poolId,
                            assetIn: livePoolIntent?.assetIn,
                            assetOut: livePoolIntent?.assetOut,
                            amountIn: amountInUnits,
                            minAmountOut: minAmountOutUnits,
                            senderPubkey: wallet?.address,
                            recipient: wallet?.address,
                            deadline: intentDeadline,
                            nonce: nextNonce,
                        },
                        privkey: wallet?.privkey,
                        signDexIntent: wallet?.signDexIntentForEngine || wallet?.signDexIntent,
                        chainId: getRuntimeConfig().chainId || wallet?.chainId || 'zeno-ledger-localtest-v0',
                    });
                    intentSignature = signed.signature;
                    intentNonce = signed.intent.nonce;
                    intentDeadline = signed.intent.deadline;
                }
                const maybeRemote = await apiSwap(
                    {
                        from: fromToken.symbol,
                        to: toToken.symbol,
                        amountIn: amountInUnits,
                        minAmountOut: minAmountOutUnits,
                        poolId: livePoolIntent?.poolId,
                        assetIn: livePoolIntent?.assetIn,
                        assetOut: livePoolIntent?.assetOut,
                        senderPubkey: wallet?.address,
                        recipient: wallet?.address,
                        signature: intentSignature,
                        nonce: intentNonce || undefined,
                        deadline: intentDeadline,
                        timeMs: submittedAt,
                        txId,
                    },
                    { timeoutMs: 3500 },
                );
                if (maybeRemote?.ok === false) {
                    throw new Error(maybeRemote?.error || 'swap_rejected');
                }
                if (maybeRemote?.txHash || maybeRemote?.tx_hash) {
                    txHash = String(maybeRemote.txHash || maybeRemote.tx_hash);
                }
                remoteReceipt = maybeRemote?.receipt || null;
                remoteAccepted = maybeRemote?.tx_accepted === true || remoteReceipt?.accepted === true;
                remoteHeight = maybeRemote?.height ?? null;
                submitPath = 'api';
                loadSwapPools({ timeoutMs: 2200, account: wallet?.address || '' })
                    .then((next) => setPoolFeed(next))
                    .catch(() => {});
            } catch (err) {
                if (!demoMode) {
                    const msg = err && typeof err === 'object' ? String(err.message || 'swap_submit_failed') : 'swap_submit_failed';
                    setQuoteError(`Live swap submission failed: ${msg}`);
                    return;
                }
                txHash = createMockTxHash();
                submitPath = 'local-fallback';
            }
            if (!txHash) {
                if (!demoMode) {
                    setQuoteError('Live swap submission failed: missing transaction hash');
                    return;
                }
                txHash = createMockTxHash();
            }
            const transactionStatus = remoteAccepted ? 'confirmed' : 'pending';

            setSubmittedSwap({
                ...submitted,
                txId,
                txHash,
                network: 'Tau Net Alpha',
                status: transactionStatus,
                submitPath,
                height: remoteHeight,
                receipt: remoteReceipt,
                submittedAt,
                confirmedAt: remoteAccepted ? submittedAt : null,
            });
            upsertTransaction({
                id: txId,
                status: transactionStatus,
                product: 'swap',
                title: `Swap ${fromToken.symbol} -> ${toToken.symbol}`,
                routePath: submitted.routePath,
                txHash,
                network: 'Tau Net Alpha',
                createdAt: submittedAt,
                confirmedAt: remoteAccepted ? submittedAt : null,
            });
            setAmountIn('');
            setQuoteError('');
        } finally {
            setIsSubmitting(false);
        }
    }, [amountIn, fromToken, toToken, activePreview, quotePayload, quoteCertificate, effectiveProfileConfig.label, advancedMode, upsertTransaction, demoMode, poolFeed, poolKey, livePoolIntent, wallet, uiSmokeSwap, resetConfirmState, exactOutMode, exactOutQuote, batchMode, batchQuote]);

    useEffect(() => {
        if (!uiSmokeSwap.enabled) return;
        if (uiSmokeSubmitRef.current) return;
        if (!wallet || poolFeed.source !== 'api' || isSubmitting || submittedSwap) return;
        if (!amountIn || !activePreview || !validation.ok) return;
        if (advancedMode && !certificateCheck.ok) return;
        try {
            if (window.sessionStorage.getItem('zenodex.uiSmokeSwap.submitted') === '1') {
                return;
            }
            window.sessionStorage.setItem('zenodex.uiSmokeSwap.submitted', '1');
        } catch {
            // Session storage is a test convenience; the ref still prevents repeats in normal browsers.
        }
        uiSmokeSubmitRef.current = true;
        executeSwap();
    }, [
        uiSmokeSwap.enabled,
        wallet,
        poolFeed.source,
        isSubmitting,
        submittedSwap,
        amountIn,
        activePreview,
        validation.ok,
        advancedMode,
        certificateCheck.ok,
        executeSwap,
    ]);

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
        if (exactOutMode) {
            if (!amountOut) return 'Enter Output Amount';
            if (exactOutQuote?.error) return exactOutQuote.error;
            if (!exactOutCanSubmit) return 'Invalid Quote';
            return 'Swap (Exact Out)';
        }
        if (batchMode) {
            if (!amountIn) return 'Enter Total Amount';
            if (batchQuote?.error) return batchQuote.error;
            if (!batchCanSubmit) return 'Invalid Batch Quote';
            return `Batch Swap (${batchQuote.legs} legs)`;
        }
        if (!amountIn) return 'Enter Amount';
        if (advancedMode && quoteError) return quoteError;
        if (advancedMode && activePreview && !certificateCheck.ok) return 'Quote Not Certified';
        if (validation.error) return validation.error;
        if (!validation.ok) return 'Invalid Swap';
        return 'Swap';
    };

    const impactSeverity = activePreview ? getPriceImpactSeverity(activePreview.priceImpact) : 'low';
    const routeProfiles = listRouteProfiles();

    // ── Runtime verification posture (honest, node-reported) ──────────────
    // Strict ZK + a subprocess verifier means the mounted live write gates are
    // proof-wrapper checked. Spot swap still reports Tau-spec math posture here
    // unless a dedicated spot proof surface is advertised by the node.
    const zkPosture = getRuntimeConfig()?.localTestnetZkPosture || {};
    const proofEnforced = zkPosture.zk_required === true
        && zkPosture.zk_mode_effective === 'strict'
        && zkPosture.proof_verifier_kind === 'subprocess';
    const postureKnown = Boolean(zkPosture.zk_mode_effective);

    // ── Market rail derived values ────────────────────────────────────────
    const livePool = poolFeed.pools[poolKey] || null;
    const railFeeBps = Number(livePool?.feeBps ?? 30);
    const midPrice = reserves ? reserves.reserveOut / reserves.reserveIn : null;
    const invariantK = reserves ? reserves.reserveIn * reserves.reserveOut : null;
    const depthInPct = reserves
        ? Math.max(4, Math.min(96, (reserves.reserveIn / (reserves.reserveIn + reserves.reserveOut)) * 100))
        : 50;
    const fmtBig = (n) => {
        if (!Number.isFinite(n)) return '—';
        const abs = Math.abs(n);
        if (abs >= 1e12) return `${(n / 1e12).toFixed(2)}T`;
        if (abs >= 1e9) return `${(n / 1e9).toFixed(2)}B`;
        if (abs >= 1e6) return `${(n / 1e6).toFixed(2)}M`;
        if (abs >= 1e3) return `${(n / 1e3).toFixed(2)}K`;
        return n.toLocaleString(undefined, { maximumFractionDigits: 2 });
    };

    // Position of the expected output within the worst→best envelope (honest,
    // data-driven; falls back to centre when bounds are unavailable).
    const envHasBounds = Boolean(
        activePreview
        && Number.isFinite(activePreview.amountOutWorstCase)
        && Number.isFinite(activePreview.amountOutBestCase)
        && activePreview.amountOutBestCase > activePreview.amountOutWorstCase,
    );
    const envPos = envHasBounds
        ? Math.max(2, Math.min(98, ((activePreview.output - activePreview.amountOutWorstCase)
            / (activePreview.amountOutBestCase - activePreview.amountOutWorstCase)) * 100))
        : 50;

    const marketRail = (
        <aside className="swap-market panel" aria-label="Market reserves">
            <div className="swap-rail-head">
                <span className="swap-rail-eyebrow">Market</span>
                <h3 className="swap-rail-pair">
                    <span className="token-icon-small">{fromToken.icon}</span>
                    {fromToken.symbol}
                    <span className="swap-rail-sep">/</span>
                    <span className="token-icon-small">{toToken.icon}</span>
                    {toToken.symbol}
                </h3>
            </div>
            {reserves ? (
                <>
                    <div className="swap-rail-price">
                        <span className="swap-rail-price-value mono">{midPrice ? formatNumber(midPrice, 6) : '—'}</span>
                        <span className="swap-rail-price-unit">{toToken.symbol} per {fromToken.symbol}</span>
                    </div>
                    <dl className="swap-rail-stats">
                        <div className="swap-rail-stat">
                            <dt>Reserve {fromToken.symbol}</dt>
                            <dd className="mono">{fmtBig(reserves.reserveIn)}</dd>
                        </div>
                        <div className="swap-rail-stat">
                            <dt>Reserve {toToken.symbol}</dt>
                            <dd className="mono">{fmtBig(reserves.reserveOut)}</dd>
                        </div>
                        <div className="swap-rail-stat">
                            <dt>Invariant k</dt>
                            <dd className="mono">{fmtBig(invariantK)}</dd>
                        </div>
                        <div className="swap-rail-stat">
                            <dt>LP fee</dt>
                            <dd className="mono">{(railFeeBps / 100).toFixed(2)}%</dd>
                        </div>
                    </dl>
                    <div className="swap-rail-depth">
                        <div className="swap-rail-depth-bar" title="Reserve balance between the two assets">
                            <span className="swap-rail-depth-in" style={{ width: `${depthInPct}%` }} />
                            <span className="swap-rail-depth-out" style={{ width: `${100 - depthInPct}%` }} />
                        </div>
                        <div className="swap-rail-depth-legend">
                            <span>{fromToken.symbol}</span>
                            <span>{toToken.symbol}</span>
                        </div>
                    </div>
                    <div className={`swap-rail-feed ${poolFeed.source === 'api' ? 'is-live' : 'is-snapshot'}`}>
                        <span className="swap-rail-dot" aria-hidden="true" />
                        {poolFeed.source === 'api' ? 'Live pool feed' : 'Reference snapshot'}
                    </div>
                </>
            ) : (
                <div className="swap-rail-empty">
                    <p className="swap-rail-empty-title">No live pool for {fromToken.symbol}/{toToken.symbol}</p>
                    <p className="swap-rail-empty-hint">Pick a pair with an active pool, or add liquidity from the Pools tab to seed reserves.</p>
                </div>
            )}
        </aside>
    );

    const proofPanel = (
        <SwapProofPanel
            proofEnforced={proofEnforced}
            postureKnown={postureKnown}
            zkPosture={zkPosture}
            advancedMode={advancedMode}
            certificateCheck={certificateCheck}
            activePreview={activePreview}
            impactSeverity={impactSeverity}
            envHasBounds={envHasBounds}
            envPos={envPos}
            toToken={toToken}
            submittedSwap={submittedSwap}
        />
    );

    return (
        <div className="swap-instrument">
            {marketRail}
            <div className="swap-panel panel">
            <div className="swap-header">
                <div className="swap-header-titles">
                    <h2>Swap</h2>
                    {proofEnforced ? (
                        <VerifiedBySpec
                            spec="cpmm_v1"
                            kind="tau"
                            title={`Swap math verified by the mathematical proof system using the ${zkPosture.proof_verifier_kind} verifier.`}
                        />
                    ) : (
                        <Tooltip text={`Swap math follows specification, but proof verification is currently disabled for testing.`}>
                            <span className="swap-spec-advisory">Verified math · proofs off</span>
                        </Tooltip>
                    )}
                </div>
                <div className="swap-header-actions">
                    <span className={`refresh-indicator ${isRefreshing ? 'active' : ''}`} title="Prices refresh every 15s">
                        <RefreshIcon />
                    </span>
                    <button
                        type="button"
                        className="settings-btn"
                        onClick={() => setShowSettings(!showSettings)}
                        title="Transaction settings"
                        aria-label="Transaction settings"
                        aria-expanded={showSettings}
                    >
                        <SettingsIcon />
                    </button>
                </div>
            </div>

            {showSettings && (
                <SwapSettings
                    suggestedSlippage={suggestedSlippage}
                    slippage={slippage}
                    setSlippage={setSlippage}
                    slippageAdviceNotice={slippageAdviceNotice}
                    pokayokeEnabled={pokayokeEnabled}
                    setPokayokeEnabled={setPokayokeEnabled}
                    advancedMode={advancedMode}
                    setAdvancedMode={setAdvancedMode}
                    autoProfile={autoProfile}
                    setAutoProfile={setAutoProfile}
                    profileSlider={profileSlider}
                    setProfileSlider={setProfileSlider}
                    effectiveProfileConfig={effectiveProfileConfig}
                    routeProfiles={routeProfiles}
                />
            )}

            {/* Swap mode toggle: Exact In / Exact Out / Batch.
                All three modes are always accessible; the batch leg count
                selector appears below when batch mode is active. */}
            {!advancedMode && (
                <div className="swap-mode-toggle" role="group" aria-label="Swap mode">
                    <button
                        type="button"
                        className={`swap-mode-btn ${!exactOutMode && !batchMode ? 'active' : ''}`}
                        data-mode="exact_in"
                        aria-pressed={!exactOutMode && !batchMode}
                        disabled={isSubmitting}
                        onClick={() => {
                            if (exactOutMode || batchMode) {
                                setExactOutMode(false);
                                setBatchMode(false);
                                setAmountOut('');
                                setAmountIn('');
                                setQuoteError('');
                            }
                        }}
                        title="Enter the amount you want to swap"
                    >
                        Pay exact amount
                    </button>
                    <button
                        type="button"
                        className={`swap-mode-btn ${exactOutMode ? 'active' : ''}`}
                        data-mode="exact_out"
                        aria-pressed={exactOutMode}
                        disabled={isSubmitting}
                        onClick={() => {
                            if (!exactOutMode) {
                                setExactOutMode(true);
                                setBatchMode(false);
                                setAmountIn('');
                                setQuoteError('');
                            }
                        }}
                        title="Enter the amount you want to receive"
                    >
                        Receive exact amount
                    </button>
                    <button
                        type="button"
                        className={`swap-mode-btn ${batchMode ? 'active' : ''}`}
                        data-mode="batch"
                        aria-pressed={batchMode}
                        disabled={isSubmitting}
                        onClick={() => {
                            if (!batchMode) {
                                setBatchMode(true);
                                setExactOutMode(false);
                                setAmountOut('');
                                setQuoteError('');
                            }
                        }}
                        title="Split your swap across multiple pools for better rates"
                    >
                        Split across pools
                    </button>
                </div>
            )}

            {/* Batch leg count selector — visible whenever batch mode is active */}
            {batchMode && !advancedMode && (
                <div className="batch-legs-selector" role="group" aria-label="Batch leg count">
                    <span className="batch-legs-label">Pools:</span>
                    {[2, 3, 4, 5].map(n => (
                        <button
                            key={n}
                            type="button"
                            className={`swap-preset-btn ${batchLegs === n ? 'active' : ''}`}
                            onClick={() => setBatchLegs(n)}
                            disabled={isSubmitting}
                        >
                            {n}
                        </button>
                    ))}
                </div>
            )}

            {/* From Token */}
            <div className={`swap-input-container ${validation.error && amountIn && !exactOutMode ? 'has-error' : ''}`}>
                <div className="swap-input-header">
                    <span className="label">
                        {exactOutMode ? 'You pay (max ≤, estimated)' : batchMode ? 'Total In' : 'From'}
                    </span>
                    <button
                        type="button"
                        className="balance"
                        onClick={exactOutMode ? undefined : handleMaxAmount}
                        disabled={exactOutMode || !wallet || fromBalance == null || fromBalance <= 0}
                        style={{ cursor: wallet && !exactOutMode && fromBalance != null && fromBalance > 0 ? 'pointer' : 'default' }}
                    >
                        Balance: {wallet ? (fromBalance == null ? 'N/A' : formatNumber(fromBalance)) : '-'}
                        {wallet && !exactOutMode && fromBalance != null && fromBalance > 0 && <span className="max-label"> (MAX)</span>}
                    </button>
                </div>
                <div className="swap-input-row">
                    {exactOutMode ? (
                        <input
                            type="text"
                            className="input input-large swap-amount-input"
                            placeholder="0.0"
                            title="Maximum amount you'll pay, calculated from your desired amount and price protection"
                            value={exactOutQuote && !exactOutQuote.error ? formatNumber(exactOutQuote.maxAmountInUnits) : ''}
                            readOnly
                            aria-label={`Maximum input, derived from quote plus ${formatPercent(slippage)} slippage`}
                        />
                    ) : (
                        <input
                            type="number"
                            className="input input-large swap-amount-input"
                            placeholder="0.0"
                            value={amountIn}
                            onChange={(e) => setAmountIn(e.target.value)}
                            min="0"
                            step="any"
                            aria-label={`Amount of ${fromToken?.symbol || 'token'} to swap`}
                            aria-describedby="swap-from-hint"
                        />
                    )}
                    <button
                        className="token-selector"
                        type="button"
                        onClick={() => setTokenModalSide('from')}
                        title="Select source token"
                        aria-label={`Select from token, currently ${fromToken?.symbol || 'none'}`}
                        aria-haspopup="dialog"
                    >
                        <span className="token-icon-small">{fromToken.icon}</span>
                        <span>{fromToken.symbol}</span>
                    </button>
                </div>
                {exactOutMode && exactOutQuote && !exactOutQuote.error && (
                    <div className="input-hint">
                        <div>
                            Est. input ~{formatNumber(exactOutQuote.requiredIn)} {fromToken.symbol}; cap ≤ {formatNumber(exactOutQuote.maxAmountInUnits)} (slippage {formatPercent(slippage)})
                        </div>
                        <div className="exact-out-impact-row swap-detail-row">
                            <span>Price Impact</span>
                            <span className={exactOutQuote.priceImpact > 0.02 ? 'impact-high' : 'impact-low'}>
                                {formatPercent(exactOutQuote.priceImpact)}
                                {exactOutQuote.priceImpact > 0.02 && <AlertIcon className="icon-warning" />}
                            </span>
                        </div>
                    </div>
                )}
                {exactOutMode && exactOutQuote && exactOutQuote.error && (
                    <div className="input-error-hint">{exactOutQuote.error}</div>
                )}
                {!exactOutMode && !batchMode && wallet && fromBalance != null && fromBalance > 0 && (
                    <div className="swap-presets" role="group" aria-label="Quick fill from balance">
                        <button
                            type="button"
                            className="swap-preset-btn"
                            onClick={() => handlePresetFraction(0.25)}
                        >
                            25%
                        </button>
                        <button
                            type="button"
                            className="swap-preset-btn"
                            onClick={() => handlePresetFraction(0.5)}
                        >
                            50%
                        </button>
                        <button
                            type="button"
                            className="swap-preset-btn"
                            onClick={() => handlePresetFraction(0.75)}
                        >
                            75%
                        </button>
                        <button
                            type="button"
                            className="swap-preset-btn swap-preset-max"
                            onClick={handleMaxAmount}
                        >
                            MAX
                        </button>
                    </div>
                )}
                {!exactOutMode && !batchMode && validation.error && amountIn && (
                    <div id="swap-from-hint" className="input-error-hint" role="alert" aria-live="polite">{validation.error}</div>
                )}
            </div>

            {/* Swap Direction Button */}
            <div className="swap-direction">
                <button
                    className="swap-direction-btn"
                    onClick={handleSwapTokens}
                    title="Swap tokens (Alt+R)"
                    aria-label={`Swap direction: from ${fromToken?.symbol || 'token'} to ${toToken?.symbol || 'token'}`}
                    type="button"
                >
                    <SwapDirectionIcon />
                </button>
            </div>

            {/* To Token */}
            <div className="swap-input-container">
                <div className="swap-input-header">
                    <span className="label">{exactOutMode ? 'You receive (exact)' : batchMode ? 'Total Out (estimated)' : 'To (estimated)'}</span>
                    <span className="balance">Balance: {wallet ? (toBalance == null ? 'N/A' : formatNumber(toBalance)) : '-'}</span>
                </div>
                <div className="swap-input-row">
                    {exactOutMode ? (
                        <input
                            type="number"
                            className="input input-large swap-amount-input"
                            placeholder="0.0"
                            title="Exact output amount (amount_out) you want to receive"
                            value={amountOut}
                            onChange={(e) => setAmountOut(e.target.value)}
                            min="0"
                            step="any"
                        />
                    ) : (
                        <input
                            type="text"
                            className="input input-large swap-amount-input"
                            placeholder="0.0"
                            value={batchMode
                                ? (batchQuote && !batchQuote.error ? formatNumber(batchQuote.totalOutput) : '')
                                : (activePreview ? formatNumber(activePreview.output) : '')}
                            readOnly
                        />
                    )}
                    <button
                        className="token-selector"
                        type="button"
                        onClick={() => setTokenModalSide('to')}
                        title="Select destination token"
                        aria-label={`Select to token, currently ${toToken?.symbol || 'none'}`}
                        aria-haspopup="dialog"
                    >
                        <span className="token-icon-small">{toToken.icon}</span>
                        <span>{toToken.symbol}</span>
                    </button>
                </div>
            </div>

            {/* Batch leg breakdown */}
            {batchMode && batchQuote && !batchQuote.error && batchQuote.legDetails && (
                <div className="batch-leg-breakdown animate-fade-in">
                    <div className="batch-leg-breakdown-head">
                        <span>Batch Breakdown</span>
                        <span className="batch-legs-badge">{batchQuote.legs} pools</span>
                    </div>
                    {batchQuote.legDetails.map(leg => (
                        <div key={leg.leg} className="batch-leg-row swap-detail-row">
                            <span>Pool {leg.leg}</span>
                            <span className="mono">
                                {formatNumber(leg.input)} → {formatNumber(leg.output)} {toToken.symbol}
                            </span>
                        </div>
                    ))}
                    <div className="batch-leg-row swap-detail-row">
                        <span>Price Impact</span>
                        <span className={batchQuote.priceImpact > 0.02 ? 'impact-high' : 'impact-low'}>
                            {formatPercent(batchQuote.priceImpact)}
                            {batchQuote.priceImpact > 0.02 && <AlertIcon className="icon-warning" />}
                        </span>
                    </div>
                    <div className="batch-leg-row swap-detail-row">
                        <span>Min Total Out</span>
                        <span>{formatNumber(batchQuote.minTotalOut)} {toToken.symbol}</span>
                    </div>
                </div>
            )}
            {batchMode && batchQuote && batchQuote.error && (
                <div className="input-error-hint">{batchQuote.error}</div>
            )}

            {/* Swap Details — critical info always visible, rest collapsible */}
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
                            {impactSeverity === 'high' && <AlertIcon className="icon-warning" />}
                        </span>
                    </div>
                    <div className="swap-detail-row">
                        <Tooltip text="Minimum you'll receive after slippage">
                            <span>Minimum Received</span>
                        </Tooltip>
                        <span>{formatNumber(activePreview.minOutput)} {toToken.symbol}</span>
                    </div>
                    <button
                        type="button"
                        className="swap-details-toggle"
                        aria-expanded={showDetails}
                        onClick={() => setShowDetails(v => !v)}
                    >
                        {showDetails ? 'Hide details' : 'Show details'}
                        <span className={`swap-details-chevron ${showDetails ? 'open' : ''}`} aria-hidden="true">▾</span>
                    </button>
                    {showDetails && (
                    <>
                    <div className="swap-detail-row">
                        <Tooltip text="Fee paid to liquidity providers">
                            <span>Fee (est.)</span>
                        </Tooltip>
                        <span>{formatNumber(activePreview.feePaidEstimate)} {fromToken.symbol}</span>
                    </div>
                    {Number.isFinite(activePreview.amountOutWorstCase) && Number.isFinite(activePreview.amountOutBestCase) && (
                        <div className="swap-detail-row">
                            <Tooltip text="Expected output range based on current market conditions">
                                <span>Output Range</span>
                            </Tooltip>
                            <span>
                                {formatNumber(activePreview.amountOutWorstCase)} - {formatNumber(activePreview.amountOutBestCase)} {toToken.symbol}
                            </span>
                        </div>
                    )}
                    <div className="swap-detail-row">
                        <Tooltip text="Source of price data for this quote">
                            <span>Data Source</span>
                        </Tooltip>
                        <span className={poolFeed.source === 'api' ? 'impact-low' : 'impact-medium'}>
                            {poolFeed.source === 'api' ? 'Live market data' : 'Cached data'}
                        </span>
                    </div>
                    {advancedMode && (
                        <>
                            <div className="swap-detail-row">
                                <Tooltip text="Selected swap path and settings">
                                    <span>Swap Path</span>
                                </Tooltip>
                                <span>{activePreview.routePath} ({activePreview.profileLabel})</span>
                            </div>
                            <div className="swap-detail-row">
                                <Tooltip text="Safety checks for multi-pool swaps">
                                    <span>Safety Checks</span>
                                </Tooltip>
                                <span>
                                    S={formatNumber(activePreview.gateDecision.stress, 3)} / P={formatNumber(activePreview.gateDecision.pressure, 3)}
                                    {activePreview.gateDecision.considerTwoHop ? ' (multi-pool check on)' : ' (multi-pool check off)'}
                                </span>
                            </div>
                            <div className="swap-detail-row">
                                <Tooltip text="Price quote is verified before submitting your swap">
                                    <span>Quote Verified</span>
                                </Tooltip>
                                <span className={certificateCheck.ok ? 'impact-low' : 'impact-high'}>
                                    {certificateCheck.ok
                                        ? `Verified (${Math.floor(certificateCheck.remainingMs / 1000)}s)`
                                        : `Invalid (${certificateCheck.reason})`}
                                </span>
                            </div>
                            <div className="swap-detail-row">
                                <Tooltip text="Computation stats for performance monitoring">
                                    <span>Computation Stats</span>
                                </Tooltip>
                                <span>
                                    calls={activePreview.quoteCallCount}, hits={swapQuote?.diagnostics?.hitsDelta ?? 0}, recomputes={swapQuote?.diagnostics?.recomputesDelta ?? 0}
                                    {activePreview.previewSource ? `, from ${activePreview.previewSource}` : ''}
                                </span>
                            </div>
                        </>
                    )}
                    </>
                    )}
                </div>
            )}

            {/* High Impact Warning */}
            {activePreview && impactSeverity === 'high' && (
                <div className="swap-warning">
                    <AlertIcon /> <span>High price impact! Consider trading a smaller amount or adding liquidity.</span>
                </div>
            )}

            {/* Medium Impact Notice */}
            {activePreview && impactSeverity === 'medium' && (
                <div className="swap-notice">
                    <InfoIcon /> <span>Moderate price impact ({formatPercent(activePreview.priceImpact)})</span>
                </div>
            )}

            {poolFeed.source !== 'api' && (
                <div className="swap-notice">
                    <InfoIcon /> <span>Live market data unavailable. Using cached data for preview quotes.</span>
                </div>
            )}

            {advancedMode && activePreview && !certificateCheck.ok && (
                <div className="swap-warning">
                    <AlertIcon /> <span>Quote certificate check failed: {certificateCheck.reason}. Refresh quote before swapping.</span>
                </div>
            )}

            {quoteError && (
                <div className="swap-warning">
                    <AlertIcon /> <span>{quoteError}</span>
                </div>
            )}

            {/* Swap Button */}
            <button
                className={`btn btn-primary btn-large swap-btn ${impactSeverity === 'high' ? 'btn-warning' : ''}`}
                onClick={handleSwapClick}
                disabled={
                    isSubmitting
                    || !wallet
                    || (exactOutMode
                        ? !exactOutCanSubmit
                        : batchMode
                            ? !batchCanSubmit
                            : (!validation.ok || (advancedMode && Boolean(activePreview) && !certificateCheck.ok)))
                }
                aria-busy={isSubmitting}
                aria-label={getButtonText()}
                type="button"
            >
                {isSubmitting && (
                    <span className="btn-spinner" aria-hidden="true" />
                )}
                {getButtonText()}
            </button>

            {/* Confirmation Modal (Poka-yoke interlocks) */}
<SwapConfirmModal
                open={showConfirm}
                activePreview={activePreview}
                amountIn={amountIn}
                fromToken={fromToken}
                toToken={toToken}
                advancedMode={advancedMode}
                effectiveProfileLabel={effectiveProfileConfig.label}
                confirmConfig={confirmConfig}
                typedConfirmText={typedConfirmText}
                onTypedConfirmTextChange={setTypedConfirmText}
                pokayokeEnabled={pokayokeEnabled}
                apiSlippageAdvice={apiSlippageAdvice}
                slippage={slippage}
                onApplySlippage={handleApplySlippage}
                pokayokeSuggesting={pokayokeSuggesting}
                onFindSaferAmount={handleFindSaferAmount}
                pokayokeHeavySuggesting={pokayokeHeavySuggesting}
                onFindSaferAmountDeep={handleFindSaferAmountDeep}
                pokayokeSuggestError={pokayokeSuggestError}
                pokayokeSuggestions={pokayokeSuggestions}
                pokayokeHeavySuggestError={pokayokeHeavySuggestError}
                pokayokeHeavySuggestions={pokayokeHeavySuggestions}
                onApplySuggestedAmount={handleApplySuggestedAmount}
                onClose={resetConfirmState}
                onProceed={executeSwap}
                isSubmitting={isSubmitting}
            />

            {/* Submitted Modal */}
            <SwapSubmittedModal
                submittedSwap={submittedSwap}
                onClose={() => setSubmittedSwap(null)}
            />

                <div className="swap-footer">
                    {proofEnforced ? (
                        <span className="verified-badge">✓ Proof-wrapper active</span>
                    ) : (
                        <span className="verified-badge verified-badge-advisory">Math verified (proofs off)</span>
                    )}
                    <span className="network-badge">Tau local-testnet</span>
                </div>
            </div>

            {proofPanel}

            <TokenSelectModal
                isOpen={Boolean(tokenModalSide)}
                onClose={() => setTokenModalSide(null)}
                onSelect={handleSelectToken}
                excludeToken={tokenModalSide === 'from' ? toToken : fromToken}
                wallet={liveWallet}
                availableTokens={tokens}
                customTokens={demoMode ? customTokens : []}
                onImportToken={handleImportToken}
                allowImportCustom={demoMode}
            />
        </div>
    );
}

export default SwapInterface;
