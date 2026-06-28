import { useEffect, useState } from 'react';
import { apiDexImpactPreview, apiDexSlippageAdvice } from './api';
import { getSlippageOptions } from './validation';
import { estimateRoutePendingVolumes } from './swapUtils.js';

function abortName(err) {
  return err && typeof err === 'object' ? err.name : '';
}

function positiveInput(amountIn) {
  const input = parseFloat(amountIn);
  return Number.isFinite(input) && input > 0 ? input : null;
}

function roundedPositive(value) {
  return Math.max(1, Math.round(Number(value || 0)));
}

function roundedNonnegative(value) {
  return Math.max(0, Math.round(Number(value || 0)));
}

function slippageOptionsBps() {
  const options = getSlippageOptions()
    .map((option) => Math.round(Number(option.value) * 10_000))
    .filter((value) => Number.isFinite(value) && value >= 0 && value <= 10_000);
  options.sort((a, b) => a - b);
  return Array.from(new Set(options));
}

function useDirectImpactPreview({ advancedMode, amountIn, reserves, feeBps }) {
  const [preview, setPreview] = useState(null);

  useEffect(() => {
    let cancelled = false;
    const controller = new AbortController();
    const run = async () => {
      if (advancedMode || !amountIn || !reserves) {
        setPreview(null);
        return;
      }
      const input = positiveInput(amountIn);
      if (input === null) {
        setPreview(null);
        return;
      }
      try {
        const resp = await apiDexImpactPreview(
          {
            reserveIn: roundedPositive(reserves.reserveIn),
            reserveOut: roundedPositive(reserves.reserveOut),
            amountIn: roundedPositive(input),
            feeBps: roundedNonnegative(feeBps),
            pendingVolumeSameDirection: 0,
            confidenceBps: 9500,
          },
          { timeoutMs: 1400, signal: controller.signal },
        );
        const payload = resp?.preview;
        if (!cancelled && resp?.ok && payload) {
          setPreview({
            amountOutIsolated: Number(payload.amount_out_isolated),
            feeAmount: Number(payload.fee_amount),
            priceImpactBps: Number(payload.price_impact_bps),
            spotPriceE8: Number(payload.spot_price_e8),
            amountOutBestCase: Number(payload.amount_out_best_case),
            amountOutWorstCase: Number(payload.amount_out_worst_case),
            recommendedMinOut: Number(payload.recommended_min_out),
          });
        }
      } catch (err) {
        if (!cancelled && abortName(err) !== 'AbortError') {
          setPreview(null);
        }
      }
    };
    run();
    return () => {
      cancelled = true;
      controller.abort();
    };
  }, [advancedMode, amountIn, reserves, feeBps]);

  return preview;
}

function useDirectSlippageAdvice({ advancedMode, amountIn, reserves, feeBps, slippage }) {
  const [advice, setAdvice] = useState(null);

  useEffect(() => {
    let cancelled = false;
    const controller = new AbortController();
    const run = async () => {
      if (advancedMode || !amountIn || !reserves) {
        setAdvice(null);
        return;
      }
      const input = positiveInput(amountIn);
      if (input === null) {
        setAdvice(null);
        return;
      }

      try {
        const resp = await apiDexSlippageAdvice(
          {
            reserveIn: roundedPositive(reserves.reserveIn),
            reserveOut: roundedPositive(reserves.reserveOut),
            amountIn: roundedPositive(input),
            feeBps: roundedNonnegative(feeBps),
            pendingVolumeSameDirection: 0,
            confidenceBps: 9500,
            slippageOptionsBps: slippageOptionsBps(),
            maxAttackerAmountIn: 2000,
            userSlippageBps: Math.max(0, Math.min(10_000, Math.round(Number(slippage || 0) * 10_000))),
          },
          { timeoutMs: 1800, signal: controller.signal },
        );
        const payload = resp?.advice;
        if (!cancelled && resp?.ok && payload) {
          setAdvice({
            status: String(payload.status || ''),
            priceImpactBps: payload.price_impact_bps,
            recommendedSlippageBps: payload.recommended_slippage_bps,
            recommendedSlippageBpsRevertSafe: payload.recommended_slippage_bps_revert_safe,
            recommendedSlippageBpsMevSafe: payload.recommended_slippage_bps_mev_safe,
            requiredSlippageBps: payload.required_slippage_bps,
            options: Array.isArray(payload.options) ? payload.options : [],
            pokayoke: payload.pokayoke || null,
          });
        }
      } catch (err) {
        if (!cancelled && abortName(err) !== 'AbortError') {
          setAdvice(null);
        }
      }
    };
    run();
    return () => {
      cancelled = true;
      controller.abort();
    };
  }, [advancedMode, amountIn, reserves, feeBps, slippage]);

  return advice;
}

export function useRouteImpactPreview({ advancedMode, swapPreview, amountIn }) {
  const [preview, setPreview] = useState(null);

  useEffect(() => {
    let cancelled = false;
    const controller = new AbortController();
    const run = async () => {
      if (!advancedMode || !swapPreview) {
        setPreview(null);
        return;
      }
      const routeEdges = Array.isArray(swapPreview.routeEdges) ? swapPreview.routeEdges : [];
      if (routeEdges.length === 0) {
        setPreview(null);
        return;
      }
      const amountInNum = Number(amountIn || 0);
      if (!Number.isFinite(amountInNum) || amountInNum <= 0) {
        setPreview(null);
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
            reserveIn: roundedPositive(edge.reserveIn),
            reserveOut: roundedPositive(edge.reserveOut),
            amountIn: roundedPositive(hopAmountIn),
            feeBps: roundedNonnegative(edge.feeBps),
            pendingVolumeSameDirection: roundedNonnegative(pendingVolume),
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
          setPreview({
            source: 'api-route',
            amountOutBestCase: Number(p.amount_out_best_case),
            amountOutWorstCase: Number(p.amount_out_worst_case),
            recommendedMinOut: Number(p.recommended_min_out),
            feeAmount: Number(p.fee_amount),
          });
          return;
        }

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
        setPreview({
          source: 'api-route',
          amountOutBestCase: Number(p2Best.amount_out_best_case),
          amountOutWorstCase: Number(p2Worst.amount_out_worst_case),
          recommendedMinOut: Number(p2Worst.recommended_min_out),
          feeAmount: Number(p1.fee_amount) + Number(p2Best.fee_amount),
        });
      } catch (err) {
        if (!cancelled && abortName(err) !== 'AbortError') {
          setPreview(null);
        }
      }
    };
    run();
    return () => {
      cancelled = true;
      controller.abort();
    };
  }, [advancedMode, swapPreview, amountIn]);

  return preview;
}

export function useDirectSwapApiPreviewState({ advancedMode, amountIn, reserves, feeBps, slippage }) {
  return {
    apiImpactPreview: useDirectImpactPreview({ advancedMode, amountIn, reserves, feeBps }),
    apiSlippageAdvice: useDirectSlippageAdvice({ advancedMode, amountIn, reserves, feeBps, slippage }),
  };
}
