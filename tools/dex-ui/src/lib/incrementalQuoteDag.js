import { calcSwapOutput, getSpotPrice, DEFAULT_FEE_RATE } from './cpmm';

function stableSig(value) {
    return JSON.stringify(value);
}

function evalNode(cache, nodeName, deps, computeFn) {
    const depsSig = stableSig(deps);
    const prev = cache.nodes.get(nodeName);
    if (prev && prev.depsSig === depsSig) {
        cache.stats.hits += 1;
        return prev.value;
    }
    const value = computeFn();
    cache.nodes.set(nodeName, { depsSig, value });
    cache.stats.recomputes += 1;
    return value;
}

function poolKey(a, b) {
    return [a, b].sort().join('-');
}

function directionalPool(pools, assetIn, assetOut) {
    const key = poolKey(assetIn, assetOut);
    const pool = pools[key];
    if (!pool) return null;
    const sorted = [assetIn, assetOut].sort();
    const forward = sorted[0] === assetIn;
    const reserveIn = forward ? Number(pool.reserve0) : Number(pool.reserve1);
    const reserveOut = forward ? Number(pool.reserve1) : Number(pool.reserve0);
    const feeBps = Number(pool.feeBps ?? 30);
    const feeRate = feeBps / 10_000;
    if (!(reserveIn > 0) || !(reserveOut > 0)) return null;
    return { key, reserveIn, reserveOut, feeBps, feeRate };
}

function routeId(route) {
    return route.hops.join('>');
}

function tieBreakRoute(a, b) {
    if (a.amountOut !== b.amountOut) return a.amountOut > b.amountOut ? a : b;
    return routeId(a) <= routeId(b) ? a : b;
}

function safeDiv(n, d) {
    if (!Number.isFinite(n) || !Number.isFinite(d) || d === 0) return 0;
    return n / d;
}

function estimatePriceImpact(spotPrice, execPrice) {
    if (spotPrice <= 0 || execPrice <= 0) return 0;
    return Math.abs((spotPrice - execPrice) / spotPrice);
}

function normalizePolicy(policy) {
    return String(policy || 'stress_or_pressure').toLowerCase();
}

function decideTwoHopGate({
    amountIn,
    directReserveIn,
    directAmountOut,
    directFeeBps,
    policy,
    config = {},
}) {
    if (!(amountIn > 0) || !(directReserveIn > 0) || !(directAmountOut > 0)) {
        return {
            considerTwoHop: true,
            stress: 0,
            pressure: 0,
            policy: normalizePolicy(policy),
        };
    }

    const p = normalizePolicy(policy);
    const stress = safeDiv(amountIn, directReserveIn);
    const pressure = safeDiv(amountIn, directAmountOut);
    const directFeeFrac = Math.max(0, Number(directFeeBps || 0)) / 10_000;

    const stressThreshold = Number(config.stress_threshold ?? 0.4);
    const pressureThreshold = Number(config.pressure_threshold ?? 1.6);
    const pressureSlope = Number(config.pressure_slope ?? 1.2);

    const piecewiseStressCutoff = Number(config.piecewise_stress_cutoff ?? 0.15);
    const piecewisePressureMid = Number(config.piecewise_pressure_mid ?? 1.5);
    const piecewisePressureLow = Number(config.piecewise_pressure_low ?? 2.2);

    const feePieceStressCutoff = Number(config.fee_piecewise_stress_cutoff ?? 0.12);
    const feePiecePressureMid = Number(config.fee_piecewise_pressure_mid ?? 1.5);
    const feePiecePressureLow = Number(config.fee_piecewise_pressure_low ?? 2.3);
    const feePieceFeeSlope = Number(config.fee_piecewise_fee_slope ?? 12.0);

    const triLowCutoff = Number(config.tripiece_stress_lower_cutoff ?? 0.14);
    const triUpperCutoff = Number(config.tripiece_stress_upper_cutoff ?? 0.2);
    const triPressureMid = Number(config.tripiece_pressure_mid_band ?? 1.6);
    const triPressureUpper = Number(config.tripiece_pressure_upper_band ?? 1.45);
    const triPressureLow = Number(config.tripiece_pressure_low_base ?? 2.3);
    const triFeeSlope = Number(config.tripiece_fee_slope ?? 16.0);

    let considerTwoHop = true;
    if (p === 'stress') {
        considerTwoHop = stress >= stressThreshold;
    } else if (p === 'pressure') {
        considerTwoHop = pressure >= pressureThreshold;
    } else if (p === 'stress_or_pressure_adaptive') {
        const adaptiveThreshold = pressureThreshold + pressureSlope * Math.max(0, stressThreshold - stress);
        considerTwoHop = stress >= stressThreshold || pressure >= adaptiveThreshold;
    } else if (p === 'stress_or_pressure_piecewise') {
        if (stress >= stressThreshold) {
            considerTwoHop = true;
        } else if (stress >= piecewiseStressCutoff) {
            considerTwoHop = pressure >= piecewisePressureMid;
        } else {
            considerTwoHop = pressure >= piecewisePressureLow;
        }
    } else if (p === 'stress_or_pressure_piecewise_fee') {
        if (stress >= stressThreshold) {
            considerTwoHop = true;
        } else if (stress >= feePieceStressCutoff) {
            considerTwoHop = pressure >= feePiecePressureMid;
        } else {
            const threshold = feePiecePressureLow + feePieceFeeSlope * directFeeFrac;
            considerTwoHop = pressure >= threshold;
        }
    } else if (p === 'stress_or_pressure_tripiece') {
        if (stress >= stressThreshold) {
            considerTwoHop = true;
        } else if (stress >= triUpperCutoff) {
            considerTwoHop = pressure >= triPressureUpper;
        } else if (stress >= triLowCutoff) {
            considerTwoHop = pressure >= triPressureMid;
        } else {
            const threshold = triPressureLow + triFeeSlope * directFeeFrac;
            considerTwoHop = pressure >= threshold;
        }
    } else {
        considerTwoHop = stress >= stressThreshold || pressure >= pressureThreshold;
    }

    return { considerTwoHop, stress, pressure, policy: p };
}

function calcDirectRoute({ pools, fromSymbol, toSymbol, amountIn }) {
    const edge = directionalPool(pools, fromSymbol, toSymbol);
    if (!edge) return null;
    const amountOut = calcSwapOutput(edge.reserveIn, edge.reserveOut, amountIn, edge.feeRate || DEFAULT_FEE_RATE);
    const spotPrice = getSpotPrice(edge.reserveIn, edge.reserveOut);
    const execPrice = safeDiv(amountOut, amountIn);
    const priceImpact = estimatePriceImpact(spotPrice, execPrice);
    return {
        type: 'direct',
        hops: [fromSymbol, toSymbol],
        poolKeys: [edge.key],
        amountOut,
        spotPrice,
        execPrice,
        priceImpact,
        reserveIn: edge.reserveIn,
        reserveOut: edge.reserveOut,
        feeBps: edge.feeBps,
        totalFeeRate: edge.feeRate,
        edges: [
            {
                assetIn: fromSymbol,
                assetOut: toSymbol,
                reserveIn: edge.reserveIn,
                reserveOut: edge.reserveOut,
                feeBps: edge.feeBps,
            },
        ],
        hopOutputs: [amountOut],
    };
}

function calcTwoHopCandidates({ pools, tokenSymbols, fromSymbol, toSymbol, amountIn }) {
    const mids = tokenSymbols
        .filter((symbol) => symbol !== fromSymbol && symbol !== toSymbol)
        .sort((a, b) => a.localeCompare(b));

    const candidates = [];
    for (const mid of mids) {
        const edge1 = directionalPool(pools, fromSymbol, mid);
        const edge2 = directionalPool(pools, mid, toSymbol);
        if (!edge1 || !edge2) continue;

        const out1 = calcSwapOutput(edge1.reserveIn, edge1.reserveOut, amountIn, edge1.feeRate || DEFAULT_FEE_RATE);
        const out2 = calcSwapOutput(edge2.reserveIn, edge2.reserveOut, out1, edge2.feeRate || DEFAULT_FEE_RATE);
        const spotPrice = getSpotPrice(edge1.reserveIn, edge1.reserveOut) * getSpotPrice(edge2.reserveIn, edge2.reserveOut);
        const execPrice = safeDiv(out2, amountIn);
        const priceImpact = estimatePriceImpact(spotPrice, execPrice);

        candidates.push({
            type: 'two-hop',
            hops: [fromSymbol, mid, toSymbol],
            poolKeys: [edge1.key, edge2.key],
            amountOut: out2,
            spotPrice,
            execPrice,
            priceImpact,
            reserveIn: edge1.reserveIn,
            reserveOut: edge2.reserveOut,
            feeBps: edge1.feeBps + edge2.feeBps,
            totalFeeRate: 1 - (1 - edge1.feeRate) * (1 - edge2.feeRate),
            edges: [
                {
                    assetIn: fromSymbol,
                    assetOut: mid,
                    reserveIn: edge1.reserveIn,
                    reserveOut: edge1.reserveOut,
                    feeBps: edge1.feeBps,
                },
                {
                    assetIn: mid,
                    assetOut: toSymbol,
                    reserveIn: edge2.reserveIn,
                    reserveOut: edge2.reserveOut,
                    feeBps: edge2.feeBps,
                },
            ],
            hopOutputs: [out1, out2],
        });
    }
    return candidates;
}

export function createQuoteDagCache() {
    return {
        nodes: new Map(),
        stats: { hits: 0, recomputes: 0 },
    };
}

/**
 * Incremental quote DAG:
 * - reuses stable subnodes across UI updates
 * - tracks cache hits/recomputes for observability
 */
export function computeSwapQuotePreviewIncremental(params, cache) {
    const {
        amountIn,
        fromSymbol,
        toSymbol,
        pools,
        tokenSymbols,
        slippage,
        profile,
    } = params;

    const hits0 = cache.stats.hits;
    const recomputes0 = cache.stats.recomputes;

    const normalized = evalNode(
        cache,
        'normalized',
        { amountIn, fromSymbol, toSymbol, slippage },
        () => {
            const amountInNum = Number(amountIn || 0);
            if (!Number.isFinite(amountInNum) || amountInNum <= 0) {
                return null;
            }
            return {
                amountIn: amountInNum,
                fromSymbol: String(fromSymbol || ''),
                toSymbol: String(toSymbol || ''),
                slippage: Number(slippage || 0),
            };
        },
    );
    if (!normalized) return null;

    const direct = evalNode(
        cache,
        'directQuote',
        { normalized, pools: Object.keys(pools).sort().map((k) => [k, pools[k]]) },
        () =>
            calcDirectRoute({
                pools,
                fromSymbol: normalized.fromSymbol,
                toSymbol: normalized.toSymbol,
                amountIn: normalized.amountIn,
            }),
    );
    if (!direct) return null;

    const gateDecision = evalNode(
        cache,
        'gateDecision',
        { normalized, direct, profileId: profile.id, policy: profile.policy, config: profile.config },
        () =>
            decideTwoHopGate({
                amountIn: normalized.amountIn,
                directReserveIn: direct.reserveIn,
                directAmountOut: direct.amountOut,
                directFeeBps: direct.feeBps,
                policy: profile.policy,
                config: profile.config,
            }),
    );

    const twoHopCandidates = evalNode(
        cache,
        'twoHopCandidates',
        {
            normalized,
            policy: gateDecision.policy,
            consider: gateDecision.considerTwoHop,
            tokenSymbols: [...tokenSymbols].sort(),
            pools: Object.keys(pools).sort().map((k) => [k, pools[k]]),
        },
        () => {
            if (!gateDecision.considerTwoHop) return [];
            return calcTwoHopCandidates({
                pools,
                tokenSymbols,
                fromSymbol: normalized.fromSymbol,
                toSymbol: normalized.toSymbol,
                amountIn: normalized.amountIn,
            });
        },
    );

    const selected = evalNode(
        cache,
        'selectedRoute',
        { direct, twoHopCandidates },
        () => {
            let best = direct;
            for (const candidate of twoHopCandidates) {
                best = tieBreakRoute(best, candidate);
            }
            return best;
        },
    );

    const quoteCallCount = 1 + (gateDecision.considerTwoHop ? twoHopCandidates.length * 2 : 0);
    const preview = evalNode(
        cache,
        'preview',
        { selected, normalized, gateDecision, quoteCallCount, profileId: profile.id, profilePolicy: profile.policy },
        () => {
            const minOutput = selected.amountOut * (1 - normalized.slippage);
            return {
                amountIn: normalized.amountIn,
                output: selected.amountOut,
                minOutput,
                spotPrice: selected.spotPrice,
                priceImpact: selected.priceImpact,
                routeType: selected.type,
                routeHops: selected.hops,
                routePath: selected.hops.join(' → '),
                totalFeeRate: selected.totalFeeRate,
                feePaidEstimate: normalized.amountIn * selected.totalFeeRate,
                quoteCallCount,
                profileId: profile.id,
                profileLabel: profile.label,
                policy: profile.policy,
                gateDecision,
                directAmountOut: direct.amountOut,
                directPriceImpact: direct.priceImpact,
                routeEdges: selected.edges || [],
                hopOutputs: selected.hopOutputs || [selected.amountOut],
            };
        },
    );

    return {
        preview,
        directQuote: direct,
        gateDecision,
        diagnostics: {
            hitsDelta: cache.stats.hits - hits0,
            recomputesDelta: cache.stats.recomputes - recomputes0,
            totalHits: cache.stats.hits,
            totalRecomputes: cache.stats.recomputes,
            nodeCount: cache.nodes.size,
        },
    };
}
