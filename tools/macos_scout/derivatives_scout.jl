#!/usr/bin/env julia

using Dates
using Printf
using Random
using Statistics

struct Candidate
    id::Int
    convexity::Float64
    funding_gain::Float64
    volatility_gate::Float64
    fee_burn_share::Float64
    insurance_share::Float64
    shock_damping::Float64
    payout_cap_share::Float64
    oracle_delay_haircut::Float64
    liquidity_floor::Float64
end

struct Result
    id::Int
    score::Float64
    disaster_rate::Float64
    deflation_bps::Float64
    p99_drawdown_bps::Float64
    min_insurance_ratio::Float64
    funding_stability::Float64
    worst_liquidity_ratio::Float64
    mean_fee_bps::Float64
    legal_shape_ok::Bool
    candidate::Candidate
end

struct RunTimings
    screen_seconds::Float64
    rerank_seconds::Float64
end

struct CounterExample
    id::Int
    path::Int
    step::Int
    reason::String
    price::Float64
    oracle::Float64
    insurance::Float64
    liquidity::Float64
    drawdown::Float64
end

function getarg(name::String, default::String)::String
    flag = "--" * name
    for i in eachindex(ARGS)
        if ARGS[i] == flag && i < length(ARGS)
            return ARGS[i + 1]
        end
        prefix = flag * "="
        if startswith(ARGS[i], prefix)
            return ARGS[i][(lastindex(prefix) + 1):end]
        end
    end
    return default
end

function json_escape(value::AbstractString)::String
    out = IOBuffer()
    for c in value
        if c == '"'
            print(out, "\\\"")
        elseif c == '\\'
            print(out, "\\\\")
        elseif c == '\n'
            print(out, "\\n")
        elseif c == '\r'
            print(out, "\\r")
        elseif c == '\t'
            print(out, "\\t")
        else
            print(out, c)
        end
    end
    return String(take!(out))
end

function json_pair(key::String, value)::String
    if value isa AbstractString
        return "\"" * json_escape(key) * "\":\"" * json_escape(value) * "\""
    elseif value isa Bool
        return "\"" * json_escape(key) * "\":" * (value ? "true" : "false")
    elseif value isa Integer
        return "\"" * json_escape(key) * "\":" * string(value)
    else
        return "\"" * json_escape(key) * "\":" * @sprintf("%.12g", Float64(value))
    end
end

function candidate_json(c::Candidate)::String
    parts = String[
        json_pair("id", c.id),
        json_pair("convexity", c.convexity),
        json_pair("funding_gain", c.funding_gain),
        json_pair("volatility_gate", c.volatility_gate),
        json_pair("fee_burn_share", c.fee_burn_share),
        json_pair("insurance_share", c.insurance_share),
        json_pair("shock_damping", c.shock_damping),
        json_pair("payout_cap_share", c.payout_cap_share),
        json_pair("oracle_delay_haircut", c.oracle_delay_haircut),
        json_pair("liquidity_floor", c.liquidity_floor),
    ]
    return "{" * join(parts, ",") * "}"
end

function result_json(r::Result)::String
    parts = String[
        json_pair("id", r.id),
        json_pair("score", r.score),
        json_pair("disaster_rate", r.disaster_rate),
        json_pair("deflation_bps", r.deflation_bps),
        json_pair("p99_drawdown_bps", r.p99_drawdown_bps),
        json_pair("min_insurance_ratio", r.min_insurance_ratio),
        json_pair("funding_stability", r.funding_stability),
        json_pair("worst_liquidity_ratio", r.worst_liquidity_ratio),
        json_pair("mean_fee_bps", r.mean_fee_bps),
        json_pair("legal_shape_ok", r.legal_shape_ok),
        "\"candidate\":" * candidate_json(r.candidate),
    ]
    return "{" * join(parts, ",") * "}"
end

function counterexample_json(ce::CounterExample)::String
    parts = String[
        json_pair("id", ce.id),
        json_pair("path", ce.path),
        json_pair("step", ce.step),
        json_pair("reason", ce.reason),
        json_pair("price", ce.price),
        json_pair("oracle", ce.oracle),
        json_pair("insurance", ce.insurance),
        json_pair("liquidity", ce.liquidity),
        json_pair("drawdown", ce.drawdown),
    ]
    return "{" * join(parts, ",") * "}"
end

function random_candidate(rng::AbstractRNG, id::Int)::Candidate
    burn = rand(rng) * 0.70
    insurance = rand(rng) * (0.95 - burn)
    return Candidate(
        id,
        1.05 + 2.95 * rand(rng),
        0.05 + 4.95 * rand(rng),
        0.002 + 0.080 * rand(rng),
        burn,
        insurance,
        0.05 + 0.90 * rand(rng),
        0.02 + 0.48 * rand(rng),
        0.00 + 0.75 * rand(rng),
        0.05 + 0.45 * rand(rng),
    )
end

function stress_return(rng::AbstractRNG, regime::Int)::Float64
    base_vol = regime == 1 ? 0.010 : regime == 2 ? 0.025 : regime == 3 ? 0.050 : 0.090
    drift = regime == 2 ? -0.0015 : regime == 3 ? 0.0010 : 0.0
    jump = rand(rng) < (regime == 4 ? 0.080 : 0.020)
    jump_size = jump ? (rand(rng) < 0.5 ? -1.0 : 1.0) * (0.08 + 0.35 * rand(rng)) : 0.0
    return drift + base_vol * randn(rng) + jump_size
end

function percentile(sorted_values::Vector{Float64}, p::Float64)::Float64
    isempty(sorted_values) && return 0.0
    idx = clamp(ceil(Int, p * length(sorted_values)), 1, length(sorted_values))
    return sorted_values[idx]
end

function evaluate_candidate(
    c::Candidate,
    rng::AbstractRNG;
    paths::Int,
    steps::Int,
)::Tuple{Result, Union{CounterExample, Nothing}}
    initial_insurance = 1_000_000.0
    base_oi = 10_000_000.0
    total_burn = 0.0
    total_fees = 0.0
    disaster_count = 0
    min_insurance_ratio = Inf
    worst_liquidity_ratio = Inf
    funding_abs_sum = 0.0
    funding_flip_count = 0
    funding_count = 0
    last_funding_sign = 0.0
    first_counterexample = nothing
    drawdowns = Float64[]

    for path in 1:paths
        price = 1.0
        oracle = 1.0
        liquidity = 1.0
        insurance = initial_insurance
        max_equity = insurance
        regime = 1 + mod(path - 1, 4)

        for step in 1:steps
            prev_price = price
            ret = stress_return(rng, regime)
            price = max(0.03, price * exp(ret))
            oracle_lag = 0.03 + 0.22 * c.shock_damping
            oracle = max(0.03, (1.0 - oracle_lag) * oracle + oracle_lag * price)
            rel_gap = abs(price / oracle - 1.0)
            vol = abs(log(price / prev_price))
            liquidity = clamp(liquidity * exp(-0.50 * vol + 0.015 * randn(rng)), 0.01, 1.25)

            oi = base_oi * (0.50 + 1.75 * liquidity)
            fee = oi * (0.00015 + 0.010 * vol + 0.003 * max(rel_gap - c.volatility_gate, 0.0))
            burn = c.fee_burn_share * fee
            insurance_fee = c.insurance_share * fee
            protocol_fee = max(fee - burn - insurance_fee, 0.0)
            total_fees += fee
            total_burn += burn
            insurance += insurance_fee + 0.20 * protocol_fee

            funding_raw = c.funding_gain * sign(price - oracle) * max(rel_gap - c.volatility_gate, 0.0)^c.convexity
            funding = clamp(funding_raw, -0.050, 0.050)
            funding_abs_sum += abs(funding)
            if funding_count > 0 && sign(funding) != 0.0 && last_funding_sign != 0.0 && sign(funding) != last_funding_sign
                funding_flip_count += 1
            end
            if sign(funding) != 0.0
                last_funding_sign = sign(funding)
            end
            funding_count += 1

            liquidation_pressure = max(rel_gap - c.volatility_gate, 0.0)
            gross_loss = oi * 0.010 * liquidation_pressure^c.convexity
            haircut = 1.0 + c.oracle_delay_haircut * min(rel_gap, 0.75)
            capped_payout = min(gross_loss * haircut, c.payout_cap_share * max(insurance, 0.0))
            insurance -= capped_payout

            liquidity_floor_breach = liquidity < c.liquidity_floor
            min_insurance_ratio = min(min_insurance_ratio, insurance / initial_insurance)
            worst_liquidity_ratio = min(worst_liquidity_ratio, liquidity)
            max_equity = max(max_equity, insurance)
            drawdown = max(0.0, (max_equity - insurance) / initial_insurance)
            push!(drawdowns, drawdown)

            reason = ""
            if insurance < 0.0
                reason = "negative_insurance"
            elseif burn > 0.90 * fee
                reason = "burn_starves_budget"
            elseif capped_payout > c.payout_cap_share * initial_insurance && rel_gap > 0.25
                reason = "payout_cap_exceeded_initial_budget"
            elseif liquidity_floor_breach && rel_gap > 0.10
                reason = "liquidity_floor_breach_under_oracle_gap"
            elseif abs(funding) > 0.040 && liquidity < 0.10
                reason = "funding_too_aggressive_in_thin_liquidity"
            end

            if reason != ""
                disaster_count += 1
                if first_counterexample === nothing
                    first_counterexample = CounterExample(
                        c.id,
                        path,
                        step,
                        reason,
                        price,
                        oracle,
                        insurance,
                        liquidity,
                        drawdown,
                    )
                end
            end
        end
    end

    sort!(drawdowns)
    observations = max(paths * steps, 1)
    disaster_rate = disaster_count / observations
    deflation_bps = total_fees <= 0.0 ? 0.0 : 10_000.0 * total_burn / total_fees
    p99_drawdown_bps = 10_000.0 * percentile(drawdowns, 0.99)
    mean_fee_bps = total_fees / (paths * steps * base_oi) * 10_000.0
    funding_stability = 1.0 / (1.0 + funding_abs_sum / observations + funding_flip_count / observations)
    legal_shape_ok = (
        c.fee_burn_share + c.insurance_share <= 0.95
        && c.payout_cap_share <= 0.50
        && c.funding_gain <= 5.0
    )
    score = (
        0.70 * deflation_bps
        + 150.0 * funding_stability
        + 60.0 * min(1.0, max(min_insurance_ratio, -1.0))
        - 8_000.0 * disaster_rate
        - 0.045 * p99_drawdown_bps
        - 40.0 * max(c.liquidity_floor - worst_liquidity_ratio, 0.0)
        - (legal_shape_ok ? 0.0 : 500.0)
    )
    return (
        Result(
            c.id,
            score,
            disaster_rate,
            deflation_bps,
            p99_drawdown_bps,
            min_insurance_ratio,
            funding_stability,
            worst_liquidity_ratio,
            mean_fee_bps,
            legal_shape_ok,
            c,
        ),
        first_counterexample,
    )
end

function dominates(a::Result, b::Result)::Bool
    no_worse = (
        a.disaster_rate <= b.disaster_rate
        && a.p99_drawdown_bps <= b.p99_drawdown_bps
        && a.deflation_bps >= b.deflation_bps
        && a.funding_stability >= b.funding_stability
    )
    strictly_better = (
        a.disaster_rate < b.disaster_rate
        || a.p99_drawdown_bps < b.p99_drawdown_bps
        || a.deflation_bps > b.deflation_bps
        || a.funding_stability > b.funding_stability
    )
    return no_worse && strictly_better
end

function pareto_front(results::Vector{Result}; limit::Int)::Vector{Result}
    pool = results[1:min(length(results), limit)]
    front = Result[]
    for candidate in pool
        dominated = false
        for other in pool
            if other.id != candidate.id && dominates(other, candidate)
                dominated = true
                break
            end
        end
        if !dominated
            push!(front, candidate)
        end
    end
    sort!(front, by = r -> r.score, rev = true)
    return front
end

function rerank_candidates(
    initial_top::Vector{Result};
    seed::Int,
    paths::Int,
    steps::Int,
)::Vector{Result}
    isempty(initial_top) && return Result[]
    reranked = Vector{Result}(undef, length(initial_top))
    Threads.@threads for i in eachindex(initial_top)
        original = initial_top[i]
        rng = MersenneTwister(seed + 17_000_019 * original.id)
        res, _ = evaluate_candidate(original.candidate, rng; paths = paths, steps = steps)
        reranked[i] = res
    end
    sort!(reranked, by = r -> r.score, rev = true)
    return reranked
end

function write_lines(path::String, lines)
    open(path, "w") do io
        for line in lines
            println(io, line)
        end
    end
end

function write_result_jsonl(path::String, results)
    open(path, "w") do io
        for r in results
            println(io, result_json(r))
        end
    end
end

function main()
    outdir = getarg("out", joinpath("internal", "macos_scout_runs", Dates.format(now(), "yyyymmdd_HHMMSS")))
    candidates = parse(Int, getarg("candidates", "2000"))
    paths = parse(Int, getarg("paths", "32"))
    steps = parse(Int, getarg("steps", "64"))
    seed = parse(Int, getarg("seed", "20260508"))
    topn = parse(Int, getarg("top", "50"))
    front_limit = parse(Int, getarg("front-limit", "5000"))
    rerank_top = parse(Int, getarg("rerank-top", "0"))
    rerank_paths = parse(Int, getarg("rerank-paths", string(paths)))
    rerank_steps = parse(Int, getarg("rerank-steps", string(steps)))
    write_all_jsonl = lowercase(getarg("write-all-jsonl", "false")) in ("1", "true", "yes")
    mkpath(outdir)

    println("ZenoDEX MacOS derivatives scout")
    println("out=", outdir)
    println("threads=", Threads.nthreads())
    println("candidates=", candidates, " paths=", paths, " steps=", steps, " seed=", seed)
    println("rerank_top=", rerank_top, " rerank_paths=", rerank_paths, " rerank_steps=", rerank_steps)

    results = Vector{Result}(undef, candidates)
    counterexamples = Vector{Union{CounterExample, Nothing}}(undef, candidates)

    screen_seconds = @elapsed begin
        Threads.@threads for i in 1:candidates
            rng = MersenneTwister(seed + 1_000_003 * i)
            c = random_candidate(rng, i)
            res, ce = evaluate_candidate(c, rng; paths = paths, steps = steps)
            results[i] = res
            counterexamples[i] = ce
        end
    end

    sorted = sort(results, by = r -> r.score, rev = true)
    top = sorted[1:min(topn, length(sorted))]
    front = pareto_front(sorted; limit = front_limit)
    ces = [ce for ce in counterexamples if ce !== nothing]
    rerank_pool = sorted[1:min(rerank_top, length(sorted))]
    reranked = Result[]
    rerank_seconds = @elapsed begin
        reranked = rerank_candidates(
            rerank_pool;
            seed = seed + 99_991,
            paths = rerank_paths,
            steps = rerank_steps,
        )
    end
    timings = RunTimings(screen_seconds, rerank_seconds)

    all_scores_path = joinpath(outdir, "all_scores.csv")
    open(all_scores_path, "w") do io
        println(io, "id,score,disaster_rate,deflation_bps,p99_drawdown_bps,min_insurance_ratio,funding_stability,worst_liquidity_ratio,mean_fee_bps,legal_shape_ok,convexity,funding_gain,volatility_gate,fee_burn_share,insurance_share,shock_damping,payout_cap_share,oracle_delay_haircut,liquidity_floor")
        for r in sorted
            @printf(
                io,
                "%d,%.12g,%.12g,%.12g,%.12g,%.12g,%.12g,%.12g,%.12g,%s,%.12g,%.12g,%.12g,%.12g,%.12g,%.12g,%.12g,%.12g,%.12g\n",
                r.id,
                r.score,
                r.disaster_rate,
                r.deflation_bps,
                r.p99_drawdown_bps,
                r.min_insurance_ratio,
                r.funding_stability,
                r.worst_liquidity_ratio,
                r.mean_fee_bps,
                string(r.legal_shape_ok),
                r.candidate.convexity,
                r.candidate.funding_gain,
                r.candidate.volatility_gate,
                r.candidate.fee_burn_share,
                r.candidate.insurance_share,
                r.candidate.shock_damping,
                r.candidate.payout_cap_share,
                r.candidate.oracle_delay_haircut,
                r.candidate.liquidity_floor,
            )
        end
    end

    write_result_jsonl(joinpath(outdir, "top_candidates.jsonl"), top)
    write_result_jsonl(joinpath(outdir, "pareto_front.jsonl"), front)
    write_result_jsonl(joinpath(outdir, "reranked_top_candidates.jsonl"), reranked)
    write_lines(joinpath(outdir, "counterexamples.jsonl"), counterexample_json.(ces))
    if write_all_jsonl
        write_result_jsonl(joinpath(outdir, "all_candidates.jsonl"), sorted)
    end

    best = first(top)
    best_reranked = isempty(reranked) ? best : first(reranked)
    zero_disaster = count(r -> r.disaster_rate == 0.0 && r.legal_shape_ok, results)
    retained_bytes = Base.summarysize(results) + Base.summarysize(counterexamples) + Base.summarysize(sorted)
    summary_json = "{" * join(String[
        json_pair("schema", "zenodex/macos_derivatives_scout_summary/v1"),
        json_pair("created_at", string(now())),
        json_pair("outdir", outdir),
        json_pair("threads", Threads.nthreads()),
        json_pair("candidates", candidates),
        json_pair("paths", paths),
        json_pair("steps", steps),
        json_pair("seed", seed),
        json_pair("topn", topn),
        json_pair("front_limit", front_limit),
        json_pair("rerank_top", rerank_top),
        json_pair("rerank_paths", rerank_paths),
        json_pair("rerank_steps", rerank_steps),
        json_pair("screen_seconds", timings.screen_seconds),
        json_pair("rerank_seconds", timings.rerank_seconds),
        json_pair("retained_bytes_estimate", retained_bytes),
        json_pair("counterexample_count", length(ces)),
        json_pair("zero_disaster_legal_shape_count", zero_disaster),
        "\"best\":" * result_json(best),
        "\"best_reranked\":" * result_json(best_reranked),
    ], ",") * "}"
    write_lines(joinpath(outdir, "summary.json"), [summary_json])

    summary_md = String[
        "# ZenoDEX MacOS Scout Summary",
        "",
        "- Candidates: $(candidates)",
        "- Paths per candidate: $(paths)",
        "- Steps per path: $(steps)",
        "- Julia threads: $(Threads.nthreads())",
        "- Seed: $(seed)",
        "- Screen seconds: $(round(timings.screen_seconds, digits = 3))",
        "- Rerank seconds: $(round(timings.rerank_seconds, digits = 3))",
        "- Retained bytes estimate: $(retained_bytes)",
        "- Counterexamples: $(length(ces))",
        "- Zero-disaster legal-shape candidates: $(zero_disaster)",
        "",
        "## Best Candidate",
        "",
        "- id: $(best.id)",
        "- score: $(round(best.score, digits = 4))",
        "- disaster_rate: $(round(best.disaster_rate, digits = 8))",
        "- deflation_bps: $(round(best.deflation_bps, digits = 4))",
        "- p99_drawdown_bps: $(round(best.p99_drawdown_bps, digits = 4))",
        "- min_insurance_ratio: $(round(best.min_insurance_ratio, digits = 6))",
        "- funding_stability: $(round(best.funding_stability, digits = 6))",
        "",
        "## Best Reranked Candidate",
        "",
        "- id: $(best_reranked.id)",
        "- score: $(round(best_reranked.score, digits = 4))",
        "- disaster_rate: $(round(best_reranked.disaster_rate, digits = 8))",
        "- deflation_bps: $(round(best_reranked.deflation_bps, digits = 4))",
        "- p99_drawdown_bps: $(round(best_reranked.p99_drawdown_bps, digits = 4))",
        "- min_insurance_ratio: $(round(best_reranked.min_insurance_ratio, digits = 6))",
        "- funding_stability: $(round(best_reranked.funding_stability, digits = 6))",
        "",
        "## Next Review",
        "",
        "1. Inspect counterexamples first.",
        "2. Re-run the best Pareto candidates with a different seed.",
        "3. Promote counterexample classes into regression tests.",
        "4. Promote candidate formulas only after two seeds and a formal proof target.",
    ]
    write_lines(joinpath(outdir, "summary.md"), summary_md)

    println("wrote ", outdir)
    println("best candidate id=", best.id, " score=", best.score)
end

main()
