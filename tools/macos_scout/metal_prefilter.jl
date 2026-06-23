#!/usr/bin/env julia

using Dates
using Printf
using Random
using Statistics

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

if "--install" in ARGS
    using Pkg
    Pkg.add("Metal")
end

try
    @eval using Metal
catch err
    println("Metal.jl is not available in this Julia environment.")
    println("Run: julia --project=tools/macos_scout tools/macos_scout/metal_prefilter.jl --install")
    rethrow(err)
end

function write_json_summary(path::String, pairs::Vector{Pair{String, Any}})
    open(path, "w") do io
        print(io, "{")
        for (idx, pair) in enumerate(pairs)
            idx > 1 && print(io, ",")
            key = replace(pair.first, "\"" => "\\\"")
            value = pair.second
            print(io, "\"", key, "\":")
            if value isa AbstractString
                print(io, "\"", replace(value, "\"" => "\\\""), "\"")
            elseif value isa Bool
                print(io, value ? "true" : "false")
            elseif value isa Integer
                print(io, value)
            else
                @printf(io, "%.12g", Float64(value))
            end
        end
        println(io, "}")
    end
end

function main()
    n = parse(Int, getarg("n", "1000000"))
    outdir = getarg("out", joinpath("internal", "macos_scout_runs", "metal_prefilter_" * Dates.format(now(), "yyyymmdd_HHMMSS")))
    topn = parse(Int, getarg("top", "1000"))
    mkpath(outdir)

    println("Metal prefilter n=", n, " top=", topn, " out=", outdir)
    Metal.versioninfo()

    rng = MersenneTwister(20260508)
    convexity = MtlArray(Float32.(1.05 .+ 2.95 .* rand(rng, n)))
    funding_gain = MtlArray(Float32.(0.05 .+ 4.95 .* rand(rng, n)))
    volatility_gate = MtlArray(Float32.(0.002 .+ 0.080 .* rand(rng, n)))
    fee_burn_share = MtlArray(Float32.(0.70 .* rand(rng, n)))
    insurance_share = MtlArray(Float32.(0.25 .* rand(rng, n)))
    shock_damping = MtlArray(Float32.(0.05 .+ 0.90 .* rand(rng, n)))
    payout_cap_share = MtlArray(Float32.(0.02 .+ 0.48 .* rand(rng, n)))
    liquidity_floor = MtlArray(Float32.(0.05 .+ 0.45 .* rand(rng, n)))

    scores = Float32[]
    elapsed = @elapsed begin
        legal_budget = max.(0.0f0, 0.95f0 .- fee_burn_share .- insurance_share)
        stability = 1.0f0 ./ (1.0f0 .+ funding_gain .* volatility_gate .+ shock_damping .* 0.05f0)
        budget_penalty = max.(0.0f0, fee_burn_share .+ insurance_share .- 0.95f0) .* 1000.0f0
        payout_penalty = max.(0.0f0, payout_cap_share .- 0.35f0) .* 500.0f0
        liquidity_penalty = max.(0.0f0, liquidity_floor .- 0.20f0) .* 250.0f0
        score_gpu = 7000.0f0 .* fee_burn_share .+ 200.0f0 .* stability .+ 100.0f0 .* legal_budget .- budget_penalty .- payout_penalty .- liquidity_penalty
        scores = Array(score_gpu)
    end

    order = partialsortperm(scores, 1:min(topn, n), rev = true)
    open(joinpath(outdir, "metal_prefilter_top.csv"), "w") do io
        println(io, "rank,id,score")
        for (rank, idx) in enumerate(order)
            @printf(io, "%d,%d,%.8f\n", rank, idx, scores[idx])
        end
    end

    write_json_summary(
        joinpath(outdir, "metal_prefilter_summary.json"),
        [
            "schema" => "zenodex/macos_metal_prefilter_summary/v1",
            "created_at" => string(now()),
            "n" => n,
            "topn" => topn,
            "elapsed_seconds" => elapsed,
            "mean_score" => mean(scores),
            "max_score" => maximum(scores),
            "min_score" => minimum(scores),
        ],
    )
    println("wrote ", outdir)
end

main()
