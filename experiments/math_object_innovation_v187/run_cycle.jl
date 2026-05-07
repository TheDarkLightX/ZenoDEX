#!/usr/bin/env julia

using Random

const ROOT = @__DIR__
const GENERATED = joinpath(ROOT, "generated")
mkpath(GENERATED)
const RAW = joinpath(GENERATED, "raw.tsv")

const FEE_NUM = BigInt(997)
const FEE_DEN = BigInt(1000)
const BASE_PRICES = BigInt[2, 3, 5, 7, 11]
const ASSET_COUNT = length(BASE_PRICES)

struct Edge
    src::Int
    dst::Int
    reserve_in::BigInt
    reserve_out::BigInt
    discount_num::BigInt
    discount_den::BigInt
end

rate_upper(e::Edge) =
    Rational{BigInt}(FEE_NUM * e.reserve_out, FEE_DEN * e.reserve_in)

function cpmm_out_post_fee(net_in::BigInt, reserve_in::BigInt, reserve_out::BigInt)::BigInt
    if net_in <= 0
        return BigInt(0)
    end
    return div(net_in * reserve_out, reserve_in + net_in)
end

function edge_from_discount(src::Int, dst::Int, num::Integer, den::Integer, k::Integer)::Edge
    p_src = BASE_PRICES[src]
    p_dst = BASE_PRICES[dst]
    # Ensures upper_rate = (p_src / p_dst) * (num / den).
    reserve_in = FEE_NUM * p_dst * BigInt(den) * BigInt(k)
    reserve_out = FEE_DEN * p_src * BigInt(num) * BigInt(k)
    Edge(src, dst, reserve_in, reserve_out, BigInt(num), BigInt(den))
end

function make_graph(seed::Int; injected::Bool=false)
    rng = MersenneTwister(seed)
    edges = Dict{Tuple{Int,Int}, Edge}()
    for i in 1:ASSET_COUNT
        for j in 1:ASSET_COUNT
            i == j && continue
            d = rand(rng, [(97,100), (98,100), (99,100)])
            k = rand(rng, 800:1400)
            if injected && i == 1 && j == 2
                d = (103,100)
                k = 1400
            elseif injected && i == 2 && j == 1
                d = (99,100)
                k = 1400
            end
            edges[(i,j)] = edge_from_discount(i, j, d[1], d[2], k)
        end
    end
    edges
end

function potential_ok(edges)::Bool
    for e in values(edges)
        lhs = rate_upper(e) * BASE_PRICES[e.dst]
        rhs = Rational{BigInt}(BASE_PRICES[e.src], 1)
        if lhs > rhs
            return false
        end
    end
    return true
end

function exact_edge_out(e::Edge, amount::BigInt)::BigInt
    # Use the post-fee net input as the local certified edge amount. This keeps
    # the theorem target focused: floor(q) <= q and q - floor(q) < 1.
    cpmm_out_post_fee(amount, e.reserve_in, e.reserve_out)
end

function exact_path_out(edges, path::Vector{Int}, amount::BigInt)::BigInt
    cur = amount
    for idx in 1:(length(path)-1)
        cur = exact_edge_out(edges[(path[idx], path[idx+1])], cur)
    end
    cur
end

function simple_paths(src::Int, dst::Int, max_edges::Int)
    paths = Vector{Vector{Int}}()
    function dfs(path::Vector{Int})
        if length(path) - 1 > max_edges
            return
        end
        if path[end] == dst
            push!(paths, copy(path))
            return
        end
        for nxt in 1:ASSET_COUNT
            nxt == path[end] && continue
            nxt in path && continue
            push!(path, nxt)
            dfs(path)
            pop!(path)
        end
    end
    dfs([src])
    paths
end

function route_prune_metrics(edges, amount::BigInt)
    paths = simple_paths(1, ASSET_COUNT, 3)
    direct = [1, ASSET_COUNT]
    incumbent = exact_path_out(edges, direct, amount)
    pruneable = 0
    false_prunes = 0
    for path in paths
        length(path) <= 2 && continue
        first = edges[(path[1], path[2])]
        prefix = exact_edge_out(first, amount)
        upper_to_dst = Rational{BigInt}(prefix * BASE_PRICES[path[2]], BASE_PRICES[ASSET_COUNT])
        exact_out = exact_path_out(edges, path, amount)
        if upper_to_dst <= incumbent
            pruneable += 1
            if exact_out > incumbent
                false_prunes += 1
            end
        end
    end
    (length(paths), incumbent, pruneable, false_prunes)
end

function cycle_profit_1_2_1(edges, amount::BigInt)
    out12 = exact_edge_out(edges[(1,2)], amount)
    out21 = exact_edge_out(edges[(2,1)], out12)
    out21 - amount
end

function floor_grid_metrics(lo::Int, hi::Int)
    count = 0
    violations = 0
    max_num = BigInt(0)
    max_den = BigInt(1)
    for reserve_in in lo:hi
        for reserve_out in lo:hi
            for net_in in lo:hi
                q = Rational{BigInt}(BigInt(net_in) * BigInt(reserve_out), BigInt(reserve_in + net_in))
                out = cpmm_out_post_fee(BigInt(net_in), BigInt(reserve_in), BigInt(reserve_out))
                err = q - Rational{BigInt}(out, 1)
                count += 1
                if !(0 <= err && err < 1)
                    violations += 1
                end
                if err > Rational{BigInt}(max_num, max_den)
                    max_num = numerator(err)
                    max_den = denominator(err)
                end
            end
        end
    end
    (count, violations, max_num, max_den)
end

open(RAW, "w") do io
    println(io, join([
        "kind", "split", "seed", "injected", "potential_ok", "path_count",
        "incumbent", "pruneable", "false_prunes", "cycle_profit",
        "grid_count", "grid_violations", "max_error"
    ], '\t'))

    for (split, seeds, injected) in [
            ("discovery", 1:80, false),
            ("holdout", 81:160, false),
            ("discovery", 1:40, true),
            ("holdout", 41:80, true),
        ]
        for seed in seeds
            edges = make_graph(seed; injected=injected)
            ok = potential_ok(edges)
            amount = BigInt(1000)
            path_count, incumbent, pruneable, false_prunes = route_prune_metrics(edges, amount)
            profit = cycle_profit_1_2_1(edges, amount)
            println(io, join([
                "graph", split, string(seed), string(injected), string(ok),
                string(path_count), string(incumbent), string(pruneable),
                string(false_prunes), string(profit), "NA", "NA", "NA"
            ], '\t'))
        end
    end

    for (split, lo, hi) in [("discovery", 1, 80), ("holdout", 81, 140)]
        count, violations, max_num, max_den = floor_grid_metrics(lo, hi)
        println(io, join([
            "floor_grid", split, "NA", "NA", "NA", "NA", "NA", "NA", "NA", "NA",
            string(count), string(violations), string(max_num) * "/" * string(max_den)
        ], '\t'))
    end
end
