#!/usr/bin/env julia

const SCHEMA = "zenodex.campaign5.math_witness_sweep.v1"
const BPS = 10_000

bankruptcy_deficit(margin::Int, shock_pnl::Int)::Int = max(0, shock_pnl - margin)
standard_sybil_final_capital(margin::Int, shock_pnl::Int)::Int = margin + shock_pnl
standard_insurance_draw(margin::Int, shock_pnl::Int)::Int = bankruptcy_deficit(margin, shock_pnl)
adl_sybil_final_capital(margin::Int, shock_pnl::Int)::Int =
    margin + shock_pnl - bankruptcy_deficit(margin, shock_pnl)

function floor_reward(epoch_reward::Int, numerator::Int, denominator::Int)::Int
    denominator > 0 || error("denominator must be positive")
    return div(epoch_reward * numerator, denominator)
end

twal_weight(liquidity::Int, duration::Int)::Int = liquidity * duration

function twal_reward(
    epoch_reward::Int,
    attacker_liquidity::Int,
    attacker_duration::Int,
    honest_liquidity::Int,
    honest_duration::Int,
)::Int
    attacker_weight = twal_weight(attacker_liquidity, attacker_duration)
    honest_weight = twal_weight(honest_liquidity, honest_duration)
    return floor_reward(epoch_reward, attacker_weight, attacker_weight + honest_weight)
end

function snapshot_reward(epoch_reward::Int, attacker_liquidity::Int, honest_liquidity::Int)::Int
    return floor_reward(epoch_reward, attacker_liquidity, attacker_liquidity + honest_liquidity)
end

function twal_share_lt_snapshot(
    attacker_liquidity::Int,
    attacker_duration::Int,
    honest_liquidity::Int,
    honest_duration::Int,
)::Bool
    left = attacker_liquidity * attacker_duration * (attacker_liquidity + honest_liquidity)
    right = attacker_liquidity * (attacker_liquidity * attacker_duration + honest_liquidity * honest_duration)
    return left < right
end

function ring_paths(
    edges::Vector{Tuple{String, String}},
    asset_in::String,
    asset_out::String,
    max_hops::Int,
)::Vector{Vector{String}}
    if asset_in == asset_out
        return Vector{String}[]
    end

    paths = Vector{String}[]
    frontier = [[asset_in]]
    for _hop in 1:max_hops
        next_frontier = Vector{String}[]
        for path in frontier
            current = path[end]
            for (a, b) in edges
                neighbor = current == a ? b : current == b ? a : nothing
                if neighbor === nothing || neighbor in path
                    continue
                end
                extended = vcat(path, [neighbor])
                if neighbor == asset_out
                    push!(paths, extended)
                else
                    push!(next_frontier, extended)
                end
            end
        end
        frontier = next_frontier
    end
    return paths
end

function case_result(id::String, ok::Bool, observed::String)::Dict{String, Any}
    return Dict("id" => id, "ok" => ok, "observed" => observed)
end

function run_cases()::Vector{Dict{String, Any}}
    cases = Dict{String, Any}[]

    margin = 1_000
    shock_pnl = 2_000
    initial_capital = 2 * margin
    standard_profit = standard_sybil_final_capital(margin, shock_pnl) - initial_capital
    insurance_draw = standard_insurance_draw(margin, shock_pnl)
    push!(
        cases,
        case_result(
            "standard_sybil_profit_equals_insurance_draw",
            standard_profit == insurance_draw && insurance_draw == 1_000,
            "standard_profit=$(standard_profit) insurance_draw=$(insurance_draw)",
        ),
    )

    adl_final = adl_sybil_final_capital(margin, shock_pnl)
    adl_profit = adl_final - initial_capital
    push!(
        cases,
        case_result(
            "adl_haircut_blocks_sybil_profit",
            adl_final == initial_capital && adl_profit == 0,
            "adl_final=$(adl_final) initial_capital=$(initial_capital) adl_profit=$(adl_profit)",
        ),
    )

    push!(
        cases,
        case_result(
            "adl_deficit_covered_by_winner_pnl",
            bankruptcy_deficit(margin, shock_pnl) <= shock_pnl,
            "deficit=$(bankruptcy_deficit(margin, shock_pnl)) winner_pnl=$(shock_pnl)",
        ),
    )

    epoch_reward = 10_000
    attacker_liquidity = 9_900_000
    attacker_duration = 1
    honest_liquidity = 100_000
    honest_duration = 1_000
    snapshot = snapshot_reward(epoch_reward, attacker_liquidity, honest_liquidity)
    twal = twal_reward(
        epoch_reward,
        attacker_liquidity,
        attacker_duration,
        honest_liquidity,
        honest_duration,
    )
    push!(
        cases,
        case_result(
            "snapshot_reward_matches_yield_vampire_witness",
            snapshot == 9_900,
            "snapshot_reward=$(snapshot)",
        ),
    )

    push!(
        cases,
        case_result(
            "twal_reward_matches_duration_exposure_witness",
            twal == 900 && twal < snapshot,
            "twal_reward=$(twal) snapshot_reward=$(snapshot)",
        ),
    )

    push!(
        cases,
        case_result(
            "twal_share_cross_multiply_less_than_snapshot",
            twal_share_lt_snapshot(attacker_liquidity, attacker_duration, honest_liquidity, honest_duration),
            "attacker_liquidity=$(attacker_liquidity) attacker_duration=$(attacker_duration) honest_duration=$(honest_duration)",
        ),
    )

    edges = [
        ("cbZENO", "wstZENO"),
        ("stZENO", "cbZENO"),
        ("wstZENO", "stZENO"),
    ]
    same_asset_paths = ring_paths(edges, "wstZENO", "wstZENO", 2)
    cross_asset_paths = ring_paths(edges, "wstZENO", "cbZENO", 2)
    acyclic = all(path -> length(path) == length(unique(path)), cross_asset_paths)
    bounded = all(path -> 2 <= length(path) <= 3, cross_asset_paths)
    push!(
        cases,
        case_result(
            "same_asset_exact_out_ring_rejected",
            isempty(same_asset_paths),
            "path_count=$(length(same_asset_paths))",
        ),
    )

    push!(
        cases,
        case_result(
            "two_hop_ring_paths_are_bounded_and_acyclic",
            length(cross_asset_paths) == 2 && acyclic && bounded,
            "path_count=$(length(cross_asset_paths)) acyclic=$(acyclic) bounded=$(bounded)",
        ),
    )

    return cases
end

function print_text(cases::Vector{Dict{String, Any}})::Nothing
    failed = [case for case in cases if !case["ok"]]
    println("schema = $(SCHEMA)")
    println("case_count = $(length(cases))")
    println("failed_count = $(length(failed))")
    println("status = $(isempty(failed) ? "accepted" : "rejected")")
end

function json_escape(value::String)::String
    escaped = replace(value, "\\" => "\\\\", "\"" => "\\\"")
    return "\"$(escaped)\""
end

function print_json(cases::Vector{Dict{String, Any}})::Nothing
    failed = [case for case in cases if !case["ok"]]
    println("{")
    println("  \"schema\": $(json_escape(SCHEMA)),")
    println("  \"ok\": $(isempty(failed) ? "true" : "false"),")
    println("  \"status\": $(json_escape(isempty(failed) ? "accepted" : "rejected")),")
    println("  \"case_count\": $(length(cases)),")
    println("  \"failed_count\": $(length(failed)),")
    println("  \"cases\": [")
    for (index, case) in enumerate(cases)
        suffix = index == length(cases) ? "" : ","
        println("    {")
        println("      \"id\": $(json_escape(case["id"])),")
        println("      \"ok\": $(case["ok"] ? "true" : "false"),")
        println("      \"observed\": $(json_escape(case["observed"]))")
        println("    }$(suffix)")
    end
    println("  ]")
    println("}")
end

function main(args::Vector{String})::Int
    format = "--json" in args ? "json" : "text"
    cases = run_cases()
    if format == "json"
        print_json(cases)
    else
        print_text(cases)
    end
    return all(case -> case["ok"], cases) ? 0 : 1
end

exit(main(ARGS))
