#!/usr/bin/env julia

const SCHEMA = "zenodex.oracle.math_witness_sweep.v1"
const BPS = 10_000

median3(a::Int, b::Int, c::Int)::Int = sort([a, b, c])[2]

function div_bps(delta::Int, reference::Int)::Int
    reference > 0 || error("reference must be positive")
    return div(delta * BPS, reference)
end

function max_median_deviation_bps(values::NTuple{3, Int})::Int
    m = median3(values...)
    m > 0 || error("median must be positive")
    return maximum(div_bps(abs(v - m), m) for v in values)
end

function source_cartel_rejected(operators::Vector{String}, max_same_operator::Int)::Bool
    max_seen = maximum(count(==(operator), operators) for operator in unique(operators))
    return max_seen > max_same_operator || length(unique(operators)) < length(operators)
end

reward_transition_ok(before::Int, reward::Int, after::Int)::Bool =
    before >= 0 && reward > 0 && after >= 0 && reward == before - after

dispute_grief_rejected(dispute_bond::Int)::Bool = dispute_bond <= 0

split_brain_rejected(
    zusd_price_e8::Int,
    zusd_epoch::Int,
    perp_price_e8::Int,
    perp_epoch::Int,
    max_divergence_bps::Int,
    max_epoch_lag::Int,
)::Bool = begin
    divergence = div_bps(abs(zusd_price_e8 - perp_price_e8), perp_price_e8)
    lag = abs(zusd_epoch - perp_epoch)
    divergence > max_divergence_bps || lag > max_epoch_lag
end

o5_independence_witness_ok(
    primary_o5_claim::Bool,
    distinct_verifiers::Bool,
    distinct_proof_kinds::Bool,
    same_input_root::Bool,
    same_output_root::Bool,
    dag_closed::Bool,
)::Bool = primary_o5_claim &&
          distinct_verifiers &&
          distinct_proof_kinds &&
          same_input_root &&
          same_output_root &&
          dag_closed

function case_result(id::String, ok::Bool, observed::String)::Dict{String, Any}
    return Dict("id" => id, "ok" => ok, "observed" => observed)
end

function run_cases()::Vector{Dict{String, Any}}
    cases = Dict{String, Any}[]

    boundary_dev = max_median_deviation_bps((100_000_000, 102_000_000, 98_000_000))
    push!(
        cases,
        case_result(
            "median_deviation_boundary_accepts",
            boundary_dev == 200,
            "max_deviation_bps=$(boundary_dev)",
        ),
    )

    reject_dev = max_median_deviation_bps((100_000_000, 103_000_000, 98_000_000))
    push!(
        cases,
        case_result(
            "median_deviation_boundary_rejects",
            reject_dev == 300,
            "max_deviation_bps=$(reject_dev)",
        ),
    )

    push!(
        cases,
        case_result(
            "source_cartel_operator_concentration_rejects",
            source_cartel_rejected(["cartel", "cartel", "cartel"], 1),
            "operators=3 unique=1 max_same_operator=1",
        ),
    )

    push!(
        cases,
        case_result(
            "zero_bond_dispute_grief_rejects",
            dispute_grief_rejected(0),
            "dispute_bond_e8=0",
        ),
    )

    push!(
        cases,
        case_result(
            "reward_pool_conservation_accepts",
            reward_transition_ok(100_000_000, 25_000_000, 75_000_000),
            "before=100000000 reward=25000000 after=75000000",
        ),
    )

    push!(
        cases,
        case_result(
            "reward_pool_overpay_rejects",
            !reward_transition_ok(100_000_000, 101_000_000, 0),
            "before=100000000 reward=101000000 after=0",
        ),
    )

    push!(
        cases,
        case_result(
            "split_brain_divergence_rejects",
            split_brain_rejected(100_000_000, 10, 110_000_000, 10, 100, 1),
            "zusd=100000000 perp=110000000 max_divergence_bps=100",
        ),
    )

    push!(
        cases,
        case_result(
            "split_brain_epoch_lag_rejects",
            split_brain_rejected(100_000_000, 10, 100_000_000, 13, 0, 1),
            "zusd_epoch=10 perp_epoch=13 max_epoch_lag=1",
        ),
    )

    push!(
        cases,
        case_result(
            "o5_independence_witness_accepts_distinct_mechanisms",
            o5_independence_witness_ok(true, true, true, true, true, true),
            "primary_o5=true distinct_verifiers=true distinct_proof_kinds=true same_roots=true dag_closed=true",
        ),
    )

    push!(
        cases,
        case_result(
            "o5_independence_missing_distinct_verifiers_rejects",
            !o5_independence_witness_ok(true, false, true, true, true, true),
            "primary_o5=true distinct_verifiers=false distinct_proof_kinds=true same_roots=true dag_closed=true",
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
