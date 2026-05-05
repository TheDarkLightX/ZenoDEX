#!/usr/bin/env julia

const SCHEMA = "zenodex.oracle.math_witness_sweep.v1"
const BPS = 10_000

median3(a::Int, b::Int, c::Int)::Int = sort([a, b, c])[2]

function div_bps(delta::Int, reference::Int)::Int
    reference > 0 || error("reference must be positive")
    return div(delta * BPS, reference)
end

function max_median_deviation_bps_scaled(values::NTuple{3, Int}, bps::Int)::Int
    m = median3(values...)
    m > 0 || error("median must be positive")
    bps >= 0 || error("bps must be nonnegative")
    return maximum(div(abs(v - m) * bps, m) for v in values)
end

max_median_deviation_bps(values::NTuple{3, Int})::Int =
    max_median_deviation_bps_scaled(values, BPS)

epoch_lag(left::Int, right::Int)::Int = abs(left - right)

function source_cartel_rejected(operators::Vector{String}, max_same_operator::Int)::Bool
    max_seen = maximum(count(==(operator), operators) for operator in unique(operators))
    return max_seen > max_same_operator || length(unique(operators)) < length(operators)
end

reward_transition_ok(before::Int, reward::Int, after::Int)::Bool =
    before >= 0 && reward > 0 && after >= 0 && reward == before - after

reward_not_overpaid(before::Int, reward::Int)::Bool =
    before >= 0 && reward >= 0 && reward <= before

live_economics_escrow_floor_e8(
    initial_dispute_pool_e8::Int,
    reporter_bonds_e8::Vector{Int},
    fee_paid_e8::Int,
)::Int = begin
    initial_dispute_pool_e8 >= 0 || error("initial dispute pool must be nonnegative")
    fee_paid_e8 >= 0 || error("fee paid must be nonnegative")
    all(bond -> bond >= 0, reporter_bonds_e8) || error("reporter bonds must be nonnegative")
    return initial_dispute_pool_e8 + sum(reporter_bonds_e8) + fee_paid_e8
end

escrow_funding_ok(required_floor_e8::Int, balance_e8::Int)::Bool =
    required_floor_e8 >= 0 && balance_e8 >= required_floor_e8

governance_timelock_ok(
    queued_at_timestamp::Int,
    executable_after_timestamp::Int,
    executed_at_timestamp::Int,
    timelock_seconds::Int,
)::Bool =
    timelock_seconds >= 0 &&
    executable_after_timestamp - queued_at_timestamp >= timelock_seconds &&
    executed_at_timestamp >= executable_after_timestamp

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

    zero_scale_dev = max_median_deviation_bps_scaled((100_000_000, 103_000_000, 98_000_000), 0)
    push!(
        cases,
        case_result(
            "median_deviation_zero_scale_is_zero",
            zero_scale_dev == 0,
            "max_deviation_bps=$(zero_scale_dev) scale_bps=0",
        ),
    )

    equal_value_dev = max_median_deviation_bps((100_000_000, 100_000_000, 100_000_000))
    push!(
        cases,
        case_result(
            "median_deviation_equal_values_are_zero",
            equal_value_dev == 0,
            "max_deviation_bps=$(equal_value_dev)",
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
            "reward_amount_cannot_exceed_pool",
            reward_not_overpaid(100_000_000, 25_000_000) &&
                !reward_not_overpaid(100_000_000, 101_000_000),
            "before=100000000 accepted_reward=25000000 rejected_reward=101000000",
        ),
    )

    escrow_floor = live_economics_escrow_floor_e8(
        20_000_000,
        [250_000_000_000, 250_000_000_000, 250_000_000_000],
        100_000_000,
    )
    push!(
        cases,
        case_result(
            "live_economics_escrow_floor_matches_replay",
            escrow_floor == 750_120_000_000,
            "escrow_floor_e8=$(escrow_floor)",
        ),
    )

    push!(
        cases,
        case_result(
            "live_economics_escrow_shortfall_rejects",
            escrow_funding_ok(escrow_floor, escrow_floor) &&
                !escrow_funding_ok(escrow_floor, escrow_floor - 1),
            "floor=$(escrow_floor) accepted_balance=$(escrow_floor) rejected_balance=$(escrow_floor - 1)",
        ),
    )

    push!(
        cases,
        case_result(
            "live_economics_governance_timelock_accepts",
            governance_timelock_ok(1_800_000_000, 1_800_172_800, 1_800_172_800, 172_800),
            "queued=1800000000 executable_after=1800172800 executed=1800172800 delay=172800",
        ),
    )

    push!(
        cases,
        case_result(
            "live_economics_governance_early_execution_rejects",
            !governance_timelock_ok(1_800_000_000, 1_800_172_800, 1_800_172_799, 172_800),
            "queued=1800000000 executable_after=1800172800 executed=1800172799 delay=172800",
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
            "epoch_lag_is_symmetric",
            epoch_lag(10, 13) == epoch_lag(13, 10) && epoch_lag(10, 10) == 0,
            "lag(10,13)=$(epoch_lag(10, 13)) lag(13,10)=$(epoch_lag(13, 10))",
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
