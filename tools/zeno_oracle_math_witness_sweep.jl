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

function median_deviation_side_obligations_ok(
    values::NTuple{3, Int},
    bps::Int,
    max_allowed_bps::Int,
)::Bool
    sorted_values = sort([values...])
    lo, mid, hi = sorted_values
    mid > 0 || error("median must be positive")
    lo_side = div((mid - lo) * bps, mid)
    hi_side = div((hi - mid) * bps, mid)
    return lo_side <= max_allowed_bps && hi_side <= max_allowed_bps
end

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

settlement_execution_totals(
    report_rewards_e8::Vector{Int},
    dispute_rewards_e8::Vector{Int},
    bond_withdrawals_e8::Vector{Int},
    slashes_e8::Vector{Int},
    fees_paid_e8::Vector{Int},
    treasury_deltas_e8::Vector{Int},
    burn_deltas_e8::Vector{Int},
)::NTuple{7, Int} = begin
    all(values -> all(value -> value >= 0, values), (
        report_rewards_e8,
        dispute_rewards_e8,
        bond_withdrawals_e8,
        slashes_e8,
        fees_paid_e8,
        treasury_deltas_e8,
        burn_deltas_e8,
    )) || error("settlement totals must be nonnegative")
    return (
        sum(report_rewards_e8),
        sum(dispute_rewards_e8),
        sum(bond_withdrawals_e8),
        sum(slashes_e8),
        sum(fees_paid_e8),
        sum(treasury_deltas_e8),
        sum(burn_deltas_e8),
    )
end

settlement_execution_totals_ok(expected::NTuple{7, Int}, observed::NTuple{7, Int})::Bool =
    expected == observed

settlement_execution_total_e8(totals::NTuple{7, Int})::Int = begin
    all(value -> value >= 0, totals) || error("settlement total components must be nonnegative")
    return sum(totals)
end

settlement_execution_components_bounded_by_total(totals::NTuple{7, Int})::Bool = begin
    total = settlement_execution_total_e8(totals)
    return all(component -> component <= total, totals)
end

settlement_execution_budget_caps_components(totals::NTuple{7, Int}, budget::Int)::Bool = begin
    budget >= 0 || error("budget must be nonnegative")
    return settlement_execution_total_e8(totals) <= budget &&
           all(component -> component <= budget, totals)
end

settlement_execution_receipt_ok(
    query_bound::Bool,
    totals_bound::Bool,
    asset_bound::Bool,
    contract_bound::Bool,
)::Bool = query_bound && totals_bound && asset_bound && contract_bound

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

terminal_dag_ok(
    deps_available::Bool,
    no_duplicate_receipts::Bool,
    content_hashes_bound::Bool,
)::Bool = deps_available && no_duplicate_receipts && content_hashes_bound

oracle_runtime_binding_ok(
    registry_root_bound::Bool,
    runtime_state_bound::Bool,
    value_bound::Bool,
    same_consumer_action::Bool,
)::Bool = registry_root_bound && runtime_state_bound && value_bound && same_consumer_action

oracle_sync_window_ok(source_epoch::Int, target_epoch::Int, max_lag::Int)::Bool =
    max_lag >= 0 && epoch_lag(source_epoch, target_epoch) <= max_lag

oracle_sync_window_composes(
    source_epoch::Int,
    bridge_epoch::Int,
    target_epoch::Int,
    max_ab::Int,
    max_bc::Int,
)::Bool =
    !(
        oracle_sync_window_ok(source_epoch, bridge_epoch, max_ab) &&
        oracle_sync_window_ok(bridge_epoch, target_epoch, max_bc)
    ) || oracle_sync_window_ok(source_epoch, target_epoch, max_ab + max_bc)

o3_action_binding_ok(
    terminal_dag::Bool,
    runtime_binding::Bool,
    sync_window::Bool,
)::Bool = terminal_dag && runtime_binding && sync_window

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

    grid_decomposes = all(
        (max_median_deviation_bps_scaled((lo, 100, hi), BPS) <= 200) ==
            median_deviation_side_obligations_ok((lo, 100, hi), BPS, 200)
        for lo in 95:100 for hi in 100:105
    )
    push!(
        cases,
        case_result(
            "median_deviation_small_grid_decomposes_to_side_obligations",
            grid_decomposes,
            "lo_range=95:100 mid=100 hi_range=100:105 max_allowed_bps=200",
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

    settlement_totals = settlement_execution_totals(
        [25_000_000, 25_000_000],
        [10_000_000],
        [250_000_000_000],
        [5_000_000],
        [100_000_000],
        [60_000_000],
        [15_000_000],
    )
    expected_totals = (
        50_000_000,
        10_000_000,
        250_000_000_000,
        5_000_000,
        100_000_000,
        60_000_000,
        15_000_000,
    )
    drifted_totals = (
        49_999_999,
        10_000_000,
        250_000_000_000,
        5_000_000,
        100_000_000,
        60_000_000,
        15_000_000,
    )
    push!(
        cases,
        case_result(
            "live_economics_settlement_execution_totals_match_replay",
            settlement_execution_totals_ok(expected_totals, settlement_totals),
            "report_rewards=50000000 dispute_rewards=10000000 withdrawals=250000000000 slashes=5000000 fee_paid=100000000 treasury=60000000 burn=15000000",
        ),
    )

    push!(
        cases,
        case_result(
            "live_economics_settlement_execution_total_drift_rejects",
            !settlement_execution_totals_ok(drifted_totals, settlement_totals),
            "expected_report_rewards=49999999 observed_report_rewards=50000000",
        ),
    )

    settlement_grand_total = settlement_execution_total_e8(settlement_totals)
    push!(
        cases,
        case_result(
            "live_economics_settlement_execution_components_bounded_by_total",
            settlement_execution_components_bounded_by_total(settlement_totals) &&
                settlement_grand_total == 250_240_000_000,
            "grand_total=$(settlement_grand_total) component_count=7",
        ),
    )

    push!(
        cases,
        case_result(
            "live_economics_settlement_execution_budget_caps_components",
            settlement_execution_budget_caps_components(settlement_totals, settlement_grand_total) &&
                !settlement_execution_budget_caps_components(settlement_totals, settlement_grand_total - 1),
            "budget=$(settlement_grand_total) short_budget=$(settlement_grand_total - 1)",
        ),
    )

    push!(
        cases,
        case_result(
            "live_economics_settlement_execution_receipt_accepts_bound_obligations",
            settlement_execution_receipt_ok(true, true, true, true),
            "query_bound=true totals_bound=true asset_bound=true contract_bound=true",
        ),
    )

    push!(
        cases,
        case_result(
            "live_economics_settlement_execution_receipt_rejects_asset_or_contract_drift",
            !settlement_execution_receipt_ok(true, true, false, true) &&
                !settlement_execution_receipt_ok(true, true, true, false),
            "asset_bound=false_or_contract_bound=false",
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

    push!(
        cases,
        case_result(
            "o3_action_binding_accepts_dag_runtime_sync",
            o3_action_binding_ok(
                terminal_dag_ok(true, true, true),
                oracle_runtime_binding_ok(true, true, true, true),
                oracle_sync_window_ok(100, 101, 1),
            ),
            "dag_closed=true runtime_bound=true sync_lag=1 max_lag=1",
        ),
    )

    push!(
        cases,
        case_result(
            "terminal_dag_duplicate_receipt_rejects",
            !terminal_dag_ok(true, false, true),
            "deps_available=true no_duplicate_receipts=false content_hashes_bound=true",
        ),
    )

    push!(
        cases,
        case_result(
            "o3_action_binding_missing_value_binding_rejects",
            !o3_action_binding_ok(
                terminal_dag_ok(true, true, true),
                oracle_runtime_binding_ok(true, true, false, true),
                oracle_sync_window_ok(100, 101, 1),
            ),
            "dag_closed=true runtime_state_bound=true value_bound=false same_consumer_action=true",
        ),
    )

    push!(
        cases,
        case_result(
            "o3_action_binding_wrong_consumer_action_rejects",
            !o3_action_binding_ok(
                terminal_dag_ok(true, true, true),
                oracle_runtime_binding_ok(true, true, true, false),
                oracle_sync_window_ok(100, 101, 1),
            ),
            "dag_closed=true runtime_state_bound=true value_bound=true same_consumer_action=false",
        ),
    )

    push!(
        cases,
        case_result(
            "oracle_sync_window_epoch_lag_rejects",
            !oracle_sync_window_ok(100, 103, 1),
            "source_epoch=100 target_epoch=103 max_lag=1",
        ),
    )

    push!(
        cases,
        case_result(
            "o3_action_binding_sync_window_widening_preserves_acceptance",
            o3_action_binding_ok(
                terminal_dag_ok(true, true, true),
                oracle_runtime_binding_ok(true, true, true, true),
                oracle_sync_window_ok(100, 101, 1),
            ) &&
                o3_action_binding_ok(
                    terminal_dag_ok(true, true, true),
                    oracle_runtime_binding_ok(true, true, true, true),
                    oracle_sync_window_ok(100, 101, 3),
                ) &&
                !oracle_sync_window_ok(100, 103, 1) &&
                oracle_sync_window_ok(100, 103, 3),
            "accepted_lag=1 widened_max_lag=3 stale_at_1_accepted_at_3",
        ),
    )

    sync_composition_grid = all(
        oracle_sync_window_composes(a, b, c, max_ab, max_bc)
        for a in 98:102
        for b in 98:102
        for c in 98:102
        for max_ab in 0:4
        for max_bc in 0:4
    )
    push!(
        cases,
        case_result(
            "oracle_sync_window_composition_preserves_bound",
            sync_composition_grid &&
                oracle_sync_window_ok(100, 102, 2) &&
                oracle_sync_window_ok(102, 105, 3) &&
                oracle_sync_window_ok(100, 105, 5),
            "grid_epochs=98:102 max_ab=0:4 max_bc=0:4 sample=100->102->105 composed_max=5",
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
