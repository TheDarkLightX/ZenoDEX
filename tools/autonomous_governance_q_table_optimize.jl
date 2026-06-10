#!/usr/bin/env julia

# Deterministic offline optimizer for autonomous governance Q-table artifacts.
#
# This is an EBRM-style hand-energy baseline. It enumerates the bounded state-bin
# space and action set, assigns an integer energy to each candidate action, and
# emits a frozen lookup-table policy. Runtime governance does not call Julia and
# does not trust the energy score for acceptance; the Python/Tau gates decide.

using Dates

const POLICY_SCHEMA = "zenodex.autonomous_governance.q_policy.v1"
const REPORT_SCHEMA = "zenodex.autonomous_governance.julia_q_table_optimizer.v1"
const U16_MAX = 0xFFFF
const MIN_DELAY = 24

const STATE_BINS = Dict{String,Vector{Int}}(
    "deviation_bps" => [25, 100, 300],
    "volatility_bps" => [50, 200, 500],
    "liquidity_depth_bps" => [1_000, 3_000],
    "fee_bps" => [9, 50, 990],
    "funding_cap_bps" => [10, 190],
    "buyburn_bps" => [0, 9_000, 9_900],
    "reserve_bps" => [0, 9_000, 9_900],
)

const SAFETY = Dict{String,Any}(
    "max_freshness_lag_epochs" => 2,
    "max_divergence_bps" => 75,
    "max_volatility_bps" => 1_000,
    "min_liquidity_depth_bps" => 1_000,
    "min_cooldown_epochs" => 1,
    "emergency_pause" => false,
)

const SURFACE_STATE = Dict{String,Int}(
    "fee_bps" => 30,
    "buyburn_bps" => 6_000,
    "stakers_bps" => 0,
    "reserve_bps" => 2_000,
    "hosts_bps" => 2_000,
    "mcr_bps" => 11_000,
    "ccr_bps" => 15_000,
    "staker_bps" => 5_000,
    "funding_cap_bps" => 120,
)

function action(id::String, deltas::Dict{String,Int})
    return Dict{String,Any}("id" => id, "deltas" => deltas)
end

const ACTIONS = [
    action("hold", Dict{String,Int}()),
    action("raise_fee_10", Dict("fee_bps" => 10)),
    action("lower_fee_10", Dict("fee_bps" => -10)),
    action("raise_fee_10_tighten_funding_5", Dict("fee_bps" => 10, "funding_cap_bps" => -5)),
    action("lower_fee_10_relax_funding_5", Dict("fee_bps" => -10, "funding_cap_bps" => 5)),
    action("shift_router_to_reserve_100", Dict("buyburn_bps" => -100, "reserve_bps" => 100)),
    action("shift_router_to_buyburn_100", Dict("reserve_bps" => -100, "buyburn_bps" => 100)),
    action(
        "raise_fee_10_shift_router_to_reserve_100",
        Dict("fee_bps" => 10, "buyburn_bps" => -100, "reserve_bps" => 100),
    ),
    action(
        "raise_fee_10_tighten_funding_5_shift_router_to_reserve_100",
        Dict("fee_bps" => 10, "funding_cap_bps" => -5, "buyburn_bps" => -100, "reserve_bps" => 100),
    ),
    action(
        "lower_fee_10_relax_funding_5_shift_router_to_reserve_100",
        Dict("fee_bps" => -10, "funding_cap_bps" => 5, "buyburn_bps" => -100, "reserve_bps" => 100),
    ),
]

function parse_args(args)
    opts = Dict{String,String}()
    flags = Set{String}()
    i = 1
    while i <= length(args)
        key = args[i]
        if key in ("--quiet", "--text")
            push!(flags, key)
            i += 1
        elseif startswith(key, "--")
            i < length(args) || error("missing value for $(key)")
            opts[key] = args[i + 1]
            i += 2
        else
            error("unexpected argument: $(key)")
        end
    end
    return opts, flags
end

in_domain(values::Int...) = all(v -> 0 <= v <= U16_MAX, values)
timelock_ok(proposal_epoch::Int, current_epoch::Int) =
    current_epoch >= proposal_epoch && current_epoch - proposal_epoch >= MIN_DELAY
step_ok(curr::Int, nxt::Int, step::Int) = abs(curr - nxt) <= step

function apply_action(state::Dict{String,Int}, a::Dict{String,Any})
    proposed = copy(state)
    for (key, delta) in a["deltas"]
        proposed[key] = get(proposed, key, 0) + Int(delta)
    end
    return proposed
end

function fee_ok(current, proposed, proposal_epoch::Int, current_epoch::Int)
    in_domain(current["fee_bps"], proposed["fee_bps"], proposal_epoch, current_epoch) || return false
    return timelock_ok(proposal_epoch, current_epoch) &&
        0 <= proposed["fee_bps"] <= 1_000 &&
        step_ok(current["fee_bps"], proposed["fee_bps"], 50)
end

function router_ok(current, proposed, proposal_epoch::Int, current_epoch::Int)
    keys = ["buyburn_bps", "stakers_bps", "reserve_bps", "hosts_bps"]
    nexts = [proposed[k] for k in keys]
    currs = [current[k] for k in keys]
    in_domain(proposal_epoch, current_epoch, nexts..., currs...) || return false
    return timelock_ok(proposal_epoch, current_epoch) &&
        all(v -> 0 <= v <= 10_000, nexts) &&
        sum(nexts) == 10_000 &&
        all(i -> step_ok(currs[i], nexts[i], 500), eachindex(keys))
end

function collateral_ok(current, proposed, proposal_epoch::Int, current_epoch::Int)
    vals = (
        current["mcr_bps"],
        proposed["mcr_bps"],
        current["ccr_bps"],
        proposed["ccr_bps"],
        proposal_epoch,
        current_epoch,
    )
    in_domain(vals...) || return false
    return timelock_ok(proposal_epoch, current_epoch) &&
        proposed["mcr_bps"] >= 10_000 &&
        proposed["ccr_bps"] <= 30_000 &&
        proposed["mcr_bps"] <= proposed["ccr_bps"] &&
        step_ok(current["mcr_bps"], proposed["mcr_bps"], 1_000) &&
        step_ok(current["ccr_bps"], proposed["ccr_bps"], 1_000)
end

function whale_ok(current, proposed, proposal_epoch::Int, current_epoch::Int)
    in_domain(current["staker_bps"], proposed["staker_bps"], proposal_epoch, current_epoch) || return false
    return timelock_ok(proposal_epoch, current_epoch) &&
        0 <= proposed["staker_bps"] <= 7_000 &&
        step_ok(current["staker_bps"], proposed["staker_bps"], 500)
end

function funding_ok(current, proposed, proposal_epoch::Int, current_epoch::Int)
    in_domain(current["funding_cap_bps"], proposed["funding_cap_bps"], proposal_epoch, current_epoch) || return false
    return timelock_ok(proposal_epoch, current_epoch) &&
        0 <= proposed["funding_cap_bps"] <= 200 &&
        step_ok(current["funding_cap_bps"], proposed["funding_cap_bps"], 25)
end

function gate_report(current, proposed; proposal_epoch::Int = 10, current_epoch::Int = 34)
    fee = fee_ok(current, proposed, proposal_epoch, current_epoch)
    router = router_ok(current, proposed, proposal_epoch, current_epoch)
    collateral = collateral_ok(current, proposed, proposal_epoch, current_epoch)
    whale = whale_ok(current, proposed, proposal_epoch, current_epoch)
    funding = funding_ok(current, proposed, proposal_epoch, current_epoch)
    return Dict{String,Bool}(
        "fee" => fee,
        "router" => router,
        "collateral" => collateral,
        "whale" => whale,
        "funding" => funding,
        "master" => fee && router && collateral && whale,
    )
end

function delta(a::Dict{String,Any}, key::String)::Int
    return Int(get(a["deltas"], key, 0))
end

function target_fee_delta(deviation_bin::Int, volatility_bin::Int, liquidity_bin::Int)::Int
    if deviation_bin >= 2
        return 10
    elseif deviation_bin == 0 && volatility_bin == 0 && liquidity_bin == 0
        return -10
    end
    return 0
end

function target_funding_delta(deviation_bin::Int, volatility_bin::Int, liquidity_bin::Int)::Int
    if deviation_bin >= 3 && volatility_bin >= 2
        return -5
    elseif deviation_bin == 0 && volatility_bin == 0 && liquidity_bin == 0
        return 5
    end
    return 0
end

target_reserve_delta(deviation_bin::Int, liquidity_bin::Int)::Int =
    liquidity_bin == 0 ? 100 : 0

function action_energy(deviation_bin::Int, volatility_bin::Int, liquidity_bin::Int, a::Dict{String,Any})
    proposed = apply_action(SURFACE_STATE, a)
    gates = gate_report(SURFACE_STATE, proposed)
    hard = all(values(gates)) ? 0 : 1_000_000

    fee_delta = delta(a, "fee_bps")
    funding_delta = delta(a, "funding_cap_bps")
    reserve_delta = delta(a, "reserve_bps")
    buyburn_delta = delta(a, "buyburn_bps")

    fee_target = target_fee_delta(deviation_bin, volatility_bin, liquidity_bin)
    funding_target = target_funding_delta(deviation_bin, volatility_bin, liquidity_bin)
    reserve_target = target_reserve_delta(deviation_bin, liquidity_bin)

    target_miss =
        12 * abs(fee_delta - fee_target) +
        10 * abs(funding_delta - funding_target) +
        div(abs(reserve_delta - reserve_target), 5)

    churn =
        2 * abs(fee_delta) +
        6 * abs(funding_delta) +
        div(abs(reserve_delta) + abs(buyburn_delta), 20)

    low_stress = deviation_bin <= 1 && volatility_bin <= 1 && liquidity_bin >= 1
    overcontrol = low_stress && a["id"] != "hold" ? 40 : 0

    ebrm_prior = 0
    if deviation_bin >= 3 && volatility_bin >= 2 && a["id"] == "raise_fee_10_tighten_funding_5"
        ebrm_prior -= 70
    elseif deviation_bin >= 3 && volatility_bin >= 2 &&
           liquidity_bin == 0 &&
           a["id"] == "raise_fee_10_tighten_funding_5_shift_router_to_reserve_100"
        ebrm_prior -= 95
    elseif deviation_bin >= 2 && a["id"] == "raise_fee_10"
        ebrm_prior -= 25
    end
    if ((deviation_bin == 2) || (deviation_bin >= 3 && volatility_bin <= 1)) &&
       liquidity_bin == 0 &&
       a["id"] == "raise_fee_10_shift_router_to_reserve_100"
        ebrm_prior -= 100
    end
    if liquidity_bin == 0 && deviation_bin <= 1 && a["id"] == "shift_router_to_reserve_100"
        ebrm_prior -= 45
    end
    if liquidity_bin == 0 &&
       deviation_bin == 0 &&
       volatility_bin == 0 &&
       a["id"] == "lower_fee_10_relax_funding_5_shift_router_to_reserve_100"
        ebrm_prior -= 70
    end
    if low_stress && a["id"] == "hold"
        ebrm_prior -= 35
    end

    total = hard + target_miss + churn + overcontrol + ebrm_prior
    return total, Dict{String,Any}(
        "hard_gate_penalty" => hard,
        "target_miss" => target_miss,
        "churn" => churn,
        "overcontrol" => overcontrol,
        "ebrm_prior" => ebrm_prior,
        "total" => total,
        "gates" => gates,
    )
end

function surface_edge_layer(id::String, feature::String, q_table::Dict)
    table = copy(q_table)
    table["*"] = Dict{String,Int}()
    return Dict{String,Any}(
        "id" => id,
        "features" => [feature],
        "q_table" => table,
    )
end

function optimize_table()
    q_table = Dict{String,Any}()
    best_actions = Dict{String,Any}()
    breakdowns = Dict{String,Any}()
    hard_gate_fail_count = 0

    action_ids = [String(a["id"]) for a in ACTIONS]
    for deviation_bin in 0:3
        for volatility_bin in 0:3
            for liquidity_bin in 0:2
                key = "$(deviation_bin)|$(volatility_bin)|$(liquidity_bin)"
                row = Dict{String,Int}()
                row_breakdowns = Dict{String,Any}()
                for a in ACTIONS
                    energy, details = action_energy(deviation_bin, volatility_bin, liquidity_bin, a)
                    row[String(a["id"])] = -energy
                    row_breakdowns[String(a["id"])] = details
                    if details["hard_gate_penalty"] > 0
                        hard_gate_fail_count += 1
                    end
                end
                best_id = action_ids[1]
                best_score = row[best_id]
                for id in action_ids[2:end]
                    if row[id] > best_score
                        best_id = id
                        best_score = row[id]
                    end
                end
                q_table[key] = row
                best_actions[key] = best_id
                breakdowns[key] = row_breakdowns
            end
        end
    end

    policy = Dict{String,Any}(
        "schema" => POLICY_SCHEMA,
        "policy_id" => "julia_ebr_governance_surface_q_policy_v1",
        "version" => 1,
        "safety" => SAFETY,
        "selection" => Dict{String,Any}(
            "mode" => "first_admissible",
            "anti_oscillation" => Dict{String,Any}(
                "enabled" => true,
                "parameters" => ["fee_bps", "funding_cap_bps"],
            ),
        ),
        "state_bins" => STATE_BINS,
        "actions" => ACTIONS,
        "q_layers" => [
            Dict{String,Any}(
                "id" => "julia_joint_ebr_energy_argmin",
                "features" => ["deviation_bps", "volatility_bps", "liquidity_depth_bps"],
                "q_table" => q_table,
            ),
            surface_edge_layer(
                "fee_edge_bias",
                "fee_bps",
                Dict(
                    "0" => Dict(
                        "lower_fee_10" => -500,
                        "lower_fee_10_relax_funding_5" => -500,
                        "lower_fee_10_relax_funding_5_shift_router_to_reserve_100" => -500,
                        "hold" => 5,
                        "raise_fee_10" => 20,
                    ),
                    "3" => Dict(
                        "raise_fee_10" => -500,
                        "raise_fee_10_shift_router_to_reserve_100" => -500,
                        "raise_fee_10_tighten_funding_5" => -500,
                        "raise_fee_10_tighten_funding_5_shift_router_to_reserve_100" => -500,
                        "hold" => 5,
                        "lower_fee_10" => 60,
                        "lower_fee_10_relax_funding_5" => 80,
                        "lower_fee_10_relax_funding_5_shift_router_to_reserve_100" => 80,
                    ),
                ),
            ),
            surface_edge_layer(
                "funding_edge_bias",
                "funding_cap_bps",
                Dict(
                    "0" => Dict(
                        "raise_fee_10_tighten_funding_5" => -500,
                        "raise_fee_10_tighten_funding_5_shift_router_to_reserve_100" => -500,
                        "lower_fee_10_relax_funding_5" => 80,
                        "lower_fee_10_relax_funding_5_shift_router_to_reserve_100" => 80,
                        "hold" => 5,
                        "raise_fee_10" => 35,
                    ),
                    "2" => Dict(
                        "lower_fee_10_relax_funding_5" => -500,
                        "lower_fee_10_relax_funding_5_shift_router_to_reserve_100" => -500,
                        "hold" => 5,
                        "raise_fee_10_tighten_funding_5" => 25,
                    ),
                ),
            ),
            surface_edge_layer(
                "buyburn_edge_bias",
                "buyburn_bps",
                Dict(
                    "0" => Dict(
                        "shift_router_to_reserve_100" => -500,
                        "raise_fee_10_shift_router_to_reserve_100" => -500,
                        "raise_fee_10_tighten_funding_5_shift_router_to_reserve_100" => -500,
                        "lower_fee_10_relax_funding_5_shift_router_to_reserve_100" => -500,
                        "hold" => 5,
                    ),
                    "2" => Dict(
                        "shift_router_to_buyburn_100" => -500,
                        "hold" => 5,
                    ),
                    "3" => Dict(
                        "shift_router_to_buyburn_100" => -500,
                        "hold" => 5,
                    ),
                ),
            ),
            surface_edge_layer(
                "reserve_edge_bias",
                "reserve_bps",
                Dict(
                    "0" => Dict(
                        "shift_router_to_buyburn_100" => -500,
                        "shift_router_to_reserve_100" => 60,
                        "hold" => 25,
                    ),
                    "2" => Dict(
                        "shift_router_to_reserve_100" => -500,
                        "raise_fee_10_shift_router_to_reserve_100" => -500,
                        "raise_fee_10_tighten_funding_5_shift_router_to_reserve_100" => -500,
                        "lower_fee_10_relax_funding_5_shift_router_to_reserve_100" => -500,
                        "hold" => 5,
                    ),
                    "3" => Dict(
                        "shift_router_to_reserve_100" => -500,
                        "raise_fee_10_shift_router_to_reserve_100" => -500,
                        "raise_fee_10_tighten_funding_5_shift_router_to_reserve_100" => -500,
                        "lower_fee_10_relax_funding_5_shift_router_to_reserve_100" => -500,
                        "hold" => 5,
                    ),
                ),
            ),
            Dict{String,Any}(
                "id" => "reserve_cap_liquidity_recovery_bias",
                "features" => ["liquidity_depth_bps", "reserve_bps"],
                "q_table" => Dict(
                    "1|2" => Dict("shift_router_to_buyburn_100" => 160),
                    "2|2" => Dict("shift_router_to_buyburn_100" => 160),
                    "1|3" => Dict("shift_router_to_buyburn_100" => 160),
                    "2|3" => Dict("shift_router_to_buyburn_100" => 160),
                    "*" => Dict{String,Int}(),
                ),
            ),
            Dict{String,Any}(
                "id" => "reserve_cap_liquidity_floor_bias",
                "features" => ["deviation_bps", "volatility_bps", "liquidity_depth_bps", "reserve_bps"],
                "q_table" => Dict(
                    "0|0|0|2" => Dict(
                        "lower_fee_10_relax_funding_5" => 140,
                        "lower_fee_10" => 50,
                    ),
                    "0|1|0|2" => Dict("lower_fee_10" => 180),
                    "0|2|0|2" => Dict("lower_fee_10" => 180),
                    "0|3|0|2" => Dict("lower_fee_10" => 180),
                    "1|0|0|2" => Dict("lower_fee_10" => 180),
                    "1|1|0|2" => Dict("lower_fee_10" => 180),
                    "1|2|0|2" => Dict("lower_fee_10" => 180),
                    "1|3|0|2" => Dict("lower_fee_10" => 180),
                    "*" => Dict{String,Int}(),
                ),
            ),
            Dict{String,Any}(
                "id" => "fee_reserve_cap_liquidity_floor_fallback",
                "features" => ["deviation_bps", "liquidity_depth_bps", "reserve_bps", "fee_bps"],
                "q_table" => Dict(
                    "2|0|2|3" => Dict("lower_fee_10" => 180),
                    "3|0|2|3" => Dict("lower_fee_10" => 180),
                    "*" => Dict{String,Int}(),
                ),
            ),
            Dict{String,Any}(
                "id" => "funding_floor_liquidity_floor_fallback",
                "features" => ["deviation_bps", "volatility_bps", "liquidity_depth_bps", "funding_cap_bps"],
                "q_table" => Dict(
                    "3|2|0|0" => Dict("raise_fee_10_shift_router_to_reserve_100" => 140),
                    "3|3|0|0" => Dict("raise_fee_10_shift_router_to_reserve_100" => 140),
                    "*" => Dict{String,Int}(),
                ),
            ),
        ],
    )

    report = Dict{String,Any}(
        "schema" => REPORT_SCHEMA,
        "generated_at" => string(Dates.now(Dates.UTC)),
        "ok" => true,
        "state_count" => length(q_table),
        "action_count" => length(ACTIONS),
        "hard_gate_fail_count" => hard_gate_fail_count,
        "objective" => "argmin hard_gate_penalty + target_miss + churn + overcontrol + ebrm_prior",
        "boundary" => "Offline optimizer only; runtime must still evaluate the frozen policy with Python/Tau governance gates.",
        "best_actions" => best_actions,
        "energy_breakdowns" => breakdowns,
        "policy" => policy,
        "non_claims" => [
            "does_not_authorize_settlement",
            "does_not_replace_governance_gates",
            "does_not_train_online",
            "does_not_prove_global_dynamic_optimality",
        ],
    )
    return policy, report
end

function json_escape(s::AbstractString)
    out = IOBuffer()
    for ch in String(s)
        if ch == '"'
            print(out, "\\\"")
        elseif ch == '\\'
            print(out, "\\\\")
        elseif ch == '\n'
            print(out, "\\n")
        elseif ch == '\r'
            print(out, "\\r")
        elseif ch == '\t'
            print(out, "\\t")
        else
            print(out, ch)
        end
    end
    return String(take!(out))
end

function write_json_value(io, value; indent::Int = 0)
    pad = repeat(" ", indent)
    nextpad = repeat(" ", indent + 2)
    if value isa AbstractString
        print(io, "\"$(json_escape(value))\"")
    elseif value isa Bool
        print(io, value ? "true" : "false")
    elseif value isa Integer
        print(io, value)
    elseif value isa AbstractFloat
        isfinite(value) || error("cannot encode non-finite float")
        print(io, value)
    elseif value isa AbstractDict
        print(io, "{")
        keys_sorted = sort(collect(keys(value)), by = string)
        if !isempty(keys_sorted)
            println(io)
            for (idx, key) in enumerate(keys_sorted)
                comma = idx == length(keys_sorted) ? "" : ","
                print(io, nextpad, "\"$(json_escape(string(key)))\": ")
                write_json_value(io, value[key]; indent = indent + 2)
                println(io, comma)
            end
            print(io, pad)
        end
        print(io, "}")
    elseif value isa AbstractVector || value isa Tuple
        print(io, "[")
        if !isempty(value)
            println(io)
            for (idx, item) in enumerate(value)
                comma = idx == length(value) ? "" : ","
                print(io, nextpad)
                write_json_value(io, item; indent = indent + 2)
                println(io, comma)
            end
            print(io, pad)
        end
        print(io, "]")
    elseif value === nothing
        print(io, "null")
    else
        error("unsupported JSON value type: $(typeof(value))")
    end
end

function write_json_file(path::String, value)
    dir = dirname(path)
    if !isempty(dir) && dir != "."
        mkpath(dir)
    end
    open(path, "w") do io
        write_json_value(io, value)
        println(io)
    end
end

function print_text_report(report)
    println("schema = $(report["schema"])")
    println("state_count = $(report["state_count"])")
    println("action_count = $(report["action_count"])")
    println("hard_gate_fail_count = $(report["hard_gate_fail_count"])")
    println("boundary = $(report["boundary"])")
end

function main(args)
    opts, flags = parse_args(args)
    policy, report = optimize_table()

    if haskey(opts, "--policy-output")
        write_json_file(opts["--policy-output"], policy)
    end
    if haskey(opts, "--report-output")
        write_json_file(opts["--report-output"], report)
    end

    if !("--quiet" in flags)
        if "--text" in flags
            print_text_report(report)
        elseif !haskey(opts, "--report-output")
            write_json_value(stdout, report)
            println()
        end
    end
    return 0
end

exit(main(ARGS))
