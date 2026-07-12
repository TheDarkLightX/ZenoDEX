#!/usr/bin/env julia

# Independent deterministic replay of the Python partial-liquidation corpus.
# This file intentionally re-expresses the integer arithmetic rather than
# importing generated Python output as executable semantics.

using SHA

const SCHEMA = "zenodex/perp-partial-liquidation-semantics/v1"
const PRICE_SCALE = 100_000_000
const BPS_SCALE = 10_000
const EXPECTED_COLUMNS = [
    "case_id",
    "position_base",
    "collateral_after_pnl",
    "settle_price_e8",
    "maintenance_margin_bps",
    "depeg_buffer_bps",
    "liquidation_penalty_bps",
    "min_notional_for_bounty",
    "liquidatable",
    "selected_fraction_bps",
]

notional_quote(position_base::Int, price_e8::Int)::Int =
    abs(position_base) * price_e8 ÷ PRICE_SCALE

margin_requirement(notional::Int, margin_bps::Int)::Int =
    notional * margin_bps ÷ BPS_SCALE

maint_margin_req(
    position_base::Int,
    price_e8::Int,
    maintenance_margin_bps::Int,
    depeg_buffer_bps::Int,
)::Int = margin_requirement(
    notional_quote(position_base, price_e8),
    maintenance_margin_bps + depeg_buffer_bps,
)

is_liquidatable(
    position_base::Int,
    collateral_after_pnl::Int,
    settle_price_e8::Int,
    maintenance_margin_bps::Int,
    depeg_buffer_bps::Int,
)::Bool = position_base != 0 && collateral_after_pnl < maint_margin_req(
    position_base,
    settle_price_e8,
    maintenance_margin_bps,
    depeg_buffer_bps,
)

partial_close_base(position_abs::Int, fraction_bps::Int)::Int =
    position_abs * fraction_bps ÷ BPS_SCALE

function remaining_position_signed(position_base::Int, fraction_bps::Int)::Int
    fraction_bps >= BPS_SCALE && return 0
    fraction_bps <= 0 && return position_base
    remaining_abs = abs(position_base) - partial_close_base(abs(position_base), fraction_bps)
    return position_base >= 0 ? remaining_abs : -remaining_abs
end

function liquidation_penalty(
    position_base::Int,
    settle_price_e8::Int,
    liquidation_penalty_bps::Int,
    min_notional_for_bounty::Int,
)::Int
    notional = notional_quote(position_base, settle_price_e8)
    notional < min_notional_for_bounty && return 0
    return margin_requirement(notional, liquidation_penalty_bps)
end

function partial_liquidation_penalty(
    position_base::Int,
    fraction_bps::Int,
    settle_price_e8::Int,
    liquidation_penalty_bps::Int,
    min_notional_for_bounty::Int,
)::Int
    if fraction_bps >= BPS_SCALE
        return liquidation_penalty(
            position_base,
            settle_price_e8,
            liquidation_penalty_bps,
            min_notional_for_bounty,
        )
    end
    closed = partial_close_base(abs(position_base), fraction_bps)
    closed == 0 && return 0
    return liquidation_penalty(
        closed,
        settle_price_e8,
        liquidation_penalty_bps,
        min_notional_for_bounty,
    )
end

function sufficient_after_partial_close(
    position_base::Int,
    collateral_after_pnl::Int,
    fraction_bps::Int,
    settle_price_e8::Int,
    maintenance_margin_bps::Int,
    depeg_buffer_bps::Int,
    liquidation_penalty_bps::Int,
    min_notional_for_bounty::Int,
)::Bool
    remaining = remaining_position_signed(position_base, fraction_bps)
    raw_penalty = partial_liquidation_penalty(
        position_base,
        fraction_bps,
        settle_price_e8,
        liquidation_penalty_bps,
        min_notional_for_bounty,
    )
    penalty = min(max(collateral_after_pnl, 0), raw_penalty)
    collateral_after = collateral_after_pnl - penalty
    remaining == 0 && return true
    requirement = maint_margin_req(
        remaining,
        settle_price_e8,
        maintenance_margin_bps,
        depeg_buffer_bps,
    )
    return collateral_after >= requirement
end

function compute_partial_close_fraction(
    position_base::Int,
    collateral_after_pnl::Int,
    settle_price_e8::Int,
    maintenance_margin_bps::Int,
    depeg_buffer_bps::Int,
    liquidation_penalty_bps::Int,
    min_notional_for_bounty::Int,
)::Int
    if !is_liquidatable(
        position_base,
        collateral_after_pnl,
        settle_price_e8,
        maintenance_margin_bps,
        depeg_buffer_bps,
    )
        return 0
    end
    for fraction_bps in 1:(BPS_SCALE - 1)
        if sufficient_after_partial_close(
            position_base,
            collateral_after_pnl,
            fraction_bps,
            settle_price_e8,
            maintenance_margin_bps,
            depeg_buffer_bps,
            liquidation_penalty_bps,
            min_notional_for_bounty,
        )
            return fraction_bps
        end
    end
    return BPS_SCALE
end

function json_escape(value::AbstractString)::String
    return replace(replace(value, "\\" => "\\\\"), "\"" => "\\\"")
end

function emit_report(ok::Bool, case_count::Int, corpus_sha256::String, errors::Vector{String})
    rendered_errors = join(["\"$(json_escape(error))\"" for error in errors], ",")
    print("{\"backend\":\"julia\",\"case_count\":$(case_count),")
    print("\"corpus_sha256\":\"$(corpus_sha256)\",\"errors\":[$(rendered_errors)],")
    println("\"ok\":$(ok ? "true" : "false"),\"schema\":\"$(SCHEMA)\"}")
end

function main()::Int
    if isempty(ARGS) || length(ARGS) > 2
        println(stderr, "usage: julia tools/perp_partial_liquidation_semantics_v1.jl CORPUS [EXPECTED_SHA256]")
        return 2
    end
    corpus_path = ARGS[1]
    expected_sha256 = length(ARGS) == 2 ? ARGS[2] : nothing
    if !isfile(corpus_path)
        emit_report(false, 0, "", ["corpus file is missing"])
        return 1
    end

    payload = read(corpus_path)
    corpus_sha256 = bytes2hex(sha256(payload))
    errors = String[]
    if expected_sha256 !== nothing && corpus_sha256 != expected_sha256
        push!(errors, "corpus sha256 mismatch")
    end
    lines = split(String(payload), '\n'; keepempty=false)
    if length(lines) < 2 || lines[1] != "# schema=$(SCHEMA)"
        push!(errors, "schema header mismatch")
    end
    if length(lines) < 2 || split(lines[2], '\t') != EXPECTED_COLUMNS
        push!(errors, "column header mismatch")
    end

    case_count = 0
    if length(lines) >= 2
        for line in lines[3:end]
            fields = split(line, '\t')
            if length(fields) != length(EXPECTED_COLUMNS)
                push!(errors, "case $(case_count): expected $(length(EXPECTED_COLUMNS)) fields")
                continue
            end
            values = try
                parse.(Int, fields)
            catch
                push!(errors, "case $(case_count): non-integer field")
                continue
            end
            case_id, position_base, collateral_after_pnl, settle_price_e8,
                maintenance_margin_bps, depeg_buffer_bps, liquidation_penalty_bps,
                min_notional_for_bounty, expected_liquidatable, expected_fraction = values
            if case_id != case_count
                push!(errors, "case id mismatch at row $(case_count)")
            end
            actual_liquidatable = is_liquidatable(
                position_base,
                collateral_after_pnl,
                settle_price_e8,
                maintenance_margin_bps,
                depeg_buffer_bps,
            )
            actual_fraction = compute_partial_close_fraction(
                position_base,
                collateral_after_pnl,
                settle_price_e8,
                maintenance_margin_bps,
                depeg_buffer_bps,
                liquidation_penalty_bps,
                min_notional_for_bounty,
            )
            if Int(actual_liquidatable) != expected_liquidatable
                push!(errors, "case $(case_id): liquidatable mismatch")
            end
            if actual_fraction != expected_fraction
                push!(errors, "case $(case_id): selected fraction mismatch")
            end
            case_count += 1
            length(errors) >= 20 && break
        end
    end
    ok = isempty(errors)
    emit_report(ok, case_count, corpus_sha256, errors)
    return ok ? 0 : 1
end

exit(main())
