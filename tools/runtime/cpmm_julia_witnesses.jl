#!/usr/bin/env julia

# Deterministic CPMM arithmetic witnesses.
#
# This script is intentionally dependency-free Julia. It emits JSON by hand so
# the generator can run in a fresh Julia install without package resolution.
# It is an offline witness generator only; it is never imported by runtime code.

const BPS_DENOM = big(10_000)
const DEX_POOL_RESERVE_MAX = big(3_000_000_000)
const U128_MAX = big(2)^128 - 1

ceil_div(n, d) = (n + d - 1) ÷ d

function json_str(s)
    out = IOBuffer()
    print(out, '"')
    for c in s
        if c == '"'
            print(out, "\\\"")
        elseif c == '\\'
            print(out, "\\\\")
        else
            print(out, c)
        end
    end
    print(out, '"')
    return String(take!(out))
end

function pool_json(reserve_in, reserve_out, fee_bps)
    return "{\"initialized\":true,\"reserve0\":$(reserve_in),\"reserve1\":$(reserve_out),\"fee_bps\":$(fee_bps)}"
end

function exact_in_tx_json(amount_in, min_amount_out)
    return "{\"kind\":\"swap_exact_in\",\"zero_for_one\":true,\"amount_in\":$(amount_in),\"min_amount_out\":$(min_amount_out)}"
end

function exact_out_tx_json(amount_out, max_amount_in, max_gap_bps)
    return "{\"kind\":\"swap_exact_out\",\"zero_for_one\":true,\"amount_out\":$(amount_out),\"max_amount_in\":$(max_amount_in),\"max_overdelivery_gap_bps\":$(max_gap_bps)}"
end

function reject_json(reason)
    return "{\"accept\":false,\"reject_reason\":$(json_str(reason))}"
end

function accept_json(receipt_fields, post_pool)
    receipt_parts = String[]
    for (key, value) in receipt_fields
        push!(receipt_parts, "$(json_str(key)):$(value)")
    end
    return "{\"accept\":true,\"receipt\":{$(join(receipt_parts, ","))},\"post_pool\":$(post_pool)}"
end

function case_json(name, op, pool, tx, expect)
    return "{\"name\":$(json_str(name)),\"op\":$(json_str(op)),\"pool\":$(pool),\"tx\":$(tx),\"expect\":$(expect)}"
end

function exact_in_case(name, reserve_in, reserve_out, amount_in, fee_bps; min_amount_out=0)
    r_in = big(reserve_in)
    r_out = big(reserve_out)
    amount = big(amount_in)
    fee = big(fee_bps)
    min_out = big(min_amount_out)
    pool = pool_json(r_in, r_out, fee)
    tx = exact_in_tx_json(amount, min_out)

    new_in = r_in + amount
    if new_in > DEX_POOL_RESERVE_MAX
        return case_json(name, "swap_exact_in", pool, tx, reject_json("reserve_domain_exceeded"))
    end
    fee_total = ceil_div(amount * fee, BPS_DENOM)
    if fee_total >= amount
        return case_json(name, "swap_exact_in", pool, tx, reject_json("trade_too_small"))
    end
    net_in = amount - fee_total
    amount_out = (r_out * net_in) ÷ (r_in + net_in)
    if amount_out == 0
        return case_json(name, "swap_exact_in", pool, tx, reject_json("trade_too_small"))
    end
    if amount_out < min_out
        return case_json(name, "swap_exact_in", pool, tx, reject_json("slippage"))
    end
    new_out = r_out - amount_out
    receipt_fields = [
        ("amount_in", amount),
        ("amount_out", amount_out),
        ("fee_total", fee_total),
        ("amount_out_quote", amount_out),
        ("overdelivery_gap", 0),
        ("gap_bps", 0),
        ("new_reserve0", new_in),
        ("new_reserve1", new_out),
    ]
    post_pool = pool_json(new_in, new_out, fee)
    return case_json(name, "swap_exact_in", pool, tx, accept_json(receipt_fields, post_pool))
end

function exact_out_case(name, reserve_in, reserve_out, amount_out, fee_bps; max_amount_in=U128_MAX, max_gap_bps=10_000)
    r_in = big(reserve_in)
    r_out = big(reserve_out)
    amount = big(amount_out)
    fee = big(fee_bps)
    max_in = big(max_amount_in)
    max_gap = big(max_gap_bps)
    pool = pool_json(r_in, r_out, fee)
    tx = exact_out_tx_json(amount, max_in, max_gap)

    if max_gap > BPS_DENOM
        return case_json(name, "swap_exact_out", pool, tx, reject_json("overdelivery_gap"))
    end
    if amount >= r_out
        return case_json(name, "swap_exact_out", pool, tx, reject_json("amount_out_ge_reserve"))
    end
    if fee > BPS_DENOM
        return case_json(name, "swap_exact_out", pool, tx, reject_json("invalid_fee_bps"))
    end
    if fee == BPS_DENOM
        return case_json(name, "swap_exact_out", pool, tx, reject_json("fee_full"))
    end

    reserve_delta = r_out - amount
    net_in = ceil_div(r_in * amount, reserve_delta)
    gross_in = ceil_div(net_in * BPS_DENOM, BPS_DENOM - fee)
    fee_total = gross_in - net_in
    amount_out_quote = (r_out * net_in) ÷ (r_in + net_in)
    new_in = r_in + gross_in
    if new_in > DEX_POOL_RESERVE_MAX
        return case_json(name, "swap_exact_out", pool, tx, reject_json("reserve_domain_exceeded"))
    end
    overdelivery_gap = max(big(0), amount_out_quote - amount)
    gap_bps = ceil_div(overdelivery_gap * BPS_DENOM, amount)
    if gap_bps > max_gap
        return case_json(name, "swap_exact_out", pool, tx, reject_json("overdelivery_gap"))
    end
    if gross_in > max_in
        return case_json(name, "swap_exact_out", pool, tx, reject_json("slippage"))
    end
    new_out = r_out - amount
    receipt_fields = [
        ("amount_in", gross_in),
        ("amount_out", amount),
        ("fee_total", fee_total),
        ("amount_out_quote", amount_out_quote),
        ("overdelivery_gap", overdelivery_gap),
        ("gap_bps", gap_bps),
        ("new_reserve0", new_in),
        ("new_reserve1", new_out),
    ]
    post_pool = pool_json(new_in, new_out, fee)
    return case_json(name, "swap_exact_out", pool, tx, accept_json(receipt_fields, post_pool))
end

cases = [
    exact_in_case("exact_in_small_floor_accept", 1, 2, 1, 0),
    exact_in_case("exact_in_near_max_accept", 2_999_999_000, 3_000_000_000, 1_000, 30),
    exact_in_case("exact_in_near_max_reserve_domain", 3_000_000_000, 1_000_000, 1, 0),
    exact_in_case("exact_in_fee_full_too_small", 12, 12, 12, 10_000),
    exact_in_case("exact_in_high_fee_one_unit_net_accept", 1, 10_000, 10_000, 9_999),
    exact_in_case("exact_in_slippage_reject", 1_000_000, 1_000_000, 10_000, 30; min_amount_out=20_000),
    exact_out_case("exact_out_small_accept", 1, 2, 1, 0),
    exact_out_case("exact_out_overdelivery_accept_when_gap_open", 1, 4, 1, 30; max_gap_bps=10_000),
    exact_out_case("exact_out_overdelivery_reject_default_gap", 1, 4, 1, 30; max_gap_bps=200),
    exact_out_case("exact_out_near_max_accept", 2_999_998_000, 3_000_000_000, 1, 0),
    exact_out_case("exact_out_near_max_reserve_domain", 3_000_000_000, 3_000_000_000, 1, 0),
    exact_out_case("exact_out_amount_ge_reserve", 1, 10, 10, 0),
    exact_out_case("exact_out_fee_full", 10, 20, 1, 10_000),
    exact_out_case("exact_out_slippage_reject", 1_000_000, 1_000_000, 10_000, 30; max_amount_in=1),
]

println("{\"schema\":\"zenodex.cpmm_julia_witnesses.v1\",\"case_count\":$(length(cases)),\"cases\":[$(join(cases, ","))]}")
