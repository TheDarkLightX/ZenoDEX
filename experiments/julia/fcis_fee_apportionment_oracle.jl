#!/usr/bin/env julia

using SHA

const DENOMINATOR = 10_000
const MAX_U256 = big(2)^256 - 1
const ALGORITHM_VERSION = "SUPPORT_RESPECTING_GREEDY_DEFICIT_V1"
const STATE_SCHEMA = "zenodex/fcis/fee-apportionment/committed-state/v2"
const ALLOCATION_SCHEMA = "zenodex/fcis/fee-apportionment/asset-allocation-batch/v2"
const RESULT_SCHEMA = "zenodex/fcis/fee-apportionment/transition-result/v2"

function json_quote(value::String)::String
    output = IOBuffer()
    write(output, UInt8('"'))
    for byte in codeunits(value)
        if byte == 0x22
            write(output, "\\\"")
        elseif byte == 0x5c
            write(output, "\\\\")
        elseif byte == 0x08
            write(output, "\\b")
        elseif byte == 0x09
            write(output, "\\t")
        elseif byte == 0x0a
            write(output, "\\n")
        elseif byte == 0x0c
            write(output, "\\f")
        elseif byte == 0x0d
            write(output, "\\r")
        elseif byte < 0x20
            write(output, "\\u00")
            write(output, string(byte, base=16, pad=2))
        else
            write(output, byte)
        end
    end
    write(output, UInt8('"'))
    return String(take!(output))
end

function hex_bytes(bytes::Vector{UInt8})::String
    return bytes2hex(bytes)
end

function digest(value::String)::String
    return "0x" * hex_bytes(sha256(Vector{UInt8}(codeunits(value))))
end

function csv_values(values)::String
    return join(string.(values), ",")
end

function key_json(domain::String, asset::String)::String
    return "{\"asset\":" * json_quote(asset) *
           ",\"fee_distribution_domain_id\":" * json_quote(domain) * "}"
end

function state_json(
    entries::Vector{Tuple{String,String,Vector{BigInt}}},
)::String
    ordered = sort(entries, by=entry -> (entry[1], entry[2]))
    rendered = [
        "{\"deficit_buyback\":" * string(entry[3][1]) *
        ",\"deficit_treasury\":" * string(entry[3][2]) *
        ",\"key\":" * key_json(entry[1], entry[2]) * "}"
        for entry in ordered
    ]
    return "{\"algorithm_version\":" * json_quote(ALGORITHM_VERSION) *
           ",\"entries\":[" * join(rendered, ",") * "]}"
end

function envelope(schema::String, value::String)::String
    return "{\"schema\":" * json_quote(schema) * ",\"value\":" * value * "}"
end

function allocation_json(
    domain::String,
    asset::String,
    amount::BigInt,
    destinations::Vector{String},
    fractions::Vector{BigInt},
    bonuses::Vector{Int},
    amounts::Vector{BigInt},
    deficits_pre::Vector{BigInt},
    deficits_post::Vector{BigInt},
)::String
    return "{\"amount\":" * string(amount) *
           ",\"buyback_amount\":" * string(amounts[1]) *
           ",\"buyback_bonus\":" * string(bonuses[1]) *
           ",\"buyback_destination\":" * json_quote(destinations[1]) *
           ",\"buyback_fraction\":" * string(fractions[1]) *
           ",\"deficit_buyback_post\":" * string(deficits_post[1]) *
           ",\"deficit_buyback_pre\":" * string(deficits_pre[1]) *
           ",\"deficit_rewards_post\":" * string(deficits_post[3]) *
           ",\"deficit_rewards_pre\":" * string(deficits_pre[3]) *
           ",\"deficit_treasury_post\":" * string(deficits_post[2]) *
           ",\"deficit_treasury_pre\":" * string(deficits_pre[2]) *
           ",\"key\":" * key_json(domain, asset) *
           ",\"rewards_amount\":" * string(amounts[3]) *
           ",\"rewards_bonus\":" * string(bonuses[3]) *
           ",\"rewards_destination\":" * json_quote(destinations[3]) *
           ",\"rewards_fraction\":" * string(fractions[3]) *
           ",\"treasury_amount\":" * string(amounts[2]) *
           ",\"treasury_bonus\":" * string(bonuses[2]) *
           ",\"treasury_destination\":" * json_quote(destinations[2]) *
           ",\"treasury_fraction\":" * string(fractions[2]) * "}"
end

function compute_one(
    amount::BigInt,
    weights::Vector{Int},
    deficits_pre::Vector{BigInt},
    denominator::Int,
)
    quotient = div(amount, denominator)
    residual = mod(amount, denominator)
    bases = BigInt[]
    fractions = BigInt[]
    for weight in weights
        product = residual * weight
        push!(bases, quotient * weight + div(product, denominator))
        push!(fractions, mod(product, denominator))
    end
    seat_count = div(sum(fractions; init=big(0)), denominator)
    eligible = [index for index in 1:3 if fractions[index] > 0]
    order = sort(eligible, by=index -> (-(deficits_pre[index] + fractions[index]), index))
    bonuses = [0, 0, 0]
    for index in order[1:seat_count]
        bonuses[index] = 1
    end
    amounts = [bases[index] + bonuses[index] for index in 1:3]
    deficits_post = [
        deficits_pre[index] + fractions[index] - denominator * bonuses[index]
        for index in 1:3
    ]
    return (:accept, amount, fractions, bonuses, amounts, deficits_pre, deficits_post)
end

function compute_transition(
    amount_values::Vector{BigInt},
    weights::Vector{Int},
    deficits_pre::Vector{BigInt},
    denominator::Int,
)
    amount = sum(amount_values; init=big(0))
    if amount > MAX_U256
        return (:reject, "aggregate_overflow", "")
    end
    return compute_one(amount, weights, deficits_pre, denominator)
end

function production_record(line::AbstractString)::String
    fields = split(line, '\t')
    length(fields) == 8 || error("expected eight tab-separated fields")
    id, domain_field, asset_field = fields[1:3]
    amount_values = [parse(BigInt, value) for value in split(fields[4], ',')]
    domains = String.(split(domain_field, ';'))
    assets = String.(split(asset_field, ';'))
    weights = [parse(Int, value) for value in split(fields[5], ',')]
    destinations = String.(split(fields[6], ','))
    length(domains) == length(amount_values) || error("domain list does not align")
    length(assets) == length(amount_values) || error("asset list does not align")
    length(weights) == 3 || error("production policy must have three roles")
    length(destinations) == 3 || error("production policy must have three roles")
    deficit_buyback = parse(BigInt, fields[7])
    deficit_treasury = parse(BigInt, fields[8])
    pre = [deficit_buyback, deficit_treasury, -deficit_buyback - deficit_treasury]

    grouped = Dict{Tuple{String,String},Vector{BigInt}}()
    for index in eachindex(amount_values)
        key = (domains[index], assets[index])
        push!(get!(grouped, key, BigInt[]), amount_values[index])
    end
    group_keys = sort(collect(keys(grouped)), by=key -> (key[1], key[2]))
    state_deficits = Dict{Tuple{String,String},Vector{BigInt}}()
    if any(value != 0 for value in pre)
        state_deficits[group_keys[1]] = pre
    end
    allocation_values = String[]
    fractions_values = String[]
    bonuses_values = String[]
    amounts_values = String[]
    post_values = String[]
    for key in group_keys
        amount_values_for_key = grouped[key]
        amount = sum(amount_values_for_key; init=big(0))
        if amount > MAX_U256
            return id * "|R|aggregate_overflow|contributions/aggregate/" *
                   key[1] * "/" * key[2]
        end
        exact_pre = get(state_deficits, key, BigInt[0, 0, 0])
        result = compute_one(amount, weights, exact_pre, DENOMINATOR)
        _, _, fractions, bonuses, amounts, _, deficits_post = result
        push!(
            allocation_values,
            allocation_json(
                key[1],
                key[2],
                amount,
                destinations,
                fractions,
                bonuses,
                amounts,
                exact_pre,
                deficits_post,
            ),
        )
        push!(fractions_values, csv_values(fractions))
        push!(bonuses_values, csv_values(bonuses))
        push!(amounts_values, csv_values(amounts))
        push!(post_values, csv_values(deficits_post))
        if any(value != 0 for value in deficits_post)
            state_deficits[key] = deficits_post
        else
            delete!(state_deficits, key)
        end
    end
    state_entries = [
        (key[1], key[2], value)
        for (key, value) in state_deficits
    ]
    state_value = state_json(state_entries)
    allocation_value = "[" * join(allocation_values, ",") * "]"
    result_value = "{\"allocations\":" * allocation_value *
                   ",\"state\":" * state_value * "}"
    state_bytes = envelope(STATE_SCHEMA, state_value)
    allocation_bytes = envelope(ALLOCATION_SCHEMA, allocation_value)
    result_bytes = envelope(RESULT_SCHEMA, result_value)
    return id * "|A|" *
           join(fractions_values, ";") * "|" *
           join(bonuses_values, ";") * "|" *
           join(amounts_values, ";") * "|" *
           join(post_values, ";") * "|" *
           hex_bytes(Vector{UInt8}(codeunits(state_bytes))) * "|" *
           hex_bytes(Vector{UInt8}(codeunits(allocation_bytes))) * "|" *
           hex_bytes(Vector{UInt8}(codeunits(result_bytes))) * "|" *
           digest(result_bytes)
end

function small_record(line::AbstractString)::String
    fields = split(line, '\t')
    length(fields) == 8 || error("expected eight small-domain fields")
    id = fields[1]
    denominator = parse(Int, fields[2])
    amount = parse(BigInt, fields[3])
    weights = [parse(Int, value) for value in split(fields[4], ',')]
    deficits_pre = [
        parse(BigInt, fields[7]),
        parse(BigInt, fields[8]),
        -parse(BigInt, fields[7]) - parse(BigInt, fields[8]),
    ]
    result = compute_transition([amount], weights, deficits_pre, denominator)
    if result[1] == :reject
        return id * "|R|" * result[2] * "|" * result[3]
    end
    _, _, fractions, bonuses, amounts, _, deficits_post = result
    return id * "|A|" *
           csv_values(fractions) * "|" *
           csv_values(bonuses) * "|" *
           csv_values(amounts) * "|" *
           csv_values(deficits_post)
end

function run_file(input_path::String, output_path::String, small::Bool)
    input = read(input_path, String)
    lines = String[]
    for line in split(input, '\n')
        isempty(line) && continue
        push!(lines, small ? small_record(line) : production_record(line))
    end
    output = isempty(lines) ? "" : join(lines, "\n") * "\n"
    write(output_path, output)
end

function main()
    if length(ARGS) == 3 && ARGS[1] == "--small-domain"
        run_file(ARGS[2], ARGS[3], true)
    elseif length(ARGS) == 2
        run_file(ARGS[1], ARGS[2], false)
    else
        error(
            "usage: fcis_fee_apportionment_oracle.jl INPUT.tsv OUTPUT.txt " *
            "or --small-domain INPUT.tsv OUTPUT.txt",
        )
    end
end

main()
