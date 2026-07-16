#!/usr/bin/env julia

# Exact-rational comparison of equal Bernstein subdivision and two adaptive
# region dispatchers. ACCEPT always comes from nonnegative Bernstein
# coefficients on a complete interval cover. Derivative data only chooses
# where the critical-aware compiler subdivides.

const Q = Rational{BigInt}
const ZERO = big(0)//big(1)
const ONE = big(1)//big(1)
const CRITICAL_GRID_DENOMINATOR = BigInt(64)

struct CorpusCase
    case_id::String
    family::String
    parameters::String
    n::Int
    coeffs::Vector{Q}
    expected::String
end

struct Leaf
    lo::Q
    hi::Q
    bcoeffs::Vector{Q}
    min_coeff::Q
    split_local::Q
    critical_hints::Int
end

struct CertificateResult
    accepted::Bool
    pieces::Int
    search_interval_checks::Int
    compiler_scalar_updates::Int
    checker_scalar_reads::Int
    certificate_bytes::Int
    critical_splits::Int
    midpoint_splits::Int
    min_coeff::Q
end

function trim_poly(coeffs::Vector{Q})::Vector{Q}
    out = copy(coeffs)
    while length(out) > 1 && out[end] == ZERO
        pop!(out)
    end
    return out
end

function poly_add(left::Vector{Q}, right::Vector{Q})::Vector{Q}
    out = fill(ZERO, max(length(left), length(right)))
    for index in eachindex(left)
        out[index] += left[index]
    end
    for index in eachindex(right)
        out[index] += right[index]
    end
    return trim_poly(out)
end

function poly_mul(left::Vector{Q}, right::Vector{Q})::Vector{Q}
    out = fill(ZERO, length(left) + length(right) - 1)
    for left_index in eachindex(left)
        for right_index in eachindex(right)
            out[left_index + right_index - 1] += left[left_index] * right[right_index]
        end
    end
    return trim_poly(out)
end

poly_scale(coeffs::Vector{Q}, scale::Q)::Vector{Q} =
    trim_poly([scale * coeff for coeff in coeffs])

function poly_pow(coeffs::Vector{Q}, exponent::Int)::Vector{Q}
    out = Q[ONE]
    for _ in 1:exponent
        out = poly_mul(out, coeffs)
    end
    return out
end

function compose_affine(coeffs::Vector{Q}, lo::Q, hi::Q)::Vector{Q}
    affine = Q[lo, hi - lo]
    out = Q[ZERO]
    power = Q[ONE]
    for coeff in coeffs
        out = poly_add(out, poly_scale(power, coeff))
        power = poly_mul(power, affine)
    end
    return trim_poly(out)
end

binom_int_q(n::Int, k::Int)::Q = BigInt(binomial(big(n), big(k)))//big(1)

function binom_q(value::Q, k::Int)::Q
    out = ONE
    for index in 0:(k - 1)
        out *= value - big(index)//big(1)
    end
    for index in 1:k
        out /= big(index)//big(1)
    end
    return out
end

function bernstein_coeffs_on_unit(power_coeffs::Vector{Q})::Vector{Q}
    degree = length(power_coeffs) - 1
    out = Q[]
    for i in 0:degree
        acc = ZERO
        for j in 0:i
            acc += power_coeffs[j + 1] * binom_int_q(i, j) / binom_int_q(degree, j)
        end
        push!(out, acc)
    end
    return out
end

function split_bernstein(coeffs::Vector{Q}, at::Q)
    @assert ZERO <= at <= ONE
    level = copy(coeffs)
    left = Q[level[1]]
    right = Q[level[end]]
    updates = 0
    while length(level) > 1
        level = Q[(ONE - at) * level[i] + at * level[i + 1] for i in 1:(length(level) - 1)]
        updates += length(level)
        push!(left, level[1])
        push!(right, level[end])
    end
    reverse!(right)
    return left, right, updates
end

function restrict_bernstein(coeffs::Vector{Q}, lo::Q, hi::Q)
    @assert ZERO <= lo < hi <= ONE
    if lo == ZERO && hi == ONE
        return copy(coeffs), 0
    end
    prefix = coeffs
    updates = 0
    if hi < ONE
        prefix, _, split_updates = split_bernstein(prefix, hi)
        updates += split_updates
    end
    if lo == ZERO
        return prefix, updates
    end
    local_lo = lo / hi
    _, restricted, split_updates = split_bernstein(prefix, local_lo)
    return restricted, updates + split_updates
end

function qstr(value::Q)::String
    denominator(value) == 1 && return string(numerator(value))
    return string(numerator(value), "/", denominator(value))
end

function certificate_bytes(leaves::Vector{Leaf})::Int
    total = 0
    for leaf in leaves
        fields = String[qstr(leaf.lo), qstr(leaf.hi)]
        append!(fields, qstr.(leaf.bcoeffs))
        total += ncodeunits(join(fields, '\t')) + 1
    end
    return total
end

function critical_probe(bcoeffs::Vector{Q})
    degree = length(bcoeffs) - 1
    degree <= 1 && return ONE / 2, 0, degree
    derivative = Q[big(degree)//big(1) * (bcoeffs[i + 1] - bcoeffs[i]) for i in 1:degree]
    derivative_degree = length(derivative) - 1
    candidates = Q[]
    if derivative_degree > 0
        for index in eachindex(derivative)
            if derivative[index] == ZERO && 1 < index < length(derivative)
                push!(candidates, big(index - 1)//big(derivative_degree))
            end
        end
        nonzero = findall(!=(ZERO), derivative)
        for pair_index in 1:(length(nonzero) - 1)
            left_index = nonzero[pair_index]
            right_index = nonzero[pair_index + 1]
            left_value = derivative[left_index]
            right_value = derivative[right_index]
            if sign(left_value) != sign(right_value)
                # The sign-change control nodes localize a derivative root. Use
                # their midpoint as a bounded-denominator landmark. Exact
                # coefficient interpolation makes recursive denominators grow
                # with coefficient height and is unsuitable for a bounded
                # certificate compiler.
                numerator_sum = big(left_index + right_index - 2)
                push!(candidates, numerator_sum//big(2 * derivative_degree))
            end
        end
    end
    filter!(candidate -> ZERO < candidate < ONE, candidates)
    isempty(candidates) && return ONE / 2, 0, degree
    sort!(unique!(candidates), by = candidate -> (abs(candidate - ONE / 2), candidate))
    return candidates[1], length(candidates), degree
end

function make_leaf(lo::Q, hi::Q, bcoeffs::Vector{Q}, strategy::Symbol)
    min_coeff = minimum(bcoeffs)
    if min_coeff >= ZERO || strategy == :midpoint
        return Leaf(lo, hi, bcoeffs, min_coeff, ONE / 2, 0), 0
    end
    split_local, hints, probe_updates = critical_probe(bcoeffs)
    return Leaf(lo, hi, bcoeffs, min_coeff, split_local, hints), probe_updates
end

function preferred_failure(leaves::Vector{Leaf}, strategy::Symbol)::Int
    failures = findall(leaf -> leaf.min_coeff < ZERO, leaves)
    best = failures[1]
    for candidate in failures[2:end]
        current = leaves[best]
        challenger = leaves[candidate]
        hint_better = strategy == :critical && challenger.critical_hints > current.critical_hints
        same_hints = strategy != :critical || challenger.critical_hints == current.critical_hints
        coeff_better = same_hints && challenger.min_coeff < current.min_coeff
        same_coeff = challenger.min_coeff == current.min_coeff
        width_better = same_hints && same_coeff && challenger.hi - challenger.lo > current.hi - current.lo
        if hint_better || coeff_better || width_better
            best = candidate
        end
    end
    return best
end

function is_complete_partition(leaves::Vector{Leaf})::Bool
    isempty(leaves) && return false
    leaves[1].lo == ZERO || return false
    leaves[end].hi == ONE || return false
    for index in eachindex(leaves)
        leaves[index].lo < leaves[index].hi || return false
        if index < length(leaves) && leaves[index].hi != leaves[index + 1].lo
            return false
        end
    end
    return true
end

function bounded_critical_split(leaf::Leaf)
    proposed = leaf.lo + leaf.split_local * (leaf.hi - leaf.lo)
    scaled = proposed * CRITICAL_GRID_DENOMINATOR
    quotient, remainder = divrem(numerator(scaled), denominator(scaled))
    nearest = 2 * remainder >= denominator(scaled) ? quotient + 1 : quotient
    first_interior = floor(BigInt, leaf.lo * CRITICAL_GRID_DENOMINATOR) + 1
    last_interior = ceil(BigInt, leaf.hi * CRITICAL_GRID_DENOMINATOR) - 1
    if first_interior > last_interior
        return ONE / 2, false
    end
    grid_index = clamp(nearest, first_interior, last_interior)
    split_global = grid_index//CRITICAL_GRID_DENOMINATOR
    split_local = (split_global - leaf.lo) / (leaf.hi - leaf.lo)
    return split_local, true
end

function result_from_leaves(
    leaves::Vector{Leaf},
    checks::Int,
    updates::Int,
    critical_splits::Int,
    midpoint_splits::Int,
)::CertificateResult
    accepted = is_complete_partition(leaves) && all(leaf -> leaf.min_coeff >= ZERO, leaves)
    reads = accepted ? sum(length(leaf.bcoeffs) for leaf in leaves) : 0
    bytes = accepted ? certificate_bytes(leaves) : 0
    min_coeff = minimum(leaf.min_coeff for leaf in leaves)
    return CertificateResult(
        accepted,
        accepted ? length(leaves) : 0,
        checks,
        updates,
        reads,
        bytes,
        critical_splits,
        midpoint_splits,
        min_coeff,
    )
end

function adaptive_certificate(coeffs::Vector{Q}, max_leaves::Int, strategy::Symbol)
    root_bcoeffs = bernstein_coeffs_on_unit(coeffs)
    root, probe_updates = make_leaf(ZERO, ONE, root_bcoeffs, strategy)
    leaves = Leaf[root]
    checks = 1
    updates = probe_updates
    critical_splits = 0
    midpoint_splits = 0
    while any(leaf -> leaf.min_coeff < ZERO, leaves) && length(leaves) < max_leaves
        selected_index = preferred_failure(leaves, strategy)
        selected = leaves[selected_index]
        split_local, used_critical = if strategy == :critical && selected.critical_hints > 0
            bounded_critical_split(selected)
        else
            (ONE / 2, false)
        end
        left_coeffs, right_coeffs, split_updates = split_bernstein(selected.bcoeffs, split_local)
        split_global = selected.lo + split_local * (selected.hi - selected.lo)
        left, left_probe = make_leaf(selected.lo, split_global, left_coeffs, strategy)
        right, right_probe = make_leaf(split_global, selected.hi, right_coeffs, strategy)
        splice!(leaves, selected_index:selected_index, Leaf[left, right])
        checks += 2
        updates += split_updates + left_probe + right_probe
        if used_critical
            critical_splits += 1
        else
            midpoint_splits += 1
        end
    end
    return result_from_leaves(leaves, checks, updates, critical_splits, midpoint_splits)
end

function equal_certificate(coeffs::Vector{Q}, candidates::Vector{Int})
    root = bernstein_coeffs_on_unit(coeffs)
    checks = 0
    updates = 0
    last_min = minimum(root)
    for pieces in candidates
        leaves = Leaf[]
        accepted = true
        for index in 0:(pieces - 1)
            lo = big(index)//big(pieces)
            hi = big(index + 1)//big(pieces)
            interval_coeffs, interval_updates = restrict_bernstein(root, lo, hi)
            leaf = Leaf(lo, hi, interval_coeffs, minimum(interval_coeffs), ONE / 2, 0)
            push!(leaves, leaf)
            checks += 1
            updates += interval_updates
            last_min = min(last_min, leaf.min_coeff)
            if leaf.min_coeff < ZERO
                accepted = false
                break
            end
        end
        if accepted
            return result_from_leaves(leaves, checks, updates, 0, 0)
        end
    end
    return CertificateResult(false, 0, checks, updates, 0, 0, 0, 0, last_min)
end

include("critical_region_corpus.jl")

function result_fields(result::CertificateResult)::Vector{String}
    return String[
        result.accepted ? "true" : "false",
        string(result.pieces),
        string(result.search_interval_checks),
        string(result.compiler_scalar_updates),
        string(result.checker_scalar_reads),
        string(result.certificate_bytes),
        string(result.critical_splits),
        string(result.midpoint_splits),
        qstr(result.min_coeff),
    ]
end

function emit_case(io, case::CorpusCase, candidates::Vector{Int}, max_leaves::Int)
    equal = equal_certificate(case.coeffs, candidates)
    midpoint = adaptive_certificate(case.coeffs, max_leaves, :midpoint)
    critical = adaptive_certificate(case.coeffs, max_leaves, :critical)
    fields = String[
        case.case_id,
        case.family,
        case.parameters,
        string(case.n),
        string(length(case.coeffs) - 1),
        case.expected,
    ]
    append!(fields, result_fields(equal))
    append!(fields, result_fields(midpoint))
    append!(fields, result_fields(critical))
    println(io, join(fields, '\t'))
end

function main()
    out_path = length(ARGS) >= 1 ? ARGS[1] : "generated/critical_region_dispatch.tsv"
    parity_path = length(ARGS) >= 2 ? ARGS[2] : "generated/critical_region_dispatch_parity.txt"
    mkpath(dirname(out_path))
    parity_checks = backend_parity_checks()
    write(parity_path, "backend_parity_checks=$parity_checks\n")
    cases = CorpusCase[]
    add_positive_cases!(cases)
    add_negative_controls!(cases)
    candidates = Int[1, 2, 4, 8, 16, 32]
    suffixes = ["accepted", "pieces", "search_interval_checks", "compiler_scalar_updates", "checker_scalar_reads", "certificate_bytes", "critical_splits", "midpoint_splits", "min_coeff"]
    header = String["case_id", "family", "parameters", "n", "degree", "expected"]
    for method in ["equal", "midpoint", "critical"]
        append!(header, [method * "_" * suffix for suffix in suffixes])
    end
    open(out_path, "w") do io
        println(io, join(header, '\t'))
        for case in cases
            emit_case(io, case, candidates, 32)
        end
    end
end

main()
