#!/usr/bin/env julia

# Exact Gasper-cone Jacobi Turan orientation scan.

const Q = Rational{BigInt}
const CERT_CACHE = Dict{String,Tuple{Int,Q,Int}}()

function trim_poly(a::Vector{Q})::Vector{Q}
    out = copy(a)
    while length(out) > 1 && out[end] == 0//1
        pop!(out)
    end
    return out
end

function poly_add(a::Vector{Q}, b::Vector{Q})::Vector{Q}
    n = max(length(a), length(b))
    out = fill(big(0)//big(1), n)
    for i in eachindex(a)
        out[i] += a[i]
    end
    for i in eachindex(b)
        out[i] += b[i]
    end
    return trim_poly(out)
end

function poly_mul(a::Vector{Q}, b::Vector{Q})::Vector{Q}
    out = fill(big(0)//big(1), length(a) + length(b) - 1)
    for i in eachindex(a)
        for j in eachindex(b)
            out[i + j - 1] += a[i] * b[j]
        end
    end
    return trim_poly(out)
end

poly_scale(a::Vector{Q}, s::Q)::Vector{Q} = trim_poly([s * x for x in a])

function poly_pow(a::Vector{Q}, n::Int)::Vector{Q}
    out = Q[1//1]
    for _ in 1:n
        out = poly_mul(out, a)
    end
    return out
end

function compose_affine(coeffs::Vector{Q}, lo::Q, hi::Q)::Vector{Q}
    affine = Q[lo, hi - lo]
    out = Q[0//1]
    pow = Q[1//1]
    for coeff in coeffs
        out = poly_add(out, poly_scale(pow, coeff))
        pow = poly_mul(pow, affine)
    end
    return trim_poly(out)
end

function binom_int_q(n::Int, k::Int)::Q
    return BigInt(binomial(big(n), big(k)))//big(1)
end

function binom_q(a::Q, k::Int)::Q
    out = big(1)//big(1)
    for i in 0:(k - 1)
        out *= a - (big(i)//big(1))
    end
    for i in 1:k
        out /= big(i)//big(1)
    end
    return out
end

function bernstein_coeffs_on_unit(power_coeffs::Vector{Q})::Vector{Q}
    degree = length(power_coeffs) - 1
    out = Q[]
    for i in 0:degree
        acc = big(0)//big(1)
        for j in 0:i
            acc += power_coeffs[j + 1] * binom_int_q(i, j) / binom_int_q(degree, j)
        end
        push!(out, acc)
    end
    return out
end

function bernstein_certificate(coeffs::Vector{Q}, pieces::Int)
    global_min = nothing
    fail_piece = -1
    for index in 0:(pieces - 1)
        lo = big(index)//big(pieces)
        hi = big(index + 1)//big(pieces)
        normalized = compose_affine(coeffs, lo, hi)
        bcoeffs = bernstein_coeffs_on_unit(normalized)
        local_min = minimum(bcoeffs)
        if global_min === nothing || local_min < global_min
            global_min = local_min
        end
        if any(x -> x < 0//1, bcoeffs)
            fail_piece = index
            return false, global_min, fail_piece
        end
    end
    return true, global_min, fail_piece
end

function first_certificate_pieces(coeffs::Vector{Q}, candidates::Vector{Int})
    last_min = big(0)//big(1)
    last_fail = -1
    for pieces in candidates
        ok, min_coeff, fail_piece = bernstein_certificate(coeffs, pieces)
        last_min = min_coeff
        last_fail = fail_piece
        if ok
            return pieces, min_coeff, -1
        end
    end
    return 0, last_min, last_fail
end

function eval_at_one(coeffs::Vector{Q})::Q
    acc = big(0)//big(1)
    for coeff in coeffs
        acc += coeff
    end
    return acc
end

function shifted_jacobi(n::Int, alpha::Q, beta::Q)::Vector{Q}
    # Shifted Jacobi expansion:
    # P_n^(alpha,beta)(2x-1) =
    #   sum_s binom(n+alpha,n-s) binom(n+beta,s) (x-1)^s x^(n-s)
    out = Q[0//1]
    x = Q[0//1, 1//1]
    xm1 = Q[-1//1, 1//1]
    for s in 0:n
        coeff = binom_q(big(n)//big(1) + alpha, n - s) *
            binom_q(big(n)//big(1) + beta, s)
        term = poly_scale(poly_mul(poly_pow(xm1, s), poly_pow(x, n - s)), coeff)
        out = poly_add(out, term)
    end
    return trim_poly(out)
end

right_norm(n::Int, alpha::Q)::Q = binom_q(big(n)//big(1) + alpha, n)

function left_norm(n::Int, beta::Q)::Q
    sign = isodd(n) ? -big(1)//big(1) : big(1)//big(1)
    return sign * binom_q(big(n)//big(1) + beta, n)
end

function normalized_jacobi(n::Int, alpha::Q, beta::Q, anchor::String)::Vector{Q}
    p = shifted_jacobi(n, alpha, beta)
    if anchor == "right"
        return poly_scale(p, (big(1)//big(1)) / right_norm(n, alpha))
    elseif anchor == "left"
        return poly_scale(p, (big(1)//big(1)) / left_norm(n, beta))
    end
    error("unknown anchor: " * anchor)
end

function jacobi_turan(n::Int, alpha::Q, beta::Q, anchor::String)::Vector{Q}
    p = normalized_jacobi(n, alpha, beta, anchor)
    pm = normalized_jacobi(n - 1, alpha, beta, anchor)
    pp = normalized_jacobi(n + 1, alpha, beta, anchor)
    return poly_add(poly_mul(p, p), poly_scale(poly_mul(pm, pp), -big(1)//big(1)))
end

function qstr(x::Q)::String
    if denominator(x) == 1
        return string(numerator(x))
    end
    return string(numerator(x), "/", denominator(x))
end

function relation(alpha::Q, beta::Q)::String
    if alpha == beta
        return "alpha_eq_beta"
    elseif beta > alpha
        return "beta_gt_alpha"
    end
    return "alpha_gt_beta"
end

function oriented_anchor(alpha::Q, beta::Q)::String
    return beta >= alpha ? "right" : "left"
end

function wrong_anchor(alpha::Q, beta::Q)::String
    return oriented_anchor(alpha, beta) == "right" ? "left" : "right"
end

function expected_for(anchor::String, alpha::Q, beta::Q)::String
    if anchor == "right"
        return beta >= alpha ? "positive_claim" : "outside_cone"
    elseif anchor == "left"
        return alpha >= beta ? "positive_claim" : "outside_cone"
    elseif anchor == "oriented"
        return "positive_claim"
    elseif anchor == "wrong"
        return alpha == beta ? "positive_claim" : "outside_cone"
    end
    return "negative"
end

function coeffs_for(anchor::String, n::Int, alpha::Q, beta::Q)::Vector{Q}
    if anchor == "oriented"
        return jacobi_turan(n, alpha, beta, oriented_anchor(alpha, beta))
    elseif anchor == "wrong"
        return jacobi_turan(n, alpha, beta, wrong_anchor(alpha, beta))
    end
    return jacobi_turan(n, alpha, beta, anchor)
end

function emit_row(io, family::String, anchor::String, alpha::Q, beta::Q, n::Int, coeffs::Vector{Q}, candidates, expected::String)
    value_at_0 = coeffs[1]
    value_at_1 = eval_at_one(coeffs)
    endpoint_falsified = value_at_0 < 0//1 || value_at_1 < 0//1
    pieces = 0
    min_coeff = min(value_at_0, value_at_1)
    fail_piece = endpoint_falsified ? -2 : -1
    if !(expected != "positive_claim" && endpoint_falsified)
        actual_anchor = anchor == "oriented" ? oriented_anchor(alpha, beta) :
            anchor == "wrong" ? wrong_anchor(alpha, beta) : anchor
        cert_key = join([family, actual_anchor, qstr(alpha), qstr(beta), string(n)], "|")
        if haskey(CERT_CACHE, cert_key)
            pieces, min_coeff, fail_piece = CERT_CACHE[cert_key]
        else
            pieces, min_coeff, fail_piece = first_certificate_pieces(coeffs, candidates)
            CERT_CACHE[cert_key] = (pieces, min_coeff, fail_piece)
        end
    end
    accepted = pieces != 0
    println(
        io,
        join(
            [
                family,
                anchor,
                qstr(alpha),
                qstr(beta),
                relation(alpha, beta),
                string(n),
                string(length(coeffs) - 1),
                string(pieces),
                accepted ? "true" : "false",
                qstr(min_coeff),
                string(fail_piece),
                qstr(value_at_0),
                qstr(value_at_1),
                endpoint_falsified ? "true" : "false",
                expected,
            ],
            '\t',
        ),
    )
end

function main()
    out_path = length(ARGS) >= 1 ? ARGS[1] : "generated/raw.tsv"
    mkpath(dirname(out_path))
    candidates = [1, 2, 4, 8, 16, 32, 64, 128]
    params = Tuple{Q,Q}[
        (big(0)//big(1), big(0)//big(1)),
        (big(1)//big(2), big(0)//big(1)),
        (big(0)//big(1), big(1)//big(2)),
        (big(1)//big(1), big(0)//big(1)),
        (big(0)//big(1), big(1)//big(1)),
        (big(1)//big(1), big(2)//big(1)),
        (big(2)//big(1), big(1)//big(1)),
        (big(1)//big(2), big(3)//big(2)),
        (big(3)//big(2), big(1)//big(2)),
        (big(2)//big(1), big(3)//big(1)),
        (big(3)//big(1), big(2)//big(1)),
        (big(1)//big(1), big(1)//big(1)),
        (big(2)//big(1), big(2)//big(1)),
        (big(1)//big(3), big(2)//big(3)),
        (big(2)//big(3), big(1)//big(3)),
        (big(0)//big(1), big(2)//big(1)),
        (big(2)//big(1), big(0)//big(1)),
        (big(1)//big(2), big(2)//big(1)),
        (big(2)//big(1), big(1)//big(2)),
        (big(3)//big(1), big(5)//big(1)),
        (big(5)//big(1), big(3)//big(1)),
    ]
    open(out_path, "w") do io
        println(io, "family\tanchor\talpha\tbeta\trelation\tn\tdegree\tbest_pieces\taccepted\tmin_coeff\tfail_piece\tvalue_at_0\tvalue_at_1\tendpoint_falsified\texpected")
        for (alpha, beta) in params
            for n in 1:18
                for anchor in ["right", "left", "oriented", "wrong"]
                    if anchor == "wrong" && alpha == beta
                        continue
                    end
                    coeffs = coeffs_for(anchor, n, alpha, beta)
                    emit_row(io, "jacobi_turan_gasper_cone", anchor, alpha, beta, n, coeffs, candidates, expected_for(anchor, alpha, beta))
                end
            end
        end
        emit_row(io, "negative_constant", "none", big(0)//big(1), big(0)//big(1), 0, Q[-1//1], candidates, "negative")
        emit_row(io, "crosses_zero", "none", big(0)//big(1), big(0)//big(1), 0, Q[-1//2, 1//1], candidates, "negative")
        emit_row(io, "negative_oriented_turan_alpha1_beta2_n4", "oriented", big(1)//big(1), big(2)//big(1), 4, poly_scale(coeffs_for("oriented", 4, big(1)//big(1), big(2)//big(1)), -big(1)//big(1)), candidates, "negative")
        emit_row(io, "negative_oriented_turan_alpha2_beta1_n5", "oriented", big(2)//big(1), big(1)//big(1), 5, poly_scale(coeffs_for("oriented", 5, big(2)//big(1), big(1)//big(1)), -big(1)//big(1)), candidates, "negative")
    end
end

main()
