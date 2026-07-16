# Exact Gegenbauer/Jacobi corpus shared by the region-dispatch comparison.

function gegenbauer_coeffs(n::Int, lambda::Q)::Vector{Q}
    n == 0 && return Q[ONE]
    n == 1 && return Q[ZERO, 2 * lambda]
    previous = Q[ONE]
    current = Q[ZERO, 2 * lambda]
    for k in 1:(n - 1)
        factor = big(k)//big(1)
        next = poly_add(
            poly_scale(poly_mul(Q[ZERO, ONE], current), 2 * (factor + lambda)),
            poly_scale(previous, -(factor + 2 * lambda - ONE)),
        )
        previous, current = current, poly_scale(next, ONE / big(k + 1))
    end
    return current
end

function normalized_gegenbauer(n::Int, lambda::Q)::Vector{Q}
    raw = gegenbauer_coeffs(n, lambda)
    norm = sum(raw)
    return poly_scale(compose_affine(raw, -ONE, ONE), ONE / norm)
end

function gegenbauer_envelope(n::Int, lambda::Q)::Vector{Q}
    polynomial = normalized_gegenbauer(n, lambda)
    return poly_add(Q[ONE], poly_scale(poly_mul(polynomial, polynomial), -ONE))
end

function gegenbauer_turan(n::Int, lambda::Q)::Vector{Q}
    polynomial = normalized_gegenbauer(n, lambda)
    previous = normalized_gegenbauer(n - 1, lambda)
    next = normalized_gegenbauer(n + 1, lambda)
    return poly_add(poly_mul(polynomial, polynomial), poly_scale(poly_mul(previous, next), -ONE))
end

function shifted_jacobi(n::Int, alpha::Q, beta::Q)::Vector{Q}
    out = Q[ZERO]
    x = Q[ZERO, ONE]
    x_minus_one = Q[-ONE, ONE]
    for s in 0:n
        coeff = binom_q(big(n)//big(1) + alpha, n - s) * binom_q(big(n)//big(1) + beta, s)
        term = poly_mul(poly_pow(x_minus_one, s), poly_pow(x, n - s))
        out = poly_add(out, poly_scale(term, coeff))
    end
    return trim_poly(out)
end

function max_normalized_jacobi(n::Int, alpha::Q, beta::Q)::Vector{Q}
    right = abs(binom_q(big(n)//big(1) + alpha, n))
    left = abs(binom_q(big(n)//big(1) + beta, n))
    return poly_scale(shifted_jacobi(n, alpha, beta), ONE / max(left, right))
end

function jacobi_envelope(n::Int, alpha::Q, beta::Q)::Vector{Q}
    polynomial = max_normalized_jacobi(n, alpha, beta)
    return poly_add(Q[ONE], poly_scale(poly_mul(polynomial, polynomial), -ONE))
end

function endpoint_normalized_jacobi(n::Int, alpha::Q, beta::Q, anchor::Symbol)::Vector{Q}
    norm = if anchor == :right
        binom_q(big(n)//big(1) + alpha, n)
    else
        (isodd(n) ? -ONE : ONE) * binom_q(big(n)//big(1) + beta, n)
    end
    return poly_scale(shifted_jacobi(n, alpha, beta), ONE / norm)
end

function oriented_jacobi_turan(n::Int, alpha::Q, beta::Q)::Vector{Q}
    anchor = beta >= alpha ? :right : :left
    polynomial = endpoint_normalized_jacobi(n, alpha, beta, anchor)
    previous = endpoint_normalized_jacobi(n - 1, alpha, beta, anchor)
    next = endpoint_normalized_jacobi(n + 1, alpha, beta, anchor)
    return poly_add(poly_mul(polynomial, polynomial), poly_scale(poly_mul(previous, next), -ONE))
end

function add_positive_cases!(cases::Vector{CorpusCase})
    lambdas = Q[1//2, 1//1, 3//2, 2//1, 3//1]
    for lambda in lambdas, n in 1:24
        parameter = "lambda=" * qstr(lambda)
        push!(cases, CorpusCase("gegenbauer_envelope_$(qstr(lambda))_$n", "gegenbauer_envelope", parameter, n, gegenbauer_envelope(n, lambda), "positive"))
        push!(cases, CorpusCase("gegenbauer_turan_$(qstr(lambda))_$n", "gegenbauer_turan", parameter, n, gegenbauer_turan(n, lambda), "positive"))
    end
    jacobi_params = Tuple{Q,Q}[
        (0//1, 0//1), (1//2, 0//1), (0//1, 1//2), (1//1, 0//1),
        (0//1, 1//1), (1//1, 2//1), (2//1, 1//1), (1//2, 3//2),
        (3//2, 1//2), (2//1, 3//1), (3//1, 2//1),
    ]
    for (alpha, beta) in jacobi_params, n in 1:14
        parameter = "alpha=$(qstr(alpha)),beta=$(qstr(beta))"
        push!(cases, CorpusCase("jacobi_envelope_$(qstr(alpha))_$(qstr(beta))_$n", "jacobi_envelope", parameter, n, jacobi_envelope(n, alpha, beta), "positive"))
    end
    oriented_params = Tuple{Q,Q}[
        (0//1, 0//1), (1//2, 0//1), (0//1, 1//2), (1//1, 0//1),
        (0//1, 1//1), (1//1, 2//1), (2//1, 1//1), (1//2, 3//2),
        (3//2, 1//2), (2//1, 3//1), (3//1, 2//1), (1//1, 1//1),
        (2//1, 2//1), (1//3, 2//3), (2//3, 1//3), (0//1, 2//1),
        (2//1, 0//1), (1//2, 2//1), (2//1, 1//2), (3//1, 5//1),
        (5//1, 3//1),
    ]
    for (alpha, beta) in oriented_params, n in 1:18
        parameter = "alpha=$(qstr(alpha)),beta=$(qstr(beta))"
        push!(cases, CorpusCase("oriented_jacobi_turan_$(qstr(alpha))_$(qstr(beta))_$n", "oriented_jacobi_turan", parameter, n, oriented_jacobi_turan(n, alpha, beta), "positive"))
    end
end

function add_negative_controls!(cases::Vector{CorpusCase})
    controls = CorpusCase[
        CorpusCase("negative_constant", "negative_constant", "none", 0, Q[-ONE], "negative"),
        CorpusCase("crosses_zero", "crosses_zero", "none", 0, Q[-ONE / 2, ONE], "negative"),
        CorpusCase("interior_negative_bowl", "interior_negative_bowl", "none", 0, Q[3//16, -ONE, ONE], "negative"),
        CorpusCase("negative_gegenbauer_envelope", "negative_gegenbauer_envelope", "lambda=2", 4, poly_scale(gegenbauer_envelope(4, Q(2)), -ONE), "negative"),
        CorpusCase("negative_gegenbauer_turan", "negative_gegenbauer_turan", "lambda=3/2", 5, poly_scale(gegenbauer_turan(5, big(3)//big(2)), -ONE), "negative"),
        CorpusCase("negative_jacobi_envelope", "negative_jacobi_envelope", "alpha=1,beta=2", 4, poly_scale(jacobi_envelope(4, Q(1), Q(2)), -ONE), "negative"),
        CorpusCase("negative_oriented_jacobi_turan", "negative_oriented_jacobi_turan", "alpha=1,beta=2", 4, poly_scale(oriented_jacobi_turan(4, Q(1), Q(2)), -ONE), "negative"),
    ]
    append!(cases, controls)
end

function backend_parity_checks()::Int
    samples = Vector{Q}[
        Q[1//3, -2//1, 5//2, 1//1],
        Q[ZERO, ONE],
        gegenbauer_envelope(4, big(3)//big(2)),
        jacobi_envelope(3, big(1)//big(2), big(3)//big(2)),
    ]
    intervals = Tuple{Q,Q}[(ZERO, ONE / 2), (ONE / 3, 2 * ONE / 3), (ONE / 2, ONE)]
    checks = 0
    for coeffs in samples, (lo, hi) in intervals
        root = bernstein_coeffs_on_unit(coeffs)
        restricted, _ = restrict_bernstein(root, lo, hi)
        reference = bernstein_coeffs_on_unit(compose_affine(coeffs, lo, hi))
        restricted == reference || error("de Casteljau/reference mismatch")
        checks += 1
    end
    return checks
end
