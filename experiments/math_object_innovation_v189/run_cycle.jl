#!/usr/bin/env julia

# Exact endpoint-obstruction formula for oriented Jacobi Turan recognizers.

const Q = Rational{BigInt}

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

c(n::Int, gamma::Q)::Q = binom_q(big(n)//big(1) + gamma, n)

function right_direct_left_endpoint(n::Int, alpha::Q, beta::Q)::Q
    r(k) = c(k, beta) / c(k, alpha)
    return r(n)^2 - r(n - 1) * r(n + 1)
end

function right_closed_left_endpoint(n::Int, alpha::Q, beta::Q)::Q
    r = c(n, beta) / c(n, alpha)
    return r^2 * (beta - alpha) / ((big(n)//big(1) + alpha + 1//1) * (big(n)//big(1) + beta))
end

function left_direct_right_endpoint(n::Int, alpha::Q, beta::Q)::Q
    s(k) = c(k, alpha) / c(k, beta)
    return s(n)^2 - s(n - 1) * s(n + 1)
end

function left_closed_right_endpoint(n::Int, alpha::Q, beta::Q)::Q
    s = c(n, alpha) / c(n, beta)
    return s^2 * (alpha - beta) / ((big(n)//big(1) + beta + 1//1) * (big(n)//big(1) + alpha))
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

function sign_name(x::Q)::String
    if x < 0//1
        return "negative"
    elseif x > 0//1
        return "positive"
    end
    return "zero"
end

function emit(io, anchor::String, alpha::Q, beta::Q, n::Int)
    if anchor == "right"
        direct = right_direct_left_endpoint(n, alpha, beta)
        closed = right_closed_left_endpoint(n, alpha, beta)
        endpoint = "x=0"
        cone_ok = beta >= alpha
    else
        direct = left_direct_right_endpoint(n, alpha, beta)
        closed = left_closed_right_endpoint(n, alpha, beta)
        endpoint = "x=1"
        cone_ok = alpha >= beta
    end
    println(
        io,
        join(
            [
                anchor,
                endpoint,
                qstr(alpha),
                qstr(beta),
                relation(alpha, beta),
                string(n),
                qstr(direct),
                qstr(closed),
                direct == closed ? "true" : "false",
                sign_name(direct),
                cone_ok ? "true" : "false",
            ],
            '\t',
        ),
    )
end

function main()
    out_path = length(ARGS) >= 1 ? ARGS[1] : "generated/raw.tsv"
    mkpath(dirname(out_path))
    values = Q[
        big(0)//big(1),
        big(1)//big(3),
        big(1)//big(2),
        big(2)//big(3),
        big(1)//big(1),
        big(3)//big(2),
        big(2)//big(1),
        big(3)//big(1),
        big(5)//big(1),
    ]
    open(out_path, "w") do io
        println(io, "anchor\tendpoint\talpha\tbeta\trelation\tn\tdirect\tclosed\tformula_match\tsign\tcone_ok")
        for alpha in values
            for beta in values
                for n in 1:64
                    emit(io, "right", alpha, beta, n)
                    emit(io, "left", alpha, beta, n)
                end
            end
        end
    end
end

main()
