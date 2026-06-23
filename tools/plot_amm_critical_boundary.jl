#!/usr/bin/env julia

# Generate paper/blog-ready SVG figures for the AMM power-family critical
# boundary at alpha = 2/3.
#
# The script intentionally avoids plotting-package dependencies. It uses
# BigFloat arithmetic for the numerical surface and writes deterministic SVGs.

using Printf

const ROOT = abspath(joinpath(@__DIR__, ".."))
const OUT_DIR = joinpath(ROOT, "docs", "assets", "amm-critical-boundary")

const COEFF = BigFloat(-179) / BigFloat(1536)
const CRITICAL_FACTOR_POLY_HIGH_TO_LOW = BigInt[
    24, 48, 72, 96, 120, 144, 168, 193, 302, 411, 520, 629, 742, 855, 968,
    1045, 642, 239, -164, -567, -954, -1341, -1728, -2349, -5346, -8343,
    -11340, -14337, -17406, -20475, -23544, -18873, -16146, -13419, -10692,
    -7965, -5670, -3375, -1080, -2160, -1620, -1080, -540,
]

bf(x::Integer)::BigFloat = BigFloat(x)
bf(x::AbstractFloat)::BigFloat = parse(BigFloat, @sprintf("%.18e", x))
bf(x::AbstractString)::BigFloat = parse(BigFloat, x)

function sech_sq(d::BigFloat)::BigFloat
    return inv(cosh(d)^2)
end

function critical_factor_poly(a::BigFloat)::BigFloat
    out = BigFloat(0)
    for coeff in CRITICAL_FACTOR_POLY_HIGH_TO_LOW
        out = out * a + BigFloat(coeff)
    end
    return out
end

function critical_factor_model(a::BigFloat)::BigFloat
    return -((a - 1)^2 * critical_factor_poly(a)) /
        (BigFloat(96) * (a^8 - 5) * (a^8 + 3)^3)
end

function critical_from_d_factorized(d::BigFloat)::BigFloat
    w = sech_sq(d)
    a = w^(BigFloat(1) / BigFloat(8))
    return critical_factor_model(a)
end

function cpmm_global_curvature_from_sech_sq(w::BigFloat)::BigFloat
    return sqrt(w) * (2 * w - 1) / 8
end

function power_family_global_curvature_poly(alpha::BigFloat, w::BigFloat)::BigFloat
    return alpha^4 * w^3 +
        8 * alpha^3 * w^2 -
        4 * alpha^2 * w^2 +
        44 * alpha^2 * w -
        16 * alpha^2 -
        16 * alpha * w^2 +
        80 * alpha * w -
        32 * alpha +
        32 * w -
        16
end

function power_family_global_curvature_from_sech_sq(alpha::BigFloat, w::BigFloat)::BigFloat
    return w^((alpha + 1) / (alpha + 2)) *
        (alpha^2 * w + 4 * alpha + 4) *
        power_family_global_curvature_poly(alpha, w) /
        (16 * (alpha + 2) * (alpha * w + 2)^3 *
            (2 * alpha + 2 - alpha * w))
end

function normalized_curvature_from_w(alpha::BigFloat, w::BigFloat)::BigFloat
    return power_family_global_curvature_from_sech_sq(alpha, w) -
        cpmm_global_curvature_from_sech_sq(w) -
        alpha / 16
end

function normalized_delta(alpha::BigFloat, d::BigFloat)::BigFloat
    if abs(alpha - BigFloat(2) / BigFloat(3)) < BigFloat("1e-70")
        return critical_from_d_factorized(d)
    end
    return normalized_curvature_from_w(alpha, sech_sq(d))
end

function html_escape(s::AbstractString)::String
    return replace(String(s), "&" => "&amp;", "<" => "&lt;", ">" => "&gt;", "\"" => "&quot;")
end

function fmt(x; digits::Int = 6)::String
    return @sprintf("%.*g", digits, Float64(x))
end

function palette(name::String)::String
    colors = Dict(
        "ink" => "#111827",
        "muted" => "#4b5563",
        "grid" => "#d1d5db",
        "axis" => "#374151",
        "blue" => "#2563eb",
        "green" => "#059669",
        "red" => "#dc2626",
        "orange" => "#ea580c",
        "purple" => "#7c3aed",
        "paper" => "#ffffff",
    )
    return colors[name]
end

struct PlotSpec
    width::Int
    height::Int
    left::Int
    right::Int
    top::Int
    bottom::Int
end

const SPEC = PlotSpec(1080, 720, 92, 38, 76, 92)

function plot_width(spec::PlotSpec)::Float64
    return Float64(spec.width - spec.left - spec.right)
end

function plot_height(spec::PlotSpec)::Float64
    return Float64(spec.height - spec.top - spec.bottom)
end

function write_svg(path::String, title::String, subtitle::String, body::String)
    mkpath(dirname(path))
    open(path, "w") do io
        println(io, """<svg xmlns="http://www.w3.org/2000/svg" width="$(SPEC.width)" height="$(SPEC.height)" viewBox="0 0 $(SPEC.width) $(SPEC.height)" role="img" aria-label="$(html_escape(title))">""")
        println(io, "<title>$(html_escape(title))</title>")
        println(io, "<desc>$(html_escape(subtitle))</desc>")
        println(io, """<rect width="100%" height="100%" fill="$(palette("paper"))"/>""")
        println(io, """<text x="$(SPEC.left)" y="34" font-family="Inter, Arial, sans-serif" font-size="24" font-weight="700" fill="$(palette("ink"))">$(html_escape(title))</text>""")
        println(io, """<text x="$(SPEC.left)" y="58" font-family="Inter, Arial, sans-serif" font-size="14" fill="$(palette("muted"))">$(html_escape(subtitle))</text>""")
        println(io, body)
        println(io, "</svg>")
    end
end

function axes_svg(spec::PlotSpec, x_ticks, y_ticks, xmap, ymap; xlabel::String, ylabel::String)::String
    parts = String[]
    x0 = spec.left
    x1 = spec.width - spec.right
    y0 = spec.height - spec.bottom
    y1 = spec.top
    push!(parts, """<line x1="$x0" y1="$y0" x2="$x1" y2="$y0" stroke="$(palette("axis"))" stroke-width="1.5"/>""")
    push!(parts, """<line x1="$x0" y1="$y0" x2="$x0" y2="$y1" stroke="$(palette("axis"))" stroke-width="1.5"/>""")
    for (value, label) in x_ticks
        x = xmap(value)
        push!(parts, """<line x1="$x" y1="$y0" x2="$x" y2="$y1" stroke="$(palette("grid"))" stroke-width="1" opacity="0.65"/>""")
        push!(parts, """<text x="$x" y="$(y0 + 28)" text-anchor="middle" font-family="Inter, Arial, sans-serif" font-size="12" fill="$(palette("muted"))">$(html_escape(label))</text>""")
    end
    for (value, label) in y_ticks
        y = ymap(value)
        push!(parts, """<line x1="$x0" y1="$y" x2="$x1" y2="$y" stroke="$(palette("grid"))" stroke-width="1" opacity="0.65"/>""")
        push!(parts, """<text x="$(x0 - 12)" y="$(y + 4)" text-anchor="end" font-family="Inter, Arial, sans-serif" font-size="12" fill="$(palette("muted"))">$(html_escape(label))</text>""")
    end
    push!(parts, """<text x="$((x0 + x1) / 2)" y="$(spec.height - 30)" text-anchor="middle" font-family="Inter, Arial, sans-serif" font-size="14" fill="$(palette("ink"))">$(html_escape(xlabel))</text>""")
    push!(parts, """<text transform="translate(28 $((y0 + y1) / 2)) rotate(-90)" text-anchor="middle" font-family="Inter, Arial, sans-serif" font-size="14" fill="$(palette("ink"))">$(html_escape(ylabel))</text>""")
    return join(parts, "\n")
end

function polyline(points, color::String; width::Real = 3, dash::String = "")::String
    pts = join([@sprintf("%.3f,%.3f", x, y) for (x, y) in points], " ")
    dash_attr = isempty(dash) ? "" : " stroke-dasharray=\"$dash\""
    return """<polyline points="$pts" fill="none" stroke="$color" stroke-width="$width" stroke-linejoin="round" stroke-linecap="round"$dash_attr/>"""
end

function legend_svg(items; x::Int = 720, y::Int = 92)::String
    parts = String[]
    for (idx, (label, color, dash)) in enumerate(items)
        yy = y + 24 * (idx - 1)
        dash_attr = isempty(dash) ? "" : " stroke-dasharray=\"$dash\""
        push!(parts, """<line x1="$x" y1="$yy" x2="$(x + 30)" y2="$yy" stroke="$color" stroke-width="3"$dash_attr/>""")
        push!(parts, """<text x="$(x + 40)" y="$(yy + 5)" font-family="Inter, Arial, sans-serif" font-size="13" fill="$(palette("ink"))">$(html_escape(label))</text>""")
    end
    return join(parts, "\n")
end

function linspace(a::Float64, b::Float64, n::Int)::Vector{Float64}
    if n == 1
        return [a]
    end
    return [a + (b - a) * (i - 1) / (n - 1) for i in 1:n]
end

function logspace(a::Float64, b::Float64, n::Int)::Vector{Float64}
    return [10.0^x for x in linspace(a, b, n)]
end

function save_csv(path::String, header::Vector{String}, rows)
    mkpath(dirname(path))
    open(path, "w") do io
        println(io, join(header, ","))
        for row in rows
            println(io, join(row, ","))
        end
    end
end

function figure_quartic_convergence()
    ds = logspace(-4.5, -0.2, 140)
    rows = []
    ratios = Float64[]
    setprecision(256) do
        for d0 in ds
            d = bf(d0)
            ratio = critical_from_d_factorized(d) / d^4
            push!(ratios, Float64(ratio))
            push!(rows, (fmt(d0; digits=10), fmt(ratio; digits=12), fmt(COEFF; digits=12)))
        end
    end
    save_csv(joinpath(OUT_DIR, "quartic_convergence.csv"), ["d", "delta_over_d4", "limit"], rows)

    xmin, xmax = log10(minimum(ds)), log10(maximum(ds))
    ymin = min(minimum(ratios), Float64(COEFF)) - 0.004
    ymax = max(maximum(ratios), Float64(COEFF)) + 0.004
    xmap(x) = SPEC.left + (x - xmin) / (xmax - xmin) * plot_width(SPEC)
    ymap(y) = SPEC.top + (ymax - y) / (ymax - ymin) * plot_height(SPEC)
    pts = [(xmap(log10(ds[i])), ymap(ratios[i])) for i in eachindex(ds)]
    limit_line = [(xmap(xmin), ymap(Float64(COEFF))), (xmap(xmax), ymap(Float64(COEFF)))]
    x_ticks = [(-4.0, "1e-4"), (-3.0, "1e-3"), (-2.0, "1e-2"), (-1.0, "1e-1")]
    y_ticks = [(round(y; digits=3), @sprintf("%.3f", y)) for y in linspace(ymin, ymax, 6)]
    body = axes_svg(SPEC, x_ticks, y_ticks, xmap, ymap, xlabel="log10(|d|)", ylabel="ΔCurv_norm(2/3,d) / d^4")
    body *= "\n" * polyline(limit_line, palette("red"); width=2, dash="8 7")
    body *= "\n" * polyline(pts, palette("blue"); width=3)
    body *= "\n" * legend_svg([
        ("computed quotient", palette("blue"), ""),
        ("Lean-proved limit -179/1536", palette("red"), "8 7"),
    ])
    write_svg(
        joinpath(OUT_DIR, "quartic_convergence.svg"),
        "Critical boundary quartic coefficient",
        "At alpha = 2/3, the quotient ΔCurv_norm(2/3,d)/d^4 converges to -179/1536.",
        body,
    )
end

function figure_quadratic_vs_quartic()
    ds = linspace(0.012, 0.82, 160)
    alphas = [
        (BigFloat(1) / BigFloat(2), "alpha = 1/2", palette("green")),
        (BigFloat(2) / BigFloat(3), "alpha = 2/3", palette("blue")),
        (BigFloat(4) / BigFloat(5), "alpha = 4/5", palette("orange")),
    ]
    series = []
    rows = []
    setprecision(256) do
        for (alpha, label, color) in alphas
            vals = Float64[]
            for d0 in ds
                d = bf(d0)
                v = normalized_delta(alpha, d) / d^2
                push!(vals, Float64(v))
                push!(rows, (fmt(d0; digits=10), label, fmt(v; digits=12)))
            end
            push!(series, (label, color, vals))
        end
    end
    save_csv(joinpath(OUT_DIR, "quadratic_regimes.csv"), ["d", "alpha_label", "delta_over_d2"], rows)

    ymin = minimum(v for (_, _, vals) in series for v in vals)
    ymax = maximum(v for (_, _, vals) in series for v in vals)
    pad = 0.08 * (ymax - ymin)
    ymin -= pad
    ymax += pad
    xmap(x) = SPEC.left + (x - minimum(ds)) / (maximum(ds) - minimum(ds)) * plot_width(SPEC)
    ymap(y) = SPEC.top + (ymax - y) / (ymax - ymin) * plot_height(SPEC)
    x_ticks = [(0.0, "0"), (0.2, "0.2"), (0.4, "0.4"), (0.6, "0.6"), (0.8, "0.8")]
    y_ticks = [(y, @sprintf("%.3f", y)) for y in linspace(ymin, ymax, 7)]
    body = axes_svg(SPEC, x_ticks, y_ticks, xmap, ymap, xlabel="imbalance coordinate d", ylabel="ΔCurv_norm(alpha,d) / d^2")
    for (label, color, vals) in series
        pts = [(xmap(ds[i]), ymap(vals[i])) for i in eachindex(ds)]
        body *= "\n" * polyline(pts, color; width=3)
    end
    zero_line = [(xmap(minimum(ds)), ymap(0.0)), (xmap(maximum(ds)), ymap(0.0))]
    body *= "\n" * polyline(zero_line, palette("axis"); width=1.5, dash="5 6")
    body *= "\n" * legend_svg([(label, color, "") for (label, color, _) in series])
    write_svg(
        joinpath(OUT_DIR, "quadratic_regime_comparison.svg"),
        "Quadratic term fails exactly at alpha = 2/3",
        "Below the boundary the quadratic-normalized curvature is positive; above it is negative; at the boundary it collapses toward zero.",
        body,
    )
end

function figure_loglog_order()
    ds = logspace(-4.2, -0.65, 130)
    xs = Float64[]
    ys = Float64[]
    rows = []
    setprecision(256) do
        for d0 in ds
            d = bf(d0)
            delta = abs(critical_from_d_factorized(d))
            push!(xs, log10(d0))
            push!(ys, log10(Float64(delta)))
            push!(rows, (fmt(d0; digits=10), fmt(delta; digits=12), fmt(log10(Float64(delta)); digits=12)))
        end
    end
    save_csv(joinpath(OUT_DIR, "loglog_quartic_order.csv"), ["d", "abs_delta", "log10_abs_delta"], rows)

    xmin, xmax = minimum(xs), maximum(xs)
    ymin, ymax = minimum(ys), maximum(ys)
    pad = 0.08 * (ymax - ymin)
    ymin -= pad
    ymax += pad
    xmap(x) = SPEC.left + (x - xmin) / (xmax - xmin) * plot_width(SPEC)
    ymap(y) = SPEC.top + (ymax - y) / (ymax - ymin) * plot_height(SPEC)
    pts = [(xmap(xs[i]), ymap(ys[i])) for i in eachindex(xs)]

    x0 = xs[20]
    y0 = ys[20]
    ref = [(xmap(x), ymap(y0 + 4 * (x - x0))) for x in (xmin, xmax)]
    x_ticks = [(-4.0, "-4"), (-3.0, "-3"), (-2.0, "-2"), (-1.0, "-1")]
    y_ticks = [(round(y; digits=1), @sprintf("%.1f", y)) for y in linspace(ymin, ymax, 7)]
    body = axes_svg(SPEC, x_ticks, y_ticks, xmap, ymap, xlabel="log10(|d|)", ylabel="log10(|ΔCurv_norm(2/3,d)|)")
    body *= "\n" * polyline(pts, palette("purple"); width=3)
    body *= "\n" * polyline(ref, palette("red"); width=2, dash="8 7")
    body *= "\n" * legend_svg([
        ("computed |ΔCurv|", palette("purple"), ""),
        ("slope 4 reference", palette("red"), "8 7"),
    ])
    write_svg(
        joinpath(OUT_DIR, "loglog_quartic_order.svg"),
        "Log-log order check",
        "The boundary curve tracks a slope-four reference line, visualizing quartic order.",
        body,
    )
end

function diverging_color(x::Float64)::String
    # Clamp a signed score into a quiet red/blue diverging palette.
    t = tanh(55.0 * x)
    if abs(t) < 0.035
        return "#f3f4f6"
    elseif t > 0
        k = min(1.0, t)
        r = round(Int, 239 - 165 * k)
        g = round(Int, 246 - 128 * k)
        b = round(Int, 255 - 73 * k)
        return @sprintf("#%02x%02x%02x", r, g, b)
    else
        k = min(1.0, -t)
        r = round(Int, 254 - 69 * k)
        g = round(Int, 242 - 122 * k)
        b = round(Int, 242 - 122 * k)
        return @sprintf("#%02x%02x%02x", r, g, b)
    end
end

function figure_regime_heatmap()
    alphas = linspace(0.32, 1.04, 73)
    ds = linspace(0.025, 0.82, 70)
    cell_w = plot_width(SPEC) / length(alphas)
    cell_h = plot_height(SPEC) / length(ds)
    rows = []
    rects = String[]
    xmap(x) = SPEC.left + (x - minimum(alphas)) / (maximum(alphas) - minimum(alphas)) * plot_width(SPEC)
    ymap(y) = SPEC.top + (maximum(ds) - y) / (maximum(ds) - minimum(ds)) * plot_height(SPEC)
    setprecision(256) do
        for (i, alpha0) in enumerate(alphas), (j, d0) in enumerate(ds)
            alpha = bf(alpha0)
            d = bf(d0)
            score = Float64(normalized_delta(alpha, d) / d^2)
            x = SPEC.left + (i - 1) * cell_w
            y = SPEC.top + (length(ds) - j) * cell_h
            push!(rects, """<rect x="$(round(x; digits=3))" y="$(round(y; digits=3))" width="$(ceil(cell_w + 0.5))" height="$(ceil(cell_h + 0.5))" fill="$(diverging_color(score))"/>""")
            if i % 6 == 1 && j % 6 == 1
                push!(rows, (fmt(alpha0; digits=8), fmt(d0; digits=8), fmt(score; digits=12)))
            end
        end
    end
    save_csv(joinpath(OUT_DIR, "regime_heatmap_sample.csv"), ["alpha", "d", "delta_over_d2"], rows)
    x_ticks = [(0.4, "0.4"), (0.5, "0.5"), (2 / 3, "2/3"), (0.8, "0.8"), (1.0, "1.0")]
    y_ticks = [(0.1, "0.1"), (0.3, "0.3"), (0.5, "0.5"), (0.7, "0.7")]
    body = join(rects, "\n")
    body *= "\n" * axes_svg(SPEC, x_ticks, y_ticks, xmap, ymap, xlabel="power-family parameter alpha", ylabel="imbalance coordinate d")
    xb = xmap(2 / 3)
    body *= "\n" * """<line x1="$xb" y1="$(SPEC.top)" x2="$xb" y2="$(SPEC.height - SPEC.bottom)" stroke="$(palette("ink"))" stroke-width="2.2" stroke-dasharray="7 6"/>"""
    body *= "\n" * """<text x="$(xb + 10)" y="$(SPEC.top + 22)" font-family="Inter, Arial, sans-serif" font-size="13" fill="$(palette("ink"))">alpha = 2/3</text>"""
    body *= "\n" * """<text x="$(SPEC.left + 18)" y="$(SPEC.top + 24)" font-family="Inter, Arial, sans-serif" font-size="13" fill="$(palette("blue"))">positive</text>"""
    body *= "\n" * """<text x="$(SPEC.width - SPEC.right - 86)" y="$(SPEC.top + 24)" font-family="Inter, Arial, sans-serif" font-size="13" fill="$(palette("red"))">negative</text>"""
    write_svg(
        joinpath(OUT_DIR, "regime_heatmap.svg"),
        "Power-family curvature regime map",
        "Color shows the sign and magnitude of ΔCurv_norm(alpha,d)/d^2; the dashed line marks the proved boundary alpha = 2/3.",
        body,
    )
end

function write_readme()
    path = joinpath(OUT_DIR, "README.md")
    mkpath(dirname(path))
    open(path, "w") do io
        println(io, "# AMM Critical Boundary Figures")
        println(io)
        println(io, "Generated by:")
        println(io)
        println(io, "```bash")
        println(io, "julia tools/plot_amm_critical_boundary.jl")
        println(io, "```")
        println(io)
        println(io, "Figures:")
        println(io)
        println(io, "- `quartic_convergence.svg`: shows `DeltaCurv_norm(2/3,d) / d^4` converging to the Lean-proved coefficient `-179/1536`.")
        println(io, "- `quadratic_regime_comparison.svg`: shows why the quadratic diagnostic fails exactly at `alpha = 2/3`.")
        println(io, "- `loglog_quartic_order.svg`: shows the slope-four behavior in log-log coordinates.")
        println(io, "- `regime_heatmap.svg`: shows the sign regime around the `alpha = 2/3` boundary.")
        println(io)
        println(io, "The SVGs are publication-friendly vector graphics. The CSV files beside them are the sampled data used to draw the figures.")
        println(io)
        println(io, "Proof boundary: these figures are explanatory. The coefficient itself is proved in the isolated Lean packet:")
        println(io)
        println(io, "```text")
        println(io, "experiments/math_object_innovation_v183/aristotle_critical_boundary_factor_v4/")
        println(io, "theorem criticalFromD_div_four_tendsto")
        println(io, "```")
    end
end

function main()
    mkpath(OUT_DIR)
    setprecision(256) do
        figure_quartic_convergence()
        figure_quadratic_vs_quartic()
        figure_loglog_order()
        figure_regime_heatmap()
    end
    write_readme()
    println("wrote figures to $(relpath(OUT_DIR, ROOT))")
end

main()
