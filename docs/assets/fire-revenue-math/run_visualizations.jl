#!/usr/bin/env julia

const ROOT = normpath(joinpath(@__DIR__, "..", "..", ".."))
const OUT = @__DIR__

readtext(parts...) = read(joinpath(ROOT, parts...), String)

function json_int(text::AbstractString, key::AbstractString)::Int
    m = match(Regex("\"" * key * "\"\\s*:\\s*(-?\\d+)"), text)
    m === nothing && error("missing integer key: $key")
    return parse(Int, m.captures[1])
end

function esc(s::AbstractString)::String
    replace(String(s), "&" => "&amp;", "<" => "&lt;", ">" => "&gt;", "\"" => "&quot;")
end

function write_csv(path::AbstractString, header::Vector{String}, rows)
    open(path, "w") do io
        println(io, join(header, ","))
        for row in rows
            println(io, join(row, ","))
        end
    end
end

function svg_begin(io, width::Int, height::Int)
    println(io, """<svg xmlns="http://www.w3.org/2000/svg" width="$width" height="$height" viewBox="0 0 $width $height">""")
    println(io, """<rect width="100%" height="100%" fill="#fbfaf7"/>""")
    println(io, """<style>
      text { font-family: Inter, ui-sans-serif, system-ui, -apple-system, BlinkMacSystemFont, "Segoe UI", sans-serif; fill: #172026; }
      .title { font-size: 23px; font-weight: 750; }
      .subtitle { font-size: 13px; fill: #52606d; }
      .label { font-size: 12px; fill: #36424d; }
      .value { font-size: 12px; font-weight: 700; fill: #172026; }
      .tiny { font-size: 10px; fill: #61717f; }
      .axis { stroke: #cbd5dd; stroke-width: 1; }
      .grid { stroke: #e3e8ed; stroke-width: 1; }
    </style>""")
end

function svg_end(io)
    println(io, "</svg>")
end

function bar(io; x, y, w, h, fill, label="", value="")
    println(io, """<rect x="$x" y="$y" width="$w" height="$h" rx="3" fill="$fill"/>""")
    if label != ""
        println(io, """<text class="label" x="$(x)" y="$(y + h + 17)">$(esc(label))</text>""")
    end
    if value != ""
        println(io, """<text class="value" x="$(x)" y="$(y - 7)">$(esc(value))</text>""")
    end
end

function stacked_bar(io; x, y, w, h, accepted, rejected, fill_ok="#2f855a", fill_bad="#c2410c")
    total = accepted + rejected
    ok_h = total == 0 ? 0.0 : h * accepted / total
    bad_h = h - ok_h
    if bad_h > 0
        println(io, """<rect x="$x" y="$y" width="$w" height="$bad_h" rx="3" fill="$fill_bad"/>""")
    end
    if ok_h > 0
        println(io, """<rect x="$x" y="$(y + bad_h)" width="$w" height="$ok_h" rx="3" fill="$fill_ok"/>""")
    end
end

function load_reports()
    v190_report = readtext("experiments", "math_object_innovation_v190", "generated", "report.json")
    v190_cal = readtext("experiments", "math_object_innovation_v190", "generated", "receipt_calibration_report.json")
    v190_caps = readtext("experiments", "math_object_innovation_v190", "generated", "fee_cap_recommendations.json")
    v191_report = readtext("experiments", "math_object_innovation_v191", "generated", "report.json")
    v192_report = readtext("experiments", "math_object_innovation_v192", "generated", "report.json")
    return v190_report, v190_cal, v190_caps, v191_report, v192_report
end

function plot_math_ladder()
    v190_report, v190_cal, v190_caps, v191, v192 = load_reports()
    rows = [
        ("Policy candidates", json_int(v190_report, "candidate_policy_count"), "#334155"),
        ("Survivor policies", json_int(v190_report, "survivor_count"), "#0f766e"),
        ("Fixture receipts", json_int(v190_cal, "receipt_count"), "#2563eb"),
        ("Stress receipts", json_int(v191, "receipt_count"), "#7c3aed"),
        ("Execution receipts", json_int(v192, "receipt_count"), "#db2777"),
        ("Execution review caps", json_int(v192, "candidate_review_cap_count"), "#ea580c"),
    ]
    write_csv(joinpath(OUT, "math_ladder.csv"), ["stage", "count"], [(r[1], r[2]) for r in rows])

    width, height = 980, 430
    left, top = 70, 92
    plot_w, plot_h = 840, 235
    max_log = maximum(log10.(Float64[r[2] for r in rows] .+ 1.0))
    open(joinpath(OUT, "math_ladder.svg"), "w") do io
        svg_begin(io, width, height)
        println(io, """<text class="title" x="70" y="42">FIRE Revenue Math Assurance Ladder</text>""")
        println(io, """<text class="subtitle" x="70" y="65">From bounded policy search to execution-derived fee-cap receipts. Bar width uses log10(count + 1).</text>""")
        for (i, (label, value, color)) in enumerate(rows)
            y = top + (i - 1) * 43
            w = round(Int, plot_w * log10(value + 1) / max_log)
            println(io, """<text class="label" x="70" y="$(y + 18)">$(esc(label))</text>""")
            bar(io; x=250, y=y, w=w, h=24, fill=color, value="")
            println(io, """<text class="value" x="$(260 + w)" y="$(y + 17)">$(value)</text>""")
        end
        println(io, """<text class="tiny" x="70" y="382">Interpretation: this is not one proof. It is a ladder of increasingly concrete evidence: search, survivor filtering, receipt guards, stress rows, and real router-derived measurements.</text>""")
        svg_end(io)
    end
end

function plot_receipt_outcomes()
    _, v190_cal, _, v191, v192 = load_reports()
    rows = [
        ("v190 fixture", json_int(v190_cal, "accepted_count"), json_int(v190_cal, "rejected_count")),
        ("v191 stress", json_int(v191, "accepted_count"), json_int(v191, "rejected_count")),
        ("v192 execution", json_int(v192, "accepted_count"), json_int(v192, "rejected_count")),
    ]
    write_csv(joinpath(OUT, "receipt_outcomes.csv"), ["cycle", "accepted", "rejected"], rows)

    width, height = 780, 430
    max_total = maximum([r[2] + r[3] for r in rows])
    open(joinpath(OUT, "receipt_outcomes.svg"), "w") do io
        svg_begin(io, width, height)
        println(io, """<text class="title" x="60" y="42">Receipt Guard Outcomes</text>""")
        println(io, """<text class="subtitle" x="60" y="65">Accepted rows stay green; deliberately bad rows must reject in orange.</text>""")
        base_y = 330
        h_max = 220
        for (i, (label, accepted, rejected)) in enumerate(rows)
            x = 125 + (i - 1) * 205
            h = round(Int, h_max * (accepted + rejected) / max_total)
            y = base_y - h
            stacked_bar(io; x=x, y=y, w=76, h=h, accepted=accepted, rejected=rejected)
            println(io, """<text class="value" x="$(x - 8)" y="$(y - 10)">$(accepted) accepted</text>""")
            println(io, """<text class="value" x="$(x - 8)" y="$(y - 26)">$(rejected) rejected</text>""")
            println(io, """<text class="label" x="$(x - 22)" y="$(base_y + 24)">$(esc(label))</text>""")
        end
        println(io, """<rect x="560" y="100" width="18" height="18" fill="#2f855a"/><text class="label" x="586" y="114">Accepted</text>""")
        println(io, """<rect x="560" y="128" width="18" height="18" fill="#c2410c"/><text class="label" x="586" y="142">Rejected by guard</text>""")
        println(io, """<text class="tiny" x="60" y="386">Interpretation: the calibration layer is becoming an adversarial filter, not just a spreadsheet of fees.</text>""")
        svg_end(io)
    end
end

function plot_execution_value_ranges()
    _, _, _, _, v192 = load_reports()
    rows = [
        ("Route surplus", json_int(v192, "route_improvement_min"), json_int(v192, "route_improvement_max"), "#0f766e"),
        ("Exact-out savings", json_int(v192, "exact_out_savings_min"), json_int(v192, "exact_out_savings_max"), "#7c3aed"),
    ]
    write_csv(joinpath(OUT, "execution_value_ranges.csv"), ["surface", "min", "max"], [(r[1], r[2], r[3]) for r in rows])

    width, height = 820, 360
    left, right = 150, 720
    axis_w = right - left
    max_val = maximum([r[3] for r in rows])
    scale(v) = left + axis_w * v / max_val
    open(joinpath(OUT, "execution_value_ranges.svg"), "w") do io
        svg_begin(io, width, height)
        println(io, """<text class="title" x="60" y="42">Execution-Derived User Value Ranges</text>""")
        println(io, """<text class="subtitle" x="60" y="65">Measured from actual CPMM router improvements in deterministic fixture markets.</text>""")
        println(io, """<line class="axis" x1="$left" y1="260" x2="$right" y2="260"/>""")
        for tick in 0:2000:8000
            x = scale(tick)
            println(io, """<line class="grid" x1="$x" y1="100" x2="$x" y2="260"/>""")
            println(io, """<text class="tiny" x="$(x - 8)" y="282">$tick</text>""")
        end
        for (i, (label, lo, hi, color)) in enumerate(rows)
            y = 125 + (i - 1) * 72
            println(io, """<text class="label" x="60" y="$(y + 5)">$(esc(label))</text>""")
            println(io, """<line x1="$(scale(lo))" y1="$y" x2="$(scale(hi))" y2="$y" stroke="$color" stroke-width="12" stroke-linecap="round"/>""")
            println(io, """<circle cx="$(scale(lo))" cy="$y" r="6" fill="#fbfaf7" stroke="$color" stroke-width="3"/>""")
            println(io, """<circle cx="$(scale(hi))" cy="$y" r="6" fill="$color"/>""")
            println(io, """<text class="value" x="$(scale(lo) - 12)" y="$(y - 18)">$(lo)</text>""")
            println(io, """<text class="value" x="$(scale(hi) - 12)" y="$(y - 18)">$(hi)</text>""")
        end
        println(io, """<text class="tiny" x="60" y="320">Interpretation: v192 now measures value from router behavior, then caps protocol capture against that measured value.</text>""")
        svg_end(io)
    end
end

function plot_review_caps()
    _, _, _, _, v192 = load_reports()
    rows = [
        ("Route surplus", json_int(v192, "route_surplus_capture"), "#0f766e"),
        ("Exact-out savings", json_int(v192, "exact_out_savings_capture"), "#7c3aed"),
    ]
    write_csv(joinpath(OUT, "review_caps.csv"), ["surface", "recommended_cap_bps", "retail_hard_rail_bps"], [(r[1], r[2], 2500) for r in rows])

    width, height = 720, 380
    max_bps = 3000
    base_y = 285
    h_max = 190
    open(joinpath(OUT, "review_caps.svg"), "w") do io
        svg_begin(io, width, height)
        println(io, """<text class="title" x="60" y="42">Review Caps vs Retail Hard Rail</text>""")
        println(io, """<text class="subtitle" x="60" y="65">v192 emits review caps only; no launch-parameter claim is produced.</text>""")
        rail_y = base_y - h_max * 2500 / max_bps
        println(io, """<line x1="100" y1="$rail_y" x2="610" y2="$rail_y" stroke="#dc2626" stroke-width="2" stroke-dasharray="7 6"/>""")
        println(io, """<text class="label" x="485" y="$(rail_y - 8)">2500 bps retail rail</text>""")
        for (i, (label, bps, color)) in enumerate(rows)
            x = 150 + (i - 1) * 230
            h = h_max * bps / max_bps
            y = base_y - h
            bar(io; x=x, y=y, w=95, h=h, fill=color, label=label, value="$(bps) bps")
        end
        println(io, """<text class="tiny" x="60" y="345">Interpretation: recommended caps are bounded by measured user value and clipped by hard retail rails.</text>""")
        svg_end(io)
    end
end

function main()
    plot_math_ladder()
    plot_receipt_outcomes()
    plot_execution_value_ranges()
    plot_review_caps()
    println("wrote FIRE revenue math visualizations to $(OUT)")
end

main()
