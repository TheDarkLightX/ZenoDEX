#!/usr/bin/env julia

# Build a dependency-free hard-negative curriculum summary for ZenoEnergy.
#
# This intentionally avoids Julia package dependencies. It reads the committed
# stress receipt with small structural extractors tailored to the deterministic
# JSON emitted by the ZenoEnergy tools.

using Dates
using Printf

function parse_args(args)
    opts = Dict{String,String}()
    i = 1
    while i <= length(args)
        key = args[i]
        if startswith(key, "--")
            if i == length(args)
                error("missing value for $(key)")
            end
            opts[key] = args[i + 1]
            i += 2
        else
            error("unexpected argument: $(key)")
        end
    end
    return opts
end

function extract_int(text::String, key::String)
    pattern = Regex("\"$(key)\"\\s*:\\s*([0-9]+)")
    m = match(pattern, text)
    m === nothing && error("missing integer key: $(key)")
    return parse(Int, m.captures[1])
end

function extract_bool(text::String, key::String)
    pattern = Regex("\"$(key)\"\\s*:\\s*(true|false)")
    m = match(pattern, text)
    m === nothing && error("missing bool key: $(key)")
    return m.captures[1] == "true"
end

function object_body_after_key(text::String, key::String)
    anchor = "\"$(key)\""
    start_anchor = findfirst(anchor, text)
    start_anchor === nothing && error("missing object key: $(key)")
    colon = findnext(':', text, last(start_anchor) + 1)
    colon === nothing && error("missing colon after object key: $(key)")
    open_brace = findnext('{', text, colon + 1)
    open_brace === nothing && error("missing object body for key: $(key)")
    depth = 0
    for idx in open_brace:lastindex(text)
        char = text[idx]
        if char == '{'
            depth += 1
        elseif char == '}'
            depth -= 1
            if depth == 0
                return text[(open_brace + 1):(idx - 1)]
            end
        end
    end
    error("unterminated object for key: $(key)")
end

function extract_int_map(text::String, key::String)
    body = object_body_after_key(text, key)
    out = Dict{String,Int}()
    for m in eachmatch(Regex("\"([^\"]+)\"\\s*:\\s*([0-9]+)"), body)
        out[m.captures[1]] = parse(Int, m.captures[2])
    end
    isempty(out) && error("empty integer map for key: $(key)")
    return out
end

function sorted_pairs(d::Dict{String,Int})
    return sort(collect(d), by = x -> x[1])
end

function curriculum_weights(histogram::Dict{String,Int})
    max_count = maximum(values(histogram))
    weights = Dict{String,Float64}()
    for (name, count) in histogram
        raw = sqrt(max_count / max(1, count))
        weights[name] = clamp(raw, 1.0, 4.0)
    end
    return weights
end

function bounded_epiplexity_proxy(
    histogram::Dict{String,Int};
    total_cases::Int,
    with_disqualifiers_ok::Int,
    without_disqualifiers_ok::Int,
)
    label_total = sum(values(histogram))
    label_entropy = 0.0
    for count in values(histogram)
        p = count / max(1, label_total)
        if p > 0.0
            label_entropy -= p * log2(p)
        end
    end
    label_count = length(histogram)
    max_label_entropy = label_count <= 1 ? 0.0 : log2(label_count)
    normalized_label_entropy =
        max_label_entropy <= 0.0 ? 0.0 : clamp(label_entropy / max_label_entropy, 0.0, 1.0)
    with_rate = with_disqualifiers_ok / max(1, total_cases)
    without_rate = without_disqualifiers_ok / max(1, total_cases)
    policy_separation = clamp(abs(with_rate - without_rate), 0.0, 1.0)
    min_count = minimum(values(histogram))
    max_count = maximum(values(histogram))
    rare_label_headroom = max_count <= 0 ? 0.0 : clamp((max_count - min_count) / max_count, 0.0, 1.0)
    score = clamp(normalized_label_entropy * policy_separation, 0.0, 1.0)
    classification =
        score == 0.0 ? "unmeasurable_or_saturated" :
        score < 0.05 ? "weak_bounded_structure" :
        "measurable_bounded_structure"
    return Dict{String,Any}(
        "schema" => "zenodex/energy/bounded_epiplexity_proxy/v1",
        "score" => score,
        "classification" => classification,
        "label_entropy_bits" => label_entropy,
        "max_label_entropy_bits" => max_label_entropy,
        "normalized_label_entropy" => normalized_label_entropy,
        "policy_separation" => policy_separation,
        "rare_label_headroom" => rare_label_headroom,
        "with_disqualifiers_ok_rate" => with_rate,
        "without_disqualifiers_ok_rate" => without_rate,
        "boundary" => "Diagnostic proxy only; it is not a correctness certificate and does not prove model accuracy, grid completeness, or production readiness.",
    )
end

function json_escape(s::AbstractString)
    return replace(String(s), "\\" => "\\\\", "\"" => "\\\"", "\n" => "\\n")
end

function json_map_int(io, d::Dict{String,Int}; indent = "    ")
    println(io, "{")
    pairs = sorted_pairs(d)
    for (idx, (key, value)) in enumerate(pairs)
        comma = idx == length(pairs) ? "" : ","
        println(io, "$(indent)\"$(json_escape(key))\": $(value)$(comma)")
    end
    print(io, "  }")
end

function json_map_float(io, d::Dict{String,Float64}; indent = "    ")
    println(io, "{")
    pairs = sort(collect(d), by = x -> x[1])
    for (idx, (key, value)) in enumerate(pairs)
        comma = idx == length(pairs) ? "" : ","
        println(io, "$(indent)\"$(json_escape(key))\": $(@sprintf("%.6f", value))$(comma)")
    end
    print(io, "  }")
end

function json_epiplexity_proxy(io, proxy::Dict{String,Any}; indent = "    ")
    println(io, "{")
    ordered = [
        "schema",
        "score",
        "classification",
        "label_entropy_bits",
        "max_label_entropy_bits",
        "normalized_label_entropy",
        "policy_separation",
        "rare_label_headroom",
        "with_disqualifiers_ok_rate",
        "without_disqualifiers_ok_rate",
        "boundary",
    ]
    for (idx, key) in enumerate(ordered)
        comma = idx == length(ordered) ? "" : ","
        value = proxy[key]
        if value isa AbstractString
            println(io, "$(indent)\"$(key)\": \"$(json_escape(value))\"$(comma)")
        elseif value isa Float64
            println(io, "$(indent)\"$(key)\": $(@sprintf("%.6f", value))$(comma)")
        else
            println(io, "$(indent)\"$(key)\": $(value)$(comma)")
        end
    end
    print(io, "  }")
end

function write_json(path, report)
    open(path, "w") do io
        println(io, "{")
        println(io, "  \"schema\": \"zenodex/energy/negative_curriculum/v1\",")
        println(io, "  \"generated_at\": \"$(json_escape(report[:generated_at]))\",")
        println(io, "  \"source_report\": \"$(json_escape(report[:source_report]))\",")
        println(io, "  \"source_schema\": \"$(json_escape(report[:source_schema]))\",")
        println(io, "  \"ok\": $(report[:ok] ? "true" : "false"),")
        println(io, "  \"evaluated_batches\": $(report[:evaluated_batches]),")
        println(io, "  \"family_count\": $(report[:family_count]),")
        println(io, "  \"total_cases\": $(report[:total_cases]),")
        println(io, "  \"adversary_invalid_count\": $(report[:adversary_invalid_count]),")
        println(io, "  \"adversary_disqualified_count\": $(report[:adversary_disqualified_count]),")
        println(io, "  \"with_disqualifiers_certificate_ok_count\": $(report[:with_disqualifiers_certificate_ok_count]),")
        println(io, "  \"without_disqualifiers_certificate_ok_count\": $(report[:without_disqualifiers_certificate_ok_count]),")
        println(io, "  \"high_declared_output_forced_fail_count\": $(report[:high_declared_output_forced_fail_count]),")
        print(io, "  \"family_case_counts\": ")
        json_map_int(io, report[:family_case_counts])
        println(io, ",")
        print(io, "  \"disqualifier_histogram\": ")
        json_map_int(io, report[:disqualifier_histogram])
        println(io, ",")
        print(io, "  \"recommended_disqualifier_sample_weights\": ")
        json_map_float(io, report[:weights])
        println(io, ",")
        print(io, "  \"bounded_epiplexity_proxy\": ")
        json_epiplexity_proxy(io, report[:bounded_epiplexity_proxy])
        println(io, ",")
        println(io, "  \"recommendations\": [")
        for (idx, item) in enumerate(report[:recommendations])
            comma = idx == length(report[:recommendations]) ? "" : ","
            println(io, "    \"$(json_escape(item))\"$(comma)")
        end
        println(io, "  ],")
        println(io, "  \"negative_knowledge\": [")
        for (idx, item) in enumerate(report[:negative_knowledge])
            comma = idx == length(report[:negative_knowledge]) ? "" : ","
            println(io, "    \"$(json_escape(item))\"$(comma)")
        end
        println(io, "  ]")
        println(io, "}")
    end
end

function write_markdown(path, report)
    open(path, "w") do io
        println(io, "# ZenoEnergy Negative Curriculum")
        println(io)
        println(io, "This Julia-generated receipt turns recorded negative knowledge into sampling guidance for the next advisory ranker.")
        println(io)
        println(io, "```text")
        println(io, "source_report: $(report[:source_report])")
        println(io, "evaluated_batches: $(report[:evaluated_batches])")
        println(io, "family_count: $(report[:family_count])")
        println(io, "total_cases: $(report[:total_cases])")
        println(io, "with_disqualifiers_certificate_ok_count: $(report[:with_disqualifiers_certificate_ok_count])")
        println(io, "without_disqualifiers_certificate_ok_count: $(report[:without_disqualifiers_certificate_ok_count])")
        println(io, "```")
        println(io)
        proxy = report[:bounded_epiplexity_proxy]
        println(io, "## Bounded Epiplexity Proxy")
        println(io)
        println(io, "```text")
        println(io, "schema: $(proxy["schema"])")
        println(io, "classification: $(proxy["classification"])")
        println(io, "score: $(@sprintf("%.6f", proxy["score"]))")
        println(io, "label_entropy_bits: $(@sprintf("%.6f", proxy["label_entropy_bits"]))")
        println(io, "normalized_label_entropy: $(@sprintf("%.6f", proxy["normalized_label_entropy"]))")
        println(io, "policy_separation: $(@sprintf("%.6f", proxy["policy_separation"]))")
        println(io, "rare_label_headroom: $(@sprintf("%.6f", proxy["rare_label_headroom"]))")
        println(io, "```")
        println(io)
        println(io, "$(proxy["boundary"])")
        println(io)
        println(io, "## Curriculum Weights")
        println(io)
        println(io, "| disqualifier | count | sample weight |")
        println(io, "| --- | ---: | ---: |")
        for (name, count) in sorted_pairs(report[:disqualifier_histogram])
            println(io, "| `$(name)` | $(count) | $(@sprintf("%.3f", report[:weights][name])) |")
        end
        println(io)
        println(io, "## Recommendations")
        println(io)
        for item in report[:recommendations]
            println(io, "- $(item)")
        end
        println(io)
        println(io, "## Negative Knowledge")
        println(io)
        for item in report[:negative_knowledge]
            println(io, "- $(item)")
        end
        println(io)
        println(io, "## Academic Hooks")
        println(io)
        println(io, "- LeCun's EBM framing supports discriminative energy ranking over structured outputs, where inference compares candidate energies and chooses low-energy configurations: https://cs.nyu.edu/~yann/research/ebm/")
        println(io, "- Song and Kingma's EBM training survey argues that full likelihood training faces an unknown normalizing constant and often needs MCMC, score matching, or NCE; ZenoEnergy should keep ranking and contrastive losses for v0: https://arxiv.org/abs/2101.03288")
        println(io, "- Learned branch-and-bound work trains policies from strong solver rules and graph/state features; the ZenoEnergy analogue is verifier-imitation with deterministic fallback and no model authority: https://arxiv.org/abs/1906.01629")
        println(io, "- Graph pointer branching adds top-k imitation losses over solver decisions; the ZenoEnergy analogue is top-k verifier-call reduction with checked suffix certificates: https://arxiv.org/abs/2307.01434")
    end
end

function main()
    opts = parse_args(ARGS)
    input_path = get(opts, "--input", "data/upba_energy/upba_v2_suffix_bound_adversarial_family_stress_seed20260545.json")
    output_json = get(opts, "--output-json", "data/upba_energy/zenoenergy_negative_curriculum_seed20260545.json")
    output_markdown = get(opts, "--output-markdown", "docs/ZENO_ENERGY_NEGATIVE_CURRICULUM.md")
    text = read(input_path, String)
    family_counts = extract_int_map(text, "family_case_counts")
    histogram = extract_int_map(text, "disqualifier_histogram")
    weights = curriculum_weights(histogram)
    total_cases = extract_int(text, "total_cases")
    with_disqualifiers_ok = extract_int(text, "with_disqualifiers_certificate_ok_count")
    without_disqualifiers_ok = extract_int(text, "without_disqualifiers_certificate_ok_count")
    epiplexity_proxy = bounded_epiplexity_proxy(
        histogram;
        total_cases = total_cases,
        with_disqualifiers_ok = with_disqualifiers_ok,
        without_disqualifiers_ok = without_disqualifiers_ok,
    )
    report = Dict{Symbol,Any}(
        :generated_at => string(Dates.now(UTC)),
        :source_report => input_path,
        :source_schema => "zenodex/energy/upba_v2_suffix_bound_adversarial_family_stress/v1",
        :ok => extract_bool(text, "ok"),
        :evaluated_batches => extract_int(text, "evaluated_batches"),
        :family_count => extract_int(text, "family_count"),
        :total_cases => total_cases,
        :adversary_invalid_count => extract_int(text, "adversary_invalid_count"),
        :adversary_disqualified_count => extract_int(text, "adversary_disqualified_count"),
        :with_disqualifiers_certificate_ok_count => with_disqualifiers_ok,
        :without_disqualifiers_certificate_ok_count => without_disqualifiers_ok,
        :high_declared_output_forced_fail_count => extract_int(text, "high_declared_output_forced_fail_count"),
        :family_case_counts => family_counts,
        :disqualifier_histogram => histogram,
        :weights => weights,
        :bounded_epiplexity_proxy => epiplexity_proxy,
        :recommendations => [
            "Oversample rare deterministic disqualifiers during candidate generation, especially output_mismatch_count.",
            "Use the bounded epiplexity proxy as a pre-training data-quality check; measurable structure means the corpus has label diversity and policy separation worth training against.",
            "Keep the current gap-weighted linear ranker as the default until a curriculum-trained model beats it on cross-seed mean verifier calls.",
            "Train advisory scorers with pairwise or listwise contrastive losses over verifier-labeled candidates instead of generative EBM likelihood.",
            "Use Julia for bounded adversarial-family search and feature-coverage sweeps, then replay all proposed candidates through the Python verifier.",
            "Treat hard-negative mining as model-training data only; deterministic verifier and suffix certificates remain the safety boundary.",
        ],
        :negative_knowledge => [
            "Epiplexity telemetry is a steering signal, not a correctness certificate.",
            "Declared-output-only suffix bounds are insufficient for attractive invalid candidates.",
            "Multi-family adversarial stress does not prove v2 bounded-grid completeness.",
            "Synthetic hard negatives can improve training coverage, but real replay is still required before production-adjacent promotion.",
        ],
    )
    mkpath(dirname(output_json))
    mkpath(dirname(output_markdown))
    write_json(output_json, report)
    write_markdown(output_markdown, report)
    println("wrote $(output_json)")
    println("wrote $(output_markdown)")
end

main()
