# Independent finite oracle for the Tree–Chord–Gate authority filtration.
# Uses only Julia Base and prints deterministic JSON for CI comparison.

struct State
    stage::Int
    receipt_mask::UInt16
    lineage_mask::UInt16
    lineage_conflict::Bool
    artifact_coherent::Bool
end

const GATE_COUNT = 9
const MAX_DEPTH = 10
const MUTATIONS = (
    :none,
    :stage_skip,
    :fake_gate,
    :lineage_without_gate,
    :lineage_conflict,
    :artifact_chord_mismatch,
)

function safe(state::State)::Bool
    0 <= state.stage <= GATE_COUNT || return false
    state.lineage_conflict && return false
    state.artifact_coherent || return false
    crossed = UInt16((1 << state.stage) - 1)
    (state.receipt_mask & crossed) == crossed || return false
    (state.lineage_mask & crossed) == crossed || return false
    (state.lineage_mask & ~state.receipt_mask) == 0 || return false
    return true
end

function successors(state::State, mutation::Symbol)
    output = Tuple{String,State}[("same_stage", state)]
    if state.stage < GATE_COUNT
        bit = UInt16(1 << state.stage)
        push!(
            output,
            (
                "gate_$(state.stage)",
                State(
                    state.stage + 1,
                    state.receipt_mask | bit,
                    state.lineage_mask | bit,
                    state.lineage_conflict,
                    state.artifact_coherent,
                ),
            ),
        )
        if mutation == :fake_gate
            push!(
                output,
                (
                    "fake_gate_$(state.stage)",
                    State(state.stage + 1, state.receipt_mask, state.lineage_mask | bit, false, true),
                ),
            )
        elseif mutation == :lineage_without_gate
            push!(
                output,
                (
                    "inject_lineage_$(state.stage)",
                    State(state.stage, state.receipt_mask, state.lineage_mask | bit, false, true),
                ),
            )
        end
    end
    if mutation == :stage_skip && state.stage + 1 < GATE_COUNT
        push!(
            output,
            (
                "skip_to_sink",
                State(GATE_COUNT, state.receipt_mask, state.lineage_mask, false, true),
            ),
        )
    elseif mutation == :lineage_conflict
        push!(
            output,
            (
                "overwrite_existing_role",
                State(state.stage, state.receipt_mask, state.lineage_mask, true, true),
            ),
        )
    elseif mutation == :artifact_chord_mismatch
        push!(
            output,
            (
                "accept_mismatched_chord",
                State(state.stage, state.receipt_mask, state.lineage_mask, false, false),
            ),
        )
    end
    return output
end

function search(mutation::Symbol)
    initial = State(0, 0x0000, 0x0000, false, true)
    queue = Tuple{State,Vector{String}}[(initial, String[])]
    seen = Set{State}([initial])
    explored = 0
    cursor = 1
    while cursor <= length(queue)
        state, trace = queue[cursor]
        cursor += 1
        if !safe(state)
            return (
                mutation=String(mutation),
                status="VIOLATION",
                trace=trace,
                trace_length=length(trace),
                reachable_states=length(seen),
                explored_transitions=explored,
            )
        end
        length(trace) == MAX_DEPTH && continue
        for (action, successor) in successors(state, mutation)
            explored += 1
            if !(successor in seen)
                push!(seen, successor)
                push!(queue, (successor, vcat(trace, [action])))
            end
        end
    end
    return (
        mutation=String(mutation),
        status="SAFE_WITHIN_BOUND",
        trace=String[],
        trace_length=0,
        reachable_states=length(seen),
        explored_transitions=explored,
    )
end

function escape_json(value::String)
    replace(replace(value, "\\" => "\\\\"), "\"" => "\\\"")
end

function string_array_json(values::Vector{String})
    "[" * join(["\"$(escape_json(value))\"" for value in values], ",") * "]"
end

function result_json(result)
    "{" *
    "\"explored_transitions\":$(result.explored_transitions)," *
    "\"mutation\":\"$(result.mutation)\"," *
    "\"reachable_states\":$(result.reachable_states)," *
    "\"status\":\"$(result.status)\"," *
    "\"trace\":" * string_array_json(result.trace) * "," *
    "\"trace_length\":$(result.trace_length)" *
    "}"
end

results = [search(mutation) for mutation in MUTATIONS]
@assert results[1].status == "SAFE_WITHIN_BOUND"
for result in results[2:end]
    @assert result.status == "VIOLATION"
    @assert result.trace_length == 1
end

println(
    "{" *
    "\"gate_count\":$(GATE_COUNT)," *
    "\"max_depth\":$(MAX_DEPTH)," *
    "\"results\":[" * join(result_json.(results), ",") * "]," *
    "\"schema_version\":\"zenodex.fcis.tcg.bounded-search.v1\"" *
    "}",
)
