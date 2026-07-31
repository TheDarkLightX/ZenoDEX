# Base-only independent finite oracle for the FCIS Durable Retraction Algebra.

const MAX_DEPTH = 14
const SWITCH_PHASE = 4
const TERMINAL_PHASE = 6

struct State
    committed::Bool
    receipt::Bool
    nullifier::Bool
    outbox::Bool
    external_effect::Bool
    ack::Bool
    commit_count::Int
    phase::Int
    head_authorized::Bool
    old_writer_after_switch::Bool
    unauthorized_publication::Bool
end

State() = State(false, false, false, false, false, false, 0, 0, false, false, false)

function replace_state(
    s::State;
    committed::Bool=s.committed,
    receipt::Bool=s.receipt,
    nullifier::Bool=s.nullifier,
    outbox::Bool=s.outbox,
    external_effect::Bool=s.external_effect,
    ack::Bool=s.ack,
    commit_count::Int=s.commit_count,
    phase::Int=s.phase,
    head_authorized::Bool=s.head_authorized,
    old_writer_after_switch::Bool=s.old_writer_after_switch,
    unauthorized_publication::Bool=s.unauthorized_publication,
)::State
    State(
        committed,
        receipt,
        nullifier,
        outbox,
        external_effect,
        ack,
        commit_count,
        phase,
        head_authorized,
        old_writer_after_switch,
        unauthorized_publication,
    )
end

function violations(s::State)::Vector{String}
    found = String[]
    bits = (s.committed, s.receipt, s.nullifier, s.outbox)
    if length(Set(bits)) != 1
        push!(found, "AtomicPublication")
    end
    if s.external_effect && !s.outbox
        push!(found, "NoEffectWithoutCommittedOutbox")
    end
    if s.ack && (!s.external_effect || !s.outbox)
        push!(found, "AckHasCommittedDeliveredAncestor")
    end
    if s.commit_count > 1
        push!(found, "SameNonceAtMostOnce")
    end
    if s.old_writer_after_switch
        push!(found, "OldWriterDisabledAfterSwitch")
    end
    if s.unauthorized_publication
        push!(found, "PublicationRequiresFreshHeadAuthorization")
    end
    if !(0 <= s.phase <= TERMINAL_PHASE)
        push!(found, "MigrationPhaseBound")
    end
    found
end

function safe_actions(s::State)::Vector{Tuple{String,State}}
    actions = Tuple{String,State}[]
    if !s.head_authorized
        # This transition stands for a verifier-produced environment grant.
        push!(actions, ("receive_verified_external_grant", replace_state(s; head_authorized=true)))
    end
    push!(actions, ("restart_reopen", replace_state(s; head_authorized=false)))
    push!(actions, ("crash_before_linearization", replace_state(s; head_authorized=false)))
    if !s.committed && s.phase != 3 && s.head_authorized
        post = replace_state(
            s;
            committed=true,
            receipt=true,
            nullifier=true,
            outbox=true,
            commit_count=1,
            head_authorized=false,
        )
        push!(actions, ("atomic_commit", post))
        push!(actions, ("crash_after_linearization", post))
    end
    if s.committed
        push!(actions, ("retry_same_commit", s))
    end
    if s.outbox
        delivered = replace_state(s; external_effect=true)
        push!(actions, ("deliver", delivered))
        push!(actions, ("deliver_then_lose_ack", delivered))
    end
    if s.external_effect && s.outbox && s.head_authorized
        # Acknowledgment consumes a verified destination receipt premise.
        push!(actions, (
            "acknowledge_verified_destination_receipt",
            replace_state(s; ack=true, head_authorized=false),
        ))
    end
    if s.phase < TERMINAL_PHASE && s.head_authorized
        push!(actions, (
            "advance_migration_phase",
            replace_state(s; phase=s.phase + 1, head_authorized=false),
        ))
    end
    actions
end

function mutant_actions(id::String, s::State)::Vector{Tuple{String,State}}
    if id == "split_publication" && !s.committed
        return [("mutant_commit_state_only", replace_state(
            s;
            committed=true,
            commit_count=1,
        ))]
    elseif id == "orphan_delivery" && !s.external_effect
        return [("mutant_deliver_without_outbox", replace_state(s; external_effect=true))]
    elseif id == "orphan_ack" && !s.ack
        return [("mutant_ack_without_delivery", replace_state(s; ack=true))]
    elseif id == "same_nonce_double_commit" && s.committed
        return [("mutant_second_same_nonce_commit", replace_state(s; commit_count=2))]
    elseif id == "old_writer_after_switch" && s.phase >= SWITCH_PHASE && !s.old_writer_after_switch
        return [("mutant_old_writer_commit", replace_state(s; old_writer_after_switch=true))]
    elseif id == "unauthorized_publication" && !s.committed && !s.head_authorized && s.phase != 3
        return [("mutant_publish_without_head_authorization", replace_state(
            s;
            committed=true,
            receipt=true,
            nullifier=true,
            outbox=true,
            commit_count=1,
            unauthorized_publication=true,
        ))]
    elseif id == "selected_root_reopen" && s.committed && s.receipt
        return [("mutant_drop_receipt_keep_state_root", replace_state(s; receipt=false))]
    end
    Tuple{String,State}[]
end

function explore_safe()
    initial = State()
    reached = Set([initial])
    queue = Tuple{State,Int}[(initial, 0)]
    cursor = 1
    transitions = 0
    while cursor <= length(queue)
        state, depth = queue[cursor]
        cursor += 1
        @assert isempty(violations(state))
        depth >= MAX_DEPTH && continue
        for (_, target) in safe_actions(state)
            transitions += 1
            @assert isempty(violations(target))
            if !(target in reached)
                push!(reached, target)
                push!(queue, (target, depth + 1))
            end
        end
    end
    reached, transitions
end

function minimize_mutant(id::String)
    initial = State()
    queue = Tuple{State,Vector{String}}[(initial, String[])]
    seen = Set([initial])
    cursor = 1
    while cursor <= length(queue)
        state, trace = queue[cursor]
        cursor += 1
        for (label, target) in mutant_actions(id, state)
            broken = violations(target)
            if !isempty(broken)
                return vcat(trace, [label]), broken
            end
        end
        length(trace) >= MAX_DEPTH && continue
        for (label, target) in safe_actions(state)
            if !(target in seen)
                push!(seen, target)
                push!(queue, (target, vcat(trace, [label])))
            end
        end
    end
    error("mutant survived: " * id)
end

function json_string(value::String)::String
    "\"" * replace(value, "\\" => "\\\\", "\"" => "\\\"") * "\""
end

function json_array(values::Vector{String})::String
    "[" * join(json_string.(values), ",") * "]"
end

mutant_ids = [
    "split_publication",
    "orphan_delivery",
    "orphan_ack",
    "same_nonce_double_commit",
    "old_writer_after_switch",
    "unauthorized_publication",
    "selected_root_reopen",
]

states, transition_count = explore_safe()
@assert length(states) == 49
@assert transition_count == 254

mutant_json = String[]
for id in mutant_ids
    trace, broken = minimize_mutant(id)
    push!(mutant_json,
        "{" *
        "\"id\":" * json_string(id) * "," *
        "\"killed\":true," *
        "\"minimal_trace\":" * json_array(trace) * "," *
        "\"violations\":" * json_array(broken) *
        "}"
    )
end

safe_invariants = [
    "AtomicPublication",
    "NoEffectWithoutCommittedOutbox",
    "AckHasCommittedDeliveredAncestor",
    "SameNonceAtMostOnce",
    "OldWriterDisabledAfterSwitch",
    "PublicationRequiresFreshHeadAuthorization",
    "MigrationPhaseBound",
]

print("{")
print("\"schema_version\":\"zenodex.fcis.durable-retraction-search.v1\",")
print("\"max_depth\":", MAX_DEPTH, ",")
print("\"safe_reachable_state_count\":", length(states), ",")
print("\"safe_transition_count\":", transition_count, ",")
print("\"safe_invariants\":", json_array(safe_invariants), ",")
print("\"mutants\":[", join(mutant_json, ","), "]")
println("}")
