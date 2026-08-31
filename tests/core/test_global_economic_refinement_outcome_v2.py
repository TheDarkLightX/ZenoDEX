from __future__ import annotations

import ast
import re
from pathlib import Path
from typing import cast

import pytest

import src.core.global_economic_refinement_checks_v2 as checks_module
import src.core.global_economic_refinement_outcome_v2 as outcome_module
from src.core.global_economic_proof_v2 import EconomicCommandOccurrenceV2
from src.core.global_economic_refinement_outcome_v2 import (
    ALL_GLOBAL_ECONOMIC_REFINEMENT_REJECT_CODES_V2,
    GLOBAL_ECONOMIC_REFINEMENT_OUTCOME_AUTHORITY_V2,
    GlobalEconomicRefinementAcceptedV2,
    GlobalEconomicRefinementRejectCodeV2,
    GlobalEconomicRefinementRejectedV2,
    classify_global_economic_refinement_error_v2,
    refine_global_economic_state_effects_outcome_v2,
)
from src.core.global_economic_state_effect_refinement_v2 import (
    GlobalEconomicStateEffectRefinementCandidateV2,
    GlobalEconomicStateEffectRefinementV2,
)
from src.core.global_economic_state_v2 import (
    GlobalEconomicStateV2,
    LaneStateRootV2,
    ReplayStateV2,
)
from src.core.global_settlement_types_v2 import (
    ALL_LANE_IDS_V2,
    ZERO_ROOT_V2,
    AssetSupplyV2,
    EconomicAmountV2,
    ExternalOutboxEnqueueV2,
    GlobalEconomicEffectPlanV2,
    GlobalOracleOccurrencePlanV2,
    GlobalTerminalObligationPlanV2,
    LaneIdV2,
)


def _root(value: int) -> str:
    return f"0x{value:064x}"


def _static_state() -> GlobalEconomicStateV2:
    return GlobalEconomicStateV2(
        chain_id="zeno-v2-outcome",
        deployment_root=_root(401),
        writer_epoch=4,
        height=7,
        profile_root=_root(402),
        lane_roots=tuple(
            LaneStateRootV2(
                lane_id=lane,
                module_release_id=_root(index + 1),
                enabled=lane is not LaneIdV2.EXTERNAL_CUSTODY,
                state_root=_root(index + 101),
            )
            for index, lane in enumerate(ALL_LANE_IDS_V2)
        ),
        history_root=ZERO_ROOT_V2,
    )


def _candidate(
    effect_plan: GlobalEconomicEffectPlanV2 | None = None,
) -> GlobalEconomicStateEffectRefinementCandidateV2:
    state = _static_state()
    return GlobalEconomicStateEffectRefinementCandidateV2(
        state,
        state,
        GlobalEconomicEffectPlanV2.empty() if effect_plan is None else effect_plan,
        (),
        GlobalTerminalObligationPlanV2.empty(),
        GlobalOracleOccurrencePlanV2.empty(),
    )


def _candidate_snapshot(
    candidate: GlobalEconomicStateEffectRefinementCandidateV2,
) -> tuple[object, ...]:
    return (
        candidate.pre_state,
        candidate.post_state,
        candidate.effect_plan,
        candidate.consumed_occurrences,
        candidate.terminal_plan,
        candidate.oracle_plan,
    )


def _signed_delta_overflow_candidate(
) -> GlobalEconomicStateEffectRefinementCandidateV2:
    template = _static_state()
    pre_amount = 1
    post_amount = pre_amount + (1 << 127)
    pre = GlobalEconomicStateV2(
        chain_id=template.chain_id,
        deployment_root=template.deployment_root,
        writer_epoch=template.writer_epoch,
        height=template.height,
        profile_root=template.profile_root,
        lane_roots=template.lane_roots,
        balances=(EconomicAmountV2("alice", "USD", "accounts", pre_amount),),
        supplies=(AssetSupplyV2("USD", pre_amount),),
        history_root=template.history_root,
    )
    occurrence = EconomicCommandOccurrenceV2(
        chain_id=pre.chain_id,
        deployment_root=pre.deployment_root,
        height=pre.height + 1,
        tx_index=0,
        op_index=0,
        command_kind="signed_delta_overflow_probe",
        command_body_hash=_root(601),
        route_release_id=_root(602),
        subject_id="alice",
        grant_root=_root(603),
        nonce=1,
        profile_root=pre.profile_root,
        pre_state_root=pre.state_root,
        consumed_object_ids=(),
    )
    post = GlobalEconomicStateV2(
        chain_id=pre.chain_id,
        deployment_root=pre.deployment_root,
        writer_epoch=pre.writer_epoch,
        height=pre.height + 1,
        profile_root=pre.profile_root,
        lane_roots=pre.lane_roots,
        balances=(EconomicAmountV2("alice", "USD", "accounts", post_amount),),
        supplies=(AssetSupplyV2("USD", post_amount),),
        replay_state=(ReplayStateV2(occurrence.replay_id, occurrence.occurrence_id),),
        history_root=pre.history_root,
    )
    effects = GlobalEconomicEffectPlanV2(
        (),
        (),
        (),
        (),
        (occurrence.occurrence_id,),
        (),
    )
    return GlobalEconomicStateEffectRefinementCandidateV2(
        pre,
        post,
        effects,
        (occurrence,),
        GlobalTerminalObligationPlanV2.empty(),
        GlobalOracleOccurrencePlanV2.empty(),
    )


def test_static_candidate_returns_existing_checker_result() -> None:
    candidate = _candidate()

    outcome = refine_global_economic_state_effects_outcome_v2(candidate)

    assert isinstance(outcome, GlobalEconomicRefinementAcceptedV2)
    assert type(outcome.witness) is GlobalEconomicStateEffectRefinementV2
    assert outcome.witness.pre_state_root == candidate.pre_state.state_root
    assert outcome.witness.post_state_root == candidate.pre_state.state_root
    assert outcome.production_authority == GLOBAL_ECONOMIC_REFINEMENT_OUTCOME_AUTHORITY_V2


def test_signed_state_delta_overflow_matches_rust_reject_code() -> None:
    candidate = _signed_delta_overflow_candidate()
    before = _candidate_snapshot(candidate)

    outcome = refine_global_economic_state_effects_outcome_v2(candidate)

    assert isinstance(outcome, GlobalEconomicRefinementRejectedV2)
    assert outcome.reject_code is (
        GlobalEconomicRefinementRejectCodeV2.SIGNED_STATE_DELTA_OVERFLOW
    )
    assert outcome.pre_state_root == outcome.post_state_root
    assert outcome.effect_plan.is_empty
    assert _candidate_snapshot(candidate) == before


def test_external_outbox_reject_is_exact_no_op_and_candidate_is_unchanged() -> None:
    effects = GlobalEconomicEffectPlanV2(
        (),
        (),
        (),
        (),
        (),
        (
            ExternalOutboxEnqueueV2(
                effect_id=_root(501),
                destination_id="external:adapter",
                payload_hash=_root(502),
                adapter_profile_root=_root(503),
            ),
        ),
    )
    candidate = _candidate(effects)
    before = _candidate_snapshot(candidate)
    pre_root = candidate.pre_state.state_root

    outcome = refine_global_economic_state_effects_outcome_v2(candidate)

    assert isinstance(outcome, GlobalEconomicRefinementRejectedV2)
    assert outcome.reject_code is (
        GlobalEconomicRefinementRejectCodeV2.EXTERNAL_OUTBOX_REQUIRES_PUBLISHER
    )
    assert outcome.pre_state_root == outcome.post_state_root == pre_root
    assert outcome.effect_plan == GlobalEconomicEffectPlanV2.empty()
    assert outcome.terminal_plan == GlobalTerminalObligationPlanV2.empty()
    assert outcome.oracle_plan == GlobalOracleOccurrencePlanV2.empty()
    assert outcome.consumed_occurrences == ()
    assert outcome.outbox == ()
    assert outcome.production_authority == "NONE"
    assert _candidate_snapshot(candidate) == before


def test_outbox_rejection_precedes_zero_occurrence_nonstatic_rejection() -> None:
    effects = GlobalEconomicEffectPlanV2(
        (),
        (),
        (),
        (),
        (),
        (
            ExternalOutboxEnqueueV2(
                _root(511),
                "external:adapter",
                _root(512),
                _root(513),
            ),
        ),
    )

    outcome = refine_global_economic_state_effects_outcome_v2(_candidate(effects))

    assert isinstance(outcome, GlobalEconomicRefinementRejectedV2)
    assert outcome.reject_code is (
        GlobalEconomicRefinementRejectCodeV2.EXTERNAL_OUTBOX_REQUIRES_PUBLISHER
    )


def test_unknown_internal_validation_text_becomes_contract_drift(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    candidate = _candidate()
    before = _candidate_snapshot(candidate)

    def drifted_refiner(
        _: GlobalEconomicStateEffectRefinementCandidateV2,
    ) -> GlobalEconomicStateEffectRefinementV2:
        raise ValueError("unmapped future validation text")

    monkeypatch.setattr(
        outcome_module,
        "refine_global_economic_state_effects_v2",
        drifted_refiner,
    )

    outcome = refine_global_economic_state_effects_outcome_v2(candidate)

    assert isinstance(outcome, GlobalEconomicRefinementRejectedV2)
    assert outcome.reject_code is (
        GlobalEconomicRefinementRejectCodeV2.INTERNAL_CONTRACT_DRIFT
    )
    assert outcome.pre_state_root == outcome.post_state_root
    assert outcome.effect_plan.is_empty
    assert _candidate_snapshot(candidate) == before
    assert classify_global_economic_refinement_error_v2(
        ValueError("unmapped future validation text")
    ) is GlobalEconomicRefinementRejectCodeV2.INTERNAL_CONTRACT_DRIFT


def test_unexpected_internal_exception_propagates_fail_closed(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    candidate = _candidate()
    before = _candidate_snapshot(candidate)

    def broken_refiner(
        _: GlobalEconomicStateEffectRefinementCandidateV2,
    ) -> GlobalEconomicStateEffectRefinementV2:
        raise RuntimeError("unexpected implementation defect")

    monkeypatch.setattr(
        outcome_module,
        "refine_global_economic_state_effects_v2",
        broken_refiner,
    )

    with pytest.raises(RuntimeError, match="unexpected implementation defect"):
        refine_global_economic_state_effects_outcome_v2(candidate)
    assert _candidate_snapshot(candidate) == before


@pytest.mark.parametrize(
    ("message", "expected"),
    (
        (
            "global refinement balances state/effect mismatch",
            GlobalEconomicRefinementRejectCodeV2.BALANCES_STATE_EFFECT_MISMATCH,
        ),
        (
            "global refinement terminal obligation plan mismatch",
            GlobalEconomicRefinementRejectCodeV2.TERMINAL_PLAN_MISMATCH,
        ),
        (
            "global refinement Oracle occurrence plan mismatch",
            GlobalEconomicRefinementRejectCodeV2.ORACLE_PLAN_MISMATCH,
        ),
        (
            "global refinement replay already consumed",
            GlobalEconomicRefinementRejectCodeV2.REPLAY_ALREADY_CONSUMED,
        ),
    ),
)
def test_representative_checker_messages_have_exact_stable_codes(
    message: str,
    expected: GlobalEconomicRefinementRejectCodeV2,
) -> None:
    assert classify_global_economic_refinement_error_v2(ValueError(message)) is expected


def _raised_validation_message_shapes(
    source_path: Path,
) -> set[tuple[str, str]]:
    tree = ast.parse(source_path.read_text(encoding="utf-8"))
    messages: set[tuple[str, str]] = set()
    for node in ast.walk(tree):
        if not isinstance(node, ast.Raise) or not isinstance(node.exc, ast.Call):
            continue
        if not isinstance(node.exc.func, ast.Name) or node.exc.func.id not in {
            "TypeError",
            "ValueError",
        }:
            continue
        if len(node.exc.args) != 1:
            raise AssertionError("validation raise must have one explicit message")
        argument = node.exc.args[0]
        if isinstance(argument, ast.Constant) and isinstance(argument.value, str):
            message = argument.value
        elif isinstance(argument, ast.JoinedStr):
            parts: list[str] = []
            for value in argument.values:
                if isinstance(value, ast.Constant) and isinstance(value.value, str):
                    parts.append(value.value)
                elif (
                    isinstance(value, ast.FormattedValue)
                    and isinstance(value.value, ast.Name)
                ):
                    parts.append("{" + value.value.id + "}")
                else:
                    raise AssertionError("validation f-string shape must stay explicit")
            message = "".join(parts)
        else:
            raise AssertionError("validation message must be a literal or simple f-string")
        messages.add((node.exc.func.id, message))
    return messages


def test_every_wrapped_python_validation_message_is_explicitly_classified() -> None:
    repository = Path(__file__).parents[2]
    source_messages = set().union(
        *(
            _raised_validation_message_shapes(repository / relative_path)
            for relative_path in (
                "src/core/global_economic_state_effect_refinement_v2.py",
                "src/core/global_economic_refinement_checks_v2.py",
            )
        )
    )
    # These messages guard constructors or the candidate API boundary. They
    # cannot arise after this adapter has acquired an exact candidate and its
    # pre-state root, so they remain exceptions instead of protocol rejects.
    constructor_or_api_boundary_only = {
        ("TypeError", "global refinement pre-state must be exact"),
        ("TypeError", "global refinement post-state must be exact"),
        ("TypeError", "global refinement effect plan must be exact"),
        (
            "TypeError",
            "global refinement occurrences must be an exact typed tuple",
        ),
        ("TypeError", "global refinement terminal plan must be exact"),
        ("TypeError", "global refinement Oracle plan must be exact"),
        ("TypeError", "global ABI V2 refinement is checker-constructed"),
        ("TypeError", "global refinement candidate must be exact"),
    }
    state_effect_family_shape = (
        "ValueError",
        "global refinement {field_name} state/effect mismatch",
    )
    special_shapes = constructor_or_api_boundary_only | {state_effect_family_shape}
    literal_reachable = source_messages - special_shapes

    assert source_messages & constructor_or_api_boundary_only == (
        constructor_or_api_boundary_only
    )
    assert state_effect_family_shape in source_messages
    assert all(error_type == "ValueError" for error_type, _ in literal_reachable)
    for _, message in literal_reachable:
        assert classify_global_economic_refinement_error_v2(
            ValueError(message)
        ) is not GlobalEconomicRefinementRejectCodeV2.INTERNAL_CONTRACT_DRIFT
    for field_name in checks_module._STATE_EFFECT_FIELDS_V2.values():
        message = f"global refinement {field_name} state/effect mismatch"
        assert classify_global_economic_refinement_error_v2(
            ValueError(message)
        ) is not GlobalEconomicRefinementRejectCodeV2.INTERNAL_CONTRACT_DRIFT


def test_python_and_rust_wire_code_sets_match() -> None:
    rust_source = (
        Path(__file__).parents[2]
        / "zk/global_settlement_abi_v2/src/outcome.rs"
    ).read_text(encoding="utf-8")
    rust_codes = tuple(
        re.findall(
            r'Self::[A-Z0-9_]+\s*=>\s*(?:\{\s*)?"([A-Z0-9_]+)"',
            rust_source,
        )
    )

    assert rust_codes == tuple(
        code.value for code in ALL_GLOBAL_ECONOMIC_REFINEMENT_REJECT_CODES_V2
    )


def test_wrapper_preserves_exact_candidate_type_boundary() -> None:
    with pytest.raises(TypeError, match="candidate must be exact"):
        refine_global_economic_state_effects_outcome_v2(
            cast(GlobalEconomicStateEffectRefinementCandidateV2, object())
        )
