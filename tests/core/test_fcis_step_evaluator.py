from __future__ import annotations

from dataclasses import replace

import pytest

from src.core.batch_clearing import compute_settlement
from src.core.dex import DexState
from src.core.fcis_step_evaluation_values import (
    FCISStepEvaluationOkV1,
    FCISStepEvaluationPhaseV1,
    FCISStepEvaluationRejectV1,
)
from src.core.fcis_step_evaluator import (
    FCIS_STEP_EVALUATOR_UNMOUNTED_V1,
    evaluate_fcis_step_candidate_v1,
)
from src.core.liquidity import create_pool
from src.core.perps import PERPS_STATE_VERSION_V4, PerpsState
from src.core.settlement import Settlement
from src.core.settlement_snapshots import snapshot_settlement
from src.state import BalanceTable, LPTable
from src.state.fcis_execution_context_values import (
    FCISFeeSplitPolicySourceV1,
    FCISSettlementExecutionContextSourceV1,
    FCISSettlementModeV1,
    FCISStepExecutionContextSourceV1,
)
from src.state.intent_snapshots import admit_intent_batch
from src.state.intents import Intent, IntentKind
from src.state.legacy_state_snapshots import (
    admit_legacy_balance_for_differential_v1,
    admit_legacy_lp_for_differential_v1,
    admit_legacy_nonce_for_differential_v1,
    admit_legacy_pool_map_for_differential_v1,
)
from src.state.state_root import state_root_preimage_with_committed_spot_state_v1
from src.state.state_snapshots import (
    snapshot_fee_accumulator,
    snapshot_oracle,
    snapshot_perps,
    snapshot_vault,
)


def _iid(value: int) -> str:
    return "0x" + f"{value:064x}"


def _context_source() -> FCISStepExecutionContextSourceV1:
    return FCISStepExecutionContextSourceV1(
        settlement=FCISSettlementExecutionContextSourceV1(
            now=700,
            min_lp_position_age_seconds=0,
            mode=FCISSettlementModeV1.STRONG_REPLAY,
            allow_cow_netting=False,
            allow_snapshot_bound_quote_bindings=False,
            protocol_fee_share_bps=0,
            protocol_fee_recipient_pubkey=None,
        ),
        require_all_nonces=True,
        reject_settlements_with_rejected_intents=True,
        fee_split_policy=FCISFeeSplitPolicySourceV1(
            buyback_bps=3_333,
            treasury_bps=3_333,
            rewards_bps=3_334,
        ),
        lp_duration_policy=None,
        snapshot_version=4,
    )


def _swap_case() -> tuple[DexState, Intent, Settlement]:
    owner = "0x" + "11" * 48
    asset0 = "0x" + "01" * 32
    asset1 = "0x" + "02" * 32
    pool_id, pool, _lp_minted = create_pool(
        asset0=asset0,
        asset1=asset1,
        amount0=2_000_000,
        amount1=2_000_000,
        fee_bps=30,
        creator_pubkey=owner,
    )
    balances = BalanceTable()
    balances.set(owner, asset0, 10_000_000)
    balances.set(owner, asset1, 10_000_000)
    state = DexState(
        balances=balances,
        pools={pool_id: pool},
        lp_balances=LPTable(),
    )
    intent = Intent(
        module="TauSwap",
        version="0.1",
        kind=IntentKind.SWAP_EXACT_IN,
        intent_id=_iid(1),
        sender_pubkey=owner,
        deadline=10_000,
        fields={
            "pool_id": pool_id,
            "asset_in": asset0,
            "asset_out": asset1,
            "amount_in": 100_000,
            "min_amount_out": 1,
            "nonce": 1,
        },
    )
    settlement = compute_settlement(
        [intent],
        state.pools,
        state.balances,
        state.lp_balances,
    )
    return state, intent, settlement


def _evaluate(
    state: DexState,
    settlement: object,
    intents: object,
    context: object,
):
    owned_settlement = (
        snapshot_settlement(settlement) if type(settlement) is Settlement else settlement
    )
    owned_intents = admit_intent_batch(intents) if type(intents) is list else intents
    return evaluate_fcis_step_candidate_v1(
        balances=admit_legacy_balance_for_differential_v1(state.balances),
        pools=admit_legacy_pool_map_for_differential_v1(state.pools),
        lp_balances=admit_legacy_lp_for_differential_v1(state.lp_balances),
        nonces=admit_legacy_nonce_for_differential_v1(state.nonces),
        vault=snapshot_vault(state.vault),
        oracle=snapshot_oracle(state.oracle),
        fee_accumulator=snapshot_fee_accumulator(state.fee_accumulator),
        perps=snapshot_perps(state.perps),
        settlement=owned_settlement,
        intents=owned_intents,
        context=context,
    )


def test_exact_step_evaluator_retains_one_candidate_and_all_leaf_patches() -> None:
    state, intent, settlement = _swap_case()
    pre_balances = admit_legacy_balance_for_differential_v1(state.balances)
    pre_pools = admit_legacy_pool_map_for_differential_v1(state.pools)
    pre_nonces = admit_legacy_nonce_for_differential_v1(state.nonces)

    result = _evaluate(state, settlement, [intent], _context_source())

    assert FCIS_STEP_EVALUATOR_UNMOUNTED_V1 is True
    assert type(result) is FCISStepEvaluationOkV1
    candidate = result.candidate
    assert candidate.spot.balance_patch is not None
    assert candidate.spot.pool_patch is not None
    assert candidate.spot.lp_patch is None
    assert candidate.nonce_patch is not None
    assert candidate.fee_allocation is not None
    assert candidate.nonces.get_last(intent.sender_pubkey) == 1
    assert admit_legacy_balance_for_differential_v1(state.balances) == pre_balances
    assert admit_legacy_pool_map_for_differential_v1(state.pools) == pre_pools
    assert admit_legacy_nonce_for_differential_v1(state.nonces) == pre_nonces


def test_evidence_binds_same_candidate_context_and_pre_post_roots() -> None:
    state, intent, settlement = _swap_case()
    context = _context_source()
    pre_root_preimage = state_root_preimage_with_committed_spot_state_v1(
        balances=admit_legacy_balance_for_differential_v1(state.balances),
        pools=admit_legacy_pool_map_for_differential_v1(state.pools),
        lp_balances=admit_legacy_lp_for_differential_v1(state.lp_balances),
        nonces=admit_legacy_nonce_for_differential_v1(state.nonces),
        fee_accumulator=snapshot_fee_accumulator(state.fee_accumulator),
    )

    first = _evaluate(state, settlement, [intent], context)
    second = _evaluate(state, settlement, [intent], context)

    assert type(first) is FCISStepEvaluationOkV1
    assert first == second
    candidate = first.candidate
    evidence = first.evidence
    assert evidence.pre_state_root_preimage == pre_root_preimage
    assert evidence.post_state_root_preimage == (
        state_root_preimage_with_committed_spot_state_v1(
            balances=candidate.spot.balances,
            pools=candidate.spot.pools,
            lp_balances=candidate.spot.lp_balances,
            nonces=candidate.nonces,
            fee_accumulator=candidate.fee_accumulator,
        )
    )
    retained_context_bytes = evidence.execution_context_bytes
    object.__setattr__(context.settlement, "now", 999_999)
    assert evidence.execution_context_bytes == retained_context_bytes


def test_context_rejection_has_stable_code_path_and_no_candidate() -> None:
    state, intent, settlement = _swap_case()
    context = _context_source()
    object.__setattr__(context.settlement, "allow_cow_netting", 1)

    result = _evaluate(state, settlement, [intent], context)

    assert result == FCISStepEvaluationRejectV1(
        FCISStepEvaluationPhaseV1.CONTEXT_ADMISSION,
        "wrong_exact_type",
        ("settlement", "allow_cow_netting"),
        ('step context admission rejected: wrong_exact_type:$["settlement"]["allow_cow_netting"]'),
    )
    assert not hasattr(result, "candidate")
    assert not hasattr(result, "evidence")


def test_invalid_eighth_state_field_rejects_without_partial_candidate() -> None:
    state, intent, settlement = _swap_case()
    perps = PerpsState(version=PERPS_STATE_VERSION_V4, markets={})
    exact_perps = snapshot_perps(perps)
    assert exact_perps is not None
    object.__setattr__(exact_perps, "version", True)

    result = evaluate_fcis_step_candidate_v1(
        balances=admit_legacy_balance_for_differential_v1(state.balances),
        pools=admit_legacy_pool_map_for_differential_v1(state.pools),
        lp_balances=admit_legacy_lp_for_differential_v1(state.lp_balances),
        nonces=admit_legacy_nonce_for_differential_v1(state.nonces),
        vault=snapshot_vault(state.vault),
        oracle=snapshot_oracle(state.oracle),
        fee_accumulator=snapshot_fee_accumulator(state.fee_accumulator),
        perps=exact_perps,
        settlement=snapshot_settlement(settlement),
        intents=admit_intent_batch([intent]),
        context=_context_source(),
    )

    assert type(result) is FCISStepEvaluationRejectV1
    assert result.phase is FCISStepEvaluationPhaseV1.STATE_ADMISSION
    assert result.code == "wrong_exact_type"
    assert result.path == ("perps", "version")
    assert not hasattr(result, "candidate")


def test_command_carrier_rejects_list_subclass_before_iteration_hook() -> None:
    state, _intent, settlement = _swap_case()

    class HostileList(list[Intent]):
        def __iter__(self):
            raise AssertionError("hostile iterator executed")

    result = _evaluate(state, settlement, HostileList(), _context_source())

    assert type(result) is FCISStepEvaluationRejectV1
    assert result.phase is FCISStepEvaluationPhaseV1.COMMAND_ADMISSION
    assert result.code == "wrong_exact_type"
    assert result.path == ("intents",)


def test_nonce_rejection_precedes_tampered_settlement_rejection() -> None:
    state, intent, settlement = _swap_case()
    missing_nonce = replace(
        intent,
        fields={key: value for key, value in intent.fields.items() if key != "nonce"},
    )
    tampered = replace(settlement, balance_deltas=[])

    result = _evaluate(state, tampered, [missing_nonce], _context_source())

    assert type(result) is FCISStepEvaluationRejectV1
    assert result.phase is FCISStepEvaluationPhaseV1.NONCE
    assert result.public_reason == "Missing/invalid nonce"
    assert not hasattr(result, "candidate")


def test_unexpected_settlement_result_fails_closed_without_candidate(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    state, intent, settlement = _swap_case()
    monkeypatch.setattr(
        "src.core.fcis_step_evaluator._evaluate_spot_v1",
        lambda **_kwargs: object(),
    )

    result = _evaluate(state, settlement, [intent], _context_source())

    assert type(result) is FCISStepEvaluationRejectV1
    assert result.phase is FCISStepEvaluationPhaseV1.SETTLEMENT
    assert result.code == "impossible_result"
    assert not hasattr(result, "candidate")
    assert not hasattr(result, "evidence")


def test_unexpected_fee_result_fails_closed_without_candidate(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    state, intent, settlement = _swap_case()
    monkeypatch.setattr(
        "src.core.fcis_step_evaluator.split_fee_with_owned_policy_v1",
        lambda **_kwargs: object(),
    )

    result = _evaluate(state, settlement, [intent], _context_source())

    assert type(result) is FCISStepEvaluationRejectV1
    assert result.phase is FCISStepEvaluationPhaseV1.FEE
    assert result.code == "impossible_result"
    assert not hasattr(result, "candidate")
    assert not hasattr(result, "evidence")


def test_exact_command_admission_rejects_legacy_settlement() -> None:
    state, intent, settlement = _swap_case()

    result = evaluate_fcis_step_candidate_v1(
        balances=admit_legacy_balance_for_differential_v1(state.balances),
        pools=admit_legacy_pool_map_for_differential_v1(state.pools),
        lp_balances=admit_legacy_lp_for_differential_v1(state.lp_balances),
        nonces=admit_legacy_nonce_for_differential_v1(state.nonces),
        vault=snapshot_vault(state.vault),
        oracle=snapshot_oracle(state.oracle),
        fee_accumulator=snapshot_fee_accumulator(state.fee_accumulator),
        perps=snapshot_perps(state.perps),
        settlement=settlement,
        intents=admit_intent_batch([intent]),
        context=_context_source(),
    )

    assert type(result) is FCISStepEvaluationRejectV1
    assert result.phase is FCISStepEvaluationPhaseV1.COMMAND_ADMISSION
    assert result.code == "wrong_exact_type"
    assert result.path == ("settlement",)
    assert "OwnedSettlementV1" in result.public_reason


def test_exact_command_admission_rejects_legacy_intent_list() -> None:
    state, _intent, settlement = _swap_case()
    owned_settlement = snapshot_settlement(settlement)

    result = evaluate_fcis_step_candidate_v1(
        balances=admit_legacy_balance_for_differential_v1(state.balances),
        pools=admit_legacy_pool_map_for_differential_v1(state.pools),
        lp_balances=admit_legacy_lp_for_differential_v1(state.lp_balances),
        nonces=admit_legacy_nonce_for_differential_v1(state.nonces),
        vault=snapshot_vault(state.vault),
        oracle=snapshot_oracle(state.oracle),
        fee_accumulator=snapshot_fee_accumulator(state.fee_accumulator),
        perps=snapshot_perps(state.perps),
        settlement=owned_settlement,
        intents=[_intent],
        context=_context_source(),
    )

    assert type(result) is FCISStepEvaluationRejectV1
    assert result.phase is FCISStepEvaluationPhaseV1.COMMAND_ADMISSION
    assert result.code == "wrong_exact_type"
    assert result.path == ("intents",)


def test_exact_command_admission_rejects_intent_subclass_in_tuple() -> None:
    state, intent, settlement = _swap_case()
    owned_settlement = snapshot_settlement(settlement)

    class IntentLookalike:
        pass

    result = evaluate_fcis_step_candidate_v1(
        balances=admit_legacy_balance_for_differential_v1(state.balances),
        pools=admit_legacy_pool_map_for_differential_v1(state.pools),
        lp_balances=admit_legacy_lp_for_differential_v1(state.lp_balances),
        nonces=admit_legacy_nonce_for_differential_v1(state.nonces),
        vault=snapshot_vault(state.vault),
        oracle=snapshot_oracle(state.oracle),
        fee_accumulator=snapshot_fee_accumulator(state.fee_accumulator),
        perps=snapshot_perps(state.perps),
        settlement=owned_settlement,
        intents=(IntentLookalike(),),
        context=_context_source(),
    )

    assert type(result) is FCISStepEvaluationRejectV1
    assert result.phase is FCISStepEvaluationPhaseV1.COMMAND_ADMISSION
    assert result.code == "wrong_exact_type"
    assert result.path == ("intents", 0)


def test_exact_command_readmission_rejects_corrupted_owned_settlement_with_stable_path() -> None:
    state, intent, settlement = _swap_case()
    owned_settlement = snapshot_settlement(settlement)
    object.__setattr__(owned_settlement, "batch_ref", 1)

    result = _evaluate(
        state,
        owned_settlement,
        admit_intent_batch([intent]),
        _context_source(),
    )

    assert result == FCISStepEvaluationRejectV1(
        FCISStepEvaluationPhaseV1.COMMAND_ADMISSION,
        "wrong_exact_type",
        ("settlement", "batch_ref"),
        'step command admission rejected: wrong_exact_type:$["settlement"]["batch_ref"]',
    )
    assert not hasattr(result, "candidate")
    assert not hasattr(result, "evidence")


def test_exact_command_readmission_rejects_corrupted_owned_intent_with_stable_path() -> None:
    state, intent, settlement = _swap_case()
    owned_intents = admit_intent_batch([intent])
    object.__setattr__(owned_intents[0], "sender_pubkey", "bad")

    result = _evaluate(
        state,
        snapshot_settlement(settlement),
        owned_intents,
        _context_source(),
    )

    assert result == FCISStepEvaluationRejectV1(
        FCISStepEvaluationPhaseV1.COMMAND_ADMISSION,
        "noncanonical_scalar",
        ("intents", 0, "sender_pubkey"),
        ('step command admission rejected: noncanonical_scalar:$["intents"][0]["sender_pubkey"]'),
    )
    assert not hasattr(result, "candidate")
    assert not hasattr(result, "evidence")


def test_exact_step_path_does_not_call_legacy_differential_callbacks(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    state, intent, settlement = _swap_case()

    def forbidden_legacy_call(**_kwargs: object) -> object:
        raise AssertionError("legacy differential callback reached exact path")

    monkeypatch.setattr(
        "src.core.fcis_step_evaluator._evaluate_spot_legacy_for_differential_v1",
        forbidden_legacy_call,
    )
    monkeypatch.setattr(
        "src.state.support_root.compute_support_state_root_for_batch_committed_v1",
        forbidden_legacy_call,
    )

    result = _evaluate(state, settlement, [intent], _context_source())

    assert type(result) is FCISStepEvaluationOkV1
    assert result.candidate.nonces.get_last(intent.sender_pubkey) == 1
    assert result.evidence.support_root_version == 5


def test_exact_step_evaluator_matches_independent_legacy_oracle() -> None:
    """Compare the exact evaluator against the independent legacy oracle
    (``_evaluate_spot_legacy_for_differential_v1``), not the shadow adapter
    which now delegates to the exact path.  Both paths receive the same
    well-formed inputs (accepted by both profiles) and must produce
    identical post-state balances, pools, and lp_balances."""
    from src.core.fcis_step_evaluator import _evaluate_spot_legacy_for_differential_v1
    from src.core.settlement_strong_validator import (
        StrongSettlementRejectV1,
        StrongSettlementStateCandidateV1,
    )
    from src.state.fcis_execution_context import admit_fcis_step_execution_context_v1
    from src.state.snapshot_combinators import AdmitOk

    state, intent, settlement = _swap_case()
    context_source = _context_source()
    exact_context = admit_fcis_step_execution_context_v1(context_source)
    if type(exact_context) is not AdmitOk:
        raise AssertionError("context admission failed")

    exact_result = _evaluate(state, settlement, [intent], context_source)
    assert type(exact_result) is FCISStepEvaluationOkV1

    legacy_result = _evaluate_spot_legacy_for_differential_v1(
        balances=admit_legacy_balance_for_differential_v1(state.balances),
        pools=admit_legacy_pool_map_for_differential_v1(state.pools),
        lp_balances=admit_legacy_lp_for_differential_v1(state.lp_balances),
        settlement=settlement,
        intents=[intent],
        context=exact_context.value,
    )
    assert type(legacy_result) is StrongSettlementStateCandidateV1
    assert not isinstance(legacy_result, StrongSettlementRejectV1)

    exact_candidate = exact_result.candidate.spot
    assert exact_candidate.balances == legacy_result.balances
    assert exact_candidate.pools == legacy_result.pools
    assert exact_candidate.lp_balances == legacy_result.lp_balances
