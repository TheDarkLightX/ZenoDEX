from __future__ import annotations

from dataclasses import replace
from typing import Any

import pytest

import src.core.fcis_step_evaluator as fcis_step_evaluator
from src.core.batch_clearing import compute_settlement
from src.core.dex import DexState
from src.core.fcis_state_read_trace_v5 import FCISStateReadTraceV5
from src.core.fcis_step_evaluation_values import (
    FCISStepEvaluationOkV1,
    FCISStepEvaluationPhaseV1,
    FCISStepEvaluationRejectV1,
)
from src.core.fcis_step_evaluator import (
    FCIS_STEP_EVALUATOR_UNMOUNTED_V1,
    evaluate_fcis_step_candidate_v1,
)
from src.core.fcis_support_profile_constants_v5 import FCIS_SUPPORT_PROFILE_ID_V5
from src.core.liquidity import create_pool
from src.core.oracle import OracleState
from src.core.perps import PERPS_STATE_VERSION_V4, PerpsState
from src.core.settlement import Settlement
from src.core.settlement_snapshots import snapshot_settlement
from src.core.vault import VaultState
from src.state import BalanceTable, LPTable
from src.state.canonical import domain_sep_bytes, sha256_hex
from src.state.committed_dex_snapshot import (
    canonical_snapshot_bytes_from_committed_state_v1,
)
from src.state.fcis_committed_state_values import (
    FCISCommittedStateSourceV1,
    FCISCommittedStateV1,
)
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


def _state_source(state: DexState) -> FCISCommittedStateSourceV1:
    return FCISCommittedStateSourceV1(
        balances=admit_legacy_balance_for_differential_v1(state.balances),
        pools=admit_legacy_pool_map_for_differential_v1(state.pools),
        lp_balances=admit_legacy_lp_for_differential_v1(state.lp_balances),
        nonces=admit_legacy_nonce_for_differential_v1(state.nonces),
        vault=snapshot_vault(state.vault),
        oracle=snapshot_oracle(state.oracle),
        fee_accumulator=snapshot_fee_accumulator(state.fee_accumulator),
        perps=snapshot_perps(state.perps),
    )


def _state_root_preimage(
    state: FCISCommittedStateV1,
    snapshot_version: int,
) -> bytes:
    snapshot_bytes = canonical_snapshot_bytes_from_committed_state_v1(
        version=snapshot_version,
        balances=state.balances,
        pools=state.pools,
        lp_balances=state.lp_balances,
        nonces=state.nonces,
        fee_accumulator=state.fee_accumulator,
        vault=state.vault,
        oracle=state.oracle,
        perps=state.perps,
    )
    return domain_sep_bytes("dex_snapshot", version=snapshot_version) + snapshot_bytes


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
        state_source=_state_source(state),
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
    assert candidate.balance_patch is not None
    assert candidate.pool_patch is not None
    assert candidate.lp_patch is None
    assert candidate.nonce_patch is not None
    assert candidate.fee_allocation is not None
    assert candidate.state.nonces.get_last(intent.sender_pubkey) == 1
    assert admit_legacy_balance_for_differential_v1(state.balances) == pre_balances
    assert admit_legacy_pool_map_for_differential_v1(state.pools) == pre_pools
    assert admit_legacy_nonce_for_differential_v1(state.nonces) == pre_nonces


def test_evidence_binds_same_candidate_context_and_pre_post_roots() -> None:
    state, intent, settlement = _swap_case()
    context = _context_source()

    first = _evaluate(state, settlement, [intent], context)
    second = _evaluate(state, settlement, [intent], context)

    assert type(first) is FCISStepEvaluationOkV1
    pre_root_preimage = _state_root_preimage(first.material.pre_state, context.snapshot_version)
    assert first == second
    candidate = first.candidate
    evidence = first.evidence
    assert evidence.pre_state_root_preimage == pre_root_preimage
    assert evidence.support_profile_id == FCIS_SUPPORT_PROFILE_ID_V5
    assert evidence.support_root != evidence.support_set_commitment
    assert len(evidence.support_root) == 66
    assert len(evidence.support_set_commitment) == 66
    assert evidence.post_state_root_preimage == _state_root_preimage(candidate.state, 4)
    retained_context_bytes = evidence.execution_context_bytes
    assert evidence.pre_state_root == sha256_hex(pre_root_preimage)
    assert evidence.post_state_root == sha256_hex(evidence.post_state_root_preimage)
    assert evidence.snapshot_commitment == evidence.post_state_root
    object.__setattr__(context.settlement, "now", 999_999)
    assert evidence.execution_context_bytes == retained_context_bytes


def test_full_state_root_binds_vault_oracle_and_perps() -> None:
    state, intent, settlement = _swap_case()
    result = _evaluate(state, settlement, [intent], _context_source())
    assert type(result) is FCISStepEvaluationOkV1
    pre_state = result.material.pre_state
    version = result.evidence.snapshot_version
    base_preimage = _state_root_preimage(pre_state, version)
    vault = snapshot_vault(VaultState(1, 0, 0, 0, 0))
    oracle = snapshot_oracle(OracleState(123, 300))
    perps = snapshot_perps(PerpsState(version=PERPS_STATE_VERSION_V4, markets={}))
    assert vault is not None
    assert oracle is not None
    assert perps is not None
    changed_preimages = {
        _state_root_preimage(replace(pre_state, vault=vault), version),
        _state_root_preimage(replace(pre_state, oracle=oracle), version),
        _state_root_preimage(replace(pre_state, perps=perps), version),
    }
    assert base_preimage not in changed_preimages
    assert len(changed_preimages) == 3


def test_evaluator_rejects_wrong_aggregate_map_before_later_fields() -> None:
    state, intent, settlement = _swap_case()
    source = replace(_state_source(state), pools=[])
    result = evaluate_fcis_step_candidate_v1(
        state_source=source,
        settlement=snapshot_settlement(settlement),
        intents=admit_intent_batch([intent]),
        context=_context_source(),
    )
    assert type(result) is FCISStepEvaluationRejectV1
    assert result.phase is FCISStepEvaluationPhaseV1.STATE_ADMISSION
    assert result.code == "wrong_container"
    assert result.path == ("pools",)


def test_success_result_rejects_cross_evaluation_splice() -> None:
    state, intent, settlement = _swap_case()
    first = _evaluate(state, settlement, [intent], _context_source())
    second_context = replace(_context_source(), fee_split_policy=None)
    second = _evaluate(state, settlement, [intent], second_context)
    assert type(first) is FCISStepEvaluationOkV1
    assert type(second) is FCISStepEvaluationOkV1
    with pytest.raises(TypeError, match="controlled constructor"):
        FCISStepEvaluationOkV1(
            first.material,
            second.candidate,
            second.evidence,
            object(),
        )


def test_exact_step_consumers_share_one_admitted_command_graph(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    state, intent, settlement = _swap_case()
    observed: dict[str, int] = {}

    original_nonce = fcis_step_evaluator._validate_and_apply_intent_nonce_batch_admitted_observed_v5
    original_settlement = fcis_step_evaluator._evaluate_settlement_strong_admitted_observed_v5
    original_fees = fcis_step_evaluator._total_settlement_fees_v1
    original_support = fcis_step_evaluator._compute_fcis_support_root_v5_admitted

    def nonce_spy(**kwargs: Any):
        observed["nonce_intents"] = id(kwargs["intents"])
        return original_nonce(**kwargs)

    def settlement_spy(**kwargs: Any):
        observed["settlement"] = id(kwargs["settlement"])
        observed["settlement_intents"] = id(kwargs["intents"])
        return original_settlement(**kwargs)

    def fee_spy(settlement_value: Any):
        observed["fee_settlement"] = id(settlement_value)
        return original_fees(settlement_value)

    def support_spy(**kwargs: Any):
        observed["support_settlement"] = id(kwargs["settlement"])
        observed["support_intents"] = id(kwargs["intents"])
        return original_support(**kwargs)

    monkeypatch.setattr(
        fcis_step_evaluator,
        "_validate_and_apply_intent_nonce_batch_admitted_observed_v5",
        nonce_spy,
    )
    monkeypatch.setattr(
        fcis_step_evaluator,
        "_evaluate_settlement_strong_admitted_observed_v5",
        settlement_spy,
    )
    monkeypatch.setattr(fcis_step_evaluator, "_total_settlement_fees_v1", fee_spy)
    monkeypatch.setattr(
        fcis_step_evaluator,
        "_compute_fcis_support_root_v5_admitted",
        support_spy,
    )

    result = _evaluate(state, settlement, [intent], _context_source())

    assert type(result) is FCISStepEvaluationOkV1
    assert observed["settlement"] == observed["fee_settlement"]
    assert observed["settlement"] == observed["support_settlement"]
    assert (
        len(
            {
                observed["nonce_intents"],
                observed["settlement_intents"],
                observed["support_intents"],
            }
        )
        == 1
    )


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
        state_source=replace(_state_source(state), perps=exact_perps),
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
        "src.core.fcis_step_evaluator._evaluate_spot_observed_v5",
        lambda **_kwargs: (object(), FCISStateReadTraceV5()),
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
        state_source=_state_source(state),
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
        state_source=_state_source(state),
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
        state_source=_state_source(state),
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
    assert result.candidate.state.nonces.get_last(intent.sender_pubkey) == 1
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

    exact_candidate = exact_result.candidate.state
    assert exact_candidate.balances == legacy_result.balances
    assert exact_candidate.pools == legacy_result.pools
    assert exact_candidate.lp_balances == legacy_result.lp_balances
