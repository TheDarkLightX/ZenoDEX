from __future__ import annotations

from dataclasses import FrozenInstanceError
from types import MappingProxyType

import pytest

from src.core.fcis_settlement_strong_values import (
    ExactSpotPreStateV1,
    ExactStrongSettlementCandidateV1,
    ExactStrongSettlementObservedV1,
    ExactStrongSettlementRejectV1,
    StrongSettlementContextV1,
    _candidate_from_exact_strong_validator_v1,
    _observed_from_exact_strong_validator_v1,
    _reject_from_exact_strong_validator_v1,
)
from src.core.fcis_state_read_trace_v5 import FCISStateReadTraceV5
from src.state.balances import BalanceTable
from src.state.fcis_execution_context import admit_fcis_settlement_execution_context_v1
from src.state.fcis_execution_context_values import (
    FCISSettlementExecutionContextSourceV1,
    FCISSettlementExecutionContextV1,
    FCISSettlementModeV1,
)
from src.state.lp import LPTable
from src.state.lp_duration_policy_values import LPDurationRiskPolicyV1
from src.state.snapshot_combinators import AdmitOk
from src.state.state_snapshot_values import (
    CommittedBalanceTableV1,
)
from src.state.state_snapshots import (
    snapshot_balance_table,
    snapshot_lp_table,
    snapshot_pool_map,
)


def _empty_pre_state() -> ExactSpotPreStateV1:
    return ExactSpotPreStateV1(
        balances=snapshot_balance_table(BalanceTable()),
        pools=snapshot_pool_map({}),
        lp_balances=snapshot_lp_table(LPTable()),
    )


def _settlement_context(
    *,
    mode: FCISSettlementModeV1 = FCISSettlementModeV1.STRONG_REPLAY,
    allow_cow_netting: bool = False,
    allow_snapshot_bound_quote_bindings: bool = False,
    protocol_fee_share_bps: int = 0,
    protocol_fee_recipient_pubkey: str | None = None,
    now: int = 0,
    min_lp_position_age_seconds: int = 0,
) -> FCISSettlementExecutionContextV1:
    admitted = admit_fcis_settlement_execution_context_v1(
        FCISSettlementExecutionContextSourceV1(
            now=now,
            min_lp_position_age_seconds=min_lp_position_age_seconds,
            mode=mode,
            allow_cow_netting=allow_cow_netting,
            allow_snapshot_bound_quote_bindings=allow_snapshot_bound_quote_bindings,
            protocol_fee_share_bps=protocol_fee_share_bps,
            protocol_fee_recipient_pubkey=protocol_fee_recipient_pubkey,
        )
    )
    assert type(admitted) is AdmitOk
    return admitted.value


def test_context_composes_the_existing_closed_settlement_context() -> None:
    context = StrongSettlementContextV1(
        settlement=_settlement_context(),
        lp_duration_policy=None,
    )

    assert context.settlement.now == 0
    with pytest.raises((FrozenInstanceError, AttributeError)):
        context.settlement = _settlement_context(now=1)  # type: ignore[misc]


def test_context_revalidates_hostile_nested_mutation() -> None:
    settlement = _settlement_context()
    object.__setattr__(settlement, "protocol_fee_share_bps", 10_001)

    with pytest.raises(TypeError, match="fee"):
        StrongSettlementContextV1(
            settlement=settlement,
            lp_duration_policy=None,
        )


def test_context_rejects_open_values_and_accepts_exact_duration_policy() -> None:
    with pytest.raises(TypeError):
        StrongSettlementContextV1(
            settlement=object(),  # type: ignore[arg-type]
            lp_duration_policy=None,
        )
    with pytest.raises(TypeError):
        StrongSettlementContextV1(
            settlement=_settlement_context(),
            lp_duration_policy=object(),  # type: ignore[arg-type]
        )

    policy = LPDurationRiskPolicyV1()
    context = StrongSettlementContextV1(
        settlement=_settlement_context(
            mode=FCISSettlementModeV1.STRONG_PROOF_CARRYING,
            allow_cow_netting=True,
            allow_snapshot_bound_quote_bindings=True,
            protocol_fee_share_bps=10_000,
            protocol_fee_recipient_pubkey="0x" + "12" * 48,
            now=1,
            min_lp_position_age_seconds=1,
        ),
        lp_duration_policy=policy,
    )
    assert context.lp_duration_policy is policy


def test_exact_pre_state_rejects_legacy_or_wrong_exact_values() -> None:
    state = _empty_pre_state()
    assert type(state.balances) is CommittedBalanceTableV1

    for field, value in (
        ("balances", object()),
        ("pools", {}),
        ("lp_balances", object()),
    ):
        kwargs = {
            "balances": state.balances,
            "pools": state.pools,
            "lp_balances": state.lp_balances,
        }
        kwargs[field] = value
        with pytest.raises(TypeError):
            ExactSpotPreStateV1(**kwargs)  # type: ignore[arg-type]


def test_candidate_reject_and_observed_values_require_controlled_derivation() -> None:
    state = _empty_pre_state()

    with pytest.raises(TypeError):
        ExactStrongSettlementCandidateV1(  # type: ignore[call-arg]
            balances=state.balances,
            pools=state.pools,
            lp_balances=state.lp_balances,
            balance_patch=None,
            pool_patch=None,
            lp_patch=None,
        )
    with pytest.raises(TypeError):
        ExactStrongSettlementRejectV1(reason="reject")  # type: ignore[call-arg]

    reject = _reject_from_exact_strong_validator_v1("reject")
    with pytest.raises(TypeError):
        ExactStrongSettlementObservedV1(  # type: ignore[call-arg]
            result=reject,
            state_read_trace=FCISStateReadTraceV5(),
        )


def test_controlled_values_form_one_candidate_or_reject_with_one_trace() -> None:
    state = _empty_pre_state()
    candidate = _candidate_from_exact_strong_validator_v1(
        balances=state.balances,
        pools=state.pools,
        lp_balances=state.lp_balances,
        balance_patch=None,
        pool_patch=None,
        lp_patch=None,
    )
    rejected = _reject_from_exact_strong_validator_v1("reason")
    accepted_observed = _observed_from_exact_strong_validator_v1(
        candidate,
        FCISStateReadTraceV5(),
    )
    rejected_observed = _observed_from_exact_strong_validator_v1(
        rejected,
        FCISStateReadTraceV5(),
    )

    assert accepted_observed.result is candidate
    assert rejected_observed.result is rejected
    assert not hasattr(rejected, "balances")
    assert not hasattr(rejected, "balance_patch")


def test_hostile_nested_map_mutation_is_detectable_by_reconstruction() -> None:
    state = _empty_pre_state()
    object.__setattr__(state.pools, "_schema_id", "attacker/schema")

    with pytest.raises(TypeError, match="schema"):
        ExactSpotPreStateV1(
            balances=state.balances,
            pools=state.pools,
            lp_balances=state.lp_balances,
        )


def test_hostile_hidden_pool_index_entry_is_rejected() -> None:
    state = _empty_pre_state()
    object.__setattr__(
        state.pools,
        "_index",
        MappingProxyType({"hidden": object()}),
    )

    with pytest.raises(TypeError, match="structure"):
        ExactSpotPreStateV1(
            balances=state.balances,
            pools=state.pools,
            lp_balances=state.lp_balances,
        )
