from __future__ import annotations

from dataclasses import replace

import pytest

from src.core.global_settlement_types_v1 import hash_global_v1
from src.core.global_settlement_types_v2 import (
    GLOBAL_SETTLEMENT_ABI_V2,
    MAX_ORACLE_OCCURRENCE_DELTAS_PER_PLAN_V2,
    MAX_TERMINAL_OBLIGATION_DELTAS_PER_PLAN_V2,
    ZERO_ROOT_V2,
    GlobalOracleOccurrencePlanV2,
    GlobalTerminalObligationPlanV2,
    LaneIdV2,
    OracleOccurrenceDeltaV2,
    OracleOccurrenceStateV2,
    TerminalObligationDeltaV2,
    TerminalObligationStatusV2,
    TerminalObligationV2,
    canonical_global_bytes_v2,
    hash_global_v2,
)


def _root(label: str) -> str:
    return hash_global_v2("test-root-v2", {"label": label})


def _obligation(
    obligation_id: str = "obligation:1",
    *,
    amount_atoms: int = 10,
    status: TerminalObligationStatusV2 = TerminalObligationStatusV2.OPEN,
) -> TerminalObligationV2:
    return TerminalObligationV2(
        obligation_id=obligation_id,
        lane_id=LaneIdV2.PERPS_MARKET,
        claimant="alice",
        asset="USD",
        liability_domain="perps:margin",
        amount_atoms=amount_atoms,
        status=status,
    )


def _oracle(oracle_id: str = "oracle:1", *, height: int = 7) -> OracleOccurrenceStateV2:
    return OracleOccurrenceStateV2(
        oracle_id=oracle_id,
        occurrence_root=_root(f"occurrence:{oracle_id}:{height}"),
        observed_height=height,
        finalized=True,
    )


def test_v2_hash_domain_is_disjoint_from_v1_for_the_same_payload() -> None:
    payload = {"asset": "USD", "amount_atoms": 1}

    assert canonical_global_bytes_v2(payload) == (b'{"amount_atoms":1,"asset":"USD"}')
    assert hash_global_v2("shared-shape", payload) != hash_global_v1(
        "shared-shape",
        payload,
    )
    assert GLOBAL_SETTLEMENT_ABI_V2.endswith("/v2")


def test_canonical_encoder_rejects_scalar_and_sequence_subclasses() -> None:
    class HostileInt(int):
        pass

    class HostileTuple(tuple[object, ...]):
        pass

    with pytest.raises(TypeError, match="scalar subclasses"):
        canonical_global_bytes_v2(HostileInt(1))
    with pytest.raises(TypeError, match="sequence subclasses"):
        canonical_global_bytes_v2(HostileTuple(("x",)))


def test_terminal_obligation_identity_includes_liability_domain() -> None:
    before = _obligation()
    after = replace(before, amount_atoms=7)
    delta = TerminalObligationDeltaV2(before.obligation_id, before, after)
    plan = GlobalTerminalObligationPlanV2((delta,))

    assert plan.plan_root != ZERO_ROOT_V2
    with pytest.raises(ValueError, match="identity fields are immutable"):
        TerminalObligationDeltaV2(
            before.obligation_id,
            before,
            replace(after, liability_domain="other:liability"),
        )


def test_terminal_obligation_creation_and_terminal_transition_are_closed() -> None:
    created = _obligation()
    assert TerminalObligationDeltaV2(created.obligation_id, None, created)

    terminal = replace(created, status=TerminalObligationStatusV2.DRAINED)
    assert TerminalObligationDeltaV2(created.obligation_id, created, terminal)
    with pytest.raises(ValueError, match="must begin open"):
        TerminalObligationDeltaV2(terminal.obligation_id, None, terminal)
    with pytest.raises(ValueError, match="preserve the final open amount"):
        TerminalObligationDeltaV2(
            created.obligation_id,
            created,
            replace(terminal, amount_atoms=9),
        )


def test_terminal_plan_empty_root_and_bound_are_exact() -> None:
    assert GlobalTerminalObligationPlanV2.empty().plan_root == ZERO_ROOT_V2
    deltas = tuple(
        TerminalObligationDeltaV2(
            f"obligation:{index:03d}",
            None,
            _obligation(f"obligation:{index:03d}"),
        )
        for index in range(MAX_TERMINAL_OBLIGATION_DELTAS_PER_PLAN_V2 + 1)
    )
    with pytest.raises(ValueError, match="bounded shape"):
        GlobalTerminalObligationPlanV2(deltas)


def test_oracle_plan_binds_pre_and_post_occurrence() -> None:
    before = _oracle(height=7)
    after = _oracle(height=8)
    delta = OracleOccurrenceDeltaV2(before.oracle_id, before, after)
    plan = GlobalOracleOccurrencePlanV2((delta,))

    assert plan.plan_root != ZERO_ROOT_V2
    with pytest.raises(ValueError, match="height cannot regress"):
        OracleOccurrenceDeltaV2(before.oracle_id, after, before)
    with pytest.raises(ValueError, match="immutable at one observed height"):
        OracleOccurrenceDeltaV2(
            before.oracle_id,
            before,
            replace(before, occurrence_root=_root("other-occurrence")),
        )


def test_oracle_plan_empty_root_and_bound_are_exact() -> None:
    assert GlobalOracleOccurrencePlanV2.empty().plan_root == ZERO_ROOT_V2
    deltas = tuple(
        OracleOccurrenceDeltaV2(
            f"oracle:{index:03d}",
            None,
            _oracle(f"oracle:{index:03d}"),
        )
        for index in range(MAX_ORACLE_OCCURRENCE_DELTAS_PER_PLAN_V2 + 1)
    )
    with pytest.raises(ValueError, match="bounded shape"):
        GlobalOracleOccurrencePlanV2(deltas)
