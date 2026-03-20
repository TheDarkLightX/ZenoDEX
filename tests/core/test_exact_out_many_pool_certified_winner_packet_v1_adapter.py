from __future__ import annotations

import pytest

from src.kernels.python.exact_out_many_pool_certified_winner_packet_v1_adapter import (
    check_exact_out_many_pool_certified_winner_packet_gate,
)


def test_exact_out_many_pool_certified_winner_packet_gate_accepts_only_when_both_inputs_pass() -> None:
    result = check_exact_out_many_pool_certified_winner_packet_gate(
        domain_contract_ok=True,
        guard_ok=True,
    )
    assert result.ok is True
    assert result.domain_contract_ok is True
    assert result.guard_ok is True
    assert result.error is None


def test_exact_out_many_pool_certified_winner_packet_gate_rejects_bad_domain_first() -> None:
    result = check_exact_out_many_pool_certified_winner_packet_gate(
        domain_contract_ok=False,
        guard_ok=True,
    )
    assert result.ok is False
    assert result.error == "bounded_candidate_domain_rejected"


def test_exact_out_many_pool_certified_winner_packet_gate_rejects_bad_guard() -> None:
    result = check_exact_out_many_pool_certified_winner_packet_gate(
        domain_contract_ok=True,
        guard_ok=False,
    )
    assert result.ok is False
    assert result.error == "many_pool_runtime_not_canonical_on_bounded_audit_domain"


def test_exact_out_many_pool_certified_winner_packet_gate_requires_bools() -> None:
    with pytest.raises(TypeError):
        check_exact_out_many_pool_certified_winner_packet_gate(  # type: ignore[arg-type]
            domain_contract_ok=1,
            guard_ok=True,
        )
    with pytest.raises(TypeError):
        check_exact_out_many_pool_certified_winner_packet_gate(  # type: ignore[arg-type]
            domain_contract_ok=True,
            guard_ok="no",
        )
