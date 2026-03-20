from __future__ import annotations

from dataclasses import dataclass


def _require_bool(name: str, value: object) -> bool:
    if not isinstance(value, bool):
        raise TypeError(f"{name} must be a bool")
    return value


@dataclass(frozen=True)
class ExactOutManyPoolCertifiedWinnerPacketGateResult:
    ok: bool
    domain_contract_ok: bool
    guard_ok: bool
    error: str | None = None


def check_exact_out_many_pool_certified_winner_packet_gate(
    *,
    domain_contract_ok: bool,
    guard_ok: bool,
) -> ExactOutManyPoolCertifiedWinnerPacketGateResult:
    domain_contract_ok = _require_bool("domain_contract_ok", domain_contract_ok)
    guard_ok = _require_bool("guard_ok", guard_ok)

    if not domain_contract_ok:
        return ExactOutManyPoolCertifiedWinnerPacketGateResult(
            ok=False,
            domain_contract_ok=False,
            guard_ok=guard_ok,
            error="bounded_candidate_domain_rejected",
        )
    if not guard_ok:
        return ExactOutManyPoolCertifiedWinnerPacketGateResult(
            ok=False,
            domain_contract_ok=True,
            guard_ok=False,
            error="many_pool_runtime_not_canonical_on_bounded_audit_domain",
        )
    return ExactOutManyPoolCertifiedWinnerPacketGateResult(
        ok=True,
        domain_contract_ok=True,
        guard_ok=True,
        error=None,
    )
