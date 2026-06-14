"""zUSD stability-pool absorption-coverage monitor (ADVISORY, read-only).

This module ships the zUSD twin of the perp funded-liquidation checker
(``src/core/perp_v2/invariants.py:inv_funded_liquidation``, recommendation R1).
It makes the documented stability-pool exit-spiral precondition an explicit,
machine-readable pre-disaster axis without touching settlement.

Background (``docs/MECHANISM_DESIGN_IMPROVEMENT_ANALYSIS.md`` section 6.2,
recommendation R7c): the deterministic ``liquidate`` path refuses outright when
the vault debt exceeds stability-pool debt::

    if state.debt_e8 > state.sp_debt_e8:  # src/core/zusd.py
        return ZUSDStepResult(ok=False, error="stability pool cannot absorb debt")

That all-or-nothing absorption rule, combined with same-epoch SP withdrawal,
admits the incentive-mediated insolvency spiral::

    vault approaches MCR -> SP depositors exit (allowed while TCR >= CCR)
    -> sp_debt < vault debt -> liquidation refused -> vault sinks further
    -> exit pressure increases -> SP empties -> insolvency dwell

By the supply-conservation invariant ``free_debt_e8 + sp_debt_e8 == debt_e8``
(``check_invariants`` -> ``inv_supply_conservation``) the absorption shortfall
``debt_e8 - sp_debt_e8`` is exactly the free (non-stability-pool) debt, which is
a monotone potential for the spiral: it is zero exactly when the whole vault is
stability-pool backed and strictly positive while any debt remains uninsured.

Everything here is a pure read-only projection of an existing ``ZUSDState``.
It is deliberately NOT wired into ``zusd.check_invariants`` or the ``step``
settlement path: enforcing coverage per transition would retroactively freeze
every vault carrying ordinary free debt, and the cooldown (R7a) and partial
absorption (R7b) fixes are paired Python+Rust settlement changes that are out
of scope for an advisory projection. The faithful binding this module DOES
provide is checked in ``tools/check_zusd_sp_absorption_coverage.py``: the
monitor's ``coverage_ok`` prediction equals the real ``zusd`` kernel's
liquidation-refusal decision on every liquidatable scenario.
"""

from __future__ import annotations

from dataclasses import asdict, dataclass
from typing import Any

from .zusd import ZUSDState, _mcr_ok

SP_ABSORPTION_COVERAGE_SCHEMA = "zenodex.zusd.sp_absorption_coverage.v0"

# Severity-ordered classification of the coverage axis. ``index`` is a small
# monotone severity rank (0 = safe, higher = closer to / in the disaster state).
CLASSIFICATION_SEVERITY: dict[str, int] = {
    "no_debt": 0,
    "covered": 0,
    "indeterminate_oracle": 1,
    "uninsurable_region": 2,
    "liquidation_blocked": 3,
}


@dataclass(frozen=True)
class SPAbsorptionCoverage:
    """Read-only stability-pool absorption-coverage projection of a vault."""

    schema: str
    has_debt: bool
    oracle_evaluable: bool
    vault_under_mcr: bool
    vault_debt_e8: int
    sp_absorption_capacity_e8: int
    under_mcr_debt_e8: int
    absorption_shortfall_e8: int
    coverage_ok: bool
    liquidation_blocked_by_sp: bool
    classification: str
    severity: int

    def to_dict(self) -> dict[str, Any]:
        return asdict(self)


def sp_absorption_coverage(state: ZUSDState) -> SPAbsorptionCoverage:
    """Project a ``ZUSDState`` onto the stability-pool absorption-coverage axis.

    Faithful to the kernel: ``vault_under_mcr`` uses the SAME predicate and the
    SAME ``price_pending_e8`` the ``liquidate`` guard uses, and ``coverage_ok``
    is the negation of the kernel's ``debt_e8 > sp_debt_e8`` refusal condition.
    """
    has_debt = state.debt_e8 > 0
    # liquidate() reads the pending price and requires it positive + oracle seen.
    oracle_evaluable = state.oracle_seen and state.price_pending_e8 > 0

    vault_under_mcr = (
        has_debt
        and oracle_evaluable
        and not _mcr_ok(
            collateral_e8=state.collateral_e8,
            debt_e8=state.debt_e8,
            price_e8=state.price_pending_e8,
            mcr_bps=state.mcr_bps,
        )
    )

    capacity = state.sp_debt_e8
    under_mcr_debt = state.debt_e8 if vault_under_mcr else 0
    shortfall = max(0, state.debt_e8 - capacity) if has_debt else 0
    # Negation of the kernel refusal `debt_e8 > sp_debt_e8` (vacuously true with
    # no debt). By supply conservation this is exactly `free_debt_e8 == 0`.
    coverage_ok = (not has_debt) or (state.debt_e8 <= capacity)
    liquidation_blocked_by_sp = vault_under_mcr and (state.debt_e8 > capacity)

    if not has_debt:
        classification = "no_debt"
    elif not oracle_evaluable:
        # Cannot price the MCR trigger; fail-closed to an indeterminate signal
        # rather than asserting coverage.
        classification = "indeterminate_oracle"
    elif coverage_ok:
        classification = "covered"
    elif vault_under_mcr:
        classification = "liquidation_blocked"
    else:
        classification = "uninsurable_region"

    return SPAbsorptionCoverage(
        schema=SP_ABSORPTION_COVERAGE_SCHEMA,
        has_debt=has_debt,
        oracle_evaluable=oracle_evaluable,
        vault_under_mcr=vault_under_mcr,
        vault_debt_e8=state.debt_e8,
        sp_absorption_capacity_e8=capacity,
        under_mcr_debt_e8=under_mcr_debt,
        absorption_shortfall_e8=shortfall,
        coverage_ok=coverage_ok,
        liquidation_blocked_by_sp=liquidation_blocked_by_sp,
        classification=classification,
        severity=CLASSIFICATION_SEVERITY[classification],
    )


def liquidation_blocked_by_sp(state: ZUSDState) -> bool:
    """True iff the vault is the acute §6.2 disaster precursor.

    The vault is under MCR (so liquidation is eligible at the pending price) yet
    the stability pool cannot absorb it, so the deterministic kernel refuses the
    liquidation and the vault is stranded below maintenance. This is the
    monitored pre-disaster state, not a settlement enforcement point.
    """
    return sp_absorption_coverage(state).liquidation_blocked_by_sp


def sp_absorption_coverage_clear(state: ZUSDState) -> bool:
    """ADVISORY monitor predicate (True == not in the acute disaster precursor).

    Mirrors ``inv_funded_liquidation`` as an advisory projection rather than an
    enforced invariant. It returns False exactly for the ``liquidation_blocked``
    class. Lean anchor for the absorption defense that this axis monitors:
    ``Proofs.CBCDisasterStateRefactors`` (stability-pool extraction closure) and
    the disaster-class analysis in
    ``docs/MECHANISM_DESIGN_IMPROVEMENT_ANALYSIS.md`` (R7).

    Deliberately NOT in ``zusd.check_invariants`` / the ``step`` settlement
    path: per-transition enforcement would freeze every vault that carries
    ordinary free (non-SP) debt, since coverage holds only when the entire
    vault is stability-pool backed.
    """
    return not liquidation_blocked_by_sp(state)
