"""Account attribution and non-reopening terminal episodes for margin V2."""

from dataclasses import replace

from .global_economic_state_v2 import GlobalEconomicStateV2
from .global_settlement_types_v2 import (
    LaneIdV2,
    TerminalObligationStatusV2,
    TerminalObligationV2,
)
from .perps_margin_state_v2 import (
    PerpsMarginClaimBindingV2,
    PerpsMarginStateV2,
    margin_claim_id_v2,
)
from .perps_margin_types_v1 import PERPS_MARGIN_CUSTODY_DOMAIN_V1, PerpsMarginStateV1


def require_margin_claim_projection_v2(
    margin: PerpsMarginStateV2, state: GlobalEconomicStateV2,
) -> None:
    """Require exact custody, owner liabilities and active claim attribution."""

    economic = margin.economic_state
    root = next(row for row in state.lane_roots if row.lane_id is LaneIdV2.PERPS_MARKET)
    if (root.state_root, root.module_release_id, root.enabled) != (
        margin.state_root, economic.module_release_id, True,
    ):
        raise ValueError("margin lane/global root mismatch")
    domain = PERPS_MARGIN_CUSTODY_DOMAIN_V1
    custody = {
        (economic.collateral_asset, account.account_id, domain): account.collateral_atoms
        for account in economic.accounts if account.collateral_atoms
    }
    actual_custody = {
        row.key: row.amount_atoms for row in state.custody if row.custody_domain == domain
    }
    liabilities: dict[tuple[str, str, str], int] = {}
    for account in economic.accounts:
        if account.collateral_atoms:
            key = (economic.collateral_asset, account.owner, domain)
            liabilities[key] = liabilities.get(key, 0) + account.collateral_atoms
    actual_liabilities = {
        row.key: row.amount_atoms for row in state.liabilities if row.custody_domain == domain
    }
    if custody != actual_custody or liabilities != actual_liabilities:
        raise ValueError("margin account custody or claimant liability mismatch")
    claims = {
        row.obligation_id: row for row in state.terminal_obligations
        if row.lane_id is LaneIdV2.PERPS_MARKET
        and row.status is TerminalObligationStatusV2.OPEN
    }
    bindings = margin.active_claims
    if set(claims) != {row.obligation_id for row in bindings}:
        raise ValueError("margin open claim coverage mismatch")
    accounts = {row.account_id: row for row in economic.accounts}
    for binding in bindings:
        account = accounts[binding.account_id]
        claim = claims[binding.obligation_id]
        if (claim.claimant, claim.asset, claim.liability_domain, claim.amount_atoms) != (
            account.owner, economic.collateral_asset, domain, account.collateral_atoms,
        ):
            raise ValueError("margin active claim attribution mismatch")


def advance_margin_claims_v2(
    margin: PerpsMarginStateV2,
    post_economic: PerpsMarginStateV1,
    obligations: tuple[TerminalObligationV2, ...],
    account_id: str,
    occurrence_id: str,
) -> tuple[PerpsMarginStateV2, tuple[TerminalObligationV2, ...]]:
    """Advance the selected account after the core checks its predecessor.

    The calling producer recomputes the economic transition and checks complete
    pre/post projections. This helper accepts no receipt or authority witness.
    """

    account = post_economic.account(account_id)
    if account is None:
        raise ValueError("margin successor lost its selected account")
    rows = {row.obligation_id: row for row in obligations}
    bindings = {row.account_id: row for row in margin.active_claims}
    previous = bindings.get(account_id)
    if previous is not None:
        old = rows[previous.obligation_id]
        if account.collateral_atoms:
            rows[old.obligation_id] = replace(old, amount_atoms=account.collateral_atoms)
        else:
            rows[old.obligation_id] = replace(old, status=TerminalObligationStatusV2.DRAINED)
            del bindings[account_id]
    elif account.collateral_atoms:
        claim_id = margin_claim_id_v2(margin.economic_state, account_id, occurrence_id)
        if claim_id in rows:
            raise ValueError("margin opening claim id already exists")
        rows[claim_id] = TerminalObligationV2(
            claim_id, LaneIdV2.PERPS_MARKET, account.owner,
            post_economic.collateral_asset, PERPS_MARGIN_CUSTODY_DOMAIN_V1,
            account.collateral_atoms, TerminalObligationStatusV2.OPEN,
        )
        bindings[account_id] = PerpsMarginClaimBindingV2(account_id, claim_id)
    return (
        PerpsMarginStateV2(post_economic, tuple(bindings[key] for key in sorted(bindings))),
        tuple(rows[key] for key in sorted(rows)),
    )
