"""Deterministic SHADOW core for perps margin accounting.

Accepted outputs are candidate lane effects and terminal obligations. They are
not route-complete: no lane coordinator currently supplies whole-state
conservation or applies terminal-table updates. Consequently this module has no
settlement, proof-verification, mount, or publication authority.
"""

from __future__ import annotations

from dataclasses import replace

from .global_economic_proof_v1 import LaneModuleTransitionJournalV1
from .global_settlement_types_v1 import (
    MAX_ATOMS_V1,
    MAX_DELTA_ATOMS_V1,
    MAX_U64_V1,
    EconomicEffectKindV1,
    EconomicEffectRowV1,
    GlobalEconomicEffectPlanV1,
    LaneIdV1,
    LaneWriteV1,
    hash_global_v1,
)
from .perps_margin_types_v1 import (
    ACCOUNT_CUSTODY_DOMAIN_V1,
    BPS_SCALE_V1,
    MAX_PERPS_MARGIN_ACCOUNTS_V1,
    PERPS_MARGIN_CLOSE_COMMAND_KIND_V1,
    PERPS_MARGIN_CUSTODY_DOMAIN_V1,
    PERPS_MARGIN_DEPOSIT_COMMAND_KIND_V1,
    PERPS_MARGIN_MODULE_INPUT_SCHEMA_V1,
    PERPS_MARGIN_MODULE_SCHEMA_V1,
    PERPS_MARGIN_WITHDRAW_COMMAND_KIND_V1,
    PerpsMarginAcceptedV1,
    PerpsMarginAccountStatusV1,
    PerpsMarginAccountV1,
    PerpsMarginCommandV1,
    PerpsMarginContextV1,
    PerpsMarginMarketStatusV1,
    PerpsMarginPrivatePortV1,
    PerpsMarginRejectCodeV1,
    PerpsMarginRejectedV1,
    PerpsMarginResultV1,
    PerpsMarginStateV1,
    _perps_margin_receipt_root_v1,
)

_SUPPORTED_COMMANDS = frozenset(
    {
        PERPS_MARGIN_DEPOSIT_COMMAND_KIND_V1,
        PERPS_MARGIN_WITHDRAW_COMMAND_KIND_V1,
        PERPS_MARGIN_CLOSE_COMMAND_KIND_V1,
    }
)


def _reject(
    code: PerpsMarginRejectCodeV1,
    pre_state: PerpsMarginStateV1,
) -> PerpsMarginRejectedV1:
    return PerpsMarginRejectedV1(
        code=code,
        pre_state_root=pre_state.state_root,
        post_state_root=pre_state.state_root,
        effects=GlobalEconomicEffectPlanV1.empty(),
    )


def _next_nonce(account: PerpsMarginAccountV1 | None) -> int | PerpsMarginRejectCodeV1:
    current = 0 if account is None else account.nonce
    if current == MAX_U64_V1:
        return PerpsMarginRejectCodeV1.NONCE_OVERFLOW
    return current + 1


def _maintenance_requirement(
    state: PerpsMarginStateV1,
    position_base: int,
) -> int | PerpsMarginRejectCodeV1:
    risk_bps = state.maintenance_margin_bps + state.depeg_buffer_bps
    numerator = abs(position_base) * state.index_price_e8 * risk_bps
    if numerator > MAX_ATOMS_V1:
        return PerpsMarginRejectCodeV1.ARITHMETIC_OVERFLOW
    quotient, remainder = divmod(numerator, BPS_SCALE_V1)
    return quotient + int(remainder != 0)


def _replace_account(
    state: PerpsMarginStateV1,
    account: PerpsMarginAccountV1,
) -> PerpsMarginStateV1:
    accounts = {
        existing.account_id: existing
        for existing in state.accounts
    }
    accounts[account.account_id] = account
    return PerpsMarginStateV1(
        module_release_id=state.module_release_id,
        market_id=state.market_id,
        collateral_asset=state.collateral_asset,
        index_price_e8=state.index_price_e8,
        maintenance_margin_bps=state.maintenance_margin_bps,
        depeg_buffer_bps=state.depeg_buffer_bps,
        max_position_abs=state.max_position_abs,
        market_status=state.market_status,
        accounts=tuple(accounts[key] for key in sorted(accounts)),
    )


def _common_policy_reject(
    context: PerpsMarginContextV1,
    state: PerpsMarginStateV1,
    command: PerpsMarginCommandV1,
) -> PerpsMarginRejectCodeV1 | None:
    if context.module_release_id != state.module_release_id:
        return PerpsMarginRejectCodeV1.RELEASE_MISMATCH
    if command.command_kind not in _SUPPORTED_COMMANDS:
        return PerpsMarginRejectCodeV1.UNKNOWN_COMMAND
    if state.market_status is PerpsMarginMarketStatusV1.HALTED:
        return PerpsMarginRejectCodeV1.HALTED_MARKET
    if (
        state.market_status is PerpsMarginMarketStatusV1.DRAIN_ONLY
        and command.command_kind == PERPS_MARGIN_DEPOSIT_COMMAND_KIND_V1
    ):
        return PerpsMarginRejectCodeV1.MARKET_DRAIN_ONLY
    if command.market_id != state.market_id:
        return PerpsMarginRejectCodeV1.MARKET_MISMATCH
    if command.asset != state.collateral_asset:
        return PerpsMarginRejectCodeV1.ASSET_MISMATCH
    if command.owner != context.subject_id:
        return PerpsMarginRejectCodeV1.UNAUTHORIZED_SUBJECT
    if command.command_kind != PERPS_MARGIN_WITHDRAW_COMMAND_KIND_V1 and context.has_oracle_authority:
        return PerpsMarginRejectCodeV1.UNEXPECTED_ORACLE_AUTHORITY
    return None


def _oracle_policy_reject(
    context: PerpsMarginContextV1,
    state: PerpsMarginStateV1,
    command: PerpsMarginCommandV1,
    account: PerpsMarginAccountV1,
) -> PerpsMarginRejectCodeV1 | None:
    if command.command_kind != PERPS_MARGIN_WITHDRAW_COMMAND_KIND_V1:
        return None
    if account.position_base == 0:
        return (
            PerpsMarginRejectCodeV1.UNEXPECTED_ORACLE_AUTHORITY
            if context.has_oracle_authority
            else None
        )
    if not context.has_oracle_authority:
        return PerpsMarginRejectCodeV1.ORACLE_AUTHORITY_MISSING
    if context.oracle_price_e8 != state.index_price_e8:
        return PerpsMarginRejectCodeV1.ORACLE_PRICE_MISMATCH
    return None


def _prepare_account(
    state: PerpsMarginStateV1,
    command: PerpsMarginCommandV1,
) -> PerpsMarginAccountV1 | PerpsMarginRejectCodeV1:
    account = state.account(command.account_id)
    if account is None and command.command_kind != PERPS_MARGIN_DEPOSIT_COMMAND_KIND_V1:
        return PerpsMarginRejectCodeV1.ACCOUNT_MISSING
    if account is None and len(state.accounts) >= MAX_PERPS_MARGIN_ACCOUNTS_V1:
        return PerpsMarginRejectCodeV1.ACCOUNT_LIMIT
    if account is not None and account.owner != command.owner:
        return PerpsMarginRejectCodeV1.ACCOUNT_OWNER_MISMATCH
    if account is not None and account.status is PerpsMarginAccountStatusV1.CLOSED:
        return PerpsMarginRejectCodeV1.ACCOUNT_CLOSED
    expected_nonce = _next_nonce(account)
    if isinstance(expected_nonce, PerpsMarginRejectCodeV1):
        return expected_nonce
    if command.nonce != expected_nonce:
        return PerpsMarginRejectCodeV1.NONCE_MISMATCH
    return account or PerpsMarginAccountV1(
        account_id=command.account_id,
        owner=command.owner,
        position_base=0,
        entry_price_e8=0,
        collateral_atoms=0,
        nonce=0,
        status=PerpsMarginAccountStatusV1.OPEN,
    )


def _post_account(
    state: PerpsMarginStateV1,
    command: PerpsMarginCommandV1,
    account: PerpsMarginAccountV1,
) -> PerpsMarginAccountV1 | PerpsMarginRejectCodeV1:
    if command.command_kind == PERPS_MARGIN_CLOSE_COMMAND_KIND_V1:
        if command.amount_atoms != 0:
            return PerpsMarginRejectCodeV1.INVALID_CLOSE_AMOUNT
        if account.position_base != 0:
            return PerpsMarginRejectCodeV1.POSITION_OPEN
        if account.collateral_atoms != 0:
            return PerpsMarginRejectCodeV1.COLLATERAL_REMAINS
        return replace(
            account,
            nonce=command.nonce,
            status=PerpsMarginAccountStatusV1.CLOSED,
        )
    if command.amount_atoms == 0:
        return PerpsMarginRejectCodeV1.ZERO_AMOUNT
    if command.amount_atoms > MAX_DELTA_ATOMS_V1:
        return PerpsMarginRejectCodeV1.EFFECT_DELTA_OVERFLOW
    if command.command_kind == PERPS_MARGIN_DEPOSIT_COMMAND_KIND_V1:
        collateral_atoms = account.collateral_atoms + command.amount_atoms
        if collateral_atoms > MAX_ATOMS_V1:
            return PerpsMarginRejectCodeV1.BALANCE_OVERFLOW
        return replace(account, collateral_atoms=collateral_atoms, nonce=command.nonce)
    if command.amount_atoms > account.collateral_atoms:
        return PerpsMarginRejectCodeV1.INSUFFICIENT_COLLATERAL
    remaining = account.collateral_atoms - command.amount_atoms
    maintenance = _maintenance_requirement(state, account.position_base)
    if isinstance(maintenance, PerpsMarginRejectCodeV1):
        return maintenance
    if account.position_base != 0 and remaining < maintenance:
        return PerpsMarginRejectCodeV1.MAINTENANCE_BREACH
    return replace(account, collateral_atoms=remaining, nonce=command.nonce)


def _effect_rows(command: PerpsMarginCommandV1) -> tuple[EconomicEffectRowV1, ...]:
    if command.command_kind == PERPS_MARGIN_CLOSE_COMMAND_KIND_V1:
        return ()
    direction = 1 if command.command_kind == PERPS_MARGIN_DEPOSIT_COMMAND_KIND_V1 else -1
    amount = command.amount_atoms
    rows = (
        EconomicEffectRowV1(
            EconomicEffectKindV1.ACCOUNT_MOVEMENT,
            command.owner,
            command.asset,
            ACCOUNT_CUSTODY_DOMAIN_V1,
            -direction * amount,
        ),
        EconomicEffectRowV1(
            EconomicEffectKindV1.CUSTODY,
            command.account_id,
            command.asset,
            PERPS_MARGIN_CUSTODY_DOMAIN_V1,
            direction * amount,
        ),
        EconomicEffectRowV1(
            EconomicEffectKindV1.LIABILITY,
            command.owner,
            command.asset,
            PERPS_MARGIN_CUSTODY_DOMAIN_V1,
            direction * amount,
        ),
    )
    return tuple(sorted(rows, key=lambda row: row.key))


def _effect_plan(
    context: PerpsMarginContextV1,
    pre_state: PerpsMarginStateV1,
    post_state: PerpsMarginStateV1,
    command: PerpsMarginCommandV1,
) -> GlobalEconomicEffectPlanV1:
    return GlobalEconomicEffectPlanV1(
        rows=_effect_rows(command),
        asset_conservation=(),
        fee_conservation=(),
        lane_writes=(
            LaneWriteV1(LaneIdV1.PERPS_MARKET, pre_state.state_root, post_state.state_root),
        ),
        occurrence_consumptions=(context.command_occurrence_id,),
        external_outbox_enqueue=(),
    )


def _statement_root(
    context: PerpsMarginContextV1,
    pre_state: PerpsMarginStateV1,
    command: PerpsMarginCommandV1,
) -> str:
    return hash_global_v1(
        "perps-margin-statement-v1",
        {
            "schema": PERPS_MARGIN_MODULE_INPUT_SCHEMA_V1,
            "context": context,
            "pre_state": pre_state,
            "command": command,
        },
    )


def _private_port(
    context: PerpsMarginContextV1,
    command: PerpsMarginCommandV1,
    effects: GlobalEconomicEffectPlanV1,
    terminal_root: str,
) -> PerpsMarginPrivatePortV1:
    return PerpsMarginPrivatePortV1(
        producer_module_schema=PERPS_MARGIN_MODULE_SCHEMA_V1,
        module_release_id=context.module_release_id,
        command_occurrence_id=context.command_occurrence_id,
        command_body_hash=command.command_body_hash,
        market_id=command.market_id,
        account_id=command.account_id,
        module_effect_plan_root=effects.effect_plan_root,
        terminal_obligations_root=terminal_root,
        oracle_authority_root=context.oracle_authority_root,
        oracle_occurrence_root=context.oracle_occurrence_root,
        oracle_price_e8=context.oracle_price_e8,
    )


def _journal(
    context: PerpsMarginContextV1,
    pre_state: PerpsMarginStateV1,
    post_state: PerpsMarginStateV1,
    effects: GlobalEconomicEffectPlanV1,
    statement_root: str,
    private_port: PerpsMarginPrivatePortV1,
    terminal_root: str,
) -> LaneModuleTransitionJournalV1:
    private_port_root = private_port.port_root
    receipt_root = _perps_margin_receipt_root_v1(
        statement_root,
        pre_state.state_root,
        post_state.state_root,
        effects,
        private_port,
    )
    return LaneModuleTransitionJournalV1(
        chain_id=context.chain_id,
        deployment_root=context.deployment_root,
        profile_root=context.profile_root,
        writer_epoch=context.writer_epoch,
        lane_id=LaneIdV1.PERPS_MARKET,
        module_release_id=context.module_release_id,
        command_occurrence_id=context.command_occurrence_id,
        pre_lane_root=pre_state.state_root,
        post_lane_root=post_state.state_root,
        effect_plan_root=effects.effect_plan_root,
        private_port_root=private_port_root,
        receipt_root=receipt_root,
        terminal_obligations_root=terminal_root,
    )


def _accept(
    context: PerpsMarginContextV1,
    pre_state: PerpsMarginStateV1,
    post_state: PerpsMarginStateV1,
    command: PerpsMarginCommandV1,
) -> PerpsMarginAcceptedV1:
    effects = _effect_plan(context, pre_state, post_state, command)
    terminal_obligations = post_state.terminal_obligations
    terminal_root = post_state.terminal_obligations_root
    statement_root = _statement_root(context, pre_state, command)
    private_port = _private_port(context, command, effects, terminal_root)
    journal = _journal(
        context,
        pre_state,
        post_state,
        effects,
        statement_root,
        private_port,
        terminal_root,
    )
    return PerpsMarginAcceptedV1(
        statement_root,
        post_state,
        effects,
        journal,
        private_port,
        terminal_obligations,
    )


def transition_perps_margin_v1(
    context: PerpsMarginContextV1,
    pre_state: PerpsMarginStateV1,
    command: PerpsMarginCommandV1,
) -> PerpsMarginResultV1:
    """Apply one subject-bound margin command with fixed reject precedence."""

    if type(context) is not PerpsMarginContextV1:
        raise TypeError("perps margin context must be exact")
    if type(pre_state) is not PerpsMarginStateV1:
        raise TypeError("perps margin pre-state must be exact")
    if type(command) is not PerpsMarginCommandV1:
        raise TypeError("perps margin command must be exact")
    common_reject = _common_policy_reject(context, pre_state, command)
    if common_reject is not None:
        return _reject(common_reject, pre_state)
    account = _prepare_account(pre_state, command)
    if isinstance(account, PerpsMarginRejectCodeV1):
        return _reject(account, pre_state)
    oracle_reject = _oracle_policy_reject(context, pre_state, command, account)
    if oracle_reject is not None:
        return _reject(oracle_reject, pre_state)
    post_account = _post_account(pre_state, command, account)
    if isinstance(post_account, PerpsMarginRejectCodeV1):
        return _reject(post_account, pre_state)
    post_state = _replace_account(pre_state, post_account)
    return _accept(context, pre_state, post_state, command)


__all__ = ["transition_perps_margin_v1"]
