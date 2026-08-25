"""Closed values for the research-only `PERPS_MARKET` margin accounting core.

This surface selects only the already documented v1 foundations: one
collateral asset per market, quote-e8 integer accounting, isolated margin,
owner/subject equality, and terminal account closure. Authentication of that
subject is an upstream route obligation. Funding, matching,
liquidation, insurance, ADL, bankruptcy, routing, proof verification, and
publication authority remain outside this module.
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from typing import Final, TypeAlias

from .global_economic_proof_v1 import LaneModuleTransitionJournalV1
from .global_settlement_types_v1 import (
    MAX_ATOMS_V1,
    ZERO_ROOT_V1,
    GlobalEconomicEffectPlanV1,
    LaneIdV1,
    TerminalObligationStatusV1,
    TerminalObligationV1,
    _require_atoms_u128,
    _require_delta_atoms_i128,
    _require_nonnegative_int,
    _require_ordered_objects,
    _require_root,
    _require_token,
    hash_economic_command_body_v1,
    hash_global_v1,
)

PERPS_MARGIN_MODULE_SCHEMA_V1: Final = "zenodex/perps-margin-module/v1"
PERPS_MARGIN_MODULE_INPUT_SCHEMA_V1: Final = "zenodex/perps-margin-module-input/v1"
PERPS_MARGIN_PRIVATE_PORT_SCHEMA_V1: Final = "zenodex/perps-margin-private-port/v1"
PERPS_MARGIN_TERMINAL_OBLIGATION_ID_SCHEMA_V1: Final = (
    "zenodex/perps-margin-terminal-obligation-id/v1"
)
PERPS_MARGIN_DEPOSIT_COMMAND_KIND_V1: Final = "perps_margin_deposit"
PERPS_MARGIN_WITHDRAW_COMMAND_KIND_V1: Final = "perps_margin_withdraw"
PERPS_MARGIN_CLOSE_COMMAND_KIND_V1: Final = "perps_margin_close"
ACCOUNT_CUSTODY_DOMAIN_V1: Final = "accounts"
PERPS_MARGIN_CUSTODY_DOMAIN_V1: Final = "perps_margin"
BPS_SCALE_V1: Final = 10_000
MAX_PERPS_MARGIN_ACCOUNTS_V1: Final = 64


def _require_exact_str(value: object, *, name: str) -> str:
    if type(value) is not str:
        raise TypeError(f"{name} must be exact text")
    return value


class PerpsMarginAccountStatusV1(str, Enum):
    OPEN = "OPEN"
    CLOSED = "CLOSED"


class PerpsMarginMarketStatusV1(str, Enum):
    ACTIVE = "ACTIVE"
    DRAIN_ONLY = "DRAIN_ONLY"
    HALTED = "HALTED"


class PerpsMarginRejectCodeV1(str, Enum):
    RELEASE_MISMATCH = "RELEASE_MISMATCH"
    UNKNOWN_COMMAND = "UNKNOWN_COMMAND"
    MARKET_DRAIN_ONLY = "MARKET_DRAIN_ONLY"
    HALTED_MARKET = "HALTED_MARKET"
    MARKET_MISMATCH = "MARKET_MISMATCH"
    ASSET_MISMATCH = "ASSET_MISMATCH"
    UNAUTHORIZED_SUBJECT = "UNAUTHORIZED_SUBJECT"
    ORACLE_AUTHORITY_MISSING = "ORACLE_AUTHORITY_MISSING"
    ORACLE_PRICE_MISMATCH = "ORACLE_PRICE_MISMATCH"
    UNEXPECTED_ORACLE_AUTHORITY = "UNEXPECTED_ORACLE_AUTHORITY"
    ACCOUNT_MISSING = "ACCOUNT_MISSING"
    ACCOUNT_OWNER_MISMATCH = "ACCOUNT_OWNER_MISMATCH"
    ACCOUNT_CLOSED = "ACCOUNT_CLOSED"
    ACCOUNT_LIMIT = "ACCOUNT_LIMIT"
    NONCE_MISMATCH = "NONCE_MISMATCH"
    NONCE_OVERFLOW = "NONCE_OVERFLOW"
    ZERO_AMOUNT = "ZERO_AMOUNT"
    INVALID_CLOSE_AMOUNT = "INVALID_CLOSE_AMOUNT"
    EFFECT_DELTA_OVERFLOW = "EFFECT_DELTA_OVERFLOW"
    BALANCE_OVERFLOW = "BALANCE_OVERFLOW"
    INSUFFICIENT_COLLATERAL = "INSUFFICIENT_COLLATERAL"
    MAINTENANCE_BREACH = "MAINTENANCE_BREACH"
    POSITION_OPEN = "POSITION_OPEN"
    COLLATERAL_REMAINS = "COLLATERAL_REMAINS"
    ARITHMETIC_OVERFLOW = "ARITHMETIC_OVERFLOW"


@dataclass(frozen=True, slots=True, order=True)
class PerpsMarginAccountV1:
    account_id: str
    owner: str
    position_base: int
    entry_price_e8: int
    collateral_atoms: int
    nonce: int
    status: PerpsMarginAccountStatusV1

    def __post_init__(self) -> None:
        _require_exact_str(self.account_id, name="perps margin account id")
        _require_exact_str(self.owner, name="perps margin account owner")
        _require_token(self.account_id, name="perps margin account id")
        _require_token(self.owner, name="perps margin account owner")
        _require_delta_atoms_i128(self.position_base, name="perps margin position")
        _require_atoms_u128(self.entry_price_e8, name="perps margin entry price")
        _require_atoms_u128(self.collateral_atoms, name="perps margin collateral")
        _require_nonnegative_int(self.nonce, name="perps margin account nonce")
        if type(self.status) is not PerpsMarginAccountStatusV1:
            raise TypeError("perps margin account status is not closed")
        if self.position_base == 0 and self.entry_price_e8 != 0:
            raise ValueError("flat perps margin account must have zero entry price")
        if self.position_base != 0 and self.entry_price_e8 == 0:
            raise ValueError("open perps margin position must have a positive entry price")
        if self.status is PerpsMarginAccountStatusV1.CLOSED and (
            self.position_base != 0 or self.entry_price_e8 != 0 or self.collateral_atoms != 0
        ):
            raise ValueError("closed account must be flat and empty")

    @property
    def key(self) -> str:
        return self.account_id

    def to_canonical(self) -> dict[str, object]:
        return {
            "account_id": self.account_id,
            "owner": self.owner,
            "position_base": self.position_base,
            "entry_price_e8": self.entry_price_e8,
            "collateral_atoms": self.collateral_atoms,
            "nonce": self.nonce,
            "status": self.status,
        }


@dataclass(frozen=True, slots=True)
class PerpsMarginStateV1:
    module_release_id: str
    market_id: str
    collateral_asset: str
    index_price_e8: int
    maintenance_margin_bps: int
    depeg_buffer_bps: int
    max_position_abs: int
    market_status: PerpsMarginMarketStatusV1
    accounts: tuple[PerpsMarginAccountV1, ...]

    def __post_init__(self) -> None:
        _require_exact_str(self.module_release_id, name="perps margin module release id")
        _require_exact_str(self.market_id, name="perps margin market id")
        _require_exact_str(self.collateral_asset, name="perps margin collateral asset")
        _require_root(self.module_release_id, name="perps margin module release id")
        _require_token(self.market_id, name="perps margin market id")
        _require_token(self.collateral_asset, name="perps margin collateral asset")
        _require_atoms_u128(self.index_price_e8, name="perps margin index price")
        if self.index_price_e8 == 0:
            raise ValueError("perps margin index price must be positive")
        _require_nonnegative_int(
            self.maintenance_margin_bps,
            name="perps margin maintenance bps",
        )
        _require_nonnegative_int(self.depeg_buffer_bps, name="perps margin depeg bps")
        if not 1 <= self.maintenance_margin_bps <= BPS_SCALE_V1:
            raise ValueError("perps margin maintenance bps out of range")
        if not 0 <= self.depeg_buffer_bps <= BPS_SCALE_V1:
            raise ValueError("perps margin depeg bps out of range")
        risk_bps = self.maintenance_margin_bps + self.depeg_buffer_bps
        if risk_bps > BPS_SCALE_V1:
            raise ValueError("perps margin maintenance plus depeg bps exceeds scale")
        _require_atoms_u128(self.max_position_abs, name="perps margin max position")
        if self.max_position_abs == 0:
            raise ValueError("perps margin max position must be positive")
        if self.max_position_abs * self.index_price_e8 * risk_bps > MAX_ATOMS_V1:
            raise ValueError("perps margin maintenance envelope exceeds u128")
        if type(self.market_status) is not PerpsMarginMarketStatusV1:
            raise TypeError("perps margin market status is not closed")
        if type(self.accounts) is not tuple or any(
            type(account) is not PerpsMarginAccountV1 for account in self.accounts
        ):
            raise TypeError("perps margin accounts must contain exact typed values")
        _require_ordered_objects(
            self.accounts,
            name="perps margin accounts",
            expected_type=PerpsMarginAccountV1,
            key="key",
        )
        if len(self.accounts) > MAX_PERPS_MARGIN_ACCOUNTS_V1:
            raise ValueError("perps margin account count exceeds bound")
        positive_position = 0
        negative_position = 0
        for account in self.accounts:
            if abs(account.position_base) > self.max_position_abs:
                raise ValueError("perps margin position exceeds market bound")
            if account.position_base != 0 and account.entry_price_e8 != self.index_price_e8:
                raise ValueError("perps margin open position entry price differs from index")
            if account.position_base >= 0:
                positive_position += account.position_base
            else:
                negative_position += -account.position_base
            if positive_position > MAX_ATOMS_V1 or negative_position > MAX_ATOMS_V1:
                raise ValueError("perps margin gross position total exceeds u128")
        if positive_position != negative_position:
            raise ValueError("perps margin peer-to-peer net position must be zero")

    @property
    def state_root(self) -> str:
        return hash_global_v1("perps-margin-state-v1", self.to_canonical())

    def account(self, account_id: str) -> PerpsMarginAccountV1 | None:
        _require_token(account_id, name="perps margin account lookup")
        return next((account for account in self.accounts if account.account_id == account_id), None)

    @property
    def terminal_obligations(self) -> tuple[TerminalObligationV1, ...]:
        obligations = tuple(
            TerminalObligationV1(
                obligation_id=hash_global_v1(
                    "perps-margin-terminal-obligation-id-v1",
                    {
                        "schema": PERPS_MARGIN_TERMINAL_OBLIGATION_ID_SCHEMA_V1,
                        "lane_id": LaneIdV1.PERPS_MARKET,
                        "module_release_id": self.module_release_id,
                        "market_id": self.market_id,
                        "account_id": account.account_id,
                    },
                ),
                lane_id=LaneIdV1.PERPS_MARKET,
                claimant=account.owner,
                asset=self.collateral_asset,
                amount_atoms=account.collateral_atoms,
                status=(
                    TerminalObligationStatusV1.OPEN
                    if account.status is PerpsMarginAccountStatusV1.OPEN
                    else TerminalObligationStatusV1.DRAINED
                ),
            )
            for account in self.accounts
        )
        return tuple(sorted(obligations, key=lambda obligation: obligation.obligation_id))

    @property
    def terminal_obligations_root(self) -> str:
        return hash_global_v1(
            "perps-margin-terminal-obligations-v1",
            self.terminal_obligations,
        )

    def to_canonical(self) -> dict[str, object]:
        return {
            "schema": PERPS_MARGIN_MODULE_SCHEMA_V1,
            "module_release_id": self.module_release_id,
            "market_id": self.market_id,
            "collateral_asset": self.collateral_asset,
            "index_price_e8": self.index_price_e8,
            "maintenance_margin_bps": self.maintenance_margin_bps,
            "depeg_buffer_bps": self.depeg_buffer_bps,
            "max_position_abs": self.max_position_abs,
            "market_status": self.market_status,
            "accounts": self.accounts,
        }


@dataclass(frozen=True, slots=True)
class PerpsMarginContextV1:
    chain_id: str
    deployment_root: str
    profile_root: str
    writer_epoch: int
    module_release_id: str
    command_occurrence_id: str
    subject_id: str
    grant_root: str
    oracle_authority_root: str
    oracle_occurrence_root: str
    oracle_price_e8: int

    def __post_init__(self) -> None:
        for name, value in (
            ("chain", self.chain_id),
            ("deployment", self.deployment_root),
            ("profile", self.profile_root),
            ("module release", self.module_release_id),
            ("occurrence", self.command_occurrence_id),
            ("subject", self.subject_id),
            ("grant", self.grant_root),
            ("oracle authority", self.oracle_authority_root),
            ("oracle occurrence", self.oracle_occurrence_root),
        ):
            _require_exact_str(value, name=f"perps margin context {name}")
        _require_token(self.chain_id, name="perps margin context chain")
        _require_root(self.deployment_root, name="perps margin context deployment")
        _require_root(self.profile_root, name="perps margin context profile")
        _require_nonnegative_int(self.writer_epoch, name="perps margin context writer epoch")
        _require_root(self.module_release_id, name="perps margin context module release")
        _require_root(self.command_occurrence_id, name="perps margin context occurrence")
        _require_token(self.subject_id, name="perps margin context subject")
        _require_root(self.grant_root, name="perps margin context grant")
        _require_root(
            self.oracle_authority_root,
            name="perps margin context oracle authority",
            allow_zero=True,
        )
        _require_root(
            self.oracle_occurrence_root,
            name="perps margin context oracle occurrence",
            allow_zero=True,
        )
        _require_atoms_u128(
            self.oracle_price_e8,
            name="perps margin context oracle price",
        )
        presence = (
            self.oracle_authority_root != ZERO_ROOT_V1,
            self.oracle_occurrence_root != ZERO_ROOT_V1,
            self.oracle_price_e8 != 0,
        )
        if any(presence) and not all(presence):
            raise ValueError("perps margin Oracle binding must be wholly absent or present")

    @property
    def has_oracle_authority(self) -> bool:
        return self.oracle_authority_root != ZERO_ROOT_V1

    def to_canonical(self) -> dict[str, object]:
        return {
            "chain_id": self.chain_id,
            "deployment_root": self.deployment_root,
            "profile_root": self.profile_root,
            "writer_epoch": self.writer_epoch,
            "module_release_id": self.module_release_id,
            "command_occurrence_id": self.command_occurrence_id,
            "subject_id": self.subject_id,
            "grant_root": self.grant_root,
            "oracle_authority_root": self.oracle_authority_root,
            "oracle_occurrence_root": self.oracle_occurrence_root,
            "oracle_price_e8": self.oracle_price_e8,
        }


@dataclass(frozen=True, slots=True)
class PerpsMarginCommandV1:
    command_kind: str
    account_id: str
    market_id: str
    owner: str
    asset: str
    amount_atoms: int
    nonce: int

    def __post_init__(self) -> None:
        for name, value in (
            ("kind", self.command_kind),
            ("account", self.account_id),
            ("market", self.market_id),
            ("owner", self.owner),
            ("asset", self.asset),
        ):
            _require_exact_str(value, name=f"perps margin command {name}")
        _require_token(self.command_kind, name="perps margin command kind")
        _require_token(self.account_id, name="perps margin command account")
        _require_token(self.market_id, name="perps margin command market")
        _require_token(self.owner, name="perps margin command owner")
        _require_token(self.asset, name="perps margin command asset")
        _require_atoms_u128(self.amount_atoms, name="perps margin command amount")
        _require_nonnegative_int(self.nonce, name="perps margin command nonce")

    @property
    def command_body_hash(self) -> str:
        return hash_economic_command_body_v1(self.command_kind, self)

    def to_canonical(self) -> dict[str, object]:
        return {
            "command_kind": self.command_kind,
            "account_id": self.account_id,
            "market_id": self.market_id,
            "owner": self.owner,
            "asset": self.asset,
            "amount_atoms": self.amount_atoms,
            "nonce": self.nonce,
        }


@dataclass(frozen=True, slots=True)
class PerpsMarginPrivatePortV1:
    producer_module_schema: str
    module_release_id: str
    command_occurrence_id: str
    command_body_hash: str
    market_id: str
    account_id: str
    module_effect_plan_root: str
    terminal_obligations_root: str
    oracle_authority_root: str
    oracle_occurrence_root: str
    oracle_price_e8: int

    def __post_init__(self) -> None:
        for name, value in (
            ("producer schema", self.producer_module_schema),
            ("module release", self.module_release_id),
            ("command occurrence", self.command_occurrence_id),
            ("command body", self.command_body_hash),
            ("market", self.market_id),
            ("account", self.account_id),
            ("effect plan", self.module_effect_plan_root),
            ("terminal obligations", self.terminal_obligations_root),
            ("oracle authority", self.oracle_authority_root),
            ("oracle occurrence", self.oracle_occurrence_root),
        ):
            _require_exact_str(value, name=f"perps margin private port {name}")
        if self.producer_module_schema != PERPS_MARGIN_MODULE_SCHEMA_V1:
            raise ValueError("perps margin private port producer schema mismatch")
        _require_root(self.module_release_id, name="perps margin private port release")
        _require_root(
            self.command_occurrence_id,
            name="perps margin private port occurrence",
        )
        _require_root(self.command_body_hash, name="perps margin private port command body")
        _require_token(self.market_id, name="perps margin private port market")
        _require_token(self.account_id, name="perps margin private port account")
        _require_root(
            self.module_effect_plan_root,
            name="perps margin private port effect plan",
        )
        _require_root(
            self.terminal_obligations_root,
            name="perps margin private port terminal obligations",
        )
        _require_root(
            self.oracle_authority_root,
            name="perps margin private port oracle authority",
            allow_zero=True,
        )
        _require_root(
            self.oracle_occurrence_root,
            name="perps margin private port oracle occurrence",
            allow_zero=True,
        )
        _require_atoms_u128(
            self.oracle_price_e8,
            name="perps margin private port oracle price",
        )
        presence = (
            self.oracle_authority_root != ZERO_ROOT_V1,
            self.oracle_occurrence_root != ZERO_ROOT_V1,
            self.oracle_price_e8 != 0,
        )
        if any(presence) and not all(presence):
            raise ValueError("perps margin private-port Oracle binding is partial")

    @property
    def port_root(self) -> str:
        return hash_global_v1("perps-margin-private-port-v1", self.to_canonical())

    def to_canonical(self) -> dict[str, object]:
        return {
            "schema": PERPS_MARGIN_PRIVATE_PORT_SCHEMA_V1,
            "producer_module_schema": self.producer_module_schema,
            "module_release_id": self.module_release_id,
            "command_occurrence_id": self.command_occurrence_id,
            "command_body_hash": self.command_body_hash,
            "market_id": self.market_id,
            "account_id": self.account_id,
            "module_effect_plan_root": self.module_effect_plan_root,
            "terminal_obligations_root": self.terminal_obligations_root,
            "oracle_authority_root": self.oracle_authority_root,
            "oracle_occurrence_root": self.oracle_occurrence_root,
            "oracle_price_e8": self.oracle_price_e8,
        }


def _perps_margin_receipt_root_v1(
    statement_root: str,
    pre_state_root: str,
    post_state_root: str,
    effects: GlobalEconomicEffectPlanV1,
    private_port: PerpsMarginPrivatePortV1,
) -> str:
    return hash_global_v1(
        "perps-margin-receipt-v1",
        {
            "statement_root": statement_root,
            "pre_state_root": pre_state_root,
            "post_state_root": post_state_root,
            "effect_plan_root": effects.effect_plan_root,
            "private_port_root": private_port.port_root,
            "terminal_obligations_root": private_port.terminal_obligations_root,
        },
    )


@dataclass(frozen=True, slots=True)
class PerpsMarginAcceptedV1:
    statement_root: str
    post_state: PerpsMarginStateV1
    effects: GlobalEconomicEffectPlanV1
    module_journal: LaneModuleTransitionJournalV1
    private_port: PerpsMarginPrivatePortV1
    terminal_obligations: tuple[TerminalObligationV1, ...]

    def __post_init__(self) -> None:
        _require_exact_str(self.statement_root, name="perps margin accepted statement")
        _require_root(self.statement_root, name="perps margin accepted statement")
        if type(self.post_state) is not PerpsMarginStateV1:
            raise TypeError("perps margin accepted state must be exact")
        if type(self.effects) is not GlobalEconomicEffectPlanV1 or self.effects.is_empty:
            raise ValueError("perps margin acceptance requires candidate effects")
        if type(self.module_journal) is not LaneModuleTransitionJournalV1:
            raise TypeError("perps margin accepted journal must be exact")
        if type(self.private_port) is not PerpsMarginPrivatePortV1:
            raise TypeError("perps margin accepted private port must be exact")
        if type(self.terminal_obligations) is not tuple or any(
            type(obligation) is not TerminalObligationV1
            for obligation in self.terminal_obligations
        ):
            raise TypeError("perps margin terminal obligations must be exact typed values")
        _require_ordered_objects(
            self.terminal_obligations,
            name="perps margin terminal obligations",
            expected_type=TerminalObligationV1,
            key="obligation_id",
        )
        if self.terminal_obligations != self.post_state.terminal_obligations:
            raise ValueError("perps margin terminal obligations differ from post-state")
        if self.module_journal.lane_id is not LaneIdV1.PERPS_MARKET:
            raise ValueError("perps margin journal has the wrong lane")
        if self.module_journal.module_release_id != self.post_state.module_release_id:
            raise ValueError("perps margin journal release mismatch")
        if self.module_journal.post_lane_root != self.post_state.state_root:
            raise ValueError("perps margin journal post-state root mismatch")
        if self.module_journal.effect_plan_root != self.effects.effect_plan_root:
            raise ValueError("perps margin journal effect-plan root mismatch")
        if self.private_port.module_release_id != self.module_journal.module_release_id:
            raise ValueError("perps margin private-port release mismatch")
        if (
            self.private_port.command_occurrence_id
            != self.module_journal.command_occurrence_id
        ):
            raise ValueError("perps margin private-port occurrence mismatch")
        if self.private_port.module_effect_plan_root != self.effects.effect_plan_root:
            raise ValueError("perps margin private-port effect-plan mismatch")
        if self.private_port.market_id != self.post_state.market_id:
            raise ValueError("perps margin private-port market mismatch")
        if self.post_state.account(self.private_port.account_id) is None:
            raise ValueError("perps margin private-port account is absent from post-state")
        if self.module_journal.private_port_root != self.private_port.port_root:
            raise ValueError("perps margin private-port root mismatch")
        if self.module_journal.terminal_obligations_root != self.terminal_obligations_root:
            raise ValueError("perps margin journal terminal root mismatch")
        if self.private_port.terminal_obligations_root != self.terminal_obligations_root:
            raise ValueError("perps margin private-port terminal root mismatch")
        if self.module_journal.receipt_root != _perps_margin_receipt_root_v1(
            self.statement_root,
            self.module_journal.pre_lane_root,
            self.module_journal.post_lane_root,
            self.effects,
            self.private_port,
        ):
            raise ValueError("perps margin receipt root mismatch")

    @property
    def terminal_obligations_root(self) -> str:
        return hash_global_v1(
            "perps-margin-terminal-obligations-v1",
            self.terminal_obligations,
        )

    @property
    def receipt_root(self) -> str:
        return self.module_journal.receipt_root


@dataclass(frozen=True, slots=True)
class PerpsMarginRejectedV1:
    code: PerpsMarginRejectCodeV1
    pre_state_root: str
    post_state_root: str
    effects: GlobalEconomicEffectPlanV1

    def __post_init__(self) -> None:
        if not isinstance(self.code, PerpsMarginRejectCodeV1):
            raise TypeError("perps margin reject code is not closed")
        _require_exact_str(self.pre_state_root, name="perps margin rejected pre-state")
        _require_exact_str(self.post_state_root, name="perps margin rejected post-state")
        _require_root(self.pre_state_root, name="perps margin rejected pre-state")
        _require_root(self.post_state_root, name="perps margin rejected post-state")
        if self.pre_state_root != self.post_state_root:
            raise ValueError("perps margin rejection changed state")
        if type(self.effects) is not GlobalEconomicEffectPlanV1 or not self.effects.is_empty:
            raise ValueError("perps margin rejection carried effects")


PerpsMarginResultV1: TypeAlias = PerpsMarginAcceptedV1 | PerpsMarginRejectedV1


__all__ = [
    "PERPS_MARGIN_MODULE_SCHEMA_V1",
    "PERPS_MARGIN_MODULE_INPUT_SCHEMA_V1",
    "PERPS_MARGIN_PRIVATE_PORT_SCHEMA_V1",
    "PERPS_MARGIN_TERMINAL_OBLIGATION_ID_SCHEMA_V1",
    "PERPS_MARGIN_DEPOSIT_COMMAND_KIND_V1",
    "PERPS_MARGIN_WITHDRAW_COMMAND_KIND_V1",
    "PERPS_MARGIN_CLOSE_COMMAND_KIND_V1",
    "ACCOUNT_CUSTODY_DOMAIN_V1",
    "PERPS_MARGIN_CUSTODY_DOMAIN_V1",
    "BPS_SCALE_V1",
    "MAX_PERPS_MARGIN_ACCOUNTS_V1",
    "PerpsMarginAccountStatusV1",
    "PerpsMarginMarketStatusV1",
    "PerpsMarginRejectCodeV1",
    "PerpsMarginAccountV1",
    "PerpsMarginStateV1",
    "PerpsMarginContextV1",
    "PerpsMarginCommandV1",
    "PerpsMarginPrivatePortV1",
    "PerpsMarginAcceptedV1",
    "PerpsMarginRejectedV1",
    "PerpsMarginResultV1",
]
