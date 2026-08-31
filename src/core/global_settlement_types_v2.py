"""Immutable foundational values for GlobalSettlementABI V2.

V2 is an explicit research-only successor.  It has distinct schemas and hash
domains from V1, and values from the two ABI majors are never interchangeable.
The module owns canonical scalar validation and the global economic effect
plan used by lane functional cores.  It grants no settlement, publication, or
release authority.
"""

from __future__ import annotations

import hashlib
from dataclasses import dataclass
from enum import Enum
from typing import Final, Mapping, Protocol, runtime_checkable

from ..state.canonical import canonical_json_bytes, domain_sep_bytes

GLOBAL_SETTLEMENT_ABI_V2: Final = "zenodex/global-settlement-abi/v2"
MAX_TOKEN_BYTES_V2: Final = 160
MAX_U64_V2: Final = (1 << 64) - 1
MAX_ATOMS_V2: Final = (1 << 128) - 1
MIN_DELTA_ATOMS_V2: Final = -(1 << 127)
MAX_DELTA_ATOMS_V2: Final = (1 << 127) - 1
MAX_ORACLE_OCCURRENCE_DELTAS_PER_PLAN_V2: Final = 64
MAX_TERMINAL_OBLIGATION_DELTAS_PER_PLAN_V2: Final = 64
ZERO_ROOT_V2: Final = "0x" + "00" * 32


@runtime_checkable
class _CanonicalizableV2(Protocol):
    def to_canonical(self) -> object: ...


def _require_nonnegative_int_v2(value: object, *, name: str) -> int:
    if type(value) is not int or value < 0:
        raise ValueError(f"{name} must be a non-negative integer")
    if value > MAX_U64_V2:
        raise ValueError(f"{name} must fit an unsigned 64-bit integer")
    return value


def _require_atoms_u128_v2(value: object, *, name: str) -> int:
    if type(value) is not int or value < 0:
        raise ValueError(f"{name} must be a non-negative integer")
    if value > MAX_ATOMS_V2:
        raise ValueError(f"{name} must fit an unsigned 128-bit integer")
    return value


def _require_delta_atoms_i128_v2(value: object, *, name: str) -> int:
    if type(value) is not int:
        raise ValueError(f"{name} must be an integer")
    if not MIN_DELTA_ATOMS_V2 <= value <= MAX_DELTA_ATOMS_V2:
        raise ValueError(f"{name} must fit a signed 128-bit integer")
    return value


def _require_bool_v2(value: object, *, name: str) -> bool:
    if type(value) is not bool:
        raise TypeError(f"{name} must be bool")
    return value


def _require_token_v2(value: object, *, name: str) -> str:
    if type(value) is not str:
        raise TypeError(f"{name} must be a string")
    if not value:
        raise ValueError(f"{name} must not be empty")
    if len(value.encode("utf-8")) > MAX_TOKEN_BYTES_V2:
        raise ValueError(f"{name} exceeds {MAX_TOKEN_BYTES_V2} UTF-8 bytes")
    if any(ord(char) < 0x21 or ord(char) > 0x7E for char in value):
        raise ValueError(f"{name} must use printable ASCII")
    return value


def _require_root_v2(value: object, *, name: str, allow_zero: bool = False) -> str:
    if type(value) is not str:
        raise TypeError(f"{name} must be a string")
    if len(value) != 66 or not value.startswith("0x") or value != value.lower():
        raise ValueError(f"{name} must be canonical lowercase 0x-prefixed 32-byte hex")
    try:
        bytes.fromhex(value[2:])
    except ValueError as exc:
        raise ValueError(f"{name} must be canonical lowercase 0x-prefixed 32-byte hex") from exc
    if not allow_zero and value == ZERO_ROOT_V2:
        raise ValueError(f"{name} must be nonzero")
    return value


def _canonical_value_v2(value: object) -> object:
    if value is None or type(value) in {bool, int, str}:
        return value
    if isinstance(value, Enum):
        return _canonical_value_v2(value.value)
    if isinstance(value, bool | int | str):
        raise TypeError("canonical scalar subclasses are unsupported")
    if type(value) is tuple or type(value) is list:
        return [_canonical_value_v2(item) for item in value]
    if isinstance(value, tuple | list):
        raise TypeError("canonical sequence subclasses are unsupported")
    if type(value) is dict:
        if any(type(key) is not str for key in value):
            raise TypeError("canonical mapping keys must be strings")
        return {
            key: _canonical_value_v2(item)
            for key, item in sorted(value.items(), key=lambda pair: pair[0])
        }
    if isinstance(value, Mapping):
        raise TypeError("canonical mapping subclasses are unsupported")
    if isinstance(value, _CanonicalizableV2):
        return _canonical_value_v2(value.to_canonical())
    raise TypeError("unsupported canonical value type")


def canonical_global_bytes_v2(value: object) -> bytes:
    """Encode a typed V2 value as deterministic canonical JSON."""

    encoded: object = canonical_json_bytes(_canonical_value_v2(value))
    if type(encoded) is not bytes:
        raise TypeError("canonical encoder returned an invalid value")
    return encoded


def hash_global_v2(domain: str, value: object) -> str:
    """Hash a canonical value under a V2-only ASCII domain."""

    _require_token_v2(domain, name="hash domain")
    digest = hashlib.sha256()
    digest.update(domain_sep_bytes(domain, version=2))
    digest.update(canonical_global_bytes_v2(value))
    return "0x" + digest.hexdigest()


def canonical_economic_command_body_bytes_v2(
    command_kind: str,
    command: object,
) -> bytes:
    _require_token_v2(command_kind, name="economic command body kind")
    return canonical_global_bytes_v2(
        {
            "command_kind": command_kind,
            "command": command,
        }
    )


def hash_economic_command_body_bytes_v2(command_body_bytes: bytes) -> str:
    if type(command_body_bytes) is not bytes:
        raise TypeError("economic command body bytes must be exact bytes")
    if not command_body_bytes:
        raise ValueError("economic command body bytes must not be empty")
    digest = hashlib.sha256()
    digest.update(domain_sep_bytes("authenticated-economic-command-body-v2", version=2))
    digest.update(command_body_bytes)
    return "0x" + digest.hexdigest()


def hash_economic_command_body_v2(command_kind: str, command: object) -> str:
    return hash_economic_command_body_bytes_v2(
        canonical_economic_command_body_bytes_v2(command_kind, command)
    )


def _require_tuple_v2(value: object, *, name: str) -> tuple[object, ...]:
    if type(value) is not tuple:
        raise TypeError(f"{name} must be a tuple")
    return value


def _require_sorted_unique_tokens_v2(
    values: object,
    *,
    name: str,
    allow_empty: bool = True,
) -> tuple[str, ...]:
    items = _require_tuple_v2(values, name=name)
    normalized = tuple(
        _require_token_v2(item, name=f"{name}[{index}]") for index, item in enumerate(items)
    )
    if not allow_empty and not normalized:
        raise ValueError(f"{name} must not be empty")
    if normalized != tuple(sorted(set(normalized))):
        raise ValueError(f"{name} must be sorted and unique")
    return normalized


def _require_ordered_objects_v2(
    values: object,
    *,
    name: str,
    expected_type: type[object],
    key: str,
) -> tuple[object, ...]:
    items = _require_tuple_v2(values, name=name)
    if any(type(item) is not expected_type for item in items):
        raise TypeError(f"{name} contains an invalid value")
    keys = tuple(getattr(item, key) for item in items)
    if keys != tuple(sorted(set(keys))):
        raise ValueError(f"{name} must be canonically ordered and unique")
    return items


class LaneIdV2(str, Enum):
    ASSET_TRANSFER = "ASSET_TRANSFER"
    SPOT_LIQUIDITY = "SPOT_LIQUIDITY"
    FARM_INCENTIVES = "FARM_INCENTIVES"
    ZDEX_TOKENOMICS = "ZDEX_TOKENOMICS"
    ZUSD_MONETARY = "ZUSD_MONETARY"
    PERPS_MARKET = "PERPS_MARKET"
    ORACLE_MARKET = "ORACLE_MARKET"
    SEALED_AUCTION = "SEALED_AUCTION"
    STRATEGY_ESCROW = "STRATEGY_ESCROW"
    PROOF_REWARDS = "PROOF_REWARDS"
    EXTERNAL_CUSTODY = "EXTERNAL_CUSTODY"
    GOVERNANCE_MIGRATION = "GOVERNANCE_MIGRATION"


ALL_LANE_IDS_V2: Final = tuple(LaneIdV2)


@dataclass(frozen=True, slots=True, order=True)
class EconomicAmountV2:
    owner: str
    asset: str
    custody_domain: str
    amount_atoms: int

    def __post_init__(self) -> None:
        _require_token_v2(self.owner, name="economic amount owner")
        _require_token_v2(self.asset, name="economic amount asset")
        _require_token_v2(self.custody_domain, name="economic amount custody domain")
        _require_atoms_u128_v2(self.amount_atoms, name="economic amount atoms")

    @property
    def key(self) -> tuple[str, str, str]:
        return (self.asset, self.owner, self.custody_domain)

    def to_canonical(self) -> dict[str, object]:
        return {
            "owner": self.owner,
            "asset": self.asset,
            "custody_domain": self.custody_domain,
            "amount_atoms": self.amount_atoms,
        }


@dataclass(frozen=True, slots=True, order=True)
class AssetSupplyV2:
    asset: str
    amount_atoms: int

    def __post_init__(self) -> None:
        _require_token_v2(self.asset, name="supply asset")
        _require_atoms_u128_v2(self.amount_atoms, name="supply atoms")

    def to_canonical(self) -> dict[str, object]:
        return {"asset": self.asset, "amount_atoms": self.amount_atoms}


@dataclass(frozen=True, slots=True, order=True)
class OracleOccurrenceStateV2:
    oracle_id: str
    occurrence_root: str
    observed_height: int
    finalized: bool

    def __post_init__(self) -> None:
        _require_token_v2(self.oracle_id, name="Oracle id")
        _require_root_v2(self.occurrence_root, name="Oracle occurrence root")
        _require_nonnegative_int_v2(self.observed_height, name="Oracle observed height")
        _require_bool_v2(self.finalized, name="Oracle finalized")

    def to_canonical(self) -> dict[str, object]:
        return {
            "oracle_id": self.oracle_id,
            "occurrence_root": self.occurrence_root,
            "observed_height": self.observed_height,
            "finalized": self.finalized,
        }


@dataclass(frozen=True, slots=True, order=True)
class OracleOccurrenceDeltaV2:
    oracle_id: str
    pre_occurrence: OracleOccurrenceStateV2 | None
    post_occurrence: OracleOccurrenceStateV2

    def __post_init__(self) -> None:
        _require_token_v2(self.oracle_id, name="Oracle occurrence delta id")
        if (
            self.pre_occurrence is not None
            and type(self.pre_occurrence) is not OracleOccurrenceStateV2
        ):
            raise TypeError("Oracle occurrence delta pre-value must be exact")
        if type(self.post_occurrence) is not OracleOccurrenceStateV2:
            raise TypeError("Oracle occurrence delta post-value must be exact")
        if self.post_occurrence.oracle_id != self.oracle_id:
            raise ValueError("Oracle occurrence delta post identity mismatch")
        if self.pre_occurrence is None:
            return
        if self.pre_occurrence.oracle_id != self.oracle_id:
            raise ValueError("Oracle occurrence delta pre identity mismatch")
        if self.pre_occurrence == self.post_occurrence:
            raise ValueError("Oracle occurrence delta must change the occurrence")
        if self.post_occurrence.observed_height < self.pre_occurrence.observed_height:
            raise ValueError("Oracle occurrence height cannot regress")
        if (
            self.post_occurrence.observed_height == self.pre_occurrence.observed_height
            and self.post_occurrence.occurrence_root != self.pre_occurrence.occurrence_root
        ):
            raise ValueError("Oracle occurrence root is immutable at one observed height")

    def to_canonical(self) -> dict[str, object]:
        return {
            "oracle_id": self.oracle_id,
            "pre_occurrence": self.pre_occurrence,
            "post_occurrence": self.post_occurrence,
        }


@dataclass(frozen=True, slots=True)
class GlobalOracleOccurrencePlanV2:
    deltas: tuple[OracleOccurrenceDeltaV2, ...] = ()

    def __post_init__(self) -> None:
        _require_ordered_objects_v2(
            self.deltas,
            name="global Oracle occurrence plan deltas",
            expected_type=OracleOccurrenceDeltaV2,
            key="oracle_id",
        )
        if len(self.deltas) > MAX_ORACLE_OCCURRENCE_DELTAS_PER_PLAN_V2:
            raise ValueError("global Oracle occurrence plan exceeds its bounded shape")

    @property
    def plan_root(self) -> str:
        if not self.deltas:
            return ZERO_ROOT_V2
        return hash_global_v2("global-oracle-occurrence-plan-v2", self.to_canonical())

    @classmethod
    def empty(cls) -> GlobalOracleOccurrencePlanV2:
        if cls is not GlobalOracleOccurrencePlanV2:
            raise TypeError("Oracle occurrence plan factory requires the exact type")
        return cls(())

    def to_canonical(self) -> dict[str, object]:
        return {"schema": GLOBAL_SETTLEMENT_ABI_V2, "deltas": self.deltas}


class TerminalObligationStatusV2(str, Enum):
    OPEN = "OPEN"
    DRAINED = "DRAINED"
    TOMBSTONED = "TOMBSTONED"


@dataclass(frozen=True, slots=True, order=True)
class TerminalObligationV2:
    obligation_id: str
    lane_id: LaneIdV2
    claimant: str
    asset: str
    liability_domain: str
    amount_atoms: int
    status: TerminalObligationStatusV2

    def __post_init__(self) -> None:
        _require_token_v2(self.obligation_id, name="terminal obligation id")
        if type(self.lane_id) is not LaneIdV2:
            raise TypeError("terminal obligation lane is not closed")
        _require_token_v2(self.claimant, name="terminal obligation claimant")
        _require_token_v2(self.asset, name="terminal obligation asset")
        _require_token_v2(
            self.liability_domain,
            name="terminal obligation liability domain",
        )
        _require_atoms_u128_v2(self.amount_atoms, name="terminal obligation amount")
        if type(self.status) is not TerminalObligationStatusV2:
            raise TypeError("terminal obligation status is not closed")

    def to_canonical(self) -> dict[str, object]:
        return {
            "obligation_id": self.obligation_id,
            "lane_id": self.lane_id,
            "claimant": self.claimant,
            "asset": self.asset,
            "liability_domain": self.liability_domain,
            "amount_atoms": self.amount_atoms,
            "status": self.status,
        }


@dataclass(frozen=True, slots=True, order=True)
class TerminalObligationDeltaV2:
    obligation_id: str
    pre_obligation: TerminalObligationV2 | None
    post_obligation: TerminalObligationV2

    def __post_init__(self) -> None:
        _require_token_v2(self.obligation_id, name="terminal obligation delta id")
        if (
            self.pre_obligation is not None
            and type(self.pre_obligation) is not TerminalObligationV2
        ):
            raise TypeError("terminal obligation delta pre-value must be exact")
        if type(self.post_obligation) is not TerminalObligationV2:
            raise TypeError("terminal obligation delta post-value must be exact")
        if self.post_obligation.obligation_id != self.obligation_id:
            raise ValueError("terminal obligation delta post identity mismatch")
        if self.pre_obligation is None:
            if self.post_obligation.status is not TerminalObligationStatusV2.OPEN:
                raise ValueError("new terminal obligation must begin open")
            return
        if self.pre_obligation.obligation_id != self.obligation_id:
            raise ValueError("terminal obligation delta pre identity mismatch")
        if (
            self.pre_obligation.lane_id,
            self.pre_obligation.claimant,
            self.pre_obligation.asset,
            self.pre_obligation.liability_domain,
        ) != (
            self.post_obligation.lane_id,
            self.post_obligation.claimant,
            self.post_obligation.asset,
            self.post_obligation.liability_domain,
        ):
            raise ValueError("terminal obligation identity fields are immutable")
        if self.pre_obligation.status is not TerminalObligationStatusV2.OPEN:
            raise ValueError("terminal obligation is already terminal")
        if self.post_obligation.status is TerminalObligationStatusV2.OPEN:
            if self.post_obligation.amount_atoms == self.pre_obligation.amount_atoms:
                raise ValueError("open terminal obligation must change amount or become terminal")
            return
        if self.post_obligation.amount_atoms != self.pre_obligation.amount_atoms:
            raise ValueError("terminal transition must preserve the final open amount")
        if self.post_obligation.status not in {
            TerminalObligationStatusV2.DRAINED,
            TerminalObligationStatusV2.TOMBSTONED,
        }:
            raise ValueError("open terminal obligation must move to a terminal status")

    def to_canonical(self) -> dict[str, object]:
        return {
            "obligation_id": self.obligation_id,
            "pre_obligation": self.pre_obligation,
            "post_obligation": self.post_obligation,
        }


@dataclass(frozen=True, slots=True)
class GlobalTerminalObligationPlanV2:
    deltas: tuple[TerminalObligationDeltaV2, ...] = ()

    def __post_init__(self) -> None:
        _require_ordered_objects_v2(
            self.deltas,
            name="global terminal obligation plan deltas",
            expected_type=TerminalObligationDeltaV2,
            key="obligation_id",
        )
        if len(self.deltas) > MAX_TERMINAL_OBLIGATION_DELTAS_PER_PLAN_V2:
            raise ValueError("global terminal obligation plan exceeds its bounded shape")

    @property
    def plan_root(self) -> str:
        if not self.deltas:
            return ZERO_ROOT_V2
        return hash_global_v2("global-terminal-obligation-plan-v2", self.to_canonical())

    @classmethod
    def empty(cls) -> GlobalTerminalObligationPlanV2:
        if cls is not GlobalTerminalObligationPlanV2:
            raise TypeError("terminal obligation plan factory requires the exact type")
        return cls(())

    def to_canonical(self) -> dict[str, object]:
        return {"schema": GLOBAL_SETTLEMENT_ABI_V2, "deltas": self.deltas}


class EconomicEffectKindV2(str, Enum):
    ACCOUNT_MOVEMENT = "ACCOUNT_MOVEMENT"
    ISSUE = "ISSUE"
    BURN = "BURN"
    CUSTODY = "CUSTODY"
    LIABILITY = "LIABILITY"
    RESERVE = "RESERVE"
    FEE_ALLOCATION = "FEE_ALLOCATION"
    REWARD = "REWARD"
    SLASH = "SLASH"


@dataclass(frozen=True, slots=True, order=True)
class EconomicEffectRowV2:
    kind: EconomicEffectKindV2
    principal: str
    asset: str
    custody_domain: str
    delta_atoms: int

    def __post_init__(self) -> None:
        if type(self.kind) is not EconomicEffectKindV2:
            raise TypeError("economic effect kind is not closed")
        _require_token_v2(self.principal, name="economic effect principal")
        _require_token_v2(self.asset, name="economic effect asset")
        _require_token_v2(self.custody_domain, name="economic effect custody domain")
        _require_delta_atoms_i128_v2(self.delta_atoms, name="economic effect delta")
        if self.delta_atoms == 0:
            raise ValueError("economic effect delta must be nonzero")
        if self.kind is EconomicEffectKindV2.ISSUE and self.delta_atoms < 0:
            raise ValueError("issue effect must be positive")
        if self.kind is EconomicEffectKindV2.BURN and self.delta_atoms > 0:
            raise ValueError("burn effect must be negative")

    @property
    def key(self) -> tuple[str, str, str, str]:
        return (self.kind.value, self.asset, self.principal, self.custody_domain)

    def to_canonical(self) -> dict[str, object]:
        return {
            "kind": self.kind,
            "principal": self.principal,
            "asset": self.asset,
            "custody_domain": self.custody_domain,
            "delta_atoms": self.delta_atoms,
        }


@dataclass(frozen=True, slots=True, order=True)
class AssetConservationRowV2:
    asset: str
    owned_and_custodied_pre_atoms: int
    owned_and_custodied_post_atoms: int
    supply_pre_atoms: int
    supply_post_atoms: int
    authorized_issue_atoms: int
    authorized_burn_atoms: int

    def __post_init__(self) -> None:
        _require_token_v2(self.asset, name="conservation asset")
        for field_name in (
            "owned_and_custodied_pre_atoms",
            "owned_and_custodied_post_atoms",
            "supply_pre_atoms",
            "supply_post_atoms",
            "authorized_issue_atoms",
            "authorized_burn_atoms",
        ):
            _require_atoms_u128_v2(
                getattr(self, field_name),
                name=f"conservation {field_name}",
            )
        expected_owned = (
            self.owned_and_custodied_pre_atoms
            + self.authorized_issue_atoms
            - self.authorized_burn_atoms
        )
        expected_supply = (
            self.supply_pre_atoms + self.authorized_issue_atoms - self.authorized_burn_atoms
        )
        if expected_owned < 0 or self.owned_and_custodied_post_atoms != expected_owned:
            raise ValueError("owned-and-custodied conservation mismatch")
        if expected_supply < 0 or self.supply_post_atoms != expected_supply:
            raise ValueError("supply conservation mismatch")

    def to_canonical(self) -> dict[str, object]:
        return {
            "asset": self.asset,
            "owned_and_custodied_pre_atoms": self.owned_and_custodied_pre_atoms,
            "owned_and_custodied_post_atoms": self.owned_and_custodied_post_atoms,
            "supply_pre_atoms": self.supply_pre_atoms,
            "supply_post_atoms": self.supply_post_atoms,
            "authorized_issue_atoms": self.authorized_issue_atoms,
            "authorized_burn_atoms": self.authorized_burn_atoms,
        }


@dataclass(frozen=True, slots=True, order=True)
class FeeConservationRowV2:
    asset: str
    fee_charged_atoms: int
    current_allocations_atoms: int
    carried_residue_atoms: int

    def __post_init__(self) -> None:
        _require_token_v2(self.asset, name="fee conservation asset")
        for field_name in (
            "fee_charged_atoms",
            "current_allocations_atoms",
            "carried_residue_atoms",
        ):
            _require_atoms_u128_v2(
                getattr(self, field_name),
                name=f"fee conservation {field_name}",
            )
        if self.fee_charged_atoms != (self.current_allocations_atoms + self.carried_residue_atoms):
            raise ValueError("fee allocation and carried residue do not reconcile")

    def to_canonical(self) -> dict[str, object]:
        return {
            "asset": self.asset,
            "fee_charged_atoms": self.fee_charged_atoms,
            "current_allocations_atoms": self.current_allocations_atoms,
            "carried_residue_atoms": self.carried_residue_atoms,
        }


@dataclass(frozen=True, slots=True, order=True)
class LaneWriteV2:
    lane_id: LaneIdV2
    pre_root: str
    post_root: str

    def __post_init__(self) -> None:
        if type(self.lane_id) is not LaneIdV2:
            raise TypeError("lane write lane is not closed")
        _require_root_v2(self.pre_root, name="lane write pre-root", allow_zero=True)
        _require_root_v2(self.post_root, name="lane write post-root", allow_zero=True)

    def to_canonical(self) -> dict[str, object]:
        return {
            "lane_id": self.lane_id,
            "pre_root": self.pre_root,
            "post_root": self.post_root,
        }


@dataclass(frozen=True, slots=True, order=True)
class ExternalOutboxEnqueueV2:
    effect_id: str
    destination_id: str
    payload_hash: str
    adapter_profile_root: str

    def __post_init__(self) -> None:
        _require_root_v2(self.effect_id, name="external outbox effect id")
        _require_token_v2(self.destination_id, name="external outbox destination")
        if self.destination_id.startswith("zenoledger:"):
            raise ValueError("same-ledger movement must not enter the external outbox")
        _require_root_v2(self.payload_hash, name="external outbox payload hash")
        _require_root_v2(
            self.adapter_profile_root,
            name="external outbox adapter profile root",
        )

    def to_canonical(self) -> dict[str, object]:
        return {
            "effect_id": self.effect_id,
            "destination_id": self.destination_id,
            "payload_hash": self.payload_hash,
            "adapter_profile_root": self.adapter_profile_root,
        }


@dataclass(frozen=True, slots=True)
class GlobalEconomicEffectPlanV2:
    rows: tuple[EconomicEffectRowV2, ...]
    asset_conservation: tuple[AssetConservationRowV2, ...]
    fee_conservation: tuple[FeeConservationRowV2, ...]
    lane_writes: tuple[LaneWriteV2, ...]
    occurrence_consumptions: tuple[str, ...]
    external_outbox_enqueue: tuple[ExternalOutboxEnqueueV2, ...]

    def __post_init__(self) -> None:
        self.validate()

    def validate(self) -> None:
        _require_ordered_objects_v2(
            self.rows,
            name="effect plan rows",
            expected_type=EconomicEffectRowV2,
            key="key",
        )
        _require_ordered_objects_v2(
            self.asset_conservation,
            name="effect plan asset conservation",
            expected_type=AssetConservationRowV2,
            key="asset",
        )
        _require_ordered_objects_v2(
            self.fee_conservation,
            name="effect plan fee conservation",
            expected_type=FeeConservationRowV2,
            key="asset",
        )
        _require_ordered_objects_v2(
            self.lane_writes,
            name="effect plan lane writes",
            expected_type=LaneWriteV2,
            key="lane_id",
        )
        consumptions = _require_sorted_unique_tokens_v2(
            self.occurrence_consumptions,
            name="effect plan occurrence consumptions",
        )
        for index, occurrence_id in enumerate(consumptions):
            _require_root_v2(
                occurrence_id,
                name=f"effect plan occurrence consumption[{index}]",
            )
        _require_ordered_objects_v2(
            self.external_outbox_enqueue,
            name="effect plan external outbox",
            expected_type=ExternalOutboxEnqueueV2,
            key="effect_id",
        )
        self._validate_issue_burn_projection()
        self._validate_fee_projection()

    def _validate_issue_burn_projection(self) -> None:
        issue_by_asset: dict[str, int] = {}
        burn_by_asset: dict[str, int] = {}
        for row in self.rows:
            if row.kind is EconomicEffectKindV2.ISSUE:
                issue_by_asset[row.asset] = issue_by_asset.get(row.asset, 0) + row.delta_atoms
            elif row.kind is EconomicEffectKindV2.BURN:
                burn_by_asset[row.asset] = burn_by_asset.get(row.asset, 0) - row.delta_atoms
        conservation_assets = {row.asset for row in self.asset_conservation}
        effect_assets = set(issue_by_asset) | set(burn_by_asset)
        if not effect_assets.issubset(conservation_assets):
            raise ValueError("issue or burn effect lacks an asset conservation row")
        for conservation_row in self.asset_conservation:
            if conservation_row.authorized_issue_atoms != issue_by_asset.get(
                conservation_row.asset,
                0,
            ):
                raise ValueError("authorized issue does not match canonical effect rows")
            if conservation_row.authorized_burn_atoms != burn_by_asset.get(
                conservation_row.asset,
                0,
            ):
                raise ValueError("authorized burn does not match canonical effect rows")

    def _validate_fee_projection(self) -> None:
        allocations: dict[str, int] = {}
        for row in self.rows:
            if row.kind is EconomicEffectKindV2.FEE_ALLOCATION:
                if row.delta_atoms < 0:
                    raise ValueError("fee allocation effect must be positive")
                allocations[row.asset] = allocations.get(row.asset, 0) + row.delta_atoms
        for fee_row in self.fee_conservation:
            if fee_row.current_allocations_atoms != allocations.get(fee_row.asset, 0):
                raise ValueError("fee conservation does not match canonical allocation effects")
        if not set(allocations).issubset({row.asset for row in self.fee_conservation}):
            raise ValueError("fee allocation effect lacks a fee conservation row")

    @property
    def effect_plan_root(self) -> str:
        self.validate()
        return hash_global_v2("global-economic-effect-plan-v2", self.to_canonical())

    @property
    def is_empty(self) -> bool:
        return not (
            self.rows
            or self.asset_conservation
            or self.fee_conservation
            or self.lane_writes
            or self.occurrence_consumptions
            or self.external_outbox_enqueue
        )

    @classmethod
    def empty(cls) -> GlobalEconomicEffectPlanV2:
        if cls is not GlobalEconomicEffectPlanV2:
            raise TypeError("effect plan factory requires the exact declared type")
        return cls((), (), (), (), (), ())

    def to_canonical(self) -> dict[str, object]:
        return {
            "schema": GLOBAL_SETTLEMENT_ABI_V2,
            "rows": self.rows,
            "asset_conservation": self.asset_conservation,
            "fee_conservation": self.fee_conservation,
            "lane_writes": self.lane_writes,
            "occurrence_consumptions": self.occurrence_consumptions,
            "external_outbox_enqueue": self.external_outbox_enqueue,
        }


__all__ = [
    "GLOBAL_SETTLEMENT_ABI_V2",
    "MAX_TOKEN_BYTES_V2",
    "MAX_U64_V2",
    "MAX_ATOMS_V2",
    "MIN_DELTA_ATOMS_V2",
    "MAX_DELTA_ATOMS_V2",
    "MAX_ORACLE_OCCURRENCE_DELTAS_PER_PLAN_V2",
    "MAX_TERMINAL_OBLIGATION_DELTAS_PER_PLAN_V2",
    "ZERO_ROOT_V2",
    "LaneIdV2",
    "ALL_LANE_IDS_V2",
    "EconomicAmountV2",
    "AssetSupplyV2",
    "OracleOccurrenceStateV2",
    "OracleOccurrenceDeltaV2",
    "GlobalOracleOccurrencePlanV2",
    "TerminalObligationStatusV2",
    "TerminalObligationV2",
    "TerminalObligationDeltaV2",
    "GlobalTerminalObligationPlanV2",
    "EconomicEffectKindV2",
    "EconomicEffectRowV2",
    "AssetConservationRowV2",
    "FeeConservationRowV2",
    "LaneWriteV2",
    "ExternalOutboxEnqueueV2",
    "GlobalEconomicEffectPlanV2",
    "canonical_global_bytes_v2",
    "canonical_economic_command_body_bytes_v2",
    "hash_economic_command_body_bytes_v2",
    "hash_economic_command_body_v2",
    "hash_global_v2",
]
