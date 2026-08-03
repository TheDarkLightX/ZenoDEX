"""Configuration-qualified current liabilities for allocated zUSD fees.

Each outstanding entry retains the configuration root, semantic role, and
destination selected when one exact borrowing-fee occurrence was allocated.
This prevents a later policy rotation from silently redirecting an older
claim.  The aggregate is a deterministic candidate and carries no state,
publication, or transfer authority.
"""

from __future__ import annotations

from dataclasses import InitVar, dataclass
from typing import Final, cast, final

from ..state.canonical import (
    canonical_hex_fixed_allow_0x,
    canonical_json_bytes,
    domain_sep_bytes,
    sha256_hex,
)
from ..state.state_snapshot_values import (
    MAX_STATE_STRING_CHARACTERS_V1,
    MAX_STATE_STRING_UTF8_BYTES_V1,
)
from .fcis_fee_apportionment_codec import canonical_sha256_fcis_fee_apportionment_v2
from .fcis_fee_apportionment_values import (
    COMMITTED_FEE_APPORTIONMENT_STATE_SCHEMA_ID_V2,
    CommittedFeeApportionmentStateV2,
)

ZUSD_PROTOCOL_FEE_ROLE_CLAIM_SCHEMA_V1: Final = "zenodex/zusd/protocol-fee-role-claim-state/v1"
MAX_ZUSD_PROTOCOL_FEE_ROLE_CLAIM_ENTRIES_V1: Final = 4_096

_U256_MAX: Final = (1 << 256) - 1
_ROLES_V1: Final = ("buyback", "treasury", "rewards")
_ROLE_ORDER_V1: Final = {role: index for index, role in enumerate(_ROLES_V1)}
_ENTRY_CONSTRUCTION_TOKEN_V1 = object()
_STATE_CONSTRUCTION_TOKEN_V1 = object()


def _require_text_v1(name: str, value: object) -> str:
    if type(value) is not str or not value:
        raise TypeError(f"{name} must be an exact nonempty string")
    if len(value) > MAX_STATE_STRING_CHARACTERS_V1:
        raise ValueError(f"{name} exceeds its character bound")
    try:
        encoded = value.encode("utf-8")
    except UnicodeEncodeError as exc:
        raise ValueError(f"{name} must contain Unicode scalar values") from exc
    if len(encoded) > MAX_STATE_STRING_UTF8_BYTES_V1:
        raise ValueError(f"{name} exceeds its UTF-8 bound")
    return value


def _require_digest_v1(name: str, value: object) -> str:
    if (
        type(value) is not str
        or len(value) != 66
        or not value.startswith("0x")
        or any(character not in "0123456789abcdef" for character in value[2:])
    ):
        raise TypeError(f"{name} must be a lowercase 32-byte hex digest")
    return value


def _require_asset_id_v1(value: object) -> str:
    if type(value) is not str:
        raise TypeError("asset_id must be an exact string")
    return canonical_hex_fixed_allow_0x(value, nbytes=32, name="asset_id")


def _require_custody_pubkey_v1(value: object) -> str:
    if type(value) is not str:
        raise TypeError("scalar_claim_custody_pubkey must be an exact string")
    return canonical_hex_fixed_allow_0x(
        value,
        nbytes=48,
        name="scalar_claim_custody_pubkey",
    )


def _apportionment_state_digest_v1(value: object) -> str:
    if type(value) is not CommittedFeeApportionmentStateV2:
        raise TypeError("apportionment_state must be exact")
    exact = cast(CommittedFeeApportionmentStateV2, value)
    exact.__post_init__()
    return canonical_sha256_fcis_fee_apportionment_v2(
        COMMITTED_FEE_APPORTIONMENT_STATE_SCHEMA_ID_V2,
        exact,
    )


def _require_u256_v1(name: str, value: object) -> int:
    if type(value) is not int:
        raise TypeError(f"{name} must be an exact int")
    if value < 0:
        raise ValueError(f"{name} is below its minimum")
    if value > _U256_MAX:
        raise OverflowError(f"{name} exceeds U256")
    return value


def _require_positive_u256_v1(name: str, value: object) -> int:
    exact = _require_u256_v1(name, value)
    if exact == 0:
        raise ValueError(f"{name} must be positive")
    return exact


@final
@dataclass(frozen=True, slots=True)
class ZUSDProtocolFeeRoleClaimEntryV1:
    """One nonzero liability under the exact allocation profile that created it."""

    configuration_root: str
    role: str
    destination: str
    outstanding_e8: int
    _construction_token: InitVar[object] = None

    def __post_init__(self, _construction_token: object) -> None:
        if _construction_token is not _ENTRY_CONSTRUCTION_TOKEN_V1:
            raise TypeError("protocol fee role claim entries require controlled derivation")
        self._revalidate()

    def _revalidate(self) -> None:
        _require_digest_v1("configuration_root", self.configuration_root)
        if type(self.role) is not str or self.role not in _ROLE_ORDER_V1:
            raise TypeError("protocol fee role must be exact and supported")
        _require_text_v1("protocol fee destination", self.destination)
        _require_positive_u256_v1("outstanding_e8", self.outstanding_e8)

    @property
    def protocol_order_key(self) -> tuple[bytes, int, bytes]:
        return (
            bytes.fromhex(self.configuration_root[2:]),
            _ROLE_ORDER_V1[self.role],
            self.destination.encode("utf-8"),
        )


def _validate_entries_v1(entries: object) -> tuple[ZUSDProtocolFeeRoleClaimEntryV1, ...]:
    if type(entries) is not tuple:
        raise TypeError("outstanding role claims must be an exact tuple")
    if len(entries) > MAX_ZUSD_PROTOCOL_FEE_ROLE_CLAIM_ENTRIES_V1:
        raise ValueError("outstanding role claim entry limit exceeded")
    exact_entries = cast(tuple[object, ...], entries)
    previous: tuple[bytes, int, bytes] | None = None
    for entry_object in exact_entries:
        if type(entry_object) is not ZUSDProtocolFeeRoleClaimEntryV1:
            raise TypeError("outstanding role claims must contain exact entries")
        entry = entry_object
        entry._revalidate()
        current = entry.protocol_order_key
        if previous is not None and previous >= current:
            raise ValueError("outstanding role claims must be unique and canonically ordered")
        previous = current
    return cast(tuple[ZUSDProtocolFeeRoleClaimEntryV1, ...], entries)


@final
@dataclass(frozen=True, slots=True)
class ZUSDProtocolFeeRoleClaimStateV1:
    """Current configuration-qualified claims plus cumulative role accounting."""

    fee_distribution_domain_id: str
    asset_id: str
    scalar_claim_custody_pubkey: str
    apportionment_state_digest: str
    outstanding_entries: tuple[ZUSDProtocolFeeRoleClaimEntryV1, ...]
    accrued_buyback_cumulative_e8: int
    accrued_treasury_cumulative_e8: int
    accrued_rewards_cumulative_e8: int
    _construction_token: InitVar[object] = None

    def __post_init__(self, _construction_token: object) -> None:
        if _construction_token is not _STATE_CONSTRUCTION_TOKEN_V1:
            raise TypeError("protocol fee role claim states require controlled derivation")
        self._revalidate()

    def _revalidate(self) -> None:
        _require_text_v1(
            "fee_distribution_domain_id",
            self.fee_distribution_domain_id,
        )
        canonical_asset = _require_asset_id_v1(self.asset_id)
        if canonical_asset != self.asset_id:
            raise ValueError("protocol fee role claim asset must be canonical")
        canonical_custody = _require_custody_pubkey_v1(self.scalar_claim_custody_pubkey)
        if canonical_custody != self.scalar_claim_custody_pubkey:
            raise ValueError("protocol fee role claim custody must be canonical")
        _require_digest_v1(
            "apportionment_state_digest",
            self.apportionment_state_digest,
        )
        entries = _validate_entries_v1(self.outstanding_entries)
        for role, cumulative in zip(
            _ROLES_V1,
            self.accrued_cumulative_e8,
            strict=True,
        ):
            _require_u256_v1(f"accrued_{role}_cumulative_e8", cumulative)
        outstanding = _outstanding_by_role_v1(entries)
        if any(
            current > cumulative
            for current, cumulative in zip(
                outstanding,
                self.accrued_cumulative_e8,
                strict=True,
            )
        ):
            raise ValueError("outstanding role claim exceeds cumulative accrual")
        _checked_sum_u256_v1("outstanding_total_e8", outstanding)
        _checked_sum_u256_v1(
            "accrued_cumulative_total_e8",
            self.accrued_cumulative_e8,
        )

    @property
    def outstanding_e8(self) -> tuple[int, int, int]:
        return _outstanding_by_role_v1(self.outstanding_entries)

    @property
    def accrued_cumulative_e8(self) -> tuple[int, int, int]:
        return (
            self.accrued_buyback_cumulative_e8,
            self.accrued_treasury_cumulative_e8,
            self.accrued_rewards_cumulative_e8,
        )

    @property
    def outstanding_total_e8(self) -> int:
        return _checked_sum_u256_v1("outstanding_total_e8", self.outstanding_e8)

    @property
    def accrued_cumulative_total_e8(self) -> int:
        return _checked_sum_u256_v1(
            "accrued_cumulative_total_e8",
            self.accrued_cumulative_e8,
        )

    @property
    def state_root(self) -> str:
        body = {
            "schema": ZUSD_PROTOCOL_FEE_ROLE_CLAIM_SCHEMA_V1,
            "version": 1,
            "fee_distribution_domain_id": self.fee_distribution_domain_id,
            "asset_id": self.asset_id,
            "scalar_claim_custody_pubkey": self.scalar_claim_custody_pubkey,
            "apportionment_state_digest": self.apportionment_state_digest,
            "outstanding_entries": [
                {
                    "configuration_root": entry.configuration_root,
                    "role": entry.role,
                    "destination": entry.destination,
                    "outstanding_e8": entry.outstanding_e8,
                }
                for entry in self.outstanding_entries
            ],
            "accrued_cumulative_e8": list(self.accrued_cumulative_e8),
        }
        preimage = domain_sep_bytes(
            "zusd/protocol-fee-role-claim-state",
            version=1,
        ) + canonical_json_bytes(body)
        return cast(str, sha256_hex(preimage))


def _checked_sum_u256_v1(name: str, values: tuple[int, int, int]) -> int:
    total = sum(values)
    if total > _U256_MAX:
        raise OverflowError(f"{name} exceeds U256")
    return total


def _outstanding_by_role_v1(
    entries: tuple[ZUSDProtocolFeeRoleClaimEntryV1, ...],
) -> tuple[int, int, int]:
    amounts = [0, 0, 0]
    for entry in entries:
        index = _ROLE_ORDER_V1[entry.role]
        amounts[index] += entry.outstanding_e8
        if amounts[index] > _U256_MAX:
            raise OverflowError("role outstanding claim exceeds U256")
    return amounts[0], amounts[1], amounts[2]


def _construct_entry_v1(
    *,
    configuration_root: str,
    role: str,
    destination: str,
    outstanding_e8: int,
) -> ZUSDProtocolFeeRoleClaimEntryV1:
    return ZUSDProtocolFeeRoleClaimEntryV1(
        configuration_root=configuration_root,
        role=role,
        destination=destination,
        outstanding_e8=outstanding_e8,
        _construction_token=_ENTRY_CONSTRUCTION_TOKEN_V1,
    )


def _construct_state_v1(
    *,
    fee_distribution_domain_id: str,
    asset_id: str,
    scalar_claim_custody_pubkey: str,
    apportionment_state_digest: str,
    outstanding_entries: tuple[ZUSDProtocolFeeRoleClaimEntryV1, ...],
    accrued_cumulative_e8: tuple[int, int, int],
) -> ZUSDProtocolFeeRoleClaimStateV1:
    return ZUSDProtocolFeeRoleClaimStateV1(
        fee_distribution_domain_id=fee_distribution_domain_id,
        asset_id=asset_id,
        scalar_claim_custody_pubkey=scalar_claim_custody_pubkey,
        apportionment_state_digest=apportionment_state_digest,
        outstanding_entries=outstanding_entries,
        accrued_buyback_cumulative_e8=accrued_cumulative_e8[0],
        accrued_treasury_cumulative_e8=accrued_cumulative_e8[1],
        accrued_rewards_cumulative_e8=accrued_cumulative_e8[2],
        _construction_token=_STATE_CONSTRUCTION_TOKEN_V1,
    )


def empty_zusd_protocol_fee_role_claim_state_v1(
    *,
    fee_distribution_domain_id: object,
    asset_id: object,
    scalar_claim_custody_pubkey: object,
    apportionment_state: object,
) -> ZUSDProtocolFeeRoleClaimStateV1:
    return _construct_state_v1(
        fee_distribution_domain_id=_require_text_v1(
            "fee_distribution_domain_id",
            fee_distribution_domain_id,
        ),
        asset_id=_require_asset_id_v1(asset_id),
        scalar_claim_custody_pubkey=_require_custody_pubkey_v1(scalar_claim_custody_pubkey),
        apportionment_state_digest=_apportionment_state_digest_v1(apportionment_state),
        outstanding_entries=(),
        accrued_cumulative_e8=(0, 0, 0),
    )


def revalidate_zusd_protocol_fee_role_claim_state_v1(value: object) -> bool:
    if type(value) is not ZUSDProtocolFeeRoleClaimStateV1:
        return False
    try:
        value._revalidate()
    except (TypeError, ValueError, OverflowError, ArithmeticError):
        return False
    return True


def _accrued_entries_v1(
    pre_state: ZUSDProtocolFeeRoleClaimStateV1,
    configuration_root: str,
    destinations: tuple[str, str, str],
    amounts_e8: tuple[int, int, int],
) -> tuple[ZUSDProtocolFeeRoleClaimEntryV1, ...]:
    entries_by_key = {
        (entry.configuration_root, entry.role, entry.destination): entry.outstanding_e8
        for entry in pre_state.outstanding_entries
    }
    for role, destination, amount in zip(
        _ROLES_V1,
        destinations,
        amounts_e8,
        strict=True,
    ):
        if amount == 0:
            continue
        key = (configuration_root, role, destination)
        previous = entries_by_key.get(key, 0)
        if previous > _U256_MAX - amount:
            raise OverflowError("configuration-qualified role claim exceeds U256")
        entries_by_key[key] = previous + amount
    return tuple(
        sorted(
            (
                _construct_entry_v1(
                    configuration_root=configuration,
                    role=role,
                    destination=destination,
                    outstanding_e8=amount,
                )
                for (configuration, role, destination), amount in entries_by_key.items()
            ),
            key=lambda entry: entry.protocol_order_key,
        )
    )


def accrue_zusd_protocol_fee_role_claim_state_v1(
    *,
    expected_pre_state: ZUSDProtocolFeeRoleClaimStateV1,
    configuration_root: str,
    destinations: tuple[str, str, str],
    amounts_e8: tuple[int, int, int],
    post_apportionment_state: object,
) -> ZUSDProtocolFeeRoleClaimStateV1:
    """Accrue one conserved allocation under its exact configuration identity."""

    expected_pre_state._revalidate()
    _require_digest_v1("configuration_root", configuration_root)
    if type(destinations) is not tuple or len(destinations) != 3:
        raise TypeError("destinations must be one exact three-tuple")
    if type(amounts_e8) is not tuple or len(amounts_e8) != 3:
        raise TypeError("amounts_e8 must be one exact three-tuple")
    for role, destination in zip(_ROLES_V1, destinations, strict=True):
        _require_text_v1(f"{role}_destination", destination)
    for role, amount in zip(_ROLES_V1, amounts_e8, strict=True):
        _require_u256_v1(f"{role}_amount_e8", amount)

    entries = _accrued_entries_v1(
        expected_pre_state,
        configuration_root,
        destinations,
        amounts_e8,
    )
    cumulative = tuple(
        previous + amount
        for previous, amount in zip(
            expected_pre_state.accrued_cumulative_e8,
            amounts_e8,
            strict=True,
        )
    )
    for role, value in zip(_ROLES_V1, cumulative, strict=True):
        _require_u256_v1(f"accrued_{role}_cumulative_e8", value)
    return _construct_state_v1(
        fee_distribution_domain_id=expected_pre_state.fee_distribution_domain_id,
        asset_id=expected_pre_state.asset_id,
        scalar_claim_custody_pubkey=expected_pre_state.scalar_claim_custody_pubkey,
        apportionment_state_digest=_apportionment_state_digest_v1(post_apportionment_state),
        outstanding_entries=entries,
        accrued_cumulative_e8=cast(tuple[int, int, int], cumulative),
    )


__all__ = (
    "MAX_ZUSD_PROTOCOL_FEE_ROLE_CLAIM_ENTRIES_V1",
    "ZUSD_PROTOCOL_FEE_ROLE_CLAIM_SCHEMA_V1",
    "ZUSDProtocolFeeRoleClaimEntryV1",
    "ZUSDProtocolFeeRoleClaimStateV1",
    "accrue_zusd_protocol_fee_role_claim_state_v1",
    "empty_zusd_protocol_fee_role_claim_state_v1",
    "revalidate_zusd_protocol_fee_role_claim_state_v1",
)
