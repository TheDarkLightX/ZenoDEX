"""Global generic-token supply and balance-location accounting invariant."""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum

from ..core.dex import DexState
from ..core.generic_token_authority import (
    U32_MAX,
    GenericTokenAuthorityState,
)
from ..core.perps_token_accounting import (
    PerpsTokenAccountingError,
    PerpsTokenAmountNonIntegral,
    perps_market_locked_quote_units,
)
from ..state.balances import NATIVE_ASSET
from ..state.canonical import canonical_hex_fixed_allow_0x
from .zusd_monetary_bridge import ZUSDMonetaryState


@dataclass(frozen=True, slots=True)
class GenericTokenAccountedUnits:
    asset_id: str
    wallet_units: int
    pool_locked_units: int
    perps_locked_units: int
    stake_locked_units: int

    @property
    def total_units(self) -> int:
        return (
            self.wallet_units
            + self.pool_locked_units
            + self.perps_locked_units
            + self.stake_locked_units
        )


@dataclass(frozen=True, slots=True)
class GenericTokenAccountingProjection:
    assets: tuple[GenericTokenAccountedUnits, ...]

    def __post_init__(self) -> None:
        if type(self.assets) is not tuple:
            raise TypeError("assets must be a tuple")
        previous_asset: str | None = None
        for asset in self.assets:
            if type(asset) is not GenericTokenAccountedUnits:
                raise TypeError("assets must contain GenericTokenAccountedUnits")
            if previous_asset is not None and asset.asset_id <= previous_asset:
                raise ValueError("accounting assets must be unique and strictly sorted")
            previous_asset = asset.asset_id

    def get_asset(self, asset_id: str) -> GenericTokenAccountedUnits | None:
        for asset in self.assets:
            if asset.asset_id == asset_id:
                return asset
            if asset.asset_id > asset_id:
                break
        return None


class GenericTokenAccountingRejectCode(str, Enum):
    LEGACY_VAULT_ASSET_UNTYPED = "legacy_vault_asset_untyped"
    NONCANONICAL_ASSET_ID = "noncanonical_asset_id"
    INVALID_ACCOUNTED_AMOUNT = "invalid_accounted_amount"
    NON_WHOLE_PERPS_AMOUNT = "non_whole_perps_amount"
    STAKE_ASSET_MISSING = "stake_asset_missing"
    CANONICAL_ZUSD_REGISTERED = "canonical_zusd_registered"
    ACCOUNTED_UNITS_OVERFLOW = "accounted_units_overflow"
    UNREGISTERED_ACCOUNTED_ASSET = "unregistered_accounted_asset"
    SUPPLY_ACCOUNTING_MISMATCH = "supply_accounting_mismatch"


@dataclass(frozen=True, slots=True)
class GenericTokenAccountingViolation:
    code: GenericTokenAccountingRejectCode
    asset_id: str | None = None
    committed_supply_units: int | None = None
    accounted_units: int | None = None


@dataclass(frozen=True, slots=True)
class GenericTokenAccountingDecision:
    accepted: bool
    projection: GenericTokenAccountingProjection | None = None
    violation: GenericTokenAccountingViolation | None = None

    def __post_init__(self) -> None:
        if type(self.accepted) is not bool:
            raise TypeError("accepted must be a bool")
        if self.accepted:
            if not isinstance(self.projection, GenericTokenAccountingProjection):
                raise ValueError("accepted accounting decision requires projection")
            if self.violation is not None:
                raise ValueError("accepted accounting decision cannot carry violation")
            return
        if self.projection is not None or not isinstance(
            self.violation,
            GenericTokenAccountingViolation,
        ):
            raise ValueError("rejected accounting decision requires one violation")


def _rejected(
    code: GenericTokenAccountingRejectCode,
    *,
    asset_id: str | None = None,
    committed_supply_units: int | None = None,
    accounted_units: int | None = None,
) -> GenericTokenAccountingDecision:
    return GenericTokenAccountingDecision(
        accepted=False,
        violation=GenericTokenAccountingViolation(
            code=code,
            asset_id=asset_id,
            committed_supply_units=committed_supply_units,
            accounted_units=accounted_units,
        ),
    )


def _canonical_observed_asset(asset_id: object) -> str:
    if not isinstance(asset_id, str):
        raise _ObservedAssetError("observed asset id must be a string")
    try:
        canonical = canonical_hex_fixed_allow_0x(
            asset_id,
            nbytes=32,
            name="observed asset id",
        )
    except (TypeError, ValueError) as exc:
        raise _ObservedAssetError(str(exc)) from exc
    if canonical != asset_id:
        raise _ObservedAssetError(
            "observed asset id must use canonical lowercase wire form"
        )
    return canonical


def _add_units(totals: dict[str, int], asset_id: str, amount: object) -> None:
    if type(amount) is not int or amount < 0:
        raise _AccountedAmountError(
            "accounted token amount must be a non-negative int"
        )
    totals[asset_id] = totals.get(asset_id, 0) + amount


class _ObservedAssetError(ValueError):
    pass


class _AccountedAmountError(ValueError):
    pass


def _strict_sum(values: object, *, name: str) -> int:
    if not isinstance(values, dict):
        raise _AccountedAmountError(f"{name} must be a dictionary")
    total = 0
    for pubkey, amount in sorted(values.items()):
        if not isinstance(pubkey, str):
            raise _AccountedAmountError(f"{name} keys must be strings")
        if type(amount) is not int or amount < 0:
            raise _AccountedAmountError(
                f"{name} values must be non-negative ints"
            )
        total += amount
    return total


def _is_generic_asset(asset_id: str, *, canonical_zusd_asset: str) -> bool:
    return asset_id not in {NATIVE_ASSET, canonical_zusd_asset}


def evaluate_generic_token_accounting(
    *,
    authority_state: GenericTokenAuthorityState,
    dex_state: DexState,
    monetary_state: ZUSDMonetaryState | None,
    canonical_zusd_asset: str,
) -> GenericTokenAccountingDecision:
    """Check committed generic supply against every represented token unit.

    The function is deterministic and observationally pure. Mutable mappings
    are fresh local builders. The returned projection is an immutable sorted
    value and shares no container with the input state.
    """

    if not isinstance(authority_state, GenericTokenAuthorityState):
        raise TypeError("authority_state must be a GenericTokenAuthorityState")
    if not isinstance(dex_state, DexState):
        raise TypeError("dex_state must be a DexState")
    if monetary_state is not None and not isinstance(monetary_state, ZUSDMonetaryState):
        raise TypeError("monetary_state must be a ZUSDMonetaryState or None")
    canonical_zusd = canonical_hex_fixed_allow_0x(
        canonical_zusd_asset,
        nbytes=32,
        name="canonical_zusd_asset",
    )
    if canonical_zusd != canonical_zusd_asset:
        raise ValueError("canonical_zusd_asset must use canonical lowercase wire form")
    if dex_state.vault is not None:
        return _rejected(
            GenericTokenAccountingRejectCode.LEGACY_VAULT_ASSET_UNTYPED
        )

    wallet_units: dict[str, int] = {}
    pool_units: dict[str, int] = {}
    perps_units: dict[str, int] = {}
    stake_units: dict[str, int] = {}
    try:
        for (_pubkey, raw_asset), amount in sorted(
            dex_state.balances.get_all_balances().items()
        ):
            asset = _canonical_observed_asset(raw_asset)
            if _is_generic_asset(asset, canonical_zusd_asset=canonical_zusd):
                _add_units(wallet_units, asset, amount)

        for pool_id in sorted(dex_state.pools):
            pool = dex_state.pools[pool_id]
            asset0 = _canonical_observed_asset(pool.asset0)
            asset1 = _canonical_observed_asset(pool.asset1)
            if _is_generic_asset(asset0, canonical_zusd_asset=canonical_zusd):
                _add_units(pool_units, asset0, pool.reserve0)
            if _is_generic_asset(asset1, canonical_zusd_asset=canonical_zusd):
                _add_units(pool_units, asset1, pool.reserve1)

        if dex_state.perps is not None:
            for market_id in sorted(dex_state.perps.markets):
                market = dex_state.perps.markets[market_id]
                asset = _canonical_observed_asset(market.quote_asset)
                if not _is_generic_asset(asset, canonical_zusd_asset=canonical_zusd):
                    continue
                try:
                    locked_units = perps_market_locked_quote_units(market)
                except PerpsTokenAmountNonIntegral:
                    return _rejected(
                        GenericTokenAccountingRejectCode.NON_WHOLE_PERPS_AMOUNT,
                        asset_id=asset,
                    )
                except (PerpsTokenAccountingError, TypeError):
                    return _rejected(
                        GenericTokenAccountingRejectCode.INVALID_ACCOUNTED_AMOUNT,
                        asset_id=asset,
                    )
                _add_units(perps_units, asset, locked_units)

        if monetary_state is not None:
            active_units = _strict_sum(
                dict(monetary_state.active_fee_stakes or {}),
                name="active_fee_stakes",
            )
            pending_units = _strict_sum(
                dict(monetary_state.pending_fee_stakes or {}),
                name="pending_fee_stakes",
            )
            total_stake_units = active_units + pending_units
            stake_asset = monetary_state.policy_binding.fee_stake_asset_id
            if total_stake_units > 0 and stake_asset is None:
                return _rejected(
                    GenericTokenAccountingRejectCode.STAKE_ASSET_MISSING
                )
            if stake_asset is not None and total_stake_units > 0:
                asset = _canonical_observed_asset(stake_asset)
                if _is_generic_asset(asset, canonical_zusd_asset=canonical_zusd):
                    _add_units(stake_units, asset, total_stake_units)
    except _ObservedAssetError:
        return _rejected(GenericTokenAccountingRejectCode.NONCANONICAL_ASSET_ID)
    except _AccountedAmountError:
        return _rejected(GenericTokenAccountingRejectCode.INVALID_ACCOUNTED_AMOUNT)

    registered_assets = {asset.asset_id for asset in authority_state.assets}
    for registered_asset in authority_state.assets:
        if registered_asset.asset_id == canonical_zusd:
            return _rejected(
                GenericTokenAccountingRejectCode.CANONICAL_ZUSD_REGISTERED,
                asset_id=registered_asset.asset_id,
                committed_supply_units=registered_asset.total_supply_units,
            )

    observed_assets = set(wallet_units) | set(pool_units) | set(perps_units) | set(stake_units)
    projection_assets: list[GenericTokenAccountedUnits] = []
    for asset_id in sorted(registered_assets | observed_assets):
        accounted = GenericTokenAccountedUnits(
            asset_id=asset_id,
            wallet_units=wallet_units.get(asset_id, 0),
            pool_locked_units=pool_units.get(asset_id, 0),
            perps_locked_units=perps_units.get(asset_id, 0),
            stake_locked_units=stake_units.get(asset_id, 0),
        )
        if accounted.total_units > U32_MAX:
            return _rejected(
                GenericTokenAccountingRejectCode.ACCOUNTED_UNITS_OVERFLOW,
                asset_id=asset_id,
                accounted_units=accounted.total_units,
            )
        registered = authority_state.get_asset(asset_id)
        if registered is None:
            return _rejected(
                GenericTokenAccountingRejectCode.UNREGISTERED_ACCOUNTED_ASSET,
                asset_id=asset_id,
                accounted_units=accounted.total_units,
            )
        if registered.total_supply_units != accounted.total_units:
            return _rejected(
                GenericTokenAccountingRejectCode.SUPPLY_ACCOUNTING_MISMATCH,
                asset_id=asset_id,
                committed_supply_units=registered.total_supply_units,
                accounted_units=accounted.total_units,
            )
        projection_assets.append(accounted)

    return GenericTokenAccountingDecision(
        accepted=True,
        projection=GenericTokenAccountingProjection(assets=tuple(projection_assets)),
    )


def generic_token_accounting_error(
    *,
    authority_state: GenericTokenAuthorityState,
    dex_state: DexState,
    monetary_state: ZUSDMonetaryState | None,
    canonical_zusd_asset: str,
) -> str | None:
    """Return one canonical invariant error, or ``None`` when consistent."""

    decision = evaluate_generic_token_accounting(
        authority_state=authority_state,
        dex_state=dex_state,
        monetary_state=monetary_state,
        canonical_zusd_asset=canonical_zusd_asset,
    )
    if decision.accepted:
        return None
    violation = decision.violation
    if violation is None:
        raise RuntimeError("rejected accounting decision must carry a violation")
    details: list[str] = []
    if violation.asset_id is not None:
        details.append(f"asset={violation.asset_id}")
    if violation.committed_supply_units is not None:
        details.append(
            f"committed_supply={violation.committed_supply_units}"
        )
    if violation.accounted_units is not None:
        details.append(f"accounted_units={violation.accounted_units}")
    suffix = "" if not details else " (" + ", ".join(details) + ")"
    return violation.code.value + suffix
