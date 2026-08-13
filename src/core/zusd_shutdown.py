"""Pure shutdown trigger semantics for the mounted zUSD profile."""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from typing import Any, Mapping

E8 = 100_000_000
BPS_SCALE = 10_000
MAX_AMOUNT_E8 = 10**30
MAX_TCR_BPS = 1_000_000_000


class ZUSDShutdownPhase(str, Enum):
    OPEN = "OPEN"
    FROZEN = "FROZEN"


class ZUSDShutdownExtensionProfile(str, Enum):
    """Closed profile tag for the separately mounted shutdown extension."""

    TERMINAL_FREEZE_V1 = "zenodex/zusd-terminal-freeze-v1"


_LOWER_HEX = frozenset("0123456789abcdef")


def require_shutdown_source_state_root(value: object) -> str:
    """Return a canonical 32-byte state root or reject it.

    The deterministic core validates shape only. The imperative shell remains
    responsible for authenticating the root and binding it to the complete
    mounted protocol state used to construct the shutdown snapshot.
    """

    if (
        not isinstance(value, str)
        or len(value) != 64
        or any(ch not in _LOWER_HEX for ch in value)
    ):
        raise ValueError(
            "shutdown_source_state_root must be 64 lowercase hex characters"
        )
    return value


@dataclass(frozen=True)
class ZUSDShutdownExtensionState:
    """State owned solely by the optional terminal-freeze extension.

    The trigger threshold is intentionally absent. A mounted instance derives
    it exactly from the baseline state's MCR, so it cannot narrow Liquity V1
    redemption admission through an independently configured ratio.
    """

    profile: ZUSDShutdownExtensionProfile = (
        ZUSDShutdownExtensionProfile.TERMINAL_FREEZE_V1
    )
    phase: ZUSDShutdownPhase = ZUSDShutdownPhase.OPEN
    epoch: int = 0
    oracle_observed_epoch: int = 0
    price_e8: int = 0
    collateral_e8: int = 0
    debt_e8: int = 0
    source_state_root: str = ""

    def __post_init__(self) -> None:
        if type(self.profile) is not ZUSDShutdownExtensionProfile:
            raise TypeError("shutdown extension profile must be exactly typed")
        if type(self.phase) is not ZUSDShutdownPhase:
            raise TypeError("shutdown extension phase must be exactly typed")
        for name in (
            "epoch",
            "oracle_observed_epoch",
            "price_e8",
            "collateral_e8",
            "debt_e8",
        ):
            _bounded_nonnegative(
                getattr(self, name),
                name=f"shutdown_extension.{name}",
                maximum=MAX_AMOUNT_E8,
            )
        snapshot = (
            self.epoch,
            self.oracle_observed_epoch,
            self.price_e8,
            self.collateral_e8,
            self.debt_e8,
        )
        if self.phase is ZUSDShutdownPhase.OPEN:
            if any(snapshot) or self.source_state_root != "":
                raise ValueError("OPEN shutdown extension requires an empty snapshot")
        else:
            require_shutdown_source_state_root(self.source_state_root)

    def to_obj(self) -> dict[str, Any]:
        return {
            "profile": self.profile.value,
            "phase": self.phase.value,
            "epoch": self.epoch,
            "oracle_observed_epoch": self.oracle_observed_epoch,
            "price_e8": self.price_e8,
            "collateral_e8": self.collateral_e8,
            "debt_e8": self.debt_e8,
            "source_state_root": self.source_state_root,
        }

    @classmethod
    def from_obj(cls, obj: object) -> ZUSDShutdownExtensionState:
        if not isinstance(obj, Mapping):
            raise TypeError("shutdown_extension must be an object")
        expected = {
            "profile",
            "phase",
            "epoch",
            "oracle_observed_epoch",
            "price_e8",
            "collateral_e8",
            "debt_e8",
            "source_state_root",
        }
        if set(obj) != expected:
            raise ValueError("shutdown_extension fields must match schema exactly")
        try:
            profile = ZUSDShutdownExtensionProfile(obj.get("profile"))
        except (TypeError, ValueError) as exc:
            raise ValueError("unsupported shutdown extension profile") from exc
        try:
            phase = ZUSDShutdownPhase(obj.get("phase"))
        except (TypeError, ValueError) as exc:
            raise ValueError("unsupported shutdown extension phase") from exc
        source_state_root = obj.get("source_state_root")
        if type(source_state_root) is not str:
            raise TypeError("shutdown_extension.source_state_root must be a str")
        return cls(
            profile=profile,
            phase=phase,
            epoch=_bounded_nonnegative(
                obj.get("epoch"),
                name="shutdown_extension.epoch",
                maximum=MAX_AMOUNT_E8,
            ),
            oracle_observed_epoch=_bounded_nonnegative(
                obj.get("oracle_observed_epoch"),
                name="shutdown_extension.oracle_observed_epoch",
                maximum=MAX_AMOUNT_E8,
            ),
            price_e8=_bounded_nonnegative(
                obj.get("price_e8"),
                name="shutdown_extension.price_e8",
                maximum=MAX_AMOUNT_E8,
            ),
            collateral_e8=_bounded_nonnegative(
                obj.get("collateral_e8"),
                name="shutdown_extension.collateral_e8",
                maximum=MAX_AMOUNT_E8,
            ),
            debt_e8=_bounded_nonnegative(
                obj.get("debt_e8"),
                name="shutdown_extension.debt_e8",
                maximum=MAX_AMOUNT_E8,
            ),
            source_state_root=source_state_root,
        )


def _bounded_nonnegative(value: object, *, name: str, maximum: int) -> int:
    if type(value) is not int:
        raise TypeError(f"{name} must be an int")
    if value < 0:
        raise ValueError(f"{name} must be non-negative")
    if value > maximum:
        raise ValueError(f"{name} exceeds maximum")
    return int(value)


def shutdown_triggered(
    *,
    collateral_e8: int,
    debt_e8: int,
    price_e8: int,
    shutdown_tcr_bps: int,
) -> bool:
    """Return whether a positive-debt branch is strictly below its shutdown TCR.

    The comparison is cross-multiplied, so no division, float, or rounding mode
    can change the boundary:

    ``collateral * price * 10_000 < debt * floor_bps * 10^8``.

    A zero floor disables shutdown activation. Zero debt never activates it.
    """

    collateral = _bounded_nonnegative(
        collateral_e8,
        name="collateral_e8",
        maximum=MAX_AMOUNT_E8,
    )
    debt = _bounded_nonnegative(
        debt_e8,
        name="debt_e8",
        maximum=MAX_AMOUNT_E8,
    )
    price = _bounded_nonnegative(
        price_e8,
        name="price_e8",
        maximum=MAX_AMOUNT_E8,
    )
    floor_bps = _bounded_nonnegative(
        shutdown_tcr_bps,
        name="shutdown_tcr_bps",
        maximum=MAX_TCR_BPS,
    )
    if debt == 0 or floor_bps == 0:
        return False
    return (collateral * price * BPS_SCALE) < (debt * floor_bps * E8)
