from __future__ import annotations

from dataclasses import dataclass
from itertools import product
from typing import Iterable

from .cantor_prefix_algebra import CantorPrefixRegion, partition_ok
from .zusd_oracle_contracts import ZUSDOraclePendingGateContract


RecoveryModeWord = tuple[int, int, int, int, int, int]


@dataclass(frozen=True)
class ZUSDRecoveryModeGateInputs:
    oracle_seen: bool
    price_pos: bool
    pending_eq: bool
    fresh: bool
    tcr_ok: bool
    risky_requested: bool

    def to_word(self) -> RecoveryModeWord:
        return (
            int(bool(self.oracle_seen)),
            int(bool(self.price_pos)),
            int(bool(self.pending_eq)),
            int(bool(self.fresh)),
            int(bool(self.tcr_ok)),
            int(bool(self.risky_requested)),
        )

    @classmethod
    def from_word(cls, word: Iterable[int | bool]) -> "ZUSDRecoveryModeGateInputs":
        bits = tuple(int(bool(bit)) for bit in word)
        if len(bits) != 6:
            raise ValueError("zUSD recovery mode gate words must have exactly 6 bits")
        return cls(
            oracle_seen=bool(bits[0]),
            price_pos=bool(bits[1]),
            pending_eq=bool(bits[2]),
            fresh=bool(bits[3]),
            tcr_ok=bool(bits[4]),
            risky_requested=bool(bits[5]),
        )

    @classmethod
    def from_contract(cls, contract: ZUSDOraclePendingGateContract) -> "ZUSDRecoveryModeGateInputs":
        return cls(
            oracle_seen=bool(contract.oracle_seen),
            price_pos=bool(contract.price_pos),
            pending_eq=bool(contract.pending_eq),
            fresh=bool(contract.fresh),
            tcr_ok=bool(contract.tcr_ok),
            risky_requested=bool(contract.risky_requested),
        )


@dataclass(frozen=True)
class ZUSDRecoveryModeGateRegions:
    env_ok: CantorPrefixRegion
    risky_ops_allowed: CantorPrefixRegion
    blocked_by_recovery: CantorPrefixRegion
    action_allowed: CantorPrefixRegion
    risky_action_allowed: CantorPrefixRegion
    safe_non_risky_action_allowed: CantorPrefixRegion
    recovery_blocked_request: CantorPrefixRegion
    env_degraded: CantorPrefixRegion
    denied: CantorPrefixRegion

    def partition_is_total(self) -> bool:
        return partition_ok((self.risky_action_allowed, self.safe_non_risky_action_allowed, self.denied))


_ALL_WORDS: tuple[RecoveryModeWord, ...] = tuple(
    tuple(int(bit) for bit in bits) for bits in product((0, 1), repeat=6)
)


def _region_from_words(words: Iterable[RecoveryModeWord]) -> CantorPrefixRegion:
    return CantorPrefixRegion(tuple(tuple(int(bit) for bit in word) for word in words))


def env_ok(inputs: ZUSDRecoveryModeGateInputs) -> bool:
    return inputs.oracle_seen and inputs.price_pos and inputs.pending_eq and inputs.fresh


def risky_ops_allowed(inputs: ZUSDRecoveryModeGateInputs) -> bool:
    return env_ok(inputs) and inputs.tcr_ok


def blocked_by_recovery(inputs: ZUSDRecoveryModeGateInputs) -> bool:
    return env_ok(inputs) and (not inputs.tcr_ok)


def action_allowed(inputs: ZUSDRecoveryModeGateInputs) -> bool:
    return (not inputs.risky_requested) or risky_ops_allowed(inputs)


def input_region(inputs: ZUSDRecoveryModeGateInputs) -> CantorPrefixRegion:
    return CantorPrefixRegion.from_prefix(inputs.to_word())


def contract_input_region(contract: ZUSDOraclePendingGateContract) -> CantorPrefixRegion:
    return input_region(ZUSDRecoveryModeGateInputs.from_contract(contract))


def build_zusd_recovery_mode_gate_regions() -> ZUSDRecoveryModeGateRegions:
    env_ok_region = _region_from_words(
        word for word in _ALL_WORDS if env_ok(ZUSDRecoveryModeGateInputs.from_word(word))
    )
    risky_ops_allowed_region = _region_from_words(
        word for word in _ALL_WORDS if risky_ops_allowed(ZUSDRecoveryModeGateInputs.from_word(word))
    )
    blocked_by_recovery_region = _region_from_words(
        word for word in _ALL_WORDS if blocked_by_recovery(ZUSDRecoveryModeGateInputs.from_word(word))
    )
    action_allowed_region = _region_from_words(
        word for word in _ALL_WORDS if action_allowed(ZUSDRecoveryModeGateInputs.from_word(word))
    )
    risky_action_allowed_region = _region_from_words(
        word
        for word in _ALL_WORDS
        if (
            ZUSDRecoveryModeGateInputs.from_word(word).risky_requested
            and risky_ops_allowed(ZUSDRecoveryModeGateInputs.from_word(word))
        )
    )
    safe_non_risky_action_allowed_region = _region_from_words(
        word
        for word in _ALL_WORDS
        if (
            (not ZUSDRecoveryModeGateInputs.from_word(word).risky_requested)
            and action_allowed(ZUSDRecoveryModeGateInputs.from_word(word))
        )
    )
    recovery_blocked_request_region = _region_from_words(
        word
        for word in _ALL_WORDS
        if (
            ZUSDRecoveryModeGateInputs.from_word(word).risky_requested
            and blocked_by_recovery(ZUSDRecoveryModeGateInputs.from_word(word))
        )
    )
    env_degraded_region = ~env_ok_region
    denied_region = ~action_allowed_region
    return ZUSDRecoveryModeGateRegions(
        env_ok=env_ok_region,
        risky_ops_allowed=risky_ops_allowed_region,
        blocked_by_recovery=blocked_by_recovery_region,
        action_allowed=action_allowed_region,
        risky_action_allowed=risky_action_allowed_region,
        safe_non_risky_action_allowed=safe_non_risky_action_allowed_region,
        recovery_blocked_request=recovery_blocked_request_region,
        env_degraded=env_degraded_region,
        denied=denied_region,
    )
