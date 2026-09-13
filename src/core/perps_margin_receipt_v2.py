"""Pure V2 perps margin statements and bounded replay frames.

The statement is a compact candidate description derived from the existing
joint transition.  A frame carries complete pre-state inputs for deterministic
replay; neither value authenticates a command or grants publication authority.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Final

from .asset_lane_custody_codec_v2 import decode_asset_lane_custody_state_v2
from .asset_lane_custody_state_v2 import (
    AssetLaneCustodyStateV2,
    snapshot_asset_lane_custody_state_v2,
)
from .global_economic_state_v2 import (
    GlobalEconomicStateV2,
    snapshot_global_economic_state_v2,
)
from .global_settlement_abi_v2_codec import (
    MAX_GLOBAL_SETTLEMENT_CODEC_BYTES_V2,
    GlobalSettlementCodecErrorV2,
    _load_canonical_object_v2,
)
from .global_settlement_types_v2 import canonical_global_bytes_v2
from .global_settlement_wire_codec_v2 import (
    GlobalSettlementWireCodecErrorV2,
    _decode_global_state_object_v2,
)
from .perps_margin_global_v2 import (
    PerpsMarginGlobalAcceptedV2,
    PerpsMarginGlobalRejectCodeV2,
    PerpsMarginGlobalRejectedV2,
    transition_perps_margin_global_v2,
)
from .perps_margin_state_v2 import PerpsMarginStateV2
from .perps_margin_wire_v2 import (
    PerpsMarginRequestV2,
    decode_perps_margin_request_v2,
    decode_perps_margin_state_v2,
)

PERPS_MARGIN_GLOBAL_STATEMENT_SCHEMA_V2: Final = "zenodex/perps-margin-global-statement/v2"
PERPS_MARGIN_FRAME_MAGIC_V2: Final = b"ZDPM2\x00"
MAX_PERPS_MARGIN_FRAME_COMPONENT_BYTES_V2: Final = MAX_GLOBAL_SETTLEMENT_CODEC_BYTES_V2
MAX_PERPS_MARGIN_FRAME_BYTES_V2: Final = 4 * (
    MAX_PERPS_MARGIN_FRAME_COMPONENT_BYTES_V2 + 4
) + len(PERPS_MARGIN_FRAME_MAGIC_V2)


def _snapshot_inputs_v2(
    assets: AssetLaneCustodyStateV2,
    margin: PerpsMarginStateV2,
    state: GlobalEconomicStateV2,
    request: PerpsMarginRequestV2,
) -> tuple[
    AssetLaneCustodyStateV2,
    PerpsMarginStateV2,
    GlobalEconomicStateV2,
    PerpsMarginRequestV2,
]:
    for value, expected, name in (
        (assets, AssetLaneCustodyStateV2, "assets"),
        (margin, PerpsMarginStateV2, "margin"),
        (state, GlobalEconomicStateV2, "global state"),
        (request, PerpsMarginRequestV2, "request"),
    ):
        if type(value) is not expected:
            raise TypeError(f"perps margin {name} must have its exact V2 type")
    return (
        snapshot_asset_lane_custody_state_v2(assets),
        PerpsMarginStateV2(margin.economic_state, margin.active_claims),
        snapshot_global_economic_state_v2(state),
        PerpsMarginRequestV2(request.command, request.occurrence, request.oracle),
    )


def _run_transition_v2(
    inputs: tuple[
        AssetLaneCustodyStateV2,
        PerpsMarginStateV2,
        GlobalEconomicStateV2,
        PerpsMarginRequestV2,
    ],
) -> PerpsMarginGlobalAcceptedV2 | PerpsMarginGlobalRejectedV2:
    assets, margin, state, request = inputs
    result = transition_perps_margin_global_v2(
        assets,
        margin,
        state,
        request.command,
        request.occurrence,
        request.oracle,
    )
    # Every committed successor must fit the same decoder used by the next
    # command. A valid predecessor alone does not establish that closure.
    if type(result) is PerpsMarginGlobalAcceptedV2 and any(
        len(canonical_global_bytes_v2(value)) > MAX_PERPS_MARGIN_FRAME_COMPONENT_BYTES_V2
        for value in (result.post_assets, result.post_margin, result.post_state)
    ):
        return PerpsMarginGlobalRejectedV2(
            PerpsMarginGlobalRejectCodeV2.SUCCESSOR_REJECTED, state.state_root, state.state_root,
        )
    return result


def _statement_bytes_v2(result: PerpsMarginGlobalAcceptedV2) -> bytes:
    return canonical_global_bytes_v2(
        {
            "schema": PERPS_MARGIN_GLOBAL_STATEMENT_SCHEMA_V2,
            "input_root": result.statement_root,
            "refinement_root": result.refinement.refinement_root,
        }
    )


def prepare_perps_margin_statement_v2(
    assets: AssetLaneCustodyStateV2,
    margin: PerpsMarginStateV2,
    state: GlobalEconomicStateV2,
    request: PerpsMarginRequestV2,
) -> bytes | PerpsMarginGlobalRejectedV2:
    """Run the actual pure transition and render its accepted statement bytes."""

    result = _run_transition_v2(_snapshot_inputs_v2(assets, margin, state, request))
    if type(result) is PerpsMarginGlobalRejectedV2:
        return result
    if type(result) is not PerpsMarginGlobalAcceptedV2:
        raise TypeError("perps margin transition returned an unexpected result")
    return _statement_bytes_v2(result)


def _frame_segments_v2(
    inputs: tuple[
        AssetLaneCustodyStateV2,
        PerpsMarginStateV2,
        GlobalEconomicStateV2,
        PerpsMarginRequestV2,
    ],
) -> tuple[bytes, bytes, bytes, bytes]:
    segments = tuple(canonical_global_bytes_v2(value) for value in inputs)
    if any(
        type(segment) is not bytes or not segment
        or len(segment) > MAX_PERPS_MARGIN_FRAME_COMPONENT_BYTES_V2
        for segment in segments
    ):
        raise ValueError("perps margin frame component exceeds its byte bound")
    return segments


def _encode_segments_v2(segments: tuple[bytes, bytes, bytes, bytes]) -> bytes:
    return PERPS_MARGIN_FRAME_MAGIC_V2 + b"".join(
        len(segment).to_bytes(4, "little") + segment for segment in segments
    )


def encode_perps_margin_frame_v2(
    assets: AssetLaneCustodyStateV2,
    margin: PerpsMarginStateV2,
    state: GlobalEconomicStateV2,
    request: PerpsMarginRequestV2,
) -> bytes:
    """Encode complete typed pre-state inputs for bounded deterministic replay."""

    inputs = _snapshot_inputs_v2(assets, margin, state, request)
    frame = _encode_segments_v2(_frame_segments_v2(inputs))
    if len(frame) > MAX_PERPS_MARGIN_FRAME_BYTES_V2:
        raise ValueError("perps margin frame exceeds its byte bound")
    return frame


def _decode_global_state_v2(raw: bytes) -> GlobalEconomicStateV2:
    try:
        value = _load_canonical_object_v2(raw)
        state = _decode_global_state_object_v2(value)
    except GlobalSettlementWireCodecErrorV2 as exc:
        raise GlobalSettlementCodecErrorV2(str(exc)) from exc
    except (RecursionError, TypeError, ValueError) as exc:
        raise GlobalSettlementCodecErrorV2("encoded global state is invalid V2") from exc
    if canonical_global_bytes_v2(state.to_canonical()) != raw:
        raise GlobalSettlementCodecErrorV2("encoded global state is not canonical V2")
    return state


def _decode_frame_segments_v2(frame: bytes) -> tuple[bytes, bytes, bytes, bytes]:
    if type(frame) is not bytes:
        raise GlobalSettlementCodecErrorV2("perps margin frame must be exact bytes")
    if len(frame) > MAX_PERPS_MARGIN_FRAME_BYTES_V2:
        raise GlobalSettlementCodecErrorV2("perps margin frame exceeds its byte bound")
    if not frame.startswith(PERPS_MARGIN_FRAME_MAGIC_V2):
        raise GlobalSettlementCodecErrorV2("perps margin frame magic is invalid")
    cursor = len(PERPS_MARGIN_FRAME_MAGIC_V2)
    segments: list[bytes] = []
    for index in range(4):
        if cursor + 4 > len(frame):
            raise GlobalSettlementCodecErrorV2("perps margin frame length is truncated")
        size = int.from_bytes(frame[cursor : cursor + 4], "little")
        cursor += 4
        if not 1 <= size <= MAX_PERPS_MARGIN_FRAME_COMPONENT_BYTES_V2:
            raise GlobalSettlementCodecErrorV2(
                f"perps margin frame component {index} exceeds its byte bound"
            )
        end = cursor + size
        if end > len(frame):
            raise GlobalSettlementCodecErrorV2("perps margin frame component is truncated")
        segments.append(frame[cursor:end])
        cursor = end
    if cursor != len(frame):
        raise GlobalSettlementCodecErrorV2("perps margin frame has trailing bytes")
    return tuple(segments)  # type: ignore[return-value]


@dataclass(frozen=True, slots=True)
class PerpsMarginFrameReplayV2:
    """Owned accepted replay material reconstructed from one complete frame."""

    request: PerpsMarginRequestV2
    assets_pre: AssetLaneCustodyStateV2
    margin_pre: PerpsMarginStateV2
    global_pre: GlobalEconomicStateV2
    result: PerpsMarginGlobalAcceptedV2
    statement: bytes

    def __post_init__(self) -> None:
        if type(self.request) is not PerpsMarginRequestV2:
            raise TypeError("perps margin replay request must be exact")
        if type(self.assets_pre) is not AssetLaneCustodyStateV2:
            raise TypeError("perps margin replay assets must be exact")
        if type(self.margin_pre) is not PerpsMarginStateV2:
            raise TypeError("perps margin replay margin must be exact")
        if type(self.global_pre) is not GlobalEconomicStateV2:
            raise TypeError("perps margin replay global state must be exact")
        if type(self.result) is not PerpsMarginGlobalAcceptedV2:
            raise TypeError("perps margin replay result must be accepted V2")
        if type(self.statement) is not bytes:
            raise TypeError("perps margin replay statement must be exact bytes")
        owned_result = PerpsMarginGlobalAcceptedV2(
            self.result.post_assets,
            self.result.post_margin,
            self.result.post_state,
            self.result.effects,
            self.result.terminal_plan,
            self.result.refinement,
            self.result.statement_root,
        )
        if self.statement != _statement_bytes_v2(owned_result):
            raise ValueError("perps margin replay statement does not match result")
        object.__setattr__(self, "request", PerpsMarginRequestV2(
            self.request.command, self.request.occurrence, self.request.oracle
        ))
        object.__setattr__(self, "assets_pre", snapshot_asset_lane_custody_state_v2(self.assets_pre))
        object.__setattr__(self, "margin_pre", PerpsMarginStateV2(
            self.margin_pre.economic_state, self.margin_pre.active_claims
        ))
        object.__setattr__(self, "global_pre", snapshot_global_economic_state_v2(self.global_pre))
        object.__setattr__(self, "result", owned_result)
        object.__setattr__(self, "statement", bytes(self.statement))


def replay_perps_margin_frame_v2(frame: bytes) -> PerpsMarginFrameReplayV2:
    """Decode, re-encode, and rerun one accepted frame without publication authority."""

    segments = _decode_frame_segments_v2(frame)
    assets = decode_asset_lane_custody_state_v2(segments[0])
    margin = decode_perps_margin_state_v2(segments[1])
    state = _decode_global_state_v2(segments[2])
    request = decode_perps_margin_request_v2(segments[3])
    inputs = _snapshot_inputs_v2(assets, margin, state, request)
    if _encode_segments_v2(_frame_segments_v2(inputs)) != frame:
        raise GlobalSettlementCodecErrorV2("perps margin frame does not re-encode exactly")
    result = _run_transition_v2(inputs)
    if type(result) is PerpsMarginGlobalRejectedV2:
        raise ValueError(f"cannot replay rejected perps margin transition: {result.code.value}")
    if type(result) is not PerpsMarginGlobalAcceptedV2:
        raise TypeError("perps margin transition returned an unexpected result")
    statement = _statement_bytes_v2(result)
    return PerpsMarginFrameReplayV2(request, assets, margin, state, result, statement)


__all__ = [
    "PERPS_MARGIN_GLOBAL_STATEMENT_SCHEMA_V2",
    "PERPS_MARGIN_FRAME_MAGIC_V2",
    "MAX_PERPS_MARGIN_FRAME_COMPONENT_BYTES_V2",
    "MAX_PERPS_MARGIN_FRAME_BYTES_V2",
    "PerpsMarginFrameReplayV2",
    "prepare_perps_margin_statement_v2",
    "encode_perps_margin_frame_v2",
    "replay_perps_margin_frame_v2",
]
