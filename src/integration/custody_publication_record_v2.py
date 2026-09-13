"""Complete isolated custody records, replayed without verifier or store I/O.

The existing guest input frame supplies both predecessors and the global
successor. Pure replay derives the complete custody successor. Authentication
messages retain publication-time evidence; they do not reselect historical
authorization registries or establish cryptographic success on recovery.
"""

from __future__ import annotations

import hashlib
from dataclasses import dataclass
from typing import cast

from ..core.asset_lane_coordinator_values_v2 import (
    AssetLaneCommandV2,
    AssetLaneRejectedV2,
    AssetLaneRouteV2,
)
from ..core.asset_lane_custody_codec_v2 import decode_asset_lane_custody_state_v2
from ..core.asset_lane_custody_coordinator_v2 import (
    AssetLaneCustodyAcceptedV2,
    transition_asset_lane_custody_v2,
)
from ..core.asset_lane_custody_frame_v2 import (
    MAX_ASSET_LANE_CUSTODY_GLOBAL_FRAME_BYTES_V2,
    decode_asset_lane_custody_global_frame_v2,
)
from ..core.asset_lane_custody_global_v2 import _require_complete_projection
from ..core.asset_lane_custody_input_v2 import _decode_context
from ..core.asset_lane_custody_state_v2 import AssetLaneCustodyStateV2
from ..core.asset_lane_custody_statement_v2 import prepare_asset_lane_custody_global_statement_v2
from ..core.asset_lane_state_v2 import AssetLaneContextV2
from ..core.economic_command_authentication_types_v2 import (
    ECONOMIC_COMMAND_AUTHENTICATION_SCHEMA_V2,
    EconomicCommandIntentV2,
)
from ..core.economic_command_authentication_v2 import (
    _AUTHENTICATION_MESSAGE_DOMAIN_V2,
    _INTENT_FIELDS_V2,
    _MESSAGE_FIELDS_V2,
    require_economic_command_intent_occurrence_v2,
)
from ..core.economic_command_signature_verifier_registry_v1 import MAX_COMMAND_SIGNATURE_BYTES_V1
from ..core.global_economic_state_v2 import GlobalEconomicStateV2
from ..core.global_settlement_abi_v2_codec import (
    decode_asset_transfer_command_v2,
    decode_managed_asset_lifecycle_command_v2,
)
from ..core.global_settlement_primitives_v2 import (
    GLOBAL_SETTLEMENT_ABI_V2,
    _require_nonnegative_int_v2,
    _require_root_v2,
    _require_token_v2,
    canonical_economic_command_body_bytes_v2,
    canonical_global_bytes_v2,
    hash_global_v2,
)
from ..core.global_settlement_wire_codec_v2 import (
    _decode_global_state_object_v2,
    _load_canonical_object_v2,
)
from ..core.perps_margin_claims_v2 import require_margin_claim_projection_v2
from ..core.perps_margin_receipt_v2 import replay_perps_margin_frame_v2
from ..core.perps_margin_state_v2 import PerpsMarginStateV2
from ..core.perps_margin_types_v1 import PerpsMarginCommandV1
from ..core.perps_margin_wire_v2 import PerpsMarginRequestV2, decode_perps_margin_state_v2
from ..state.canonical import domain_sep_bytes
from .global_receipt_verifier_v1 import MAX_JOURNAL_BYTES_V1, MAX_RECEIPT_BYTES_V1

JOINT_MARGIN_FRAME_MAGIC_V2 = b"ZDJM2\x00"
MAX_JOINT_MARGIN_FRAME_BYTES_V2 = (
    MAX_ASSET_LANE_CUSTODY_GLOBAL_FRAME_BYTES_V2 + 1_048_576 + 11
)


def raw_root_v2(raw: bytes) -> str:
    return "0x" + hashlib.sha256(raw).hexdigest()


def decode_custody_global_state_v2(raw: bytes) -> GlobalEconomicStateV2:
    return _decode_global_state_object_v2(_load_canonical_object_v2(raw))


@dataclass(frozen=True, slots=True)
class CustodyPublicationReplayV2:
    context: AssetLaneContextV2 | PerpsMarginRequestV2
    command: AssetLaneCommandV2 | PerpsMarginCommandV1
    global_pre: GlobalEconomicStateV2
    lane_pre: AssetLaneCustodyStateV2
    global_post: GlobalEconomicStateV2
    lane_post: AssetLaneCustodyStateV2
    statement: bytes
    margin_pre: PerpsMarginStateV2 | None = None
    margin_post: PerpsMarginStateV2 | None = None


def replay_custody_publication_frame_v2(frame: bytes) -> CustodyPublicationReplayV2:
    route, context_raw, lane_raw, command_raw, pre_raw, post_raw = (
        decode_asset_lane_custody_global_frame_v2(frame)
    )
    context = _decode_context(context_raw)
    lane_pre = decode_asset_lane_custody_state_v2(lane_raw)
    command: AssetLaneCommandV2
    if route is AssetLaneRouteV2.TRANSFER:
        command = decode_asset_transfer_command_v2(command_raw)
    else:
        command = decode_managed_asset_lifecycle_command_v2(command_raw)
    global_pre = decode_custody_global_state_v2(pre_raw)
    global_post = decode_custody_global_state_v2(post_raw)
    result = transition_asset_lane_custody_v2(context, lane_pre, command)
    if type(result) is AssetLaneRejectedV2:
        raise ValueError("a rejected custody transition cannot be a durable record")
    accepted = cast(AssetLaneCustodyAcceptedV2, result)
    statement = prepare_asset_lane_custody_global_statement_v2(
        context, lane_pre, command, global_pre, global_post
    )
    if type(statement) is not bytes:
        raise ValueError("custody publication statement is rejected")
    _require_complete_projection(accepted.post_state, global_post)
    return CustodyPublicationReplayV2(
        context, command, global_pre, lane_pre, global_post, accepted.post_state, statement
    )


def _require_authentication_transcript_v2(
    message: bytes, replay: CustodyPublicationReplayV2
) -> None:
    prefix = domain_sep_bytes(_AUTHENTICATION_MESSAGE_DOMAIN_V2, version=2)
    if not message.startswith(prefix):
        raise ValueError("custody authentication message domain mismatch")
    value = _load_canonical_object_v2(message[len(prefix) :])
    if (
        set(value) != set(_MESSAGE_FIELDS_V2)
        or value["schema"] != ECONOMIC_COMMAND_AUTHENTICATION_SCHEMA_V2
    ):
        raise ValueError("custody authentication message fields or schema mismatch")
    raw_intent = value["intent"]
    if type(raw_intent) is not dict or set(raw_intent) != {*_INTENT_FIELDS_V2, "schema"}:
        raise ValueError("custody authentication intent fields mismatch")
    if raw_intent["schema"] != ECONOMIC_COMMAND_AUTHENTICATION_SCHEMA_V2:
        raise ValueError("custody authentication intent schema mismatch")
    fields = {key: raw_intent[key] for key in _INTENT_FIELDS_V2}
    objects = fields["consumed_object_ids"]
    if type(objects) is not list:
        raise ValueError("custody authentication consumed objects must be an array")
    fields["consumed_object_ids"] = tuple(objects)
    intent = EconomicCommandIntentV2(**fields)
    occurrence = replay.context.occurrence
    if occurrence is None:
        raise ValueError("custody authentication occurrence is absent")
    require_economic_command_intent_occurrence_v2(intent, occurrence)
    body = canonical_economic_command_body_bytes_v2(replay.command.command_kind, replay.command)
    if value["command_body_bytes_digest"] != raw_root_v2(body):
        raise ValueError("custody authentication body digest mismatch")
    for name in _MESSAGE_FIELDS_V2:
        if name.endswith(("_root", "_id")) and name != "signer_key_id":
            _require_root_v2(value[name], name=f"custody authentication {name}")
    for name in ("signature_algorithm", "signer_key_id", "signer_public_key"):
        _require_token_v2(value[name], name=f"custody authentication {name}")


def custody_request_id_v2(
    context_raw: bytes, command_raw: bytes, message: bytes, signature: bytes, receipt: bytes
) -> str:
    return hash_global_v2(
        "isolated-custody-request-v2",
        {
            "context": raw_root_v2(context_raw),
            "command": raw_root_v2(command_raw),
            "message": raw_root_v2(message),
            "signature": raw_root_v2(signature),
            "receipt": raw_root_v2(receipt),
        },
    )


def joint_margin_request_id_v2(*parts: bytes) -> str:
    return hash_global_v2(
        "isolated-joint-margin-request-v2", {"request_root": custody_request_id_v2(*parts)}
    )


@dataclass(frozen=True, slots=True)
class CustodyPublicationRecordV2:
    sequence: int
    source_publication_id: str
    authority_root: str
    frame: bytes
    statement: bytes
    authentication_message: bytes
    signature: bytes
    receipt: bytes

    def __post_init__(self) -> None:
        _require_nonnegative_int_v2(self.sequence, name="custody publication sequence")
        if self.sequence == 0:
            raise ValueError("ordinary custody publication sequence must be positive")
        _require_root_v2(self.source_publication_id, name="custody publication predecessor")
        _require_root_v2(self.authority_root, name="custody publication authority")
        for raw, limit in (
            (self.frame, MAX_JOINT_MARGIN_FRAME_BYTES_V2 if self.is_joint_margin
             else MAX_ASSET_LANE_CUSTODY_GLOBAL_FRAME_BYTES_V2),
            (self.statement, MAX_JOURNAL_BYTES_V1),
            (self.authentication_message, MAX_JOURNAL_BYTES_V1),
            (self.signature, MAX_COMMAND_SIGNATURE_BYTES_V1),
            (self.receipt, MAX_RECEIPT_BYTES_V1),
        ):
            if type(raw) is not bytes or not 1 <= len(raw) <= limit:
                raise ValueError("custody publication component exceeds its type or byte bound")

    def replay(self) -> CustodyPublicationReplayV2:
        if self.is_joint_margin:
            replay = replay_joint_margin_publication_v2(self.frame)
        else:
            replay = replay_custody_publication_frame_v2(self.frame)
        if replay.statement != self.statement:
            raise ValueError("custody publication statement differs from pure replay")
        _require_authentication_transcript_v2(self.authentication_message, replay)
        return replay

    @property
    def publication_id(self) -> str:
        domain = "isolated-joint-margin-publication-v2" if self.is_joint_margin else "isolated-custody-publication-v2"
        return hash_global_v2(
            domain,
            {
                "schema": domain,
                "abi": GLOBAL_SETTLEMENT_ABI_V2,
                "sequence": self.sequence,
                "source_publication_id": self.source_publication_id,
                "authority_root": self.authority_root,
                "frame": raw_root_v2(self.frame),
                "statement": raw_root_v2(self.statement),
                "authentication_message": raw_root_v2(self.authentication_message),
                "signature": raw_root_v2(self.signature),
                "receipt": raw_root_v2(self.receipt),
            },
        )

    @property
    def request_id(self) -> str:
        identify = joint_margin_request_id_v2 if self.is_joint_margin else custody_request_id_v2
        return identify(*self.request_parts)

    @property
    def is_joint_margin(self) -> bool:
        return type(self.frame) is bytes and self.frame.startswith(JOINT_MARGIN_FRAME_MAGIC_V2)

    @property
    def request_parts(self) -> tuple[bytes, bytes, bytes, bytes, bytes]:
        if self.is_joint_margin:
            replay = self.replay()
            return (
                canonical_global_bytes_v2(replay.context), canonical_global_bytes_v2(replay.command),
                self.authentication_message, self.signature, self.receipt,
            )
        _, context, _, command, _, _ = decode_asset_lane_custody_global_frame_v2(self.frame)
        return context, command, self.authentication_message, self.signature, self.receipt

    @property
    def byte_count(self) -> int:
        return sum(
            map(
                len,
                (
                    self.frame,
                    self.statement,
                    self.authentication_message,
                    self.signature,
                    self.receipt,
                ),
            )
        )


JOINT_MARGIN_GENESIS_MAGIC_V2 = b"ZDJG2\x00"
_MARGIN_BYTES_LIMIT = 1_048_576


def encode_joint_margin_genesis_v2(
    assets: AssetLaneCustodyStateV2, margin: PerpsMarginStateV2,
) -> bytes:
    components = (canonical_global_bytes_v2(assets), canonical_global_bytes_v2(margin))
    if any(not 1 <= len(raw) <= _MARGIN_BYTES_LIMIT for raw in components):
        raise ValueError("joint margin genesis component exceeds its byte bound")
    return JOINT_MARGIN_GENESIS_MAGIC_V2 + b"".join(
        len(raw).to_bytes(4, "little") + raw for raw in components
    )


def decode_joint_margin_genesis_v2(raw: bytes) -> tuple[AssetLaneCustodyStateV2, PerpsMarginStateV2]:
    cursor = len(JOINT_MARGIN_GENESIS_MAGIC_V2)
    if type(raw) is not bytes or len(raw) > cursor + 2 * (_MARGIN_BYTES_LIMIT + 4):
        raise ValueError("joint margin genesis exceeds its type or byte bound")
    if not raw.startswith(JOINT_MARGIN_GENESIS_MAGIC_V2):
        raise ValueError("joint margin genesis discriminator mismatch")
    components = []
    for _ in range(2):
        if cursor + 4 > len(raw):
            raise ValueError("joint margin genesis length is truncated")
        size = int.from_bytes(raw[cursor:cursor + 4], "little")
        cursor += 4
        if not 1 <= size <= _MARGIN_BYTES_LIMIT or cursor + size > len(raw):
            raise ValueError("joint margin genesis component is invalid")
        components.append(raw[cursor:cursor + size])
        cursor += size
    if cursor != len(raw):
        raise ValueError("joint margin genesis has trailing bytes")
    assets = decode_asset_lane_custody_state_v2(components[0])
    margin = decode_perps_margin_state_v2(components[1])
    if encode_joint_margin_genesis_v2(assets, margin) != raw:
        raise ValueError("joint margin genesis must be canonical")
    return assets, margin


def frame_joint_margin_publication_v2(frame: bytes, margin: PerpsMarginStateV2 | None) -> bytes:
    """Tag a margin frame, or retain the unchanged margin beside a custody frame."""
    if type(frame) is not bytes:
        raise TypeError("joint publication frame must be exact bytes")
    if margin is None:
        result = JOINT_MARGIN_FRAME_MAGIC_V2 + b"\x01" + frame
    else:
        raw = canonical_global_bytes_v2(margin)
        if not 1 <= len(raw) <= _MARGIN_BYTES_LIMIT:
            raise ValueError("joint publication margin exceeds its byte bound")
        result = JOINT_MARGIN_FRAME_MAGIC_V2 + b"\x00" + len(raw).to_bytes(4, "little") + raw + frame
    if len(result) > MAX_JOINT_MARGIN_FRAME_BYTES_V2:
        raise ValueError("joint publication frame exceeds its byte bound")
    return result


def replay_joint_margin_publication_v2(raw: bytes) -> CustodyPublicationReplayV2:
    if type(raw) is not bytes or len(raw) > MAX_JOINT_MARGIN_FRAME_BYTES_V2:
        raise ValueError("joint publication frame exceeds its type or byte bound")
    cursor = len(JOINT_MARGIN_FRAME_MAGIC_V2)
    if not raw.startswith(JOINT_MARGIN_FRAME_MAGIC_V2) or len(raw) <= cursor:
        raise ValueError("joint publication frame discriminator is absent")
    tag, cursor = raw[cursor], cursor + 1
    if tag == 1:
        margin_replay = replay_perps_margin_frame_v2(raw[cursor:])
        if margin_replay.request.oracle is not None:
            raise ValueError("joint publication cannot authenticate oracle candidate data")
        return CustodyPublicationReplayV2(
            margin_replay.request, margin_replay.request.command,
            margin_replay.global_pre, margin_replay.assets_pre,
            margin_replay.result.post_state, margin_replay.result.post_assets, margin_replay.statement,
            margin_replay.margin_pre, margin_replay.result.post_margin,
        )
    if tag != 0 or cursor + 4 > len(raw):
        raise ValueError("joint publication route or margin length is invalid")
    size = int.from_bytes(raw[cursor:cursor + 4], "little")
    cursor += 4
    if not 1 <= size <= _MARGIN_BYTES_LIMIT or cursor + size >= len(raw):
        raise ValueError("joint publication margin component is invalid")
    margin = decode_perps_margin_state_v2(raw[cursor:cursor + size])
    replay = replay_custody_publication_frame_v2(raw[cursor + size:])
    require_margin_claim_projection_v2(margin, replay.global_pre)
    require_margin_claim_projection_v2(margin, replay.global_post)
    return CustodyPublicationReplayV2(
        replay.context, replay.command, replay.global_pre, replay.lane_pre,
        replay.global_post, replay.lane_post, replay.statement, margin, margin,
    )
