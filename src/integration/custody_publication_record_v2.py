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
    hash_global_v2,
)
from ..core.global_settlement_wire_codec_v2 import (
    _decode_global_state_object_v2,
    _load_canonical_object_v2,
)
from ..state.canonical import domain_sep_bytes
from .global_receipt_verifier_v1 import MAX_JOURNAL_BYTES_V1, MAX_RECEIPT_BYTES_V1


def raw_root_v2(raw: bytes) -> str:
    return "0x" + hashlib.sha256(raw).hexdigest()


def decode_custody_global_state_v2(raw: bytes) -> GlobalEconomicStateV2:
    return _decode_global_state_object_v2(_load_canonical_object_v2(raw))


@dataclass(frozen=True, slots=True)
class CustodyPublicationReplayV2:
    context: AssetLaneContextV2
    command: AssetLaneCommandV2
    global_pre: GlobalEconomicStateV2
    lane_pre: AssetLaneCustodyStateV2
    global_post: GlobalEconomicStateV2
    lane_post: AssetLaneCustodyStateV2
    statement: bytes


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
            (self.frame, MAX_ASSET_LANE_CUSTODY_GLOBAL_FRAME_BYTES_V2),
            (self.statement, MAX_JOURNAL_BYTES_V1),
            (self.authentication_message, MAX_JOURNAL_BYTES_V1),
            (self.signature, MAX_COMMAND_SIGNATURE_BYTES_V1),
            (self.receipt, MAX_RECEIPT_BYTES_V1),
        ):
            if type(raw) is not bytes or not 1 <= len(raw) <= limit:
                raise ValueError("custody publication component exceeds its type or byte bound")

    def replay(self) -> CustodyPublicationReplayV2:
        replay = replay_custody_publication_frame_v2(self.frame)
        if replay.statement != self.statement:
            raise ValueError("custody publication statement differs from pure replay")
        _require_authentication_transcript_v2(self.authentication_message, replay)
        return replay

    @property
    def publication_id(self) -> str:
        return hash_global_v2(
            "isolated-custody-publication-v2",
            {
                "schema": "isolated-custody-publication-v2",
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
        return custody_request_id_v2(*self.request_parts)

    @property
    def request_parts(self) -> tuple[bytes, bytes, bytes, bytes, bytes]:
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
