"""Independent G02 proof-context codec checker and vector builder."""

from __future__ import annotations

import json
from pathlib import Path

from experiments.fcis_m6_g01_proof_context_check import build_context
from src.core.fcis_m6_g02_proof_context_codec import (
    FCIS_M6_G02_PROOF_CONTEXT_CODEC_SCHEMA_V1,
    G02ProofContextCodeV1,
    G02ProofContextRejectV1,
    G02ProofContextSuccessV1,
    decode_g02_proof_context_v1,
    derive_g02_codec_root_v1,
    encode_g02_proof_context_v1,
)
from src.state.canonical import canonical_json_bytes

ROOT = Path(__file__).resolve().parents[1]
VECTOR_PATH = ROOT / "docs/research/m6_tasks/TASK_G02_PROOF_CONTEXT_V1.json"
_MAGIC = b"FCIS-M6-G02\x01"


def _field_end(payload: bytes, offset: int) -> int:
    name_size = int.from_bytes(payload[offset : offset + 4], "big")
    name_end = offset + 4 + name_size
    value_size_offset = name_end + 1
    value_size = int.from_bytes(payload[value_size_offset : value_size_offset + 4], "big")
    return value_size_offset + 4 + value_size


def _swap_first_two_fields(payload: bytes) -> bytes:
    start = len(_MAGIC) + 2
    first_end = _field_end(payload, start)
    second_end = _field_end(payload, first_end)
    return (
        payload[:start]
        + payload[first_end:second_end]
        + payload[start:first_end]
        + payload[second_end:]
    )


def _require_reject(value: object, code: G02ProofContextCodeV1, message: str) -> None:
    if type(value) is not G02ProofContextRejectV1:
        raise AssertionError(message)
    if value.code is not code:
        raise AssertionError(f"{message}: got {value.code.value}")


def run_checks(*, check_vector: bool = True) -> dict[str, object]:
    context = build_context()
    encoded = encode_g02_proof_context_v1(context)
    decoded = decode_g02_proof_context_v1(encoded)
    if type(decoded) is not G02ProofContextSuccessV1:
        raise AssertionError("G02 rejected its canonical context bytes")
    if decoded.context != context or decoded.canonical_bytes != encoded:
        raise AssertionError("G02 canonical round trip changed the context")
    if decoded.codec_root != derive_g02_codec_root_v1(encoded):
        raise AssertionError("G02 codec root is not stable")

    wrong_version = bytearray(encoded)
    wrong_version[len(_MAGIC) - 1] = 2
    _require_reject(
        decode_g02_proof_context_v1(bytes(wrong_version)),
        G02ProofContextCodeV1.WRONG_VERSION,
        "G02 accepted a foreign codec version",
    )
    unknown = encoded.replace(b"chain_id", b"foreign!", 1)
    _require_reject(
        decode_g02_proof_context_v1(unknown),
        G02ProofContextCodeV1.UNKNOWN_FIELD,
        "G02 accepted an unknown field",
    )
    reordered = _swap_first_two_fields(encoded)
    _require_reject(
        decode_g02_proof_context_v1(reordered),
        G02ProofContextCodeV1.NONCANONICAL_ORDER,
        "G02 accepted reordered fields",
    )
    wrong_type = bytearray(encoded)
    first_start = len(_MAGIC) + 2
    name_size = int.from_bytes(wrong_type[first_start : first_start + 4], "big")
    wrong_type[first_start + 4 + name_size] = ord("R")
    _require_reject(
        decode_g02_proof_context_v1(bytes(wrong_type)),
        G02ProofContextCodeV1.WRONG_FIELD_TYPE,
        "G02 accepted a wrong field tag",
    )
    _require_reject(
        decode_g02_proof_context_v1(encoded + b"\x00"),
        G02ProofContextCodeV1.INVALID_FRAME,
        "G02 accepted trailing bytes",
    )
    foreign_root = encoded.replace(context.context_root.encode("ascii"), b"0x" + b"f" * 64, 1)
    _require_reject(
        decode_g02_proof_context_v1(foreign_root),
        G02ProofContextCodeV1.CONTEXT_REJECTED,
        "G02 accepted a crossed G01 context root",
    )
    if check_vector:
        expected = json.loads(VECTOR_PATH.read_text(encoding="utf-8"))
        if canonical_json_bytes(build_payload()) != canonical_json_bytes(expected):
            raise SystemExit("FAIL: G02 proof-context vector is stale")
    return build_payload()


def build_payload() -> dict[str, object]:
    context = build_context()
    encoded = encode_g02_proof_context_v1(context)
    return {
        "schema": FCIS_M6_G02_PROOF_CONTEXT_CODEC_SCHEMA_V1,
        "context_root": context.context_root,
        "codec_root": derive_g02_codec_root_v1(encoded),
        "canonical_bytes_hex": encoded.hex(),
        "field_count": 15,
        "mutants_rejected": [
            "foreign codec version",
            "unknown field",
            "reordered fields",
            "wrong field tag",
            "trailing frame bytes",
            "crossed G01 context root",
        ],
        "all_rejections_typed": True,
    }


def build_rust_input() -> str:
    """Return the tab-separated field vector consumed by the Rust parity tool."""

    context = build_context()
    fields: tuple[object, ...] = (
        context.chain_id,
        context.deployment_id,
        context.state_root,
        context.configuration_root,
        context.protocol_version,
        context.language_runtime_version,
        context.verifier_implementation_id,
        context.verification_key_digest,
        context.statement_schema_id,
        context.algorithm_profile_id,
        context.history_genesis_authority_root,
        context.authority_epoch,
        context.not_before_epoch,
        context.expires_at_epoch,
        context.context_root,
    )
    return "\t".join("none" if value is None else str(value) for value in fields) + "\n"


def main() -> None:
    result = run_checks()
    print("G02_PROOF_CONTEXT_CHECKS_PASS", result["codec_root"])


if __name__ == "__main__":
    main()
