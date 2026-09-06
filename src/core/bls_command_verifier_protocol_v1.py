"""Closed byte protocol for a measured G2 Basic command verifier.

This successor protocol does not reinterpret the historical in-process backend
root. Parsing a response conveys only a cryptographic verdict for one request;
policy admission, evidence qualification and publication are separate gates.
"""

from __future__ import annotations

import hashlib
from typing import Final

from .global_settlement_types_v1 import hash_global_v1

BLS_COMMAND_ALGORITHM_V1: Final = "BLS12_381_G2_BASIC_V1"
BLS_COMMAND_DST_V1: Final = "BLS_SIG_BLS12381G2_XMD:SHA-256_SSWU_RO_NUL_"
BLS_COMMAND_MAX_MESSAGE_BYTES_V1: Final = 1024 * 1024
BLS_COMMAND_REQUEST_MAGIC_V1: Final = b"ZDXBLSV1"
BLS_COMMAND_ACCEPT_MAGIC_V1: Final = b"ZDXBOKV1"
BLS_COMMAND_REJECT_MAGIC_V1: Final = b"ZDXBNOV1"


def bls_command_verifier_protocol_root_v1() -> str:
    return hash_global_v1("economic-command-bls-sealed-protocol-v1", {
        "algorithm": BLS_COMMAND_ALGORITHM_V1,
        "dst": BLS_COMMAND_DST_V1,
        "message_semantics": "RAW_NO_PREHASH_NO_AUGMENTATION",
        "request_magic_hex": BLS_COMMAND_REQUEST_MAGIC_V1.hex(),
        "request_fields": ("public_key:G1_compressed_48", "signature:G2_compressed_96",
                           "message_length:u32le", "message:exact_bytes"),
        "message_min_bytes": 1,
        "message_max_bytes": BLS_COMMAND_MAX_MESSAGE_BYTES_V1,
        "accept_magic_hex": BLS_COMMAND_ACCEPT_MAGIC_V1.hex(),
        "reject_magic_hex": BLS_COMMAND_REJECT_MAGIC_V1.hex(),
        "response_suffix": "SHA256_EXACT_REQUEST_32_BYTES",
        "response_contract": "EXACT_40_BYTES_ZERO_EXIT_EMPTY_STDERR",
        "group_validation": "CANONICAL_COMPRESSED_NONINFINITY_SUBGROUP_CHECKED",
    })


def encode_bls_command_request_v1(
    *, signature_algorithm: str, signer_public_key: str,
    message_bytes: bytes, signature_bytes: bytes,
) -> bytes:
    if type(signature_algorithm) is not str or signature_algorithm != BLS_COMMAND_ALGORITHM_V1:
        raise ValueError("BLS command algorithm mismatch")
    if (
        type(signer_public_key) is not str or len(signer_public_key) != 98
        or not signer_public_key.startswith("0x")
        or any(c not in "0123456789abcdef" for c in signer_public_key[2:])
    ):
        raise ValueError("BLS command public key encoding mismatch")
    if type(signature_bytes) is not bytes or len(signature_bytes) != 96:
        raise ValueError("BLS command signature encoding mismatch")
    if type(message_bytes) is not bytes or not 1 <= len(message_bytes) <= BLS_COMMAND_MAX_MESSAGE_BYTES_V1:
        raise ValueError("BLS command message bounds mismatch")
    return (BLS_COMMAND_REQUEST_MAGIC_V1 + bytes.fromhex(signer_public_key[2:])
            + signature_bytes + len(message_bytes).to_bytes(4, "little") + message_bytes)


def decode_bls_command_response_v1(request: bytes, response: bytes) -> bool:
    if type(request) is not bytes or type(response) is not bytes:
        raise ValueError("BLS command transcript must contain exact bytes")
    message_length = int.from_bytes(request[152:156], "little")
    if (request[:8] != BLS_COMMAND_REQUEST_MAGIC_V1
        or not 1 <= message_length <= BLS_COMMAND_MAX_MESSAGE_BYTES_V1
        or len(request) != 156 + message_length):
        raise ValueError("BLS command request framing mismatch")
    digest = hashlib.sha256(request).digest()
    if response == BLS_COMMAND_ACCEPT_MAGIC_V1 + digest:
        return True
    if response == BLS_COMMAND_REJECT_MAGIC_V1 + digest:
        return False
    raise ValueError("BLS command response binding mismatch")
