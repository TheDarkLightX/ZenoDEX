"""Fail-closed loaders for the WS2 client trust roots.

Two inputs feed `decide_admission`, and BOTH are client-shipped (never host data):

1. The consensus-semantics contract (config/semantics/zenodex_consensus_contract_v1.json)
   -> `ConsensusContract`. Provides the claim-level total order, the required level
   per operation, the deployed-admission binding status, and the INDEPENDENT
   proof_type -> level mapping that makes gate 10 non-tautological.

2. A client pinset JSON -> `PinnedRegistry`. Pins the verifier identity (absolute
   binary + sha256), the RISC0 image id, proof_type/chain_id, the closed
   required-journal-field set, and the admission allow-list.

Loader philosophy: parse STRICTLY and raise `ClientPinsetError` on anything
malformed — a client must refuse to START with a broken trust root rather than
run permissive (the WS5-A browser-pinset lesson: malformed pinsets must never
silently fall back to unpinned mode).

The repo ships a LOCAL-DEV pinset format only. How production pins are
distributed (signed releases, WS5 upgrade gating) is explicitly out of scope
here and documented as a residual in docs/WS2_TRUSTLESS_REFUSE_BY_DEFAULT.md.
"""

from __future__ import annotations

import json
import re
from pathlib import Path
from typing import Any, Mapping

from src.integration.client_admission_decision import (
    ConsensusContract,
    OperationPins,
    PinnedRegistry,
    VerifierIdentity,
)

_REPO_ROOT = Path(__file__).resolve().parents[2]
DEFAULT_CONTRACT_PATH = _REPO_ROOT / "config" / "semantics" / "zenodex_consensus_contract_v1.json"

_PINSET_SCHEMA = "zenodex/client-pinset/v1"
_HEX64_RE = re.compile(r"\A[0-9a-f]{64}\Z")
_U32_MAX = (1 << 32) - 1

_PIN_ROW_KEYS = frozenset(
    {
        "surface",
        "operation",
        "proof_type",
        "chain_id",
        "risc0_image_id_words",
        "blessed_verifier",
        "required_journal_fields",
        "expected_static",
        "recomputed_fields",
        "cross_field_equal",
        "head_equal_fields",
        "claim_level",
        "ceiling_level",
        "admission_threshold_level",
        "admission_proof_gated_statuses",
    }
)


class ClientPinsetError(ValueError):
    """A client trust root failed to load. The client must not start permissive."""


def _require(condition: bool, message: str) -> None:
    if not condition:
        raise ClientPinsetError(message)


def _str_field(obj: Mapping[str, Any], key: str, *, where: str) -> str:
    value = obj.get(key)
    _require(type(value) is str and bool(value), f"{where}.{key} must be a non-empty string")
    return value  # type: ignore[return-value]


def load_consensus_contract(path: Path | str = DEFAULT_CONTRACT_PATH) -> ConsensusContract:
    """Typed, fail-closed view over the consensus-semantics contract JSON."""
    raw = json.loads(Path(path).read_text())
    _require(isinstance(raw, dict), "contract must be a JSON object")

    levels = raw.get("claim_levels")
    _require(
        isinstance(levels, dict) and len(levels) >= 2,
        "contract.claim_levels must be an object with >= 2 levels",
    )
    # JSON object order IS the contract's weakest..strongest order (the file is
    # authored that way and the BDD linter gates the file's content).
    order = tuple(levels.keys())
    _require(all(type(k) is str and k for k in order), "claim level names must be strings")
    _require(len(set(order)) == len(order), "claim levels must be unique")

    operations = raw.get("operations")
    _require(isinstance(operations, dict), "contract.operations must be an object")

    required_level_by_op: dict[tuple[str, str], str] = {}
    admission_status_by_op: dict[tuple[str, str], str | None] = {}
    level_by_proof_type: dict[str, str] = {}
    for op_key, op in operations.items():
        _require(
            type(op_key) is str and op_key.count(".") == 1,
            f"operation key {op_key!r} must be 'surface.operation'",
        )
        surface, operation = op_key.split(".", 1)
        _require(isinstance(op, dict), f"operations[{op_key!r}] must be an object")
        guest = op.get("guest")
        _require(isinstance(guest, dict), f"operations[{op_key!r}].guest must be an object")
        claim = guest.get("live_equivalence_claim_level")
        _require(
            type(claim) is str and claim in order,
            f"operations[{op_key!r}].guest.live_equivalence_claim_level must be a known level",
        )
        required_level_by_op[(surface, operation)] = claim

        envelope = op.get("envelope")
        status = envelope.get("live_binding_status") if isinstance(envelope, dict) else None
        _require(
            status is None or (type(status) is str and bool(status)),
            f"operations[{op_key!r}].envelope.live_binding_status must be a string when present",
        )
        admission_status_by_op[(surface, operation)] = status

        proof_type = guest.get("proof_type")
        if proof_type is not None:
            _require(
                type(proof_type) is str and bool(proof_type),
                f"operations[{op_key!r}].guest.proof_type must be a non-empty string",
            )
            existing = level_by_proof_type.get(proof_type)
            _require(
                existing is None or existing == claim,
                f"proof_type {proof_type!r} maps to conflicting claim levels",
            )
            level_by_proof_type[proof_type] = claim

    return ConsensusContract(
        claim_levels_order=order,
        required_level_by_op=required_level_by_op,
        admission_binding_status_by_op=admission_status_by_op,
        level_by_proof_type=level_by_proof_type,
    )


def _parse_image_words(value: Any, *, where: str) -> tuple[int, ...]:
    _require(isinstance(value, list) and len(value) == 8, f"{where} must be 8 u32 words")
    words: list[int] = []
    for item in value:
        _require(type(item) is int and 0 <= item <= _U32_MAX, f"{where} words must be u32")
        words.append(item)
    return tuple(words)


def _parse_str_tuple(value: Any, *, where: str, allow_empty: bool) -> tuple[str, ...]:
    _require(isinstance(value, list), f"{where} must be a list")
    if not allow_empty:
        _require(len(value) > 0, f"{where} must be non-empty")
    out: list[str] = []
    for item in value:
        _require(type(item) is str and bool(item), f"{where} entries must be non-empty strings")
        out.append(item)
    _require(len(set(out)) == len(out), f"{where} entries must be unique")
    return tuple(out)


def _parse_expected_static(value: Any, *, where: str) -> dict[str, bytes]:
    _require(isinstance(value, dict), f"{where} must be an object")
    out: dict[str, bytes] = {}
    for key, hexval in value.items():
        _require(type(key) is str and bool(key), f"{where} keys must be strings")
        _require(
            type(hexval) is str and bool(_HEX64_RE.match(hexval)),
            f"{where}[{key!r}] must be 64 lowercase hex chars",
        )
        out[key] = bytes.fromhex(hexval)
    return out


def _parse_cross_field_equal(value: Any, *, where: str) -> tuple[tuple[str, str], ...]:
    _require(isinstance(value, list), f"{where} must be a list")
    out: list[tuple[str, str]] = []
    for item in value:
        _require(
            isinstance(item, list) and len(item) == 2 and all(type(x) is str and x for x in item),
            f"{where} entries must be [field, other_field] string pairs",
        )
        out.append((item[0], item[1]))
    return tuple(out)


def load_pinned_registry(path: Path | str) -> PinnedRegistry:
    """Parse a client pinset JSON into the registry `decide_admission` trusts."""
    raw = json.loads(Path(path).read_text())
    _require(isinstance(raw, dict), "pinset must be a JSON object")
    _require(raw.get("schema") == _PINSET_SCHEMA, f"pinset schema must be {_PINSET_SCHEMA}")
    pins_raw = raw.get("pins")
    _require(isinstance(pins_raw, list) and len(pins_raw) > 0, "pinset.pins must be non-empty")

    by_op: dict[tuple[str, str], OperationPins] = {}
    for index, row in enumerate(pins_raw):
        where = f"pins[{index}]"
        _require(isinstance(row, dict), f"{where} must be an object")
        _require(set(row.keys()) == _PIN_ROW_KEYS, f"{where} must have exactly the pin keys")

        surface = _str_field(row, "surface", where=where)
        operation = _str_field(row, "operation", where=where)
        blessed_raw = row.get("blessed_verifier")
        _require(isinstance(blessed_raw, dict), f"{where}.blessed_verifier must be an object")
        _require(
            set(blessed_raw.keys()) == {"binary_path", "sha256"},
            f"{where}.blessed_verifier must have exactly binary_path + sha256",
        )
        binary_path = _str_field(blessed_raw, "binary_path", where=f"{where}.blessed_verifier")
        _require(
            binary_path.startswith("/"),
            f"{where}.blessed_verifier.binary_path must be absolute",
        )
        sha256 = _str_field(blessed_raw, "sha256", where=f"{where}.blessed_verifier")
        _require(
            bool(_HEX64_RE.match(sha256)),
            f"{where}.blessed_verifier.sha256 must be 64 lowercase hex chars",
        )

        key = (surface, operation)
        _require(key not in by_op, f"{where} duplicates pin for {key!r}")
        by_op[key] = OperationPins(
            surface=surface,
            operation=operation,
            pinned_image_id=_parse_image_words(
                row.get("risc0_image_id_words"), where=f"{where}.risc0_image_id_words"
            ),
            pinned_proof_type=_str_field(row, "proof_type", where=where),
            pinned_chain_id=_str_field(row, "chain_id", where=where),
            blessed_verifier=VerifierIdentity(
                expected_cmd_hash=sha256,
                binary_path=binary_path,
                allow_path_lookup=False,
            ),
            required_journal_fields=_parse_str_tuple(
                row.get("required_journal_fields"),
                where=f"{where}.required_journal_fields",
                allow_empty=False,
            ),
            expected_static=_parse_expected_static(
                row.get("expected_static"), where=f"{where}.expected_static"
            ),
            recomputed_fields=_parse_str_tuple(
                row.get("recomputed_fields"),
                where=f"{where}.recomputed_fields",
                allow_empty=True,
            ),
            cross_field_equal=_parse_cross_field_equal(
                row.get("cross_field_equal"), where=f"{where}.cross_field_equal"
            ),
            head_equal_fields=_parse_str_tuple(
                row.get("head_equal_fields"),
                where=f"{where}.head_equal_fields",
                allow_empty=True,
            ),
            claim_level=_str_field(row, "claim_level", where=where),
            ceiling_level=_str_field(row, "ceiling_level", where=where),
            admission_threshold_level=_str_field(row, "admission_threshold_level", where=where),
            admission_proof_gated_statuses=_parse_str_tuple(
                row.get("admission_proof_gated_statuses"),
                where=f"{where}.admission_proof_gated_statuses",
                allow_empty=True,
            ),
        )
    return PinnedRegistry(by_op=by_op)
