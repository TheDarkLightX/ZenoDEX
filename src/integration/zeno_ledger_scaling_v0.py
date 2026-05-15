"""Scaling receipts for ZenoLedger proof-carrying execution.

The objects in this module do not prove a transition by themselves. They define
the canonical public journal and receipt bindings that replay, zkVM, TEE, and
future recursive proof backends must agree on.
"""

from __future__ import annotations

import re
from typing import Any, Mapping

from src.integration.zeno_ledger_v0 import (
    ROOT_NBYTES,
    canonical_header_hash_v0,
    hash_v0,
    validate_header_v0,
)
from src.state.canonical import canonical_hex_fixed_allow_0x


EXECUTION_JOURNAL_SCHEMA_V0 = "zenodex/zeno_ledger/execution_journal/v0"
TRANSITION_RECEIPT_SCHEMA_V0 = "zenodex/zeno_ledger/transition_receipt/v0"
ZERO_ROOT_V0 = "0x" + "00" * ROOT_NBYTES

VERIFIER_KINDS_V0 = frozenset(
    {
        "deterministic_replay_v0",
        "risc0_zkvm_v0",
        "sp1_zkvm_v0",
        "tee_attestation_v0",
        "recursive_epoch_v0",
    }
)

_ID_RE = re.compile(r"^[A-Za-z0-9_.:/-]+$")


def _require_mapping(value: object, *, name: str) -> Mapping[str, Any]:
    if not isinstance(value, Mapping):
        raise TypeError(f"{name} must be a JSON object")
    return value


def _require_str(value: object, *, name: str) -> str:
    if not isinstance(value, str) or value == "":
        raise ValueError(f"{name} must be a non-empty str")
    return value


def _require_id(value: object, *, name: str) -> str:
    text = _require_str(value, name=name)
    if not _ID_RE.fullmatch(text):
        raise ValueError(f"{name} contains unsupported characters")
    return text


def _require_nonnegative_int(value: object, *, name: str) -> int:
    if not isinstance(value, int) or isinstance(value, bool) or value < 0:
        raise ValueError(f"{name} must be a non-negative int")
    return value


def _require_root(value: object, *, name: str) -> str:
    if not isinstance(value, str):
        raise TypeError(f"{name} must be a str")
    canonical = canonical_hex_fixed_allow_0x(value, nbytes=ROOT_NBYTES, name=name)
    if value != canonical:
        raise ValueError(f"{name} must be canonical lowercase 0x-prefixed hex")
    return canonical


def build_execution_journal_v0(
    *,
    chain_id: str,
    height: int,
    program_id: str,
    proof_policy_id: str,
    pre_state_root: str,
    ordered_body_root: str,
    post_state_root: str,
    app_hash: str,
    data_availability_root: str,
    feature_suite_hash: str,
    token_registry_hash: str,
    rejection_receipt_root: str = ZERO_ROOT_V0,
) -> dict[str, Any]:
    journal = {
        "schema": EXECUTION_JOURNAL_SCHEMA_V0,
        "chain_id": chain_id,
        "height": height,
        "program_id": program_id,
        "proof_policy_id": proof_policy_id,
        "pre_state_root": pre_state_root,
        "ordered_body_root": ordered_body_root,
        "post_state_root": post_state_root,
        "app_hash": app_hash,
        "data_availability_root": data_availability_root,
        "feature_suite_hash": feature_suite_hash,
        "token_registry_hash": token_registry_hash,
        "rejection_receipt_root": rejection_receipt_root,
    }
    validate_execution_journal_v0(journal)
    return journal


def validate_execution_journal_v0(journal: Mapping[str, Any]) -> None:
    obj = _require_mapping(journal, name="execution_journal")
    expected = {
        "schema",
        "chain_id",
        "height",
        "program_id",
        "proof_policy_id",
        "pre_state_root",
        "ordered_body_root",
        "post_state_root",
        "app_hash",
        "data_availability_root",
        "feature_suite_hash",
        "token_registry_hash",
        "rejection_receipt_root",
    }
    if set(obj.keys()) != expected:
        raise ValueError("execution_journal keys mismatch")
    if obj.get("schema") != EXECUTION_JOURNAL_SCHEMA_V0:
        raise ValueError("execution_journal schema mismatch")
    _require_str(obj.get("chain_id"), name="execution_journal.chain_id")
    _require_nonnegative_int(obj.get("height"), name="execution_journal.height")
    _require_id(obj.get("program_id"), name="execution_journal.program_id")
    _require_id(obj.get("proof_policy_id"), name="execution_journal.proof_policy_id")
    for key in (
        "pre_state_root",
        "ordered_body_root",
        "post_state_root",
        "app_hash",
        "data_availability_root",
        "feature_suite_hash",
        "token_registry_hash",
        "rejection_receipt_root",
    ):
        _require_root(obj.get(key), name=f"execution_journal.{key}")


def execution_journal_hash_v0(journal: Mapping[str, Any]) -> str:
    validate_execution_journal_v0(journal)
    return hash_v0("execution_journal_v0", dict(journal))


def build_execution_journal_from_header_v0(
    *,
    header: Mapping[str, Any],
    program_id: str,
    proof_policy_id: str,
    feature_suite_hash: str,
    token_registry_hash: str,
    rejection_receipt_root: str = ZERO_ROOT_V0,
) -> dict[str, Any]:
    validate_header_v0(dict(header))
    return build_execution_journal_v0(
        chain_id=str(header["chain_id"]),
        height=int(header["height"]),
        program_id=program_id,
        proof_policy_id=proof_policy_id,
        pre_state_root=str(header["pre_state_root"]),
        ordered_body_root=str(header["body_root"]),
        post_state_root=str(header["post_state_root"]),
        app_hash=str(header["app_hash"]),
        data_availability_root=str(header["data_availability_root"]),
        feature_suite_hash=feature_suite_hash,
        token_registry_hash=token_registry_hash,
        rejection_receipt_root=rejection_receipt_root,
    )


def build_transition_receipt_v0(
    *,
    execution_journal: Mapping[str, Any],
    verifier_kind: str,
    verifier_version: str,
    proof_commitment: str,
    receipt_metadata_hash: str = ZERO_ROOT_V0,
) -> dict[str, Any]:
    validate_execution_journal_v0(execution_journal)
    kind = _require_id(verifier_kind, name="transition_receipt.verifier_kind")
    if kind not in VERIFIER_KINDS_V0:
        raise ValueError("transition_receipt verifier_kind is not allowed")
    body = {
        "schema": TRANSITION_RECEIPT_SCHEMA_V0,
        "chain_id": execution_journal["chain_id"],
        "height": execution_journal["height"],
        "verifier_kind": kind,
        "verifier_version": _require_id(
            verifier_version,
            name="transition_receipt.verifier_version",
        ),
        "execution_journal": dict(execution_journal),
        "execution_journal_hash": execution_journal_hash_v0(execution_journal),
        "proof_commitment": proof_commitment,
        "data_availability_root": execution_journal["data_availability_root"],
        "receipt_metadata_hash": receipt_metadata_hash,
    }
    validate_transition_receipt_body_v0(body)
    receipt = {**body, "receipt_hash": hash_v0("transition_receipt_v0", body)}
    validate_transition_receipt_v0(receipt)
    return receipt


def validate_transition_receipt_body_v0(receipt_body: Mapping[str, Any]) -> None:
    obj = _require_mapping(receipt_body, name="transition_receipt_body")
    expected = {
        "schema",
        "chain_id",
        "height",
        "verifier_kind",
        "verifier_version",
        "execution_journal",
        "execution_journal_hash",
        "proof_commitment",
        "data_availability_root",
        "receipt_metadata_hash",
    }
    if set(obj.keys()) != expected:
        raise ValueError("transition_receipt body keys mismatch")
    if obj.get("schema") != TRANSITION_RECEIPT_SCHEMA_V0:
        raise ValueError("transition_receipt schema mismatch")
    chain_id = _require_str(obj.get("chain_id"), name="transition_receipt.chain_id")
    height = _require_nonnegative_int(obj.get("height"), name="transition_receipt.height")
    kind = _require_id(obj.get("verifier_kind"), name="transition_receipt.verifier_kind")
    if kind not in VERIFIER_KINDS_V0:
        raise ValueError("transition_receipt verifier_kind is not allowed")
    _require_id(obj.get("verifier_version"), name="transition_receipt.verifier_version")
    journal = _require_mapping(obj.get("execution_journal"), name="transition_receipt.execution_journal")
    validate_execution_journal_v0(journal)
    if journal["chain_id"] != chain_id:
        raise ValueError("transition_receipt chain_id does not match journal")
    if journal["height"] != height:
        raise ValueError("transition_receipt height does not match journal")
    expected_journal_hash = execution_journal_hash_v0(journal)
    if _require_root(
        obj.get("execution_journal_hash"),
        name="transition_receipt.execution_journal_hash",
    ) != expected_journal_hash:
        raise ValueError("transition_receipt execution_journal_hash mismatch")
    _require_root(obj.get("proof_commitment"), name="transition_receipt.proof_commitment")
    if _require_root(
        obj.get("data_availability_root"),
        name="transition_receipt.data_availability_root",
    ) != journal["data_availability_root"]:
        raise ValueError("transition_receipt data_availability_root mismatch")
    _require_root(
        obj.get("receipt_metadata_hash"),
        name="transition_receipt.receipt_metadata_hash",
    )


def validate_transition_receipt_v0(receipt: Mapping[str, Any]) -> None:
    obj = _require_mapping(receipt, name="transition_receipt")
    expected = {
        "schema",
        "chain_id",
        "height",
        "verifier_kind",
        "verifier_version",
        "execution_journal",
        "execution_journal_hash",
        "proof_commitment",
        "data_availability_root",
        "receipt_metadata_hash",
        "receipt_hash",
    }
    if set(obj.keys()) != expected:
        raise ValueError("transition_receipt keys mismatch")
    body = {key: obj[key] for key in expected if key != "receipt_hash"}
    validate_transition_receipt_body_v0(body)
    if _require_root(obj.get("receipt_hash"), name="transition_receipt.receipt_hash") != hash_v0(
        "transition_receipt_v0",
        body,
    ):
        raise ValueError("transition_receipt receipt_hash mismatch")


def transition_receipt_hash_v0(receipt: Mapping[str, Any]) -> str:
    validate_transition_receipt_v0(receipt)
    return str(receipt["receipt_hash"])


def validate_header_transition_receipt_binding_v0(
    header: Mapping[str, Any],
    receipt: Mapping[str, Any],
) -> None:
    validate_header_v0(dict(header))
    validate_transition_receipt_v0(receipt)
    journal = _require_mapping(receipt["execution_journal"], name="transition_receipt.execution_journal")
    header_hash = canonical_header_hash_v0(dict(header))

    checks = {
        "chain_id": header["chain_id"],
        "height": header["height"],
        "pre_state_root": header["pre_state_root"],
        "ordered_body_root": header["body_root"],
        "post_state_root": header["post_state_root"],
        "app_hash": header["app_hash"],
        "data_availability_root": header["data_availability_root"],
    }
    for key, expected_value in checks.items():
        if journal[key] != expected_value:
            raise ValueError(f"transition_receipt/header binding mismatch: {key}")
    if header["proof_journal_hash"] != receipt["execution_journal_hash"]:
        raise ValueError("transition_receipt/header binding mismatch: proof_journal_hash")
    if header_hash == ZERO_ROOT_V0:
        raise ValueError("header hash must not be zero")

