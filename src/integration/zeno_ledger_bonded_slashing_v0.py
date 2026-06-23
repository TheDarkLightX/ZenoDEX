"""Bonded slashing policy receipts for ZenoLedger equivocation evidence."""

from __future__ import annotations

from typing import Any, Mapping, Sequence

from src.integration.zeno_ledger_anti_equivocation_v0 import (
    build_checkpoint_equivocation_slashing_evidence_v0,
    build_watcher_attestation_equivocation_slashing_evidence_v0,
    validate_slashing_evidence_v0,
)
from src.integration.zeno_ledger_v0 import hash_v0
from src.state.canonical import canonical_hex_fixed_allow_0x


BOND_REGISTRY_SCHEMA_V0 = "zenodex/zeno_ledger/bond_registry/v0"
SLASHING_POLICY_SCHEMA_V0 = "zenodex/zeno_ledger/bonded_slashing_policy/v0"
BONDED_SLASHING_RECEIPT_SCHEMA_V0 = "zenodex/zeno_ledger/bonded_slashing_receipt/v0"
BPS_SCALE_V0 = 10_000

_SUPPORTED_EVIDENCE_KINDS_V0 = {
    "checkpoint_equivocation": "validator_set",
    "watcher_attestation_equivocation": "watcher_profile",
}
_SUPPORTED_BOND_STATUSES_V0 = {"active", "slashed", "revoked"}


def _require_mapping(value: object, *, name: str) -> Mapping[str, Any]:
    if not isinstance(value, Mapping):
        raise TypeError(f"{name} must be a JSON object")
    return value


def _require_sequence(value: object, *, name: str) -> Sequence[object]:
    if not isinstance(value, Sequence) or isinstance(value, (str, bytes, bytearray)):
        raise TypeError(f"{name} must be a sequence")
    return value


def _require_str(value: object, *, name: str, allow_empty: bool = False) -> str:
    if not isinstance(value, str) or (value == "" and not allow_empty):
        requirement = "a str" if allow_empty else "a non-empty str"
        raise ValueError(f"{name} must be {requirement}")
    return value


def _require_nonnegative_int(value: object, *, name: str) -> int:
    if not isinstance(value, int) or isinstance(value, bool) or value < 0:
        raise ValueError(f"{name} must be a non-negative int")
    return int(value)


def _require_positive_int(value: object, *, name: str) -> int:
    if not isinstance(value, int) or isinstance(value, bool) or value <= 0:
        raise ValueError(f"{name} must be a positive int")
    return int(value)


def _require_bps(value: object, *, name: str) -> int:
    out = _require_nonnegative_int(value, name=name)
    if out > BPS_SCALE_V0:
        raise ValueError(f"{name} exceeds bps scale")
    return out


def _require_root(value: object, *, name: str) -> str:
    if not isinstance(value, str):
        raise TypeError(f"{name} must be a str")
    canonical = canonical_hex_fixed_allow_0x(value, nbytes=32, name=name)
    if value != canonical:
        raise ValueError(f"{name} must be canonical lowercase 0x-prefixed hex")
    return canonical


def _require_roots(value: object, *, name: str) -> list[str]:
    roots = [
        _require_root(item, name=f"{name}[{index}]")
        for index, item in enumerate(_require_sequence(value, name=name))
    ]
    if roots != sorted(roots):
        raise ValueError(f"{name} must be sorted")
    if len(set(roots)) != len(roots):
        raise ValueError(f"{name} must not contain duplicates")
    return roots


def _expected_subject_kind(evidence_kind: str) -> str:
    subject_kind = _SUPPORTED_EVIDENCE_KINDS_V0.get(evidence_kind)
    if subject_kind is None:
        raise ValueError("slashing evidence kind is not supported by bonded policy")
    return subject_kind


def _bond_entry_body(
    *,
    subject_id: str,
    subject_kind: str,
    bonded_amount: int,
    slashed_amount: int,
    slashable_until_height: int,
    status: str,
    processed_evidence_hashes: Sequence[str],
) -> dict[str, Any]:
    checked_kind = _require_str(subject_kind, name="subject_kind")
    if checked_kind not in set(_SUPPORTED_EVIDENCE_KINDS_V0.values()):
        raise ValueError("bond subject_kind is not supported")
    checked_status = _require_str(status, name="status")
    if checked_status not in _SUPPORTED_BOND_STATUSES_V0:
        raise ValueError("bond status is not supported")
    bonded = _require_positive_int(bonded_amount, name="bonded_amount")
    slashed = _require_nonnegative_int(slashed_amount, name="slashed_amount")
    if slashed > bonded:
        raise ValueError("slashed amount exceeds bonded amount")
    body = {
        "subject_id": _require_str(subject_id, name="subject_id"),
        "subject_kind": checked_kind,
        "bonded_amount": bonded,
        "slashed_amount": slashed,
        "slashable_until_height": _require_nonnegative_int(
            slashable_until_height,
            name="slashable_until_height",
        ),
        "status": checked_status,
        "processed_evidence_hashes": _require_roots(
            processed_evidence_hashes,
            name="processed_evidence_hashes",
        ),
    }
    return {**body, "bond_entry_hash": hash_v0("zeno_ledger_bond_entry_v0", body)}


def _bond_registry_hash_v0(registry: Mapping[str, Any]) -> str:
    body = {key: value for key, value in dict(registry).items() if key != "bond_registry_hash"}
    return hash_v0("zeno_ledger_bond_registry_v0", body)


def build_bond_registry_v0(
    *,
    chain_id: str,
    asset_id: str,
    entries: Sequence[Mapping[str, Any]],
) -> dict[str, Any]:
    """Build a canonical registry of slashable ZenoLedger bonds."""

    items = _require_sequence(entries, name="entries")
    checked_entries: list[dict[str, Any]] = []
    seen_subjects: set[str] = set()
    for index, raw in enumerate(items):
        obj = _require_mapping(raw, name=f"entries[{index}]")
        entry = _bond_entry_body(
            subject_id=_require_str(obj.get("subject_id"), name=f"entries[{index}].subject_id"),
            subject_kind=_require_str(obj.get("subject_kind"), name=f"entries[{index}].subject_kind"),
            bonded_amount=_require_positive_int(obj.get("bonded_amount"), name=f"entries[{index}].bonded_amount"),
            slashed_amount=_require_nonnegative_int(
                obj.get("slashed_amount", 0),
                name=f"entries[{index}].slashed_amount",
            ),
            slashable_until_height=_require_nonnegative_int(
                obj.get("slashable_until_height"),
                name=f"entries[{index}].slashable_until_height",
            ),
            status=_require_str(obj.get("status", "active"), name=f"entries[{index}].status"),
            processed_evidence_hashes=[
                str(item)
                for item in _require_sequence(
                    obj.get("processed_evidence_hashes", []),
                    name=f"entries[{index}].processed_evidence_hashes",
                )
            ],
        )
        subject_id = str(entry["subject_id"])
        if subject_id in seen_subjects:
            raise ValueError("duplicate bond subject_id")
        seen_subjects.add(subject_id)
        checked_entries.append(entry)

    checked_entries.sort(key=lambda item: (str(item["subject_kind"]), str(item["subject_id"])))
    body = {
        "schema": BOND_REGISTRY_SCHEMA_V0,
        "chain_id": _require_str(chain_id, name="chain_id", allow_empty=True),
        "asset_id": _require_str(asset_id, name="asset_id"),
        "entries": checked_entries,
    }
    return {**body, "bond_registry_hash": _bond_registry_hash_v0(body)}


def validate_bond_registry_v0(registry: Mapping[str, Any]) -> None:
    obj = _require_mapping(registry, name="bond_registry")
    if obj.get("schema") != BOND_REGISTRY_SCHEMA_V0:
        raise ValueError("bond registry schema mismatch")
    expected = build_bond_registry_v0(
        chain_id=_require_str(obj.get("chain_id"), name="bond_registry.chain_id", allow_empty=True),
        asset_id=_require_str(obj.get("asset_id"), name="bond_registry.asset_id"),
        entries=[
            _require_mapping(item, name=f"bond_registry.entries[{index}]")
            for index, item in enumerate(_require_sequence(obj.get("entries"), name="bond_registry.entries"))
        ],
    )
    if dict(obj) != expected:
        raise ValueError("bond registry binding mismatch")


def _slashing_policy_hash_v0(policy: Mapping[str, Any]) -> str:
    body = {key: value for key, value in dict(policy).items() if key != "policy_hash"}
    return hash_v0("zeno_ledger_bonded_slashing_policy_v0", body)


def build_slashing_policy_v0(
    *,
    chain_id: str,
    policy_id: str,
    evidence_kind: str,
    slash_fraction_bps: int,
    min_slash_amount: int,
    max_slash_amount: int,
    burn_fraction_bps: int,
    status: str = "active",
) -> dict[str, Any]:
    """Build a deterministic bounded slashing policy."""

    checked_evidence_kind = _require_str(evidence_kind, name="evidence_kind")
    _expected_subject_kind(checked_evidence_kind)
    checked_status = _require_str(status, name="status")
    if checked_status not in {"active", "revoked"}:
        raise ValueError("slashing policy status is not supported")
    min_amount = _require_nonnegative_int(min_slash_amount, name="min_slash_amount")
    max_amount = _require_positive_int(max_slash_amount, name="max_slash_amount")
    if min_amount > max_amount:
        raise ValueError("min_slash_amount exceeds max_slash_amount")
    body = {
        "schema": SLASHING_POLICY_SCHEMA_V0,
        "chain_id": _require_str(chain_id, name="chain_id", allow_empty=True),
        "policy_id": _require_str(policy_id, name="policy_id"),
        "evidence_kind": checked_evidence_kind,
        "slash_fraction_bps": _require_bps(slash_fraction_bps, name="slash_fraction_bps"),
        "min_slash_amount": min_amount,
        "max_slash_amount": max_amount,
        "burn_fraction_bps": _require_bps(burn_fraction_bps, name="burn_fraction_bps"),
        "status": checked_status,
    }
    return {**body, "policy_hash": _slashing_policy_hash_v0(body)}


def validate_slashing_policy_v0(policy: Mapping[str, Any]) -> None:
    obj = _require_mapping(policy, name="slashing_policy")
    if obj.get("schema") != SLASHING_POLICY_SCHEMA_V0:
        raise ValueError("slashing policy schema mismatch")
    expected = build_slashing_policy_v0(
        chain_id=_require_str(obj.get("chain_id"), name="slashing_policy.chain_id", allow_empty=True),
        policy_id=_require_str(obj.get("policy_id"), name="slashing_policy.policy_id"),
        evidence_kind=_require_str(obj.get("evidence_kind"), name="slashing_policy.evidence_kind"),
        slash_fraction_bps=_require_bps(obj.get("slash_fraction_bps"), name="slashing_policy.slash_fraction_bps"),
        min_slash_amount=_require_nonnegative_int(
            obj.get("min_slash_amount"),
            name="slashing_policy.min_slash_amount",
        ),
        max_slash_amount=_require_positive_int(
            obj.get("max_slash_amount"),
            name="slashing_policy.max_slash_amount",
        ),
        burn_fraction_bps=_require_bps(obj.get("burn_fraction_bps"), name="slashing_policy.burn_fraction_bps"),
        status=_require_str(obj.get("status"), name="slashing_policy.status"),
    )
    if dict(obj) != expected:
        raise ValueError("slashing policy binding mismatch")


def _find_bond_entry(registry: Mapping[str, Any], *, subject_id: str, subject_kind: str) -> Mapping[str, Any]:
    for entry in registry["entries"]:
        obj = _require_mapping(entry, name="bond_registry.entry")
        if obj["subject_id"] == subject_id and obj["subject_kind"] == subject_kind:
            return obj
    raise ValueError("slashing subject is not bonded")




def _validate_equivocation_artifacts(*, evidence: Mapping[str, Any]) -> None:
    artifacts = _require_sequence(evidence.get("artifacts"), name="evidence.artifacts")
    if len(artifacts) != 2:
        raise ValueError("slashing evidence artifacts must contain two objects")
    artifact_a = _require_mapping(artifacts[0], name="evidence.artifacts[0]")
    artifact_b = _require_mapping(artifacts[1], name="evidence.artifacts[1]")

    kind = str(evidence["evidence_kind"])
    if kind == "checkpoint_equivocation":
        rebuilt = build_checkpoint_equivocation_slashing_evidence_v0(artifact_a, artifact_b)
    elif kind == "watcher_attestation_equivocation":
        rebuilt = build_watcher_attestation_equivocation_slashing_evidence_v0(artifact_a, artifact_b)
    else:
        raise ValueError("slashing evidence kind is not supported by bonded policy")

    if rebuilt != dict(evidence):
        raise ValueError("slashing evidence does not match canonical artifacts")

def _slash_amount(*, bonded_amount: int, policy: Mapping[str, Any]) -> int:
    proportional = (bonded_amount * int(policy["slash_fraction_bps"])) // BPS_SCALE_V0
    slash = max(proportional, int(policy["min_slash_amount"]))
    slash = min(slash, int(policy["max_slash_amount"]))
    if slash <= 0:
        raise ValueError("slashing policy computes zero slash amount")
    return slash


def apply_bonded_slashing_v0(
    *,
    evidence: Mapping[str, Any],
    bond_registry: Mapping[str, Any],
    policy: Mapping[str, Any],
) -> dict[str, Any]:
    """Apply one slashing receipt when evidence, policy, and bond state agree."""

    evidence_obj = dict(_require_mapping(evidence, name="evidence"))
    validate_slashing_evidence_v0(evidence_obj)
    _validate_equivocation_artifacts(evidence=evidence_obj)
    registry_obj = dict(_require_mapping(bond_registry, name="bond_registry"))
    validate_bond_registry_v0(registry_obj)
    policy_obj = dict(_require_mapping(policy, name="policy"))
    validate_slashing_policy_v0(policy_obj)

    if evidence_obj["chain_id"] != registry_obj["chain_id"]:
        raise ValueError("slashing evidence chain_id does not match bond registry")
    if evidence_obj["chain_id"] != policy_obj["chain_id"]:
        raise ValueError("slashing evidence chain_id does not match policy")
    if policy_obj["status"] != "active":
        raise ValueError("slashing policy is not active")
    if evidence_obj["evidence_kind"] != policy_obj["evidence_kind"]:
        raise ValueError("slashing evidence kind does not match policy")

    subject_id = _require_str(evidence_obj.get("subject_id"), name="evidence.subject_id")
    subject_kind = _expected_subject_kind(str(evidence_obj["evidence_kind"]))
    entry = _find_bond_entry(registry_obj, subject_id=subject_id, subject_kind=subject_kind)
    if entry["status"] != "active":
        raise ValueError("slashing subject bond is not active")
    evidence_height = _require_nonnegative_int(evidence_obj.get("height"), name="evidence.height")
    if evidence_height > int(entry["slashable_until_height"]):
        raise ValueError("slashing evidence height is outside bond slashability window")

    evidence_hash = _require_root(evidence_obj.get("evidence_hash"), name="evidence.evidence_hash")
    processed = list(entry["processed_evidence_hashes"])
    if evidence_hash in processed:
        raise ValueError("slashing evidence was already processed")

    bonded = int(entry["bonded_amount"])
    already_slashed = int(entry["slashed_amount"])
    available = bonded - already_slashed
    slash_amount = _slash_amount(bonded_amount=bonded, policy=policy_obj)
    if slash_amount > available:
        raise ValueError("slash amount exceeds available bond")
    burn_amount = (slash_amount * int(policy_obj["burn_fraction_bps"])) // BPS_SCALE_V0
    treasury_amount = slash_amount - burn_amount
    new_slashed = already_slashed + slash_amount
    remaining_bond = bonded - new_slashed

    updated_entries: list[Mapping[str, Any]] = []
    for raw_entry in registry_obj["entries"]:
        current = dict(_require_mapping(raw_entry, name="bond_registry.entry"))
        if current["subject_id"] == subject_id:
            current["slashed_amount"] = new_slashed
            current["status"] = "slashed" if remaining_bond == 0 else "active"
            current["processed_evidence_hashes"] = sorted([*processed, evidence_hash])
        updated_entries.append(current)
    updated_registry = build_bond_registry_v0(
        chain_id=str(registry_obj["chain_id"]),
        asset_id=str(registry_obj["asset_id"]),
        entries=updated_entries,
    )
    body = {
        "schema": BONDED_SLASHING_RECEIPT_SCHEMA_V0,
        "ok": True,
        "status": "accepted",
        "chain_id": evidence_obj["chain_id"],
        "asset_id": registry_obj["asset_id"],
        "evidence_kind": evidence_obj["evidence_kind"],
        "evidence_hash": evidence_hash,
        "policy_id": policy_obj["policy_id"],
        "policy_hash": policy_obj["policy_hash"],
        "bond_registry_hash_before": registry_obj["bond_registry_hash"],
        "bond_registry_hash_after": updated_registry["bond_registry_hash"],
        "subject_id": subject_id,
        "subject_kind": subject_kind,
        "evidence_height": evidence_height,
        "bonded_amount_before": bonded,
        "already_slashed_before": already_slashed,
        "slash_amount": slash_amount,
        "burn_amount": burn_amount,
        "treasury_amount": treasury_amount,
        "remaining_bond": remaining_bond,
        "updated_bond_entry_hash": _find_bond_entry(
            updated_registry,
            subject_id=subject_id,
            subject_kind=subject_kind,
        )["bond_entry_hash"],
    }
    receipt = {**body, "receipt_hash": hash_v0("zeno_ledger_bonded_slashing_receipt_v0", body)}
    return {"receipt": receipt, "bond_registry": updated_registry}


def validate_bonded_slashing_receipt_v0(
    *,
    receipt: Mapping[str, Any],
    updated_bond_registry: Mapping[str, Any],
    evidence: Mapping[str, Any],
    bond_registry_before: Mapping[str, Any],
    policy: Mapping[str, Any],
) -> None:
    obj = _require_mapping(receipt, name="receipt")
    if obj.get("schema") != BONDED_SLASHING_RECEIPT_SCHEMA_V0:
        raise ValueError("bonded slashing receipt schema mismatch")
    expected = apply_bonded_slashing_v0(
        evidence=evidence,
        bond_registry=bond_registry_before,
        policy=policy,
    )
    if dict(obj) != expected["receipt"]:
        raise ValueError("bonded slashing receipt binding mismatch")
    if dict(_require_mapping(updated_bond_registry, name="updated_bond_registry")) != expected["bond_registry"]:
        raise ValueError("updated bond registry binding mismatch")
