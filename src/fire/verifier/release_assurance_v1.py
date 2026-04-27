from __future__ import annotations

import json
from dataclasses import dataclass
from pathlib import Path
from typing import Mapping

import yaml

from src.fire.pathing_v1 import (
    fire_acceptance_receipt_schema_path,
    fire_formal_assurance_claims_path,
    fire_verifier_rules_path,
)
from src.fire.verifier.formal_assurance_claims_v1 import verify_fire_formal_assurance_claims_file
from src.fire.verifier.settlement_v1 import (
    FireSettlementPacket,
    FireVerifierReceipt,
    fire_witness_binding_hash,
    verify_fire_settlement_authority_packet,
    verify_fire_settlement_packet,
)


FIRE_RELEASE_ASSURANCE_CHECK_REPORT_SCHEMA = "zenodex/fire-release-assurance-check-report/v1"

REQUIRED_SETTLEMENT_RULE_REJECTS = frozenset(
    {
        "object_hash_mismatch",
        "instance_hash_mismatch",
        "cert_sha256_mismatch",
        "witness_hash_mismatch",
        "delta_hash_mismatch",
        "receipt_hash_mismatch",
    }
)

REQUIRED_NON_AUTHORITATIVE_SURFACES = frozenset(
    {
        "zpl_source",
        "fire_refiner",
        "object_card",
        "product_docs",
        "ui_rendering",
        "marketing_copy",
    }
)

MONEY_MOVING_SOURCE_RULES = {
    "src/fire/kernel/ledger_adapter_v1.py": {
        "required": (
            "verify_fire_settlement_authority_packet",
            "extract_verified_fire_settlement_authority_packet",
            "verify_fire_authority_apply_receipt",
        ),
        "forbidden": (
            "verify_fire_settlement_packet(",
            "extract_verified_fire_settlement_packet(",
            "verify_fire_apply_receipt(",
        ),
    },
    "src/fire/verifier/settlement_apply_report_v1.py": {
        "required": (
            "verify_fire_settlement_authority_packet",
            "verify_fire_authority_apply_receipt",
        ),
        "forbidden": (
            "verify_fire_settlement_packet(",
            "verify_fire_apply_receipt(",
        ),
    },
    "src/fire/runtime/adapter_manifest_gate_v1.py": {
        "required": ("verify_fire_settlement_authority_receipt",),
        "forbidden": ("verify_fire_verifier_receipt(",),
    },
    "src/fire/runtime/common_v1.py": {
        "required": (
            "verify_fire_settlement_authority_receipt",
            "witness_inputs_missing",
        ),
        "forbidden": ("verify_fire_verifier_receipt(",),
    },
}


class FireReleaseAssuranceError(RuntimeError):
    pass


@dataclass(frozen=True)
class FireReleaseAssuranceVerification:
    formal_claims_manifest: Path
    acceptance_receipt_schema: Path
    verifier_rules: Path
    formal_claims_manifest_sha256: str
    component_count: int
    settlement_authority_components: tuple[str, ...]

    def to_report_dict(self) -> dict[str, object]:
        return {
            "schema": FIRE_RELEASE_ASSURANCE_CHECK_REPORT_SCHEMA,
            "ok": True,
            "formal_claims_manifest": str(self.formal_claims_manifest),
            "acceptance_receipt_schema": str(self.acceptance_receipt_schema),
            "verifier_rules": str(self.verifier_rules),
            "formal_claims_manifest_sha256": self.formal_claims_manifest_sha256,
            "component_count": self.component_count,
            "settlement_authority_components": list(self.settlement_authority_components),
            "acceptance_receipt_authorizes_settlement": False,
            "settlement_authority_predicate": "FIREVReceiptOK",
            "settlement_authority_missing_or_mismatch_behavior": "reject",
        }


def _as_mapping(value: object, *, ctx: str) -> Mapping[str, object]:
    if not isinstance(value, Mapping):
        raise FireReleaseAssuranceError(f"{ctx}: expected object")
    return value


def _expect(condition: bool, message: str) -> None:
    if not condition:
        raise FireReleaseAssuranceError(message)


def _load_json(path: Path) -> Mapping[str, object]:
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except Exception as exc:
        raise FireReleaseAssuranceError(f"failed to read JSON {path}: {exc}") from exc
    return _as_mapping(payload, ctx=str(path))


def _load_yaml(path: Path) -> Mapping[str, object]:
    try:
        payload = yaml.safe_load(path.read_text(encoding="utf-8"))
    except Exception as exc:
        raise FireReleaseAssuranceError(f"failed to read YAML {path}: {exc}") from exc
    return _as_mapping(payload, ctx=str(path))


def _check_acceptance_receipt_schema(path: Path) -> None:
    schema = _load_json(path)
    package_acceptance = _as_mapping(
        _as_mapping(schema.get("properties"), ctx="acceptance_schema.properties").get("package_acceptance"),
        ctx="acceptance_schema.properties.package_acceptance",
    )
    package_props = _as_mapping(package_acceptance.get("properties"), ctx="acceptance_schema.package_acceptance.properties")
    authorizes_settlement = _as_mapping(
        package_props.get("authorizes_settlement"),
        ctx="acceptance_schema.package_acceptance.authorizes_settlement",
    )
    _expect(
        authorizes_settlement.get("const") is False,
        "acceptance receipt schema must pin package_acceptance.authorizes_settlement to false",
    )


def _check_verifier_rules(path: Path) -> None:
    rules = _load_yaml(path)
    settlement_rules = rules.get("settlement_rules")
    _expect(isinstance(settlement_rules, list), "verifier-rules settlement_rules must be a list")
    _expect("settlement_authority_receipt_binding" in settlement_rules, "settlement_authority_receipt_binding missing")

    catalog = _as_mapping(rules.get("rule_catalog"), ctx="verifier-rules.rule_catalog")
    settlement_catalog = catalog.get("settlement")
    _expect(isinstance(settlement_catalog, list), "verifier-rules.rule_catalog.settlement must be a list")

    rule = None
    for raw_entry in settlement_catalog:
        entry = _as_mapping(raw_entry, ctx="verifier-rules.rule_catalog.settlement[]")
        if entry.get("id") == "settlement_authority_receipt_binding":
            rule = entry
            break
    _expect(rule is not None, "settlement_authority_receipt_binding catalog entry missing")

    establishes = rule.get("establishes")
    _expect(isinstance(establishes, list) and establishes, "settlement authority rule must establish a predicate")
    predicates = {
        str(_as_mapping(entry, ctx="settlement_authority_receipt_binding.establishes[]").get("predicate"))
        for entry in establishes
    }
    _expect("FIREVReceiptOK" in predicates, "settlement authority rule must establish FIREVReceiptOK")

    reject_if = rule.get("reject_if")
    _expect(isinstance(reject_if, list), "settlement authority rule must declare reject_if conditions")
    missing_rejects = sorted(REQUIRED_SETTLEMENT_RULE_REJECTS - {str(value) for value in reject_if})
    _expect(not missing_rejects, f"settlement authority rule missing reject_if conditions: {missing_rejects}")

    non_authoritative_surfaces = rules.get("non_authoritative_surfaces")
    _expect(isinstance(non_authoritative_surfaces, list), "non_authoritative_surfaces must be a list")
    missing_surfaces = sorted(REQUIRED_NON_AUTHORITATIVE_SURFACES - {str(value) for value in non_authoritative_surfaces})
    _expect(not missing_surfaces, f"missing non-authoritative surfaces: {missing_surfaces}")


def _check_authority_api_requires_witness_and_command_tag() -> None:
    receipt_without_witness = FireVerifierReceipt.build(
        object_hash="sha256:" + "1" * 64,
        instance_hash="sha256:" + "2" * 64,
        cert_sha256="sha256:" + "3" * 64,
        holder_delta=1,
        writer_delta=-1,
        command_tag="firev_accept_and_settle",
        object_name="ReleaseGateProbe",
        object_version="v1",
    )
    packet_without_witness = FireSettlementPacket.build(
        receipt=receipt_without_witness,
        holder_delta=1,
        writer_delta=-1,
        payoff_out=1,
        firev_accept=True,
    )
    ok, err = verify_fire_settlement_packet(packet_without_witness)
    _expect(ok and err is None, "generic settlement packet verifier should remain a structural checker")
    ok, err = verify_fire_settlement_authority_packet(packet_without_witness)
    _expect(not ok and err == "receipt_witness_hash_missing", "authority packet verifier must require witness_hash")

    witness_hash = fire_witness_binding_hash({"witness_final": 1})
    advisory_receipt = FireVerifierReceipt.build(
        object_hash=receipt_without_witness.object_hash,
        instance_hash=receipt_without_witness.instance_hash,
        cert_sha256=receipt_without_witness.cert_sha256,
        holder_delta=1,
        writer_delta=-1,
        command_tag="advisory_only",
        object_name=receipt_without_witness.object_name,
        object_version=receipt_without_witness.object_version,
        witness_hash=witness_hash,
    )
    advisory_packet = FireSettlementPacket.build(
        receipt=advisory_receipt,
        holder_delta=1,
        writer_delta=-1,
        payoff_out=1,
        firev_accept=True,
    )
    ok, err = verify_fire_settlement_authority_packet(advisory_packet)
    _expect(not ok and err == "receipt_command_tag_mismatch", "authority packet verifier must require authority command tag")


def _check_money_moving_sources_use_authority_api(source_root: Path) -> None:
    for rel, rule in MONEY_MOVING_SOURCE_RULES.items():
        path = source_root / rel
        _expect(path.is_file(), f"money-moving source file missing: {rel}")
        text = path.read_text(encoding="utf-8")
        for required in rule["required"]:
            _expect(required in text, f"{rel}: missing authority API marker {required}")
        for forbidden in rule["forbidden"]:
            _expect(forbidden not in text, f"{rel}: forbidden generic verifier call {forbidden}")


def verify_fire_release_assurance(
    *,
    formal_claims_manifest: Path | None = None,
    acceptance_receipt_schema: Path | None = None,
    verifier_rules: Path | None = None,
    repo_root: Path | None = None,
    source_root: Path | None = None,
) -> tuple[bool, str | None, FireReleaseAssuranceVerification | None]:
    resolved_formal_claims = (formal_claims_manifest or fire_formal_assurance_claims_path()).resolve()
    resolved_acceptance_schema = (acceptance_receipt_schema or fire_acceptance_receipt_schema_path()).resolve()
    resolved_verifier_rules = (verifier_rules or fire_verifier_rules_path()).resolve()
    resolved_source_root = (source_root.resolve() if source_root is not None else resolved_formal_claims.parents[3])
    try:
        ok, err, formal_verification = verify_fire_formal_assurance_claims_file(
            resolved_formal_claims,
            repo_root=repo_root,
        )
        if not ok or formal_verification is None:
            raise FireReleaseAssuranceError(f"formal assurance claims failed: {err}")

        _check_acceptance_receipt_schema(resolved_acceptance_schema)
        _check_verifier_rules(resolved_verifier_rules)
        _check_authority_api_requires_witness_and_command_tag()
        _check_money_moving_sources_use_authority_api(resolved_source_root)

        verification = FireReleaseAssuranceVerification(
            formal_claims_manifest=resolved_formal_claims,
            acceptance_receipt_schema=resolved_acceptance_schema,
            verifier_rules=resolved_verifier_rules,
            formal_claims_manifest_sha256=formal_verification.manifest_sha256,
            component_count=formal_verification.component_count,
            settlement_authority_components=formal_verification.settlement_authority_components,
        )
        return True, None, verification
    except FireReleaseAssuranceError as exc:
        return False, str(exc), None


__all__ = [
    "FIRE_RELEASE_ASSURANCE_CHECK_REPORT_SCHEMA",
    "FireReleaseAssuranceVerification",
    "verify_fire_release_assurance",
]
