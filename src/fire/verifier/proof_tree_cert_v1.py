from __future__ import annotations

import json
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Mapping, Sequence

import yaml
from jsonschema import Draft202012Validator, FormatChecker

from src.fire.pathing_v1 import fire_cert_rules_schema_path, fire_verifier_rules_path
from src.fire.registry.instance_v1 import FireObjectInstanceManifest
from src.fire.registry.lock_v1 import FireObjectDependencyLock
from src.fire.registry.object_manifest_v1 import FireEvidenceLabels, FireObjectManifest
from src.fire.registry.replay_input_v1 import FireReplayInput
from src.fire.verifier.cert_v1 import FireCertNode, FireInstanceGateClaims, FireIntervalCertificate, _require_int, _require_sha256_prefixed, fire_cert_sha256


FIRE_PROOF_TREE_CERT_CHECK_REPORT_SCHEMA = "zenodex/fire-proof-tree-cert-check-report/v1"
_EVIDENCE_RANK = {
    "proved": 0,
    "contract": 1,
    "implemented": 2,
    "tested_discovery": 3,
    "hypothesis": 4,
}


@dataclass(frozen=True)
class FireProofTreeRuleShape:
    predicate: str
    input_predicates: tuple[str, ...] | None


def _evidence_meet(*levels: str) -> str:
    weakest = max((_EVIDENCE_RANK[level] for level in levels), default=_EVIDENCE_RANK["proved"])
    for level, rank in _EVIDENCE_RANK.items():
        if rank == weakest:
            return level
    raise AssertionError("unreachable evidence meet")


def _load_json(path: Path) -> Mapping[str, object]:
    payload = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(payload, dict):
        raise TypeError(f"{path} must contain a JSON object")
    return payload


def _error_path(error: Any) -> str:
    if not error.path:
        return "/"
    return "/" + "/".join(str(item) for item in error.path)


def _validate_against_schema(
    payload: Mapping[str, object],
    *,
    schema_path: Path,
) -> tuple[bool, str | None]:
    schema = json.loads(schema_path.read_text(encoding="utf-8"))
    validator = Draft202012Validator(schema, format_checker=FormatChecker())
    errors = sorted(validator.iter_errors(payload), key=lambda item: tuple(item.path))
    if not errors:
        return True, None
    first = errors[0]
    return False, f"proof_tree_cert_schema_invalid:{_error_path(first)}:{first.message}"


def _require_mapping(name: str, value: object) -> Mapping[str, object]:
    if not isinstance(value, Mapping):
        raise TypeError(f"{name} must be an object")
    return value


def _derive_evidence_floor(claims: Mapping[str, object]) -> str:
    weakest = max(
        (
            _EVIDENCE_RANK[_require_mapping(f"claims[{claim_name}]", claim_payload)["evidence"]]  # type: ignore[index]
            for claim_name, claim_payload in claims.items()
        ),
        default=_EVIDENCE_RANK["proved"],
    )
    for level, rank in _EVIDENCE_RANK.items():
        if rank == weakest:
            return level
    raise AssertionError("unreachable evidence floor")


def _load_verifier_rule_ids() -> frozenset[str]:
    payload = yaml.safe_load(fire_verifier_rules_path().read_text(encoding="utf-8"))
    if not isinstance(payload, dict):
        raise TypeError("verifier-rules.yaml must contain an object")
    rule_catalog = payload.get("rule_catalog")
    if not isinstance(rule_catalog, Mapping):
        raise TypeError("verifier-rules.yaml must contain rule_catalog")
    rule_ids: set[str] = set()
    for entries in rule_catalog.values():
        if not isinstance(entries, list):
            raise TypeError("verifier-rules.yaml rule_catalog entries must be lists")
        for entry in entries:
            if not isinstance(entry, Mapping):
                raise TypeError("verifier-rules.yaml rule entry must be an object")
            rule_id = entry.get("id")
            if not isinstance(rule_id, str) or not rule_id:
                raise TypeError("verifier-rules.yaml rule entry must contain a non-empty id")
            rule_ids.add(rule_id)
    return frozenset(rule_ids)


def _load_verifier_rule_shapes() -> dict[str, tuple[FireProofTreeRuleShape, ...]]:
    payload = yaml.safe_load(fire_verifier_rules_path().read_text(encoding="utf-8"))
    if not isinstance(payload, dict):
        raise TypeError("verifier-rules.yaml must contain an object")
    rule_catalog = payload.get("rule_catalog")
    if not isinstance(rule_catalog, Mapping):
        raise TypeError("verifier-rules.yaml must contain rule_catalog")
    rule_shapes: dict[str, tuple[FireProofTreeRuleShape, ...]] = {}
    for entries in rule_catalog.values():
        if not isinstance(entries, list):
            raise TypeError("verifier-rules.yaml rule_catalog entries must be lists")
        for entry in entries:
            if not isinstance(entry, Mapping):
                raise TypeError("verifier-rules.yaml rule entry must be an object")
            rule_id = entry.get("id")
            if not isinstance(rule_id, str) or not rule_id:
                raise TypeError("verifier-rules.yaml rule entry must contain a non-empty id")
            raw_shapes = entry.get("establishes", [])
            if not isinstance(raw_shapes, list):
                raise TypeError(f"verifier-rules.yaml establishes for {rule_id} must be a list")
            normalized_shapes: list[FireProofTreeRuleShape] = []
            seen_predicates: set[str] = set()
            for idx, raw_shape in enumerate(raw_shapes):
                shape_map = _require_mapping(f"verifier-rules.yaml establishes[{rule_id}][{idx}]", raw_shape)
                predicate = shape_map.get("predicate")
                if not isinstance(predicate, str) or not predicate:
                    raise TypeError(f"verifier-rules.yaml establishes[{rule_id}][{idx}] must contain a non-empty predicate")
                if predicate in seen_predicates:
                    raise TypeError(f"verifier-rules.yaml establishes for {rule_id} duplicates predicate {predicate}")
                seen_predicates.add(predicate)
                raw_input_predicates = shape_map.get("input_predicates")
                if raw_input_predicates is None:
                    input_predicates = None
                else:
                    if not isinstance(raw_input_predicates, list):
                        raise TypeError(
                            f"verifier-rules.yaml establishes[{rule_id}][{idx}].input_predicates must be a list when present"
                        )
                    normalized_inputs: list[str] = []
                    for input_idx, value in enumerate(raw_input_predicates):
                        if not isinstance(value, str) or not value:
                            raise TypeError(
                                f"verifier-rules.yaml establishes[{rule_id}][{idx}].input_predicates[{input_idx}] must be a non-empty string"
                            )
                        normalized_inputs.append(value)
                    input_predicates = tuple(normalized_inputs)
                normalized_shapes.append(
                    FireProofTreeRuleShape(
                        predicate=predicate,
                        input_predicates=input_predicates,
                    )
                )
            rule_shapes[rule_id] = tuple(normalized_shapes)
    return rule_shapes


_CANONICAL_FIRE_VERIFIER_RULE_IDS = _load_verifier_rule_ids()
_CANONICAL_FIRE_VERIFIER_RULE_SHAPES = _load_verifier_rule_shapes()


def _claims_from_instance_gate_claims(claims: FireInstanceGateClaims) -> dict[str, str]:
    return {
        "ParamOK": claims.param_ok,
        "AuthorizationOK": claims.authorization_ok,
        "NonceOK": claims.nonce_ok,
        "MaturityOK": claims.maturity_ok,
        "WindowOK": claims.window_ok,
    }


def _claims_from_manifest_evidence(evidence: FireEvidenceLabels) -> dict[str, str]:
    return {
        "BoundOK": evidence.payoff_bound,
        "CollateralOK": evidence.collateral_sufficiency,
        "WitnessOK": evidence.witness_policy,
        "ReplayOK": evidence.settlement_replay,
        "IntegerEvalOK": evidence.kernel_semantics,
        "UnitOK": evidence.unit_safety,
    }


def expected_fire_proof_tree_claim_evidence(
    object_manifest: FireObjectManifest,
    certificate: FireIntervalCertificate,
) -> dict[str, str]:
    if certificate.instance_gate_claims is None:
        raise ValueError("certificate instance_gate_claims are required for proof-tree consistency checks")
    return {
        **_claims_from_manifest_evidence(object_manifest.evidence),
        **_claims_from_instance_gate_claims(certificate.instance_gate_claims),
        "ObjectHashBindOK": "implemented",
        "InstanceHashBindOK": "implemented",
        "DependencyClosed": "contract",
    }


def expected_fire_proof_tree_dependency_hashes(
    object_lock: FireObjectDependencyLock,
) -> tuple[dict[str, str], ...]:
    return tuple(
        {
            "name": item.name,
            "version": item.object_version,
            "hash": item.ir_hash,
        }
        for item in object_lock.dependencies
    )


def expected_fire_proof_tree_object_bind_summary(
    object_manifest: FireObjectManifest,
    *,
    object_manifest_file_sha256: str,
) -> dict[str, object]:
    return {
        "artifact": "object_manifest",
        "object_manifest_sha256": object_manifest_file_sha256,
        "ir_hash": object_manifest.ir_hash,
    }


def expected_fire_proof_tree_instance_bind_summary(
    object_instance: FireObjectInstanceManifest,
    object_lock: FireObjectDependencyLock,
    *,
    object_instance_file_sha256: str,
) -> dict[str, object]:
    return {
        "artifact": "instance_manifest",
        "instance_manifest_sha256": object_instance_file_sha256,
        "object_hash": object_instance.object_hash,
        "lock_hash": object_lock.lock_hash,
    }


def expected_fire_proof_tree_dependency_summary(
    object_lock: FireObjectDependencyLock,
    *,
    object_lock_file_sha256: str,
) -> dict[str, object]:
    return {
        "dependency_count": str(len(object_lock.dependencies)),
        "object_lock_sha256": object_lock_file_sha256,
        "lock_hash": object_lock.lock_hash,
    }


def expected_fire_proof_tree_integer_eval_summary(
    certificate: FireIntervalCertificate,
    *,
    compile_receipt_sha256: str | None = None,
    kernel_receipt_sha256: str | None = None,
    kernel_eval_receipt_sha256: str | None = None,
) -> dict[str, object]:
    runtime_summary = summarize_fire_interval_certificate(certificate)
    exact_params = runtime_summary["exact_params"]
    source_bounds = runtime_summary["source_bounds"]
    assert isinstance(exact_params, list)
    assert isinstance(source_bounds, list)
    summary = {
        "runtime_root_rule": runtime_summary["root_rule"],
        "runtime_node_count": runtime_summary["node_count"],
        "exact_param_names": [str(item["name"]) for item in exact_params],
        "source_bound_names": [str(item["name"]) for item in source_bounds],
    }
    if compile_receipt_sha256 is not None:
        summary["compile_receipt_sha256"] = compile_receipt_sha256
    if kernel_receipt_sha256 is not None:
        summary["kernel_receipt_sha256"] = kernel_receipt_sha256
    if kernel_eval_receipt_sha256 is not None:
        summary["kernel_eval_receipt_sha256"] = kernel_eval_receipt_sha256
    return summary


def expected_fire_proof_tree_unit_summary(
    object_manifest: FireObjectManifest,
) -> dict[str, object]:
    return {
        "settlement_asset": object_manifest.settlement_asset,
        "parameter_units": [
            {"name": item.name, "unit": item.unit}
            for item in object_manifest.parameters
        ],
        "imported_interface_units": [
            {
                "name": item.name,
                "interface_object_id": item.interface_object_id,
                "interface_output": item.interface_output,
                "unit": item.unit,
            }
            for item in object_manifest.imported_interfaces
        ],
    }


def expected_fire_proof_tree_replay_summary(
    replay_input: FireReplayInput,
    *,
    replay_input_sha256: str,
    kernel_settlement_receipt: Mapping[str, object] | None = None,
    kernel_settlement_receipt_sha256: str | None = None,
    kernel_replay_receipt: Mapping[str, object] | None = None,
    kernel_replay_receipt_sha256: str | None = None,
) -> dict[str, object]:
    summary = {
        "replay_input_sha256": replay_input_sha256,
        "holder_posted": replay_input.holder_posted,
        "writer_posted": replay_input.writer_posted,
        "holder_balance": replay_input.holder_balance,
        "writer_balance": replay_input.writer_balance,
        "witness_inputs": dict(replay_input.witness_inputs),
    }
    if kernel_settlement_receipt is not None and kernel_settlement_receipt_sha256 is not None:
        summary["kernel_settlement_receipt_sha256"] = kernel_settlement_receipt_sha256
        summary["holder_delta"] = int(kernel_settlement_receipt["holder_delta"])
        summary["writer_delta"] = int(kernel_settlement_receipt["writer_delta"])
        summary["payoff_out"] = int(kernel_settlement_receipt["payoff_out"])
        summary["firev_accept"] = bool(kernel_settlement_receipt["firev_accept"])
    if kernel_replay_receipt is not None and kernel_replay_receipt_sha256 is not None:
        summary["kernel_replay_receipt_sha256"] = kernel_replay_receipt_sha256
        summary["transcript_sha256"] = str(kernel_replay_receipt["transcript_sha256"])
        summary["delta_sha256"] = str(kernel_replay_receipt["delta_sha256"])
        summary["settlement_state_sha256"] = str(kernel_replay_receipt["settlement_state_sha256"])
        summary["settlement_effects_sha256"] = str(kernel_replay_receipt["settlement_effects_sha256"])
    return summary


def _normalize_contract_receipt_summary(
    contract_receipts: Sequence[Mapping[str, object]],
) -> list[dict[str, object]]:
    normalized: list[dict[str, object]] = []
    for idx, item in enumerate(contract_receipts):
        item_map = _require_mapping(f"contract_receipts[{idx}]", item)
        name = item_map.get("name")
        if not isinstance(name, str) or not name:
            raise TypeError(f"contract_receipts[{idx}].name must be a non-empty string")
        roles_raw = item_map.get("roles")
        if not isinstance(roles_raw, Sequence) or isinstance(roles_raw, (str, bytes, bytearray)):
            raise TypeError(f"contract_receipts[{idx}].roles must be a sequence of non-empty strings")
        roles: list[str] = []
        for role_idx, role in enumerate(roles_raw):
            if not isinstance(role, str) or not role:
                raise TypeError(f"contract_receipts[{idx}].roles[{role_idx}] must be a non-empty string")
            roles.append(role)
        use_sites_raw = item_map.get("use_sites")
        if not isinstance(use_sites_raw, Sequence) or isinstance(use_sites_raw, (str, bytes, bytearray)):
            raise TypeError(f"contract_receipts[{idx}].use_sites must be a sequence of non-empty strings")
        use_sites: list[str] = []
        for use_site_idx, use_site in enumerate(use_sites_raw):
            if not isinstance(use_site, str) or not use_site:
                raise TypeError(f"contract_receipts[{idx}].use_sites[{use_site_idx}] must be a non-empty string")
            use_sites.append(use_site)
        normalized.append(
            {
                "name": name,
                "roles": sorted(roles),
                "use_sites": sorted(use_sites),
            }
        )
    normalized.sort(key=lambda item: str(item["name"]))
    return normalized


def expected_fire_proof_tree_contract_receipt_summary(
    object_manifest: FireObjectManifest,
) -> list[dict[str, object]]:
    grouped: dict[str, dict[str, set[str]]] = {}

    def record(name: str, role: str, *, use_site: str) -> None:
        entry = grouped.setdefault(name, {"roles": set(), "use_sites": set()})
        entry["roles"].add(role)
        entry["use_sites"].add(use_site)

    for imported in object_manifest.imported_interfaces:
        if imported.contract is None:
            continue
        record(imported.contract.name, imported.contract.role, use_site=f"import:{imported.name}")
    for witness in object_manifest.witnesses:
        if witness.contract is None:
            continue
        record(witness.contract.name, witness.contract.role, use_site=f"witness:{witness.name}")

    return [
        {
            "name": name,
            "roles": sorted(entry["roles"]),
            "use_sites": sorted(entry["use_sites"]),
        }
        for name, entry in sorted(grouped.items())
    ]


def expected_fire_proof_tree_witness_policy_summary(
    object_manifest: FireObjectManifest,
    *,
    contract_receipts: Sequence[Mapping[str, object]] | None = None,
) -> dict[str, object]:
    summary = {
        "witness_requirements": [
            {
                "name": item.name,
                "freshness": item.freshness,
                "lower": item.lower,
                "upper": item.upper,
                **(
                    {}
                    if item.contract is None
                    else {
                        "contract_name": item.contract.name,
                        "contract_role": item.contract.role,
                    }
                ),
            }
            for item in object_manifest.witnesses
        ],
        "imported_interface_requirements": [
            {
                "name": item.name,
                "interface_object_id": item.interface_object_id,
                "interface_output": item.interface_output,
                "unit": item.unit,
                "lower": item.lower,
                "upper": item.upper,
                **(
                    {}
                    if item.contract is None
                    else {
                        "contract_name": item.contract.name,
                        "contract_role": item.contract.role,
                    }
                ),
            }
            for item in object_manifest.imported_interfaces
        ],
    }
    summary["contract_receipts"] = (
        expected_fire_proof_tree_contract_receipt_summary(object_manifest)
        if contract_receipts is None
        else _normalize_contract_receipt_summary(contract_receipts)
    )
    return summary


def expected_fire_proof_tree_param_summary(
    object_manifest: FireObjectManifest,
    object_instance: FireObjectInstanceManifest,
) -> dict[str, object]:
    instance_values = {item.name: item.value for item in object_instance.parameters}
    return {
        "parameters": [
            {
                "name": item.name,
                "unit": item.unit,
                "minimum": item.minimum,
                "maximum": item.maximum,
                "value": instance_values[item.name],
            }
            for item in object_manifest.parameters
        ],
    }


def expected_fire_proof_tree_authorization_summary(
    object_manifest: FireObjectManifest,
    object_instance: FireObjectInstanceManifest,
) -> dict[str, object]:
    return {
        "authorization_mode": object_manifest.instance_policy.authorization_mode,
        "required_party_roles": list(object_manifest.instance_policy.required_party_roles),
        "bound_parties": [
            {
                "role": item.role,
                "party_id": item.party_id,
            }
            for item in object_instance.parties
        ],
    }


def expected_fire_proof_tree_nonce_summary(
    object_manifest: FireObjectManifest,
    object_instance: FireObjectInstanceManifest,
) -> dict[str, object]:
    return {
        "nonce_required": object_manifest.instance_policy.nonce_required,
        "nonce_present": bool(object_instance.nonce),
        "nonce": object_instance.nonce,
    }


def expected_fire_proof_tree_maturity_summary(
    object_manifest: FireObjectManifest,
    object_instance: FireObjectInstanceManifest,
) -> dict[str, object]:
    payload: dict[str, object] = {
        "maturity_required": object_manifest.instance_policy.maturity_required,
        "maturity_present": object_instance.maturity is not None,
    }
    if object_instance.maturity is not None:
        payload["maturity"] = object_instance.maturity
    return payload


def expected_fire_proof_tree_window_summary(
    object_manifest: FireObjectManifest,
    object_instance: FireObjectInstanceManifest,
) -> dict[str, object]:
    payload: dict[str, object] = {
        "settlement_window_required": object_manifest.instance_policy.settlement_window_required,
        "settlement_window_present": object_instance.settlement_window is not None,
    }
    if object_instance.settlement_window is not None:
        payload["settlement_window_start"] = object_instance.settlement_window.start
        payload["settlement_window_end"] = object_instance.settlement_window.end
    return payload


def _walk_runtime_certificate(
    node: FireCertNode,
    *,
    exact_params: dict[str, int],
    source_bounds: dict[str, tuple[int, int]],
) -> int:
    count = 1
    if node.rule == "exact_param":
        assert node.name is not None
        value = int(node.lower)
        if node.name in exact_params and exact_params[node.name] != value:
            raise ValueError(f"conflicting exact_param binding for {node.name}")
        exact_params[node.name] = value
    elif node.rule == "source_bound":
        assert node.name is not None
        bound = (int(node.lower), int(node.upper))
        if node.name in source_bounds and source_bounds[node.name] != bound:
            raise ValueError(f"conflicting source_bound binding for {node.name}")
        source_bounds[node.name] = bound
    for child in node.children:
        count += _walk_runtime_certificate(child, exact_params=exact_params, source_bounds=source_bounds)
    return count


def _summarize_runtime_certificate_node(node: FireCertNode) -> dict[str, object]:
    payload: dict[str, object] = {
        "rule": node.rule,
        "lower": int(node.lower),
        "upper": int(node.upper),
        "children": [_summarize_runtime_certificate_node(child) for child in node.children],
    }
    if node.name is not None:
        payload["name"] = node.name
    if node.value is not None:
        payload["value"] = int(node.value)
    elif node.rule in {"exact_param", "const"}:
        payload["value"] = int(node.lower)
    return payload


def summarize_fire_interval_certificate(certificate: FireIntervalCertificate) -> dict[str, object]:
    exact_params: dict[str, int] = {}
    source_bounds: dict[str, tuple[int, int]] = {}
    node_count = _walk_runtime_certificate(
        certificate.root,
        exact_params=exact_params,
        source_bounds=source_bounds,
    )
    return {
        "root_rule": certificate.root.rule,
        "root_interval": certificate.root.interval.to_dict(),
        "node_count": node_count,
        "exact_params": [
            {"name": name, "value": value}
            for name, value in sorted(exact_params.items())
        ],
        "source_bounds": [
            {"name": name, "lower": lower, "upper": upper}
            for name, (lower, upper) in sorted(source_bounds.items())
        ],
        "operator_tree": _summarize_runtime_certificate_node(certificate.root),
    }


def _normalize_runtime_certificate_summary(summary: object) -> dict[str, object]:
    summary_map = _require_mapping("runtime_certificate_summary", summary)
    root_rule = summary_map.get("root_rule")
    if not isinstance(root_rule, str) or not root_rule:
        raise TypeError("runtime_certificate_summary.root_rule must be a non-empty string")
    root_interval_map = _require_mapping("runtime_certificate_summary.root_interval", summary_map.get("root_interval"))
    root_interval = {
        "lower": _require_int("runtime_certificate_summary.root_interval.lower", root_interval_map.get("lower")),
        "upper": _require_int("runtime_certificate_summary.root_interval.upper", root_interval_map.get("upper")),
    }
    node_count = _require_int("runtime_certificate_summary.node_count", summary_map.get("node_count"))
    if node_count < 1:
        raise ValueError("runtime_certificate_summary.node_count must be positive")

    raw_exact_params = summary_map.get("exact_params")
    if not isinstance(raw_exact_params, list):
        raise TypeError("runtime_certificate_summary.exact_params must be a list")
    exact_params: list[dict[str, object]] = []
    for idx, entry in enumerate(raw_exact_params):
        entry_map = _require_mapping(f"runtime_certificate_summary.exact_params[{idx}]", entry)
        name = entry_map.get("name")
        if not isinstance(name, str) or not name:
            raise TypeError(f"runtime_certificate_summary.exact_params[{idx}].name must be a non-empty string")
        value = _require_int(f"runtime_certificate_summary.exact_params[{idx}].value", entry_map.get("value"))
        exact_params.append({"name": name, "value": value})

    raw_source_bounds = summary_map.get("source_bounds")
    if not isinstance(raw_source_bounds, list):
        raise TypeError("runtime_certificate_summary.source_bounds must be a list")
    source_bounds: list[dict[str, object]] = []
    for idx, entry in enumerate(raw_source_bounds):
        entry_map = _require_mapping(f"runtime_certificate_summary.source_bounds[{idx}]", entry)
        name = entry_map.get("name")
        if not isinstance(name, str) or not name:
            raise TypeError(f"runtime_certificate_summary.source_bounds[{idx}].name must be a non-empty string")
        lower = _require_int(f"runtime_certificate_summary.source_bounds[{idx}].lower", entry_map.get("lower"))
        upper = _require_int(f"runtime_certificate_summary.source_bounds[{idx}].upper", entry_map.get("upper"))
        source_bounds.append({"name": name, "lower": lower, "upper": upper})

    operator_tree = _normalize_runtime_operator_node(summary_map.get("operator_tree"))

    return {
        "root_rule": root_rule,
        "root_interval": root_interval,
        "node_count": node_count,
        "exact_params": sorted(exact_params, key=lambda item: str(item["name"])),
        "source_bounds": sorted(source_bounds, key=lambda item: str(item["name"])),
        "operator_tree": operator_tree,
    }


def _normalize_runtime_operator_node(node: object) -> dict[str, object]:
    node_map = _require_mapping("runtime_operator_node", node)
    rule = node_map.get("rule")
    if not isinstance(rule, str) or not rule:
        raise TypeError("runtime_operator_node.rule must be a non-empty string")
    lower = _require_int("runtime_operator_node.lower", node_map.get("lower"))
    upper = _require_int("runtime_operator_node.upper", node_map.get("upper"))
    raw_children = node_map.get("children")
    if not isinstance(raw_children, list):
        raise TypeError("runtime_operator_node.children must be a list")
    normalized: dict[str, object] = {
        "rule": rule,
        "lower": lower,
        "upper": upper,
        "children": [_normalize_runtime_operator_node(child) for child in raw_children],
    }
    name = node_map.get("name")
    if name is not None:
        if not isinstance(name, str) or not name:
            raise TypeError("runtime_operator_node.name must be a non-empty string")
        normalized["name"] = name
    value = node_map.get("value")
    if value is not None:
        normalized["value"] = _require_int("runtime_operator_node.value", value)
    elif rule in {"exact_param", "const"}:
        normalized["value"] = lower
    return normalized


def _runtime_operator_rule_to_proof_rule(rule: str) -> str:
    mapping = {
        "const": "interval_const",
        "exact_param": "exact_param",
        "source_bound": "source_bound",
        "add": "interval_add",
        "sub": "interval_sub",
        "mul": "interval_mul",
        "min": "interval_min",
        "max": "interval_max",
    }
    if rule not in mapping:
        raise ValueError(f"unsupported runtime operator rule: {rule}")
    return mapping[rule]


def _bound_expr_node_id(path: tuple[int, ...]) -> str:
    if not path:
        return "n_bound_expr"
    return "n_bound_expr_" + "_".join(str(item) for item in path)


def _reachable_input_node_ids(
    start_node_id: str,
    *,
    node_by_id: Mapping[str, Mapping[str, object]],
) -> set[str]:
    reachable: set[str] = set()
    stack = [start_node_id]
    while stack:
        node_id = stack.pop()
        if node_id in reachable:
            continue
        reachable.add(node_id)
        node_map = node_by_id[node_id]
        raw_inputs = node_map.get("inputs", [])
        if not isinstance(raw_inputs, list):
            continue
        for input_id in raw_inputs:
            if isinstance(input_id, str) and input_id in node_by_id:
                stack.append(input_id)
    return reachable


def _build_bound_proof_nodes(
    runtime_node: Mapping[str, object],
    *,
    evidence: str,
    path: tuple[int, ...] = (),
) -> list[dict[str, object]]:
    node_id = _bound_expr_node_id(path)
    rule = str(runtime_node["rule"])
    children = runtime_node["children"]
    assert isinstance(children, list)
    nodes: list[dict[str, object]] = []
    input_ids: list[str] = []
    for idx, child in enumerate(children):
        child_map = _require_mapping(f"runtime_operator_node[{idx}]", child)
        child_nodes = _build_bound_proof_nodes(child_map, evidence=evidence, path=(*path, idx))
        nodes.extend(child_nodes)
        input_ids.append(_bound_expr_node_id((*path, idx)))

    claim: dict[str, object]
    if rule == "exact_param":
        claim = {
            "predicate": "BoundLeafExactParam",
            "name": runtime_node["name"],
            "value": str(runtime_node.get("value", runtime_node["lower"])),
            "lower": str(runtime_node["lower"]),
            "upper": str(runtime_node["upper"]),
        }
    elif rule == "source_bound":
        claim = {
            "predicate": "BoundLeafSourceBound",
            "name": runtime_node["name"],
            "lower": str(runtime_node["lower"]),
            "upper": str(runtime_node["upper"]),
        }
    elif rule == "const":
        claim = {
            "predicate": "BoundLeafConst",
            "value": str(runtime_node.get("value", runtime_node["lower"])),
            "lower": str(runtime_node["lower"]),
            "upper": str(runtime_node["upper"]),
        }
    else:
        claim = {
            "predicate": "BoundExpr",
            "runtime_rule": rule,
            "lower": str(runtime_node["lower"]),
            "upper": str(runtime_node["upper"]),
        }
    node_payload: dict[str, object] = {
        "id": node_id,
        "rule": _runtime_operator_rule_to_proof_rule(rule),
        "claim": claim,
        "evidence": evidence,
    }
    if input_ids:
        node_payload["inputs"] = input_ids
    nodes.append(node_payload)
    return nodes


def _verify_bound_proof_tree_node(
    runtime_node: Mapping[str, object],
    *,
    path: tuple[int, ...],
    node_by_id: Mapping[str, Mapping[str, object]],
) -> tuple[bool, str | None]:
    node_id = _bound_expr_node_id(path)
    if node_id not in node_by_id:
        return False, f"proof_tree_cert_missing_bound_expr_node:{node_id}"
    node_map = node_by_id[node_id]
    expected_rule = _runtime_operator_rule_to_proof_rule(str(runtime_node["rule"]))
    if node_map.get("rule") != expected_rule:
        return False, f"proof_tree_cert_bound_expr_rule_mismatch:{node_id}"
    claim = _require_mapping(f"proof_tree[{node_id}].claim", node_map.get("claim"))
    rule = str(runtime_node["rule"])
    if rule == "exact_param":
        if claim.get("predicate") != "BoundLeafExactParam":
            return False, f"proof_tree_cert_bound_expr_predicate_mismatch:{node_id}"
        if claim.get("name") != runtime_node.get("name") or claim.get("value") != str(runtime_node.get("value", runtime_node.get("lower"))):
            return False, f"proof_tree_cert_bound_expr_leaf_mismatch:{node_id}"
    elif rule == "source_bound":
        if claim.get("predicate") != "BoundLeafSourceBound":
            return False, f"proof_tree_cert_bound_expr_predicate_mismatch:{node_id}"
        if (
            claim.get("name") != runtime_node.get("name")
            or claim.get("lower") != str(runtime_node.get("lower"))
            or claim.get("upper") != str(runtime_node.get("upper"))
        ):
            return False, f"proof_tree_cert_bound_expr_leaf_mismatch:{node_id}"
    elif rule == "const":
        if claim.get("predicate") != "BoundLeafConst":
            return False, f"proof_tree_cert_bound_expr_predicate_mismatch:{node_id}"
        if claim.get("value") != str(runtime_node.get("value", runtime_node.get("lower"))):
            return False, f"proof_tree_cert_bound_expr_leaf_mismatch:{node_id}"
    else:
        if claim.get("predicate") != "BoundExpr":
            return False, f"proof_tree_cert_bound_expr_predicate_mismatch:{node_id}"
        if claim.get("runtime_rule") != rule:
            return False, f"proof_tree_cert_bound_expr_runtime_rule_mismatch:{node_id}"
    if claim.get("lower") != str(runtime_node.get("lower")) or claim.get("upper") != str(runtime_node.get("upper")):
        return False, f"proof_tree_cert_bound_expr_interval_mismatch:{node_id}"
    raw_inputs = node_map.get("inputs", [])
    if not isinstance(raw_inputs, list):
        return False, f"proof_tree_cert_inputs_invalid:{node_id}"
    expected_inputs = [_bound_expr_node_id((*path, idx)) for idx, _ in enumerate(runtime_node["children"])]
    if raw_inputs != expected_inputs:
        return False, f"proof_tree_cert_bound_expr_inputs_mismatch:{node_id}"
    for idx, child in enumerate(runtime_node["children"]):
        child_map = _require_mapping(f"runtime_operator_node.children[{idx}]", child)
        ok, err = _verify_bound_proof_tree_node(child_map, path=(*path, idx), node_by_id=node_by_id)
        if not ok:
            return False, err
    return True, None


def _proof_tree_node_predicate(node_id: str, node_map: Mapping[str, object]) -> tuple[bool, str | None, str | None]:
    claim = _require_mapping(f"proof_tree[{node_id}].claim", node_map.get("claim"))
    predicate = claim.get("predicate")
    if not isinstance(predicate, str) or not predicate:
        return False, f"proof_tree_cert_claim_predicate_invalid:{node_id}", None
    return True, None, predicate


def _claim_summary_matches(
    claim: Mapping[str, object],
    expected_summary: Mapping[str, object],
) -> bool:
    for key, expected_value in expected_summary.items():
        if claim.get(key) != expected_value:
            return False
    return True


def _normalize_dependency_hashes(raw_dependency_hashes: object) -> tuple[tuple[str, str | None, str], ...]:
    if not isinstance(raw_dependency_hashes, list):
        raise TypeError("dependency_hashes must be a list")
    normalized: list[tuple[str, str | None, str]] = []
    for idx, entry in enumerate(raw_dependency_hashes):
        entry_map = _require_mapping(f"dependency_hashes[{idx}]", entry)
        name = entry_map.get("name")
        if not isinstance(name, str) or not name:
            raise TypeError(f"dependency_hashes[{idx}].name must be a non-empty string")
        version = entry_map.get("version")
        if version is not None and (not isinstance(version, str) or not version):
            raise TypeError(f"dependency_hashes[{idx}].version must be a non-empty string when present")
        digest = _require_sha256_prefixed(f"dependency_hashes[{idx}].hash", entry_map.get("hash"))
        normalized.append((name, version, digest))
    return tuple(normalized)


def build_fire_proof_tree_certificate(
    *,
    object_manifest: FireObjectManifest,
    object_instance: FireObjectInstanceManifest,
    object_lock: FireObjectDependencyLock,
    certificate: FireIntervalCertificate,
    object_manifest_file_sha256: str,
    object_instance_file_sha256: str,
    object_lock_file_sha256: str,
    replay_input: FireReplayInput | None = None,
    replay_input_sha256: str | None = None,
    compile_receipt_sha256: str | None = None,
    kernel_receipt_sha256: str | None = None,
    kernel_eval_receipt_sha256: str | None = None,
    kernel_settlement_receipt: Mapping[str, object] | None = None,
    kernel_settlement_receipt_sha256: str | None = None,
    kernel_replay_receipt: Mapping[str, object] | None = None,
    kernel_replay_receipt_sha256: str | None = None,
) -> dict[str, object]:
    if certificate.instance_gate_claims is None:
        raise ValueError("certificate instance_gate_claims are required to build a proof-tree sidecar")
    if (replay_input is None) != (replay_input_sha256 is None):
        raise ValueError("replay_input and replay_input_sha256 must be provided together")
    if (kernel_settlement_receipt is None) != (kernel_settlement_receipt_sha256 is None):
        raise ValueError("kernel_settlement_receipt and kernel_settlement_receipt_sha256 must be provided together")
    if (kernel_replay_receipt is None) != (kernel_replay_receipt_sha256 is None):
        raise ValueError("kernel_replay_receipt and kernel_replay_receipt_sha256 must be provided together")

    manifest_claims = _claims_from_manifest_evidence(object_manifest.evidence)
    instance_claims = _claims_from_instance_gate_claims(certificate.instance_gate_claims)
    runtime_certificate_summary = summarize_fire_interval_certificate(certificate)
    object_bind_summary = expected_fire_proof_tree_object_bind_summary(
        object_manifest,
        object_manifest_file_sha256=object_manifest_file_sha256,
    )
    instance_bind_summary = expected_fire_proof_tree_instance_bind_summary(
        object_instance,
        object_lock,
        object_instance_file_sha256=object_instance_file_sha256,
    )
    dependency_summary = expected_fire_proof_tree_dependency_summary(
        object_lock,
        object_lock_file_sha256=object_lock_file_sha256,
    )
    integer_eval_summary = expected_fire_proof_tree_integer_eval_summary(
        certificate,
        compile_receipt_sha256=compile_receipt_sha256,
        kernel_receipt_sha256=kernel_receipt_sha256,
        kernel_eval_receipt_sha256=kernel_eval_receipt_sha256,
    )
    unit_summary = expected_fire_proof_tree_unit_summary(object_manifest)
    witness_policy_summary = expected_fire_proof_tree_witness_policy_summary(object_manifest)
    param_summary = expected_fire_proof_tree_param_summary(object_manifest, object_instance)
    authorization_summary = expected_fire_proof_tree_authorization_summary(object_manifest, object_instance)
    nonce_summary = expected_fire_proof_tree_nonce_summary(object_manifest, object_instance)
    maturity_summary = expected_fire_proof_tree_maturity_summary(object_manifest, object_instance)
    window_summary = expected_fire_proof_tree_window_summary(object_manifest, object_instance)
    replay_summary = (
        None
        if replay_input is None or replay_input_sha256 is None
        else expected_fire_proof_tree_replay_summary(
            replay_input,
            replay_input_sha256=replay_input_sha256,
            kernel_settlement_receipt=kernel_settlement_receipt,
            kernel_settlement_receipt_sha256=kernel_settlement_receipt_sha256,
            kernel_replay_receipt=kernel_replay_receipt,
            kernel_replay_receipt_sha256=kernel_replay_receipt_sha256,
        )
    )
    claim_evidence = {
        **manifest_claims,
        **instance_claims,
        "ObjectHashBindOK": "implemented",
        "InstanceHashBindOK": "implemented",
        "DependencyClosed": "contract",
    }

    proof_tree: list[dict[str, object]] = [
        {
            "id": "n_object_hash",
            "rule": "hash_bind_object",
            "claim": {
                "predicate": "ObjectHashBindOK",
                **object_bind_summary,
            },
            "evidence": claim_evidence["ObjectHashBindOK"],
        },
        {
            "id": "n_instance_hash",
            "rule": "hash_bind_instance",
            "claim": {
                "predicate": "InstanceHashBindOK",
                **instance_bind_summary,
            },
            "inputs": ["n_object_hash"],
            "evidence": claim_evidence["InstanceHashBindOK"],
        },
        {
            "id": "n_dependency_closed",
            "rule": "dependency_closed",
            "claim": {
                "predicate": "DependencyClosed",
                **dependency_summary,
            },
            "evidence": claim_evidence["DependencyClosed"],
        },
        {
            "id": "n_collateral",
            "rule": "collateral_two_party",
            "claim": {
                "predicate": "CollateralOK",
                "holder_required": str(object_manifest.holder_collateral_required),
                "writer_required": str(object_manifest.writer_collateral_required),
            },
            "inputs": ["n_bound"],
            "evidence": claim_evidence["CollateralOK"],
        },
        {
            "id": "n_witness",
            "rule": "witness_bound_intro",
            "claim": {
                "predicate": "WitnessOK",
                **witness_policy_summary,
            },
            "evidence": claim_evidence["WitnessOK"],
        },
        {
            "id": "n_replay",
            "rule": "replay_determinism",
            "claim": {
                "predicate": "ReplayOK",
                **({} if replay_summary is None else replay_summary),
            },
            "inputs": ["n_instance_hash"],
            "evidence": claim_evidence["ReplayOK"],
        },
        {
            "id": "n_integer_eval",
            "rule": "fixed_point_rounding_bound",
            "claim": {
                "predicate": "IntegerEvalOK",
                **integer_eval_summary,
            },
            "evidence": claim_evidence["IntegerEvalOK"],
        },
        {
            "id": "n_unit",
            "rule": "unit_add",
            "claim": {
                "predicate": "UnitOK",
                **unit_summary,
            },
            "evidence": claim_evidence["UnitOK"],
        },
    ]

    bound_expr_nodes = _build_bound_proof_nodes(
        _require_mapping("runtime_certificate_summary.operator_tree", runtime_certificate_summary["operator_tree"]),
        evidence=claim_evidence["BoundOK"],
    )
    proof_tree.extend(bound_expr_nodes)

    proof_tree.insert(
        3,
        {
            "id": "n_bound",
            "rule": "witness_bound_intro",
            "claim": {
                "predicate": "BoundOK",
                "lower": str(runtime_certificate_summary["root_interval"]["lower"]),
                "upper": str(runtime_certificate_summary["root_interval"]["upper"]),
                "runtime_root_rule": runtime_certificate_summary["root_rule"],
                "runtime_node_count": str(runtime_certificate_summary["node_count"]),
            },
            "inputs": [_bound_expr_node_id(())],
            "evidence": claim_evidence["BoundOK"],
        },
    )

    claim_nodes = {
        "BoundOK": "n_bound",
        "CollateralOK": "n_collateral",
        "WitnessOK": "n_witness",
        "ReplayOK": "n_replay",
        "IntegerEvalOK": "n_integer_eval",
        "UnitOK": "n_unit",
        "ObjectHashBindOK": "n_object_hash",
        "InstanceHashBindOK": "n_instance_hash",
        "DependencyClosed": "n_dependency_closed",
    }
    gate_rule_by_name = {
        "ParamOK": "hash_bind_instance",
        "AuthorizationOK": "hash_bind_instance",
        "NonceOK": "hash_bind_instance",
        "MaturityOK": "hash_bind_instance",
        "WindowOK": "hash_bind_instance",
    }
    gate_predicate_detail = {
        "ParamOK": "instance parameters within declared bounds",
        "AuthorizationOK": "required roles bound under instance policy",
        "NonceOK": "nonce present when instance policy requires it",
        "MaturityOK": "maturity gate satisfied or not required",
        "WindowOK": "settlement window gate satisfied or not required",
    }
    for claim_name in ("ParamOK", "AuthorizationOK", "NonceOK", "MaturityOK", "WindowOK"):
        node_id = f"n_{claim_name.removesuffix('OK').lower()}"
        proof_tree.append(
            {
                "id": node_id,
                "rule": gate_rule_by_name[claim_name],
                "claim": {
                    "predicate": claim_name,
                    "detail": gate_predicate_detail[claim_name],
                    **(
                        param_summary
                        if claim_name == "ParamOK"
                        else authorization_summary
                        if claim_name == "AuthorizationOK"
                        else nonce_summary
                        if claim_name == "NonceOK"
                        else maturity_summary
                        if claim_name == "MaturityOK"
                        else window_summary
                    ),
                },
                "inputs": ["n_instance_hash"],
                "evidence": claim_evidence[claim_name],
            }
        )
        claim_nodes[claim_name] = node_id

    claims = {
        claim_name: {
            "evidence": claim_evidence[claim_name],
            "claim": claim_name,
            "root_node": claim_nodes[claim_name],
        }
        for claim_name in sorted(claim_nodes)
    }

    dependency_hashes = [
        {
            "name": item.name,
            "version": item.object_version,
            "hash": item.ir_hash,
        }
        for item in object_lock.dependencies
    ]

    return {
        "version": "FIRE_CERT_RULES_v0.1",
        "object_hash": object_manifest.manifest_hash,
        "instance_hash": object_instance.instance_hash,
        "certificate_sha256": fire_cert_sha256(certificate),
        "runtime_certificate_summary": runtime_certificate_summary,
        "dependency_hashes": dependency_hashes,
        "evidence_floor": _evidence_meet(*claim_evidence.values()),
        "claims": claims,
        "proof_tree": proof_tree,
    }


@dataclass(frozen=True)
class FireProofTreeCertificateVerification:
    certificate_path: Path | None
    schema_path: Path
    object_hash: str
    instance_hash: str | None
    certificate_sha256: str
    evidence_floor: str
    claim_count: int
    proof_node_count: int

    def to_report_dict(self) -> dict[str, object]:
        payload = {
            "schema": FIRE_PROOF_TREE_CERT_CHECK_REPORT_SCHEMA,
            "ok": True,
            "schema_path": str(self.schema_path.resolve()),
            "object_hash": self.object_hash,
            "instance_hash": self.instance_hash,
            "certificate_sha256": self.certificate_sha256,
            "evidence_floor": self.evidence_floor,
            "claim_count": self.claim_count,
            "proof_node_count": self.proof_node_count,
        }
        if self.certificate_path is not None:
            payload["certificate_path"] = str(self.certificate_path.resolve())
        return payload


def verify_fire_proof_tree_certificate(
    payload: Mapping[str, object],
    *,
    expected_object_hash: str | None = None,
    expected_instance_hash: str | None = None,
    expected_certificate_sha256: str | None = None,
    expected_runtime_certificate_summary: Mapping[str, object] | None = None,
    expected_dependency_hashes: Sequence[Mapping[str, object]] | None = None,
    expected_claim_evidence: Mapping[str, str] | None = None,
    expected_integer_eval_summary: Mapping[str, object] | None = None,
    expected_unit_summary: Mapping[str, object] | None = None,
    expected_replay_summary: Mapping[str, object] | None = None,
    expected_witness_policy_summary: Mapping[str, object] | None = None,
    expected_param_summary: Mapping[str, object] | None = None,
    expected_authorization_summary: Mapping[str, object] | None = None,
    expected_nonce_summary: Mapping[str, object] | None = None,
    expected_maturity_summary: Mapping[str, object] | None = None,
    expected_window_summary: Mapping[str, object] | None = None,
    expected_object_bind_summary: Mapping[str, object] | None = None,
    expected_instance_bind_summary: Mapping[str, object] | None = None,
    expected_dependency_summary: Mapping[str, object] | None = None,
    certificate_path: Path | None = None,
) -> tuple[bool, str | None, FireProofTreeCertificateVerification | None]:
    schema_path = fire_cert_rules_schema_path()
    valid, err = _validate_against_schema(payload, schema_path=schema_path)
    if not valid:
        return False, err, None

    object_hash = payload["object_hash"]
    if not isinstance(object_hash, str):
        return False, "proof_tree_cert_object_hash_invalid", None
    if expected_object_hash is not None and object_hash != expected_object_hash:
        return False, "proof_tree_cert_object_hash_mismatch", None

    raw_instance_hash = payload.get("instance_hash")
    if raw_instance_hash is not None and not isinstance(raw_instance_hash, str):
        return False, "proof_tree_cert_instance_hash_invalid", None
    if expected_instance_hash is not None and raw_instance_hash != expected_instance_hash:
        return False, "proof_tree_cert_instance_hash_mismatch", None

    raw_certificate_sha256 = payload.get("certificate_sha256")
    try:
        certificate_sha256 = _require_sha256_prefixed("certificate_sha256", raw_certificate_sha256)
    except (TypeError, ValueError):
        return False, "proof_tree_cert_certificate_sha256_invalid", None
    if expected_certificate_sha256 is not None and certificate_sha256 != expected_certificate_sha256:
        return False, "proof_tree_cert_certificate_sha256_mismatch", None

    try:
        runtime_certificate_summary = _normalize_runtime_certificate_summary(payload.get("runtime_certificate_summary"))
    except (TypeError, ValueError):
        return False, "proof_tree_cert_runtime_certificate_summary_invalid", None
    if expected_runtime_certificate_summary is not None:
        expected_summary = _normalize_runtime_certificate_summary(dict(expected_runtime_certificate_summary))
        if runtime_certificate_summary != expected_summary:
            return False, "proof_tree_cert_runtime_certificate_summary_mismatch", None

    try:
        dependency_hashes = _normalize_dependency_hashes(payload.get("dependency_hashes"))
    except (TypeError, ValueError):
        return False, "proof_tree_cert_dependency_hashes_invalid", None
    if expected_dependency_hashes is not None:
        try:
            expected_dependencies = _normalize_dependency_hashes(list(expected_dependency_hashes))
        except (TypeError, ValueError):
            raise
        if dependency_hashes != expected_dependencies:
            return False, "proof_tree_cert_dependency_hashes_mismatch", None

    claims = _require_mapping("claims", payload["claims"])
    proof_tree = payload["proof_tree"]
    if not isinstance(proof_tree, list):
        return False, "proof_tree_cert_nodes_invalid", None

    node_ids: set[str] = set()
    node_by_id: dict[str, Mapping[str, object]] = {}
    for idx, node in enumerate(proof_tree):
        node_map = _require_mapping(f"proof_tree[{idx}]", node)
        node_id = node_map.get("id")
        if not isinstance(node_id, str):
            return False, f"proof_tree_cert_node_id_invalid:{idx}", None
        if node_id in node_ids:
            return False, f"proof_tree_cert_duplicate_node_id:{node_id}", None
        node_ids.add(node_id)
        node_by_id[node_id] = node_map
        rule_id = node_map.get("rule")
        if not isinstance(rule_id, str):
            return False, f"proof_tree_cert_rule_invalid:{idx}", None
        if rule_id not in _CANONICAL_FIRE_VERIFIER_RULE_IDS:
            return False, f"proof_tree_cert_unknown_rule:{rule_id}", None

    for idx, node in enumerate(proof_tree):
        node_map = _require_mapping(f"proof_tree[{idx}]", node)
        raw_inputs = node_map.get("inputs", [])
        if not isinstance(raw_inputs, list):
            return False, f"proof_tree_cert_inputs_invalid:{idx}", None
        for input_id in raw_inputs:
            if not isinstance(input_id, str):
                return False, f"proof_tree_cert_input_id_invalid:{idx}", None
            if input_id not in node_ids:
                return False, f"proof_tree_cert_missing_input_node:{input_id}", None
        node_id = node_map["id"]
        assert isinstance(node_id, str)
        ok, claim_err, predicate = _proof_tree_node_predicate(node_id, node_map)
        if not ok:
            assert claim_err is not None
            return False, claim_err, None
        assert predicate is not None
        rule_id = node_map["rule"]
        assert isinstance(rule_id, str)
        rule_shapes = _CANONICAL_FIRE_VERIFIER_RULE_SHAPES.get(rule_id, ())
        if not rule_shapes:
            return False, f"proof_tree_cert_rule_shape_missing:{rule_id}", None
        matching_shape = next((shape for shape in rule_shapes if shape.predicate == predicate), None)
        if matching_shape is None:
            return False, f"proof_tree_cert_rule_predicate_mismatch:{node_id}", None
        if matching_shape.input_predicates is not None:
            actual_input_predicates: list[str] = []
            for input_id in raw_inputs:
                assert isinstance(input_id, str)
                child_ok, child_err, child_predicate = _proof_tree_node_predicate(input_id, node_by_id[input_id])
                if not child_ok:
                    assert child_err is not None
                    return False, child_err, None
                assert child_predicate is not None
                actual_input_predicates.append(child_predicate)
            if tuple(actual_input_predicates) != matching_shape.input_predicates:
                return False, f"proof_tree_cert_rule_input_predicates_mismatch:{node_id}", None

    for claim_name, claim_payload in claims.items():
        claim_map = _require_mapping(f"claims[{claim_name}]", claim_payload)
        root_node = claim_map.get("root_node")
        if root_node is not None:
            if not isinstance(root_node, str):
                return False, f"proof_tree_cert_claim_root_invalid:{claim_name}", None
            if root_node not in node_ids:
                return False, f"proof_tree_cert_missing_root_node:{claim_name}:{root_node}", None
            root_node_map = node_by_id[root_node]
            root_claim = _require_mapping(f"proof_tree[{root_node}].claim", root_node_map.get("claim"))
            predicate = root_claim.get("predicate")
            if not isinstance(predicate, str) or predicate != claim_name:
                return False, f"proof_tree_cert_claim_root_predicate_mismatch:{claim_name}", None
            root_evidence = root_node_map.get("evidence")
            claim_evidence = claim_map.get("evidence")
            if root_evidence is not None and root_evidence != claim_evidence:
                return False, f"proof_tree_cert_claim_evidence_mismatch:{claim_name}", None
            if claim_name == "BoundOK":
                if root_claim.get("lower") != str(runtime_certificate_summary["root_interval"]["lower"]):
                    return False, "proof_tree_cert_bound_lower_mismatch", None
                if root_claim.get("upper") != str(runtime_certificate_summary["root_interval"]["upper"]):
                    return False, "proof_tree_cert_bound_upper_mismatch", None
                raw_inputs = root_node_map.get("inputs", [])
                if raw_inputs != [_bound_expr_node_id(())]:
                    return False, "proof_tree_cert_bound_root_input_mismatch", None
                ok, bound_err = _verify_bound_proof_tree_node(
                    _require_mapping(
                        "runtime_certificate_summary.operator_tree",
                        runtime_certificate_summary["operator_tree"],
                    ),
                    path=(),
                    node_by_id=node_by_id,
                )
                if not ok:
                    assert bound_err is not None
                    return False, bound_err, None
            elif claim_name == "IntegerEvalOK" and expected_integer_eval_summary is not None:
                if not _claim_summary_matches(root_claim, expected_integer_eval_summary):
                    return False, "proof_tree_cert_integer_eval_summary_mismatch", None
            elif claim_name == "UnitOK" and expected_unit_summary is not None:
                if not _claim_summary_matches(root_claim, expected_unit_summary):
                    return False, "proof_tree_cert_unit_summary_mismatch", None
            elif claim_name == "ReplayOK" and expected_replay_summary is not None:
                if not _claim_summary_matches(root_claim, expected_replay_summary):
                    return False, "proof_tree_cert_replay_summary_mismatch", None
            elif claim_name == "ObjectHashBindOK" and expected_object_bind_summary is not None:
                if not _claim_summary_matches(root_claim, expected_object_bind_summary):
                    return False, "proof_tree_cert_object_bind_summary_mismatch", None
            elif claim_name == "InstanceHashBindOK" and expected_instance_bind_summary is not None:
                if not _claim_summary_matches(root_claim, expected_instance_bind_summary):
                    return False, "proof_tree_cert_instance_bind_summary_mismatch", None
            elif claim_name == "DependencyClosed" and expected_dependency_summary is not None:
                if not _claim_summary_matches(root_claim, expected_dependency_summary):
                    return False, "proof_tree_cert_dependency_summary_mismatch", None
            elif claim_name == "WitnessOK" and expected_witness_policy_summary is not None:
                if not _claim_summary_matches(root_claim, expected_witness_policy_summary):
                    return False, "proof_tree_cert_witness_policy_summary_mismatch", None
            elif claim_name == "ParamOK" and expected_param_summary is not None:
                if not _claim_summary_matches(root_claim, expected_param_summary):
                    return False, "proof_tree_cert_param_summary_mismatch", None
            elif claim_name == "AuthorizationOK" and expected_authorization_summary is not None:
                if not _claim_summary_matches(root_claim, expected_authorization_summary):
                    return False, "proof_tree_cert_authorization_summary_mismatch", None
            elif claim_name == "NonceOK" and expected_nonce_summary is not None:
                if not _claim_summary_matches(root_claim, expected_nonce_summary):
                    return False, "proof_tree_cert_nonce_summary_mismatch", None
            elif claim_name == "MaturityOK" and expected_maturity_summary is not None:
                if not _claim_summary_matches(root_claim, expected_maturity_summary):
                    return False, "proof_tree_cert_maturity_summary_mismatch", None
            elif claim_name == "WindowOK" and expected_window_summary is not None:
                if not _claim_summary_matches(root_claim, expected_window_summary):
                    return False, "proof_tree_cert_window_summary_mismatch", None

    if expected_claim_evidence is not None:
        for claim_name, expected_evidence in expected_claim_evidence.items():
            claim_payload = claims.get(claim_name)
            if claim_payload is None:
                return False, f"proof_tree_cert_missing_claim:{claim_name}", None
            claim_map = _require_mapping(f"claims[{claim_name}]", claim_payload)
            actual_evidence = claim_map.get("evidence")
            if actual_evidence != expected_evidence:
                return False, f"proof_tree_cert_claim_evidence_mismatch:{claim_name}", None
            root_node = claim_map.get("root_node")
            if not isinstance(root_node, str):
                return False, f"proof_tree_cert_claim_root_invalid:{claim_name}", None

    evidence_floor = payload.get("evidence_floor")
    if evidence_floor is not None:
        if not isinstance(evidence_floor, str):
            return False, "proof_tree_cert_evidence_floor_invalid", None
        derived_evidence_floor = _derive_evidence_floor(claims)
        if evidence_floor != derived_evidence_floor:
            return False, "proof_tree_cert_evidence_floor_mismatch", None
    else:
        derived_evidence_floor = _derive_evidence_floor(claims)

    return (
        True,
        None,
        FireProofTreeCertificateVerification(
            certificate_path=certificate_path,
            schema_path=schema_path,
            object_hash=object_hash,
            instance_hash=raw_instance_hash,
            certificate_sha256=certificate_sha256,
            evidence_floor=derived_evidence_floor,
            claim_count=len(claims),
            proof_node_count=len(proof_tree),
        ),
    )


def verify_fire_proof_tree_certificate_file(
    path: str | Path,
    *,
    expected_object_hash: str | None = None,
    expected_instance_hash: str | None = None,
    expected_certificate_sha256: str | None = None,
) -> tuple[bool, str | None, FireProofTreeCertificateVerification | None]:
    certificate_path = Path(path).resolve()
    payload = _load_json(certificate_path)
    return verify_fire_proof_tree_certificate(
        payload,
        expected_object_hash=expected_object_hash,
        expected_instance_hash=expected_instance_hash,
        expected_certificate_sha256=expected_certificate_sha256,
        certificate_path=certificate_path,
    )


__all__ = [
    "FIRE_PROOF_TREE_CERT_CHECK_REPORT_SCHEMA",
    "FireProofTreeCertificateVerification",
    "build_fire_proof_tree_certificate",
    "expected_fire_proof_tree_claim_evidence",
    "expected_fire_proof_tree_contract_receipt_summary",
    "expected_fire_proof_tree_dependency_hashes",
    "expected_fire_proof_tree_dependency_summary",
    "expected_fire_proof_tree_integer_eval_summary",
    "expected_fire_proof_tree_instance_bind_summary",
    "expected_fire_proof_tree_object_bind_summary",
    "expected_fire_proof_tree_authorization_summary",
    "expected_fire_proof_tree_maturity_summary",
    "expected_fire_proof_tree_nonce_summary",
    "expected_fire_proof_tree_param_summary",
    "expected_fire_proof_tree_replay_summary",
    "expected_fire_proof_tree_unit_summary",
    "expected_fire_proof_tree_window_summary",
    "expected_fire_proof_tree_witness_policy_summary",
    "summarize_fire_interval_certificate",
    "verify_fire_proof_tree_certificate",
    "verify_fire_proof_tree_certificate_file",
]
