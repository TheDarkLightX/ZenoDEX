#!/usr/bin/env python3
"""Validate the adversarial hardening Pokayoke matrix.

The matrix is an obligation map, not production security evidence. This checker
fails closed when a named adversarial scenario lacks actors, a disaster state,
side/covert-channel controls, Pokayoke closure, an evidence lane, or explicit
non-claims.
"""

from __future__ import annotations

import argparse
import json
from json import JSONDecodeError
from pathlib import Path
from typing import Any, Mapping

REPO_ROOT = Path(__file__).resolve().parents[1]
DEFAULT_MANIFEST = REPO_ROOT / "tools" / "adversarial_hardening_pokayoke_matrix.json"

MATRIX_SCHEMA = "zenodex/adversarial_hardening_pokayoke_matrix/v1"
REPORT_SCHEMA = "zenodex/adversarial_hardening_pokayoke_matrix_report/v1"

REQUIRED_ACTORS = {
    "alice",
    "bob",
    "mallory",
    "sequencer",
    "oracle_reporter",
    "governance_operator",
}
REQUIRED_NON_CLAIMS = {
    "no_unknown_disaster_absence_claim",
    "no_production_security_claim",
    "no_model_authority",
    "no_settlement_authority",
    "no_side_channel_elimination_claim",
}
REQUIRED_SCENARIOS = {
    "AH-PK-001",
    "AH-PK-002",
    "AH-PK-003",
    "AH-PK-004",
    "AH-PK-005",
    "AH-PK-006",
    "AH-PK-007",
    "AH-PK-008",
}
ALLOWED_SEVERITIES = {"medium", "high", "critical"}
ALLOWED_STAGES = {"research_backlog", "promotion_target", "closed"}
ALLOWED_EVIDENCE_STATUSES = {"pending", "mapped_partial", "implemented_checker", "existing_replay"}
ALLOWED_DEFENSE_LAYERS = {
    "unrepresentable",
    "guarded_transition",
    "detected_at_commit",
    "bounded_blast_radius",
}
STRONG_DEFENSE_LAYERS = {"unrepresentable", "guarded_transition"}


def validate_matrix(matrix: Any) -> dict[str, Any]:
    errors: list[str] = []
    root = _mapping(matrix, "matrix", errors)
    if root.get("schema") != MATRIX_SCHEMA:
        errors.append("schema mismatch")
    if root.get("status") != "research_obligation_matrix":
        errors.append("status must be research_obligation_matrix")

    promotion = _validate_promotion_boundary(root.get("promotion_boundary"))
    actors = _validate_actors(root.get("actors"))
    controls = _validate_controls(root.get("control_classes"))
    scenarios = _validate_scenarios(
        root.get("scenarios"),
        actor_ids=actors["facts"]["actor_ids"],
        control_layers=controls["facts"]["control_layers"],
    )

    for name, section in (
        ("promotion_boundary", promotion),
        ("actors", actors),
        ("control_classes", controls),
        ("scenarios", scenarios),
    ):
        if not section["ok"]:
            errors.append(f"{name} rejected")

    return {
        "schema": REPORT_SCHEMA,
        "ok": not errors,
        "status": "accepted" if not errors else "rejected",
        "errors": errors,
        "facts": {
            "actor_count": actors["facts"]["actor_count"],
            "control_count": controls["facts"]["control_count"],
            "scenario_count": scenarios["facts"]["scenario_count"],
            "high_or_critical_scenario_count": scenarios["facts"]["high_or_critical_scenario_count"],
            "missing_required_scenarios": scenarios["facts"]["missing_required_scenarios"],
        },
        "promotion_boundary": promotion,
        "actors": actors,
        "control_classes": controls,
        "scenarios": scenarios,
    }


def _validate_promotion_boundary(value: Any) -> dict[str, Any]:
    errors: list[str] = []
    obj = _mapping(value, "promotion_boundary", errors)
    public_claim_allowed = _bool(obj.get("public_claim_allowed"), "promotion_boundary.public_claim_allowed", errors)
    claim_registry_entry_allowed = _bool(
        obj.get("claim_registry_entry_allowed"),
        "promotion_boundary.claim_registry_entry_allowed",
        errors,
    )
    model_authority = _str(obj.get("model_authority"), "promotion_boundary.model_authority", errors)
    non_claims = _str_set(obj.get("non_claims"), "promotion_boundary.non_claims", errors)

    if public_claim_allowed is not False:
        errors.append("promotion_boundary.public_claim_allowed must be false")
    if claim_registry_entry_allowed is not False:
        errors.append("promotion_boundary.claim_registry_entry_allowed must be false")
    if model_authority != "advisory_only":
        errors.append("promotion_boundary.model_authority must be advisory_only")

    missing_non_claims = sorted(REQUIRED_NON_CLAIMS - non_claims)
    if missing_non_claims:
        errors.append("promotion_boundary.non_claims missing required values")

    return {
        "ok": not errors,
        "errors": errors,
        "facts": {
            "public_claim_allowed": public_claim_allowed,
            "claim_registry_entry_allowed": claim_registry_entry_allowed,
            "model_authority": model_authority,
            "missing_required_non_claims": missing_non_claims,
        },
    }


def _validate_actors(value: Any) -> dict[str, Any]:
    errors: list[str] = []
    items = _list(value, "actors", errors)
    actor_ids: set[str] = set()
    reports: list[dict[str, Any]] = []
    for index, item in enumerate(items):
        item_errors: list[str] = []
        actor = _mapping(item, f"actors[{index}]", item_errors)
        actor_id = _str(actor.get("id"), f"actors[{index}].id", item_errors)
        _str(actor.get("role"), f"actors[{index}].role", item_errors)
        _str(actor.get("authority"), f"actors[{index}].authority", item_errors)
        _str(actor.get("incentive"), f"actors[{index}].incentive", item_errors)
        if actor_id is not None:
            if actor_id in actor_ids:
                item_errors.append("actor id must be unique")
            actor_ids.add(actor_id)
        reports.append({"id": actor_id, "ok": not item_errors, "errors": item_errors})

    missing = sorted(REQUIRED_ACTORS - actor_ids)
    if missing:
        errors.append(f"missing required actors: {', '.join(missing)}")
    if any(not report["ok"] for report in reports):
        errors.append("one or more actors rejected")

    return {
        "ok": not errors,
        "errors": errors,
        "facts": {
            "actor_count": len(actor_ids),
            "actor_ids": sorted(actor_ids),
            "missing_required_actors": missing,
        },
        "items": reports,
    }


def _validate_controls(value: Any) -> dict[str, Any]:
    errors: list[str] = []
    items = _list(value, "control_classes", errors)
    control_layers: dict[str, str] = {}
    reports: list[dict[str, Any]] = []
    for index, item in enumerate(items):
        item_errors: list[str] = []
        control = _mapping(item, f"control_classes[{index}]", item_errors)
        control_id = _str(control.get("id"), f"control_classes[{index}].id", item_errors)
        _str(control.get("description"), f"control_classes[{index}].description", item_errors)
        defense_layer = _str(control.get("defense_layer"), f"control_classes[{index}].defense_layer", item_errors)
        if defense_layer is not None and defense_layer not in ALLOWED_DEFENSE_LAYERS:
            item_errors.append("control defense_layer unsupported")
        if control_id is not None:
            if control_id in control_layers:
                item_errors.append("control id must be unique")
            elif defense_layer is not None:
                control_layers[control_id] = defense_layer
        reports.append({"id": control_id, "ok": not item_errors, "errors": item_errors})

    for required in ("reject_is_no_op", "side_channel_budget", "covert_channel_budget", "pokayoke_interlock"):
        if required not in control_layers:
            errors.append(f"missing required control: {required}")
    if any(not report["ok"] for report in reports):
        errors.append("one or more controls rejected")

    return {
        "ok": not errors,
        "errors": errors,
        "facts": {
            "control_count": len(control_layers),
            "control_ids": sorted(control_layers),
            "control_layers": control_layers,
        },
        "items": reports,
    }


def _validate_scenarios(value: Any, *, actor_ids: list[str], control_layers: Mapping[str, str]) -> dict[str, Any]:
    errors: list[str] = []
    items = _list(value, "scenarios", errors)
    known_actors = set(actor_ids)
    known_controls = set(control_layers)
    scenario_ids: set[str] = set()
    high_or_critical = 0
    reports: list[dict[str, Any]] = []

    for index, item in enumerate(items):
        item_errors: list[str] = []
        scenario = _mapping(item, f"scenarios[{index}]", item_errors)
        scenario_id = _str(scenario.get("id"), f"scenarios[{index}].id", item_errors)
        _str(scenario.get("title"), f"scenarios[{index}].title", item_errors)
        severity = _str(scenario.get("severity"), f"scenarios[{index}].severity", item_errors)
        stage = _str(scenario.get("stage"), f"scenarios[{index}].stage", item_errors)
        if severity is not None and severity not in ALLOWED_SEVERITIES:
            item_errors.append("severity unsupported")
        if stage is not None and stage not in ALLOWED_STAGES:
            item_errors.append("stage unsupported")
        if severity in {"high", "critical"}:
            high_or_critical += 1
        if scenario_id is not None:
            if scenario_id in scenario_ids:
                item_errors.append("scenario id must be unique")
            scenario_ids.add(scenario_id)

        _validate_scenario_actor_refs(scenario, index, known_actors, item_errors)
        scenario_controls = _validate_scenario_controls(scenario, index, known_controls, control_layers, item_errors)
        _validate_required_mapping_strings(scenario.get("game_surface"), f"scenarios[{index}].game_surface", item_errors)
        _validate_bounded_model(scenario.get("bounded_model"), f"scenarios[{index}].bounded_model", item_errors)

        for field in ("attack_query", "disaster_state", "mechanism_update", "game_theory_condition"):
            _str(scenario.get(field), f"scenarios[{index}].{field}", item_errors)
        defense_layers = _str_set(scenario.get("defense_layers"), f"scenarios[{index}].defense_layers", item_errors)
        if not defense_layers:
            item_errors.append("scenario must name at least one defense layer")
        if not defense_layers <= ALLOWED_DEFENSE_LAYERS:
            item_errors.append("scenario defense_layers contain unsupported value")
        if severity in {"high", "critical"} and not (defense_layers & STRONG_DEFENSE_LAYERS):
            item_errors.append("high or critical scenario needs unrepresentable or guarded_transition defense")

        _validate_channel_controls(scenario.get("side_channels"), f"scenarios[{index}].side_channels", item_errors)
        _validate_channel_controls(scenario.get("covert_channels"), f"scenarios[{index}].covert_channels", item_errors)
        _validate_evidence_lane(scenario.get("evidence_lane"), f"scenarios[{index}].evidence_lane", item_errors)
        _validate_scenario_promotion_boundary(
            scenario.get("promotion_boundary"),
            f"scenarios[{index}].promotion_boundary",
            item_errors,
        )
        if "mallory" not in set(_str_list(scenario.get("actors"), f"scenarios[{index}].actors", item_errors)):
            item_errors.append("scenario must include mallory")
        for required_control in ("reject_is_no_op", "side_channel_budget", "covert_channel_budget"):
            if required_control not in scenario_controls:
                item_errors.append(f"scenario must include {required_control}")

        reports.append({"id": scenario_id, "ok": not item_errors, "errors": item_errors})

    missing_required = sorted(REQUIRED_SCENARIOS - scenario_ids)
    if missing_required:
        errors.append("missing required scenarios")
    if high_or_critical < len(REQUIRED_SCENARIOS):
        errors.append("required adversarial scenarios must be high or critical")
    if any(not report["ok"] for report in reports):
        errors.append("one or more scenarios rejected")

    return {
        "ok": not errors,
        "errors": errors,
        "facts": {
            "scenario_count": len(scenario_ids),
            "high_or_critical_scenario_count": high_or_critical,
            "missing_required_scenarios": missing_required,
        },
        "items": reports,
    }


def _validate_scenario_actor_refs(
    scenario: Mapping[str, Any],
    index: int,
    known_actors: set[str],
    errors: list[str],
) -> None:
    actors = set(_str_list(scenario.get("actors"), f"scenarios[{index}].actors", errors))
    if not actors:
        errors.append("scenario must reference actors")
    unknown = sorted(actors - known_actors)
    if unknown:
        errors.append(f"scenario references unknown actors: {', '.join(unknown)}")


def _validate_scenario_controls(
    scenario: Mapping[str, Any],
    index: int,
    known_controls: set[str],
    control_layers: Mapping[str, str],
    errors: list[str],
) -> set[str]:
    controls = set(_str_list(scenario.get("controls"), f"scenarios[{index}].controls", errors))
    if not controls:
        errors.append("scenario must reference controls")
        return controls
    unknown = sorted(controls - known_controls)
    if unknown:
        errors.append(f"scenario references unknown controls: {', '.join(unknown)}")
    if not any(control_layers.get(control) in STRONG_DEFENSE_LAYERS for control in controls):
        errors.append("scenario controls need an unrepresentable or guarded_transition control")
    return controls


def _validate_required_mapping_strings(value: Any, field: str, errors: list[str]) -> None:
    obj = _mapping(value, field, errors)
    for key in ("players", "actions", "information_sets", "timing", "state", "payoff"):
        _str(obj.get(key), f"{field}.{key}", errors)


def _validate_bounded_model(value: Any, field: str, errors: list[str]) -> None:
    obj = _mapping(value, field, errors)
    for key in ("variables", "bounds", "assumptions", "exclusions"):
        items = _str_list(obj.get(key), f"{field}.{key}", errors)
        if not items:
            errors.append(f"{field}.{key} must be non-empty")


def _validate_channel_controls(value: Any, field: str, errors: list[str]) -> None:
    items = _list(value, field, errors)
    if not items:
        errors.append(f"{field} must be non-empty")
    for index, item in enumerate(items):
        obj = _mapping(item, f"{field}[{index}]", errors)
        _str(obj.get("channel"), f"{field}[{index}].channel", errors)
        _str(obj.get("control"), f"{field}[{index}].control", errors)


def _validate_evidence_lane(value: Any, field: str, errors: list[str]) -> None:
    obj = _mapping(value, field, errors)
    status = _str(obj.get("status"), f"{field}.status", errors)
    if status is not None and status not in ALLOWED_EVIDENCE_STATUSES:
        errors.append(f"{field}.status unsupported")
    _str(obj.get("next_command"), f"{field}.next_command", errors)
    _str(obj.get("promotion_requirement"), f"{field}.promotion_requirement", errors)


def _validate_scenario_promotion_boundary(value: Any, field: str, errors: list[str]) -> None:
    obj = _mapping(value, field, errors)
    claim_status = _str(obj.get("claim_status"), f"{field}.claim_status", errors)
    if claim_status == "production_ready":
        errors.append(f"{field}.claim_status cannot be production_ready")
    _str(obj.get("non_claim"), f"{field}.non_claim", errors)


def _mapping(value: Any, name: str, errors: list[str]) -> Mapping[str, Any]:
    if not isinstance(value, Mapping):
        errors.append(f"{name} must be an object")
        return {}
    return value


def _list(value: Any, name: str, errors: list[str]) -> list[Any]:
    if not isinstance(value, list):
        errors.append(f"{name} must be a list")
        return []
    return value


def _str(value: Any, name: str, errors: list[str]) -> str | None:
    if not isinstance(value, str) or value == "":
        errors.append(f"{name} must be a non-empty string")
        return None
    return value


def _bool(value: Any, name: str, errors: list[str]) -> bool | None:
    if not isinstance(value, bool):
        errors.append(f"{name} must be a bool")
        return None
    return value


def _str_list(value: Any, name: str, errors: list[str]) -> list[str]:
    raw = _list(value, name, errors)
    items: list[str] = []
    for index, item in enumerate(raw):
        parsed = _str(item, f"{name}[{index}]", errors)
        if parsed is not None:
            items.append(parsed)
    return items


def _str_set(value: Any, name: str, errors: list[str]) -> set[str]:
    return set(_str_list(value, name, errors))


def _load_json(path: Path) -> tuple[Any | None, list[str]]:
    try:
        return json.loads(path.read_text(encoding="utf-8")), []
    except FileNotFoundError:
        return None, [f"manifest missing: {path}"]
    except PermissionError:
        return None, [f"manifest unreadable: {path}"]
    except JSONDecodeError as exc:
        return None, [f"manifest json invalid: {exc.msg}"]


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("manifest", nargs="?", type=Path, default=DEFAULT_MANIFEST)
    parser.add_argument("--json", action="store_true", help="Emit a stable JSON report.")
    args = parser.parse_args(argv)

    manifest, load_errors = _load_json(args.manifest)
    if load_errors:
        report = {
            "schema": REPORT_SCHEMA,
            "ok": False,
            "status": "rejected",
            "errors": load_errors,
        }
    else:
        report = validate_matrix(manifest)

    if args.json or not report["ok"]:
        print(json.dumps(report, indent=2, sort_keys=True))
    elif report["ok"]:
        print("ok")
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
