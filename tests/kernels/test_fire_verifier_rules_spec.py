from __future__ import annotations

from pathlib import Path

import yaml


REPO_ROOT = Path(__file__).resolve().parents[2]
VERIFIER_RULES = REPO_ROOT / "src/fire/spec/verifier-rules.yaml"
EVIDENCE_LATTICE = REPO_ROOT / "src/fire/spec/evidence-lattice.yaml"


def _load_yaml(path: Path) -> dict[str, object]:
    payload = yaml.safe_load(path.read_text(encoding="utf-8"))
    assert isinstance(payload, dict)
    return payload


def test_fire_verifier_rules_schema_and_theorem_surface() -> None:
    spec = _load_yaml(VERIFIER_RULES)

    assert spec["schema"] == "zenodex/fire-verifier-rules/v1"

    theorem = spec["theorem"]
    assert isinstance(theorem, dict)
    assert theorem["name"] == "settlement_admissibility"
    assert theorem["statement"] == "FIREVAccept(O, I, Gamma, w, C) -> SettlementSafe(O, I, w, C)"

    required_checks = spec["required_checks"]
    assert isinstance(required_checks, list)
    assert "BoundOK" in required_checks
    assert "IntegerEvalOK" in required_checks
    assert "ReplayOK" in required_checks

    theorem_premises = theorem["premises"]
    assert isinstance(theorem_premises, list)
    assert theorem_premises == required_checks


def test_fire_verifier_rules_match_evidence_lattice_and_cal_ids() -> None:
    spec = _load_yaml(VERIFIER_RULES)
    lattice = _load_yaml(EVIDENCE_LATTICE)

    evidence_lattice = spec["evidence_lattice"]
    assert isinstance(evidence_lattice, dict)
    assert evidence_lattice["levels"] == lattice["levels"]
    assert evidence_lattice["meet_rule"] == lattice["meet_rule"]

    assert "fire_refiner" in spec["non_authoritative_surfaces"]
    assert "object_card" in spec["non_authoritative_surfaces"]

    rule_catalog = spec["rule_catalog"]
    assert isinstance(rule_catalog, dict)

    expected_ids = {
        "exact_param",
        "source_bound",
        "hash_bind_object",
        "hash_bind_instance",
        "dependency_closed",
        "unit_add",
        "unit_sub",
        "unit_mul",
        "unit_div",
        "interval_const",
        "interval_add",
        "interval_sub",
        "interval_mul",
        "interval_min",
        "interval_max",
        "interval_positive_part",
        "interval_cap",
        "interval_clamp",
        "witness_bound_intro",
        "collateral_one_sided_writer",
        "collateral_two_party",
        "delta_conservation_cash",
        "delta_conservation_with_sinks",
        "replay_determinism",
        "fixed_point_rounding_bound",
        "settlement_authority_receipt_binding",
        "settlement_admissibility",
    }

    seen_ids: set[str] = set()
    for entries in rule_catalog.values():
        assert isinstance(entries, list)
        for entry in entries:
            assert isinstance(entry, dict)
            rule_id = entry["id"]
            assert isinstance(rule_id, str)
            assert rule_id not in seen_ids
            seen_ids.add(rule_id)

    assert expected_ids.issubset(seen_ids)


def test_fire_verifier_rules_include_machine_readable_proof_tree_shapes() -> None:
    spec = _load_yaml(VERIFIER_RULES)
    rule_catalog = spec["rule_catalog"]
    assert isinstance(rule_catalog, dict)

    shapes_by_id: dict[str, list[dict[str, object]]] = {}
    for entries in rule_catalog.values():
        assert isinstance(entries, list)
        for entry in entries:
            assert isinstance(entry, dict)
            establishes = entry.get("establishes", [])
            assert isinstance(establishes, list)
            shapes_by_id[entry["id"]] = establishes

    assert shapes_by_id["hash_bind_object"] == [
        {"predicate": "ObjectHashBindOK", "input_predicates": []}
    ]
    assert {"predicate": "InstanceHashBindOK", "input_predicates": ["ObjectHashBindOK"]} in shapes_by_id["hash_bind_instance"]
    assert {"predicate": "BoundLeafExactParam", "input_predicates": []} in shapes_by_id["exact_param"]
    assert {"predicate": "BoundLeafSourceBound", "input_predicates": []} in shapes_by_id["source_bound"]
    assert {"predicate": "BoundExpr"} in shapes_by_id["interval_min"]
    assert {"predicate": "BoundOK", "input_predicates": ["BoundExpr"]} in shapes_by_id["witness_bound_intro"]
    assert {"predicate": "WitnessOK", "input_predicates": []} in shapes_by_id["witness_bound_intro"]
    assert {"predicate": "CollateralOK", "input_predicates": ["BoundOK"]} in shapes_by_id["collateral_two_party"]
    assert {"predicate": "ReplayOK", "input_predicates": ["InstanceHashBindOK"]} in shapes_by_id["replay_determinism"]
    assert {
        "predicate": "FIREVReceiptOK",
        "input_predicates": ["ObjectHashBindOK", "InstanceHashBindOK", "WitnessOK", "DeltaConservationOK"],
    } in shapes_by_id["settlement_authority_receipt_binding"]


def test_fire_refinement_rules_remain_non_authoritative() -> None:
    spec = _load_yaml(VERIFIER_RULES)
    refinements = spec["refinement_rules"]
    assert isinstance(refinements, list)
    assert {entry["id"] for entry in refinements} == {
        "CapRefinement",
        "ClampRefinement",
        "CollateralRefinement",
        "WitnessRefinement",
        "UnitRepairRefinement",
        "SpreadRefinement",
        "TrancheRefinement",
        "EvidenceRefinement",
    }
    assert all(entry["trusted"] is False for entry in refinements)
