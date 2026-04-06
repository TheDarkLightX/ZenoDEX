from __future__ import annotations

from pathlib import Path

from tools.krr_reasoner_engine import advise_candidate_krr, load_krr_kb
from tools.krr_refine_from_evidence import _build_hypothesis_index, _collect_evidence, _refine_kb
from tools.krr_self_improve_loop import _aggregate


def test_load_krr_kb_returns_defaults_for_missing_file(tmp_path: Path) -> None:
    kb = load_krr_kb(tmp_path / "missing_kb.json")
    assert kb["schema"] == "zenodex/krr-kb/v1"
    assert kb["operator_priors"] == {}
    assert kb["semantic_rules"] == []
    assert kb["check_priors"] == {}
    assert kb["check_family_priors"] == {}
    assert kb["engine"]["backend"] == "auto"
    assert kb["engine"]["prolog"]["binary"] == "swipl"
    assert kb["engine"]["souffle"]["binary"] == "souffle"
    assert kb["engine"]["scoring"]["exploitation_weight"] == 0.72


def test_advise_candidate_krr_uses_rules_priors_and_python_backend() -> None:
    kb = {
        "operator_priors": {
            "op_x": {
                "check_preferences": ["alpha::one"],
                "avoid_checks": ["gamma::three"],
                "score_bias": 0.2,
            }
        },
        "semantic_rules": [
            {
                "name": "route-rule",
                "if_semantic_contains": ["route"],
                "then_prefer_checks": ["beta::two"],
                "score_bias": 0.1,
            }
        ],
        "check_priors": {
            "alpha::one": {"score_bias": 0.9},
            "beta::two": {"score_bias": 0.1},
            "gamma::three": {"score_bias": -0.2},
        },
        "check_family_priors": {},
        "engine": {"backend": "python"},
    }
    history = {
        "alpha::one": {"supported": 9, "falsified": 1, "support_rate": 0.9, "total": 10},
        "beta::two": {"supported": 8, "falsified": 2, "support_rate": 0.8, "total": 10},
        "gamma::three": {"supported": 10, "falsified": 0, "support_rate": 1.0, "total": 10},
    }

    advice = advise_candidate_krr(
        operator_id="op_x",
        schema="schema_v1",
        semantic_signature="route canonical",
        check_options=["gamma::three"],
        history_check_stats=history,
        kb=kb,
        backend="python",
    )

    assert advice["preferred_checks"][:2] == ["alpha::one", "beta::two"]
    assert advice["score_delta"] == 0.30000000000000004
    assert advice["backend_requested"] == "python"
    assert advice["backend_used"] == "python"
    assert advice["backend_fallback_reason"] is None
    assert advice["semantic_predicates"] == ["canonicalization", "routing"]
    assert advice["rule_hits"] == [{"name": "route-rule", "score_bias": 0.1}]
    assert advice["confidence"] > 0.0


def test_refine_kb_learns_operator_priors_and_semantic_rules(tmp_path: Path) -> None:
    bridge_path = tmp_path / "bridge.json"
    summary_path = tmp_path / "summary.json"
    bridge_path.write_text(
        """
{
  "hypotheses": [
    {"hypothesis_id": "h1", "operator_id": "op_x", "support_recipe": "alpha::one", "zag_semantic_signature": "route canonical", "zag_schema": "schema_v1"},
    {"hypothesis_id": "h2", "operator_id": "op_x", "support_recipe": "alpha::one", "zag_semantic_signature": "route canonical", "zag_schema": "schema_v1"},
    {"hypothesis_id": "h3", "operator_id": "op_x", "support_recipe": "alpha::one", "zag_semantic_signature": "route canonical", "zag_schema": "schema_v1"},
    {"hypothesis_id": "h4", "operator_id": "op_x", "support_recipe": "alpha::one", "zag_semantic_signature": "route canonical", "zag_schema": "schema_v1"},
    {"hypothesis_id": "h5", "operator_id": "op_x", "support_recipe": "beta::two", "zag_semantic_signature": "route canonical", "zag_schema": "schema_v1"},
    {"hypothesis_id": "h6", "operator_id": "op_x", "support_recipe": "beta::two", "zag_semantic_signature": "route canonical", "zag_schema": "schema_v1"},
    {"hypothesis_id": "h7", "operator_id": "op_x", "support_recipe": "beta::two", "zag_semantic_signature": "route canonical", "zag_schema": "schema_v1"}
  ]
}
""".strip()
        + "\n",
        encoding="utf-8",
    )
    summary_path.write_text(
        """
{
  "rows": [
    {"hypothesis_id": "h1", "check": "alpha::one", "final_status": "supported"},
    {"hypothesis_id": "h2", "check": "alpha::one", "final_status": "supported"},
    {"hypothesis_id": "h3", "check": "alpha::one", "final_status": "supported"},
    {"hypothesis_id": "h4", "check": "alpha::one", "final_status": "supported"},
    {"hypothesis_id": "h5", "check": "beta::two", "final_status": "falsified"},
    {"hypothesis_id": "h6", "check": "beta::two", "final_status": "falsified"},
    {"hypothesis_id": "h7", "check": "beta::two", "final_status": "falsified"}
  ]
}
""".strip()
        + "\n",
        encoding="utf-8",
    )

    kb = load_krr_kb(tmp_path / "seed.json")
    hypothesis_index = _build_hypothesis_index([bridge_path])
    evidence = _collect_evidence([summary_path], hypothesis_index)
    refined = _refine_kb(
        kb=kb,
        evidence=evidence,
        min_count=1,
        max_preferred_checks=3,
        token_min_count=1,
        max_auto_rules=10,
    )

    op_prior = refined["operator_priors"]["op_x"]
    assert op_prior["check_preferences"][0] == "alpha::one"
    assert "beta::two" in op_prior["avoid_checks"]
    assert op_prior["evidence_total"] == 7
    assert refined["check_priors"]["alpha::one"]["evidence_supported"] == 4
    assert refined["check_family_priors"]["alpha"]["evidence_support_rate"] == 1.0
    assert any(rule["source"] == "auto_refine_v1" for rule in refined["semantic_rules"])
    assert refined["learning"]["matched_rows"] == 7


def test_self_improve_aggregate_combines_successful_runs() -> None:
    rows = [
        {
            "ok": True,
            "hypothesis_count": 4,
            "supported": 2,
            "falsified": 1,
            "inconclusive": 1,
            "avg_selection_score": 0.5,
            "frontier_size": 3,
        },
        {
            "ok": True,
            "hypothesis_count": 2,
            "supported": 1,
            "falsified": 1,
            "inconclusive": 0,
            "avg_selection_score": 0.7,
            "frontier_size": 1,
        },
        {"ok": False, "hypothesis_count": 99},
    ]

    agg = _aggregate(rows)
    assert agg == {
        "runs": 2,
        "total_hypotheses": 6,
        "supported": 3,
        "falsified": 2,
        "inconclusive": 1,
        "support_rate": 0.5,
        "avg_selection_score_mean": 0.6,
        "frontier_size_mean": 2.0,
    }
