"""Verifier-labeled EBRM corpus evidence tests."""

from __future__ import annotations

import json
import subprocess
import sys
from collections import defaultdict
from functools import lru_cache
from pathlib import Path
from typing import Any, Mapping, Sequence

from src.integration.autonomous_governance_ebrm_evidence import (
    AUTONOMOUS_GOVERNANCE_EBRM_CORPUS_SCHEMA_V1,
    AUTONOMOUS_GOVERNANCE_EBRM_EVIDENCE_SCHEMA_V1,
    AUTONOMOUS_GOVERNANCE_EBRM_TRAINED_RANKER_SCHEMA_V1,
    AUTONOMOUS_GOVERNANCE_EBRM_TRAINING_REPORT_SCHEMA_V1,
    build_autonomous_governance_ebrm_corpus_v1,
    build_autonomous_governance_ebrm_evidence_report_v1,
    build_autonomous_governance_ebrm_training_report_v1,
)

ROOT = Path(__file__).resolve().parents[2]


@lru_cache(maxsize=1)
def _cached_corpus() -> dict[str, Any]:
    return build_autonomous_governance_ebrm_corpus_v1()


@lru_cache(maxsize=1)
def _cached_evidence_report() -> dict[str, Any]:
    return build_autonomous_governance_ebrm_evidence_report_v1()


@lru_cache(maxsize=1)
def _cached_training_report() -> dict[str, Any]:
    return build_autonomous_governance_ebrm_training_report_v1()


def _group_rows(rows: Sequence[Mapping[str, Any]]) -> dict[str, list[Mapping[str, Any]]]:
    grouped: dict[str, list[Mapping[str, Any]]] = defaultdict(list)
    for row in rows:
        grouped[str(row["group_id"])].append(row)
    return grouped


class TestEBRMLabeledCorpus:
    def test_corpus_is_deterministic_and_hash_stable(self) -> None:
        first = build_autonomous_governance_ebrm_corpus_v1()
        second = build_autonomous_governance_ebrm_corpus_v1()

        assert first["schema"] == AUTONOMOUS_GOVERNANCE_EBRM_CORPUS_SCHEMA_V1
        assert first["corpus_hash"] == second["corpus_hash"]
        assert first["summary"] == second["summary"]
        assert first["rows"] == second["rows"]

    def test_every_group_has_gate_admitted_candidate_and_rejected_hard_negative(self) -> None:
        corpus = _cached_corpus()
        grouped = _group_rows(corpus["rows"])

        assert grouped
        assert all(any(row["gate_admitted"] is True for row in rows) for rows in grouped.values())
        assert any(row["gate_admitted"] is False for row in corpus["rows"])
        assert any(
            row["surface"] == "fee_bps"
            and row["curr"] == 30
            and row["candidate"] == 81
            and row["gate_errors"] == ("gov_gate_rejected:fee_bps",)
            for row in corpus["rows"]
        )

    def test_labels_are_not_model_features(self) -> None:
        corpus = _cached_corpus()
        summary = corpus["summary"]

        forbidden = set(summary["forbidden_feature_sources"])
        assert "gate_admitted" in forbidden
        assert "objective_cost" in forbidden
        assert "split" in forbidden
        assert "gate_admitted" not in set(summary["feature_sources"])
        assert "gate_admitted" not in set(summary["model_feature_names"])
        assert "objective_cost" not in set(summary["model_feature_names"])

    def test_compositional_energy_uses_structural_pressure_not_gate_label(self) -> None:
        corpus = _cached_corpus()
        for row in corpus["rows"]:
            features = row["model_features"]
            pressure = features["structural_guard_pressure"]
            assert "hard_gate_reject_penalty" not in row["energy_terms"]
            assert "structural_guard_penalty" in row["energy_terms"]
            if row["gate_admitted"] is True:
                assert pressure == 0
            else:
                assert pressure > 0

    def test_target_classes_match_gate_labels(self) -> None:
        corpus = _cached_corpus()
        for row in corpus["rows"]:
            if row["target_class"] == "gate_rejected":
                assert row["gate_admitted"] is False
                assert row["utility_regret_to_frontier"] is None
            else:
                assert row["gate_admitted"] is True


class TestEBRMEvidenceReport:
    def test_report_keeps_promotion_claim_false(self) -> None:
        report = _cached_evidence_report()

        assert report["schema"] == AUTONOMOUS_GOVERNANCE_EBRM_EVIDENCE_SCHEMA_V1
        assert report["ok"] is True
        assert report["production_promotion_claim"] is False
        assert report["promotion_ready"] is False
        assert "synthetic_corpus_only" in report["promotion_blockers"]
        assert "does_not_replace_tau_or_gov_gate" in report["not_claimed"]
        assert report["authority_boundary"]["label_authority"].endswith("gov_gate")

    def test_compositional_energy_beats_target_only_baseline_on_heldout(self) -> None:
        report = _cached_evidence_report()
        metrics = report["ranking_metrics"]
        comparison = metrics["comparison"]
        baseline = metrics["target_only_baseline"]["heldout"]
        compositional = metrics["compositional_ebrm"]["heldout"]

        assert comparison["compositional_beats_or_ties_baseline"] is True
        assert compositional["groups_without_admitted"] == 0
        assert (
            compositional["invalid_before_first_admitted_total"]
            <= baseline["invalid_before_first_admitted_total"]
        )
        assert compositional["selected_regret_total"] <= baseline["selected_regret_total"]

    def test_cli_emits_report_and_optional_corpus(self, tmp_path: Path) -> None:
        report_path = tmp_path / "ebrm-evidence-report.json"
        corpus_path = tmp_path / "ebrm-corpus.json"

        run = subprocess.run(
            [
                sys.executable,
                str(ROOT / "tools" / "autonomous_governance_q_policy.py"),
                "ebrm-evidence",
                "--output",
                str(report_path),
                "--corpus-output",
                str(corpus_path),
            ],
            cwd=ROOT,
            check=False,
            capture_output=True,
            text=True,
        )

        assert run.returncode == 0, run.stderr
        report = json.loads(report_path.read_text(encoding="utf-8"))
        corpus = json.loads(corpus_path.read_text(encoding="utf-8"))
        assert report["ok"] is True
        assert report["corpus_hash"] == corpus["corpus_hash"]
        assert corpus["summary"]["groups_total"] > 0


class TestEBRMTrainingReport:
    def test_training_report_is_deterministic_and_advisory(self) -> None:
        first = _cached_training_report()
        second = build_autonomous_governance_ebrm_training_report_v1()
        model = first["trained_model"]

        assert first["schema"] == AUTONOMOUS_GOVERNANCE_EBRM_TRAINING_REPORT_SCHEMA_V1
        assert first["training_report_hash"] == second["training_report_hash"]
        assert model["schema"] == AUTONOMOUS_GOVERNANCE_EBRM_TRAINED_RANKER_SCHEMA_V1
        assert model["model_hash"] == second["trained_model"]["model_hash"]
        assert model["authority"] == "candidate_ordering_only"
        assert first["production_promotion_claim"] is False
        assert first["promotion_ready"] is False
        assert "runtime_authority_remains_exact_gov_gate" in first["promotion_blockers"]

    def test_learned_ranker_beats_target_only_baseline_on_heldout(self) -> None:
        report = _cached_training_report()
        metrics = report["ranking_metrics"]
        comparison = metrics["comparison"]
        baseline = metrics["target_only_baseline"]["heldout"]
        learned = metrics["learned_ebrm"]["heldout"]

        assert report["ok"] is True
        assert comparison["learned_beats_or_ties_baseline"] is True
        assert learned["groups_without_admitted"] == 0
        assert learned["invalid_before_first_admitted_total"] <= baseline[
            "invalid_before_first_admitted_total"
        ]
        assert learned["selected_regret_total"] <= baseline["selected_regret_total"]
        assert learned["rank1_gate_admitted_count"] >= baseline["rank1_gate_admitted_count"]

    def test_cli_trains_report_and_model_artifact(self, tmp_path: Path) -> None:
        report_path = tmp_path / "ebrm-training-report.json"
        model_path = tmp_path / "ebrm-trained-model.json"

        run = subprocess.run(
            [
                sys.executable,
                str(ROOT / "tools" / "autonomous_governance_q_policy.py"),
                "ebrm-train",
                "--output",
                str(report_path),
                "--model-output",
                str(model_path),
            ],
            cwd=ROOT,
            check=False,
            capture_output=True,
            text=True,
        )

        assert run.returncode == 0, run.stderr
        report = json.loads(report_path.read_text(encoding="utf-8"))
        model = json.loads(model_path.read_text(encoding="utf-8"))
        assert report["ok"] is True
        assert report["trained_model"]["model_hash"] == model["model_hash"]
        assert model["authority"] == "candidate_ordering_only"
