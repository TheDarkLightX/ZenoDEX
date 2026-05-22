"""Chaos Toolkit experiment runner with JSON artifact output.

This module executes chaos experiments and produces standalone JSON
evidence artifacts (hypothesis, recipe, journal) that can be consumed
by external hypothesis ledgers.
"""

from __future__ import annotations

import hashlib
import json
import os
import platform
import subprocess
import sys
import time
from dataclasses import dataclass, field
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Callable, Mapping, Optional, Sequence


def _utc_now_iso() -> str:
    return datetime.now(timezone.utc).isoformat()


def _stable_hash(obj: object) -> str:
    raw = json.dumps(obj, sort_keys=True, separators=(",", ":"), default=str).encode("utf-8")
    return hashlib.sha256(raw).hexdigest()


def _short_hash(obj: object, length: int = 16) -> str:
    return _stable_hash(obj)[:length]


@dataclass
class RefutationCriterion:
    criterion: str
    description: str


@dataclass
class Hypothesis:
    claim: str
    test: str
    target: str
    perturbation_type: str
    refutation_criteria: list[RefutationCriterion]
    domain: str = "chaos"
    agent: str = "chaos_toolkit"
    confidence: float = 0.5
    tags: list[str] = field(default_factory=list)

    def to_artifact(self) -> dict[str, Any]:
        id_seed = {"claim": self.claim, "test": self.test, "target": self.target}
        return {
            "schema": "chaos/hypothesis/v1",
            "id": _short_hash(id_seed),
            "claim": str(self.claim),
            "test": str(self.test),
            "target": str(self.target),
            "perturbation_type": str(self.perturbation_type),
            "refutation_criteria": [
                {"criterion": str(rc.criterion), "description": str(rc.description)}
                for rc in self.refutation_criteria
            ],
            "created_at": _utc_now_iso(),
            "status": "pending",
            "confidence": float(self.confidence),
            "domain": str(self.domain),
            "agent": str(self.agent),
            "references": [],
            "tags": list(self.tags),
        }


@dataclass
class SteadyStateProbe:
    name: str
    probe_type: str  # "python", "http", "tcp", "process"
    check: Callable[[], bool]
    tolerance: Optional[dict[str, Any]] = None


@dataclass
class Perturbation:
    perturbation_type: str  # "toxiproxy", "signal", "resource", "mock", "delay"
    action: str
    params: dict[str, Any] = field(default_factory=dict)
    duration_s: float = 0.0


@dataclass
class RollbackAction:
    name: str
    action_type: str
    params: dict[str, Any] = field(default_factory=dict)

    def to_artifact(self) -> dict[str, Any]:
        return {
            "name": str(self.name),
            "type": str(self.action_type),
            "params": dict(self.params),
        }


@dataclass
class Recipe:
    hypothesis: Hypothesis
    name: str
    description: str
    target_module: str
    target_component: str
    steady_state_probes: list[SteadyStateProbe]
    perturbation: Perturbation
    refutation_checks: list[Callable[[], tuple[str, bool, str]]]  # Returns (criterion, triggered, details)
    setup: Optional[Callable[[], None]] = None
    rollback: Optional[Callable[[], None]] = None
    rollback_actions: list[RollbackAction] = field(default_factory=list)
    teardown: Optional[Callable[[], None]] = None
    tags: list[str] = field(default_factory=list)

    def to_artifact(self, hypothesis_id: str) -> dict[str, Any]:
        id_seed = {"hypothesis_id": hypothesis_id, "name": self.name}
        criteria = list(self.hypothesis.refutation_criteria)
        refutation_artifacts: list[dict[str, Any]] = []
        for idx, _check in enumerate(self.refutation_checks):
            if idx < len(criteria):
                refutation_artifacts.append(
                    {"criterion": str(criteria[idx].criterion), "check": {"type": "callable"}}
                )
            else:
                refutation_artifacts.append({"criterion": "dynamic", "check": {"type": "callable"}})
        return {
            "schema": "chaos/recipe/v1",
            "id": _short_hash(id_seed),
            "hypothesis_id": str(hypothesis_id),
            "name": str(self.name),
            "description": str(self.description),
            "target": {
                "module": str(self.target_module),
                "component": str(self.target_component),
                "version": _get_git_commit(),
            },
            "steady_state": {
                "probes": [
                    {
                        "name": str(p.name),
                        "type": str(p.probe_type),
                        "check": {"type": "callable"},
                        "tolerance": p.tolerance or {},
                    }
                    for p in self.steady_state_probes
                ],
            },
            "perturbation": {
                "type": str(self.perturbation.perturbation_type),
                "action": str(self.perturbation.action),
                "params": dict(self.perturbation.params),
                "duration_s": float(self.perturbation.duration_s),
            },
            "rollback": {
                "actions": [action.to_artifact() for action in self.rollback_actions],
            },
            "refutation_checks": refutation_artifacts,
            "created_at": _utc_now_iso(),
            "tags": list(self.tags),
        }


@dataclass
class ProbeResult:
    name: str
    passed: bool
    value: Any = None
    error: Optional[str] = None


@dataclass
class RefutationResult:
    criterion: str
    triggered: bool
    details: str = ""


@dataclass
class JournalEntry:
    recipe_id: str
    hypothesis_id: str
    context_key: str
    started_at: str
    completed_at: str
    duration_s: float
    outcome: str  # "corroborated", "falsified", "inconclusive", "error"
    steady_state_before_passed: bool
    steady_state_before_probes: list[ProbeResult]
    perturbation_applied: bool
    perturbation_type: str
    perturbation_action: str
    perturbation_params: dict[str, Any]
    perturbation_started_at: Optional[str]
    perturbation_ended_at: Optional[str]
    perturbation_error: Optional[str]
    rollback_attempted: bool
    rollback_actions: list[RollbackAction]
    rollback_error: Optional[str]
    steady_state_after_passed: bool
    steady_state_after_probes: list[ProbeResult]
    refutation_results: list[RefutationResult]
    falsification_reason: Optional[str] = None
    logs: dict[str, str] = field(default_factory=dict)
    metrics: dict[str, Any] = field(default_factory=dict)
    notes: str = ""

    def to_artifact(self) -> dict[str, Any]:
        id_seed = {
            "recipe_id": self.recipe_id,
            "started_at": self.started_at,
        }
        return {
            "schema": "chaos/journal/v1",
            "id": _short_hash(id_seed),
            "recipe_id": str(self.recipe_id),
            "hypothesis_id": str(self.hypothesis_id),
            "context_key": str(self.context_key),
            "started_at": str(self.started_at),
            "completed_at": str(self.completed_at),
            "duration_s": float(self.duration_s),
            "outcome": str(self.outcome),
            "steady_state_before": {
                "passed": bool(self.steady_state_before_passed),
                "probes": [
                    {
                        "name": str(p.name),
                        "passed": bool(p.passed),
                        "value": p.value,
                        "error": p.error,
                    }
                    for p in self.steady_state_before_probes
                ],
                "timestamp": self.started_at,
            },
            "perturbation_applied": {
                "applied": bool(self.perturbation_applied),
                "type": str(self.perturbation_type),
                "action": str(self.perturbation_action),
                "params": dict(self.perturbation_params),
                "started_at": self.perturbation_started_at,
                "ended_at": self.perturbation_ended_at,
                "error": self.perturbation_error,
            },
            "rollback": {
                "attempted": bool(self.rollback_attempted),
                "actions": [action.to_artifact() for action in self.rollback_actions],
                "error": self.rollback_error,
            },
            "steady_state_after": {
                "passed": bool(self.steady_state_after_passed),
                "probes": [
                    {
                        "name": str(p.name),
                        "passed": bool(p.passed),
                        "value": p.value,
                        "error": p.error,
                    }
                    for p in self.steady_state_after_probes
                ],
                "timestamp": self.completed_at,
            },
            "refutation_checks": [
                {
                    "criterion": str(r.criterion),
                    "triggered": bool(r.triggered),
                    "details": str(r.details),
                }
                for r in self.refutation_results
            ],
            "falsification_reason": self.falsification_reason,
            "logs": dict(self.logs),
            "metrics": dict(self.metrics),
            "environment": {
                "hostname": platform.node(),
                "python_version": platform.python_version(),
                "git_commit": _get_git_commit(),
            },
            "agent": "chaos_toolkit_runner",
            "notes": str(self.notes),
        }


def _get_git_commit() -> str:
    try:
        result = subprocess.run(
            ["git", "rev-parse", "HEAD"],
            capture_output=True,
            text=True,
            timeout=5,
        )
        if result.returncode == 0:
            return result.stdout.strip()[:12]
    except Exception:
        pass
    return "unknown"


class ChaosExperimentRunner:
    def __init__(
        self,
        output_dir: Path,
        *,
        verbose: bool = False,
        context_key: Optional[str] = None,
    ) -> None:
        self._output_dir = Path(output_dir).resolve()
        self._output_dir.mkdir(parents=True, exist_ok=True)
        self._verbose = bool(verbose)
        self._context_key = str(context_key) if context_key else f"git:{_get_git_commit()}"

    def _log(self, msg: str) -> None:
        if self._verbose:
            print(f"[chaos] {msg}", file=sys.stderr)

    def _run_probes(self, probes: Sequence[SteadyStateProbe]) -> tuple[bool, list[ProbeResult]]:
        results: list[ProbeResult] = []
        all_passed = True
        for probe in probes:
            try:
                passed = probe.check()
                results.append(ProbeResult(name=probe.name, passed=bool(passed)))
                if not passed:
                    all_passed = False
            except Exception as exc:
                results.append(ProbeResult(name=probe.name, passed=False, error=str(exc)[:200]))
                all_passed = False
        return all_passed, results

    def _run_refutation_checks(
        self, checks: Sequence[Callable[[], tuple[str, bool, str]]]
    ) -> list[RefutationResult]:
        results: list[RefutationResult] = []
        for check in checks:
            try:
                criterion, triggered, details = check()
                results.append(RefutationResult(criterion=str(criterion), triggered=bool(triggered), details=str(details)))
            except Exception as exc:
                results.append(RefutationResult(criterion="check_error", triggered=True, details=str(exc)[:200]))
        return results

    def run(
        self,
        recipe: Recipe,
        *,
        apply_perturbation: Callable[[], None],
    ) -> JournalEntry:
        hypothesis_artifact = recipe.hypothesis.to_artifact()
        hypothesis_id = str(hypothesis_artifact["id"])
        recipe_artifact = recipe.to_artifact(hypothesis_id)
        recipe_id = str(recipe_artifact["id"])

        self._log(f"Running experiment: {recipe.name}")
        self._log(f"  Hypothesis ID: {hypothesis_id}")
        self._log(f"  Recipe ID: {recipe_id}")

        started_at = _utc_now_iso()
        t0 = time.monotonic()

        if recipe.setup:
            self._log("  Running setup...")
            try:
                recipe.setup()
            except Exception as exc:
                self._log(f"  Setup failed: {exc}")
                raise

        self._log("  Checking steady state (before)...")
        ss_before_passed, ss_before_probes = self._run_probes(recipe.steady_state_probes)
        self._log(f"  Steady state before: {'PASS' if ss_before_passed else 'FAIL'}")

        perturbation_applied = False
        perturbation_started_at: Optional[str] = None
        perturbation_ended_at: Optional[str] = None
        perturbation_error: Optional[str] = None

        if ss_before_passed:
            self._log(f"  Applying perturbation: {recipe.perturbation.action}...")
            perturbation_started_at = _utc_now_iso()
            try:
                apply_perturbation()
                perturbation_applied = True
                self._log("  Perturbation applied successfully")
            except Exception as exc:
                perturbation_error = str(exc)[:200]
                self._log(f"  Perturbation failed: {perturbation_error}")
            finally:
                perturbation_ended_at = _utc_now_iso()

        self._log("  Running refutation checks...")
        refutation_results = self._run_refutation_checks(recipe.refutation_checks)
        any_refutation_triggered = any(r.triggered for r in refutation_results)

        rollback_attempted = False
        rollback_error: Optional[str] = None
        if recipe.rollback is not None or recipe.rollback_actions:
            rollback_attempted = True
            self._log("  Running rollback...")
            if recipe.rollback is not None:
                try:
                    recipe.rollback()
                except Exception as exc:
                    rollback_error = str(exc)[:200]
                    self._log(f"  Rollback failed: {rollback_error}")

        self._log("  Checking steady state (after)...")
        ss_after_passed, ss_after_probes = self._run_probes(recipe.steady_state_probes)
        self._log(f"  Steady state after: {'PASS' if ss_after_passed else 'FAIL'}")

        if recipe.teardown:
            self._log("  Running teardown...")
            try:
                recipe.teardown()
            except Exception as exc:
                self._log(f"  Teardown failed: {exc}")

        completed_at = _utc_now_iso()
        duration_s = time.monotonic() - t0

        if not ss_before_passed:
            outcome = "error"
            falsification_reason = "steady_state_before_failed"
        elif not perturbation_applied:
            outcome = "error"
            falsification_reason = f"perturbation_failed: {perturbation_error}"
        elif any_refutation_triggered:
            outcome = "falsified"
            triggered = [r for r in refutation_results if r.triggered]
            falsification_reason = "; ".join(f"{r.criterion}: {r.details}" for r in triggered)
        elif rollback_attempted and rollback_error is not None:
            outcome = "error"
            falsification_reason = f"rollback_failed: {rollback_error}"
        elif not ss_after_passed:
            outcome = "inconclusive"
            falsification_reason = "steady_state_after_failed"
        else:
            outcome = "corroborated"
            falsification_reason = None

        self._log(f"  Outcome: {outcome}")

        journal = JournalEntry(
            recipe_id=recipe_id,
            hypothesis_id=hypothesis_id,
            context_key=self._context_key,
            started_at=started_at,
            completed_at=completed_at,
            duration_s=duration_s,
            outcome=outcome,
            steady_state_before_passed=ss_before_passed,
            steady_state_before_probes=ss_before_probes,
            perturbation_applied=perturbation_applied,
            perturbation_type=recipe.perturbation.perturbation_type,
            perturbation_action=recipe.perturbation.action,
            perturbation_params=dict(recipe.perturbation.params),
            perturbation_started_at=perturbation_started_at,
            perturbation_ended_at=perturbation_ended_at,
            perturbation_error=perturbation_error,
            rollback_attempted=rollback_attempted,
            rollback_actions=list(recipe.rollback_actions),
            rollback_error=rollback_error,
            steady_state_after_passed=ss_after_passed,
            steady_state_after_probes=ss_after_probes,
            refutation_results=refutation_results,
            falsification_reason=falsification_reason,
        )

        self._save_artifacts(hypothesis_artifact, recipe_artifact, journal.to_artifact())

        return journal

    def _save_artifacts(
        self,
        hypothesis: dict[str, Any],
        recipe: dict[str, Any],
        journal: dict[str, Any],
    ) -> None:
        timestamp = datetime.now(timezone.utc).strftime("%Y%m%d_%H%M%S")
        run_dir = self._output_dir / f"run_{timestamp}_{journal['id'][:8]}"
        run_dir.mkdir(parents=True, exist_ok=True)

        (run_dir / "hypothesis.json").write_text(
            json.dumps(hypothesis, indent=2, sort_keys=True) + "\n",
            encoding="utf-8",
        )
        (run_dir / "recipe.json").write_text(
            json.dumps(recipe, indent=2, sort_keys=True) + "\n",
            encoding="utf-8",
        )
        (run_dir / "journal.json").write_text(
            json.dumps(journal, indent=2, sort_keys=True) + "\n",
            encoding="utf-8",
        )

        self._log(f"  Artifacts saved to: {run_dir}")
