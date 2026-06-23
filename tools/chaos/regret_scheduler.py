"""Regret-aware campaign state and experiment selection for chaos runs.

This module sits above the single-experiment runner. It aggregates prior journals,
estimates which experiments are likely to yield useful falsifiers, and penalizes
high-cost, high-blast, or repeatedly corroborated experiments.
"""

from __future__ import annotations

import json
import math
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Iterable, Optional

import yaml


class ChaosCampaignConfigError(ValueError):
    pass


def _utc_now_iso() -> str:
    return datetime.now(timezone.utc).isoformat()


def _clamp(value: float, lo: float = 0.0, hi: float = 1.0) -> float:
    return max(lo, min(hi, float(value)))


def _safe_float(value: object, default: float) -> float:
    try:
        return float(value)
    except Exception:
        return float(default)


def _safe_int(value: object, default: int) -> int:
    try:
        return int(value)
    except Exception:
        return int(default)


def _safe_bool(value: object, default: bool) -> bool:
    if isinstance(value, bool):
        return value
    if isinstance(value, (int, float)) and value in (0, 1):
        return bool(value)
    if isinstance(value, str):
        lowered = value.strip().lower()
        if lowered in {"1", "true", "yes"}:
            return True
        if lowered in {"0", "false", "no"}:
            return False
    return bool(default)


_ALLOWED_ORACLE_KINDS = frozenset({"steady_state", "slo", "ux", "recovery"})
_ALLOWED_SCENARIO_COMPOSITIONS = frozenset({"serial", "parallel", "intermittent", "delayed", "bursty", "correlated"})


@dataclass(frozen=True)
class OracleMetadata:
    kind: str
    source: str
    metrics: tuple[str, ...]
    stop_conditions: tuple[str, ...]

    def to_artifact(self) -> dict[str, Any]:
        return {
            "kind": self.kind,
            "source": self.source,
            "metrics": list(self.metrics),
            "stop_conditions": list(self.stop_conditions),
        }


@dataclass(frozen=True)
class ScenarioMetadata:
    faults: tuple[str, ...]
    state_axes: tuple[str, ...]
    composition: str
    scope: str

    def to_artifact(self) -> dict[str, Any]:
        return {
            "faults": list(self.faults),
            "state_axes": list(self.state_axes),
            "composition": self.composition,
            "scope": self.scope,
        }


@dataclass(frozen=True)
class SafetyBudget:
    max_blast_radius: float
    max_duration_s: float
    max_error_budget_burn_rate: float
    production_slice_percent: float
    requires_rollback: bool
    stop_conditions: tuple[str, ...]

    def to_artifact(self) -> dict[str, Any]:
        return {
            "max_blast_radius": self.max_blast_radius,
            "max_duration_s": self.max_duration_s,
            "max_error_budget_burn_rate": self.max_error_budget_burn_rate,
            "production_slice_percent": self.production_slice_percent,
            "requires_rollback": self.requires_rollback,
            "stop_conditions": list(self.stop_conditions),
        }


@dataclass(frozen=True)
class ExperimentMetadata:
    name: str
    target: str
    perturbation_type: str
    tags: tuple[str, ...]
    severity: float
    blast_radius: float
    cost_estimate_s: float
    oracle: OracleMetadata
    scenario: ScenarioMetadata
    safety_budget: SafetyBudget


@dataclass
class ContextStats:
    total_runs: int = 0
    corroborated: int = 0
    falsified: int = 0
    inconclusive: int = 0
    harness_errors: int = 0


@dataclass
class ExperimentStats:
    total_runs: int = 0
    corroborated: int = 0
    falsified: int = 0
    inconclusive: int = 0
    harness_errors: int = 0
    total_duration_s: float = 0.0
    contexts: dict[str, ContextStats] = None  # type: ignore[assignment]
    failure_signatures: set[str] = None  # type: ignore[assignment]
    last_outcome: Optional[str] = None
    last_completed_at: Optional[str] = None

    def __post_init__(self) -> None:
        if self.contexts is None:
            self.contexts = {}
        if self.failure_signatures is None:
            self.failure_signatures = set()

    @property
    def mean_duration_s(self) -> float:
        if self.total_runs <= 0:
            return 0.0
        return float(self.total_duration_s) / float(self.total_runs)


def _iter_experiment_docs(experiments_dir: Path) -> Iterable[tuple[Path, dict[str, Any]]]:
    resolved_dir = Path(experiments_dir).resolve()
    if not resolved_dir.is_dir():
        raise ChaosCampaignConfigError(f"{resolved_dir}: experiments directory is missing")
    paths = sorted(resolved_dir.glob("*.yaml"))
    if not paths:
        raise ChaosCampaignConfigError(f"{resolved_dir}: no experiment metadata files found")
    for path in paths:
        data = yaml.safe_load(path.read_text(encoding="utf-8")) or {}
        if not isinstance(data, dict):
            raise ChaosCampaignConfigError(f"{path}: expected top-level mapping")
        yield path, data


def _infer_severity(doc: dict[str, Any]) -> float:
    tags = {str(tag) for tag in doc.get("tags") or []}
    perturbation_type = str((doc.get("hypothesis") or {}).get("perturbation_type", "")).strip()
    if "high_risk" in tags:
        return 1.0
    if perturbation_type == "network_fault":
        return 0.85
    if perturbation_type == "process_fault":
        return 0.75
    if perturbation_type == "resource_exhaustion":
        return 0.70
    if perturbation_type == "http_fault":
        return 0.55
    if perturbation_type == "timing_fault":
        return 0.60
    return 0.50


def _infer_blast_radius(doc: dict[str, Any]) -> float:
    perturbation = doc.get("perturbation") or {}
    perturbation_type = str(perturbation.get("type", "")).strip()
    if perturbation_type == "toxiproxy":
        return 0.35
    if perturbation_type == "signal":
        return 0.25
    if perturbation_type == "resource":
        return 0.22
    if perturbation_type == "mock":
        return 0.18
    if perturbation_type == "http":
        return 0.12
    return 0.20


def _infer_cost_estimate_s(doc: dict[str, Any]) -> float:
    perturbation = doc.get("perturbation") or {}
    duration = _safe_float(perturbation.get("duration_s"), 0.0)
    tags = {str(tag) for tag in doc.get("tags") or []}
    if duration > 0:
        return max(1.0, duration)
    if "high_risk" in tags:
        return 2.5
    if "network_fault" in tags:
        return 2.0
    if "resource_exhaustion" in tags:
        return 3.0
    return 1.5


def _require_non_empty_string(value: object, *, source_path: Path, field_name: str) -> str:
    if isinstance(value, str) and value.strip():
        return value.strip()
    raise ChaosCampaignConfigError(f"{source_path}: missing required {field_name}")


def _read_optional_mapping(value: object, *, source_path: Path, field_name: str) -> dict[str, Any]:
    if value is None:
        return {}
    if isinstance(value, dict):
        return value
    raise ChaosCampaignConfigError(f"{source_path}: {field_name} must be a mapping")


def _read_string_tuple(value: object, *, source_path: Path, field_name: str) -> tuple[str, ...]:
    if value is None:
        return ()
    if not isinstance(value, list):
        raise ChaosCampaignConfigError(f"{source_path}: {field_name} must be a list")
    normalized: list[str] = []
    for idx, item in enumerate(value):
        if not isinstance(item, str) or not item.strip():
            raise ChaosCampaignConfigError(f"{source_path}: {field_name}[{idx}] must be a non-empty string")
        normalized.append(item.strip())
    return tuple(normalized)


def _read_choice(
    value: object,
    *,
    source_path: Path,
    field_name: str,
    default: str,
    allowed: frozenset[str],
) -> str:
    if value is None:
        return default
    if isinstance(value, str) and not value.strip():
        return default
    candidate = _require_non_empty_string(value, source_path=source_path, field_name=field_name)
    if candidate in allowed:
        return candidate
    allowed_values = ", ".join(sorted(allowed))
    raise ChaosCampaignConfigError(f"{source_path}: {field_name} must be one of {allowed_values}")


def _build_oracle_metadata(path: Path, doc: dict[str, Any]) -> OracleMetadata:
    oracle = _read_optional_mapping(doc.get("oracle"), source_path=path, field_name="oracle")
    source_value = oracle.get("source")
    source = str(source_value).strip() if isinstance(source_value, str) and source_value.strip() else "steady_state_probes"
    return OracleMetadata(
        kind=_read_choice(
            oracle.get("kind"),
            source_path=path,
            field_name="oracle.kind",
            default="steady_state",
            allowed=_ALLOWED_ORACLE_KINDS,
        ),
        source=source,
        metrics=_read_string_tuple(oracle.get("metrics"), source_path=path, field_name="oracle.metrics"),
        stop_conditions=_read_string_tuple(
            oracle.get("stop_conditions"),
            source_path=path,
            field_name="oracle.stop_conditions",
        ),
    )


def _build_scenario_metadata(path: Path, doc: dict[str, Any], perturbation: dict[str, Any]) -> ScenarioMetadata:
    scenario = _read_optional_mapping(doc.get("scenario"), source_path=path, field_name="scenario")
    default_fault = str(perturbation.get("action", "")).strip() or str(perturbation.get("type", "")).strip()
    faults = _read_string_tuple(scenario.get("faults"), source_path=path, field_name="scenario.faults")
    scope_value = scenario.get("scope")
    scope = str(scope_value).strip() if isinstance(scope_value, str) and scope_value.strip() else "single_component"
    return ScenarioMetadata(
        faults=faults or (default_fault,),
        state_axes=_read_string_tuple(scenario.get("state_axes"), source_path=path, field_name="scenario.state_axes"),
        composition=_read_choice(
            scenario.get("composition"),
            source_path=path,
            field_name="scenario.composition",
            default="serial",
            allowed=_ALLOWED_SCENARIO_COMPOSITIONS,
        ),
        scope=scope,
    )


def _build_safety_budget(
    path: Path,
    doc: dict[str, Any],
    *,
    default_blast_radius: float,
    default_cost_estimate_s: float,
) -> SafetyBudget:
    safety_budget = _read_optional_mapping(doc.get("safety_budget"), source_path=path, field_name="safety_budget")
    rollback = _read_optional_mapping(doc.get("rollback"), source_path=path, field_name="rollback")
    rollback_actions = rollback.get("actions")
    if rollback_actions is None:
        rollback_action_count = 0
    elif isinstance(rollback_actions, list):
        rollback_action_count = len(rollback_actions)
    else:
        raise ChaosCampaignConfigError(f"{path}: rollback.actions must be a list")
    requires_rollback = _safe_bool(safety_budget.get("requires_rollback"), False)
    if requires_rollback and rollback_action_count <= 0:
        raise ChaosCampaignConfigError(f"{path}: safety_budget.requires_rollback requires rollback.actions")
    return SafetyBudget(
        max_blast_radius=_clamp(_safe_float(safety_budget.get("max_blast_radius"), default_blast_radius)),
        max_duration_s=max(0.1, _safe_float(safety_budget.get("max_duration_s"), max(1.0, default_cost_estimate_s * 2.0))),
        max_error_budget_burn_rate=max(0.1, _safe_float(safety_budget.get("max_error_budget_burn_rate"), 1.0)),
        production_slice_percent=max(0.0, min(100.0, _safe_float(safety_budget.get("production_slice_percent"), 0.0))),
        requires_rollback=requires_rollback,
        stop_conditions=_read_string_tuple(
            safety_budget.get("stop_conditions"),
            source_path=path,
            field_name="safety_budget.stop_conditions",
        ),
    )


def _build_experiment_metadata(path: Path, doc: dict[str, Any]) -> ExperimentMetadata:
    hypothesis = doc.get("hypothesis")
    if not isinstance(hypothesis, dict):
        raise ChaosCampaignConfigError(f"{path}: missing required hypothesis mapping")
    perturbation = doc.get("perturbation")
    if not isinstance(perturbation, dict):
        raise ChaosCampaignConfigError(f"{path}: missing required perturbation mapping")
    target = _require_non_empty_string(
        hypothesis.get("target"),
        source_path=path,
        field_name="hypothesis.target",
    )
    perturbation_type = _require_non_empty_string(
        hypothesis.get("perturbation_type"),
        source_path=path,
        field_name="hypothesis.perturbation_type",
    )
    _require_non_empty_string(
        perturbation.get("type"),
        source_path=path,
        field_name="perturbation.type",
    )
    campaign = _read_optional_mapping(doc.get("campaign"), source_path=path, field_name="campaign")
    blast_radius = _clamp(_safe_float(campaign.get("blast_radius"), _infer_blast_radius(doc)))
    cost_estimate_s = max(0.1, _safe_float(campaign.get("cost_estimate_s"), _infer_cost_estimate_s(doc)))
    return ExperimentMetadata(
        name=path.stem,
        target=target,
        perturbation_type=perturbation_type,
        tags=_read_string_tuple(doc.get("tags"), source_path=path, field_name="tags"),
        severity=_clamp(_safe_float(campaign.get("severity"), _infer_severity(doc))),
        blast_radius=blast_radius,
        cost_estimate_s=cost_estimate_s,
        oracle=_build_oracle_metadata(path, doc),
        scenario=_build_scenario_metadata(path, doc, perturbation),
        safety_budget=_build_safety_budget(
            path,
            doc,
            default_blast_radius=blast_radius,
            default_cost_estimate_s=cost_estimate_s,
        ),
    )


def load_experiment_metadata(experiments_dir: Path) -> dict[str, ExperimentMetadata]:
    metadata: dict[str, ExperimentMetadata] = {}
    for path, doc in _iter_experiment_docs(experiments_dir):
        metadata[path.stem] = _build_experiment_metadata(path, doc)
    return metadata


def _load_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def _infer_context_key(journal: dict[str, Any]) -> str:
    context_key = journal.get("context_key")
    if isinstance(context_key, str) and context_key.strip():
        return context_key.strip()
    env = journal.get("environment") or {}
    git_commit = str(env.get("git_commit", "unknown")).strip() or "unknown"
    return f"git:{git_commit}"


def _is_harness_error(journal: dict[str, Any]) -> bool:
    if str(journal.get("outcome", "")) == "error":
        return True
    perturb = journal.get("perturbation_applied") or {}
    rollback = journal.get("rollback") or {}
    return bool(perturb.get("error")) or bool(rollback.get("error"))


def aggregate_campaign_stats(runs_root: Path) -> dict[str, ExperimentStats]:
    stats: dict[str, ExperimentStats] = {}
    runs_root = Path(runs_root)
    if not runs_root.exists():
        return stats

    for experiment_dir in sorted(runs_root.iterdir()):
        if not experiment_dir.is_dir():
            continue
        experiment_name = experiment_dir.name
        exp_stats = stats.setdefault(experiment_name, ExperimentStats())
        for run_dir in sorted(experiment_dir.glob("run_*")):
            journal_path = run_dir / "journal.json"
            if not journal_path.exists():
                continue
            journal = _load_json(journal_path)
            context_key = _infer_context_key(journal)
            ctx = exp_stats.contexts.setdefault(context_key, ContextStats())
            outcome = str(journal.get("outcome", "error"))
            duration_s = _safe_float(journal.get("duration_s"), 0.0)

            exp_stats.total_runs += 1
            exp_stats.total_duration_s += duration_s
            exp_stats.last_outcome = outcome
            exp_stats.last_completed_at = str(journal.get("completed_at", "")) or exp_stats.last_completed_at
            ctx.total_runs += 1

            if outcome == "corroborated":
                exp_stats.corroborated += 1
                ctx.corroborated += 1
            elif outcome == "falsified":
                exp_stats.falsified += 1
                ctx.falsified += 1
                reason = str(journal.get("falsification_reason", "")).strip()
                if reason:
                    exp_stats.failure_signatures.add(reason)
            elif outcome == "inconclusive":
                exp_stats.inconclusive += 1
                ctx.inconclusive += 1
            else:
                exp_stats.harness_errors += 1
                ctx.harness_errors += 1

            if _is_harness_error(journal) and outcome != "error":
                exp_stats.harness_errors += 1
                ctx.harness_errors += 1

    return stats


def _beta_ucb(successes: int, failures: int) -> float:
    total = max(0, successes) + max(0, failures)
    alpha = 1.0 + max(0, successes)
    beta = 1.0 + max(0, failures)
    mean = alpha / (alpha + beta)
    explore = math.sqrt((2.0 * math.log(total + 2.0)) / (total + 1.0))
    return _clamp(mean + explore)


def _novelty_score(ctx: ContextStats) -> float:
    if ctx.total_runs <= 0:
        return 1.0
    if ctx.falsified > 0:
        return 0.10
    score = 1.0 / (1.0 + float(ctx.corroborated) + 0.5 * float(ctx.inconclusive) + 0.75 * float(ctx.harness_errors))
    return _clamp(score, 0.05, 1.0)


def _duration_penalty(mean_duration_s: float, fallback_cost_s: float) -> float:
    cost = mean_duration_s if mean_duration_s > 0 else fallback_cost_s
    return _clamp(cost / 30.0)


def _repeat_penalty(ctx: ContextStats) -> float:
    if ctx.falsified > 0:
        return 0.50
    if ctx.corroborated <= 1:
        return 0.0
    return min(0.40, 0.10 * float(ctx.corroborated - 1))


def build_campaign_state(
    *,
    runs_root: Path,
    experiments_dir: Path,
    context_key: Optional[str] = None,
    max_blast_radius: Optional[float] = None,
) -> tuple[dict[str, Any], dict[str, Any]]:
    metadata = load_experiment_metadata(experiments_dir)
    stats = aggregate_campaign_stats(runs_root)
    current_context_key = str(context_key).strip() if isinstance(context_key, str) and context_key.strip() else "git:unknown"

    candidates: list[dict[str, Any]] = []
    for name, meta in sorted(metadata.items()):
        exp_stats = stats.get(name, ExperimentStats())
        ctx = exp_stats.contexts.get(current_context_key, ContextStats())
        falsify_ucb = _beta_ucb(
            successes=exp_stats.falsified,
            failures=exp_stats.corroborated + exp_stats.inconclusive + exp_stats.harness_errors,
        )
        harness_ucb = _beta_ucb(
            successes=exp_stats.harness_errors,
            failures=max(0, exp_stats.total_runs - exp_stats.harness_errors),
        )
        novelty = _novelty_score(ctx)
        repeat_penalty = _repeat_penalty(ctx)
        duration_penalty = _duration_penalty(exp_stats.mean_duration_s, meta.cost_estimate_s)
        within_safety_budget = meta.blast_radius <= meta.safety_budget.max_blast_radius
        within_requested_blast_radius = max_blast_radius is None or meta.blast_radius <= float(max_blast_radius)
        feasible = within_safety_budget and within_requested_blast_radius
        score = (
            meta.severity * novelty * falsify_ucb
            - 0.35 * harness_ucb
            - 0.15 * meta.blast_radius
            - 0.10 * duration_penalty
            - repeat_penalty
        )
        if not feasible:
            score = -1_000_000.0
        candidates.append(
            {
                "name": name,
                "target": meta.target,
                "perturbation_type": meta.perturbation_type,
                "tags": list(meta.tags),
                "severity": meta.severity,
                "blast_radius": meta.blast_radius,
                "cost_estimate_s": meta.cost_estimate_s,
                "oracle": meta.oracle.to_artifact(),
                "scenario": meta.scenario.to_artifact(),
                "safety_budget": meta.safety_budget.to_artifact(),
                "stats": {
                    "total_runs": exp_stats.total_runs,
                    "corroborated": exp_stats.corroborated,
                    "falsified": exp_stats.falsified,
                    "inconclusive": exp_stats.inconclusive,
                    "harness_errors": exp_stats.harness_errors,
                    "mean_duration_s": exp_stats.mean_duration_s,
                    "failure_signature_count": len(exp_stats.failure_signatures),
                    "last_outcome": exp_stats.last_outcome,
                    "last_completed_at": exp_stats.last_completed_at,
                },
                "current_context": {
                    "context_key": current_context_key,
                    "total_runs": ctx.total_runs,
                    "corroborated": ctx.corroborated,
                    "falsified": ctx.falsified,
                    "inconclusive": ctx.inconclusive,
                    "harness_errors": ctx.harness_errors,
                },
                "priority": {
                    "score": score,
                    "novelty": novelty,
                    "falsify_ucb": falsify_ucb,
                    "harness_error_ucb": harness_ucb,
                    "duration_penalty": duration_penalty,
                    "repeat_penalty": repeat_penalty,
                    "within_safety_budget": within_safety_budget,
                    "feasible": feasible,
                },
            }
        )

    candidates.sort(key=lambda item: (-float(item["priority"]["score"]), item["name"]))
    feasible_scores = [float(candidate["priority"]["score"]) for candidate in candidates if bool(candidate["priority"]["feasible"])]
    best_score = max(feasible_scores) if feasible_scores else None
    for candidate in candidates:
        score = float(candidate["priority"]["score"])
        candidate["priority"]["regret_vs_best"] = 0.0 if best_score is None else max(0.0, best_score - score)

    selected = next((candidate["name"] for candidate in candidates if bool(candidate["priority"]["feasible"])), None)

    campaign_state = {
        "schema": "chaos/campaign_state/v1",
        "generated_at": _utc_now_iso(),
        "runs_root": str(Path(runs_root).resolve()),
        "experiments_dir": str(Path(experiments_dir).resolve()),
        "context_key": current_context_key,
        "selected_experiment": selected,
        "total_experiments": len(candidates),
        "total_runs": sum(int(candidate["stats"]["total_runs"]) for candidate in candidates),
        "experiments": candidates,
    }
    regret_snapshot = {
        "schema": "chaos/regret_snapshot/v1",
        "generated_at": _utc_now_iso(),
        "context_key": current_context_key,
        "selected_experiment": selected,
        "candidate_priorities": [
            {
                "name": candidate["name"],
                "score": candidate["priority"]["score"],
                "regret_vs_best": candidate["priority"]["regret_vs_best"],
                "feasible": candidate["priority"]["feasible"],
            }
            for candidate in candidates
        ],
    }
    return campaign_state, regret_snapshot


def write_json_artifact(path: Path, payload: dict[str, Any]) -> None:
    Path(path).write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
