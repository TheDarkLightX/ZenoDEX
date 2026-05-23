"""ZenoOps metrics primitives for operator status output."""

from __future__ import annotations

import re
from dataclasses import dataclass, field
from typing import Any, Iterable, Mapping

METRICS_SNAPSHOT_SCHEMA_V0 = "zenodex/zeno_ops_metrics_snapshot/v0"
PROM_METRIC_RE = re.compile(r"^[a-zA-Z_:][a-zA-Z0-9_:]*$")


@dataclass(frozen=True)
class MetricSample:
    name: str
    value: int | float
    labels: Mapping[str, str] = field(default_factory=dict)
    description: str = ""
    unit: str = ""

    def __post_init__(self) -> None:
        if not PROM_METRIC_RE.match(self.name):
            raise ValueError(f"invalid metric name: {self.name}")
        if isinstance(self.value, bool) or not isinstance(self.value, (int, float)):
            raise TypeError("metric value must be int or float")
        for key, value in self.labels.items():
            if not PROM_METRIC_RE.match(str(key)):
                raise ValueError(f"invalid label name: {key}")
            if not isinstance(value, str):
                raise TypeError("metric label values must be strings")

    def public_dict(self) -> dict[str, Any]:
        return {
            "name": self.name,
            "value": self.value,
            "labels": dict(sorted(self.labels.items())),
            "description": self.description,
            "unit": self.unit,
        }


def build_metrics_snapshot_v0(*, samples: Iterable[MetricSample], source: str = "local") -> dict[str, Any]:
    sample_list = [sample.public_dict() for sample in samples]
    alerts = evaluate_alerts_v0(sample_list)
    return {
        "schema": METRICS_SNAPSHOT_SCHEMA_V0,
        "ok": not alerts,
        "source": source,
        "sample_count": len(sample_list),
        "samples": sample_list,
        "alerts": alerts,
    }


def render_prometheus_text_v0(samples: Iterable[MetricSample]) -> str:
    lines: list[str] = []
    for sample in samples:
        if sample.description:
            lines.append(f"# HELP {sample.name} {_escape_help(sample.description)}")
        if sample.unit:
            lines.append(f"# UNIT {sample.name} {sample.unit}")
        labels = _render_labels(sample.labels)
        lines.append(f"{sample.name}{labels} {sample.value}")
    return "\n".join(lines) + "\n"


def build_minimal_operator_samples_v0(
    *,
    ledger_height: int = 0,
    peer_count: int = 0,
    gossip_rejection_count: int = 0,
    slashing_evidence_count: int = 0,
    proof_metadata_mismatch_count: int = 0,
    key_admission_rejection_count: int = 0,
) -> list[MetricSample]:
    return [
        MetricSample("zeno_ledger_height", ledger_height, description="Current local ledger height", unit="blocks"),
        MetricSample("zeno_peer_count", peer_count, description="Current admitted peer count", unit="peers"),
        MetricSample("zeno_gossip_rejections_total", gossip_rejection_count, description="Gossip rejection count", unit="events"),
        MetricSample("zeno_slashing_evidence_total", slashing_evidence_count, description="Slashing evidence count", unit="events"),
        MetricSample("zeno_proof_metadata_mismatch_total", proof_metadata_mismatch_count, description="Proof metadata mismatch count", unit="events"),
        MetricSample("zeno_key_admission_rejections_total", key_admission_rejection_count, description="Key admission rejection count", unit="events"),
    ]


def samples_from_chaos_report_v0(report: Mapping[str, Any]) -> list[MetricSample]:
    samples: list[MetricSample] = []
    for scenario in report.get("scenarios", []):
        if not isinstance(scenario, Mapping):
            continue
        scenario_name = str(scenario.get("scenario", "unknown"))
        model_report = scenario.get("model_report", {})
        if not isinstance(model_report, Mapping):
            continue
        for raw_key, raw_value in dict(model_report.get("metrics", {})).items():
            key = str(raw_key)
            value = raw_value if isinstance(raw_value, (int, float)) and not isinstance(raw_value, bool) else 0
            metric, reason = _metric_from_chaos_key(key)
            labels = {"scenario": scenario_name}
            if reason:
                labels["reason"] = reason
            samples.append(MetricSample(metric, value, labels=labels, description=f"Chaos harness metric {key}"))
        for node_id, node in dict(model_report.get("nodes", {})).items():
            if isinstance(node, Mapping):
                samples.append(
                    MetricSample(
                        "zeno_ledger_height",
                        int(node.get("height", 0)),
                        labels={"scenario": scenario_name, "node": str(node_id)},
                    )
                )
                samples.append(
                    MetricSample(
                        "zeno_peer_count",
                        int(node.get("peer_count", 0)),
                        labels={"scenario": scenario_name, "node": str(node_id)},
                    )
                )
    return samples


def evaluate_alerts_v0(sample_dicts: Iterable[Mapping[str, Any]]) -> list[dict[str, Any]]:
    alerts: list[dict[str, Any]] = []
    for sample in sample_dicts:
        name = sample.get("name")
        value = sample.get("value")
        labels = sample.get("labels", {})
        if name == "zeno_peer_count" and value == 0:
            alerts.append({"id": "peer_count_zero", "severity": "warning", "labels": labels})
        if name == "zeno_proof_metadata_mismatch_total" and isinstance(value, (int, float)) and value > 0:
            alerts.append({"id": "proof_metadata_mismatch", "severity": "critical", "labels": labels})
        if name == "zeno_key_admission_rejections_total" and isinstance(value, (int, float)) and value > 0:
            alerts.append({"id": "key_admission_rejection", "severity": "warning", "labels": labels})
        if str(name).endswith("_rejections_total") and isinstance(value, (int, float)) and value > 0:
            alerts.append({"id": "rejection_count_nonzero", "severity": "info", "metric": name, "labels": labels})
    return alerts


def _metric_from_chaos_key(key: str) -> tuple[str, str]:
    if ":" not in key:
        return f"zeno_chaos_{key}_total", ""
    prefix, reason = key.split(":", 1)
    return f"zeno_chaos_{prefix}_total", reason


def _render_labels(labels: Mapping[str, str]) -> str:
    if not labels:
        return ""
    parts = [f'{key}="{_escape_label(value)}"' for key, value in sorted(labels.items())]
    return "{" + ",".join(parts) + "}"


def _escape_label(value: str) -> str:
    return value.replace("\\", "\\\\").replace("\n", "\\n").replace('"', '\\"')


def _escape_help(value: str) -> str:
    return value.replace("\\", "\\\\").replace("\n", "\\n")
