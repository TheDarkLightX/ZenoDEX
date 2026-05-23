from __future__ import annotations

import json

from src.integration.metrics_v0 import (
    MetricSample,
    build_metrics_snapshot_v0,
    build_minimal_operator_samples_v0,
    render_prometheus_text_v0,
    samples_from_chaos_report_v0,
)
from tools import zeno_ops_status
from tools.zeno_ledger_chaos_harness import run_chaos_harness


def test_metrics_snapshot_emits_alerts_for_zero_peers_and_mismatch() -> None:
    samples = build_minimal_operator_samples_v0(
        ledger_height=12,
        peer_count=0,
        proof_metadata_mismatch_count=1,
    )
    snapshot = build_metrics_snapshot_v0(samples=samples)

    assert snapshot["ok"] is False
    assert {alert["id"] for alert in snapshot["alerts"]} >= {
        "peer_count_zero",
        "proof_metadata_mismatch",
    }


def test_prometheus_renderer_escapes_labels() -> None:
    text = render_prometheus_text_v0(
        [
            MetricSample(
                "zeno_gossip_rejections_total",
                2,
                labels={"reason": 'bad"quote'},
                description="Gossip rejects",
            )
        ]
    )

    assert '# HELP zeno_gossip_rejections_total Gossip rejects' in text
    assert 'reason="bad\\"quote"' in text


def test_chaos_report_can_be_converted_to_metrics() -> None:
    report = run_chaos_harness(["gossip_flood"])
    samples = samples_from_chaos_report_v0(report)

    assert any(sample.name == "zeno_chaos_block_rejected_total" for sample in samples)
    assert any(sample.labels.get("reason") == "duplicate_gossip_envelope" for sample in samples)


def test_zeno_ops_status_cli_json(capsys) -> None:
    rc = zeno_ops_status.main(["--ledger-height", "12", "--peer-count", "2"])

    assert rc == 0
    snapshot = json.loads(capsys.readouterr().out)
    assert snapshot["schema"] == "zenodex/zeno_ops_metrics_snapshot/v0"
    assert snapshot["ok"] is True
