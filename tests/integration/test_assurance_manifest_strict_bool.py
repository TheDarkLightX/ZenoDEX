from __future__ import annotations

import json
from pathlib import Path

import pytest

import tools.check_batch_auction_ifql_vmo_manifest as batch_ifql_manifest
import tools.check_runtime_shell_assurance_manifest as runtime_shell_manifest


def _write_json(path: Path, payload: object) -> None:
    path.write_text(json.dumps(payload, indent=2, sort_keys=True), encoding="utf-8")


def test_runtime_shell_manifest_rejects_string_ok(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.setattr(runtime_shell_manifest, "REPO_ROOT", tmp_path)
    _write_json(
        tmp_path / "shell.json",
        {
            "ok": "false",
            "command": "shell-lint",
            "ir_hash": "abc",
            "adapter": {"spec": "adapter"},
            "expected": {"actions": [], "effects": []},
            "got": {"actions": [], "effects": []},
            "issues": [],
        },
    )

    with pytest.raises(runtime_shell_manifest.ManifestError, match="shell.json: ok: expected bool"):
        runtime_shell_manifest._check_shell_lint(
            {
                "report_path": "shell.json",
                "ir_hash": "abc",
                "adapter_spec": "adapter",
                "actions": [],
                "effects": [],
            }
        )


def test_runtime_shell_manifest_rejects_string_determinism_ok(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    monkeypatch.setattr(runtime_shell_manifest, "REPO_ROOT", tmp_path)
    _write_json(
        tmp_path / "verify.json",
        {
            "ok": True,
            "command": "verify-shell",
            "ir_hash": "abc",
            "mode": "bounded",
            "seed": 7,
            "traces": 2,
            "max_steps": 3,
            "determinism_trials": 2,
            "failure": None,
            "adapter": {"spec": "adapter"},
            "model": "kernel.yaml",
            "determinism": {"ok": "false", "fingerprints": ["fp", "fp"]},
        },
    )

    with pytest.raises(runtime_shell_manifest.ManifestError, match="determinism.ok: expected bool"):
        runtime_shell_manifest._check_verify_shell(
            {
                "report_path": "verify.json",
                "ir_hash": "abc",
                "mode": "bounded",
                "seed": 7,
                "traces": 2,
                "max_steps": 3,
                "determinism_trials": 2,
                "adapter_spec": "adapter",
                "kernel_path": "kernel.yaml",
                "fingerprint": "fp",
            }
        )


def test_batch_ifql_manifest_rejects_string_ok(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.setattr(batch_ifql_manifest, "REPO_ROOT", tmp_path)
    _write_json(
        tmp_path / "intent.json",
        {
            "ok": "false",
            "schema": "esso-intent-report/v1",
            "intent_hash": "intent",
            "intent_source": str(tmp_path / "intent.yaml"),
            "issues": [],
            "stats": {"nodes": 1, "leaf_nodes": 1, "leaf_nodes_mapped": 1},
            "coverage": {"required": {"ok": True}},
        },
    )

    with pytest.raises(batch_ifql_manifest.ManifestError, match="intent.json: ok: expected bool"):
        batch_ifql_manifest._check_intent_lint(
            {
                "report_path": "intent.json",
                "intent_hash": "intent",
                "intent_source": "intent.yaml",
                "nodes": 1,
                "leaf_nodes": 1,
                "leaf_nodes_mapped": 1,
                "required_ok": True,
            }
        )


def test_batch_ifql_manifest_rejects_string_required_ok(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    monkeypatch.setattr(batch_ifql_manifest, "REPO_ROOT", tmp_path)
    _write_json(tmp_path / "intent.yaml", "intent: sample\n")
    _write_json(
        tmp_path / "intent.json",
        {
            "ok": True,
            "schema": "esso-intent-report/v1",
            "intent_hash": "intent",
            "intent_source": str(tmp_path / "intent.yaml"),
            "issues": [],
            "stats": {"nodes": 1, "leaf_nodes": 1, "leaf_nodes_mapped": 1},
            "coverage": {"required": {"ok": "false"}},
        },
    )

    with pytest.raises(batch_ifql_manifest.ManifestError, match="coverage.required.ok: expected bool"):
        batch_ifql_manifest._check_intent_lint(
            {
                "report_path": "intent.json",
                "intent_hash": "intent",
                "intent_source": "intent.yaml",
                "nodes": 1,
                "leaf_nodes": 1,
                "leaf_nodes_mapped": 1,
                "required_ok": True,
            }
        )


def test_batch_ifql_manifest_rejects_string_effective_ok(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    monkeypatch.setattr(batch_ifql_manifest, "REPO_ROOT", tmp_path)
    _write_json(
        tmp_path / "ifql.json",
        {
            "ok": True,
            "ok_effective": "false",
            "schema": "esso-ifql-report/v1",
            "report_hash": "report",
            "issues": [],
            "inputs": {"model": {"ir_hash": "ir", "model_id": "model"}},
            "nodes": [{"id": "n0"}],
        },
    )

    with pytest.raises(batch_ifql_manifest.ManifestError, match="report ok_effective: expected bool"):
        batch_ifql_manifest._check_ifql_report(
            {
                "report_path": "ifql.json",
                "report_hash": "report",
                "model_ir_hash": "ir",
                "model_id": "model",
                "node_ids": ["n0"],
            }
        )


def test_batch_ifql_manifest_rejects_string_vmo_ok(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    monkeypatch.setattr(batch_ifql_manifest, "REPO_ROOT", tmp_path)
    _write_json(
        tmp_path / "vmo.json",
        {
            "ok": True,
            "fiber": "intent-a",
            "intent_id": "intent-a",
            "schema": "esso-ifql-vmo/v1",
            "observables": {"state_vars": ["x"], "effects": []},
            "vmo": {
                "ok": "false",
                "schema": "esso-vmo/v1",
                "vmo_hash": "vmo",
                "preserves": ["intent-a"],
                "checks": [
                    {
                        "kind": "z3.observational_equivalence",
                        "mode": "bounded",
                        "ok": True,
                        "result": {"status": "PASS"},
                    },
                    {"kind": "hash.replay", "ok": True},
                ],
            },
        },
    )

    with pytest.raises(batch_ifql_manifest.ManifestError, match="vmo ok: expected bool"):
        batch_ifql_manifest._check_ifql_vmo(
            {
                "report_path": "vmo.json",
                "fiber": "intent-a",
                "intent_id": "intent-a",
                "observed_state_vars": ["x"],
                "vmo_hash": "vmo",
                "preserves": ["intent-a"],
                "mode": "bounded",
            }
        )
