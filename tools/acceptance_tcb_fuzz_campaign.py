#!/usr/bin/env python3
"""Plan or execute the acceptance TCB fuzz bundle and emit a replayable receipt."""

from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys
import time
from pathlib import Path
from typing import Any, Sequence


REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from tools.stateful_feedback import (
    build_exploit_proximity_report,
    build_guard_attribution_report,
    build_introspection_report,
    build_surface_suggestions,
    build_weird_machine_atlas,
    load_dangerous_surface_manifest,
)


DEFAULT_CAMPAIGN_ROOT_BASE = REPO_ROOT / "internal" / "fuzz_campaigns"
DEFAULT_TARGET_MANIFEST = REPO_ROOT / "tools" / "acceptance_tcb_dangerous_surfaces.json"
FAST_GATE_PATH = REPO_ROOT / "tools" / "run_acceptance_tcb_fuzz_gate.sh"
DEEP_GATE_PATH = REPO_ROOT / "tools" / "run_acceptance_tcb_fuzz_gate_deep.sh"
MINIMIZED_WITNESS_SPECS: tuple[dict[str, Any], ...] = (
    {
        "id": "dex_engine_replay_dead_tail",
        "tool": "tools/dex_engine_sequence_grammar_fuzz.py",
        "target": "dex_engine_sequence",
        "derivation": "DexSeq->ReplayPoolAfterSuccessWithDeadTail",
        "lanes": ("fast", "deep"),
    },
    {
        "id": "dex_engine_quote_receipt_stale_dead_tail",
        "tool": "tools/dex_engine_quote_receipt_sequence_grammar_fuzz.py",
        "target": "direct_quote_receipt_sequence",
        "derivation": "DirectSeq->ValidThenStaleSamePoolWithDeadTail",
        "lanes": ("deep",),
    },
    {
        "id": "dex_engine_settlement_stale_dead_tail",
        "tool": "tools/dex_engine_settlement_sequence_grammar_fuzz.py",
        "target": "dex_engine_settlement_sequence",
        "derivation": "SettlementSeq->WarmupThenStaleProvidedAbWithDeadTail",
        "lanes": ("deep",),
    },
    {
        "id": "nonce_cross_batch_replay",
        "tool": "tools/nonce_replay_sequence_grammar_fuzz.py",
        "target": "nonce_replay_sequence",
        "derivation": "Seq->CrossBatchReplayWithDeadTail",
        "lanes": ("fast", "deep"),
    },
    {
        "id": "operations_duplicate_signature",
        "tool": "tools/operations_grammar_fuzz.py",
        "target": "signed_intents",
        "derivation": "SignedOps->OneEntry ; Entry->DuplicateSignatureSameWithDeadTail",
        "lanes": ("fast", "deep"),
    },
    {
        "id": "route_certificate_candidate_set_hash_mismatch",
        "tool": "tools/route_certificate_sequence_grammar_fuzz.py",
        "target": "route_certificate_sequence",
        "derivation": "add_better_candidate",
        "lanes": ("deep",),
    },
    {
        "id": "route_canonicalization_candidate_set_hash_mismatch",
        "tool": "tools/route_certificate_sequence_grammar_fuzz.py",
        "target": "route_certificate_sequence",
        "derivation": "add_better_candidate",
        "lanes": ("deep",),
    },
    {
        "id": "settlement_attestation_stale",
        "tool": "tools/settlement_attestation_sequence_grammar_fuzz.py",
        "target": "settlement_attestation_sequence",
        "derivation": "stale_second_step",
        "lanes": ("deep",),
        "extra_args": ["--attestation-mode", "policy"],
    },
    {
        "id": "settlement_attestation_allowlist_drift",
        "tool": "tools/settlement_attestation_sequence_grammar_fuzz.py",
        "target": "settlement_attestation_sequence",
        "derivation": "narrow_allowlist",
        "lanes": ("deep",),
        "extra_args": ["--attestation-mode", "policy"],
    },
    {
        "id": "settlement_attestation_packet_hash_mismatch",
        "tool": "tools/settlement_attestation_sequence_grammar_fuzz.py",
        "target": "settlement_attestation_sequence",
        "derivation": "tamper_second_step_hash",
        "lanes": ("deep",),
        "extra_args": ["--attestation-mode", "policy"],
    },
    {
        "id": "settlement_attestation_signature_invalid",
        "tool": "tools/settlement_attestation_sequence_grammar_fuzz.py",
        "target": "settlement_attestation_sequence",
        "derivation": "tamper_second_step_signature",
        "lanes": ("deep",),
        "extra_args": ["--attestation-mode", "policy"],
    },
    {
        "id": "settlement_attestation_future_epoch",
        "tool": "tools/settlement_attestation_sequence_grammar_fuzz.py",
        "target": "settlement_attestation_sequence",
        "derivation": "future_second_step",
        "lanes": ("deep",),
        "extra_args": ["--attestation-mode", "policy"],
    },
)
STATEFUL_EXPLORER_SPECS: tuple[dict[str, Any], ...] = (
    {
        "id": "state_boundary_concolic",
        "tool": "tools/state_boundary_concolic_stateful.py",
        "target": "all",
        "max_depth": 2,
        "max_frontier": 128,
        "slow": False,
    },
    {
        "id": "route_certificate_sequence",
        "tool": "tools/route_certificate_sequence_grammar_fuzz.py",
        "target": "route_certificate_sequence",
        "max_depth": 3,
        "max_frontier": 128,
        "slow": False,
    },
    {
        "id": "operations_signature_sequence",
        "tool": "tools/operations_signature_sequence_grammar_fuzz.py",
        "target": "signature_reuse_sequence",
        "max_depth": 1,
        "max_frontier": 32,
        "slow": False,
    },
    {
        "id": "quote_receipt_sequence",
        "tool": "tools/quote_receipt_sequence_grammar_fuzz.py",
        "target": "stale_quote_receipt_sequence",
        "max_depth": 1,
        "max_frontier": 32,
        "slow": False,
    },
    {
        "id": "stale_settlement_sequence",
        "tool": "tools/stale_settlement_sequence_grammar_fuzz.py",
        "target": "stale_settlement_sequence",
        "max_depth": 1,
        "max_frontier": 32,
        "slow": False,
    },
    {
        "id": "settlement_attestation_sequence_policy",
        "tool": "tools/settlement_attestation_sequence_grammar_fuzz.py",
        "target": "settlement_attestation_sequence",
        "max_depth": 3,
        "max_frontier": 64,
        "slow": False,
        "extra_args": ["--attestation-mode", "policy"],
    },
    {
        "id": "settlement_attestation_sequence_full",
        "tool": "tools/settlement_attestation_sequence_grammar_fuzz.py",
        "target": "settlement_attestation_sequence",
        "max_depth": 1,
        "max_frontier": 8,
        "slow": True,
        "extra_args": ["--attestation-mode", "full"],
    },
)
SUMMARY_RE = re.compile(
    r"(?P<passed>\d+) passed(?:, (?P<failed>\d+) failed)?(?:, (?P<warnings>\d+) warning[s]?)? in (?P<duration_s>[0-9.]+)s"
)


class CampaignError(RuntimeError):
    pass


def _default_campaign_root(gate_lane: str) -> str:
    return str(DEFAULT_CAMPAIGN_ROOT_BASE / gate_lane)


def _default_target_manifest() -> str | None:
    if DEFAULT_TARGET_MANIFEST.is_file():
        return str(DEFAULT_TARGET_MANIFEST)
    return None


def _witness_specs_for_lane(gate_lane: str) -> tuple[dict[str, Any], ...]:
    return tuple(spec for spec in MINIMIZED_WITNESS_SPECS if gate_lane in tuple(spec.get("lanes", ())))


def _sanitize_run_id(raw: str) -> str:
    text = re.sub(r"[^A-Za-z0-9._-]+", "-", raw.strip())
    text = text.strip("-.")
    return text or "run"


def _default_python() -> str:
    env_python = os.environ.get("PYTHON")
    if env_python:
        return env_python
    venv_python = REPO_ROOT / ".venv" / "bin" / "python"
    if venv_python.is_file() and os.access(venv_python, os.X_OK):
        return str(venv_python)
    return sys.executable or "python3"


def _git_value(*args: str) -> str | None:
    try:
        proc = subprocess.run(
            ["git", *args],
            cwd=REPO_ROOT,
            check=True,
            capture_output=True,
            text=True,
        )
    except Exception:
        return None
    return proc.stdout.strip() or None


def _git_dirty_count() -> int | None:
    try:
        proc = subprocess.run(
            ["git", "status", "--porcelain"],
            cwd=REPO_ROOT,
            check=True,
            capture_output=True,
            text=True,
        )
    except Exception:
        return None
    return len([line for line in proc.stdout.splitlines() if line.strip()])


def _parse_summary(stdout: str) -> dict[str, Any] | None:
    for line in reversed(stdout.splitlines()):
        match = SUMMARY_RE.search(line)
        if match:
            return {
                "passed": int(match.group("passed")),
                "failed": int(match.group("failed") or 0),
                "warnings": int(match.group("warnings") or 0),
                "pytest_duration_s": float(match.group("duration_s")),
                "summary_line": line.strip(),
            }
    return None


def _gate_path_for_lane(lane: str) -> Path:
    if lane == "fast":
        return FAST_GATE_PATH
    if lane == "deep":
        return DEEP_GATE_PATH
    raise CampaignError(f"unknown gate lane: {lane}")


def _run_gate(gate_path: Path) -> dict[str, Any]:
    started = time.monotonic()
    proc = subprocess.run(
        ["bash", str(gate_path)],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
    )
    duration_s = round(time.monotonic() - started, 3)
    summary = _parse_summary(proc.stdout)
    return {
        "command": ["bash", str(gate_path.relative_to(REPO_ROOT))],
        "mode": "run_gate",
        "ok": proc.returncode == 0,
        "returncode": proc.returncode,
        "duration_s": duration_s,
        "stdout": proc.stdout,
        "stderr": proc.stderr,
        "pytest_summary": summary,
    }


def _refresh_only_result(*, campaign_root: str | None, fallback_report_out: str | None) -> dict[str, Any]:
    started = time.monotonic()
    out_path = _refresh_shared_witness_index(campaign_root=campaign_root, fallback_report_out=fallback_report_out)
    return {
        "command": ["refresh_shared_index"],
        "mode": "refresh_shared_index_only",
        "ok": True,
        "returncode": 0,
        "duration_s": round(time.monotonic() - started, 3),
        "stdout": "",
        "stderr": "",
        "pytest_summary": None,
        "shared_minimized_witness_index_out": out_path,
    }


def _default_report_path(*, campaign_root: str | None, gate_lane: str, timestamp_utc: str | None, run_id: str | None) -> str | None:
    campaign_root = campaign_root or _default_campaign_root(gate_lane)
    ts = (timestamp_utc or time.strftime("%Y%m%dT%H%M%SZ", time.gmtime())).strip()
    rid = _sanitize_run_id(run_id or "acceptance-tcb-fuzz")
    return str(Path(campaign_root) / f"{ts}_{rid}" / "acceptance_tcb_fuzz_report.json")


def _write_report(path: str | None, payload: dict[str, Any]) -> None:
    if not path:
        return
    report_path = Path(path)
    report_path.parent.mkdir(parents=True, exist_ok=True)
    report_path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _relpath(path: Path) -> str:
    try:
        return str(path.relative_to(REPO_ROOT))
    except ValueError:
        return str(path)


def _resolve_repo_path(path: str | None) -> Path | None:
    if path is None:
        return None
    raw = Path(path)
    if raw.is_absolute():
        return raw
    return REPO_ROOT / raw


def _campaign_dir(report_out: str | None) -> Path | None:
    if not report_out:
        return None
    return Path(report_out).parent


def _shared_witness_index_out(campaign_root: str | None, report_out: str | None) -> str | None:
    if campaign_root:
        return _relpath(Path(campaign_root) / "minimized_witness_index.json")
    campaign_dir = _campaign_dir(report_out)
    if campaign_dir is None:
        return None
    parent = campaign_dir.parent
    if parent == campaign_dir:
        return None
    return _relpath(parent / "minimized_witness_index.json")


def _stateful_report_dir(report_out: str | None) -> Path | None:
    campaign_dir = _campaign_dir(report_out)
    if campaign_dir is None:
        return None
    return campaign_dir / "stateful_reports"


def _introspection_out(report_out: str | None) -> Path | None:
    campaign_dir = _campaign_dir(report_out)
    if campaign_dir is None:
        return None
    return campaign_dir / "stateful_introspection.json"


def _atlas_out(report_out: str | None) -> Path | None:
    campaign_dir = _campaign_dir(report_out)
    if campaign_dir is None:
        return None
    return campaign_dir / "weird_machine_atlas.json"


def _surface_suggestions_out(report_out: str | None) -> Path | None:
    campaign_dir = _campaign_dir(report_out)
    if campaign_dir is None:
        return None
    return campaign_dir / "stateful_surface_suggestions.json"


def _guard_attribution_out(report_out: str | None) -> Path | None:
    campaign_dir = _campaign_dir(report_out)
    if campaign_dir is None:
        return None
    return campaign_dir / "guard_attribution.json"


def _exploit_proximity_out(report_out: str | None) -> Path | None:
    campaign_dir = _campaign_dir(report_out)
    if campaign_dir is None:
        return None
    return campaign_dir / "stateful_exploit_proximity.json"


def _campaign_artifact_paths(
    *,
    report_out: str | None,
    campaign_root: str | None,
    stateful_exploration: bool,
    target_manifest: str | None,
    include_slow_explorers: bool,
) -> dict[str, Any]:
    campaign_dir = _campaign_dir(report_out)
    base: dict[str, Any] = {
        "campaign_dir": None,
        "minimized_witness_dir": None,
        "minimized_witness_index_out": None,
        "shared_minimized_witness_index_out": None,
        "stateful_report_dir": None,
        "introspection_out": None,
        "atlas_out": None,
        "surface_suggestions_out": None,
        "guard_attribution_out": None,
        "exploit_proximity_out": None,
        "target_manifest": None,
        "include_slow_explorers": include_slow_explorers,
    }
    if campaign_dir is None:
        return base
    base.update(
        {
            "campaign_dir": _relpath(campaign_dir),
            "minimized_witness_dir": _relpath(campaign_dir / "minimized_witnesses"),
            "minimized_witness_index_out": _relpath(campaign_dir / "minimized_witness_index.json"),
            "shared_minimized_witness_index_out": _shared_witness_index_out(campaign_root, report_out),
        }
    )
    manifest_path = _resolve_repo_path(target_manifest)
    if stateful_exploration:
        report_dir = _stateful_report_dir(report_out)
        introspection_out = _introspection_out(report_out)
        atlas_out = _atlas_out(report_out)
        surface_suggestions_out = _surface_suggestions_out(report_out)
        guard_attribution_out = _guard_attribution_out(report_out)
        exploit_proximity_out = _exploit_proximity_out(report_out)
        if report_dir is not None:
            base["stateful_report_dir"] = _relpath(report_dir)
        if introspection_out is not None:
            base["introspection_out"] = _relpath(introspection_out)
        if atlas_out is not None:
            base["atlas_out"] = _relpath(atlas_out)
        if surface_suggestions_out is not None:
            base["surface_suggestions_out"] = _relpath(surface_suggestions_out)
        if guard_attribution_out is not None:
            base["guard_attribution_out"] = _relpath(guard_attribution_out)
        if exploit_proximity_out is not None:
            base["exploit_proximity_out"] = _relpath(exploit_proximity_out)
        if manifest_path is not None:
            base["target_manifest"] = _relpath(manifest_path)
    return base


def _run_minimized_witness_capture(*, python_bin: str, spec: dict[str, Any]) -> dict[str, Any]:
    command = [
        python_bin,
        spec["tool"],
        "--target",
        spec["target"],
        "--minimize-derivation",
        spec["derivation"],
        "--format",
        "json",
    ]
    extra_args = spec.get("extra_args", ())
    if isinstance(extra_args, (list, tuple)):
        command.extend(str(arg) for arg in extra_args)
    proc = subprocess.run(
        command,
        cwd=REPO_ROOT,
        check=False,
        capture_output=True,
        text=True,
    )
    if proc.returncode != 0:
        raise CampaignError(f"minimized witness command failed for {spec['id']}: {proc.stderr or proc.stdout}")
    try:
        payload = json.loads(proc.stdout)
    except json.JSONDecodeError as exc:  # pragma: no cover
        raise CampaignError(f"invalid minimized witness JSON for {spec['id']}") from exc
    if payload.get("schema") is None or "witness" not in payload:
        raise CampaignError(f"incomplete minimized witness payload for {spec['id']}")
    return payload


def _build_campaign_witness_index_payload(*, gate_lane: str, report_out: str, witnesses: list[dict[str, Any]]) -> dict[str, Any]:
    return {
        "schema": "zenodex/acceptance-tcb-fuzz-minimized-witness-index/v1",
        "gate_lane": gate_lane,
        "campaign_report": _relpath(Path(report_out)),
        "count": len(witnesses),
        "witnesses": witnesses,
    }


def _write_minimized_witness_artifacts(*, python_bin: str, gate_lane: str, report_out: str, campaign_root: str | None) -> dict[str, Any]:
    campaign_dir = _campaign_dir(report_out)
    if campaign_dir is None:
        raise CampaignError("report_out is required to write minimized witness artifacts")
    witness_dir = campaign_dir / "minimized_witnesses"
    witness_dir.mkdir(parents=True, exist_ok=True)

    witnesses: list[dict[str, Any]] = []
    for spec in _witness_specs_for_lane(gate_lane):
        payload = _run_minimized_witness_capture(python_bin=python_bin, spec=spec)
        witness_path = witness_dir / f"{spec['id']}.json"
        witness_path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
        witness = payload["witness"]
        witnesses.append(
            {
                "id": spec["id"],
                "tool": spec["tool"],
                "target": witness["target"],
                "derivation": witness["derivation"],
                "outcome_label": witness["outcome_label"],
                "path_id": witness["path_id"],
                "path_length": witness["path_length"],
                "original_size": witness["original_size"],
                "minimized_size": witness["minimized_size"],
                "witness_out": _relpath(witness_path),
            }
        )

    local_index_out = campaign_dir / "minimized_witness_index.json"
    local_payload = _build_campaign_witness_index_payload(gate_lane=gate_lane, report_out=report_out, witnesses=witnesses)
    local_index_out.write_text(json.dumps(local_payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    shared_index_out = _refresh_shared_witness_index(campaign_root=campaign_root, fallback_report_out=report_out)
    return {
        "count": len(witnesses),
        "minimized_witness_dir": _relpath(witness_dir),
        "minimized_witness_index_out": _relpath(local_index_out),
        "shared_minimized_witness_index_out": shared_index_out,
        "witnesses": witnesses,
    }


def _refresh_shared_witness_index(*, campaign_root: str | None, fallback_report_out: str | None) -> str | None:
    if campaign_root:
        root = Path(campaign_root)
    else:
        campaign_dir = _campaign_dir(fallback_report_out)
        if campaign_dir is None:
            return None
        root = campaign_dir.parent
    root.mkdir(parents=True, exist_ok=True)

    campaigns: list[dict[str, Any]] = []
    flat_witnesses: list[dict[str, Any]] = []
    for child in sorted(root.iterdir()):
        if not child.is_dir():
            continue
        local_index = child / "minimized_witness_index.json"
        if not local_index.is_file():
            continue
        payload = json.loads(local_index.read_text(encoding="utf-8"))
        campaign_report = payload.get("campaign_report")
        witnesses = payload.get("witnesses", [])
        campaigns.append(
            {
                "campaign_dir": _relpath(child),
                "gate_lane": payload.get("gate_lane"),
                "campaign_report": campaign_report,
                "count": int(payload.get("count", len(witnesses))),
                "index_out": _relpath(local_index),
            }
        )
        for witness in witnesses:
            flat_witnesses.append(
                {
                    "campaign_dir": _relpath(child),
                    "gate_lane": payload.get("gate_lane"),
                    "campaign_report": campaign_report,
                    "id": witness["id"],
                    "target": witness["target"],
                    "derivation": witness["derivation"],
                    "outcome_label": witness["outcome_label"],
                    "path_id": witness["path_id"],
                    "minimized_size": witness["minimized_size"],
                    "witness_out": witness["witness_out"],
                }
            )

    out_path = root / "minimized_witness_index.json"
    out_payload = {
        "schema": "zenodex/acceptance-tcb-fuzz-minimized-witness-shared-index/v1",
        "campaign_count": len(campaigns),
        "witness_count": len(flat_witnesses),
        "campaigns": campaigns,
        "witnesses": flat_witnesses,
    }
    out_path.write_text(json.dumps(out_payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return _relpath(out_path)


def _run_stateful_explorer(
    *,
    python_bin: str,
    spec: dict[str, Any],
    feedback_mode: str,
    target_manifest: str,
    target_id: str | None,
) -> dict[str, Any]:
    command = [
        python_bin,
        spec["tool"],
        "--format",
        "json",
        "--feedback-mode",
        feedback_mode,
        "--max-depth",
        str(int(spec["max_depth"])),
        "--max-frontier",
        str(int(spec["max_frontier"])),
        "--target-manifest",
        target_manifest,
    ]
    target = str(spec.get("target", "all"))
    if target != "all":
        command.extend(["--target", target])
    if target_id is not None:
        command.extend(["--target-id", target_id])
    extra_args = spec.get("extra_args", ())
    if isinstance(extra_args, (list, tuple)):
        command.extend(str(arg) for arg in extra_args)
    proc = subprocess.run(
        command,
        cwd=REPO_ROOT,
        check=False,
        capture_output=True,
        text=True,
    )
    if proc.returncode != 0:
        raise CampaignError(f"stateful explorer failed for {spec['id']}: {proc.stderr or proc.stdout}")
    try:
        return json.loads(proc.stdout)
    except json.JSONDecodeError as exc:  # pragma: no cover
        raise CampaignError(f"invalid JSON from stateful explorer {spec['id']}") from exc


def _write_stateful_exploration_artifacts(
    *,
    python_bin: str,
    report_out: str,
    feedback_mode: str,
    target_manifest: str,
    target_id: str | None,
    include_slow_explorers: bool,
    shared_minimized_witness_index_out: str | None,
) -> dict[str, Any]:
    manifest_path = _resolve_repo_path(target_manifest)
    if manifest_path is None or not manifest_path.is_file():
        raise CampaignError(f"missing target manifest: {target_manifest}")
    dangerous_surfaces = load_dangerous_surface_manifest(manifest_path)

    report_dir = _stateful_report_dir(report_out)
    introspection_out = _introspection_out(report_out)
    atlas_out = _atlas_out(report_out)
    surface_suggestions_out = _surface_suggestions_out(report_out)
    guard_attribution_out = _guard_attribution_out(report_out)
    exploit_proximity_out = _exploit_proximity_out(report_out)
    if report_dir is None or introspection_out is None or atlas_out is None or surface_suggestions_out is None or guard_attribution_out is None or exploit_proximity_out is None:
        raise CampaignError("report_out is required to write stateful exploration artifacts")
    report_dir.mkdir(parents=True, exist_ok=True)

    report_payloads: list[dict[str, Any]] = []
    explorer_rows: list[dict[str, Any]] = []
    for spec in STATEFUL_EXPLORER_SPECS:
        if bool(spec.get("slow")) and not include_slow_explorers:
            continue
        payload = _run_stateful_explorer(
            python_bin=python_bin,
            spec=spec,
            feedback_mode=feedback_mode,
            target_manifest=str(manifest_path),
            target_id=target_id,
        )
        out_path = report_dir / f"{spec['id']}.json"
        out_path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
        report_payloads.append(payload)
        explorer_rows.append(
            {
                "id": spec["id"],
                "tool": spec["tool"],
                "schema": payload.get("schema"),
                "supported": payload.get("supported", True),
                "report_count": len(payload.get("reports", [])) if isinstance(payload.get("reports"), list) else 0,
                "report_out": _relpath(out_path),
            }
        )

    shared_witness_index = None
    shared_index_path = _resolve_repo_path(shared_minimized_witness_index_out)
    if shared_index_path is not None and shared_index_path.is_file():
        shared_witness_index = json.loads(shared_index_path.read_text(encoding="utf-8"))

    introspection_payload = build_introspection_report(
        dangerous_surfaces=dangerous_surfaces,
        shared_witness_index=shared_witness_index,
        report_payloads=report_payloads,
        target_id=target_id,
    )
    atlas_payload = build_weird_machine_atlas(
        dangerous_surfaces=dangerous_surfaces,
        shared_witness_index=shared_witness_index,
        report_payloads=report_payloads,
        target_id=target_id,
    )
    suggestions_payload = build_surface_suggestions(
        dangerous_surfaces=dangerous_surfaces,
        shared_witness_index=shared_witness_index,
        report_payloads=report_payloads,
        target_id=target_id,
    )
    guard_attribution_payload = build_guard_attribution_report(
        dangerous_surfaces=dangerous_surfaces,
        shared_witness_index=shared_witness_index,
        target_id=target_id,
    )
    exploit_proximity_payload = build_exploit_proximity_report(
        dangerous_surfaces=dangerous_surfaces,
        shared_witness_index=shared_witness_index,
        target_id=target_id,
    )
    introspection_out.write_text(json.dumps(introspection_payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    atlas_out.write_text(json.dumps(atlas_payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    surface_suggestions_out.write_text(json.dumps(suggestions_payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    guard_attribution_out.write_text(json.dumps(guard_attribution_payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    exploit_proximity_out.write_text(json.dumps(exploit_proximity_payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    return {
        "stateful_report_dir": _relpath(report_dir),
        "reports": explorer_rows,
        "target_manifest": _relpath(manifest_path),
        "target_id": target_id,
        "feedback_mode": feedback_mode,
        "include_slow_explorers": include_slow_explorers,
        "introspection_out": _relpath(introspection_out),
        "atlas_out": _relpath(atlas_out),
        "surface_suggestions_out": _relpath(surface_suggestions_out),
        "guard_attribution_out": _relpath(guard_attribution_out),
        "exploit_proximity_out": _relpath(exploit_proximity_out),
        "status_counts": introspection_payload["status_counts"],
        "surface_count": introspection_payload["surface_count"],
        "suggestion_count": suggestions_payload["suggestion_count"],
        "guard_family_count": guard_attribution_payload["guard_family_count"],
        "hotspot_count": exploit_proximity_payload["hotspot_count"],
    }


def _payload(
    *,
    plan: bool,
    python_bin: str,
    gate_lane: str,
    gate_path: Path,
    report_out: str | None,
    campaign_root: str | None,
    result: dict[str, Any] | None,
    artifacts: dict[str, Any] | None,
    stateful_exploration: bool,
    feedback_mode: str,
    target_manifest: str | None,
    target_id: str | None,
    include_slow_explorers: bool,
) -> dict[str, Any]:
    resolved_target_manifest = _resolve_repo_path(target_manifest)
    return {
        "schema": "zenodex/acceptance-tcb-fuzz-campaign-report/v1",
        "plan_only": plan,
        "python": python_bin,
        "gate_lane": gate_lane,
        "gate": str(gate_path.relative_to(REPO_ROOT)),
        "report_out": report_out,
        "git_head": _git_value("rev-parse", "HEAD"),
        "git_head_short": _git_value("rev-parse", "--short", "HEAD"),
        "git_dirty_count": _git_dirty_count(),
        "stateful_config": {
            "enabled": stateful_exploration,
            "feedback_mode": feedback_mode,
            "target_manifest": _relpath(resolved_target_manifest) if resolved_target_manifest is not None else None,
            "target_id": target_id,
            "include_slow_explorers": include_slow_explorers,
        },
        "artifacts": artifacts
        if artifacts is not None
        else _campaign_artifact_paths(
            report_out=report_out,
            campaign_root=campaign_root,
            stateful_exploration=stateful_exploration,
            target_manifest=target_manifest,
            include_slow_explorers=include_slow_explorers,
        ),
        "result": result,
    }


def _print_text(payload: dict[str, Any]) -> None:
    print("Acceptance TCB Fuzz Campaign")
    print(f"plan_only: {'yes' if payload['plan_only'] else 'no'}")
    print(f"gate: {payload['gate']}")
    if payload["git_head_short"] is not None:
        print(f"git_head: {payload['git_head_short']}")
    if payload["git_dirty_count"] is not None:
        print(f"git_dirty_count: {payload['git_dirty_count']}")
    if payload["report_out"]:
        print(f"report_out: {payload['report_out']}")
    stateful = payload.get("stateful_config") or {}
    print(f"stateful_exploration: {'yes' if stateful.get('enabled') else 'no'}")
    if stateful.get("target_manifest"):
        print(f"target_manifest: {stateful['target_manifest']}")
    if stateful.get("target_id"):
        print(f"target_id: {stateful['target_id']}")
    artifacts = payload.get("artifacts") or {}
    if artifacts.get("minimized_witness_index_out"):
        print(f"minimized_witness_index_out: {artifacts['minimized_witness_index_out']}")
    if artifacts.get("shared_minimized_witness_index_out"):
        print(f"shared_minimized_witness_index_out: {artifacts['shared_minimized_witness_index_out']}")
    if artifacts.get("stateful_report_dir"):
        print(f"stateful_report_dir: {artifacts['stateful_report_dir']}")
    if artifacts.get("introspection_out"):
        print(f"introspection_out: {artifacts['introspection_out']}")
    if artifacts.get("atlas_out"):
        print(f"atlas_out: {artifacts['atlas_out']}")
    if artifacts.get("surface_suggestions_out"):
        print(f"surface_suggestions_out: {artifacts['surface_suggestions_out']}")
    if artifacts.get("guard_attribution_out"):
        print(f"guard_attribution_out: {artifacts['guard_attribution_out']}")
    if artifacts.get("exploit_proximity_out"):
        print(f"exploit_proximity_out: {artifacts['exploit_proximity_out']}")
    result = payload.get("result")
    if result is None:
        return
    print(f"ok: {'yes' if result['ok'] else 'no'}")
    mode = result.get("mode")
    if mode is not None:
        print(f"mode: {mode}")
    print(f"duration_s: {result['duration_s']}")
    summary = result.get("pytest_summary")
    if summary is not None:
        print(f"pytest_summary: {summary['summary_line']}")
    shared_out = result.get("shared_minimized_witness_index_out")
    if shared_out and shared_out != artifacts.get("shared_minimized_witness_index_out"):
        print(f"shared_minimized_witness_index_out: {shared_out}")
    stateful_summary = result.get("stateful_exploration")
    if isinstance(stateful_summary, dict):
        print(f"stateful_reports: {len(stateful_summary.get('reports', []))}")
        if stateful_summary.get("status_counts"):
            print(f"stateful_status_counts: {json.dumps(stateful_summary['status_counts'], sort_keys=True)}")
        if stateful_summary.get("suggestion_count") is not None:
            print(f"stateful_suggestion_count: {stateful_summary['suggestion_count']}")
        if stateful_summary.get("guard_family_count") is not None:
            print(f"stateful_guard_family_count: {stateful_summary['guard_family_count']}")
        if stateful_summary.get("hotspot_count") is not None:
            print(f"stateful_hotspot_count: {stateful_summary['hotspot_count']}")


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--format", choices=("text", "json"), default="text")
    parser.add_argument("--plan", action="store_true", help="print the campaign plan without executing the gate")
    parser.add_argument("--report-out", help="optional path to write the JSON campaign report")
    parser.add_argument(
        "--campaign-root",
        help="optional root directory for stable campaign output (writes <timestamp>_<run-id>/acceptance_tcb_fuzz_report.json)",
    )
    parser.add_argument("--timestamp-utc", help="optional UTC timestamp token for campaign output")
    parser.add_argument("--run-id", help="optional run id token for campaign output")
    parser.add_argument(
        "--refresh-shared-index-only",
        action="store_true",
        help="rebuild the shared minimized witness index from existing per-campaign indexes without running the gate",
    )
    parser.add_argument(
        "--gate-lane",
        choices=("fast", "deep"),
        default="deep",
        help="select the gate lane: fast default gate or deep stateful campaign gate",
    )
    parser.add_argument("--target-manifest", default=_default_target_manifest())
    parser.add_argument("--target-id")
    parser.add_argument("--feedback-mode", choices=("legacy", "stateful"), default="stateful")
    parser.add_argument(
        "--include-slow-explorers",
        action="store_true",
        help="include slow stateful explorers such as settlement attestation sequence analysis",
    )
    stateful_group = parser.add_mutually_exclusive_group()
    stateful_group.add_argument(
        "--stateful-exploration",
        dest="stateful_exploration",
        action="store_true",
        help="run the state-feedback explorer bundle alongside minimized witness refresh",
    )
    stateful_group.add_argument(
        "--no-stateful-exploration",
        dest="stateful_exploration",
        action="store_false",
        help="skip the state-feedback explorer bundle",
    )
    parser.set_defaults(stateful_exploration=None)
    args = parser.parse_args(argv)

    gate_path = _gate_path_for_lane(args.gate_lane)
    if not gate_path.is_file():
        raise CampaignError(f"missing gate: {gate_path.relative_to(REPO_ROOT)}")

    python_bin = _default_python()
    if args.plan and args.refresh_shared_index_only:
        parser.error("--plan cannot be combined with --refresh-shared-index-only")

    stateful_exploration = args.stateful_exploration
    if stateful_exploration is None:
        stateful_exploration = args.gate_lane == "deep"

    campaign_root = args.campaign_root
    if campaign_root is None and args.report_out is None:
        campaign_root = _default_campaign_root(args.gate_lane)

    if args.refresh_shared_index_only:
        report_out = args.report_out
    else:
        report_out = args.report_out or _default_report_path(
            campaign_root=campaign_root,
            gate_lane=args.gate_lane,
            timestamp_utc=args.timestamp_utc,
            run_id=args.run_id,
        )

    result: dict[str, Any] | None
    if args.refresh_shared_index_only:
        result = _refresh_only_result(campaign_root=campaign_root, fallback_report_out=report_out)
    else:
        result = None if args.plan else _run_gate(gate_path)

    artifacts = _campaign_artifact_paths(
        report_out=report_out,
        campaign_root=campaign_root,
        stateful_exploration=bool(stateful_exploration),
        target_manifest=args.target_manifest,
        include_slow_explorers=bool(args.include_slow_explorers),
    )
    if args.refresh_shared_index_only:
        if result is None:
            raise CampaignError("refresh_shared_index_only requires a result payload")
        artifacts.update(
            {
                "campaign_dir": None,
                "minimized_witness_dir": None,
                "minimized_witness_index_out": None,
                "stateful_report_dir": None,
                "introspection_out": None,
                "atlas_out": None,
                "surface_suggestions_out": None,
                "shared_minimized_witness_index_out": result["shared_minimized_witness_index_out"],
            }
        )

    if not args.plan and not args.refresh_shared_index_only and result and result["ok"] and report_out:
        witness_artifacts = _write_minimized_witness_artifacts(
            python_bin=python_bin,
            gate_lane=args.gate_lane,
            report_out=report_out,
            campaign_root=campaign_root,
        )
        artifacts.update(witness_artifacts)
        if stateful_exploration:
            if args.target_manifest is None:
                raise CampaignError("stateful exploration requires --target-manifest or the default manifest file")
            stateful_artifacts = _write_stateful_exploration_artifacts(
                python_bin=python_bin,
                report_out=report_out,
                feedback_mode=args.feedback_mode,
                target_manifest=args.target_manifest,
                target_id=args.target_id,
                include_slow_explorers=bool(args.include_slow_explorers),
                shared_minimized_witness_index_out=artifacts.get("shared_minimized_witness_index_out"),
            )
            artifacts.update(
                {
                    "stateful_report_dir": stateful_artifacts["stateful_report_dir"],
                    "introspection_out": stateful_artifacts["introspection_out"],
                    "atlas_out": stateful_artifacts["atlas_out"],
                    "surface_suggestions_out": stateful_artifacts["surface_suggestions_out"],
                    "guard_attribution_out": stateful_artifacts["guard_attribution_out"],
                    "target_manifest": stateful_artifacts["target_manifest"],
                }
            )
            result["stateful_exploration"] = stateful_artifacts

    payload = _payload(
        plan=bool(args.plan),
        python_bin=python_bin,
        gate_lane=args.gate_lane,
        gate_path=gate_path,
        report_out=report_out,
        campaign_root=campaign_root,
        result=result,
        artifacts=artifacts,
        stateful_exploration=bool(stateful_exploration),
        feedback_mode=args.feedback_mode,
        target_manifest=args.target_manifest,
        target_id=args.target_id,
        include_slow_explorers=bool(args.include_slow_explorers),
    )
    _write_report(report_out, payload)
    if args.format == "json":
        json.dump(payload, sys.stdout, indent=2, sort_keys=True)
        sys.stdout.write("\n")
    else:
        _print_text(payload)
    return 0 if result is None or result["ok"] else int(result["returncode"] or 1)


if __name__ == "__main__":  # pragma: no cover
    raise SystemExit(main())
