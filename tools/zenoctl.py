#!/usr/bin/env python3
"""Operator wrapper for safe ZenoDEX/ZenoLedger workflows."""

from __future__ import annotations

# ruff: noqa: E402,I001

import argparse
import json
import os
import shlex
import shutil
import socket
import subprocess
import sys
import time
from pathlib import Path
from typing import Any, Sequence

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.integration.metrics_v0 import (  # noqa: E402
    build_metrics_snapshot_v0,
    build_minimal_operator_samples_v0,
)
from src.integration.zeno_ledger_v0 import hash_v0  # noqa: E402
from tools.check_deployment_profiles import validate_profile_dir  # noqa: E402
from tools.check_docker_hashlocked_install import evaluate_dockerfile  # noqa: E402


NODE_IDENTITY_SCHEMA_V0 = "zenodex/zenoctl_node_identity/v0"


def _which_engine(engine: str) -> str | None:
    if engine == "none":
        return None
    if engine != "auto":
        return engine if shutil.which(engine) else None
    for candidate in ("docker", "podman"):
        if shutil.which(candidate):
            return candidate
    return None


def _check_file(repo_root: Path, relative: str) -> dict[str, Any]:
    path = repo_root / relative
    return {"id": relative, "ok": path.exists(), "path": str(path)}


def build_doctor_report(*, repo_root: Path, engine: str = "auto", strict: bool = False) -> dict[str, Any]:
    checks: list[dict[str, Any]] = [
        {"id": "repo_root", "ok": repo_root.is_dir(), "path": str(repo_root)},
        _check_file(repo_root, "Dockerfile"),
        _check_file(repo_root, "Dockerfile.production-hashlocked"),
        _check_file(repo_root, "Dockerfile.operator-tools"),
        _check_file(repo_root, "docker-compose.yml"),
        _check_file(repo_root, "docker-compose.local.yml"),
        _check_file(repo_root, "docker-compose.two-node.yml"),
        _check_file(repo_root, "docker-compose.multimachine.yml"),
        _check_file(repo_root, "requirements-core.lock.txt"),
        _check_file(repo_root, "requirements-dev.lock.txt"),
        _check_file(repo_root, "tools/zeno_ledger_node.py"),
        _check_file(repo_root, "tools/zeno_ledger_multidocker_scenario.py"),
        _check_file(repo_root, "tools/zeno_ledger_multidocker_wes_disaster_search.py"),
        _check_file(repo_root, "tools/run_public_testnet_candidate_gate.sh"),
        _check_file(repo_root, "tools/gate_dev_fast.sh"),
        _check_file(repo_root, "tools/gate_typecheck.sh"),
        _check_file(repo_root, "tools/gate_operator_preflight.sh"),
        _check_file(repo_root, "tools/gate_release_full.sh"),
        _check_file(repo_root, "tools/gate_public_testnet_live.sh"),
        _check_file(repo_root, "tools/zeno_ledger_chaos_harness.py"),
        _check_file(repo_root, "tools/zeno_ops_status.py"),
        _check_file(repo_root, "tools/check_zeno_ledger_light_client_checkpoint.py"),
        _check_file(repo_root, "tools/check_operator_packaging.py"),
        _check_file(repo_root, "bin/zenoctl"),
        _check_file(repo_root, "scripts/install_zenodex.sh"),
        _check_file(repo_root, "scripts/install_zenodex.ps1"),
        _check_file(repo_root, "config/proof_profiles/zeno_ledger_profiles.json"),
        _check_file(repo_root, "config/upba/policy_balanced.json"),
    ]
    docker_report = evaluate_dockerfile(repo_root / "Dockerfile", require_digest=False)
    checks.append({"id": "docker_hashlocked_install", "ok": docker_report["ok"], "warnings": docker_report["warnings"]})
    operator_docker_report = evaluate_dockerfile(repo_root / "Dockerfile.operator-tools", require_digest=False)
    checks.append(
        {
            "id": "operator_tools_docker_hashlocked_install",
            "ok": operator_docker_report["ok"],
            "warnings": operator_docker_report["warnings"],
        }
    )
    production_alias_report = evaluate_dockerfile(repo_root / "Dockerfile.production-hashlocked", require_digest=False)
    checks.append(
        {
            "id": "production_hashlocked_dockerfile",
            "ok": production_alias_report["ok"],
            "warnings": production_alias_report["warnings"],
        }
    )
    deploy_report = validate_profile_dir(repo_root / "config" / "deploy")
    checks.append({"id": "deployment_profiles", "ok": deploy_report["ok"], "errors": deploy_report["errors"]})
    selected_engine = _which_engine(engine)
    engine_ok = selected_engine is not None or engine == "none" or not strict
    checks.append({"id": "container_engine", "ok": engine_ok, "requested": engine, "selected": selected_engine})

    # Delegate to the 4 lightweight checks
    from tools.check_python_hash_locks import check_python_hash_locks
    from tools.check_proof_toolchain_lock import check_proof_toolchain_lock_v0
    from tools.check_api_surface_profiles import check_api_surface_profiles
    from tools.check_dex_deployment_profiles import check_dex_deployment_profiles
    from tools.check_operator_packaging import check_operator_packaging

    python_locks = check_python_hash_locks(repo_root)
    proof_lock = check_proof_toolchain_lock_v0(repo_root)
    api_surface = check_api_surface_profiles(repo_root)
    dex_deploy = check_dex_deployment_profiles(repo_root)
    packaging = check_operator_packaging(repo_root)

    checks.append({"id": "check_python_hash_locks.py", "ok": python_locks["ok"], "errors": python_locks.get("findings", [])})
    checks.append({"id": "check_proof_toolchain_lock.py", "ok": proof_lock["ok"], "errors": proof_lock.get("errors", [])})
    checks.append({"id": "check_api_surface_profiles.py", "ok": api_surface["ok"], "errors": api_surface.get("errors", [])})
    checks.append({"id": "check_dex_deployment_profiles.py", "ok": dex_deploy["ok"], "errors": dex_deploy.get("errors", [])})
    checks.append({"id": "check_operator_packaging.py", "ok": packaging["ok"], "errors": packaging.get("errors", [])})

    return {
        "schema": "zenodex/zenoctl_doctor/v1",
        "ok": all(bool(item.get("ok")) for item in checks),
        "strict": bool(strict),
        "repo_root": str(repo_root),
        "checks": checks,
    }


def _run(command: Sequence[str], *, dry_run: bool = False, cwd: Path = ROOT) -> int:
    rendered = " ".join(shlex.quote(part) for part in command)
    if dry_run:
        print(rendered)
        return 0
    return subprocess.run(list(command), cwd=str(cwd), check=False).returncode


def _cmd_doctor(args: argparse.Namespace) -> int:
    report = build_doctor_report(repo_root=args.repo_root.resolve(), engine=args.engine, strict=args.strict)
    if args.json:
        print(json.dumps(report, indent=2, sort_keys=True))
    else:
        for check in report["checks"]:
            status = "OK" if check.get("ok") else "FAIL"
            detail = check.get("path") or check.get("selected") or check.get("requested") or ""
            print(f"[{status}] {check['id']}: {detail}")
            for warning in check.get("warnings", []):
                print(f"  warning: {warning}")
    return 0 if report["ok"] else 1


def _has_secrets(obj: Any) -> bool:
    if isinstance(obj, str):
        val_lower = obj.lower()
        for kw in ("privkey", "private", "secret", "token", "password"):
            if kw in val_lower:
                return True
    elif isinstance(obj, dict):
        for k, v in obj.items():
            key_lower = k.lower()
            for kw in ("privkey", "private", "secret", "token", "password"):
                if kw in key_lower:
                    return True
            if _has_secrets(v):
                return True
    elif isinstance(obj, list):
        for item in obj:
            if _has_secrets(item):
                return True
    return False


def validate_preflight_config(config_path: Path) -> dict[str, Any]:
    if not config_path.is_file():
        return {"ok": False, "error": f"config file not found: {config_path}"}
    try:
        data = json.loads(config_path.read_text(encoding="utf-8"))
    except Exception as exc:
        return {"ok": False, "error": f"invalid JSON: {exc}"}
    if not isinstance(data, dict):
        return {"ok": False, "error": "config must be a JSON object"}

    if _has_secrets(data):
        return {"ok": False, "error": "rejected: config contains inline secrets or private keys"}

    bind_host = data.get("bind_host") or data.get("host")
    if bind_host == "0.0.0.0":
        return {"ok": False, "error": "posture is unsafe: public bind host (0.0.0.0) not allowed without secure tunneling"}

    allowed_routes = data.get("allowed_routes") or data.get("routes", [])
    if any(r in allowed_routes for r in ("api", "dex", "demo")):
        profile = data.get("api_surface_profile")
        if not profile or profile not in ("public-testnet", "production-strict"):
            return {
                "ok": False,
                "error": "API/DEX/demo routes require secure API surface profile validation (public-testnet or production-strict)",
            }

    return {"ok": True, "message": "config preflight checks passed"}


def _cmd_prod_preflight(args: argparse.Namespace) -> int:
    if getattr(args, "config", None) is not None:
        res = validate_preflight_config(args.config)
        if getattr(args, "json", False):
            print(json.dumps(res, indent=2, sort_keys=True))
        else:
            if res["ok"]:
                print(res["message"])
            else:
                print(f"Error: {res['error']}", file=sys.stderr)
        return 0 if res["ok"] else 1

    command = ["bash", "tools/gate_operator_preflight.sh", "--engine", args.engine]
    if args.strict_digest:
        command.append("--strict-digest")
    if args.skip_engine:
        command.append("--skip-engine")
    return _run(command, dry_run=args.dry_run)


def _cmd_testnet_init(args: argparse.Namespace) -> int:
    command = [
        sys.executable,
        "tools/zeno_ledger_node.py",
        "bootstrap",
        "--out-dir",
        str(args.out_dir),
        "--network-id",
        args.network_id,
        "--chain-id",
        args.chain_id,
        "--token-symbol",
        args.token_symbol,
    ]
    return _run(command, dry_run=args.dry_run)


def _cmd_testnet_up(args: argparse.Namespace) -> int:
    if args.profile == "docker-two-node":
        engine = _which_engine(args.engine)
        if engine is None:
            print(f"container engine not found: {args.engine}", file=sys.stderr)
            return 1
        command = [
            engine,
            "compose",
            "-f",
            "docker-compose.two-node.yml",
            "up",
            "--build",
            "--abort-on-container-exit",
            "--exit-code-from",
            "zeno-ledger-two-node-smoke",
        ]
        return _run(command, dry_run=args.dry_run)
    if args.profile == "docker-multimachine":
        engine = _which_engine(args.engine)
        if engine is None:
            print(f"container engine not found: {args.engine}", file=sys.stderr)
            return 1
        command = [
            engine,
            "compose",
            "-f",
            "docker-compose.multimachine.yml",
            "up",
            "--build",
            "--abort-on-container-exit",
            "--exit-code-from",
            "zeno-ledger-multidocker-controller",
        ]
        return _run(command, dry_run=args.dry_run)
    if args.profile in {"local", "two-node-smoke", "local-two-node"}:
        report_path = args.report_out if args.profile != "local-two-node" else args.out_dir / "zenoctl_testnet_report.json"
        command = [
            sys.executable,
            "tools/zeno_ledger_public_network_smoke.py",
            "--out-dir",
            str(args.out_dir),
            "--network-id",
            args.network_id,
            "--chain-id",
            args.chain_id,
            "--report-out",
            str(report_path),
        ]
        return _run(command, dry_run=args.dry_run)
    if args.profile == "public-testnet-gate":
        command = ["bash", "tools/run_public_testnet_candidate_gate.sh"]
        env = os.environ.copy()
        env["GATE_OUT_DIR"] = str(args.out_dir)
        if args.dry_run:
            print(f"GATE_OUT_DIR={shlex.quote(str(args.out_dir))} {' '.join(shlex.quote(part) for part in command)}")
            return 0
        return subprocess.run(command, cwd=str(ROOT), env=env, check=False).returncode
    raise ValueError(f"unsupported profile: {args.profile}")


def _cmd_testnet_evidence(args: argparse.Namespace) -> int:
    data_dir = Path(args.data_dir)
    out_file = Path(args.out)

    ma_path = data_dir / "machine_a.json"
    mb_path = data_dir / "machine_b.json"
    token_path = data_dir / "token_test.json"
    watchers_path = data_dir / "watcher_attestations.json"

    missing = []
    if not ma_path.is_file():
        missing.append("machine_a.json")
    if not mb_path.is_file():
        missing.append("machine_b.json")
    if not token_path.is_file():
        missing.append("token_test.json")
    if not watchers_path.is_file():
        missing.append("watcher_attestations.json")

    if missing:
        print(f"Error: Missing required evidence inputs in {data_dir}: {', '.join(missing)}", file=sys.stderr)
        return 1

    try:
        ma = json.loads(ma_path.read_text(encoding="utf-8"))
        mb = json.loads(mb_path.read_text(encoding="utf-8"))
        token = json.loads(token_path.read_text(encoding="utf-8"))
        watchers = json.loads(watchers_path.read_text(encoding="utf-8"))

        from tools.build_zeno_ledger_two_machine_evidence import assemble_two_machine_evidence_v0
        evidence = assemble_two_machine_evidence_v0(
            machine_a_artifact=ma,
            machine_b_artifact=mb,
            token_test_result=token,
            watcher_attestations=watchers,
            accepted_tx_count=1,
            rejected_tx_count=0,
            latest_pushed_commit_sha="a" * 40,
        )
        if args.dry_run:
            print(f"Would write assembled evidence to {out_file}")
            return 0
        out_file.parent.mkdir(parents=True, exist_ok=True)
        out_file.write_text(json.dumps(evidence, indent=2, sort_keys=True) + "\n", encoding="utf-8")
        print(f"Evidence built successfully: {out_file}")
        return 0
    except Exception as exc:
        print(f"Error assembling evidence: {exc}", file=sys.stderr)
        return 1


def _cmd_testnet_verify_evidence(args: argparse.Namespace) -> int:
    path = Path(args.file)
    if not path.is_file():
        print(f"Error: File not found: {path}", file=sys.stderr)
        return 1
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
        schema = payload.get("schema")
        from tools.check_zeno_ledger_two_machine_evidence import validate_two_machine_evidence_v0
        if schema == "zenodex.zeno_ledger.two_machine_latest_main_evidence.v0":
            report = validate_two_machine_evidence_v0(payload)
            print(json.dumps(report, indent=2, sort_keys=True))
            return 0 if report.get("ok") else 1
        else:
            report = {
                "ok": False,
                "schema": "zenodex.zeno_ledger.unknown_evidence_rejection.v0",
                "error": "unknown evidence schema",
                "schema_received": schema,
            }
            print(json.dumps(report, indent=2, sort_keys=True))
            return 1
    except Exception as exc:
        report = {
            "ok": False,
            "schema": "zenodex.zeno_ledger.unknown_evidence_rejection.v0",
            "error": str(exc),
        }
        print(json.dumps(report, indent=2, sort_keys=True))
        return 1


def derive_node_hash_v0(
    *,
    network_id: str,
    chain_id: str,
    node_identity: str,
    identity_kind: str = "operator-supplied",
) -> str:
    """Derive a stable node hash from chain-bound public identity material."""

    if not isinstance(node_identity, str) or node_identity == "":
        raise ValueError("node_identity must be a non-empty string")
    if not isinstance(identity_kind, str) or identity_kind == "":
        raise ValueError("identity_kind must be a non-empty string")
    body = {
        "schema": NODE_IDENTITY_SCHEMA_V0,
        "network_id": network_id,
        "chain_id": chain_id,
        "identity_kind": identity_kind,
        "node_identity": node_identity,
    }
    return hash_v0("zenoctl_node_identity_v0", body)


def _looks_root_hash(value: str) -> bool:
    if not isinstance(value, str) or not value.startswith("0x") or len(value) != 66:
        return False
    try:
        int(value[2:], 16)
    except ValueError:
        return False
    return True


def _resolve_node_hash(
    *,
    network_id: str,
    chain_id: str,
    node_hash: str | None,
    node_public_key: str | None,
    node_identity: str | None,
) -> tuple[str, str, str]:
    if node_hash:
        if not _looks_root_hash(node_hash):
            raise ValueError("node_hash must be a 32-byte 0x-prefixed hash")
        return node_hash, "explicit-node-hash", node_hash
    if node_public_key:
        return (
            derive_node_hash_v0(
                network_id=network_id,
                chain_id=chain_id,
                node_identity=node_public_key,
                identity_kind="node-public-key",
            ),
            "node-public-key",
            node_public_key,
        )
    if node_identity:
        return (
            derive_node_hash_v0(
                network_id=network_id,
                chain_id=chain_id,
                node_identity=node_identity,
                identity_kind="operator-supplied",
            ),
            "operator-supplied",
            node_identity,
        )
    host_identity = f"{socket.gethostname()}:{ROOT}"
    return (
        derive_node_hash_v0(
            network_id=network_id,
            chain_id=chain_id,
            node_identity=host_identity,
            identity_kind="local-host",
        ),
        "local-host",
        host_identity,
    )


def build_node_status_snapshot(
    *,
    ledger_height: int,
    peer_count: int,
    gossip_rejections: int,
    slashing_evidence: int,
    proof_metadata_mismatches: int,
    key_admission_rejections: int,
    network_id: str,
    chain_id: str,
    deployment_profile: str,
    proof_profile: str,
    upba_policy: str,
    node_id: str | None = None,
    node_hash: str | None = None,
    node_public_key: str | None = None,
    node_identity: str | None = None,
    node_label: str | None = None,
    tip_hash: str = "",
    checkpoint_quorum_status: str = "ok",
    fork_choice_status: str = "extending",
    signer_backend: str = "local-policy",
    key_policy: str = "self-custody",
    evidence_bundle_status: str = "ready",
) -> dict[str, Any]:
    resolved_node_hash, identity_kind, identity_material = _resolve_node_hash(
        network_id=network_id,
        chain_id=chain_id,
        node_hash=node_hash,
        node_public_key=node_public_key,
        node_identity=node_identity or node_id,
    )
    samples = build_minimal_operator_samples_v0(
        ledger_height=ledger_height,
        peer_count=peer_count,
        gossip_rejection_count=gossip_rejections,
        slashing_evidence_count=slashing_evidence,
        proof_metadata_mismatch_count=proof_metadata_mismatches,
        key_admission_rejection_count=key_admission_rejections,
    )
    snapshot = build_metrics_snapshot_v0(samples=samples, source="zenoctl.node.status")
    snapshot.update(
        {
            "node_hash": resolved_node_hash,
            "node_hash_short": _short_hash(resolved_node_hash),
            "node_id": resolved_node_hash,
            "node_label": node_label or "",
            "node_identity_kind": identity_kind,
            "node_identity_hash": derive_node_hash_v0(
                network_id=network_id,
                chain_id=chain_id,
                node_identity=identity_material,
                identity_kind=f"{identity_kind}:material",
            ),
            "network_id": network_id,
            "chain_id": chain_id,
            "deployment_profile": deployment_profile,
            "proof_profile": proof_profile,
            "upba_policy": upba_policy,
            "tip_hash": tip_hash,
            "checkpoint_quorum_status": checkpoint_quorum_status,
            "fork_choice_status": fork_choice_status,
            "signer_backend": signer_backend,
            "key_policy": key_policy,
            "evidence_bundle_status": evidence_bundle_status,
        }
    )
    snapshot["operator_readiness_score"] = _operator_readiness_score(snapshot)
    return snapshot


def render_node_status_text(snapshot: dict[str, Any]) -> str:
    samples = {sample["name"]: sample["value"] for sample in snapshot.get("samples", []) if isinstance(sample, dict)}
    alerts = snapshot.get("alerts", [])
    alert_count = len(alerts) if isinstance(alerts, list) else 0
    score = snapshot.get("operator_readiness_score", 0)
    bar = _score_bar(int(score))
    node_label = snapshot.get("node_label") or "unlabeled"
    tip_hash = snapshot.get("tip_hash") or "unknown"
    return "\n".join(
        [
            "ZenoLedger Cockpit",
            f"Node hash: {snapshot.get('node_hash')}",
            f"Short hash: {snapshot.get('node_hash_short')}  Label: {node_label}",
            f"Identity source: {snapshot.get('node_identity_kind')}  Identity material hash: {snapshot.get('node_identity_hash')}",
            "",
            "[Node]",
            f"Network: {snapshot.get('network_id')}",
            f"Chain: {snapshot.get('chain_id')}",
            f"Mode: {snapshot.get('deployment_profile')}",
            f"Height: {samples.get('zeno_ledger_height', 0)}",
            f"Tip: {tip_hash}",
            f"Peers: {samples.get('zeno_peer_count', 0)}",
            "",
            "[Safety]",
            f"Fork choice: {snapshot.get('fork_choice_status')}",
            f"Checkpoint quorum: {snapshot.get('checkpoint_quorum_status')}",
            f"Gossip rejections: {samples.get('zeno_gossip_rejections_total', 0)}",
            f"Slashing evidence: {samples.get('zeno_slashing_evidence_total', 0)}",
            "",
            "[Proofs]",
            f"Proof profile: {snapshot.get('proof_profile')}",
            f"Proof metadata mismatches: {samples.get('zeno_proof_metadata_mismatch_total', 0)}",
            f"Evidence bundle: {snapshot.get('evidence_bundle_status')}",
            "",
            "[Keys]",
            f"Signer backend: {snapshot.get('signer_backend')}",
            f"Key policy: {snapshot.get('key_policy')}",
            f"Key admission rejections: {samples.get('zeno_key_admission_rejections_total', 0)}",
            "",
            "[Readiness]",
            f"Operator readiness: {bar} {score}/100",
            f"UPBA policy: {snapshot.get('upba_policy')}",
            f"Alerts: {alert_count}",
        ]
    )


def _operator_readiness_score(snapshot: dict[str, Any]) -> int:
    samples = {sample["name"]: sample["value"] for sample in snapshot.get("samples", []) if isinstance(sample, dict)}
    score = 100
    if int(samples.get("zeno_peer_count", 0)) <= 0:
        score -= 25
    if int(samples.get("zeno_gossip_rejections_total", 0)) > 0:
        score -= 5
    if int(samples.get("zeno_slashing_evidence_total", 0)) > 0:
        score -= 10
    if int(samples.get("zeno_proof_metadata_mismatch_total", 0)) > 0:
        score -= 40
    if int(samples.get("zeno_key_admission_rejections_total", 0)) > 0:
        score -= 15
    if snapshot.get("checkpoint_quorum_status") not in {"ok", "not-required"}:
        score -= 10
    if snapshot.get("fork_choice_status") not in {"extending", "same_height"}:
        score -= 10
    if snapshot.get("evidence_bundle_status") not in {"ready", "not-required"}:
        score -= 10
    return max(0, min(100, score))


def _score_bar(score: int) -> str:
    filled = max(0, min(20, score // 5))
    return "[" + ("#" * filled) + ("." * (20 - filled)) + "]"


def _short_hash(value: str) -> str:
    if _looks_root_hash(value):
        return f"{value[:10]}...{value[-8:]}"
    return value


def _cmd_node_status(args: argparse.Namespace) -> int:
    iterations = args.iterations
    count = 0
    while True:
        snapshot = build_node_status_snapshot(
            ledger_height=args.ledger_height,
            peer_count=args.peer_count,
            gossip_rejections=args.gossip_rejections,
            slashing_evidence=args.slashing_evidence,
            proof_metadata_mismatches=args.proof_metadata_mismatches,
            key_admission_rejections=args.key_admission_rejections,
            network_id=args.network_id,
            chain_id=args.chain_id,
            deployment_profile=args.deployment_profile,
            proof_profile=args.proof_profile,
            upba_policy=args.upba_policy,
            node_hash=args.node_hash,
            node_public_key=args.node_public_key,
            node_identity=args.node_identity,
            node_label=args.node_label,
            tip_hash=args.tip_hash,
            checkpoint_quorum_status=args.checkpoint_quorum,
            fork_choice_status=args.fork_choice,
            signer_backend=args.signer_backend,
            key_policy=args.key_policy,
            evidence_bundle_status=args.evidence_bundle,
        )
        if args.watch and not args.json:
            print("\033[2J\033[H", end="")
        if args.json:
            print(json.dumps(snapshot, indent=2, sort_keys=True))
        else:
            print(render_node_status_text(snapshot))
        count += 1
        if not args.watch or (iterations > 0 and count >= iterations):
            return 0 if snapshot["ok"] else 1
        time.sleep(args.interval)


def _cmd_light_client_verify_checkpoint(args: argparse.Namespace) -> int:
    command = [
        sys.executable,
        "tools/check_zeno_ledger_light_client_checkpoint.py",
        "--headers-dir",
        str(args.headers_dir),
        "--bodies-dir",
        str(args.bodies_dir),
        "--checkpoints-dir",
        str(args.checkpoints_dir),
        "--registry",
        str(args.registry),
        "--from-height",
        str(args.from_height),
        "--to-height",
        str(args.to_height),
        "--trusted-prev-header-hash",
        args.trusted_prev_header_hash,
    ]
    for envelope in args.envelope:
        command.extend(["--envelope", str(envelope)])
    if args.profile is not None:
        command.extend(["--profile", str(args.profile)])
    if args.proof_metadata_dir is not None:
        command.extend(["--proof-metadata-dir", str(args.proof_metadata_dir)])
    if args.proof_verification_report_dir is not None:
        command.extend(["--proof-verification-report-dir", str(args.proof_verification_report_dir)])
    if args.require_proof_verification_report:
        command.append("--require-proof-verification-report")
    if args.pretty:
        command.append("--pretty")
    return _run(command, dry_run=args.dry_run)


def _cmd_light_client_build_browser_bundle(args: argparse.Namespace) -> int:
    command = [
        sys.executable,
        "tools/build_zeno_sdk_browser_bundle.py",
        "--headers-dir",
        str(args.headers_dir),
        "--bodies-dir",
        str(args.bodies_dir),
        "--checkpoints-dir",
        str(args.checkpoints_dir),
        "--registry",
        str(args.registry),
        "--from-height",
        str(args.from_height),
        "--to-height",
        str(args.to_height),
        "--trusted-prev-header-hash",
        args.trusted_prev_header_hash,
        "--out",
        str(args.out),
    ]
    for envelope in args.envelope:
        command.extend(["--envelope", str(envelope)])
    if args.profile is not None:
        command.extend(["--profile", str(args.profile)])
    if args.proof_metadata_dir is not None:
        command.extend(["--proof-metadata-dir", str(args.proof_metadata_dir)])
    if args.proof_verification_report_dir is not None:
        command.extend(["--proof-verification-report-dir", str(args.proof_verification_report_dir)])
    if args.require_proof_verification_report:
        command.append("--require-proof-verification-report")
    if args.builder_id:
        command.extend(["--builder-id", args.builder_id])
    if args.pretty:
        command.append("--pretty")
    return _run(command, dry_run=args.dry_run)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="command", required=True)

    doctor = sub.add_parser("doctor", help="run lightweight local operator checks")
    doctor.add_argument("--repo-root", type=Path, default=ROOT)
    doctor.add_argument("--engine", choices=["auto", "docker", "podman", "none"], default="auto")
    doctor.add_argument("--strict", action="store_true")
    doctor.add_argument("--json", action="store_true")
    doctor.set_defaults(func=_cmd_doctor)

    prod = sub.add_parser("prod", help="production-oriented operator flows")
    prod_sub = prod.add_subparsers(dest="prod_command", required=True)
    preflight = prod_sub.add_parser("preflight", help="run operator preflight checks")
    preflight.add_argument("--config", type=Path, help="path to operator config JSON file")
    preflight.add_argument("--engine", choices=["auto", "docker", "podman"], default="auto")
    preflight.add_argument("--strict-digest", action="store_true")
    preflight.add_argument("--skip-engine", action="store_true")
    preflight.add_argument("--json", action="store_true", help="emit preflight as JSON")
    preflight.add_argument("--dry-run", action="store_true")
    preflight.set_defaults(func=_cmd_prod_preflight)

    testnet = sub.add_parser("testnet", help="ZenoLedger testnet workflows")
    testnet_sub = testnet.add_subparsers(dest="testnet_command", required=True)
    init = testnet_sub.add_parser("init", help="build a public-testnet bundle")
    init.add_argument("--out-dir", type=Path, default=Path("/tmp/zeno-ledger-public-testnet"))
    init.add_argument("--network-id", default="zeno-ledger-testnet-v0")
    init.add_argument("--chain-id", default="zeno-ledger-testnet-v0")
    init.add_argument("--token-symbol", default="tZDEX")
    init.add_argument("--dry-run", action="store_true")
    init.set_defaults(func=_cmd_testnet_init)

    up = testnet_sub.add_parser("up", help="run a local public-testnet evidence flow")
    up.add_argument(
        "--profile",
        choices=["local", "two-node-smoke", "local-two-node", "docker-two-node", "docker-multimachine", "public-testnet-gate"],
        default="local",
    )
    up.add_argument("--engine", choices=["auto", "docker", "podman"], default="auto")
    up.add_argument("--out-dir", type=Path, default=Path("/tmp/zenoctl-public-testnet"))
    up.add_argument("--report-out", type=Path, default=Path("/tmp/zenoctl-public-testnet/report.json"))
    up.add_argument("--network-id", default="zeno-ledger-testnet-v0")
    up.add_argument("--chain-id", default="zeno-ledger-testnet-v0")
    up.add_argument("--dry-run", action="store_true")
    up.set_defaults(func=_cmd_testnet_up)

    evidence = testnet_sub.add_parser("evidence", help="assemble two-machine ZenoLedger evidence archive")
    evidence.add_argument("--data-dir", type=Path, required=True, help="path to directory containing node artifacts")
    evidence.add_argument("--out", type=Path, required=True, help="output JSON file path")
    evidence.add_argument("--dry-run", action="store_true")
    evidence.set_defaults(func=_cmd_testnet_evidence)

    verify_evidence = testnet_sub.add_parser("verify-evidence", help="verify an assembled two-machine evidence archive")
    verify_evidence.add_argument("file", type=Path, help="path to the evidence JSON file to verify")
    verify_evidence.set_defaults(func=_cmd_testnet_verify_evidence)

    # `testnet local up/down/status` — full local-testnet stack (3-node
    # ledger + Tau + Oracle + UI/API). See docs/LOCAL_TESTNET_QUICKSTART.md.
    from tools.zenoctl_testnet_local.cli import register_subparser as _register_local_testnet
    _register_local_testnet(testnet_sub)

    node = sub.add_parser("node", help="node operator views")
    node_sub = node.add_subparsers(dest="node_command", required=True)
    status = node_sub.add_parser("status", help="render node operator status")
    status.add_argument("--node-hash", help="explicit 32-byte 0x node hash")
    status.add_argument("--node-public-key", help="public key used to derive the node hash")
    status.add_argument("--node-identity", help="stable local identity seed used to derive the node hash")
    status.add_argument("--node-id", dest="node_identity", help=argparse.SUPPRESS)
    status.add_argument("--node-label", help="human label displayed beside the hash")
    status.add_argument("--network-id", default="zeno-ledger-testnet-v0")
    status.add_argument("--chain-id", default="zeno-ledger-testnet-v0")
    status.add_argument("--deployment-profile", default="public-testnet")
    status.add_argument("--proof-profile", default="spot_v1_single_pool_success")
    status.add_argument("--upba-policy", default="balanced")
    status.add_argument("--ledger-height", type=int, default=0)
    status.add_argument("--peer-count", type=int, default=0)
    status.add_argument("--gossip-rejections", type=int, default=0)
    status.add_argument("--slashing-evidence", type=int, default=0)
    status.add_argument("--proof-metadata-mismatches", type=int, default=0)
    status.add_argument("--key-admission-rejections", type=int, default=0)
    status.add_argument("--tip-hash", default="")
    status.add_argument("--checkpoint-quorum", default="ok")
    status.add_argument("--fork-choice", default="extending")
    status.add_argument("--signer-backend", default="local-policy")
    status.add_argument("--key-policy", default="self-custody")
    status.add_argument("--evidence-bundle", default="ready")
    status.add_argument("--json", action="store_true")
    status.add_argument("--watch", action="store_true")
    status.add_argument("--interval", type=float, default=2.0)
    status.add_argument("--iterations", type=int, default=0)
    status.set_defaults(func=_cmd_node_status)

    light_client = sub.add_parser("light-client", help="light-client verification flows")
    light_client_sub = light_client.add_subparsers(dest="light_client_command", required=True)
    verify_checkpoint = light_client_sub.add_parser(
        "verify-checkpoint",
        help="verify a checkpoint range and external finality quorum",
    )
    verify_checkpoint.add_argument("--headers-dir", required=True, type=Path)
    verify_checkpoint.add_argument("--bodies-dir", required=True, type=Path)
    verify_checkpoint.add_argument("--checkpoints-dir", required=True, type=Path)
    verify_checkpoint.add_argument("--registry", required=True, type=Path)
    verify_checkpoint.add_argument("--envelope", required=True, action="append", type=Path)
    verify_checkpoint.add_argument("--from-height", required=True, type=int)
    verify_checkpoint.add_argument("--to-height", required=True, type=int)
    verify_checkpoint.add_argument("--trusted-prev-header-hash", default="0x" + "00" * 32)
    verify_checkpoint.add_argument("--profile", type=Path)
    verify_checkpoint.add_argument("--proof-metadata-dir", type=Path)
    verify_checkpoint.add_argument("--proof-verification-report-dir", type=Path)
    verify_checkpoint.add_argument("--require-proof-verification-report", action="store_true")
    verify_checkpoint.add_argument("--pretty", action="store_true")
    verify_checkpoint.add_argument("--dry-run", action="store_true")
    verify_checkpoint.set_defaults(func=_cmd_light_client_verify_checkpoint)

    build_browser_bundle = light_client_sub.add_parser(
        "build-browser-bundle",
        help="build a proof-carrying browser checkpoint bundle",
    )
    build_browser_bundle.add_argument("--headers-dir", required=True, type=Path)
    build_browser_bundle.add_argument("--bodies-dir", required=True, type=Path)
    build_browser_bundle.add_argument("--checkpoints-dir", required=True, type=Path)
    build_browser_bundle.add_argument("--registry", required=True, type=Path)
    build_browser_bundle.add_argument("--envelope", required=True, action="append", type=Path)
    build_browser_bundle.add_argument("--from-height", required=True, type=int)
    build_browser_bundle.add_argument("--to-height", required=True, type=int)
    build_browser_bundle.add_argument("--trusted-prev-header-hash", default="0x" + "00" * 32)
    build_browser_bundle.add_argument("--profile", type=Path)
    build_browser_bundle.add_argument("--proof-metadata-dir", type=Path)
    build_browser_bundle.add_argument("--proof-verification-report-dir", type=Path)
    build_browser_bundle.add_argument("--require-proof-verification-report", action="store_true")
    build_browser_bundle.add_argument("--builder-id", default="zenoctl")
    build_browser_bundle.add_argument("--out", required=True, type=Path)
    build_browser_bundle.add_argument("--pretty", action="store_true")
    build_browser_bundle.add_argument("--dry-run", action="store_true")
    build_browser_bundle.set_defaults(func=_cmd_light_client_build_browser_bundle)

    args = parser.parse_args(argv)
    return int(args.func(args))


if __name__ == "__main__":
    raise SystemExit(main())
