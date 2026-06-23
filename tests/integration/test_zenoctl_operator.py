from __future__ import annotations

import io
import json
import tarfile
from pathlib import Path

import pytest

from tools import zenoctl
from tools.check_deployment_profiles import validate_deployment_profile, validate_profile_dir
from tools.check_docker_hashlocked_install import evaluate_dockerfile
from tools.zeno_ledger_multidocker_scenario import (
    _extract_bundle_archive,
    _write_bundle_archive,
    build_multidocker_plan_v0,
)


def test_current_dockerfile_uses_hashlocked_runtime_install() -> None:
    report = evaluate_dockerfile(Path("Dockerfile"))

    assert report["ok"] is True
    assert report["checks"]["copies_runtime_lock"] is True
    assert report["checks"]["uses_require_hashes"] is True
    assert report["checks"]["does_not_install_unlocked_runtime_requirements"] is True


def test_operator_tools_dockerfile_uses_hashlocked_runtime_install() -> None:
    report = evaluate_dockerfile(Path("Dockerfile.operator-tools"))

    assert report["ok"] is True
    assert report["checks"]["copies_runtime_lock"] is True
    assert report["checks"]["uses_require_hashes"] is True


def test_production_hashlocked_dockerfile_uses_hashlocked_runtime_install() -> None:
    report = evaluate_dockerfile(Path("Dockerfile.production-hashlocked"))

    assert report["ok"] is True
    assert report["checks"]["copies_runtime_lock"] is True
    assert report["checks"]["uses_require_hashes"] is True


def test_dockerfile_check_rejects_unlocked_requirements(tmp_path: Path) -> None:
    dockerfile = tmp_path / "Dockerfile"
    dockerfile.write_text(
        "\n".join(
            [
                "FROM python:3.11-slim-bookworm",
                "COPY requirements-core.txt ./",
                "RUN python -m pip install -r requirements-core.txt",
            ]
        ),
        encoding="utf-8",
    )

    report = evaluate_dockerfile(dockerfile)

    assert report["ok"] is False
    assert report["checks"]["copies_runtime_lock"] is False
    assert report["checks"]["uses_require_hashes"] is False
    assert report["checks"]["does_not_install_unlocked_runtime_requirements"] is False


def test_dockerfile_check_can_require_digest_pinning(tmp_path: Path) -> None:
    dockerfile = tmp_path / "Dockerfile"
    dockerfile.write_text(
        "\n".join(
            [
                "FROM python:3.11-slim-bookworm",
                "COPY requirements-core.lock.txt ./",
                "RUN python -m pip install --require-hashes -r requirements-core.lock.txt",
            ]
        ),
        encoding="utf-8",
    )

    report = evaluate_dockerfile(dockerfile, require_digest=True)

    assert report["ok"] is False
    assert report["checks"]["base_images_pinned_by_digest"] is False
    assert report["warnings"] == ["base_images_not_pinned_by_digest"]


def test_zenoctl_doctor_passes_static_repo_checks_without_engine_requirement() -> None:
    report = zenoctl.build_doctor_report(repo_root=Path.cwd(), engine="none", strict=True)

    assert report["ok"] is True
    checks = {item["id"]: item for item in report["checks"]}
    assert checks["Dockerfile"]["ok"] is True
    assert checks["docker_hashlocked_install"]["ok"] is True
    assert checks["operator_tools_docker_hashlocked_install"]["ok"] is True
    assert checks["production_hashlocked_dockerfile"]["ok"] is True
    assert checks["deployment_profiles"]["ok"] is True
    assert checks["docker-compose.multimachine.yml"]["ok"] is True
    assert checks["docker-compose.testnet-demo.yml"]["ok"] is True
    assert checks["tools/zeno_ledger_multidocker_scenario.py"]["ok"] is True
    assert checks["tools/zeno_ledger_multidocker_wes_disaster_search.py"]["ok"] is True
    assert checks["tools/gate_typecheck.sh"]["ok"] is True
    assert checks["tools/gate_operator_preflight.sh"]["ok"] is True


def test_deployment_profiles_accept_default_profile_dir() -> None:
    report = validate_profile_dir(Path("config/deploy"))

    assert report["ok"] is True
    assert {item["profile_id"] for item in report["profiles"]} >= {
        "local-dev",
        "public-testnet",
        "production-strict",
    }


def test_deployment_profiles_reject_raw_keys_in_production() -> None:
    profile = {
        "schema": "zenodex/deployment_profile/v1",
        "profile_id": "production-strict",
        "threat_model": "bad",
        "allowed_routes": ["health"],
        "required_auth": {"write_api": "signed"},
        "key_policy": {
            "raw_private_key_flags_allowed": True,
            "production_key_receipts_required": True,
        },
        "proof_policy": {"proof_metadata_required": True},
        "upba_policy": "conservative",
        "peer_policy": {"dynamic_peer_cap_required": True},
        "gossip_policy": {"transport_auth_required": True},
        "observability_policy": {"metrics_required": True},
    }

    report = validate_deployment_profile(profile)

    assert report["ok"] is False
    assert "production-strict must reject raw private key flags" in report["errors"]


def test_deployment_profiles_reject_unknown_allowed_route() -> None:
    profile = {
        "schema": "zenodex/deployment_profile/v1",
        "profile_id": "public-testnet",
        "threat_model": "bad",
        "allowed_routes": ["health", "local_demo_typo"],
        "required_auth": {"write_api": "signed"},
        "key_policy": {
            "raw_private_key_flags_allowed": False,
            "production_key_receipts_required": False,
        },
        "proof_policy": {"proof_metadata_required": True},
        "upba_policy": "balanced",
        "peer_policy": {"dynamic_peer_cap_required": True},
        "gossip_policy": {"transport_auth_required": True},
        "observability_policy": {"metrics_required": True},
    }

    report = validate_deployment_profile(profile)

    assert report["ok"] is False
    assert "allowed_routes contains unknown routes: ['local_demo_typo']" in report["errors"]


def test_deployment_profiles_reject_unknown_top_level_key() -> None:
    profile = {
        "schema": "zenodex/deployment_profile/v1",
        "profile_id": "public-testnet",
        "threat_model": "bad",
        "allowed_routes": ["health"],
        "required_auth": {"write_api": "signed"},
        "key_policy": {
            "raw_private_key_flags_allowed": False,
            "production_key_receipts_required": False,
        },
        "proof_policy": {"proof_metadata_required": True},
        "upba_policy": "balanced",
        "peer_policy": {"dynamic_peer_cap_required": True},
        "gossip_policy": {"transport_auth_required": True},
        "observability_policy": {"metrics_required": True},
        "runtime_polciy": {"local_only_routes_allowed": False},
    }

    report = validate_deployment_profile(profile)

    assert report["ok"] is False
    assert "profile has unknown top-level keys: ['runtime_polciy']" in report["errors"]


def test_zenoctl_testnet_init_dry_run(capsys) -> None:
    rc = zenoctl.main(
        [
            "testnet",
            "init",
            "--out-dir",
            "/tmp/zenoctl-test",
            "--network-id",
            "n",
            "--chain-id",
            "c",
            "--dry-run",
        ]
    )

    assert rc == 0
    output = capsys.readouterr().out
    assert "tools/zeno_ledger_node.py" in output
    assert "bootstrap" in output
    assert "--out-dir /tmp/zenoctl-test" in output


def test_zenoctl_testnet_up_local_dry_run(capsys) -> None:
    rc = zenoctl.main(
        [
            "testnet",
            "up",
            "--profile",
            "local",
            "--out-dir",
            "/tmp/zenoctl-smoke",
            "--report-out",
            "/tmp/zenoctl-smoke/report.json",
            "--dry-run",
        ]
    )

    assert rc == 0
    output = capsys.readouterr().out
    assert "tools/zeno_ledger_public_network_smoke.py" in output
    assert "--report-out /tmp/zenoctl-smoke/report.json" in output


def test_zenoctl_testnet_up_docker_two_node_dry_run(capsys) -> None:
    rc = zenoctl.main(
        [
            "testnet",
            "up",
            "--profile",
            "docker-two-node",
            "--engine",
            "auto",
            "--dry-run",
        ]
    )

    assert rc in {0, 1}
    output = capsys.readouterr().out
    if rc == 0:
        assert "docker-compose.two-node.yml" in output


def test_zenoctl_testnet_up_docker_multimachine_dry_run(capsys) -> None:
    rc = zenoctl.main(
        [
            "testnet",
            "up",
            "--profile",
            "docker-multimachine",
            "--engine",
            "auto",
            "--dry-run",
        ]
    )

    assert rc in {0, 1}
    output = capsys.readouterr().out
    if rc == 0:
        assert "docker-compose.multimachine.yml" in output
        assert "zeno-ledger-multidocker-controller" in output


def test_zenoctl_testnet_demo_dry_run(capfd) -> None:
    rc = zenoctl.main(
        [
            "testnet",
            "demo",
            "up",
            "--engine",
            "auto",
            "--ui-port",
            "3999",
            "--dry-run",
        ]
    )

    assert rc == 0
    output = capfd.readouterr().out
    assert "scripts/zenodex_testnet_demo.sh" in output
    assert "docker-compose.testnet-demo.yml" in output
    assert "--ui-port 3999" in output


def test_zenoctl_testnet_demo_smoke_dry_run(capfd) -> None:
    rc = zenoctl.main(["testnet", "demo", "smoke", "--engine", "auto", "--dry-run"])

    assert rc == 0
    output = capfd.readouterr().out
    assert "tools/zenoctl.py testnet up --profile docker-two-node" in output


def test_zenoctl_testnet_join_dry_run(capfd) -> None:
    rc = zenoctl.main(
        [
            "testnet",
            "join",
            "--config-url",
            "https://example.test/public_network_config.json",
            "--node-id",
            "operator-laptop",
            "--bundle-root",
            "/tmp/zenodex-bundle",
            "--data-dir",
            "/tmp/zenodex-node",
            "--serve",
            "--write-auth-token-env",
            "ZENO_TESTNET_WRITE_TOKEN",
            "--port",
            "8788",
            "--poll-seconds",
            "5",
            "--dry-run",
        ]
    )

    assert rc == 0
    output = capfd.readouterr().out
    assert "tools/zeno_ledger_node.py join-network" in output
    assert "--config-url https://example.test/public_network_config.json" in output
    assert "--node-id operator-laptop" in output
    assert "--bundle-root /tmp/zenodex-bundle" in output
    assert "--data-dir /tmp/zenodex-node" in output
    assert "--host 127.0.0.1" in output
    assert "--serve" in output
    assert "--write-auth-token-env ZENO_TESTNET_WRITE_TOKEN" in output


def test_zenoctl_testnet_join_serve_requires_write_auth_token_env(capfd) -> None:
    rc = zenoctl.main(
        [
            "testnet",
            "join",
            "--config-url",
            "https://example.test/public_network_config.json",
            "--node-id",
            "operator-laptop",
            "--serve",
            "--dry-run",
        ]
    )

    assert rc == 2
    stderr = capfd.readouterr().err
    assert "--serve requires --write-auth-token-env" in stderr


def test_zenoctl_testnet_publish_config_dry_run(capfd) -> None:
    rc = zenoctl.main(
        [
            "testnet",
            "publish-config",
            "--bundle-root",
            "/tmp/zeno-ledger-public-testnet",
            "--mirror-base-url",
            "https://seed.example.test/zeno-ledger-public-testnet/",
            "--writer-url",
            "https://seed.example.test:8787",
            "--peer-url",
            "https://seed-b.example.test:8788",
            "--out",
            "/tmp/zeno-ledger-public-testnet/public_network_config.json",
            "--dry-run",
        ]
    )

    assert rc == 0
    output = capfd.readouterr().out
    assert "tools/zeno_ledger_node.py write-network-config" in output
    assert "--bundle-root /tmp/zeno-ledger-public-testnet" in output
    assert "--mirror-base-url https://seed.example.test/zeno-ledger-public-testnet/" in output
    assert "--writer-url https://seed.example.test:8787" in output
    assert "--peer-url https://seed-b.example.test:8788" in output
    assert "--out /tmp/zeno-ledger-public-testnet/public_network_config.json" in output


def test_zenoctl_testnet_help_lists_join(capfd) -> None:
    with pytest.raises(SystemExit) as excinfo:
        zenoctl.main(["testnet", "--help"])

    assert excinfo.value.code == 0
    output = capfd.readouterr().out
    assert "join" in output
    assert "publish-config" in output


def test_multidocker_plan_uses_hashes_for_all_nodes() -> None:
    plan = build_multidocker_plan_v0(
        machine_count=3,
        network_id="zeno-ledger-testnet-v0",
        chain_id="zeno-ledger-testnet-v0",
    )

    assert plan["ok"] is True
    assert plan["machine_count"] == 3
    hashes = [node["node_hash"] for node in plan["nodes"]]
    assert len(set(hashes)) == 3
    assert all(isinstance(node_hash, str) and node_hash.startswith("0x") and len(node_hash) == 66 for node_hash in hashes)
    assert "readonly_follower_faucet_rejected" in plan["adversarial_http_checks"]


def test_multidocker_bundle_archive_round_trips_without_path_escape(tmp_path: Path) -> None:
    bundle = tmp_path / "bundle"
    bundle.mkdir()
    (bundle / "public_testnet_manifest.json").write_text('{"ok": true}\n', encoding="utf-8")
    (bundle / "nested").mkdir()
    (bundle / "nested" / "artifact.json").write_text('{"artifact": true}\n', encoding="utf-8")
    archive = tmp_path / "bundle.tar.gz"
    out = tmp_path / "out" / "bundle"

    _write_bundle_archive(bundle_root=bundle, tar_out=archive)
    _extract_bundle_archive(archive_path=archive, bundle_root=out)

    assert (out / "public_testnet_manifest.json").is_file()
    assert json.loads((out / "nested" / "artifact.json").read_text(encoding="utf-8")) == {"artifact": True}


def test_multidocker_bundle_archive_rejects_path_escape(tmp_path: Path) -> None:
    archive = tmp_path / "bad.tar.gz"
    with tarfile.open(archive, "w:gz") as tar:
        info = tarfile.TarInfo("../escape.txt")
        payload = b"bad"
        info.size = len(payload)
        tar.addfile(info, io.BytesIO(payload))

    try:
        _extract_bundle_archive(archive_path=archive, bundle_root=tmp_path / "bundle")
    except ValueError as exc:
        assert "unsafe bundle archive member" in str(exc)
    else:
        raise AssertionError("unsafe bundle archive was accepted")


def test_zenoctl_prod_preflight_dry_run(capsys) -> None:
    rc = zenoctl.main(["prod", "preflight", "--skip-engine", "--dry-run"])

    assert rc == 0
    output = capsys.readouterr().out
    assert "tools/gate_operator_preflight.sh" in output
    assert "--skip-engine" in output


def test_zenoctl_node_status_text(capsys) -> None:
    rc = zenoctl.main(
        [
            "node",
            "status",
            "--node-identity",
            "operator-fixture",
            "--node-label",
            "operator fixture",
            "--ledger-height",
            "12",
            "--peer-count",
            "2",
            "--proof-profile",
            "spot_v1_single_pool_success",
            "--upba-policy",
            "balanced",
        ]
    )

    assert rc == 0
    output = capsys.readouterr().out
    assert "ZenoLedger Cockpit" in output
    assert "Node hash: 0x" in output
    assert "Short hash: 0x" in output
    assert "Label: operator fixture" in output
    assert "Height: 12" in output
    assert "Peers: 2" in output
    assert "Operator readiness: [####################] 100/100" in output


def test_zenoctl_node_status_watch_one_iteration(capsys) -> None:
    rc = zenoctl.main(
        [
            "node",
            "status",
            "--watch",
            "--iterations",
            "1",
            "--node-identity",
            "watch-fixture",
            "--peer-count",
            "1",
        ]
    )

    assert rc == 0
    assert "ZenoLedger Cockpit" in capsys.readouterr().out


def test_zenoctl_node_status_json_uses_hash_identity(capsys) -> None:
    rc = zenoctl.main(
        [
            "node",
            "status",
            "--json",
            "--node-public-key",
            "0x" + "11" * 48,
            "--peer-count",
            "1",
        ]
    )

    assert rc == 0
    payload = json.loads(capsys.readouterr().out)
    assert payload["node_hash"].startswith("0x")
    assert len(payload["node_hash"]) == 66
    assert payload["node_id"] == payload["node_hash"]
    assert payload["node_identity_kind"] == "node-public-key"
