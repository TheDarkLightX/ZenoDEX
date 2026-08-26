"""`up`/`down`/`status` lifecycle for `zenoctl testnet local`.

The orchestrator drives:
  1. Preflight (external/tau-testnet present, no conflicting stack without --force).
  2. Generate deterministic fixture bundle with accepted live profile shapes.
  3. Initialize a writable Oracle home under the local out-dir.
  4. Render nginx config and UI runtime config into <out_dir>/rendered/.
  5. Write manifest at <out_dir>/local_testnet_manifest.json.
  6. `compose up -d` the local-testnet overlay.
  7. Wait for base service health through nginx.
  8. Seed ledger/zUSD/perps state so the mounted tabs are actually usable.
  9. Run lane readiness checks and print a short summary.
"""

from __future__ import annotations

import json
import os
import re
import secrets
import shutil
import subprocess
import sys
import tempfile
import textwrap
import time
import urllib.error
import urllib.parse
import urllib.request
import webbrowser
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Mapping

from src.integration.zusd_tau_token import derive_zusd_tau_asset_id
from tools.zeno_ledger_make_testnet_bundle import (
    DEFAULT_RELEASE_TESTNET_TOKEN_SYMBOL,
    DEFAULT_TAGRS_ASSET_ID,
    DEFAULT_TZDEX_ASSET_ID,
)

from . import compose as cm
from . import fixtures as fx
from . import manifest as mf
from . import nginx as ng

REPO_ROOT = Path(__file__).resolve().parents[2]
COMPOSE_FILE = REPO_ROOT / "docker-compose.local-testnet.yml"
NGINX_TEMPLATE = REPO_ROOT / ".docker" / "nginx.local-testnet.conf.template"

DEFAULT_UI_PORT = 18080
DEFAULT_CHAIN_ID = "zeno-ledger-localtest-v0"
DEFAULT_NETWORK_ID = "zeno-ledger-localtest-v0"
DEFAULT_HEALTH_TIMEOUT_S = 120.0
DEFAULT_ZK_MODE = "auto-strict"
DEFAULT_PUBLIC_OUT_DIR = Path.home() / ".zenodex" / "public-testnet-v0.1.16"
ZK_MODES = ("auto-strict", "strict", "open")
MAX_PROOF_ARTIFACT_METADATA_BYTES = 65_536
GLOBAL_ZK_ENV_NAMES = (
    "TAU_DEX_PROOF_VERIFIER_CMD_JSON",
    "TAU_DEX_PROOF_VERIFIER_TIMEOUT_S",
    "TAU_DEX_PROOF_VERIFIER_MAX_PROOF_BYTES",
    "TAU_DEX_PROOF_VERIFIER_ALLOW_PATH_LOOKUP",
    "TAU_DEX_PROOF_VERIFIER_ARTIFACT_JSON",
    "TAU_DEX_PROOF_CIRCUIT_ARTIFACT_JSON",
    "TAU_DEX_PROOF_VERIFIER_ARTIFACT_FILE",
    "TAU_DEX_PROOF_CIRCUIT_ARTIFACT_FILE",
)
GLOBAL_ZK_MATERIAL_ENV_NAMES = (
    "TAU_DEX_PROOF_VERIFIER_CMD_JSON",
    "TAU_DEX_PROOF_VERIFIER_ARTIFACT_JSON",
    "TAU_DEX_PROOF_CIRCUIT_ARTIFACT_JSON",
    "TAU_DEX_PROOF_VERIFIER_ARTIFACT_FILE",
    "TAU_DEX_PROOF_CIRCUIT_ARTIFACT_FILE",
)

OPERATOR_TOOLS_IMAGE = "zenodex/operator-tools:local"
TAU_LOCAL_IMAGE = "zenodex/tau-local:local-testnet"
UI_NGINX_IMAGE = "zenodex:local"
CLOUDFLARED_IMAGE = "cloudflare/cloudflared:latest"

DEFAULT_MARKET_ID = "perp:ch2p:localtest-zusd-perps-v1"
E8 = 100_000_000
DEFAULT_ORACLE_PRICE_E8 = 20_000_000 * E8
DEFAULT_ZUSD_BOOTSTRAP_COLLATERAL_E8 = 1_000
DEFAULT_ZUSD_BOOTSTRAP_MINT_E8 = 100 * E8
DEFAULT_FIXTURE_NATIVE_MATERIALIZE_E8 = DEFAULT_ZUSD_BOOTSTRAP_COLLATERAL_E8
DEFAULT_FIXTURE_TEST_ASSET_PREFUND = 1_000_000
DEFAULT_FIXTURE_ZUSD_COUNTERPARTY_PREFUND = 25
SMOKE_CONFIDENTIAL_POLICY_DIGEST = "0x" + ("d" * 64)
LOCAL_TESTNET_ENABLED_LANES = (
    "DEX_API_ENABLED",
    "PERPS_WALLET_API_ENABLED",
    "ZUSD_MONETARY_WALLET_API_ENABLED",
    "AUTOTRADER_LIVE_API_ENABLED",
    "CONFIDENTIAL_ATTESTATION_API_ENABLED",
)


@dataclass(frozen=True)
class UpOptions:
    out_dir: Path
    chain_id: str = DEFAULT_CHAIN_ID
    network_id: str = DEFAULT_NETWORK_ID
    ui_port: int = DEFAULT_UI_PORT
    engine: str = "auto"  # "auto" | "docker" | "podman"
    force: bool = False
    health_timeout_s: float = DEFAULT_HEALTH_TIMEOUT_S
    seed_override_hex: str | None = None
    use_random_seed: bool = False
    zk_mode: str = DEFAULT_ZK_MODE


@dataclass(frozen=True)
class DownOptions:
    out_dir: Path
    engine: str = "auto"


@dataclass(frozen=True)
class StatusOptions:
    out_dir: Path
    engine: str = "auto"
    as_json: bool = False


@dataclass(frozen=True)
class SmokeOptions:
    out_dir: Path
    engine: str = "auto"
    browser: str = "auto"  # "auto" | "off" | "required"
    chrome_bin: Path | None = None
    browser_timeout_s: float = 60.0


@dataclass(frozen=True)
class ReleaseSmokeOptions:
    out_dir: Path
    engine: str = "auto"


@dataclass(frozen=True)
class PublicUpOptions(UpOptions):
    cloudflared_bin: str = "cloudflared"
    tunnel_url: str | None = None
    open_browser: bool = False
    release_smoke_before_tunnel: bool = False


@dataclass(frozen=True)
class LogsOptions:
    out_dir: Path
    engine: str = "auto"
    service: str | None = None
    tail: int | None = None


@dataclass(frozen=True)
class ResetOptions:
    out_dir: Path
    engine: str = "auto"


@dataclass(frozen=True)
class ConfidentialLocalFixture:
    nitro_pcr0: str
    nitro_pcr8: str
    policy_digest: str = SMOKE_CONFIDENTIAL_POLICY_DIGEST

    @property
    def measurement(self) -> str:
        return f"nitro:pcr0:{self.nitro_pcr0}:pcr8:{self.nitro_pcr8}"

    def to_runtime_config(self) -> dict[str, str]:
        return {
            "provider": "nitro",
            "nitroPcr0": self.nitro_pcr0,
            "nitroPcr8": self.nitro_pcr8,
            "policyDigest": self.policy_digest,
            "measurement": self.measurement,
        }


def cmd_up(opts: UpOptions) -> int:
    paths = mf.ManifestPaths.from_out_dir(opts.out_dir)
    existing_manifest = _load_manifest_if_present(paths.manifest_path, allow_invalid=opts.force)
    if existing_manifest is not None:
        if not opts.force:
            return _cmd_up_existing(opts=opts, paths=paths, manifest=existing_manifest)
        _log("preflight", f"force reset requested for {paths.out_dir}")
        _reset_stack(paths=paths, engine_name=opts.engine, manifest=existing_manifest)

    paths.out_dir.mkdir(parents=True, exist_ok=True)
    paths.reports_dir.mkdir(parents=True, exist_ok=True)
    cm.check_external_tau_testnet_present(REPO_ROOT)
    cm.check_host_port_free(opts.ui_port)
    zk_posture = _resolve_zk_posture(opts.zk_mode)
    if zk_posture.get("ok") is not True:
        _log("preflight", str(zk_posture.get("zk_fallback_reason") or "ZK strict mode unavailable"))
        return 2

    engine = cm.detect_engine(opts.engine)
    _log("preflight", f"engine={engine.binary}")

    seed = _resolve_fixture_seed(opts)
    _log("fixtures", "generating deterministic fixture bundle")
    bundle = fx.generate_fixture_bundle(
        out_dir=paths.out_dir,
        chain_id=opts.chain_id,
        network_id=opts.network_id,
        seed_override_hex=seed.hex(),
        use_random=False,
    )
    key_bundle = _load_json_file(bundle.key_bundle, label="key bundle")
    roles = _role_materials(key_bundle)

    _log("oracle", "initializing Oracle home")
    _init_oracle_home(paths.oracle_home_dir)
    _install_oracle_authority_profile(
        home_dir=paths.oracle_home_dir,
        authority_profile_path=bundle.oracle_authority_profile,
    )

    writer_token = fx.derive_writer_token(seed)
    stdlib_token = _derive_stdlib_token(seed)
    confidential_fixture = _new_confidential_local_fixture()

    _log("render", "rendering nginx + UI runtime config")
    rendered_nginx = ng.render_nginx_conf(
        ng.NginxRenderInputs(
            writer_upstream="zeno-ledger-writer:8787",
            stdlib_upstream="zenodex-api:8000",
            oracle_upstream="zenodex-oracle:9100",
            writer_token=writer_token,
            stdlib_token=stdlib_token,
        ),
        template_path=NGINX_TEMPLATE,
    )
    ng.write_rendered_conf(rendered_nginx, out_path=paths.rendered_nginx)
    paths.rendered_runtime_config.parent.mkdir(parents=True, exist_ok=True)
    device_approval_exercise = json.loads(bundle.perps_wallet_device_approval_exercise.read_text(encoding="utf-8"))
    signer_device_integration = json.loads(bundle.perps_wallet_signer_device_integration.read_text(encoding="utf-8"))
    signer_prompt_capture = json.loads(bundle.perps_wallet_signer_prompt_capture.read_text(encoding="utf-8"))
    signer_execution_exercise = json.loads(bundle.perps_wallet_signer_execution_exercise.read_text(encoding="utf-8"))
    signer_ceremony_fixture = {
        "device_approval_exercise": device_approval_exercise,
        "signer_device_integration": signer_device_integration,
        "signer_prompt_capture": signer_prompt_capture,
        "signer_execution_exercise": signer_execution_exercise,
    }
    gov_fixtures = {
        "recoveryExercise": json.loads(bundle.perps_wallet_recovery_exercise.read_text(encoding="utf-8")),
        "rotationExercise": json.loads(bundle.perps_wallet_rotation_exercise.read_text(encoding="utf-8")),
        "deviceApprovalExercise": device_approval_exercise,
        "signerDeviceIntegration": signer_device_integration,
        "signerPromptCapture": signer_prompt_capture,
        "signerExecutionExercise": signer_execution_exercise,
        "signerCeremony": signer_ceremony_fixture,
        "hardwareCustody": signer_ceremony_fixture,
        "encryptedSssBackup": json.loads(bundle.perps_wallet_encrypted_sss_backup.read_text(encoding="utf-8")),
    }
    paths.rendered_runtime_config.write_text(
        ng.render_runtime_config(
            demo_mode=False,
            extra={
                "chainId": opts.chain_id,
                "networkId": opts.network_id,
                "localTestnetGovernanceFixtures": gov_fixtures,
                "localTestnetZkPosture": zk_posture,
                "localTestnetConfidentialFixture": confidential_fixture.to_runtime_config(),
            },
        ),
        encoding="utf-8",
    )

    manifest = mf.build_manifest(
        out_dir=paths.out_dir,
        chain_id=opts.chain_id,
        network_id=opts.network_id,
        ports={"ui": opts.ui_port},
        service_urls={
            "ui": f"http://127.0.0.1:{opts.ui_port}",
            "stdlib_api": "compose://zenodex-api:8000",
            "writer": "compose://zeno-ledger-writer:8787",
            "oracle": "compose://zenodex-oracle:9100",
            "tau": "compose://tau-local:65432",
        },
        image_refs={
            "operator_tools": OPERATOR_TOOLS_IMAGE,
            "tau_local": TAU_LOCAL_IMAGE,
            "ui_nginx": UI_NGINX_IMAGE,
        },
        enabled_lanes=list(LOCAL_TESTNET_ENABLED_LANES),
        fixture_paths=bundle.as_manifest_paths(),
        ledger_bundle_manifest=str(paths.out_dir / "ledger" / "public_testnet_manifest.json"),
        writer_token=writer_token,
        stdlib_token=stdlib_token,
        zk_posture=zk_posture,
        created_at_ms=int(time.time() * 1000),
    )
    manifest["confidential_fixture"] = confidential_fixture.to_runtime_config()
    mf.save_manifest(manifest, paths.manifest_path)
    ng.assert_no_token_in_file(paths.manifest_path, writer_token)
    ng.assert_no_token_in_file(paths.manifest_path, stdlib_token)
    ng.assert_no_token_in_file(paths.rendered_runtime_config, writer_token)
    ng.assert_no_token_in_file(paths.rendered_runtime_config, stdlib_token)

    env = _compose_env(
        paths=paths,
        ui_port=opts.ui_port,
        chain_id=opts.chain_id,
        network_id=opts.network_id,
        writer_token=writer_token,
        stdlib_token=stdlib_token,
        roles=roles,
        zk_required=bool(zk_posture.get("zk_required")),
        expected_zk_posture=zk_posture,
        confidential_fixture=confidential_fixture,
    )
    project = str(manifest["compose_project"])

    _log("compose", f"compose up project={project}")
    cm.compose_up(
        engine=engine,
        project_name=project,
        compose_files=[COMPOSE_FILE],
        env=env,
        extra_args=["--build"],
    )

    try:
        ui_base = f"http://127.0.0.1:{opts.ui_port}"
        _wait_for_base_services(ui_base=ui_base, timeout_s=opts.health_timeout_s)

        _log("seed", "seeding ledger writer with initial pool and faucet state")
        controller_report = _seed_ledger_controller(
            engine=engine,
            project=project,
            env=env,
            chain_id=opts.chain_id,
            timeout_s=max(float(opts.health_timeout_s), 900.0),
        )
        _write_json(paths.reports_dir / "ledger_controller_report.json", controller_report)

        _log("seed", "seeding zUSD monetary state and perps market")
        seed_report = _seed_api_state(
            engine=engine,
            project=project,
            env=env,
            roles=roles,
            chain_id=opts.chain_id,
            tau_rpc_timeout_s=max(float(opts.health_timeout_s), 900.0),
        )
        _write_json(paths.reports_dir / "api_seed_report.json", seed_report)

        readiness = _wait_for_lane_readiness(ui_base=ui_base, timeout_s=opts.health_timeout_s, manifest=manifest)
        _write_json(paths.reports_dir / "readiness_report.json", readiness)
    except Exception as exc:
        _log("failure", f"{type(exc).__name__}: {exc}")
        _tail_service_logs(engine=engine, project=project, env=env)
        cm.compose_down(
            engine=engine,
            project_name=project,
            compose_files=[COMPOSE_FILE],
            remove_volumes=False,
            env=env,
        )
        return 1

    _log("done", f"stack up: http://127.0.0.1:{opts.ui_port}")
    sys.stderr.write(_summary_text(manifest))
    return 0


def _cmd_up_existing(*, opts: UpOptions, paths: mf.ManifestPaths, manifest: Mapping[str, Any]) -> int:
    """Restart an existing local-testnet stack from its saved artifacts.

    The manifest intentionally stores token hashes only. The only place raw
    local bearer tokens persist is the rendered nginx config inside the
    operator-selected out-dir. For restart, recover those tokens from the
    rendered config, verify the writer token hash against the manifest, and
    rebuild the compose environment without printing secrets.
    """
    engine = cm.detect_engine(opts.engine)
    manifest_port = _manifest_ui_port(manifest)
    if opts.ui_port != DEFAULT_UI_PORT and opts.ui_port != manifest_port:
        _log(
            "preflight",
            f"existing manifest uses ui_port={manifest_port}; use --force to recreate on {opts.ui_port}",
        )
        return 2

    project = str(manifest["compose_project"])
    requested_gap = _existing_manifest_zk_request_gap(opts=opts, manifest=manifest)
    if requested_gap:
        _log("preflight", requested_gap)
        return 2
    zk_env_gap = _strict_zk_env_gap(expected=_zk_posture_from_manifest(manifest)) if manifest.get("zk_required") is True else None
    if zk_env_gap:
        _log("preflight", f"existing strict ZK manifest cannot be restarted: {zk_env_gap}")
        return 2
    paths.reports_dir.mkdir(parents=True, exist_ok=True)
    env = _runtime_env_for_existing_manifest(manifest=manifest, paths=paths)
    _log("preflight", f"existing manifest detected; restarting compose project={project}")
    cm.compose_up(
        engine=engine,
        project_name=project,
        compose_files=[COMPOSE_FILE],
        env=env,
        extra_args=["--build"],
    )

    ui_base = str((manifest.get("service_urls") or {}).get("ui") or f"http://127.0.0.1:{manifest_port}")
    try:
        _wait_for_base_services(ui_base=ui_base, timeout_s=opts.health_timeout_s)
        readiness = _wait_for_lane_readiness(ui_base=ui_base, timeout_s=opts.health_timeout_s, manifest=manifest)
        _write_json(paths.reports_dir / "readiness_report.json", readiness)
    except Exception as exc:
        _log("failure", f"{type(exc).__name__}: {exc}")
        _tail_service_logs(engine=engine, project=project, env=env)
        cm.compose_down(
            engine=engine,
            project_name=project,
            compose_files=[COMPOSE_FILE],
            remove_volumes=False,
            env=env,
        )
        return 1

    _log("done", f"stack up: {ui_base}")
    sys.stderr.write(_summary_text(manifest))
    return 0


def _existing_manifest_zk_request_gap(*, opts: UpOptions, manifest: Mapping[str, Any]) -> str | None:
    if opts.zk_mode == DEFAULT_ZK_MODE:
        return None
    saved_modes = {
        str(manifest.get("zk_mode_requested") or ""),
        str(manifest.get("zk_mode_effective") or ""),
    }
    if opts.zk_mode in saved_modes:
        return None
    saved = manifest.get("zk_mode_requested") or manifest.get("zk_mode_effective") or "unknown"
    return (
        f"existing manifest uses zk_mode={saved}; use --force to recreate with "
        f"--zk-mode {opts.zk_mode}"
    )


def cmd_down(opts: DownOptions) -> int:
    paths = mf.ManifestPaths.from_out_dir(opts.out_dir)
    manifest = _load_manifest_if_present(paths.manifest_path)
    if manifest is None:
        _log("down", f"no manifest at {paths.manifest_path}; nothing to do")
        return 0
    engine = cm.detect_engine(opts.engine)
    project = str(manifest["compose_project"])
    _log("down", f"compose down project={project} (preserving volumes and out-dir)")
    cm.compose_down(
        engine=engine,
        project_name=project,
        compose_files=[COMPOSE_FILE],
        remove_volumes=False,
        env=_lifecycle_env_for_compose(manifest, paths),
    )
    return 0


def cmd_status(opts: StatusOptions) -> int:
    paths = mf.ManifestPaths.from_out_dir(opts.out_dir)
    manifest = _load_manifest_if_present(paths.manifest_path)
    if manifest is None:
        report = {"ok": False, "status": "no_manifest", "manifest_path": str(paths.manifest_path)}
        _emit_status(report, as_json=opts.as_json)
        return 1

    engine = cm.detect_engine(opts.engine)
    services = cm.compose_ps_json(
        engine=engine,
        project_name=str(manifest["compose_project"]),
        compose_files=[COMPOSE_FILE],
        env=_lifecycle_env_for_compose(manifest, paths),
    )
    ui_base = str(manifest["service_urls"]["ui"])
    base_health = _probe_base_services(ui_base=ui_base)
    lanes = _collect_lane_readiness(ui_base=ui_base, manifest=manifest) if base_health["ok"] else {"ok": False, "lanes": {}}
    report = {
        "ok": bool(base_health["ok"]) and bool(lanes.get("ok")) and len(services) > 0,
        "manifest_path": str(paths.manifest_path),
        "compose_project": manifest["compose_project"],
        "ui_url": ui_base,
        "zk_posture": _zk_posture_from_manifest(manifest),
        "key_management_authority": lanes.get("key_management_authority") if isinstance(lanes, Mapping) else None,
        "base_health": base_health,
        "lanes": lanes,
        "service_count": len(services),
        "services": [
            {
                "name": svc.get("Service") or svc.get("Name") or "<unknown>",
                "state": svc.get("State") or svc.get("Status") or "<unknown>",
                "health": svc.get("Health") or "<n/a>",
            }
            for svc in services
        ],
    }
    _emit_status(report, as_json=opts.as_json)
    return 0 if report["ok"] else 1


def cmd_smoke(opts: SmokeOptions) -> int:
    paths = mf.ManifestPaths.from_out_dir(opts.out_dir)
    manifest = _load_manifest_if_present(paths.manifest_path)
    if manifest is None:
        report = {"ok": False, "status": "no_manifest", "manifest_path": str(paths.manifest_path)}
        _write_json(paths.reports_dir / "local_smoke_report.json", report)
        print(json.dumps(report, indent=2, sort_keys=True))
        return 1

    engine = cm.detect_engine(opts.engine)
    services = cm.compose_ps_json(
        engine=engine,
        project_name=str(manifest["compose_project"]),
        compose_files=[COMPOSE_FILE],
        env=_lifecycle_env_for_compose(manifest, paths),
    )
    ui_base = str(manifest["service_urls"]["ui"])
    base_health = _probe_base_services(ui_base=ui_base)
    readiness = (
        _collect_lane_readiness(ui_base=ui_base, manifest=manifest)
        if base_health["ok"]
        else {"ok": False, "checks": {}, "lanes": {}}
    )
    report: dict[str, Any] = {
        "schema": "zenodex.local_testnet.smoke_report.v1",
        "ok": False,
        "manifest_path": str(paths.manifest_path),
        "compose_project": manifest["compose_project"],
        "ui_url": ui_base,
        "service_count": len(services),
        "zk_posture": _zk_posture_from_manifest(manifest),
        "key_management_authority": readiness.get("key_management_authority") if isinstance(readiness, Mapping) else None,
        "base_health": base_health,
        "readiness": readiness,
        "feature_checks": {},
        "browser_checks": {"mode": opts.browser, "checks": {}, "skipped": False},
    }

    if base_health["ok"] and readiness.get("ok") is True:
        try:
            report["feature_checks"] = _run_feature_smoke(ui_base=ui_base, paths=paths, manifest=manifest)
        except Exception as exc:
            report["feature_checks"] = {"ok": False, "error": f"{type(exc).__name__}: {exc}"}

    browser_ok = True
    if opts.browser != "off":
        browser_report = _run_browser_smoke(
            ui_base=ui_base,
            paths=paths,
            manifest=manifest,
            chrome_bin=opts.chrome_bin,
            mode=opts.browser,
            timeout_s=opts.browser_timeout_s,
        )
        report["browser_checks"] = browser_report
        browser_ok = bool(browser_report.get("ok"))

    feature_ok = bool((report.get("feature_checks") or {}).get("ok"))
    report["ok"] = (
        bool(base_health["ok"])
        and bool(readiness.get("ok"))
        and feature_ok
        and browser_ok
        and len(services) > 0
    )
    _write_json(paths.reports_dir / "local_smoke_report.json", report)
    print(json.dumps(report, indent=2, sort_keys=True))
    return 0 if report["ok"] else 1


def cmd_release_smoke(opts: ReleaseSmokeOptions) -> int:
    paths = mf.ManifestPaths.from_out_dir(opts.out_dir)
    manifest = _load_manifest_if_present(paths.manifest_path)
    if manifest is None:
        report = {"ok": False, "status": "no_manifest", "manifest_path": str(paths.manifest_path)}
        _write_json(paths.reports_dir / "release_flow_smoke_report.json", report)
        print(json.dumps(report, indent=2, sort_keys=True))
        return 1

    engine = cm.detect_engine(opts.engine)
    env = _runtime_env_for_existing_manifest(manifest=manifest, paths=paths)
    services = cm.compose_ps_json(
        engine=engine,
        project_name=str(manifest["compose_project"]),
        compose_files=[COMPOSE_FILE],
        env=env,
    )
    ui_base = str(manifest["service_urls"]["ui"])
    report: dict[str, Any] = {
        "schema": "zenodex.local_testnet.release_flow_smoke_report.v1",
        "ok": False,
        "status": "running",
        "manifest_path": str(paths.manifest_path),
        "compose_project": manifest["compose_project"],
        "ui_url": ui_base,
        "service_count": len(services),
        "assets": {
            "tAGRS": DEFAULT_TAGRS_ASSET_ID,
            "tZDEX": DEFAULT_TZDEX_ASSET_ID,
            "zUSD": derive_zusd_tau_asset_id(chain_id=str(manifest["chain_id"])),
        },
        "checks": {},
    }
    try:
        report["checks"] = _run_release_flow_smoke(
            ui_base=ui_base,
            paths=paths,
            manifest=manifest,
            engine=engine,
            compose_project=str(manifest["compose_project"]),
            env=env,
        )
        report["ok"] = all(bool(item.get("ok")) for item in report["checks"].values())
        report["status"] = "accepted" if report["ok"] else "rejected"
    except Exception as exc:
        report["ok"] = False
        report["status"] = "rejected"
        report["error"] = f"{type(exc).__name__}: {exc}"
    _write_json(paths.reports_dir / "release_flow_smoke_report.json", report)
    print(json.dumps(report, indent=2, sort_keys=True))
    return 0 if report["ok"] else 1


def cmd_public_up(opts: PublicUpOptions) -> int:
    if not opts.tunnel_url and _resolve_cloudflared_runner(opts.cloudflared_bin, engine=opts.engine) is None:
        _log(
            "public",
            "no Quick Tunnel runner found. Install cloudflared, keep Docker/Podman on PATH, "
            "or pass --tunnel-url after starting a tunnel.",
        )
        return 2
    up_code = cmd_up(
        UpOptions(
            out_dir=opts.out_dir,
            chain_id=opts.chain_id,
            network_id=opts.network_id,
            ui_port=opts.ui_port,
            engine=opts.engine,
            force=opts.force,
            health_timeout_s=opts.health_timeout_s,
            seed_override_hex=opts.seed_override_hex,
            use_random_seed=opts.use_random_seed,
            zk_mode=opts.zk_mode,
        )
    )
    if up_code != 0:
        return up_code

    paths = mf.ManifestPaths.from_out_dir(opts.out_dir)
    manifest = _load_manifest_if_present(paths.manifest_path)
    if manifest is None:
        _log("public", f"manifest missing after up: {paths.manifest_path}")
        return 1
    if opts.release_smoke_before_tunnel:
        _log("public", "running v0.1.16 release smoke before opening the public tunnel")
        smoke_code = cmd_release_smoke(ReleaseSmokeOptions(out_dir=opts.out_dir, engine=opts.engine))
        if smoke_code != 0:
            _log("public", "release smoke failed; public tunnel was not opened")
            return smoke_code
    if opts.tunnel_url:
        report = _write_public_host_report(
            paths=paths,
            manifest=manifest,
            public_url=opts.tunnel_url,
            source="provided",
        )
        sys.stderr.write(_public_host_summary(report))
        if opts.open_browser and report.get("ok") is True:
            _open_public_ui_url(str(report["public_ui_url"]))
        return 0 if report.get("ok") is True else 1
    return _run_cloudflare_quick_tunnel(opts=opts, paths=paths, manifest=manifest)


def cmd_logs(opts: LogsOptions) -> int:
    paths = mf.ManifestPaths.from_out_dir(opts.out_dir)
    manifest = _load_manifest_if_present(paths.manifest_path)
    if manifest is None:
        _log("logs", f"no manifest at {paths.manifest_path}")
        return 1
    engine = cm.detect_engine(opts.engine)
    output = cm.compose_logs(
        engine=engine,
        project_name=str(manifest["compose_project"]),
        compose_files=[COMPOSE_FILE],
        service=opts.service,
        tail=opts.tail,
        env=_lifecycle_env_for_compose(manifest, paths),
    )
    sys.stdout.write(output)
    return 0


def cmd_reset(opts: ResetOptions) -> int:
    paths = mf.ManifestPaths.from_out_dir(opts.out_dir)
    manifest = _load_manifest_if_present(paths.manifest_path)
    _reset_stack(paths=paths, engine_name=opts.engine, manifest=manifest)
    return 0


_LIFECYCLE_PLACEHOLDER = "unused-for-lifecycle-op"
_BEARER_HEADER_RE = re.compile(r'proxy_set_header\s+Authorization\s+"Bearer\s+([^"]+)";')

# Directories that would be catastrophic to rmtree. We don't try to limit
# the out-dir to /tmp or ~/ — legitimate operators may use /var/lib or
# similar — but `/`, the user home itself, and core system dirs are never
# valid local-testnet out-dirs and must never be rm-rf'd by accident.
_FORBIDDEN_RESET_DIRS: tuple[str, ...] = (
    "/",
    "/root",
    "/home",
    "/etc",
    "/usr",
    "/var",
    "/bin",
    "/sbin",
    "/opt",
    "/lib",
    "/lib64",
    "/dev",
    "/proc",
    "/sys",
    "/boot",
    "/mnt",
    "/srv",
)


def _refuse_unsafe_reset_target(out_dir: Path) -> None:
    """Refuse destructive operations on system roots or the user's home
    directory. A typo like `--out-dir /` must not be able to wipe the
    filesystem."""
    raw = str(Path(out_dir).absolute())
    resolved = str(Path(out_dir).resolve())
    if raw in _FORBIDDEN_RESET_DIRS or resolved in _FORBIDDEN_RESET_DIRS:
        raise ValueError(
            f"refusing destructive operation on {resolved!r}: pick a dedicated "
            "--out-dir (e.g. /tmp/zen-local) instead of a system path."
        )
    home = str(Path.home().resolve())
    if home and resolved == home:
        raise ValueError(
            f"refusing destructive operation on the user home directory {home!r}. "
            "Use a dedicated subdirectory (e.g. ~/zen-local)."
        )


def _reset_stack(*, paths: mf.ManifestPaths, engine_name: str, manifest: Mapping[str, Any] | None) -> None:
    _refuse_unsafe_reset_target(paths.out_dir)
    # If there is no manifest and the out-dir contains unrelated entries,
    # refuse to rmtree it. An empty/nonexistent dir is safe to skip.
    if manifest is None and paths.out_dir.exists():
        try:
            entries = {p.name for p in paths.out_dir.iterdir()}
        except OSError:
            entries = set()
        known = {"fixtures", "rendered", "reports", "oracle-home", "ledger", mf.MANIFEST_FILENAME}
        unexpected = entries - known
        if unexpected:
            raise ValueError(
                f"refusing to reset {paths.out_dir}: no manifest, and the directory "
                f"contains unrelated entries {sorted(unexpected)[:5]}. Move or empty it first."
            )
    if manifest is not None:
        engine = cm.detect_engine(engine_name)
        cm.compose_down(
            engine=engine,
            project_name=str(manifest["compose_project"]),
            compose_files=[COMPOSE_FILE],
            remove_volumes=True,
            env=_lifecycle_env_for_compose(dict(manifest), paths),
        )
    shutil.rmtree(paths.out_dir, ignore_errors=True)


def _compose_env(
    *,
    paths: mf.ManifestPaths,
    ui_port: int,
    chain_id: str,
    network_id: str,
    writer_token: str,
    stdlib_token: str,
    roles: Mapping[str, Mapping[str, Any]],
    zk_required: bool,
    expected_zk_posture: Mapping[str, Any] | None = None,
    confidential_fixture: ConfidentialLocalFixture | None = None,
) -> dict[str, str]:
    if zk_required:
        zk_env_gap = _strict_zk_env_gap(expected=expected_zk_posture)
        if zk_env_gap:
            raise ValueError(f"strict ZK compose environment is not ready: {zk_env_gap}")
    env = {
        "ZENO_LEDGER_WRITER_TOKEN": writer_token,
        "ZENODEX_API_BEARER_TOKEN": stdlib_token,
        "RENDERED_NGINX_CONF_PATH": str(paths.rendered_nginx),
        "RENDERED_RUNTIME_CONFIG_PATH": str(paths.rendered_runtime_config),
        "FIXTURES_DIR": str(paths.fixtures_dir),
        "SECRETS_DIR": str(paths.secrets_dir),
        "ORACLE_HOME_DIR": str(paths.oracle_home_dir),
        "HOST_UID": str(_host_uid()),
        "HOST_GID": str(_host_gid()),
        "UI_PORT": str(ui_port),
        "CHAIN_ID": chain_id,
        "NETWORK_ID": network_id,
        "ZENO_LEDGER_TOKEN_SYMBOL": DEFAULT_RELEASE_TESTNET_TOKEN_SYMBOL,
        "TAU_DEX_REQUIRE_LIVE_ZK_PROOF": "true" if zk_required else "false",
        "TAU_DEX_TOKEN_OPERATOR_PUBKEY": str(roles["operator"]["public_key"]),
        "TAU_DEX_TOKEN_OPERATOR_PRIVKEY": str(roles["operator"].get("privkey_int", "")),
        "TAU_DEX_ORACLE_PUBKEY": str(roles["oracle_authority"]["public_key"]),
        "TAU_DEX_ZUSD_ORACLE_PUBKEY": str(roles["alice"]["public_key"]),
        "TAU_DEX_PROOF_MINING_POOL_PUBKEY": _proof_mining_pool_pubkey_from_roles(roles),
    }
    if zk_required:
        env["TAU_DEX_ALLOW_EXTERNAL_TOOLS"] = "1"
        env["TAU_DEX_CONSENSUS_MODE"] = "0"
        env.update(_local_live_wrapper_zk_env())
    fixture = confidential_fixture or _fallback_confidential_local_fixture(
        chain_id=chain_id,
        network_id=network_id,
        out_dir=paths.out_dir,
    )
    env["CONFIDENTIAL_APPROVED_MEASUREMENTS"] = fixture.measurement
    env["CONFIDENTIAL_ATTESTATION_VERIFIER_CMD_JSON"] = _confidential_verifier_cmd_json(fixture)
    for name in GLOBAL_ZK_ENV_NAMES:
        value = os.environ.get(name)
        if value is not None and value.strip():
            env[name] = value
    return env


def _local_live_wrapper_zk_env() -> dict[str, str]:
    """Surface-specific fixture ZK verifier env for strict local testnet lanes."""
    cmd_json = json.dumps(["python3", "/app/tools/proof_verifiers/local_live_wrapper_echo_v1.py"])
    verifier_artifact = json.dumps(
        {
            "artifact_id": "local-live-wrapper-echo-v1",
            "artifact_hash": "sha256:" + "33" * 32,
            "production_security_claim": False,
        },
        sort_keys=True,
    )
    circuit_artifact = json.dumps(
        {
            "artifact_id": "local-live-wrapper-fixture-circuit-v1",
            "artifact_hash": "sha256:" + "44" * 32,
            "proof_system": "local-testnet-live-wrapper-fixture-v1",
            "production_security_claim": False,
        },
        sort_keys=True,
    )
    return {
        "TAU_DEX_PROOF_VERIFIER_CMD_JSON": cmd_json,
        "TAU_DEX_PROOF_VERIFIER_ALLOW_PATH_LOOKUP": "true",
        "TAU_DEX_PROOF_VERIFIER_ARTIFACT_JSON": verifier_artifact,
        "TAU_DEX_PROOF_CIRCUIT_ARTIFACT_JSON": circuit_artifact,
        "ZUSD_MONETARY_WALLET_PROOF_VERIFIER_CMD_JSON": cmd_json,
        "ZUSD_MONETARY_WALLET_PROOF_VERIFIER_ALLOW_PATH_LOOKUP": "true",
        "ZUSD_MONETARY_WALLET_PROOF_VERIFIER_ARTIFACT_JSON": verifier_artifact,
        "ZUSD_MONETARY_WALLET_PROOF_CIRCUIT_ARTIFACT_JSON": circuit_artifact,
        "PERPS_WALLET_PROOF_VERIFIER_CMD_JSON": cmd_json,
        "PERPS_WALLET_PROOF_VERIFIER_ALLOW_PATH_LOOKUP": "true",
        "PERPS_WALLET_PROOF_VERIFIER_ARTIFACT_JSON": verifier_artifact,
        "PERPS_WALLET_PROOF_CIRCUIT_ARTIFACT_JSON": circuit_artifact,
    }


def _proof_mining_pool_pubkey_from_roles(roles: Mapping[str, Mapping[str, Any]]) -> str:
    """Return the local active-participant reward pool pubkey.

    The tokenomics distribution wires the active-participant rewards pool to the
    guardian_2 fixture. Falling back keeps low-level tests usable with minimal
    role maps, while real local-testnet fixtures always provide guardian_2.
    """

    for role in ("guardian_2", "operator"):
        material = roles.get(role)
        if isinstance(material, Mapping) and material.get("public_key"):
            return str(material["public_key"])
    return ""


def _validate_confidential_hex(value: object, *, nbytes: int, name: str) -> str:
    text = str(value or "").strip().lower()
    if text.startswith("0x"):
        text = text[2:]
    if len(text) != nbytes * 2 or any(ch not in "0123456789abcdef" for ch in text):
        raise ValueError(f"{name} must be {nbytes * 2}-char hex")
    if len(set(text)) < 4:
        raise ValueError(f"{name} must not be a low-entropy placeholder")
    return text


def _new_confidential_local_fixture() -> ConfidentialLocalFixture:
    return ConfidentialLocalFixture(
        nitro_pcr0=secrets.token_hex(48),
        nitro_pcr8=secrets.token_hex(48),
    )


def _fallback_confidential_local_fixture(
    *,
    chain_id: str,
    network_id: str,
    out_dir: Path,
) -> ConfidentialLocalFixture:
    import hashlib

    seed_material = f"{Path(out_dir).resolve()}:{chain_id}:{network_id}:confidential-local-fixture-v1"
    digest0 = hashlib.sha384((seed_material + ":pcr0").encode("utf-8")).hexdigest()
    digest8 = hashlib.sha384((seed_material + ":pcr8").encode("utf-8")).hexdigest()
    return ConfidentialLocalFixture(nitro_pcr0=digest0, nitro_pcr8=digest8)


def _confidential_local_fixture_from_mapping(value: object) -> ConfidentialLocalFixture | None:
    if not isinstance(value, Mapping):
        return None
    try:
        return ConfidentialLocalFixture(
            nitro_pcr0=_validate_confidential_hex(value.get("nitroPcr0"), nbytes=48, name="nitroPcr0"),
            nitro_pcr8=_validate_confidential_hex(value.get("nitroPcr8"), nbytes=48, name="nitroPcr8"),
            policy_digest=f"0x{_validate_confidential_hex(value.get('policyDigest'), nbytes=32, name='policyDigest')}",
        )
    except Exception:
        return None


def _confidential_local_fixture_from_manifest(
    *,
    manifest: Mapping[str, Any],
    paths: mf.ManifestPaths,
) -> ConfidentialLocalFixture:
    fixture = _confidential_local_fixture_from_mapping(manifest.get("confidential_fixture"))
    if fixture is not None:
        return fixture
    return _fallback_confidential_local_fixture(
        chain_id=str(manifest.get("chain_id") or DEFAULT_CHAIN_ID),
        network_id=str(manifest.get("network_id") or DEFAULT_NETWORK_ID),
        out_dir=paths.out_dir,
    )


def _confidential_verifier_cmd_json(fixture: ConfidentialLocalFixture) -> str:
    code = (
        "import json,sys;"
        "json.load(sys.stdin);"
        "print(json.dumps({'ok': True, 'result': "
        f"{{'measurement': {fixture.measurement!r}, 'policy_digest': {fixture.policy_digest!r}, 'attestation_epoch': 9}}"
        "}))"
    )
    return json.dumps(["/usr/local/bin/python", "-c", code])


def _lifecycle_env_for_compose(manifest: dict[str, Any], paths: mf.ManifestPaths) -> dict[str, str]:
    host_paths = manifest.get("host_paths") if isinstance(manifest.get("host_paths"), Mapping) else {}
    confidential_fixture = _confidential_local_fixture_from_manifest(manifest=manifest, paths=paths)
    env = {
        "ZENO_LEDGER_WRITER_TOKEN": _LIFECYCLE_PLACEHOLDER,
        "ZENODEX_API_BEARER_TOKEN": _LIFECYCLE_PLACEHOLDER,
        "RENDERED_NGINX_CONF_PATH": str(
            ((manifest.get("rendered_paths") or {}).get("nginx_conf"))
            or paths.rendered_nginx
        ),
        "RENDERED_RUNTIME_CONFIG_PATH": str(
            ((manifest.get("rendered_paths") or {}).get("runtime_config"))
            or paths.rendered_runtime_config
        ),
        "FIXTURES_DIR": str(host_paths.get("fixtures_dir") or paths.fixtures_dir),
        "SECRETS_DIR": str(host_paths.get("secrets_dir") or paths.secrets_dir),
        "ORACLE_HOME_DIR": str(host_paths.get("oracle_home_dir") or paths.oracle_home_dir),
        "HOST_UID": str(_host_uid()),
        "HOST_GID": str(_host_gid()),
        "UI_PORT": str(manifest["ports"]["ui"]),
        "CHAIN_ID": str(manifest["chain_id"]),
        "NETWORK_ID": str(manifest["network_id"]),
        "ZENO_LEDGER_TOKEN_SYMBOL": str(manifest.get("token_symbol") or DEFAULT_RELEASE_TESTNET_TOKEN_SYMBOL),
        "TAU_DEX_REQUIRE_LIVE_ZK_PROOF": "true" if manifest.get("zk_required") is True else "false",
        "TAU_DEX_TOKEN_OPERATOR_PUBKEY": _LIFECYCLE_PLACEHOLDER,
        "TAU_DEX_TOKEN_OPERATOR_PRIVKEY": _LIFECYCLE_PLACEHOLDER,
        "TAU_DEX_ORACLE_PUBKEY": _LIFECYCLE_PLACEHOLDER,
        "TAU_DEX_ZUSD_ORACLE_PUBKEY": _LIFECYCLE_PLACEHOLDER,
        "CONFIDENTIAL_APPROVED_MEASUREMENTS": confidential_fixture.measurement,
        "CONFIDENTIAL_ATTESTATION_VERIFIER_CMD_JSON": _confidential_verifier_cmd_json(confidential_fixture),
    }
    if manifest.get("zk_required") is True:
        env.update(_local_live_wrapper_zk_env())
    return env


def _runtime_env_for_existing_manifest(*, manifest: Mapping[str, Any], paths: mf.ManifestPaths) -> dict[str, str]:
    writer_token, stdlib_token = _recover_tokens_from_rendered_nginx(manifest=manifest, paths=paths)
    expected_writer_hash = manifest.get("writer_token_sha256")
    actual_writer_hash = mf.writer_token_sha256(writer_token)
    if expected_writer_hash != actual_writer_hash:
        raise ValueError("rendered nginx writer token does not match manifest writer_token_sha256")
    expected_stdlib_hash = manifest.get("stdlib_token_sha256")
    if isinstance(expected_stdlib_hash, str):
        actual_stdlib_hash = mf.writer_token_sha256(stdlib_token)
        if expected_stdlib_hash != actual_stdlib_hash:
            raise ValueError("rendered nginx stdlib token does not match manifest stdlib_token_sha256")

    rendered_nginx = ng.render_nginx_conf(
        ng.NginxRenderInputs(
            writer_upstream="zeno-ledger-writer:8787",
            stdlib_upstream="zenodex-api:8000",
            oracle_upstream="zenodex-oracle:9100",
            writer_token=writer_token,
            stdlib_token=stdlib_token,
        ),
        template_path=NGINX_TEMPLATE,
    )
    ng.write_rendered_conf(rendered_nginx, out_path=paths.rendered_nginx)
    _refresh_existing_runtime_config(paths.rendered_runtime_config)

    fixture_paths = manifest.get("fixture_paths") if isinstance(manifest.get("fixture_paths"), Mapping) else {}
    key_bundle_path = Path(str(fixture_paths.get("key_bundle") or (paths.fixtures_dir / "keys.json")))
    key_bundle = _load_json_file(key_bundle_path, label="key bundle")
    roles = _role_materials(key_bundle)

    return _compose_env(
        paths=paths,
        ui_port=_manifest_ui_port(manifest),
        chain_id=str(manifest["chain_id"]),
        network_id=str(manifest["network_id"]),
        writer_token=writer_token,
        stdlib_token=stdlib_token,
        roles=roles,
        zk_required=manifest.get("zk_required") is True,
        expected_zk_posture=_zk_posture_from_manifest(manifest),
        confidential_fixture=_confidential_local_fixture_from_manifest(manifest=manifest, paths=paths),
    )


def _refresh_existing_runtime_config(path: Path) -> None:
    """Carry forward old runtime config while applying current local-testnet defaults."""

    if path.is_file():
        raw = _load_json_file(path, label="runtime config")
        config = dict(raw)
    else:
        config = {}
    default_external_signer = {
        "schema": "zenodex/dex-ui/runtime-default-external-signer/v0",
        "signerSecurityProfile": "native-desktop-loopback-signer-v0",
        "connectUrl": "http://127.0.0.1:8799/public-receipt",
        "signTauTransactionPayloadUrl": "http://127.0.0.1:8799/sign-tau-transaction-payload",
        "signDexIntentForEngineUrl": "http://127.0.0.1:8799/sign-dex-intent",
    }
    config.update(
        {
            "demoMode": False,
            "allowDemoMode": False,
            "apiBase": "",
            "zenoOracleApiBase": "",
            "oracleApiBase": "",
            "deployment": "local-testnet",
            "allowBrowserKeyGeneration": True,
            "allowDefaultExternalSigner": True,
            "defaultExternalSigner": default_external_signer,
            "uiSurfaceContractSchema": "zenodex.dex_ui.surface_contract.v1",
            "uiSurfaceContractVersion": ng.ui_surface_contract_version(),
            "uiSurfaceContractHash": ng.ui_surface_contract_hash(),
        }
    )
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(config, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _recover_tokens_from_rendered_nginx(*, manifest: Mapping[str, Any], paths: mf.ManifestPaths) -> tuple[str, str]:
    rendered_paths = manifest.get("rendered_paths") if isinstance(manifest.get("rendered_paths"), Mapping) else {}
    nginx_path = Path(str(rendered_paths.get("nginx_conf") or paths.rendered_nginx))
    if not nginx_path.is_file():
        raise FileNotFoundError(f"rendered nginx config missing: {nginx_path}")
    rendered = nginx_path.read_text(encoding="utf-8")

    writer_block = _extract_nginx_location_block(rendered, "location = /api/pools")
    stdlib_block = _extract_nginx_location_block(rendered, "location = /api/health")
    writer_token = _extract_bearer_token(writer_block, label="writer")
    stdlib_token = _extract_bearer_token(stdlib_block, label="stdlib")
    return writer_token, stdlib_token


def _extract_nginx_location_block(rendered: str, marker: str) -> str:
    marker_idx = rendered.find(marker)
    if marker_idx < 0:
        raise ValueError(f"rendered nginx config missing {marker!r} location block")
    brace_idx = rendered.find("{", marker_idx)
    if brace_idx < 0:
        raise ValueError(f"rendered nginx config has malformed {marker!r} location block")
    depth = 0
    for idx in range(brace_idx, len(rendered)):
        char = rendered[idx]
        if char == "{":
            depth += 1
        elif char == "}":
            depth -= 1
            if depth == 0:
                return rendered[marker_idx:idx + 1]
    raise ValueError(f"rendered nginx config has unterminated {marker!r} location block")


def _extract_bearer_token(block: str, *, label: str) -> str:
    match = _BEARER_HEADER_RE.search(block)
    if not match:
        raise ValueError(f"rendered nginx {label} bearer token missing")
    token = match.group(1).strip()
    if not token:
        raise ValueError(f"rendered nginx {label} bearer token empty")
    return token


def _manifest_ui_port(manifest: Mapping[str, Any]) -> int:
    ports = manifest.get("ports")
    if not isinstance(ports, Mapping):
        raise ValueError("manifest ports missing")
    port = ports.get("ui")
    if not isinstance(port, int) or not (1 <= port <= 65535):
        raise ValueError(f"manifest ui port invalid: {port!r}")
    return port


def _resolve_fixture_seed(opts: UpOptions) -> bytes:
    if opts.seed_override_hex is not None:
        try:
            seed = bytes.fromhex(opts.seed_override_hex)
        except ValueError as exc:
            raise ValueError(f"--seed must be valid hex: {exc}") from None
        if len(seed) != 32:
            raise ValueError(f"--seed must be 32 bytes, got {len(seed)}")
        return seed
    if opts.use_random_seed:
        return secrets.token_bytes(32)
    return fx.derive_seed(out_dir=opts.out_dir, chain_id=opts.chain_id)


def _host_uid() -> int:
    getuid = getattr(os, "getuid", None)
    return int(getuid()) if callable(getuid) else 1000


def _host_gid() -> int:
    getgid = getattr(os, "getgid", None)
    return int(getgid()) if callable(getgid) else 1000


def _derive_stdlib_token(seed: bytes) -> str:
    import hashlib

    if len(seed) != 32:
        raise ValueError("seed must be 32 bytes")
    domain = b"zenodex.local_testnet.stdlib_api_token.v1"
    return hashlib.blake2b(seed + b"|" + domain, digest_size=32).hexdigest()


def _resolve_zk_posture(zk_mode: str) -> dict[str, Any]:
    if zk_mode not in ZK_MODES:
        return {
            "ok": False,
            "zk_mode_requested": zk_mode,
            "zk_mode_effective": "open",
            "zk_required": False,
            "zk_fallback_reason": f"unsupported zk mode: {zk_mode}",
            "proof_verifier_kind": "misconfigured",
            "proof_artifact_hashes": {},
            "production_security_claim": False,
        }
    strict = _strict_zk_posture()
    if zk_mode == "strict":
        if strict["strict_ready"]:
            return {
                "ok": True,
                "zk_mode_requested": "strict",
                "zk_mode_effective": "strict",
                "zk_required": True,
                "zk_fallback_reason": None,
                "proof_verifier_kind": strict["proof_verifier_kind"],
                "proof_artifact_hashes": strict["proof_artifact_hashes"],
                "production_security_claim": False,
            }
        return {
            "ok": False,
            "zk_mode_requested": "strict",
            "zk_mode_effective": "strict",
            "zk_required": True,
            "zk_fallback_reason": strict["reason"],
            "proof_verifier_kind": strict["proof_verifier_kind"],
            "proof_artifact_hashes": strict["proof_artifact_hashes"],
            "production_security_claim": False,
        }
    if zk_mode == "auto-strict" and strict["strict_ready"]:
        return {
            "ok": True,
            "zk_mode_requested": "auto-strict",
            "zk_mode_effective": "strict",
            "zk_required": True,
            "zk_fallback_reason": None,
            "proof_verifier_kind": strict["proof_verifier_kind"],
            "proof_artifact_hashes": strict["proof_artifact_hashes"],
            "production_security_claim": False,
        }
    fallback_reason = None if zk_mode == "open" else strict["reason"]
    return {
        "ok": True,
        "zk_mode_requested": zk_mode,
        "zk_mode_effective": "open",
        "zk_required": False,
        "zk_fallback_reason": fallback_reason,
        "proof_verifier_kind": strict["proof_verifier_kind"],
        "proof_artifact_hashes": strict["proof_artifact_hashes"],
        "production_security_claim": False,
    }


def _strict_zk_posture() -> dict[str, Any]:
    env = _strict_zk_source_env()
    verifier_kind, verifier_error = _proof_verifier_kind_from_env(env=env)
    artifact_hashes, artifact_error = _proof_artifact_hashes_from_env(env=env)
    errors = []
    if verifier_error:
        errors.append(verifier_error)
    if verifier_kind == "disabled":
        errors.append("proof verifier command unavailable")
    elif verifier_kind != "subprocess" and not verifier_error:
        errors.append("proof verifier command misconfigured")
    if artifact_error:
        errors.append(artifact_error)
    for key in ("verifier", "circuit"):
        if key not in artifact_hashes:
            errors.append(f"proof {key} artifact hash unavailable")
    return {
        "strict_ready": not errors,
        "proof_verifier_kind": verifier_kind,
        "proof_artifact_hashes": artifact_hashes,
        "reason": "; ".join(errors) if errors else None,
    }


def _strict_zk_source_env() -> Mapping[str, str]:
    """Return the env used by local-testnet strict ZK posture checks.

    An explicit global proof verifier configuration is treated as authoritative
    and must be complete. With no explicit verifier material, the public
    fake-value local testnet uses its bundled live-wrapper fixture verifier so
    `auto-strict` starts fail-closed by default.
    """

    current = {key: value for key, value in os.environ.items()}
    if any(str(current.get(name, "")).strip() for name in GLOBAL_ZK_MATERIAL_ENV_NAMES):
        return current
    merged = dict(current)
    for key, value in _local_live_wrapper_zk_env().items():
        if key in GLOBAL_ZK_ENV_NAMES and not str(merged.get(key, "")).strip():
            merged[key] = value
    return merged


def _strict_zk_env_gap(*, expected: Mapping[str, Any] | None = None) -> str | None:
    strict = _strict_zk_posture()
    if strict["strict_ready"] is not True:
        return str(strict.get("reason") or "strict ZK verifier/artifacts unavailable")
    if expected is None:
        return None
    expected_verifier_kind = expected.get("proof_verifier_kind")
    if expected_verifier_kind and expected_verifier_kind != strict.get("proof_verifier_kind"):
        return (
            "current proof verifier kind does not match manifest "
            f"({strict.get('proof_verifier_kind')} != {expected_verifier_kind})"
        )
    expected_hashes = dict(expected.get("proof_artifact_hashes") or {})
    if expected_hashes and dict(strict.get("proof_artifact_hashes") or {}) != expected_hashes:
        return "current proof artifact hashes do not match manifest"
    return None


def _proof_verifier_kind_from_env(*, env: Mapping[str, str] | None = None) -> tuple[str, str | None]:
    source = os.environ if env is None else env
    raw = str(source.get("TAU_DEX_PROOF_VERIFIER_CMD_JSON", "")).strip()
    if not raw:
        return "disabled", None
    try:
        parsed = json.loads(raw)
    except json.JSONDecodeError as exc:
        return "misconfigured", f"TAU_DEX_PROOF_VERIFIER_CMD_JSON invalid: {exc}"
    if not isinstance(parsed, list) or not parsed or not all(isinstance(item, str) and item for item in parsed):
        return "misconfigured", "TAU_DEX_PROOF_VERIFIER_CMD_JSON must be a non-empty JSON string array"
    cmd0 = parsed[0]
    allow_path_lookup = _env_bool_from(source, "TAU_DEX_PROOF_VERIFIER_ALLOW_PATH_LOOKUP", default=False)
    if os.path.isabs(cmd0):
        if not (os.path.isfile(cmd0) and os.access(cmd0, os.X_OK)):
            return "misconfigured", f"proof verifier command is not executable: {cmd0}"
    elif allow_path_lookup:
        if shutil.which(cmd0) is None:
            return "misconfigured", f"proof verifier command not found on PATH: {cmd0}"
    else:
        return (
            "misconfigured",
            "TAU_DEX_PROOF_VERIFIER_CMD_JSON[0] must be an absolute executable path "
            "unless TAU_DEX_PROOF_VERIFIER_ALLOW_PATH_LOOKUP=true",
        )
    return "subprocess", None


def _env_bool(name: str, *, default: bool) -> bool:
    return _env_bool_from(os.environ, name, default=default)


def _env_bool_from(env: Mapping[str, str], name: str, *, default: bool) -> bool:
    raw = str(env.get(name, "")).strip().lower()
    if not raw:
        return bool(default)
    if raw in {"1", "true", "yes", "on"}:
        return True
    if raw in {"0", "false", "no", "off"}:
        return False
    return bool(default)


def _proof_artifact_hashes_from_env(*, env: Mapping[str, str] | None = None) -> tuple[dict[str, str], str | None]:
    source = os.environ if env is None else env
    hashes: dict[str, str] = {}
    errors: list[str] = []
    verifier_hash, verifier_error = _artifact_hash_from_env(
        env=source,
        json_name="TAU_DEX_PROOF_VERIFIER_ARTIFACT_JSON",
        file_name="TAU_DEX_PROOF_VERIFIER_ARTIFACT_FILE",
        label="proof verifier artifact",
        require_proof_system=False,
    )
    circuit_hash, circuit_error = _artifact_hash_from_env(
        env=source,
        json_name="TAU_DEX_PROOF_CIRCUIT_ARTIFACT_JSON",
        file_name="TAU_DEX_PROOF_CIRCUIT_ARTIFACT_FILE",
        label="proof circuit artifact",
        require_proof_system=True,
    )
    if verifier_hash is not None:
        hashes["verifier"] = verifier_hash
    if circuit_hash is not None:
        hashes["circuit"] = circuit_hash
    if verifier_error:
        errors.append(verifier_error)
    if circuit_error:
        errors.append(circuit_error)
    return hashes, "; ".join(errors) if errors else None


def _artifact_hash_from_env(
    *,
    env: Mapping[str, str] | None = None,
    json_name: str,
    file_name: str,
    label: str,
    require_proof_system: bool = False,
) -> tuple[str | None, str | None]:
    source = os.environ if env is None else env
    raw_json = str(source.get(json_name, "")).strip()
    raw_file = str(source.get(file_name, "")).strip()
    if raw_json:
        try:
            obj = json.loads(raw_json)
        except json.JSONDecodeError as exc:
            return None, f"{label} JSON invalid: {exc}"
    elif raw_file:
        try:
            artifact_path = Path(raw_file)
            if artifact_path.suffix.lower() != ".json":
                return None, f"{label} file must be JSON metadata"
            if artifact_path.is_symlink() or not artifact_path.is_file():
                return None, f"{label} file must be a regular JSON file"
            if artifact_path.stat().st_size > MAX_PROOF_ARTIFACT_METADATA_BYTES:
                return None, f"{label} file too large"
            obj = json.loads(artifact_path.read_text(encoding="utf-8"))
        except Exception as exc:
            return None, f"{label} file invalid: {exc}"
    else:
        return None, None
    if not isinstance(obj, Mapping):
        return None, f"{label} must be a JSON object"
    artifact_id = obj.get("artifact_id")
    if not isinstance(artifact_id, str) or not artifact_id.strip():
        return None, f"{label} artifact_id missing or invalid"
    if require_proof_system:
        proof_system = obj.get("proof_system")
        if not isinstance(proof_system, str) or not proof_system.strip():
            return None, f"{label} proof_system missing or invalid"
    value = obj.get("artifact_hash")
    if not isinstance(value, str) or not re.fullmatch(r"(?:0x|sha256:)[0-9a-f]{64}", value):
        return None, f"{label} artifact_hash missing or invalid"
    return value, None


def _load_manifest_if_present(path: Path, *, allow_invalid: bool = False) -> dict[str, Any] | None:
    if not path.exists():
        return None
    try:
        return mf.load_manifest(path)
    except ValueError:
        if not allow_invalid:
            raise
        raw = json.loads(path.read_text(encoding="utf-8"))
        if not isinstance(raw, dict):
            raise
        return raw


def _load_json_file(path: Path, *, label: str) -> dict[str, Any]:
    obj = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(obj, dict):
        raise ValueError(f"{label} must be a JSON object")
    return obj


def _role_materials(key_bundle: Mapping[str, Any]) -> dict[str, dict[str, Any]]:
    roles = key_bundle.get("roles")
    if not isinstance(roles, Mapping):
        raise ValueError("key bundle roles missing")
    out: dict[str, dict[str, Any]] = {}
    for role_name, raw in roles.items():
        if not isinstance(raw, Mapping):
            raise ValueError(f"key bundle role {role_name!r} invalid")
        privkey_hex = str(raw.get("privkey_hex") or "")
        public_key = str(raw.get("public_key") or "")
        if not privkey_hex or not public_key:
            raise ValueError(f"key bundle role {role_name!r} missing key material")
        out[str(role_name)] = {
            "privkey_hex": privkey_hex,
            "public_key": public_key,
            "privkey_int": int(privkey_hex[2:] if privkey_hex.startswith("0x") else privkey_hex, 16),
        }
    return out


def _init_oracle_home(home_dir: Path) -> None:
    if home_dir.exists():
        shutil.rmtree(home_dir)
    home_dir.parent.mkdir(parents=True, exist_ok=True)
    cmd = [sys.executable, "tools/zenodex_oracle.py", "init", "--home", str(home_dir)]
    result = subprocess.run(
        cmd,
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        check=False,
    )
    if result.returncode != 0:
        raise RuntimeError(
            f"oracle init failed (exit {result.returncode}): {result.stderr.strip() or result.stdout.strip()}"
        )


def _install_oracle_authority_profile(*, home_dir: Path, authority_profile_path: Path) -> None:
    authority_dir = home_dir / "authority"
    authority_dir.mkdir(parents=True, exist_ok=True)
    target = authority_dir / "production_authority_profile.json"
    shutil.copy2(authority_profile_path, target)


def _seed_ledger_controller(
    *,
    engine: cm.ComposeEngine,
    project: str,
    env: dict[str, str],
    chain_id: str,
    timeout_s: float,
) -> dict[str, Any]:
    report_out = "/tmp/localtest-controller-report.json"
    timeout_seconds = str(max(int(timeout_s), 300))
    result = cm.compose_run(
        engine=engine,
        project_name=project,
        compose_files=[COMPOSE_FILE],
        service="zeno-ledger-bootstrap",
        command=[
            "tools/zeno_ledger_multidocker_scenario.py",
            "controller",
            "--machine-count",
            "3",
            "--writer-url",
            "http://zeno-ledger-writer:8787",
            "--forwarder-url",
            "http://zeno-ledger-forwarder:8787",
            "--readonly-url",
            "http://zeno-ledger-readonly:8787",
            "--node-data-dir",
            "/app/data/local-testnet/node-writer",
            "--node-data-dir",
            "/app/data/local-testnet/node-forwarder",
            "--node-data-dir",
            "/app/data/local-testnet/node-readonly",
            "--chain-id",
            chain_id,
            "--network-id",
            chain_id,
            "--timeout-seconds",
            timeout_seconds,
            "--write-auth-token-env",
            "ZENO_LEDGER_WRITER_TOKEN",
            "--report-out",
            report_out,
        ],
        env=env,
        capture=True,
    )
    if result.returncode != 0:
        detail = result.stdout.strip() or result.stderr.strip() or "ledger controller failed"
        raise RuntimeError(f"ledger controller failed (exit {result.returncode}): {detail}")
    try:
        parsed = json.loads(result.stdout)
    except json.JSONDecodeError:
        report = _extract_json_from_text(result.stdout)
    else:
        if not isinstance(parsed, dict):
            raise RuntimeError("ledger controller did not emit a JSON object")
        report = parsed
    if report.get("ok") is not True:
        raise RuntimeError(f"ledger controller rejected: {report}")
    return report


def _seed_api_state(
    *,
    engine: cm.ComposeEngine,
    project: str,
    env: dict[str, str],
    roles: Mapping[str, Mapping[str, Any]],
    chain_id: str,
    tau_rpc_timeout_s: float,
) -> dict[str, Any]:
    payload = {
        "chain_id": chain_id,
        "market_id": DEFAULT_MARKET_ID,
        "oracle_price_e8": DEFAULT_ORACLE_PRICE_E8,
        "tau_rpc_timeout_s": max(1.0, float(tau_rpc_timeout_s)),
        "spot_asset0": DEFAULT_TAGRS_ASSET_ID,
        "spot_asset1": DEFAULT_TZDEX_ASSET_ID,
        "roles": {
            role_name: {
                "public_key": str(role["public_key"]),
                "privkey_int": int(role["privkey_int"]),
            }
            for role_name, role in sorted(roles.items())
        },
    }
    script = textwrap.dedent(
        f"""
        import json
        import sys
        import time

        from src.core.zusd import E8
        from src.integration.dex_snapshot import snapshot_with_legacy_lp_metadata_defaults, state_from_snapshot
        from src.integration.tau_net_client import (
            TauNetTcpClient,
            TauNetTcpConfig,
            sign_dex_intent_for_engine,
            sign_perp_op_for_engine,
            tau_rpc_response_is_success,
        )
        from src.integration.zeno_ledger_v0 import hash_v0
        from src.integration.zusd_tau_token import derive_zusd_tau_asset_id

        PAYLOAD = json.loads(sys.stdin.read())
        client = TauNetTcpClient(TauNetTcpConfig(host="tau-local", port=65432, timeout_s=10.0))
        quote_asset = derive_zusd_tau_asset_id(chain_id=str(PAYLOAD["chain_id"]))
        deadline = int(time.time()) + 3600
        owner = PAYLOAD["roles"]["alice"]
        counterparty = PAYLOAD["roles"]["bob"]
        native_refiller = PAYLOAD["roles"].get("carol") or counterparty

        def wait_for_tau_rpc(timeout_s=None, poll_interval_s=1.0):
            if timeout_s is None:
                timeout_s = PAYLOAD.get("tau_rpc_timeout_s", 180.0)
            deadline_at = time.monotonic() + float(timeout_s)
            last_error = "no attempts made"
            attempts = 0
            while time.monotonic() < deadline_at:
                attempts += 1
                try:
                    response = client.rpc("hello version=1")
                    if str(response).strip():
                        return {{"ok": True, "attempts": attempts, "response": str(response).strip()[:160]}}
                    last_error = "empty response"
                except Exception as exc:
                    last_error = f"{{type(exc).__name__}}: {{exc}}"
                time.sleep(float(poll_interval_s))
            raise RuntimeError(f"Tau RPC not ready before API seed: {{last_error}}")

        def load_state():
            payload = json.loads(client.getappstate(full=True))
            app_state = payload.get("app_state")
            if not isinstance(app_state, dict):
                raise RuntimeError("Tau app_state missing")
            return app_state

        def native_balance(pubkey):
            key = str(pubkey)
            if key.startswith("0x"):
                key = key[2:]
            return int(client.get_balance(key))

        def perps_market_state():
            app_state = load_state()
            dex_state = app_state.get("dex_state")
            if not isinstance(dex_state, dict):
                dex_state = app_state
            perps = dex_state.get("perps")
            if not isinstance(perps, dict):
                return None
            markets = perps.get("markets")
            if not isinstance(markets, list):
                return None
            for market in markets:
                if not isinstance(market, dict):
                    continue
                if str(market.get("market_id")) != str(PAYLOAD["market_id"]):
                    continue
                state = market.get("state")
                return state if isinstance(state, dict) else {{}}
            return None

        def perps_market_exists():
            return perps_market_state() is not None

        def perps_market_field_at_least(field, value):
            state = perps_market_state()
            if not isinstance(state, dict):
                return False
            try:
                return int(state.get(field, 0)) >= int(value)
            except Exception:
                return False

        def require_success(response, *, label):
            if not tau_rpc_response_is_success(response):
                raise RuntimeError(f"{{label}} failed: {{response}}")

        def send_and_mine(
            label,
            *,
            privkey,
            operations,
            allow_empty_mempool=False,
            resend_on_empty=False,
            accept_block_failure_if=None,
        ):
            last_send_response = None
            last_block_response = None
            max_send_attempts = 2 if resend_on_empty else 1
            for send_attempt in range(1, max_send_attempts + 1):
                send_response = client.send_signed_tx(
                    privkey=int(privkey),
                    operations=operations,
                    expiration_seconds=3600,
                )
                last_send_response = send_response
                require_success(send_response, label=f"{{label}} send")
                for block_attempt in range(1, 11):
                    block_response = client.createblock()
                    if tau_rpc_response_is_success(block_response):
                        return {{
                            "send": send_response,
                            "createblock": block_response,
                            "createblock_attempts": block_attempt,
                            "send_attempts": send_attempt,
                        }}
                    last_block_response = block_response
                    if "Mempool is empty" not in str(block_response):
                        break
                    time.sleep(0.5)
                if accept_block_failure_if is not None and accept_block_failure_if():
                    return {{
                        "send": last_send_response,
                        "createblock": last_block_response,
                        "send_attempts": send_attempt,
                        "target_state_already_materialized": True,
                    }}
                if (
                    resend_on_empty
                    and send_attempt < max_send_attempts
                    and "Mempool is empty" in str(last_block_response)
                ):
                    time.sleep(0.5)
                    continue
                break
            if allow_empty_mempool and "Mempool is empty" in str(last_block_response):
                return {{
                    "send": last_send_response,
                    "createblock": last_block_response,
                    "createblock_attempts": 10,
                    "send_attempts": max_send_attempts,
                    "empty_mempool_accepted": True,
                }}
            if accept_block_failure_if is not None and accept_block_failure_if():
                return {{
                    "send": last_send_response,
                    "createblock": last_block_response,
                    "send_attempts": max_send_attempts,
                    "target_state_already_materialized": True,
                }}
            require_success(last_block_response, label=f"{{label}} createblock")
            return {{"send": last_send_response, "createblock": last_block_response, "send_attempts": max_send_attempts}}

        report = {{
            "ok": True,
            "chain_id": PAYLOAD["chain_id"],
            "quote_asset": quote_asset,
            "market_id": PAYLOAD["market_id"],
            "steps": {{}},
        }}

        report["steps"]["tau_rpc_ready"] = wait_for_tau_rpc()
        report["steps"]["materialize_fixture_native_balances"] = {{}}
        for role_name, role in sorted(PAYLOAD["roles"].items()):
            report["steps"]["materialize_fixture_native_balances"][role_name] = send_and_mine(
                f"materialize_fixture_native_balance_{{role_name}}",
                privkey=role["privkey_int"],
                operations={{
                    "1": [
                        [
                            str(role["public_key"])[2:],
                            str(role["public_key"])[2:],
                            str({DEFAULT_FIXTURE_NATIVE_MATERIALIZE_E8}),
                        ]
                    ]
                }},
            )
        spot_asset0 = PAYLOAD["spot_asset0"]
        spot_asset1 = PAYLOAD["spot_asset1"]
        report["steps"]["prefund_fixture_test_assets"] = send_and_mine(
            "prefund_fixture_test_assets",
            privkey=owner["privkey_int"],
            operations={{
                "7": {{
                    "mint": [
                        {{
                            "pubkey": str(role["public_key"]),
                            "asset": asset,
                            "amount": {DEFAULT_FIXTURE_TEST_ASSET_PREFUND},
                        }}
                        for role in PAYLOAD["roles"].values()
                        for asset in (spot_asset0, spot_asset1)
                    ]
                }}
            }},
        )
        report["steps"]["bootstrap_oracle_and_deposit"] = send_and_mine(
            "bootstrap_oracle_and_deposit",
            privkey=owner["privkey_int"],
            operations={{
                "11": [
                    {{
                        "module": "ZUSDFinance",
                        "version": "0.1",
                        "action": "bootstrap_oracle",
                        "price_e8": int(PAYLOAD["oracle_price_e8"]),
                        "nonce": 1,
                        "deadline": deadline,
                    }},
                    {{
                        "module": "ZUSDFinance",
                        "version": "0.1",
                        "action": "deposit_collateral",
                        "owner_pubkey": owner["public_key"],
                        "amount_e8": {DEFAULT_ZUSD_BOOTSTRAP_COLLATERAL_E8},
                        "nonce": 2,
                        "deadline": deadline,
                    }},
                ]
            }},
        )
        report["steps"]["mint_zusd"] = send_and_mine(
            "mint_zusd",
            privkey=owner["privkey_int"],
            operations={{
                "11": [{{
                    "module": "ZUSDFinance",
                    "version": "0.1",
                    "action": "mint_zusd",
                    "owner_pubkey": owner["public_key"],
                    "amount_e8": {DEFAULT_ZUSD_BOOTSTRAP_MINT_E8},
                    "nonce": 3,
                    "deadline": deadline,
                }}]
            }},
            resend_on_empty=True,
            accept_block_failure_if=lambda: int(
                (
                    (load_state().get("zusd_monetary") or {{}}).get("core") or {{}}
                ).get("debt_e8", 0)
            ) >= {DEFAULT_ZUSD_BOOTSTRAP_MINT_E8},
        )
        report["steps"]["refill_owner_native_collateral"] = send_and_mine(
            "refill_owner_native_collateral",
            privkey=native_refiller["privkey_int"],
            operations={{
                "1": [
                    [
                        str(native_refiller["public_key"])[2:],
                        str(owner["public_key"])[2:],
                        str({DEFAULT_ZUSD_BOOTSTRAP_COLLATERAL_E8}),
                    ]
                ]
                }},
            resend_on_empty=True,
            accept_block_failure_if=lambda: native_balance(owner["public_key"]) >= {DEFAULT_ZUSD_BOOTSTRAP_COLLATERAL_E8},
        )
        report["steps"]["prefund_counterparty_zusd"] = send_and_mine(
            "prefund_counterparty_zusd",
            privkey=owner["privkey_int"],
            operations={{
                "9": [{{
                    "module": "TauToken",
                    "version": "0.1",
                    "action": "transfer",
                    "asset": quote_asset,
                    "sender_pubkey": owner["public_key"],
                    "to_pubkey": counterparty["public_key"],
                    "amount": {DEFAULT_FIXTURE_ZUSD_COUNTERPARTY_PREFUND},
                    "nonce": 1,
                    "deadline": deadline,
                }}]
            }},
        )

        init_market = {{
            "module": "TauPerp",
            "version": "1.0",
            "market_id": PAYLOAD["market_id"],
            "action": "init_market_2p",
            "quote_asset": quote_asset,
            "account_a_pubkey": owner["public_key"],
            "account_b_pubkey": counterparty["public_key"],
            "deadline": deadline,
            "nonce_a": 1,
            "nonce_b": 1,
        }}
        init_market["sig_a"] = sign_perp_op_for_engine(
            init_market,
            privkey=int(owner["privkey_int"]),
            chain_id=str(PAYLOAD["chain_id"]),
            signer_pubkey=str(owner["public_key"]),
            nonce=1,
        )
        init_market["sig_b"] = sign_perp_op_for_engine(
            init_market,
            privkey=int(counterparty["privkey_int"]),
            chain_id=str(PAYLOAD["chain_id"]),
            signer_pubkey=str(counterparty["public_key"]),
            nonce=1,
        )
        report["steps"]["init_market_2p"] = send_and_mine(
            "init_market_2p",
            privkey=owner["privkey_int"],
            operations={{"8": [init_market]}},
            resend_on_empty=True,
            accept_block_failure_if=perps_market_exists,
        )
        report["steps"]["perps_deposit_collateral"] = send_and_mine(
            "perps_deposit_collateral",
            privkey=owner["privkey_int"],
            operations={{
                "8": [{{
                    "module": "TauPerp",
                    "version": "1.0",
                    "market_id": PAYLOAD["market_id"],
                    "action": "deposit_collateral",
                    "account_pubkey": owner["public_key"],
                    "amount": 25,
                }}]
            }},
            resend_on_empty=True,
            accept_block_failure_if=lambda: perps_market_field_at_least("collateral_e8_a", 25),
        )
        report["steps"]["perps_advance_epoch"] = send_and_mine(
            "perps_advance_epoch",
            privkey=owner["privkey_int"],
            operations={{
                "8": [{{
                    "module": "TauPerp",
                    "version": "1.0",
                    "market_id": PAYLOAD["market_id"],
                    "action": "advance_epoch",
                    "delta": 1,
                }}]
            }},
            allow_empty_mempool=True,
            resend_on_empty=True,
            accept_block_failure_if=lambda: perps_market_field_at_least("now_epoch", 1),
        )

        def dex_pool_count():
            state = load_state()
            dex_state = state.get("dex_state")
            pools = dex_state.get("pools") if isinstance(dex_state, dict) else None
            return len(pools) if isinstance(pools, list) else 0

        if dex_pool_count() == 0:
            dex_snapshot = load_state().get("dex_state")
            dex_state = state_from_snapshot(
                snapshot_with_legacy_lp_metadata_defaults(dex_snapshot if isinstance(dex_snapshot, dict) else {{}})
            )
            owner_nonce = int(dex_state.nonces.get_last(owner["public_key"])) + 1
            intent_id = hash_v0(
                "localtest-autotrader-spot-pool-v1",
                {{
                    "owner": owner["public_key"],
                    "nonce": owner_nonce,
                    "asset0": spot_asset0,
                    "asset1": spot_asset1,
                }},
            )
            create_pool_intent = {{
                "module": "TauSwap",
                "version": "0.1",
                "kind": "CREATE_POOL",
                "intent_id": intent_id,
                "sender_pubkey": owner["public_key"],
                "deadline": deadline,
                "nonce": owner_nonce,
                "asset0": spot_asset0,
                "asset1": spot_asset1,
                "fee_bps": 30,
                "amount0": 100_000,
                "amount1": 200_000,
            }}
            create_pool_intent["signature"] = sign_dex_intent_for_engine(
                create_pool_intent,
                privkey=int(owner["privkey_int"]),
                chain_id=str(PAYLOAD["chain_id"]),
            )
            report["steps"]["autotrader_spot_pool"] = send_and_mine(
                "autotrader_spot_pool",
                privkey=owner["privkey_int"],
                operations={{
                    "7": {{
                        "mint": [
                            {{"pubkey": owner["public_key"], "asset": spot_asset0, "amount": 100_000}},
                            {{"pubkey": owner["public_key"], "asset": spot_asset1, "amount": 200_000}},
                        ]
                    }},
                    "5": [create_pool_intent],
                }},
            )

        def dex_balance(pubkey, asset):
            dex_snapshot = load_state().get("dex_state")
            balances = dex_snapshot.get("balances") if isinstance(dex_snapshot, dict) else None
            if not isinstance(balances, list):
                return 0
            total = 0
            for row in balances:
                if not isinstance(row, dict):
                    continue
                if str(row.get("pubkey")).lower() != str(pubkey).lower():
                    continue
                if str(row.get("asset")).lower() != str(asset).lower():
                    continue
                total += int(row.get("amount", 0))
            return total

        owner_spot_asset0_balance = dex_balance(owner["public_key"], spot_asset0)
        if owner_spot_asset0_balance < 10_000:
            report["steps"]["autotrader_owner_spot_faucet"] = send_and_mine(
                "autotrader_owner_spot_faucet",
                privkey=owner["privkey_int"],
                operations={{
                    "7": {{
                        "mint": [
                            {{
                                "pubkey": owner["public_key"],
                                "asset": spot_asset0,
                                "amount": 50_000 - owner_spot_asset0_balance,
                            }}
                        ]
                    }}
                }},
            )

        app_state = load_state()
        zusd_state = app_state.get("zusd_monetary")
        dex_state = app_state.get("dex_state")
        if not isinstance(zusd_state, dict):
            raise RuntimeError("zusd_monetary state missing after seed")
        if not isinstance(dex_state, dict):
            raise RuntimeError("dex_state missing after seed")
        perps = dex_state.get("perps")
        markets = perps.get("markets") if isinstance(perps, dict) else None
        if not isinstance(markets, list) or not markets:
            raise RuntimeError("perps markets missing after seed")
        market_row = None
        for row in markets:
            if isinstance(row, dict) and row.get("market_id") == PAYLOAD["market_id"]:
                market_row = row
                break
        if market_row is None:
            raise RuntimeError("seeded perps market not found")

        balances = dex_state.get("balances")
        owner_zusd_balance = 0
        if isinstance(balances, list):
            for row in balances:
                if not isinstance(row, dict):
                    continue
                if str(row.get("pubkey")).strip().lower() != str(owner["public_key"]).strip().lower():
                    continue
                if str(row.get("asset")).strip().lower() != str(quote_asset).strip().lower():
                    continue
                owner_zusd_balance = int(row.get("amount", 0))
                break
        core = zusd_state.get("core")
        report["zusd"] = {{
            "owner_balance_units": owner_zusd_balance,
            "core": core,
        }}
        report["fixture_prefund"] = {{
            "role_count": len(PAYLOAD["roles"]),
            "native_materialize_e8": {DEFAULT_FIXTURE_NATIVE_MATERIALIZE_E8},
            "test_asset_prefund_amount": {DEFAULT_FIXTURE_TEST_ASSET_PREFUND},
            "counterparty_zusd_prefund_amount": {DEFAULT_FIXTURE_ZUSD_COUNTERPARTY_PREFUND},
            "assets": [spot_asset0, spot_asset1],
            "roles": sorted(PAYLOAD["roles"].keys()),
        }}
        report["perps"] = {{
            "market_count": len(markets),
            "market": market_row,
        }}
        print(json.dumps(report, sort_keys=True))
        """
    ).strip()
    result = cm.compose_run(
        engine=engine,
        project_name=project,
        compose_files=[COMPOSE_FILE],
        service="zenodex-api",
        command=["-c", script],
        env=env,
        extra_args=["-T"],
        capture=True,
        input_text=json.dumps(payload, sort_keys=True),
    )
    if result.returncode != 0:
        raise RuntimeError(result.stderr.strip() or result.stdout.strip() or "Tau seed bootstrap failed")
    report = _extract_json_from_text(result.stdout)
    if report.get("ok") is not True:
        raise RuntimeError(f"Tau seed bootstrap failed: {report}")
    return report


def _wait_for_base_services(*, ui_base: str, timeout_s: float) -> None:
    deadline = time.monotonic() + timeout_s
    last_error = "no attempts made"
    while time.monotonic() < deadline:
        probe = _probe_base_services(ui_base=ui_base)
        if probe["ok"]:
            return
        last_error = json.dumps(probe, sort_keys=True)
        time.sleep(1.0)
    raise TimeoutError(f"base services did not become ready: {last_error}")


def _wait_for_lane_readiness(
    *,
    ui_base: str,
    timeout_s: float,
    manifest: Mapping[str, Any] | None = None,
) -> dict[str, Any]:
    deadline = time.monotonic() + timeout_s
    last_report: dict[str, Any] = {"ok": False, "checks": {}, "lanes": {}}
    while time.monotonic() < deadline:
        last_report = (
            _collect_lane_readiness(ui_base=ui_base)
            if manifest is None
            else _collect_lane_readiness(ui_base=ui_base, manifest=manifest)
        )
        if last_report.get("ok") is True:
            return last_report
        time.sleep(1.0)
    raise TimeoutError(
        "lane readiness checks did not pass: "
        + json.dumps(last_report.get("checks") or {}, sort_keys=True)
    )


def _probe_base_services(*, ui_base: str) -> dict[str, Any]:
    ui_health = _safe_get_json(f"{ui_base}/health")
    api_health = _safe_get_json(f"{ui_base}/api/health")
    oracle_health = _safe_get_json(f"{ui_base}/api/oracle/health")
    ui_contract = _probe_ui_surface_contract(ui_base=ui_base)
    return {
        "ok": (
            bool(ui_health.get("ok"))
            and bool(api_health.get("ok"))
            and bool(oracle_health.get("ok"))
            and bool(ui_contract.get("ok"))
        ),
        "ui": ui_health,
        "api": api_health,
        "oracle": oracle_health,
        "ui_surface_contract": ui_contract,
    }


def _probe_ui_surface_contract(*, ui_base: str) -> dict[str, Any]:
    contract = _safe_get_json(f"{ui_base}/zenodex-ui-contract.json")
    runtime_config = _safe_get_json(f"{ui_base}/zenodex-config.json")
    errors: list[str] = []
    try:
        expected_contract = ng.load_ui_surface_contract()
        expected_version = str(expected_contract["version"])
        expected_hash = ng.ui_surface_contract_hash()
    except Exception as exc:
        return {
            "ok": False,
            "errors": [f"source UI surface contract invalid: {type(exc).__name__}: {exc}"],
            "served_contract": contract,
            "runtime_config": runtime_config,
        }
    if contract.get("ok") is not True:
        errors.append("served UI surface contract unavailable")
    else:
        if contract.get("schema") != expected_contract.get("schema"):
            errors.append("served UI surface contract schema mismatch")
        if contract.get("version") != expected_version:
            errors.append(
                f"served UI surface contract version mismatch: {contract.get('version')} != {expected_version}"
            )
    if runtime_config.get("ok") is not True:
        errors.append("runtime UI config unavailable")
    else:
        if runtime_config.get("demoMode") is not False:
            errors.append("runtime config must disable demoMode for local testnet")
        if runtime_config.get("allowDemoMode") is not False:
            errors.append("runtime config must disallow demo mode for local testnet")
        if runtime_config.get("uiSurfaceContractSchema") != expected_contract.get("schema"):
            errors.append("runtime UI surface contract schema mismatch")
        if runtime_config.get("uiSurfaceContractVersion") != expected_version:
            errors.append("runtime UI surface contract version mismatch")
        if runtime_config.get("uiSurfaceContractHash") != expected_hash:
            errors.append("runtime UI surface contract hash mismatch")
    return {
        "ok": not errors,
        "errors": errors,
        "expected_version": expected_version,
        "expected_hash": expected_hash,
        "served_contract": contract,
        "runtime_config": runtime_config,
    }


def _collect_lane_readiness(*, ui_base: str, manifest: Mapping[str, Any] | None = None) -> dict[str, Any]:
    lanes = {
        "spot": _safe_get_json(f"{ui_base}/api/pools"),
        "zusd_monetary": _safe_get_json(f"{ui_base}/api/zusd/monetary/status"),
        "perps_wallet": _safe_get_json(f"{ui_base}/api/perps/wallet/status", timeout_s=15.0),
        "autotrader": _safe_get_json(f"{ui_base}/api/strategy/autotrader/status"),
        "oracle_health": _safe_get_json(f"{ui_base}/api/oracle/health"),
        "oracle_dashboard": _safe_get_json(f"{ui_base}/api/oracle/dashboard"),
        "confidential": _safe_get_json(f"{ui_base}/api/confidential/status"),
    }
    checks = {
        "spot": bool(lanes["spot"].get("ok")) and isinstance(lanes["spot"].get("pools"), list) and len(lanes["spot"]["pools"]) > 0,
        "zusd_monetary": bool(lanes["zusd_monetary"].get("ok"))
        and bool(((lanes["zusd_monetary"].get("status") or {}).get("node_reachable")))
        and bool(((lanes["zusd_monetary"].get("status") or {}).get("monetary_state_present"))),
        "perps_wallet": bool(lanes["perps_wallet"].get("ok"))
        and bool(((lanes["perps_wallet"].get("status") or {}).get("node_reachable")))
        and int(((lanes["perps_wallet"].get("status") or {}).get("market_count") or 0)) >= 1
        and bool((((lanes["perps_wallet"].get("status") or {}).get("wallet_authority") or {}).get("ok")))
        and bool((((lanes["perps_wallet"].get("status") or {}).get("oracle_authority") or {}).get("ok"))),
        "autotrader": bool(lanes["autotrader"].get("ok"))
        and bool((((lanes["autotrader"].get("status") or {}).get("supervisor") or {}).get("ok"))),
        "oracle_health": bool(lanes["oracle_health"].get("ok")),
        "oracle_dashboard": bool(lanes["oracle_dashboard"].get("ok")),
        "confidential": bool(lanes["confidential"].get("ok")),
    }
    key_management_authority = _key_management_authority_readiness(manifest=manifest, lanes=lanes)
    zk_posture = _zk_posture_from_manifest(manifest)
    tokenomics_authority_ready = bool(key_management_authority.get("tokenomics_authority_ready"))
    if not checks:
        raise RuntimeError("no local-testnet lane readiness checks registered")
    return {
        "ok": all(checks.values()),
        "checks": checks,
        "lanes": lanes,
        "zk_posture": zk_posture,
        "key_management_authority": key_management_authority,
        "tokenomics_lane": {
            "enabled": tokenomics_authority_ready,
            "rejection_code": None
            if tokenomics_authority_ready
            else "TOKENOMICS_AUTHORITY_NOT_READY",
        },
    }


def _zk_posture_from_manifest(manifest: Mapping[str, Any] | None) -> dict[str, Any]:
    if manifest is None:
        posture = _resolve_zk_posture(DEFAULT_ZK_MODE)
    else:
        posture = {
            "zk_mode_requested": manifest.get("zk_mode_requested", "open"),
            "zk_mode_effective": manifest.get("zk_mode_effective", "open"),
            "zk_required": manifest.get("zk_required") is True,
            "zk_fallback_reason": manifest.get("zk_fallback_reason"),
            "proof_verifier_kind": manifest.get("proof_verifier_kind", "disabled"),
            "proof_artifact_hashes": dict(manifest.get("proof_artifact_hashes") or {}),
            "production_security_claim": manifest.get("production_security_claim") is True,
        }
    return {
        "zk_mode_requested": posture.get("zk_mode_requested"),
        "zk_mode_effective": posture.get("zk_mode_effective"),
        "zk_required": posture.get("zk_required") is True,
        "zk_fallback_reason": posture.get("zk_fallback_reason"),
        "proof_verifier_kind": posture.get("proof_verifier_kind"),
        "proof_artifact_hashes": dict(posture.get("proof_artifact_hashes") or {}),
        "production_security_claim": False if posture.get("production_security_claim") is not True else True,
    }


def _key_management_authority_readiness(
    *,
    manifest: Mapping[str, Any] | None,
    lanes: Mapping[str, Any],
) -> dict[str, Any]:
    perps_payload = lanes.get("perps_wallet")
    perps_status = perps_payload.get("status") if isinstance(perps_payload, Mapping) else None
    wallet_authority = perps_status.get("wallet_authority") if isinstance(perps_status, Mapping) else None
    if not isinstance(wallet_authority, Mapping):
        return {
            "tokenomics_authority_ready": False,
            "status": "blocked",
            "rejection_code": "TOKENOMICS_AUTHORITY_NOT_READY",
            "readiness_gaps": ["perps wallet authority status unavailable"],
            "production_security_claim": False,
            "secret_sharing": _secret_sharing_status(None),
        }

    active_signer_count = _safe_int(wallet_authority.get("active_signer_count"))
    threshold = _safe_int(wallet_authority.get("threshold"))
    recoverable_active_key_count = _safe_int(wallet_authority.get("recoverable_active_key_count"))
    signer_registry_threshold_satisfied = threshold > 0 and active_signer_count >= threshold
    recovery_policy_complete = active_signer_count > 0 and recoverable_active_key_count == active_signer_count
    checks = {
        "wallet_authority_status_ready": wallet_authority.get("ok") is True and wallet_authority.get("status") == "ready",
        "wallet_authority_profile_present": wallet_authority.get("production_wallet_authority") is True,
        "wallet_authority_identity_present": isinstance(wallet_authority.get("authority_id"), str)
        and bool(str(wallet_authority.get("authority_id")).strip()),
        "wallet_authority_hashes_present": all(
            _is_root_hash(wallet_authority.get(key))
            for key in ("wallet_authority_hash", "signer_registry_hash", "key_manager_hash")
        ),
        "signer_registry_threshold_satisfied": signer_registry_threshold_satisfied,
        "recovery_policy_for_every_active_key": recovery_policy_complete,
        "recovery_exercise_ready": _nested_ready(wallet_authority, "recovery_exercise", "recovery_exercise_ready"),
        "rotation_exercise_ready": _nested_ready(wallet_authority, "rotation_exercise", "rotation_exercise_ready"),
        "device_approval_ready": _nested_ready(wallet_authority, "device_approval_exercise", "device_approval_ready"),
        "signer_ceremony_ready": _nested_ready(wallet_authority, "signer_ceremony", "signer_ceremony_ready"),
        "hardware_custody_ready": _nested_ready(wallet_authority, "hardware_custody", "hardware_custody_ready"),
        "encrypted_sss_backup_ready": _encrypted_sss_backup_ready(wallet_authority),
    }
    public_scan_payload = {
        "manifest": {} if manifest is None else dict(manifest),
        "lanes": dict(lanes),
    }
    no_raw_private_key_fields = not _contains_private_key_field(public_scan_payload)
    checks["no_raw_private_key_fields"] = no_raw_private_key_fields

    gaps = _key_management_gaps(checks)
    for item in wallet_authority.get("readiness_gaps", []):
        if isinstance(item, str) and item:
            gaps.append(item)
    tokenomics_authority_ready = not gaps
    encrypted_sss = (
        wallet_authority.get("encrypted_sss_backup")
        if isinstance(wallet_authority.get("encrypted_sss_backup"), Mapping)
        else None
    )
    hardware_custody = (
        wallet_authority.get("hardware_custody")
        if isinstance(wallet_authority.get("hardware_custody"), Mapping)
        else None
    )
    zk_posture = _zk_posture_from_manifest(manifest)
    production_checks = {
        "local_tokenomics_authority_ready": tokenomics_authority_ready,
        "strict_zk_ready": zk_posture.get("zk_required") is True
        and zk_posture.get("zk_mode_effective") == "strict"
        and zk_posture.get("proof_verifier_kind") == "subprocess",
        "production_hardware_custody_ready": isinstance(hardware_custody, Mapping)
        and hardware_custody.get("production_hardware_custody_ready") is True,
        "live_provider_delivery_ready": isinstance(encrypted_sss, Mapping)
        and encrypted_sss.get("live_provider_delivery_ready") is True,
        "external_audit_ready": isinstance(encrypted_sss, Mapping)
        and encrypted_sss.get("external_audit_ready") is True,
    }
    production_authority_ready = all(production_checks.values())
    return {
        "schema": "zenodex.local_testnet.key_management_authority_readiness.v0",
        "tokenomics_authority_ready": tokenomics_authority_ready,
        "status": "ready" if tokenomics_authority_ready else "blocked",
        "rejection_code": None if tokenomics_authority_ready else "TOKENOMICS_AUTHORITY_NOT_READY",
        "checks": checks,
        "readiness_gaps": gaps,
        "authority_id": wallet_authority.get("authority_id"),
        "wallet_authority_hash": wallet_authority.get("wallet_authority_hash"),
        "signer_registry_hash": wallet_authority.get("signer_registry_hash"),
        "key_manager_hash": wallet_authority.get("key_manager_hash"),
        "active_signer_count": active_signer_count,
        "threshold": threshold,
        "recoverable_active_key_count": recoverable_active_key_count,
        "tokenomics_admin_payload_kind": "tokenomics-admin",
        "tokenomics_admin_multisig_threshold_satisfied": signer_registry_threshold_satisfied,
        "custody_mode": "hardware_or_local_testnet_fixture",
        "production_authority_ready": production_authority_ready,
        "production_checks": production_checks,
        "production_security_claim": False,
        "secret_sharing": _secret_sharing_status(encrypted_sss),
        "encrypted_sss_backup": encrypted_sss,
    }


def _secret_sharing_status(encrypted_sss_backup: Mapping[str, Any] | None) -> dict[str, Any]:
    if isinstance(encrypted_sss_backup, Mapping) and encrypted_sss_backup.get("encrypted_sss_backup_ready") is True:
        return {
            "sss_implemented": True,
            "recovery_model": "guardian-threshold-social-recovery-plus-encrypted-sss-backup",
            "backup_mode": "client-side-encrypted-share-envelopes",
            "threshold": encrypted_sss_backup.get("threshold"),
            "share_count": encrypted_sss_backup.get("share_count"),
            "storage_provider_kinds": encrypted_sss_backup.get("storage_provider_kinds"),
            "provider_delivery_ready": encrypted_sss_backup.get("provider_delivery_ready"),
            "live_provider_delivery_ready": encrypted_sss_backup.get("live_provider_delivery_ready"),
            "delivery_modes": encrypted_sss_backup.get("delivery_modes"),
            "recovery_drill_ready": encrypted_sss_backup.get("recovery_drill_ready"),
            "replay_recovery_ready": encrypted_sss_backup.get("replay_recovery_ready"),
            "hostile_share_tests_ready": encrypted_sss_backup.get("hostile_share_tests_ready"),
            "replay_hostile_tests_ready": encrypted_sss_backup.get("replay_hostile_tests_ready"),
            "server_side_reconstitution": False,
            "external_audit_ready": encrypted_sss_backup.get("external_audit_ready"),
            "production_security_claim": False,
            "claim": (
                "Encrypted SSS fixture evidence is ready for local-testnet. "
                "External email/cloud/offline delivery requires configured provider adapters."
            ),
        }
    return {
        "sss_implemented": False,
        "recovery_model": "guardian-threshold-social-recovery",
        "claim": "Encrypted SSS backup is not ready for this local-testnet authority status.",
    }


def _nested_ready(obj: Mapping[str, Any], key: str, ready_key: str) -> bool:
    nested = obj.get(key)
    return isinstance(nested, Mapping) and nested.get(ready_key) is True


def _encrypted_sss_backup_ready(wallet_authority: Mapping[str, Any]) -> bool:
    nested = wallet_authority.get("encrypted_sss_backup")
    return (
        isinstance(nested, Mapping)
        and nested.get("encrypted_sss_backup_ready") is True
        and nested.get("replay_recovery_ready") is True
        and nested.get("subject_public_key_matches") is True
        and nested.get("replay_hostile_tests_ready") is True
        and nested.get("provider_delivery_ready") is True
        and nested.get("raw_material_absent") is True
    )


def _safe_int(value: object) -> int:
    return int(value) if isinstance(value, int) and not isinstance(value, bool) else 0


def _is_root_hash(value: object) -> bool:
    return isinstance(value, str) and re.fullmatch(r"0x[0-9a-f]{64}", value) is not None


def _key_management_gaps(checks: Mapping[str, bool]) -> list[str]:
    labels = {
        "wallet_authority_status_ready": "wallet authority status is not ready",
        "wallet_authority_profile_present": "wallet authority profile is not ready",
        "wallet_authority_identity_present": "wallet authority id is missing",
        "wallet_authority_hashes_present": "wallet authority hashes are missing or invalid",
        "signer_registry_threshold_satisfied": "signer registry threshold is not satisfied",
        "recovery_policy_for_every_active_key": "recovery policy is missing for at least one active authority key",
        "recovery_exercise_ready": "recovery exercise is not ready",
        "rotation_exercise_ready": "rotation exercise is not ready",
        "device_approval_ready": "device approval is not ready",
        "signer_ceremony_ready": "signer ceremony is not ready",
        "hardware_custody_ready": "hardware custody or fixture custody is not ready",
        "encrypted_sss_backup_ready": "encrypted SSS backup is not ready",
        "no_raw_private_key_fields": "raw private-key field detected in public status or manifest",
    }
    return [label for key, label in labels.items() if checks.get(key) is not True]


_PRIVATE_KEY_FIELD_RE = re.compile(
    r"(privkey|private_key|privatekey|secret_key|secretkey|mnemonic|seed_phrase|seedphrase|raw_private_key|private_key_hex)"
)
_SAFE_SECRET_STATUS_FIELDS = frozenset({"no_raw_private_key_exposure"})


def _contains_private_key_field(value: object) -> bool:
    if isinstance(value, Mapping):
        for key, item in value.items():
            if isinstance(key, str):
                lowered = key.lower()
                if lowered not in _SAFE_SECRET_STATUS_FIELDS and _PRIVATE_KEY_FIELD_RE.search(lowered):
                    return True
            if _contains_private_key_field(item):
                return True
        return False
    if isinstance(value, list):
        return any(_contains_private_key_field(item) for item in value)
    return False


def _run_feature_smoke(*, ui_base: str, paths: mf.ManifestPaths, manifest: Mapping[str, Any]) -> dict[str, Any]:
    key_bundle_path = Path(str(manifest["fixture_paths"]["key_bundle"]))
    roles = _role_materials(_load_json_file(key_bundle_path, label="key bundle"))
    seed_report = _load_json_file(paths.reports_dir / "api_seed_report.json", label="api seed report")
    deadline = int(time.time()) + 3600
    run_id = _smoke_run_id()
    chain_id = str(manifest["chain_id"])
    confidential_fixture = _confidential_local_fixture_from_manifest(manifest=manifest, paths=paths)
    zk_required = manifest.get("zk_required") is True

    # Fund Alice with release-facing test assets so spot swap tests succeed.
    alice_pubkey = _role_pubkey(roles, "alice")
    faucet_url = f"{ui_base}/api/testnet/faucet"
    _post_json(
        faucet_url,
        {
            "to_pubkey": alice_pubkey,
            "asset": DEFAULT_TAGRS_ASSET_ID,
            "amount": 100_000,
            "local_fixture_mode": True,
            "tx_id": f"local-smoke-alice-fund-tagrs-{run_id}",
        },
    )
    _post_json(
        faucet_url,
        {
            "to_pubkey": alice_pubkey,
            "asset": DEFAULT_TZDEX_ASSET_ID,
            "amount": 100_000,
            "local_fixture_mode": True,
            "tx_id": f"local-smoke-alice-fund-tzdex-{run_id}",
        },
    )

    checks: dict[str, Any] = {}

    def capture(name: str, fn: Any) -> None:
        try:
            checks[name] = fn()
        except Exception as exc:
            checks[name] = {"ok": False, "error": f"{type(exc).__name__}: {exc}"}

    capture(
        "spot_swap",
        lambda: _summarize_response(
            _post_json(
                f"{ui_base}/api/swap",
                _build_signed_live_swap_payload(
                    ui_base=ui_base,
                    roles=roles,
                    chain_id=chain_id,
                    sender_role="alice",
                    amount_in=100,
                    min_amount_out=0,
                    deadline=deadline,
                    from_symbol="tAGRS",
                    to_symbol="tZDEX",
                ),
            ),
            require_any=("tx_accepted", "ok"),
        ),
    )
    capture(
        "complex_grouped_transactions",
        lambda: _run_complex_grouped_transaction_smoke(
            ui_base=ui_base,
            roles=roles,
            chain_id=chain_id,
            deadline=deadline,
            run_id=run_id,
        ),
    )
    capture(
        "zusd_monetary_advance_epoch",
        lambda: _summarize_response(
            _post_json(
                f"{ui_base}/api/zusd/monetary/submit",
                _with_local_fixture_zk_proof(
                    {
                        "action": "advance_epoch",
                        "actor_pubkey": _role_pubkey(roles, "alice"),
                        "delta": 1,
                        "deadline": deadline,
                        "tx_fee_limit": "0",
                        "signer_privkey": _role_privkey_int(roles, "alice"),
                    },
                    zk_required=zk_required,
                ),
            ),
        ),
    )
    capture(
        "perps_publish_clearing_price",
        lambda: _run_perps_wallet_cycle_smoke(
            ui_base=ui_base,
            market_id=str(seed_report["market_id"]),
            roles=roles,
            deadline=deadline,
            zk_required=zk_required,
        ),
    )
    capture(
        "oracle_write_flow",
        lambda: _run_oracle_write_smoke(ui_base=ui_base, run_id=run_id),
    )
    capture(
        "autotrader_live_prepare",
        lambda: _summarize_response(
            _post_json(
                f"{ui_base}/api/strategy/autotrader/prepare",
                {
                    "acknowledge_experimental_live_risk": True,
                    "signer_privkey": _role_privkey_int(roles, "alice"),
                    "chain_id": chain_id,
                },
            ),
        ),
    )
    capture(
        "confidential_runtime_execute",
        lambda: _summarize_response(
            _post_json(
                f"{ui_base}/api/confidential/attestation/execute",
                _confidential_runtime_payload(run_id=run_id, fixture=confidential_fixture),
            ),
        ),
    )

    return {
        "ok": all(bool(value.get("ok")) for value in checks.values()),
        "checks": checks,
        "run_id": run_id,
    }


def _materialize_release_native_collateral(
    *,
    engine: cm.ComposeEngine,
    compose_project: str,
    env: Mapping[str, str],
    roles: Mapping[str, Mapping[str, Any]],
    amount_e8: int,
) -> dict[str, Any]:
    owner = roles["alice"]
    preferred_refiller_names = [
        "carol",
        "guardian_1",
        "guardian_2",
        "guardian_3",
        "operator",
        "oracle_authority",
        "perps_wallet_authority",
        "bob",
        "autotrader_supervisor",
    ]
    refiller_roles = {
        name: {
            "public_key": role["public_key"],
            "privkey_int": role.get("privkey_int"),
        }
        for name, role in roles.items()
        if name != "alice" and role.get("privkey_int") is not None
    }
    payload = {
        "owner_pubkey": owner["public_key"],
        "refiller_roles": refiller_roles,
        "preferred_refiller_names": preferred_refiller_names,
        "amount_e8": int(amount_e8),
    }
    script = textwrap.dedent(
        """
        import json
        import sys
        import time

        from src.integration.tau_net_client import TauNetTcpClient, TauNetTcpConfig, tau_rpc_response_is_success

        PAYLOAD = json.loads(sys.stdin.read())
        client = TauNetTcpClient(TauNetTcpConfig(host="tau-local", port=65432, timeout_s=10.0))
        owner_pubkey = str(PAYLOAD["owner_pubkey"])
        owner_rpc = owner_pubkey[2:] if owner_pubkey.startswith("0x") else owner_pubkey
        target = int(PAYLOAD["amount_e8"])

        def native_balance():
            return int(client.get_balance(owner_rpc))

        before = native_balance()
        needed = max(0, target - before)
        report = {
            "ok": True,
            "schema": "zenodex.local_testnet.release_native_collateral_materialize.v0",
            "testnet_only": True,
            "production_authority": False,
            "owner_pubkey": owner_pubkey,
            "target_balance_e8": target,
            "balance_before_e8": before,
            "materialize_amount_e8": needed,
        }
        if needed == 0:
            report["balance_after_e8"] = before
            report["status"] = "already_funded"
            print(json.dumps(report, sort_keys=True))
            raise SystemExit(0)

        raw_refillers = PAYLOAD.get("refiller_roles") or {}
        preferred_names = list(PAYLOAD.get("preferred_refiller_names") or [])
        for name in sorted(raw_refillers):
            if name not in preferred_names:
                preferred_names.append(name)

        refiller_candidates = []
        selected = None
        for name in preferred_names:
            role = raw_refillers.get(name)
            if not isinstance(role, dict):
                continue
            refiller_pubkey = str(role.get("public_key") or "")
            refiller_rpc = refiller_pubkey[2:] if refiller_pubkey.startswith("0x") else refiller_pubkey
            try:
                balance = int(client.get_balance(refiller_rpc))
            except Exception as exc:
                refiller_candidates.append({"role": name, "balance_error": str(exc)})
                continue
            refiller_candidates.append({"role": name, "balance_e8": balance})
            if selected is None and balance >= needed:
                selected = {
                    "role": name,
                    "pubkey": refiller_pubkey,
                    "rpc": refiller_rpc,
                    "privkey_int": int(role["privkey_int"]),
                    "balance_e8": balance,
                }

        report["refiller_candidates"] = refiller_candidates
        if selected is None:
            report["ok"] = False
            report["status"] = "no_release_native_refiller_with_sufficient_balance"
            print(json.dumps(report, sort_keys=True))
            raise SystemExit(0)

        report["refiller_role"] = selected["role"]
        report["refiller_pubkey"] = selected["pubkey"]
        report["refiller_balance_before_e8"] = selected["balance_e8"]

        last_block_response = None
        last_send_response = None
        last_after = before
        for send_attempt in range(1, 3):
            current = native_balance()
            needed_now = max(0, target - current)
            if needed_now == 0:
                last_after = current
                break
            send_response = client.send_signed_tx(
                privkey=selected["privkey_int"],
                operations={"1": [[selected["rpc"], owner_rpc, str(needed_now)]]},
                expiration_seconds=3600,
            )
            last_send_response = send_response
            report["send"] = send_response
            report["send_attempts"] = send_attempt
            report["materialize_amount_e8"] = needed_now
            if not tau_rpc_response_is_success(send_response):
                report["ok"] = False
                report["status"] = "send_rejected"
                print(json.dumps(report, sort_keys=True))
                raise SystemExit(0)
            for block_attempt in range(1, 11):
                block_response = client.createblock()
                last_block_response = block_response
                report["createblock"] = block_response
                report["createblock_attempts"] = block_attempt
                last_after = native_balance()
                if last_after >= target:
                    break
                if tau_rpc_response_is_success(block_response):
                    break
                if "mempool is empty" not in str(block_response).lower():
                    break
                time.sleep(0.5)
            if last_after >= target:
                break
            if "mempool is empty" in str(last_block_response).lower() and send_attempt < 2:
                time.sleep(0.5)
                continue
            break

        after = last_after
        report["balance_after_e8"] = after
        if after < target:
            report["ok"] = False
            report["status"] = "target_balance_not_materialized"
            report["last_createblock"] = last_block_response
            report["last_send"] = last_send_response
        else:
            report["status"] = "accepted"
        print(json.dumps(report, sort_keys=True))
        """
    ).strip()
    result = cm.compose_run(
        engine=engine,
        project_name=compose_project,
        compose_files=[COMPOSE_FILE],
        service="zenodex-api",
        command=["-c", script],
        env=dict(env),
        extra_args=["-T"],
        capture=True,
        input_text=json.dumps(payload, sort_keys=True),
    )
    if result.returncode != 0:
        raise RuntimeError(result.stderr.strip() or result.stdout.strip() or "native collateral materialization failed")
    report = _extract_json_from_text(result.stdout)
    if report.get("ok") is not True:
        raise RuntimeError(f"native collateral materialization failed: {json.dumps(report, sort_keys=True)}")
    return report


def _run_release_flow_smoke(
    *,
    ui_base: str,
    paths: mf.ManifestPaths,
    manifest: Mapping[str, Any],
    engine: cm.ComposeEngine,
    compose_project: str,
    env: Mapping[str, str],
) -> dict[str, Any]:
    key_bundle_path = Path(str(manifest["fixture_paths"]["key_bundle"]))
    roles = _role_materials(_load_json_file(key_bundle_path, label="key bundle"))
    seed_report = _load_json_file(paths.reports_dir / "api_seed_report.json", label="api seed report")
    deadline = int(time.time()) + 3600
    run_id = _smoke_run_id()
    chain_id = str(manifest["chain_id"])
    market_id = str(seed_report["market_id"])
    zk_required = manifest.get("zk_required") is True
    alice = _role_pubkey(roles, "alice")
    bob = _role_pubkey(roles, "bob")

    checks: dict[str, dict[str, Any]] = {}

    def require(name: str, response: Mapping[str, Any], *, require_any: tuple[str, ...] = ("ok",)) -> dict[str, Any]:
        summary = _summarize_response(response, require_any=require_any)
        if summary.get("ok") is not True:
            raise RuntimeError(f"{name} failed: {json.dumps(response, sort_keys=True)}")
        checks[name] = summary
        return summary

    def submit_perps(name: str, payload: Mapping[str, Any], *, zk_required: bool = False) -> dict[str, Any]:
        response = _post_json(
            f"{ui_base}/api/perps/wallet/submit",
            _with_local_fixture_zk_proof(payload, zk_required=zk_required),
            timeout_s=20.0,
        )
        summary = require(name, response)
        if summary.get("preflight_ok") is not True:
            raise RuntimeError(f"{name} preflight failed: {summary.get('preflight_error')}")
        if summary.get("submission_ok") is not True:
            raise RuntimeError(f"{name} submission was not accepted")
        return summary

    tokens = _safe_get_json(f"{ui_base}/tokens", timeout_s=10.0)
    _require_ok(tokens, label="release token catalog")
    observed_symbols = {
        str(item.get("symbol"))
        for item in tokens.get("test_token_catalog", [])
        if isinstance(item, Mapping)
    }
    checks["token_catalog"] = {
        "ok": {"tAGRS", "tZDEX", "zUSD"}.issubset(observed_symbols),
        "symbols": sorted(observed_symbols),
    }
    if checks["token_catalog"]["ok"] is not True:
        raise RuntimeError(f"release token catalog missing required symbols: {sorted(observed_symbols)}")

    config = _safe_get_json(f"{ui_base}/public_network_config.json", timeout_s=10.0)
    _require_ok(config, label="public network config")
    checks["public_network_config"] = {
        "ok": isinstance(config.get("network_config_hash"), str),
        "network_config_hash": config.get("network_config_hash"),
        "posture": config.get("public_config_url_posture"),
    }
    fixture_prefund = seed_report.get("fixture_prefund") if isinstance(seed_report.get("fixture_prefund"), Mapping) else {}
    funded_roles = set(fixture_prefund.get("roles") or []) if isinstance(fixture_prefund, Mapping) else set()
    funded_assets = set(fixture_prefund.get("assets") or []) if isinstance(fixture_prefund, Mapping) else set()
    checks["fixture_prefund"] = {
        "ok": (
            {"alice", "bob"}.issubset(funded_roles)
            and {DEFAULT_TAGRS_ASSET_ID, DEFAULT_TZDEX_ASSET_ID}.issubset(funded_assets)
            and int(fixture_prefund.get("native_materialize_e8") or 0) >= DEFAULT_ZUSD_BOOTSTRAP_COLLATERAL_E8
            and int(fixture_prefund.get("test_asset_prefund_amount") or 0) > 0
        ),
        "roles": sorted(funded_roles),
        "assets": sorted(funded_assets),
        "native_materialize_e8": fixture_prefund.get("native_materialize_e8"),
        "test_asset_prefund_amount": fixture_prefund.get("test_asset_prefund_amount"),
    }
    if checks["fixture_prefund"]["ok"] is not True:
        raise RuntimeError(f"fixture prefund missing required release accounts/assets: {checks['fixture_prefund']}")

    require(
        "faucet_tagrs",
        _post_json(
            f"{ui_base}/api/testnet/faucet",
            {
                "to_pubkey": alice,
                "asset": DEFAULT_TAGRS_ASSET_ID,
                "amount": 100_000,
                "local_fixture_mode": True,
                "tx_id": f"release-smoke-tagrs-faucet-{run_id}",
            },
            timeout_s=20.0,
        ),
    )

    require(
        "testnet_native_collateral_topup",
        _materialize_release_native_collateral(
            engine=engine,
            compose_project=compose_project,
            env=env,
            roles=roles,
            amount_e8=DEFAULT_ZUSD_BOOTSTRAP_COLLATERAL_E8,
        ),
    )

    require(
        "zusd_collateral_deposit",
        _post_json(
            f"{ui_base}/api/zusd/monetary/submit",
            _with_local_fixture_zk_proof(
                {
                    "action": "deposit_collateral",
                    "owner_pubkey": alice,
                    "amount_e8": DEFAULT_ZUSD_BOOTSTRAP_COLLATERAL_E8,
                    "deadline": deadline,
                    "tx_fee_limit": "0",
                    "signer_privkey": _role_privkey_int(roles, "alice"),
                },
                zk_required=zk_required,
            ),
            timeout_s=20.0,
        ),
    )
    require(
        "zusd_minted_from_collateral",
        _post_json(
            f"{ui_base}/api/zusd/monetary/submit",
            _with_local_fixture_zk_proof(
                {
                    "action": "mint_zusd",
                    "owner_pubkey": alice,
                    "amount_e8": E8,
                    "deadline": deadline,
                    "tx_fee_limit": "0",
                    "signer_privkey": _role_privkey_int(roles, "alice"),
                },
                zk_required=zk_required,
            ),
            timeout_s=20.0,
        ),
    )

    perps_common = {"market_id": market_id, "deadline": deadline, "tx_fee_limit": "0"}
    submit_perps(
        "perps_collateral_deposit_alice",
        {
            **perps_common,
            "action": "deposit_collateral",
            "account_pubkey": alice,
            "account_privkey": _role_privkey_int(roles, "alice"),
            "amount": 10,
        },
        zk_required=zk_required,
    )
    submit_perps(
        "perps_collateral_deposit_bob",
        {
            **perps_common,
            "action": "deposit_collateral",
            "account_pubkey": bob,
            "account_privkey": _role_privkey_int(roles, "bob"),
            "amount": 10,
        },
        zk_required=zk_required,
    )
    checks["perps_collateral_deposit"] = {
        "ok": checks["perps_collateral_deposit_alice"]["ok"] and checks["perps_collateral_deposit_bob"]["ok"],
        "accounts": [alice, bob],
        "quote_asset": derive_zusd_tau_asset_id(chain_id=chain_id),
    }
    checks["perps_price_bootstrap"] = _run_perps_wallet_cycle_smoke(
        ui_base=ui_base,
        market_id=market_id,
        roles=roles,
        deadline=deadline,
        zk_required=zk_required,
    )
    if checks["perps_price_bootstrap"].get("ok") is not True:
        raise RuntimeError("perps price bootstrap failed")
    submit_perps(
        "perps_long_short_open",
        {
            **perps_common,
            "action": "set_position_pair",
            "account_a_pubkey": alice,
            "account_b_pubkey": bob,
            "account_a_privkey": _role_privkey_int(roles, "alice"),
            "account_b_privkey": _role_privkey_int(roles, "bob"),
            "new_position_base_a": 1,
            "new_position_base_b": -1,
        },
        zk_required=zk_required,
    )
    checks["perps_settlement_cycle"] = _run_perps_wallet_cycle_smoke(
        ui_base=ui_base,
        market_id=market_id,
        roles=roles,
        deadline=deadline,
        zk_required=zk_required,
    )
    if checks["perps_settlement_cycle"].get("ok") is not True:
        raise RuntimeError("perps settlement cycle failed")

    require(
        "spot_swap_tagrs_tzdex",
        _post_json(
            f"{ui_base}/api/swap",
            _build_signed_live_swap_payload(
                ui_base=ui_base,
                roles=roles,
                chain_id=chain_id,
                sender_role="alice",
                amount_in=100,
                min_amount_out=0,
                deadline=deadline,
                from_symbol="tAGRS",
                to_symbol="tZDEX",
            ),
            timeout_s=20.0,
        ),
        require_any=("tx_accepted", "ok"),
    )

    pools = _safe_get_json(f"{ui_base}/api/pools?{urllib.parse.urlencode({'account': alice})}", timeout_s=10.0)
    features = _safe_get_json(f"{ui_base}/features", timeout_s=10.0)
    network = _safe_get_json(f"{ui_base}/network", timeout_s=10.0)
    _require_ok(pools, label="release pools status")
    _require_ok(features, label="release feature status")
    _require_ok(network, label="release network status")
    local_tip = network.get("local_tip") if isinstance(network.get("local_tip"), Mapping) else {}
    checks["status_and_header_agreement"] = {
        "ok": (
            isinstance(features.get("feature_suite_hash"), str)
            and isinstance(config.get("network_config_hash"), str)
            and int(pools.get("latest_height") or -1) == int(local_tip.get("height") or -2)
            and isinstance(local_tip.get("header_hash"), str)
            and isinstance(local_tip.get("app_hash"), str)
        ),
        "live_height": pools.get("latest_height"),
        "local_tip": dict(local_tip),
        "feature_suite_hash": features.get("feature_suite_hash"),
        "network_config_hash": config.get("network_config_hash"),
    }
    if checks["status_and_header_agreement"]["ok"] is not True:
        raise RuntimeError("release status/header agreement check failed")
    return checks


def _run_browser_smoke(
    *,
    ui_base: str,
    paths: mf.ManifestPaths,
    manifest: Mapping[str, Any],
    chrome_bin: Path | None,
    mode: str,
    timeout_s: float,
) -> dict[str, Any]:
    chrome = _resolve_chrome_bin(chrome_bin)
    if chrome is None:
        skipped = {"ok": mode == "auto", "mode": mode, "skipped": True, "reason": "chrome_not_found", "checks": {}}
        if mode == "required":
            skipped["error"] = "chrome_not_found"
        return skipped

    key_bundle_path = Path(str(manifest["fixture_paths"]["key_bundle"]))
    roles = _role_materials(_load_json_file(key_bundle_path, label="key bundle"))
    seed_report = _load_json_file(paths.reports_dir / "api_seed_report.json", label="api seed report")
    checks: dict[str, Any] = {}
    for item in _browser_smoke_cases(
        ui_base=ui_base,
        roles=roles,
        seed_report=seed_report,
        chain_id=str(manifest["chain_id"]),
        zk_required=manifest.get("zk_required") is True,
    ):
        checks[str(item["name"])] = _run_browser_case(
            chrome=chrome,
            url=str(item["url"]),
            snippets=tuple(str(s) for s in item["snippets"]),
            timeout_s=timeout_s,
        )
    return {
        "ok": all(bool(value.get("ok")) for value in checks.values()),
        "mode": mode,
        "skipped": False,
        "chrome": chrome,
        "checks": checks,
    }


def _run_browser_case(*, chrome: str, url: str, snippets: tuple[str, ...], timeout_s: float) -> dict[str, Any]:
    with tempfile.TemporaryDirectory(prefix="zenodex-localtest-chrome-", ignore_cleanup_errors=True) as profile:
        try:
            result = subprocess.run(
                [
                    chrome,
                    "--headless=new",
                    "--disable-gpu",
                    "--no-sandbox",
                    f"--user-data-dir={profile}",
                    "--virtual-time-budget=25000",
                    "--dump-dom",
                    url,
                ],
                check=False,
                capture_output=True,
                text=True,
                timeout=max(5.0, float(timeout_s)),
            )
        except subprocess.TimeoutExpired:
            return {"ok": False, "error": "browser_timeout"}
    dom = result.stdout or ""
    missing = [snippet for snippet in snippets if snippet not in dom]
    failed_text = " failed " in f" {dom.lower()} "
    return {
        "ok": result.returncode == 0 and not missing and not failed_text,
        "returncode": result.returncode,
        "missing_snippets": missing,
        "stderr_tail": (result.stderr or "")[-1000:],
    }


def _browser_smoke_cases(
    *,
    ui_base: str,
    roles: Mapping[str, Mapping[str, Any]],
    seed_report: Mapping[str, Any],
    chain_id: str,
    zk_required: bool = False,
) -> list[dict[str, Any]]:
    deadline = int(time.time()) + 3600
    alice = _role_pubkey(roles, "alice")
    alice_priv = roles["alice"]["privkey_hex"]
    oracle_auth = _role_pubkey(roles, "oracle_authority")
    oracle_priv = roles["oracle_authority"]["privkey_hex"]
    market_id = str(seed_report["market_id"])
    spot_payload = _build_signed_live_swap_payload(
        ui_base=ui_base,
        roles=roles,
        chain_id=chain_id,
        sender_role="alice",
        amount_in=100,
        min_amount_out=0,
        deadline=deadline,
        from_symbol="tAGRS",
        to_symbol="tZDEX",
    )

    def url(params: Mapping[str, str]) -> str:
        return f"{ui_base}/?{urllib.parse.urlencode(params)}"

    zk_query = {"zkProofJson": _local_fixture_zk_proof_json()} if zk_required else {}

    return [
        {
            "name": "spot_swap_ui",
            "url": url(
                {
                    "tab": "swap",
                    "demo": "false",
                    "zenodexUiSmokeSwap": "1",
                    "walletAddress": alice,
                    "smokeAmountIn": "100",
                    "smokeMinAmountOut": "0",
                    "smokeIntentSignature": str(spot_payload["signature"]),
                    "smokeNonce": str(spot_payload["nonce"]),
                    "smokeDeadline": str(spot_payload["deadline"]),
                    "smokeFromSymbol": "tAGRS",
                    "smokeToSymbol": "tZDEX",
                }
            ),
            "snippets": ("Swap Confirmed",),
        },
        {
            "name": "zusd_monetary_ui",
            "url": url(
                {
                    "tab": "zusd",
                    "demo": "false",
                    "zenodexUiSmokeZusdMonetary": "1",
                    "zusdMonetaryAction": "advance_epoch",
                    "actorPubkey": alice,
                    "zusdDelta": "1",
                    "zusdDeadline": str(deadline),
                    "signerPrivkey": alice_priv,
                    **zk_query,
                }
            ),
            "snippets": ("zUSD Monetary Vault", "preflight accepted"),
        },
        {
            "name": "zusd_quick_mint_ui",
            "url": url(
                {
                    "tab": "zusd",
                    "demo": "false",
                    "zenodexUiSmokeZusdQuickMint": "1",
                    "ownerPubkey": alice,
                    "zusdCollateral": "0",
                    "zusdMint": "1",
                    "zusdDeadline": str(deadline),
                    "zusdAcceptProtocolResponse": "1",
                    "signerPrivkey": alice_priv,
                }
            ),
            "snippets": ("Quick Mint zUSD", "mint request completed"),
        },
        {
            "name": "perps_wallet_ui",
            "url": url(
                {
                    "tab": "perps",
                    "demo": "false",
                    "zenodexUiSmokePerpsWallet": "1",
                    "perpsWalletAction": "publish_clearing_price",
                    "marketId": market_id,
                    "priceE8": str(E8),
                    "perpsDeadline": str(deadline),
                    "oraclePubkey": oracle_auth,
                    "oraclePrivkey": oracle_priv,
                    **zk_query,
                }
            ),
            "snippets": ("Live Perps Wallet", "submit accepted"),
        },
        {
            "name": "oracle_ui",
            "url": url(
                {
                    "tab": "oracle",
                    "oracleView": "Receipts",
                    "demo": "false",
                    "zenodexUiSmokeOracleWrites": "1",
                }
            ),
            "snippets": ("ZenoOracle", "oracle write smoke accepted"),
        },
        {
            "name": "autotrader_ui",
            "url": url(
                {
                    "tab": "strategy",
                    "strategyView": "create",
                    "demo": "false",
                    "zenodexUiSmokeStrategyLive": "1",
                }
            ),
            "snippets": ("AutoTrader Live Prepare", "accepted"),
        },
        {
            "name": "confidential_ui",
            "url": url(
                {
                    "tab": "confidential",
                    "demo": "false",
                    "zenodexUiSmokeConfidentialVerify": "1",
                }
            ),
            "snippets": ("Confidential trading", "Runtime receipt"),
        },
    ]


def _safe_get_json(url: str, *, timeout_s: float = 5.0, headers: Mapping[str, str] | None = None) -> dict[str, Any]:
    try:
        request = urllib.request.Request(url, headers=dict(headers or {}), method="GET")
        with urllib.request.urlopen(request, timeout=timeout_s) as response:
            body = json.loads(response.read().decode("utf-8"))
        if isinstance(body, dict):
            return {"ok": True, "status_code": response.status, **body}
        return {"ok": False, "status_code": response.status, "error": "non_object_json"}
    except urllib.error.HTTPError as exc:
        payload = _decode_error_json(exc)
        return {"ok": False, "status_code": exc.code, **payload}
    except Exception as exc:
        return {"ok": False, "error": f"{type(exc).__name__}: {exc}"}


def _post_json(url: str, payload: Mapping[str, Any], *, timeout_s: float = 10.0) -> dict[str, Any]:
    data = json.dumps(payload, sort_keys=True).encode("utf-8")
    request = urllib.request.Request(
        url,
        data=data,
        headers={"Content-Type": "application/json"},
        method="POST",
    )
    try:
        with urllib.request.urlopen(request, timeout=timeout_s) as response:
            body = json.loads(response.read().decode("utf-8"))
        if isinstance(body, dict):
            return {"status_code": response.status, **body}
        raise ValueError("non_object_json")
    except urllib.error.HTTPError as exc:
        payload = _decode_error_json(exc)
        return {"status_code": exc.code, **payload}


def _public_config_probe_headers(public_url: str) -> dict[str, str]:
    parsed = urllib.parse.urlparse(public_url)
    if parsed.scheme not in {"http", "https"} or not parsed.netloc:
        raise ValueError("public URL must be an http(s) URL")
    return {
        "Host": parsed.netloc,
        "X-Forwarded-Proto": parsed.scheme,
    }


def _write_public_host_report(
    *,
    paths: mf.ManifestPaths,
    manifest: Mapping[str, Any],
    public_url: str,
    source: str,
) -> dict[str, Any]:
    public_base = public_url.rstrip("/")
    local_config_url = f"{manifest['service_urls']['ui']}/public_network_config.json"
    config = _safe_get_json(
        local_config_url,
        timeout_s=10.0,
        headers=_public_config_probe_headers(public_base),
    )
    ok = bool(config.get("ok")) and isinstance(config.get("network_config_hash"), str)
    report = {
        "schema": "zenodex.local_testnet.public_host_report.v1",
        "ok": ok,
        "status": "accepted" if ok else "rejected",
        "public_url": public_base,
        "public_ui_url": public_base,
        "public_network_config_url": f"{public_base}/public_network_config.json",
        "public_config_url_posture": config.get("public_config_url_posture"),
        "public_network_config_hash": config.get("network_config_hash"),
        "admin_write_token_location": str(paths.rendered_nginx),
        "manifest_path": str(paths.manifest_path),
        "reports_dir": str(paths.reports_dir),
        "source": source,
        "fake_value_public_testnet": True,
        "production_security_claim": False,
        "read_only_tester_instructions": [
            f"Open {public_base} in a browser.",
            f"Fetch {public_base}/public_network_config.json and verify public_network_config_hash.",
            f"Run: zenodex-public-follower --config-url {public_base}/public_network_config.json",
            (
                "For a faster bootstrap-only check, run: zenodex-public-follower "
                f"--config-url {public_base}/public_network_config.json --skip-pull-live --no-require-live"
            ),
            "Use the UI faucet and local test wallet flow for capped fake-value transactions.",
        ],
    }
    if not ok:
        report["config_probe"] = config
    _write_json(paths.reports_dir / "public_testnet_host_report.json", report)
    return report


def _public_host_summary(report: Mapping[str, Any]) -> str:
    lines = [
        "",
        "ZenoDEX public fake-value testnet host is ready.",
        "",
        f"  Public UI URL:          {report.get('public_ui_url')}",
        f"  Public config URL:      {report.get('public_network_config_url')}",
        f"  Config hash:            {report.get('public_network_config_hash')}",
        f"  Config URL posture:     {report.get('public_config_url_posture')}",
        f"  Admin/write token file: {report.get('admin_write_token_location')}",
        "",
        "  Read-only tester path:",
        f"    curl -fsS {report.get('public_network_config_url')}",
        f"    zenodex-public-follower --config-url {report.get('public_network_config_url')}",
        (
            "    zenodex-public-follower --config-url "
            f"{report.get('public_network_config_url')} --skip-pull-live --no-require-live"
        ),
        "",
        "  Fake-value warning: no production value, no mainnet custody.",
        "",
    ]
    return "\n".join(lines)


def _open_public_ui_url(public_url: str) -> None:
    if not public_url:
        return
    try:
        opened = webbrowser.open(public_url, new=2)
    except Exception as exc:
        _log("public", f"could not open browser automatically: {type(exc).__name__}: {exc}")
        return
    if opened:
        _log("public", f"opened browser: {public_url}")
    else:
        _log("public", f"browser did not report success; open manually: {public_url}")


def _run_cloudflare_quick_tunnel(
    *,
    opts: PublicUpOptions,
    paths: mf.ManifestPaths,
    manifest: Mapping[str, Any],
) -> int:
    runner = _resolve_cloudflared_runner(opts.cloudflared_bin, engine=opts.engine)
    if runner is None:
        _log(
            "public",
            "no Quick Tunnel runner found. Install cloudflared, keep Docker/Podman on PATH, "
            "or pass --tunnel-url after starting a tunnel.",
        )
        return 2
    origin_url = str(manifest["service_urls"]["ui"])
    command, source = _cloudflared_command(runner, origin_url)
    _log("public", f"starting Cloudflare Quick Tunnel for {origin_url} via {source}")
    proc = subprocess.Popen(
        command,
        cwd=str(REPO_ROOT),
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
        bufsize=1,
    )
    public_url: str | None = None
    try:
        assert proc.stdout is not None
        for line in proc.stdout:
            sys.stderr.write(line)
            if public_url is None:
                match = re.search(r"https://[A-Za-z0-9-]+\.trycloudflare\.com", line)
                if match:
                    public_url = match.group(0).rstrip("/")
                    report = _write_public_host_report(
                        paths=paths,
                        manifest=manifest,
                        public_url=public_url,
                        source=source,
                    )
                    sys.stderr.write(_public_host_summary(report))
                    if report.get("ok") is not True:
                        _log("public", "public config probe failed; stopping tunnel")
                        proc.terminate()
                        try:
                            proc.wait(timeout=10)
                        except subprocess.TimeoutExpired:
                            proc.kill()
                        return 1
                    if opts.open_browser and report.get("ok") is True:
                        _open_public_ui_url(public_url)
            if proc.poll() is not None:
                break
    except KeyboardInterrupt:
        _log("public", "stopping Cloudflare Quick Tunnel")
        proc.terminate()
        try:
            proc.wait(timeout=10)
        except subprocess.TimeoutExpired:
            proc.kill()
        return 130
    exit_code = int(proc.wait())
    if public_url is None:
        _log("public", "cloudflared exited before publishing a public URL")
        return exit_code if exit_code != 0 else 1
    return exit_code


def _resolve_cloudflared_binary(cloudflared_bin: str) -> str | None:
    name = str(cloudflared_bin or "").strip()
    if not name:
        return None
    if os.sep in name:
        return name if Path(name).is_file() and os.access(name, os.X_OK) else None
    return shutil.which(name)


def _resolve_cloudflared_container_engine(engine: str) -> str | None:
    candidates = (engine,) if engine in {"docker", "podman"} else ("docker", "podman")
    for candidate in candidates:
        resolved = shutil.which(candidate)
        if resolved:
            return resolved
    return None


def _resolve_cloudflared_runner(cloudflared_bin: str, *, engine: str) -> tuple[str, str] | None:
    binary = _resolve_cloudflared_binary(cloudflared_bin)
    if binary:
        return ("binary", binary)
    requested = str(cloudflared_bin or "").strip()
    if requested and requested != "cloudflared":
        return None
    container_engine = _resolve_cloudflared_container_engine(engine)
    if container_engine:
        return ("container", container_engine)
    return None


def _cloudflared_command(runner: tuple[str, str], origin_url: str) -> tuple[list[str], str]:
    kind, executable = runner
    if kind == "binary":
        return ([executable, "tunnel", "--url", origin_url], "cloudflare_quick_tunnel_binary")
    return (
        [
            executable,
            "run",
            "--rm",
            "--network",
            "host",
            CLOUDFLARED_IMAGE,
            "tunnel",
            "--no-autoupdate",
            "--url",
            origin_url,
        ],
        f"cloudflare_quick_tunnel_{Path(executable).name}_container",
    )


def _summarize_response(payload: Mapping[str, Any], *, require_any: tuple[str, ...] = ("ok",)) -> dict[str, Any]:
    accepted = any(payload.get(key) is True for key in require_any)
    summary: dict[str, Any] = {
        "ok": bool(accepted),
        "status_code": payload.get("status_code"),
        "status": payload.get("status"),
        "error": payload.get("error"),
    }
    for key in (
        "height",
        "tx_id",
        "receipt_hash",
        "runtime_receipt_hash",
        "action",
        "surface",
    ):
        if key in payload:
            summary[key] = payload.get(key)
    submission = payload.get("submission")
    if isinstance(submission, Mapping):
        summary["submission_ok"] = "SUCCESS:" in str(submission.get("sendtx_response", ""))
        if "createblock_response" in submission:
            summary["mined"] = "SUCCESS:" in str(submission.get("createblock_response", ""))
    report = payload.get("report")
    if isinstance(report, Mapping):
        summary["action"] = report.get("action", summary.get("action"))
        preflight = report.get("preflight")
        if isinstance(preflight, Mapping):
            summary["preflight_ok"] = bool(preflight.get("ok"))
            summary["preflight_error"] = preflight.get("error")
    proof = payload.get("proof")
    if isinstance(proof, Mapping):
        verified = False
        artifact_complete = False
        for key in ("zk_wrapper", "post_submit_zk_wrapper"):
            wrapper = proof.get(key)
            if not isinstance(wrapper, Mapping):
                continue
            summary[f"{key}_verified"] = wrapper.get("zk_proof_verified") is True
            summary[f"{key}_artifact_binding_complete"] = wrapper.get("artifact_binding_complete") is True
            verified = verified or wrapper.get("zk_proof_verified") is True
            artifact_complete = artifact_complete or wrapper.get("artifact_binding_complete") is True
        if "zk_wrapper_verified" in summary or "post_submit_zk_wrapper_verified" in summary:
            summary["zk_proof_verified"] = verified
            summary["zk_artifact_binding_complete"] = artifact_complete
    receipt = payload.get("receipt")
    if isinstance(receipt, Mapping):
        summary["receipt_accepted"] = bool(receipt.get("accepted"))
    return summary


def _pool_asset_for_symbol(pool: Mapping[str, Any], symbol: str) -> str | None:
    wanted = str(symbol).strip().upper()
    for token_key, asset_key in (("token0", "asset0"), ("token1", "asset1")):
        token = str(pool.get(token_key, "")).strip().upper()
        asset = pool.get(asset_key)
        if token == wanted and isinstance(asset, str) and asset:
            return asset
    return None


def _find_live_swap_pool(
    *,
    ui_base: str,
    account: str,
    from_symbol: str,
    to_symbol: str,
) -> tuple[dict[str, Any], int]:
    query = urllib.parse.urlencode({"account": account})
    pools_report = _safe_get_json(f"{ui_base}/api/pools?{query}", timeout_s=10.0)
    _require_ok(pools_report, label="live swap pool fetch")
    pools = pools_report.get("pools")
    if not isinstance(pools, list):
        raise ValueError("live swap pool response missing pools")
    for row in pools:
        if not isinstance(row, Mapping):
            continue
        if _pool_asset_for_symbol(row, from_symbol) and _pool_asset_for_symbol(row, to_symbol):
            last_nonce = pools_report.get("account_last_nonce", 0)
            if not isinstance(last_nonce, int) or isinstance(last_nonce, bool) or last_nonce < 0:
                raise ValueError("live swap account_last_nonce invalid")
            return dict(row), int(last_nonce)
    raise ValueError(f"live swap pool not found for {from_symbol}->{to_symbol}")


def _build_signed_live_swap_intent(
    *,
    ui_base: str,
    roles: Mapping[str, Mapping[str, Any]],
    chain_id: str,
    sender_role: str,
    amount_in: int,
    min_amount_out: int,
    deadline: int,
    from_symbol: str = "tAGRS",
    to_symbol: str = "tZDEX",
    nonce_override: int | None = None,
) -> tuple[dict[str, Any], dict[str, Any]]:
    from src.integration.tau_net_client import sign_dex_intent_for_engine
    from src.integration.zeno_ledger_v0 import hash_v0

    sender = _role_pubkey(roles, sender_role)
    pool, last_nonce = _find_live_swap_pool(
        ui_base=ui_base,
        account=sender,
        from_symbol=from_symbol,
        to_symbol=to_symbol,
    )
    asset_in = _pool_asset_for_symbol(pool, from_symbol)
    asset_out = _pool_asset_for_symbol(pool, to_symbol)
    if not asset_in or not asset_out:
        raise ValueError("live swap pool asset mapping missing")
    pool_id = str(pool.get("pool_id") or pool.get("poolId") or "")
    if not pool_id:
        raise ValueError("live swap pool id missing")
    nonce = int(nonce_override) if nonce_override is not None else int(last_nonce) + 1
    if nonce <= int(last_nonce):
        raise ValueError(f"swap nonce must advance account nonce: {nonce} <= {last_nonce}")
    intent_payload = {
        "sender_pubkey": sender,
        "recipient": sender,
        "pool_id": pool_id,
        "asset_in": asset_in,
        "asset_out": asset_out,
        "amount_in": int(amount_in),
        "min_amount_out": int(min_amount_out),
        "nonce": nonce,
    }
    operation = {
        "module": "TauSwap",
        "version": "0.1",
        "kind": "SWAP_EXACT_IN",
        "intent_id": hash_v0("ui_swap_intent_v0", intent_payload),
        "sender_pubkey": sender,
        "deadline": int(deadline),
        "nonce": nonce,
        "pool_id": pool_id,
        "asset_in": asset_in,
        "asset_out": asset_out,
        "amount_in": int(amount_in),
        "min_amount_out": int(min_amount_out),
        "recipient": sender,
    }
    operation["signature"] = sign_dex_intent_for_engine(
        operation,
        privkey=_role_privkey_int(roles, sender_role),
        chain_id=chain_id,
    )
    payload = {
        "from": from_symbol,
        "to": to_symbol,
        "poolId": pool_id,
        "assetIn": asset_in,
        "assetOut": asset_out,
        "amountIn": int(amount_in),
        "minAmountOut": int(min_amount_out),
        "senderPubkey": sender,
        "recipient": sender,
        "deadline": int(deadline),
        "nonce": nonce,
        "signature": operation["signature"],
    }
    return payload, operation


def _build_signed_live_swap_payload(**kwargs: Any) -> dict[str, Any]:
    payload, _operation = _build_signed_live_swap_intent(**kwargs)
    return payload


def _live_account_asset_balance(*, ui_base: str, account: str, asset: str) -> int:
    query = urllib.parse.urlencode({"account": account})
    pools_report = _safe_get_json(f"{ui_base}/api/pools?{query}", timeout_s=10.0)
    _require_ok(pools_report, label="live account balance fetch")
    pools = pools_report.get("pools")
    if not isinstance(pools, list):
        raise ValueError("live account balance response missing pools")
    for row in pools:
        if not isinstance(row, Mapping):
            continue
        if row.get("asset0") == asset:
            return int(row.get("account_balance0", row.get("accountBalance0", 0)))
        if row.get("asset1") == asset:
            return int(row.get("account_balance1", row.get("accountBalance1", 0)))
    raise ValueError(f"asset balance not found for {asset}")


def _run_complex_grouped_transaction_smoke(
    *,
    ui_base: str,
    roles: Mapping[str, Mapping[str, Any]],
    chain_id: str,
    deadline: int,
    run_id: str,
) -> dict[str, Any]:
    sender = _role_pubkey(roles, "alice")
    payload, operation = _build_signed_live_swap_intent(
        ui_base=ui_base,
        roles=roles,
        chain_id=chain_id,
        sender_role="alice",
        amount_in=100,
        min_amount_out=0,
        deadline=deadline,
    )
    _, operation_b = _build_signed_live_swap_intent(
        ui_base=ui_base,
        roles=roles,
        chain_id=chain_id,
        sender_role="alice",
        amount_in=101,
        min_amount_out=0,
        deadline=deadline,
        nonce_override=int(operation["nonce"]) + 1,
    )
    asset_in = str(payload["assetIn"])
    good_group = {
        "tx_id": f"local-smoke-grouped-swap-batch-{run_id}",
        "block_timestamp": int(time.time()),
        "tx_sender_pubkey": sender,
        "operations": {"5": [operation, operation_b]},
    }
    good = _post_json(f"{ui_base}/tx", {"tx": good_group, "time_ms": int(time.time() * 1000)}, timeout_s=20.0)
    if good.get("tx_accepted") is not True:
        raise RuntimeError(f"grouped transaction was not accepted: {json.dumps(good, sort_keys=True)}")
    balance_after_good = _live_account_asset_balance(ui_base=ui_base, account=sender, asset=asset_in)

    bad_group = {
        "tx_id": f"local-smoke-grouped-replay-reject-{run_id}",
        "block_timestamp": int(time.time()),
        "tx_sender_pubkey": sender,
        "operations": {"5": [operation, operation_b]},
    }
    bad = _post_json(f"{ui_base}/tx", {"tx": bad_group, "time_ms": int(time.time() * 1000)}, timeout_s=20.0)
    if bad.get("tx_accepted") is True:
        raise RuntimeError("grouped replay transaction was accepted")
    balance_after_bad = _live_account_asset_balance(ui_base=ui_base, account=sender, asset=asset_in)
    if balance_after_bad != balance_after_good:
        raise RuntimeError(
            "rejected grouped transaction changed balance: "
            f"before={balance_after_good} after={balance_after_bad}"
        )
    return {
        "ok": True,
        "accepted_group_height": good.get("height"),
        "rejected_group_height": bad.get("height"),
        "asset_in": asset_in,
        "balance_after_good": balance_after_good,
        "balance_after_bad": balance_after_bad,
        "replay_rejected": True,
        "atomic_reject_preserved_balance": True,
    }


def _role_pubkey(roles: Mapping[str, Mapping[str, Any]], role: str) -> str:
    value = roles.get(role, {}).get("public_key")
    if not isinstance(value, str) or not value:
        raise ValueError(f"missing public key for role {role!r}")
    return value


def _role_privkey_int(roles: Mapping[str, Mapping[str, Any]], role: str) -> int:
    value = roles.get(role, {}).get("privkey_int")
    if not isinstance(value, int):
        raise ValueError(f"missing private key for role {role!r}")
    return int(value)


def _with_local_fixture_zk_proof(payload: Mapping[str, Any], *, zk_required: bool) -> dict[str, Any]:
    body = dict(payload)
    if zk_required:
        body["zk_proof"] = _local_fixture_zk_proof()
    return body


def _local_fixture_zk_proof() -> dict[str, Any]:
    return {
        "system": "local-testnet-live-wrapper-fixture-v1",
        "production_security_claim": False,
    }


def _local_fixture_zk_proof_json() -> str:
    return json.dumps(_local_fixture_zk_proof(), sort_keys=True, separators=(",", ":"))


def _smoke_run_id() -> str:
    import hashlib

    raw = f"{time.time_ns()}:{os.getpid()}".encode("utf-8")
    return hashlib.sha256(raw).hexdigest()[:16]


def _resolve_chrome_bin(chrome_bin: Path | None) -> str | None:
    if chrome_bin is not None:
        return str(chrome_bin)
    for name in ("google-chrome", "google-chrome-stable", "chromium", "chromium-browser"):
        found = shutil.which(name)
        if found:
            return found
    return None


def _zusd_transfer_payload(
    *,
    ui_base: str,
    roles: Mapping[str, Mapping[str, Any]],
    deadline: int,
) -> dict[str, Any]:
    alice = _role_pubkey(roles, "alice")
    bob = _role_pubkey(roles, "bob")
    alice_inspect = _post_json(
        f"{ui_base}/api/zusd/wallet/inspect",
        {"action": "transfer", "sender_pubkey": alice, "recipient_pubkey": bob, "amount": 1, "deadline": deadline},
    )
    bob_inspect = _post_json(
        f"{ui_base}/api/zusd/wallet/inspect",
        {"action": "transfer", "sender_pubkey": bob, "recipient_pubkey": alice, "amount": 1, "deadline": deadline},
    )
    alice_balance = int(((alice_inspect.get("transport") or {}).get("sender_balance_before") or 0))
    bob_balance = int(((bob_inspect.get("transport") or {}).get("sender_balance_before") or 0))
    if bob_balance > alice_balance:
        sender_role, recipient = "bob", alice
    else:
        sender_role, recipient = "alice", bob
    return {
        "action": "transfer",
        "sender_pubkey": _role_pubkey(roles, sender_role),
        "recipient_pubkey": recipient,
        "amount": 1,
        "deadline": deadline,
        "signer_privkey": _role_privkey_int(roles, sender_role),
    }


def _confidential_runtime_payload(*, run_id: str, fixture: ConfidentialLocalFixture) -> dict[str, Any]:
    return {
        "attestation_payload": {
            "provider": "nitro",
            "nonce": f"local-smoke-{run_id}",
            "summary": {"pcrs": {"0": fixture.nitro_pcr0, "8": fixture.nitro_pcr8}},
        },
        "extension_id": "route-premium-v1",
        "provider_id": "provider-1",
        "request_id": f"req-local-smoke-{run_id}",
        "policy_version": "tee-policy-v1",
        "do_execute": 1,
        "policy_ok": 1,
        "nonce_unused": 1,
        "output_bound_ok": 1,
        "current_epoch": 10,
        "max_attestation_age": 2,
        "fee_charged": 7,
        "receipt_fee": 7,
        "credit_before": 40,
        "credit_after": 33,
        "provider_balance_before": 9,
        "provider_balance_after": 16,
        "expected_policy_digest": fixture.policy_digest,
        "execution_id": f"exec-local-smoke-{run_id}",
        "execution_kind": "private_route_quote",
        "result_code": "bounded_route_selected",
    }


def _run_perps_wallet_cycle_smoke(
    *,
    ui_base: str,
    market_id: str,
    roles: Mapping[str, Mapping[str, Any]],
    deadline: int,
    zk_required: bool = False,
) -> dict[str, Any]:
    """Exercise a clearinghouse perps price cycle and leave it reusable.

    The local-testnet clearinghouse requires a published price before settle,
    and a settled epoch before the next advance. This smoke publishes a price,
    settles it, then advances once so the browser/UI smoke can publish again.
    """
    steps: dict[str, dict[str, Any]] = {}

    def submit(name: str, payload: Mapping[str, Any]) -> dict[str, Any]:
        response = _post_json(
            f"{ui_base}/api/perps/wallet/submit",
            _with_local_fixture_zk_proof(payload, zk_required=zk_required),
            timeout_s=20.0,
        )
        summary = _summarize_response(response)
        steps[name] = summary
        _require_ok(response, label=f"perps {name}")
        if summary.get("preflight_ok") is not True:
            raise RuntimeError(f"perps {name} preflight failed: {summary.get('preflight_error')}")
        if summary.get("submission_ok") is not True:
            raise RuntimeError(f"perps {name} submission was not accepted")
        return response

    operator_privkey = _role_privkey_int(roles, "operator")
    oracle_privkey = _role_privkey_int(roles, "oracle_authority")
    common = {"market_id": market_id, "deadline": deadline, "tx_fee_limit": "0"}

    def get_bridge_payload() -> dict[str, Any]:
        resp = _post_json(
            f"{ui_base}/api/perps/wallet/oracle-bridge-template",
            {"action": "settle_epoch", "market_id": market_id},
        )
        return resp.get("bridge") or {}

    status_before = _safe_get_json(f"{ui_base}/api/perps/wallet/status")
    market_before = _find_perps_market(status_before, market_id=market_id)
    prep = _perps_pre_publish_step(market_before)
    if prep == "settle_then_advance":
        submit(
            "settle_epoch_before_publish",
            {
                **common,
                "action": "settle_epoch",
                "operator_privkey": operator_privkey,
                "oracle_adapter_bridge": get_bridge_payload(),
            },
        )
        submit(
            "advance_epoch_before_publish",
            {
                **common,
                "action": "advance_epoch",
                "delta": 1,
                "operator_privkey": operator_privkey,
            },
        )
    elif prep == "advance":
        submit(
            "advance_epoch_before_publish",
            {
                **common,
                "action": "advance_epoch",
                "delta": 1,
                "operator_privkey": operator_privkey,
            },
        )

    publish = submit(
        "publish_clearing_price",
        {
            **common,
            "action": "publish_clearing_price",
            "price_e8": E8,
            "oracle_privkey": oracle_privkey,
        },
    )
    submit(
        "settle_epoch",
        {
            **common,
            "action": "settle_epoch",
            "operator_privkey": operator_privkey,
            "oracle_adapter_bridge": get_bridge_payload(),
        },
    )
    submit(
        "advance_epoch_after_settle",
        {
            **common,
            "action": "advance_epoch",
            "delta": 1,
            "operator_privkey": operator_privkey,
        },
    )
    return {
        "ok": all(bool(item.get("ok")) for item in steps.values()),
        "status_code": publish.get("status_code"),
        "action": "publish_clearing_price",
        "steps": steps,
    }


def _find_perps_market(status_payload: Mapping[str, Any], *, market_id: str) -> Mapping[str, Any] | None:
    status = status_payload.get("status")
    markets = status.get("markets") if isinstance(status, Mapping) else None
    if not isinstance(markets, list):
        return None
    for item in markets:
        if isinstance(item, Mapping) and str(item.get("market_id")) == market_id:
            return item
    return None


def _perps_pre_publish_step(market: Mapping[str, Any] | None) -> str:
    if market is None:
        return "none"
    now_epoch = int(market.get("now_epoch") or 0)
    clearing_epoch = int(market.get("clearing_price_epoch") or 0)
    oracle_last_update = int(market.get("oracle_last_update_epoch") or 0)
    if now_epoch == 0 or oracle_last_update >= now_epoch:
        return "advance"
    if clearing_epoch >= now_epoch:
        return "settle_then_advance"
    return "none"


def _run_oracle_write_smoke(*, ui_base: str, run_id: str) -> dict[str, Any]:
    import hashlib

    def digest(label: str) -> str:
        return "sha256:" + hashlib.sha256(f"{label}:{run_id}".encode("utf-8")).hexdigest()

    query_id = digest("query")
    action_id = digest("action")
    action_facts_hash = digest("action_facts")
    pre_state_hash = digest("pre_state")
    source_id = f"source:local-smoke-{run_id}"
    steps: dict[str, Any] = {}

    def call(name: str, path: str, payload: Mapping[str, Any]) -> dict[str, Any]:
        response = _post_json(f"{ui_base}{path}", payload)
        steps[name] = _summarize_response(response)
        _require_ok(response, label=f"oracle {name}")
        return response

    def call_rejected(name: str, path: str, payload: Mapping[str, Any], *, error_contains: str) -> dict[str, Any]:
        response = _post_json(f"{ui_base}{path}", payload)
        error = str(response.get("error") or "")
        rejected = (
            response.get("ok") is not True
            and 400 <= int(response.get("status_code") or 0) < 500
            and error_contains in error
        )
        steps[name] = {
            **_summarize_response(response),
            "ok": rejected,
            "expected_rejection": True,
            "expected_error_contains": error_contains,
            "observed_error": error,
        }
        if not rejected:
            raise RuntimeError(f"oracle {name} did not reject as expected: {json.dumps(response, sort_keys=True)}")
        return response

    identity = call("identity", "/api/oracle/identity/create", {"force": True})
    call(
        "query_register",
        "/api/oracle/query/register",
        {
            "base_asset": "AGRS",
            "quote_asset": "zDEX",
            "query_id": query_id,
            "source_policy_id": "source-policy:registered-diverse-v1",
            "min_reporters": 1,
            "report_reward_e8": 17,
            "force": True,
        },
    )
    call("query_fund", "/api/oracle/query/fund", {"query_id": query_id, "amount_e8": 20})
    call("reporter_register", "/api/oracle/reporter/register", {"query_id": query_id, "required_bond_e8": 1, "force": True})
    call("reporter_bond", "/api/oracle/reporter/bond", {"amount_e8": 1})
    call(
        "source_register",
        "/api/oracle/source/register",
        {
            "source_id": source_id,
            "source_kind": "cex",
            "control_group_id": f"control:local-smoke-{run_id}",
            "venue_id": f"venue:local-smoke-{run_id}",
            "data_family_id": "price:cex-last-trade",
            "transport_id": "api:https:local-smoke",
            "asset_class": "crypto",
            "query_id": query_id,
            "assurance_class": "S3",
            "force": True,
        },
    )
    report_payload = {
        "query_id": query_id,
        "price_e8": 123456789,
        "source_observed_epoch": 12,
        "source_id": source_id,
    }
    submitted = call("report_submit", "/api/oracle/report/submit", report_payload)
    duplicate_report = call(
        "report_duplicate_idempotency",
        "/api/oracle/report/submit",
        {**report_payload, "reward_e8": 999},
    )
    if (
        duplicate_report.get("idempotent_replay") is not True
        or duplicate_report.get("report_id") != submitted.get("report_id")
        or int(duplicate_report.get("reward_e8", -1)) != 0
        or int(duplicate_report.get("pending_rewards_e8", -1)) != 17
    ):
        raise RuntimeError(
            "oracle duplicate report was not idempotent: "
            f"{json.dumps(_summarize_response(duplicate_report), sort_keys=True)}"
        )
    steps["report_duplicate_idempotency"]["idempotent_replay"] = True
    dispute = call(
        "dispute_open_escrow",
        "/api/oracle/dispute/open",
        {
            "report_id": submitted.get("report_id"),
            "reporter_id": identity.get("reporter_id"),
            "bond_e8": 1,
            "reason": "local-smoke-adversarial",
            "epoch": 12,
        },
    )
    call_rejected(
        "dispute_duplicate_open_rejected",
        "/api/oracle/dispute/open",
        {
            "report_id": submitted.get("report_id"),
            "reporter_id": identity.get("reporter_id"),
            "bond_e8": 1,
            "reason": "local-smoke-duplicate",
            "epoch": 12,
        },
        error_contains="open dispute already exists",
    )
    call_rejected(
        "dispute_overbond_rejected",
        "/api/oracle/dispute/open",
        {
            "report_id": submitted.get("report_id"),
            "reporter_id": identity.get("reporter_id"),
            "bond_e8": 1,
            "reason": "local-smoke-overbond",
            "epoch": 12,
            "force": True,
        },
        error_contains="dispute bond exceeds available reporter bond",
    )
    resolved_dispute = call(
        "dispute_rejected_slashes_escrow",
        "/api/oracle/dispute/resolve",
        {
            "dispute_id": dispute.get("dispute_id"),
            "outcome": "rejected",
            "epoch": 13,
        },
    )
    if ((resolved_dispute.get("dispute") or {}).get("bond_escrow_status")) != "slashed":
        raise RuntimeError(
            "oracle rejected dispute did not slash escrow: "
            f"{json.dumps(_summarize_response(resolved_dispute), sort_keys=True)}"
        )
    aggregate = call("aggregate_build", "/api/oracle/aggregate/build", {"query_id": query_id, "epoch": 12})
    read = call(
        "read_accept",
        "/api/oracle/read/accept",
        {
            "aggregate_id": aggregate.get("aggregate_id"),
            "consumer_module": "zenodex.zusd",
            "profile_id": "critical-zusd-v1",
        },
    )
    authorization = call(
        "authorization_build",
        "/api/oracle/authorization/build",
        {
            "read_id": read.get("read_id"),
            "action_kind": "mint",
            "action_id": action_id,
            "action_facts_hash": action_facts_hash,
            "pre_state_hash": pre_state_hash,
            "now_epoch": 12,
        },
    )
    reward = call("reward_pay", "/api/oracle/rewards/pay", {"amount_e8": 5})
    return {
        "ok": True,
        "query_id": query_id,
        "report_id": submitted.get("report_id"),
        "duplicate_report_idempotent": True,
        "dispute_id": dispute.get("dispute_id"),
        "aggregate_id": aggregate.get("aggregate_id"),
        "read_id": read.get("read_id"),
        "authorization_id": authorization.get("authorization_id"),
        "reward_receipt_id": reward.get("receipt_id") or reward.get("reward_receipt_id"),
        "steps": steps,
    }


def _decode_error_json(exc: urllib.error.HTTPError) -> dict[str, Any]:
    raw = exc.read().decode("utf-8", errors="replace")
    try:
        parsed = json.loads(raw)
    except json.JSONDecodeError:
        return {"error": raw or exc.reason}
    if isinstance(parsed, dict):
        return parsed
    return {"error": raw or exc.reason}


def _require_ok(payload: Mapping[str, Any], *, label: str) -> None:
    if payload.get("ok") is True:
        return
    raise RuntimeError(f"{label} failed: {json.dumps(payload, sort_keys=True)}")


def _extract_json_from_text(text: str) -> dict[str, Any]:
    lines = [line.strip() for line in text.splitlines() if line.strip()]
    for line in reversed(lines):
        try:
            obj = json.loads(line)
        except json.JSONDecodeError:
            continue
        if isinstance(obj, dict):
            return obj
    raise RuntimeError("expected JSON object in command output")


def _write_json(path: Path, payload: Mapping[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _tail_service_logs(*, engine: cm.ComposeEngine, project: str, env: dict[str, str]) -> None:
    for svc in ("tau-local", "zeno-ledger-writer", "zenodex-api", "zenodex-oracle", "zenodex-nginx"):
        tail = cm.compose_logs(
            engine=engine,
            project_name=project,
            compose_files=[COMPOSE_FILE],
            service=svc,
            tail=40,
            env=env,
        )
        sys.stderr.write(f"--- {svc} (last 40 lines) ---\n{tail}\n")


def _summary_text(manifest: dict[str, Any]) -> str:
    lines = [
        "",
        "ZenoDEX local-testnet is up.",
        "",
        f"  UI:                {manifest['service_urls']['ui']}",
        f"  Compose project:   {manifest['compose_project']}",
        f"  Chain ID:          {manifest['chain_id']}",
        f"  ZK mode:           {manifest.get('zk_mode_effective', 'open')} (requested {manifest.get('zk_mode_requested', 'open')})",
        f"  Manifest:          {manifest['out_dir']}/local_testnet_manifest.json",
        f"  Fixtures:          {manifest['host_paths']['fixtures_dir']}",
        f"  Key secrets:       {manifest['fixture_paths']['key_bundle']}",
        f"  Oracle home:       {manifest['host_paths']['oracle_home_dir']}",
        f"  Reports:           {manifest['host_paths']['reports_dir']}",
        "",
        "  Stop the stack (preserves state):",
        f"    python3 tools/zenoctl.py testnet local down --out-dir {manifest['out_dir']}",
        "",
    ]
    return "\n".join(lines)


def _emit_status(report: dict[str, Any], *, as_json: bool) -> None:
    if as_json:
        print(json.dumps(report, indent=2, sort_keys=True))
        return
    sys.stdout.write(f"ok={report['ok']} ui={report.get('ui_url')}\n")
    zk = report.get("zk_posture") if isinstance(report.get("zk_posture"), Mapping) else {}
    if zk:
        sys.stdout.write(
            f"zk.mode={zk.get('zk_mode_effective')} zk.required={zk.get('zk_required')} "
            f"proof_verifier={zk.get('proof_verifier_kind')}\n"
        )
    key_mgmt = report.get("key_management_authority") if isinstance(report.get("key_management_authority"), Mapping) else {}
    if key_mgmt:
        sys.stdout.write(
            "key_management.tokenomics_authority_ready="
            f"{key_mgmt.get('tokenomics_authority_ready')}\n"
        )
    base_health = report.get("base_health") or {}
    sys.stdout.write(f"base_health_ok={base_health.get('ok')}\n")
    for name, ok in sorted(((report.get("lanes") or {}).get("checks") or {}).items()):
        sys.stdout.write(f"lane.{name}={ok}\n")
    for svc in report.get("services", []):
        sys.stdout.write(f"  - {svc['name']}: state={svc['state']} health={svc['health']}\n")


def _log(phase: str, msg: str) -> None:
    sys.stderr.write(f"[testnet-local phase={phase}] {msg}\n")
