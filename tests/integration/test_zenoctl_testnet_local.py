"""Unit tests for `zenoctl testnet local` orchestration (no Docker required).

Verifies:
  - CLI dispatch shape (sub-commands present, required args enforced)
  - Manifest schema (build/save/load round-trip; validation rejects bad inputs)
  - Nginx template render (path split correct; tokens injected only in writer/
    stdlib blocks; nginx $variables preserved)
  - Token leakage guards (no literal token in manifest or runtime config)
  - Loopback-only enforcement in compose overlay
  - Port collision detection
  - Fixture determinism for same out-dir + chain-id
  - Compose image refs match the existing multimachine compose file
"""

from __future__ import annotations

import json
import os
import socket
import subprocess
import sys
import yaml
from contextlib import closing
from pathlib import Path

import pytest


REPO_ROOT = Path(__file__).resolve().parents[2]
COMPOSE_OVERLAY = REPO_ROOT / "docker-compose.local-testnet.yml"
COMPOSE_MULTIMACHINE = REPO_ROOT / "docker-compose.multimachine.yml"
NGINX_TEMPLATE = REPO_ROOT / ".docker" / "nginx.local-testnet.conf.template"


# ---------------------------------------------------------------------------
# Manifest schema
# ---------------------------------------------------------------------------


def _valid_manifest_kwargs(out_dir: Path) -> dict:
    return dict(
        out_dir=out_dir,
        chain_id="zeno-ledger-localtest-v0",
        network_id="zeno-ledger-localtest-v0",
        ports={"ui": 18080},
        service_urls={
            "ui": "http://127.0.0.1:18080",
            "stdlib_api": "compose://zenodex-api:8000",
            "writer": "compose://zeno-ledger-writer:8787",
            "oracle": "compose://zenodex-oracle:9100",
            "tau": "compose://tau-local:65432",
        },
        image_refs={
            "operator_tools": "zenodex/operator-tools:local",
            "tau_local": "zenodex/tau-local:local-testnet",
        },
        enabled_lanes=["DEX_API_ENABLED", "PERPS_WALLET_API_ENABLED"],
        fixture_paths={
            "key_bundle": str(out_dir / "fixtures" / "keys.json"),
            "oracle_authority_profile": str(out_dir / "fixtures" / "oracle_authority_profile.json"),
            "perps_wallet_authority_profile": str(out_dir / "fixtures" / "perps_wallet_authority_profile.json"),
            "autotrader_supervisor_profile": str(out_dir / "fixtures" / "autotrader_supervisor_profile.json"),
            "guardian_quorum": str(out_dir / "fixtures" / "guardians.json"),
        },
        ledger_bundle_manifest=str(out_dir / "ledger" / "public_testnet_manifest.json"),
        writer_token="writer-secret-abc",
        created_at_ms=1_700_000_000_000,
    )


def test_manifest_build_validate_roundtrip(tmp_path: Path) -> None:
    from tools.zenoctl_testnet_local import manifest as mf

    body = mf.build_manifest(**_valid_manifest_kwargs(tmp_path))
    assert mf.validate_manifest(body) == []
    assert body["schema"] == mf.SCHEMA_V1
    assert body["compose_project"].startswith("zenodex-local-testnet-")
    assert body["writer_token_sha256"].startswith("sha256:")
    assert body["rendered_paths"]["nginx_conf"].startswith("/")
    assert body["rendered_paths"]["runtime_config"].startswith("/")
    assert body["host_paths"]["fixtures_dir"].startswith("/")
    assert body["host_paths"]["oracle_home_dir"].startswith("/")
    assert body["host_paths"]["reports_dir"].startswith("/")
    assert "writer-secret-abc" not in json.dumps(body, sort_keys=True), "raw token must not be in manifest"


def test_manifest_save_load_roundtrip(tmp_path: Path) -> None:
    from tools.zenoctl_testnet_local import manifest as mf

    body = mf.build_manifest(**_valid_manifest_kwargs(tmp_path))
    path = tmp_path / "manifest.json"
    mf.save_manifest(body, path)
    assert path.is_file()
    loaded = mf.load_manifest(path)
    assert loaded == body


def test_manifest_rejects_bad_schema(tmp_path: Path) -> None:
    from tools.zenoctl_testnet_local import manifest as mf

    body = mf.build_manifest(**_valid_manifest_kwargs(tmp_path))
    body["schema"] = "wrong"
    errors = mf.validate_manifest(body)
    assert any("schema" in e for e in errors)


def test_manifest_rejects_missing_keys(tmp_path: Path) -> None:
    from tools.zenoctl_testnet_local import manifest as mf

    body = mf.build_manifest(**_valid_manifest_kwargs(tmp_path))
    del body["service_urls"]
    errors = mf.validate_manifest(body)
    assert any("service_urls" in e for e in errors)


def test_manifest_rejects_invalid_port(tmp_path: Path) -> None:
    from tools.zenoctl_testnet_local import manifest as mf

    body = mf.build_manifest(**_valid_manifest_kwargs(tmp_path))
    body["ports"]["ui"] = 99_999
    errors = mf.validate_manifest(body)
    assert any("ports[ui]" in e for e in errors)


def test_writer_token_sha256_is_stable() -> None:
    from tools.zenoctl_testnet_local import manifest as mf

    a = mf.writer_token_sha256("hello-token")
    b = mf.writer_token_sha256("hello-token")
    assert a == b
    c = mf.writer_token_sha256("different")
    assert a != c


# ---------------------------------------------------------------------------
# Fixture determinism
# ---------------------------------------------------------------------------


def test_fixture_seed_is_deterministic_per_out_dir(tmp_path: Path) -> None:
    from tools.zenoctl_testnet_local import fixtures as fx

    s1 = fx.derive_seed(out_dir=tmp_path, chain_id="zeno-ledger-localtest-v0")
    s2 = fx.derive_seed(out_dir=tmp_path, chain_id="zeno-ledger-localtest-v0")
    assert s1 == s2

    s3 = fx.derive_seed(out_dir=tmp_path, chain_id="other-chain")
    assert s1 != s3, "chain_id change must rotate seed"


def test_fixture_role_keys_are_distinct() -> None:
    from tools.zenoctl_testnet_local import fixtures as fx

    seed = b"\xab" * 32
    keys = {role: fx.derive_role_privkey(seed, role) for role in fx.KEY_ROLES}
    assert len(set(keys.values())) == len(fx.KEY_ROLES)


def test_fixture_writer_token_is_not_a_role_key() -> None:
    from tools.zenoctl_testnet_local import fixtures as fx

    seed = b"\xab" * 32
    token_hex = fx.derive_writer_token(seed)
    token_bytes = bytes.fromhex(token_hex)
    for role in fx.KEY_ROLES:
        assert token_bytes != fx.derive_role_privkey(seed, role)


def test_fixture_bundle_writes_expected_files(tmp_path: Path) -> None:
    from tools.zenoctl_testnet_local import fixtures as fx

    bundle = fx.generate_fixture_bundle(
        out_dir=tmp_path,
        chain_id="zeno-ledger-localtest-v0",
        network_id="zeno-ledger-localtest-v0",
        created_at_ms=1000,
    )
    for path in (
        bundle.key_bundle,
        bundle.oracle_authority_profile,
        bundle.perps_wallet_authority_profile,
        bundle.autotrader_supervisor_profile,
        bundle.guardian_quorum,
    ):
        assert path.is_file(), f"missing fixture file: {path}"

    doc = json.loads(bundle.key_bundle.read_text(encoding="utf-8"))
    assert doc["schema"] == "zenodex.local_testnet.key_bundle.v0"
    assert set(doc["roles"].keys()) == set(fx.KEY_ROLES)


def test_fixture_bundle_writes_key_material_with_owner_only_mode(tmp_path: Path) -> None:
    from tools.zenoctl_testnet_local import fixtures as fx

    bundle = fx.generate_fixture_bundle(
        out_dir=tmp_path,
        chain_id="zeno-ledger-localtest-v0",
        network_id="zeno-ledger-localtest-v0",
        created_at_ms=1000,
    )
    if os.name == "nt":
        pytest.skip("chmod mode bits are not reliable on Windows")
    for path in (
        bundle.key_bundle,
        bundle.oracle_authority_profile,
        bundle.perps_wallet_authority_profile,
        bundle.autotrader_supervisor_profile,
        bundle.guardian_quorum,
    ):
        mode = path.stat().st_mode & 0o777
        assert mode == 0o600, f"{path} must be 0600, got {oct(mode)}"


def test_fixture_bundle_is_byte_identical_across_reruns(tmp_path: Path) -> None:
    from tools.zenoctl_testnet_local import fixtures as fx
    import hashlib

    common_kwargs = dict(
        out_dir=tmp_path,
        chain_id="zeno-ledger-localtest-v0",
        network_id="zeno-ledger-localtest-v0",
        created_at_ms=1000,
    )
    b1 = fx.generate_fixture_bundle(**common_kwargs)
    b2 = fx.generate_fixture_bundle(**common_kwargs)
    assert hashlib.sha256(b1.key_bundle.read_bytes()).hexdigest() == hashlib.sha256(
        b2.key_bundle.read_bytes()
    ).hexdigest()


def test_fixture_profiles_pass_live_authority_evaluators(tmp_path: Path) -> None:
    from src.integration.autotrader_supervisor_profile import evaluate_autotrader_supervisor_profile_v1
    from src.integration.perps_wallet_authority import evaluate_perps_wallet_authority_profile_v1
    from src.integration.zeno_oracle_authority import evaluate_oracle_authority_profile_v1
    from tools.zenoctl_testnet_local import fixtures as fx

    chain_id = "zeno-ledger-localtest-v0"
    bundle = fx.generate_fixture_bundle(
        out_dir=tmp_path,
        chain_id=chain_id,
        network_id=chain_id,
        created_at_ms=1000,
    )

    oracle_profile = json.loads(bundle.oracle_authority_profile.read_text(encoding="utf-8"))
    oracle_status = evaluate_oracle_authority_profile_v1(oracle_profile)
    assert oracle_status["ok"] is True, oracle_status["readiness_gaps"]

    perps_profile = json.loads(bundle.perps_wallet_authority_profile.read_text(encoding="utf-8"))
    perps_status = evaluate_perps_wallet_authority_profile_v1(
        perps_profile,
        expected_chain_id=chain_id,
    )
    assert perps_status["ok"] is True, perps_status["readiness_gaps"]

    autotrader_profile = json.loads(bundle.autotrader_supervisor_profile.read_text(encoding="utf-8"))
    autotrader_status = evaluate_autotrader_supervisor_profile_v1(
        autotrader_profile,
        expected_chain_id=chain_id,
    )
    assert autotrader_status["ok"] is True, autotrader_status["readiness_gaps"]


def test_fixture_seed_and_random_are_mutually_exclusive(tmp_path: Path) -> None:
    from tools.zenoctl_testnet_local import fixtures as fx

    with pytest.raises(ValueError, match="mutually exclusive"):
        fx.generate_fixture_bundle(
            out_dir=tmp_path,
            chain_id="zeno-ledger-localtest-v0",
            network_id="zeno-ledger-localtest-v0",
            seed_override_hex="ab" * 32,
            use_random=True,
        )


def test_fixture_seed_override_rejects_bad_length(tmp_path: Path) -> None:
    from tools.zenoctl_testnet_local import fixtures as fx

    with pytest.raises(ValueError, match="32 bytes"):
        fx.generate_fixture_bundle(
            out_dir=tmp_path,
            chain_id="zeno-ledger-localtest-v0",
            network_id="zeno-ledger-localtest-v0",
            seed_override_hex="ab" * 16,
        )


def test_lifecycle_seed_resolution_default_matches_fixture_derivation(tmp_path: Path) -> None:
    from tools.zenoctl_testnet_local import fixtures as fx
    from tools.zenoctl_testnet_local import lifecycle as lc

    opts = lc.UpOptions(
        out_dir=tmp_path,
        chain_id="zeno-ledger-localtest-v0",
        network_id="zeno-ledger-localtest-v0",
    )
    assert lc._resolve_fixture_seed(opts) == fx.derive_seed(
        out_dir=tmp_path,
        chain_id="zeno-ledger-localtest-v0",
    )


def test_lifecycle_seed_resolution_uses_override(tmp_path: Path) -> None:
    from tools.zenoctl_testnet_local import lifecycle as lc

    override = "ab" * 32
    opts = lc.UpOptions(
        out_dir=tmp_path,
        chain_id="zeno-ledger-localtest-v0",
        network_id="zeno-ledger-localtest-v0",
        seed_override_hex=override,
    )
    assert lc._resolve_fixture_seed(opts) == bytes.fromhex(override)


def test_lifecycle_seed_resolution_validates_override(tmp_path: Path) -> None:
    from tools.zenoctl_testnet_local import lifecycle as lc

    bad_len = lc.UpOptions(
        out_dir=tmp_path,
        chain_id="zeno-ledger-localtest-v0",
        network_id="zeno-ledger-localtest-v0",
        seed_override_hex="ab" * 16,
    )
    with pytest.raises(ValueError, match="32 bytes"):
        lc._resolve_fixture_seed(bad_len)

    bad_hex = lc.UpOptions(
        out_dir=tmp_path,
        chain_id="zeno-ledger-localtest-v0",
        network_id="zeno-ledger-localtest-v0",
        seed_override_hex="zz" * 32,
    )
    with pytest.raises(ValueError, match="valid hex"):
        lc._resolve_fixture_seed(bad_hex)


def test_lifecycle_seed_resolution_random_mode_uses_token_bytes(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path: Path,
) -> None:
    from tools.zenoctl_testnet_local import lifecycle as lc

    monkeypatch.setattr(lc.secrets, "token_bytes", lambda n: b"\x42" * n)
    opts = lc.UpOptions(
        out_dir=tmp_path,
        chain_id="zeno-ledger-localtest-v0",
        network_id="zeno-ledger-localtest-v0",
        use_random_seed=True,
    )
    assert lc._resolve_fixture_seed(opts) == b"\x42" * 32


# ---------------------------------------------------------------------------
# Nginx render
# ---------------------------------------------------------------------------


def _nginx_inputs():
    from tools.zenoctl_testnet_local.nginx import NginxRenderInputs

    return NginxRenderInputs(
        writer_upstream="zeno-ledger-writer:8787",
        stdlib_upstream="zenodex-api:8000",
        oracle_upstream="zenodex-oracle:9100",
        writer_token="writer-secret-abc",
        stdlib_token="stdlib-secret-xyz",
    )


def test_nginx_template_renders_all_required_location_blocks() -> None:
    from tools.zenoctl_testnet_local import nginx as ng

    rendered = ng.render_nginx_conf(_nginx_inputs())
    for block in ng.EXPECTED_LOCATION_BLOCKS:
        assert block in rendered, f"missing nginx location block: {block!r}"


def test_nginx_path_split_targets_correct_upstreams() -> None:
    from tools.zenoctl_testnet_local import nginx as ng

    rendered = ng.render_nginx_conf(_nginx_inputs())
    # /api/pools and /api/swap → writer (URI passed through)
    assert "http://zeno-ledger-writer:8787/api/pools" in rendered
    assert "http://zeno-ledger-writer:8787/api/swap" in rendered
    # /api/oracle/ → oracle. proxy_pass omits the trailing slash so the
    # full URI (/api/oracle/...) is preserved, matching the oracle
    # service's route table at tools/zenodex_oracle.py:/api/oracle/*.
    assert "proxy_pass http://zenodex-oracle:9100;" in rendered
    # /api/ (everything else) → stdlib API, also preserving the URI so
    # routes like /api/zusd/wallet/* reach src/integration/api_server.py.
    assert "proxy_pass http://zenodex-api:8000;" in rendered


def test_nginx_injects_bearer_tokens_for_writer_and_stdlib() -> None:
    from tools.zenoctl_testnet_local import nginx as ng

    rendered = ng.render_nginx_conf(_nginx_inputs())
    assert 'Bearer writer-secret-abc' in rendered
    assert 'Bearer stdlib-secret-xyz' in rendered


def test_nginx_does_not_inject_writer_token_into_oracle_block() -> None:
    """The oracle does not get a token injection; writer/stdlib do."""
    from tools.zenoctl_testnet_local import nginx as ng

    rendered = ng.render_nginx_conf(_nginx_inputs())
    # Slice out the oracle block. The template uses ^~ prefix to make
    # /api/oracle/ take precedence over the /api/ catch-all.
    oracle_idx = rendered.index("location ^~ /api/oracle/")
    next_block = rendered.find("location ^~ /api/", oracle_idx + 1)
    assert next_block > oracle_idx, "expected stdlib /api/ block after oracle block"
    oracle_chunk = rendered[oracle_idx:next_block]
    assert "Bearer" not in oracle_chunk, "oracle block must not inject Bearer"


def test_nginx_preserves_nginx_variables() -> None:
    """nginx variables like $binary_remote_addr must NOT be substituted by
    our template renderer."""
    from tools.zenoctl_testnet_local import nginx as ng

    rendered = ng.render_nginx_conf(_nginx_inputs())
    assert "$binary_remote_addr" in rendered
    assert "$remote_addr" in rendered
    assert "$host" in rendered


def test_nginx_listens_on_port_8080_only() -> None:
    from tools.zenoctl_testnet_local import nginx as ng

    rendered = ng.render_nginx_conf(_nginx_inputs())
    # Single 'listen' directive inside the server{} block.
    assert "listen 8080;" in rendered
    # No 'listen 80' or arbitrary other ports leaked from a typo
    bad_listens = [
        line for line in rendered.splitlines()
        if line.strip().startswith("listen ") and "8080" not in line
    ]
    assert not bad_listens, f"unexpected listen directives: {bad_listens}"


def test_nginx_render_rejects_empty_token() -> None:
    from tools.zenoctl_testnet_local import nginx as ng
    import dataclasses

    with pytest.raises(ValueError, match="non-empty"):
        ng.render_nginx_conf(dataclasses.replace(_nginx_inputs(), writer_token=""))


def test_nginx_render_rejects_malformed_upstream() -> None:
    from tools.zenoctl_testnet_local import nginx as ng
    import dataclasses

    with pytest.raises(ValueError, match="host:port"):
        ng.render_nginx_conf(dataclasses.replace(_nginx_inputs(), writer_upstream="no-port"))


def test_runtime_config_has_no_tokens() -> None:
    from tools.zenoctl_testnet_local import nginx as ng

    runtime = ng.render_runtime_config(demo_mode=False)
    parsed = json.loads(runtime)
    assert parsed["demoMode"] is False
    assert parsed["apiBase"] == ""
    assert parsed["zenoOracleApiBase"] == ""
    assert parsed["oracleApiBase"] == ""
    # No bearer-token-like fields
    serialized = json.dumps(parsed, sort_keys=True)
    assert "Bearer" not in serialized
    assert "writer" not in serialized.lower()
    assert "token" not in serialized.lower()


def test_runtime_config_rejects_overriding_builtin_keys() -> None:
    from tools.zenoctl_testnet_local import nginx as ng

    with pytest.raises(ValueError, match="conflicts"):
        ng.render_runtime_config(extra={"demoMode": True})


def test_token_leak_guard_fires_when_token_present(tmp_path: Path) -> None:
    from tools.zenoctl_testnet_local import nginx as ng

    leaky = tmp_path / "leaky.json"
    leaky.write_text(json.dumps({"oops": "writer-secret-abc"}))
    with pytest.raises(AssertionError, match="SECURITY"):
        ng.assert_no_token_in_file(leaky, "writer-secret-abc")


def test_token_leak_guard_silent_when_clean(tmp_path: Path) -> None:
    from tools.zenoctl_testnet_local import nginx as ng

    clean = tmp_path / "clean.json"
    clean.write_text(json.dumps({"foo": "bar"}))
    ng.assert_no_token_in_file(clean, "writer-secret-abc")  # no raise


# ---------------------------------------------------------------------------
# Compose overlay
# ---------------------------------------------------------------------------


def _load_compose_overlay() -> dict:
    return yaml.safe_load(COMPOSE_OVERLAY.read_text(encoding="utf-8"))


def _load_multimachine() -> dict:
    return yaml.safe_load(COMPOSE_MULTIMACHINE.read_text(encoding="utf-8"))


def test_compose_overlay_has_all_expected_services() -> None:
    doc = _load_compose_overlay()
    expected = {
        "zeno-ledger-bootstrap",
        "zeno-ledger-writer",
        "zeno-ledger-forwarder",
        "zeno-ledger-readonly",
        "tau-local",
        "zenodex-oracle",
        "zenodex-api",
        "zenodex-nginx",
    }
    assert set(doc["services"].keys()) == expected


def test_compose_overlay_only_nginx_exposes_host_ports() -> None:
    doc = _load_compose_overlay()
    for name, svc in doc["services"].items():
        ports = svc.get("ports") or []
        if name == "zenodex-nginx":
            assert ports, "nginx must expose a port"
        else:
            assert not ports, f"service {name!r} must NOT expose host ports, got {ports}"


def test_compose_overlay_nginx_binds_loopback_only() -> None:
    doc = _load_compose_overlay()
    ports = doc["services"]["zenodex-nginx"].get("ports") or []
    assert ports, "nginx ports missing"
    for p in ports:
        # Each binding must include 127.0.0.1; reject 0.0.0.0 or implicit-any binds.
        assert "127.0.0.1" in p, f"nginx must bind loopback only, got {p!r}"


def test_compose_overlay_image_refs_match_multimachine() -> None:
    """The local-testnet overlay reuses Dockerfile.operator-tools (image
    `zenodex/operator-tools:local`). It must agree with the multimachine
    file on that image tag to avoid silent build drift."""
    overlay = _load_compose_overlay()
    multi = _load_multimachine()
    multi_writer_image = multi["services"]["zeno-ledger-writer"]["image"]
    overlay_writer_image = overlay["services"]["zeno-ledger-writer"]["image"]
    assert (
        overlay_writer_image == multi_writer_image
    ), f"image drift: overlay={overlay_writer_image} vs multimachine={multi_writer_image}"


def test_compose_overlay_api_command_respects_operator_tools_entrypoint() -> None:
    doc = _load_compose_overlay()
    command = doc["services"]["zenodex-api"]["command"]
    assert command[:2] == ["-m", "src.integration.api_server"]


def test_compose_overlay_api_explicitly_allows_local_demo_token_auth() -> None:
    doc = _load_compose_overlay()
    env = doc["services"]["zenodex-api"]["environment"]
    assert env["ALLOW_DEMO_TOKEN_AUTH"] == "1"


def test_compose_overlay_bootstrap_service_has_writer_token_for_controller_runs() -> None:
    doc = _load_compose_overlay()
    env = doc["services"]["zeno-ledger-bootstrap"]["environment"]
    assert "ZENO_LEDGER_WRITER_TOKEN" in env


def test_compose_overlay_readonly_authenticates_controller_rejection_probe() -> None:
    doc = _load_compose_overlay()
    service = doc["services"]["zeno-ledger-readonly"]
    command = service["command"]
    assert service["environment"] == doc["services"]["zeno-ledger-writer"]["environment"]
    assert "--write-auth-token-env" in command
    assert "ZENO_LEDGER_WRITER_TOKEN" in command
    assert "--enable-testnet-faucet" not in command
    assert "--enable-testnet-intake" not in command


def test_compose_overlay_tau_local_enables_balance_patch_for_local_state_bootstrap() -> None:
    doc = _load_compose_overlay()
    env = doc["services"]["tau-local"]["environment"]
    assert env["TAU_ENABLE_FAUCET"] == "0"
    assert env["TAU_APP_BRIDGE_ALLOW_BALANCE_PATCH"] == "1"


def test_compose_overlay_requires_orchestrator_env() -> None:
    """The compose file must use `${VAR:?…}` to refuse running without
    orchestrator-provided env."""
    raw = COMPOSE_OVERLAY.read_text(encoding="utf-8")
    for required in (
        "ZENO_LEDGER_WRITER_TOKEN",
        "DEMO_API_TOKEN",
        "RENDERED_NGINX_CONF_PATH",
        "RENDERED_RUNTIME_CONFIG_PATH",
        "FIXTURES_DIR",
        "ORACLE_HOME_DIR",
        "HOST_UID",
        "HOST_GID",
        "TAU_DEX_TOKEN_OPERATOR_PUBKEY",
        "TAU_DEX_ORACLE_PUBKEY",
        "TAU_DEX_ZUSD_ORACLE_PUBKEY",
    ):
        assert f"{required}:?" in raw, f"compose overlay must require env {required!r}"


def test_compose_overlay_bind_mount_services_run_as_host_user() -> None:
    doc = _load_compose_overlay()
    expected = "${HOST_UID:?HOST_UID must be set by the orchestrator}:${HOST_GID:?HOST_GID must be set by the orchestrator}"
    for service in ("zenodex-oracle", "zenodex-api", "zenodex-nginx"):
        assert doc["services"][service]["user"] == expected


def test_compose_overlay_api_seeds_confidential_local_smoke_profile() -> None:
    """The confidential UI/API path should be testable in local mode."""
    doc = _load_compose_overlay()
    env = doc["services"]["zenodex-api"]["environment"]
    assert env["CONFIDENTIAL_ATTESTATION_API_ENABLED"] == "true"
    assert env["CONFIDENTIAL_ATTESTATION_VERIFIER_ENABLED"] == "true"
    assert "CONFIDENTIAL_ATTESTATION_VERIFIER_CMD_JSON" in env
    assert '["/usr/local/bin/python"' in env["CONFIDENTIAL_ATTESTATION_VERIFIER_CMD_JSON"]
    assert env["CONFIDENTIAL_APPROVED_MEASUREMENTS"].startswith("nitro:pcr0:")
    assert env["CONFIDENTIAL_OPERATOR_CONTACT"].startswith("https://")


def test_operator_tools_image_copies_perps_reference_models() -> None:
    """Perps wallet submit paths import generated reference models at runtime."""
    raw = (REPO_ROOT / "Dockerfile.operator-tools").read_text(encoding="utf-8")
    for name in (
        "perp_epoch_clearinghouse_2p_v0_1_ref.py",
        "perp_epoch_clearinghouse_3p_transfer_v0_1_ref.py",
        "perp_epoch_isolated_v2_ref.py",
        "perp_epoch_isolated_v3_ref.py",
    ):
        assert f"COPY generated/perp_python/{name}" in raw


def test_local_seed_advances_perps_epoch_for_first_ui_publish() -> None:
    raw = (REPO_ROOT / "tools/zenoctl_testnet_local/lifecycle.py").read_text(encoding="utf-8")
    assert 'report["steps"]["perps_advance_epoch"]' in raw
    assert '"action": "advance_epoch"' in raw


def test_perps_pre_publish_step_handles_reusable_smoke_states() -> None:
    from tools.zenoctl_testnet_local import lifecycle as lc

    assert lc._perps_pre_publish_step({"now_epoch": 0, "clearing_price_epoch": 0}) == "advance"
    assert (
        lc._perps_pre_publish_step(
            {"now_epoch": 2, "clearing_price_epoch": 2, "oracle_last_update_epoch": 1}
        )
        == "settle_then_advance"
    )
    assert (
        lc._perps_pre_publish_step(
            {"now_epoch": 2, "clearing_price_epoch": 1, "oracle_last_update_epoch": 1}
        )
        == "none"
    )


# ---------------------------------------------------------------------------
# Port collision detection
# ---------------------------------------------------------------------------


def test_port_collision_raises_actionable_error() -> None:
    from tools.zenoctl_testnet_local import compose as cm

    listener = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
    listener.bind(("127.0.0.1", 0))
    listener.listen(1)
    busy_port = listener.getsockname()[1]
    try:
        with pytest.raises(ValueError, match="is in use"):
            cm.check_host_port_free(busy_port)
    finally:
        listener.close()


def test_port_collision_check_accepts_free_port() -> None:
    from tools.zenoctl_testnet_local import compose as cm

    with closing(socket.socket(socket.AF_INET, socket.SOCK_STREAM)) as s:
        s.bind(("127.0.0.1", 0))
        free_port = s.getsockname()[1]
    cm.check_host_port_free(free_port)  # no raise


def test_port_collision_rejects_out_of_range() -> None:
    from tools.zenoctl_testnet_local import compose as cm

    for bad in (0, -1, 65_536, 100_000):
        with pytest.raises(ValueError, match=r"out of range"):
            cm.check_host_port_free(bad)


# ---------------------------------------------------------------------------
# CLI shape
# ---------------------------------------------------------------------------


def _zenoctl(*args: str) -> subprocess.CompletedProcess:
    return subprocess.run(
        [sys.executable, "tools/zenoctl.py", *args],
        cwd=str(REPO_ROOT),
        capture_output=True,
        text=True,
        check=False,
        timeout=30,
    )


def test_cli_testnet_local_help_lists_full_lifecycle_surface() -> None:
    result = _zenoctl("testnet", "local", "--help")
    assert result.returncode == 0, result.stderr
    for sub in ("up", "down", "status", "smoke", "logs", "reset"):
        assert sub in result.stdout, f"missing subcommand: {sub}"


def test_cli_testnet_local_up_requires_out_dir() -> None:
    result = _zenoctl("testnet", "local", "up")
    assert result.returncode != 0
    assert "--out-dir" in result.stderr or "required" in result.stderr.lower()


def test_cli_testnet_local_up_help_documents_options() -> None:
    result = _zenoctl("testnet", "local", "up", "--help")
    assert result.returncode == 0, result.stderr
    for flag in ("--out-dir", "--chain-id", "--ui-port", "--engine", "--force", "--seed", "--random"):
        assert flag in result.stdout, f"missing flag in up help: {flag}"


def test_cli_testnet_local_smoke_help_documents_browser_options() -> None:
    result = _zenoctl("testnet", "local", "smoke", "--help")
    assert result.returncode == 0, result.stderr
    for flag in ("--out-dir", "--engine", "--browser", "--chrome-bin", "--browser-timeout"):
        assert flag in result.stdout, f"missing flag in smoke help: {flag}"


def test_cli_existing_testnet_subcommands_still_present() -> None:
    """Adding `local` must not remove `init|up|evidence|verify-evidence`."""
    result = _zenoctl("testnet", "--help")
    assert result.returncode == 0
    for sub in ("init", "up", "evidence", "verify-evidence", "local"):
        assert sub in result.stdout, f"missing subcommand under testnet: {sub}"


def test_cli_rejects_malformed_seed_hex(tmp_path: Path) -> None:
    """--seed must be exactly 64 hex chars; clear error before any compose work."""
    # Wrong length
    result = _zenoctl(
        "testnet", "local", "up", "--out-dir", str(tmp_path), "--seed", "ab" * 16
    )
    assert result.returncode == 2
    assert "64 hex" in result.stderr.lower() or "64 hex" in result.stdout.lower()

    # Wrong charset
    result = _zenoctl(
        "testnet", "local", "up", "--out-dir", str(tmp_path), "--seed", "z" * 64
    )
    assert result.returncode == 2
    assert "hex" in result.stderr.lower() or "hex" in result.stdout.lower()


def test_cli_rejects_seed_and_random_together(tmp_path: Path) -> None:
    """argparse mutually-exclusive group must reject both flags."""
    result = _zenoctl(
        "testnet", "local", "up",
        "--out-dir", str(tmp_path),
        "--seed", "ab" * 32,
        "--random",
    )
    assert result.returncode != 0
    assert "not allowed" in result.stderr.lower() or "argument" in result.stderr.lower()


def test_cli_reset_requires_force(tmp_path: Path) -> None:
    """`reset` is destructive (removes compose volumes + out-dir). Without
    --force it must refuse with exit code 2 and a clear message — no
    docker invocation, no rmtree."""
    sentinel = tmp_path / "sentinel.txt"
    sentinel.write_text("keep me", encoding="utf-8")
    result = _zenoctl("testnet", "local", "reset", "--out-dir", str(tmp_path))
    assert result.returncode == 2, result.stderr
    assert "force" in result.stderr.lower(), result.stderr
    # The sentinel must still be on disk: refusing --force must not touch the dir.
    assert sentinel.read_text(encoding="utf-8") == "keep me"


# ---------------------------------------------------------------------------
# Destructive-path safety guards
# ---------------------------------------------------------------------------


def test_reset_refuses_filesystem_root() -> None:
    """A typo like `--out-dir /` must not be able to wipe the host."""
    from tools.zenoctl_testnet_local import lifecycle as lc

    with pytest.raises(ValueError, match="refusing destructive"):
        lc._refuse_unsafe_reset_target(Path("/"))


def test_reset_refuses_user_home_itself() -> None:
    """Refuse to rmtree the user's home directory itself."""
    from tools.zenoctl_testnet_local import lifecycle as lc

    with pytest.raises(ValueError, match="home directory"):
        lc._refuse_unsafe_reset_target(Path.home())


def test_reset_refuses_system_directories() -> None:
    from tools.zenoctl_testnet_local import lifecycle as lc

    for sysdir in ("/etc", "/usr", "/var", "/opt", "/root", "/home", "/bin", "/sbin"):
        with pytest.raises(ValueError, match="refusing destructive"):
            lc._refuse_unsafe_reset_target(Path(sysdir))


def test_reset_allows_dedicated_out_dirs(tmp_path: Path) -> None:
    """Tmp paths and user-chosen subdirectories must be allowed."""
    from tools.zenoctl_testnet_local import lifecycle as lc

    lc._refuse_unsafe_reset_target(tmp_path)
    lc._refuse_unsafe_reset_target(Path.home() / "zen-local-testnet")


def test_reset_refuses_dir_without_manifest_when_dir_has_unrelated_files(tmp_path: Path) -> None:
    """If the out-dir has no manifest AND contains files we didn't create,
    refuse the reset — the user likely pointed at a populated dir by mistake."""
    from tools.zenoctl_testnet_local import lifecycle as lc
    from tools.zenoctl_testnet_local import manifest as mf

    unrelated = tmp_path / "my_real_data.txt"
    unrelated.write_text("important user data", encoding="utf-8")
    paths = mf.ManifestPaths.from_out_dir(tmp_path)
    with pytest.raises(ValueError, match="unrelated entries"):
        lc._reset_stack(paths=paths, engine_name="auto", manifest=None)
    assert unrelated.exists(), "guard must not have deleted the file"


# ---------------------------------------------------------------------------
# Lifecycle env helper (down / status compose-env contract)
# ---------------------------------------------------------------------------


def test_lifecycle_env_for_compose_returns_all_required_vars(tmp_path: Path) -> None:
    """`down` and `status` invoke compose, which interpolates ${VAR:?...}.
    The env helper must set every var the overlay requires, so compose
    operations on an existing stack don't fail with "VAR not set"."""
    from tools.zenoctl_testnet_local import lifecycle as lc
    from tools.zenoctl_testnet_local import manifest as mf

    body = mf.build_manifest(**_valid_manifest_kwargs(tmp_path))
    paths = mf.ManifestPaths.from_out_dir(tmp_path)
    env = lc._lifecycle_env_for_compose(body, paths)
    for required in (
        "ZENO_LEDGER_WRITER_TOKEN",
        "DEMO_API_TOKEN",
        "RENDERED_NGINX_CONF_PATH",
        "RENDERED_RUNTIME_CONFIG_PATH",
        "FIXTURES_DIR",
        "ORACLE_HOME_DIR",
        "HOST_UID",
        "HOST_GID",
        "UI_PORT",
        "CHAIN_ID",
        "NETWORK_ID",
        "TAU_DEX_TOKEN_OPERATOR_PUBKEY",
        "TAU_DEX_ORACLE_PUBKEY",
        "TAU_DEX_ZUSD_ORACLE_PUBKEY",
    ):
        assert env.get(required), f"compose env missing required var: {required}"


def test_lifecycle_env_does_not_leak_real_tokens(tmp_path: Path) -> None:
    """The down/status env uses placeholders, never the real bearer token."""
    from tools.zenoctl_testnet_local import lifecycle as lc
    from tools.zenoctl_testnet_local import manifest as mf

    body = mf.build_manifest(**_valid_manifest_kwargs(tmp_path))
    paths = mf.ManifestPaths.from_out_dir(tmp_path)
    env = lc._lifecycle_env_for_compose(body, paths)
    # Manifest input used 'writer-secret-abc' as the raw token; the env
    # must NOT carry that value into compose.
    assert env["ZENO_LEDGER_WRITER_TOKEN"] != "writer-secret-abc"


def test_runtime_env_for_existing_manifest_recovers_tokens_and_roles(tmp_path: Path) -> None:
    """Restarting an existing stack must recover the live compose env from
    saved local artifacts. The manifest stores only the writer-token hash."""
    from tools.zenoctl_testnet_local import fixtures as fx
    from tools.zenoctl_testnet_local import lifecycle as lc
    from tools.zenoctl_testnet_local import manifest as mf
    from tools.zenoctl_testnet_local import nginx as ng

    paths = mf.ManifestPaths.from_out_dir(tmp_path)
    bundle = fx.generate_fixture_bundle(
        out_dir=tmp_path,
        chain_id="zeno-ledger-localtest-v0",
        network_id="zeno-ledger-localtest-v0",
        created_at_ms=1000,
    )
    writer_token = "writer-secret-abc"
    stdlib_token = "stdlib-secret-xyz"
    rendered = ng.render_nginx_conf(
        ng.NginxRenderInputs(
            writer_upstream="zeno-ledger-writer:8787",
            stdlib_upstream="zenodex-api:8000",
            oracle_upstream="zenodex-oracle:9100",
            writer_token=writer_token,
            stdlib_token=stdlib_token,
        )
    )
    ng.write_rendered_conf(rendered, out_path=paths.rendered_nginx)

    body = mf.build_manifest(
        **{
            **_valid_manifest_kwargs(tmp_path),
            "fixture_paths": bundle.as_manifest_paths(),
            "writer_token": writer_token,
        }
    )
    env = lc._runtime_env_for_existing_manifest(manifest=body, paths=paths)

    assert env["ZENO_LEDGER_WRITER_TOKEN"] == writer_token
    assert env["DEMO_API_TOKEN"] == stdlib_token
    assert env["UI_PORT"] == "18080"
    assert env["CHAIN_ID"] == "zeno-ledger-localtest-v0"
    assert env["TAU_DEX_TOKEN_OPERATOR_PUBKEY"]
    assert env["TAU_DEX_ORACLE_PUBKEY"]
    assert env["TAU_DEX_ZUSD_ORACLE_PUBKEY"]


def test_runtime_env_for_existing_manifest_rejects_writer_hash_mismatch(tmp_path: Path) -> None:
    from tools.zenoctl_testnet_local import fixtures as fx
    from tools.zenoctl_testnet_local import lifecycle as lc
    from tools.zenoctl_testnet_local import manifest as mf
    from tools.zenoctl_testnet_local import nginx as ng

    paths = mf.ManifestPaths.from_out_dir(tmp_path)
    bundle = fx.generate_fixture_bundle(
        out_dir=tmp_path,
        chain_id="zeno-ledger-localtest-v0",
        network_id="zeno-ledger-localtest-v0",
        created_at_ms=1000,
    )
    rendered = ng.render_nginx_conf(
        ng.NginxRenderInputs(
            writer_upstream="zeno-ledger-writer:8787",
            stdlib_upstream="zenodex-api:8000",
            oracle_upstream="zenodex-oracle:9100",
            writer_token="rendered-writer-token",
            stdlib_token="stdlib-secret-xyz",
        )
    )
    ng.write_rendered_conf(rendered, out_path=paths.rendered_nginx)

    body = mf.build_manifest(
        **{
            **_valid_manifest_kwargs(tmp_path),
            "fixture_paths": bundle.as_manifest_paths(),
            "writer_token": "different-manifest-token",
        }
    )
    with pytest.raises(ValueError, match="writer_token_sha256"):
        lc._runtime_env_for_existing_manifest(manifest=body, paths=paths)


def test_cmd_up_restarts_existing_manifest_without_force(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path: Path,
) -> None:
    """A stopped stack with a valid manifest should be restartable without
    destroying fixtures or forcing a fresh network."""
    from tools.zenoctl_testnet_local import lifecycle as lc
    from tools.zenoctl_testnet_local import manifest as mf

    paths = mf.ManifestPaths.from_out_dir(tmp_path)
    body = mf.build_manifest(**_valid_manifest_kwargs(tmp_path))
    mf.save_manifest(body, paths.manifest_path)

    calls: list[str] = []

    class Engine:
        binary = "docker"

    def fake_compose_up(**kwargs):
        calls.append("compose_up")
        assert kwargs["project_name"] == body["compose_project"]
        assert kwargs["env"]["ZENO_LEDGER_WRITER_TOKEN"] == "writer-secret-abc"

    monkeypatch.setattr(lc.cm, "detect_engine", lambda engine: Engine())
    monkeypatch.setattr(
        lc,
        "_runtime_env_for_existing_manifest",
        lambda *, manifest, paths: {
            "ZENO_LEDGER_WRITER_TOKEN": "writer-secret-abc",
            "DEMO_API_TOKEN": "stdlib-secret-xyz",
            "UI_PORT": "18080",
            "CHAIN_ID": "zeno-ledger-localtest-v0",
            "NETWORK_ID": "zeno-ledger-localtest-v0",
            "RENDERED_NGINX_CONF_PATH": str(paths.rendered_nginx),
            "RENDERED_RUNTIME_CONFIG_PATH": str(paths.rendered_runtime_config),
            "FIXTURES_DIR": str(paths.fixtures_dir),
            "ORACLE_HOME_DIR": str(paths.oracle_home_dir),
            "HOST_UID": "1000",
            "HOST_GID": "1000",
            "TAU_DEX_TOKEN_OPERATOR_PUBKEY": "operator",
            "TAU_DEX_ORACLE_PUBKEY": "oracle",
            "TAU_DEX_ZUSD_ORACLE_PUBKEY": "zusd",
        },
    )
    monkeypatch.setattr(lc.cm, "compose_up", fake_compose_up)
    monkeypatch.setattr(lc, "_wait_for_base_services", lambda **kwargs: None)
    monkeypatch.setattr(lc, "_collect_lane_readiness", lambda **kwargs: {"ok": True, "lanes": {}})
    monkeypatch.setattr(lc, "_summary_text", lambda manifest: "")

    rc = lc.cmd_up(lc.UpOptions(out_dir=tmp_path))
    assert rc == 0
    assert calls == ["compose_up"]


def test_wait_for_lane_readiness_retries_until_ready(monkeypatch: pytest.MonkeyPatch) -> None:
    from tools.zenoctl_testnet_local import lifecycle as lc

    reports = [
        {"ok": False, "checks": {"spot": False}, "lanes": {}},
        {"ok": True, "checks": {"spot": True}, "lanes": {}},
    ]
    sleeps: list[float] = []

    monkeypatch.setattr(lc, "_collect_lane_readiness", lambda *, ui_base: reports.pop(0))
    monkeypatch.setattr(lc.time, "sleep", lambda seconds: sleeps.append(seconds))
    monkeypatch.setattr(lc.time, "monotonic", lambda: 0.0)

    result = lc._wait_for_lane_readiness(ui_base="http://127.0.0.1:18080", timeout_s=10)
    assert result["ok"] is True
    assert sleeps == [1.0]


def test_compose_overlay_zenodex_nginx_has_build_block() -> None:
    """zenodex:local must be buildable from the local-testnet overlay alone
    (so `compose up` doesn't fail with `image not found` on a fresh host)."""
    doc = _load_compose_overlay()
    nginx_svc = doc["services"]["zenodex-nginx"]
    assert "build" in nginx_svc, "zenodex-nginx must declare a build block"
    assert nginx_svc["build"].get("dockerfile") == "Dockerfile"
