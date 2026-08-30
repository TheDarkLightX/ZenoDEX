from __future__ import annotations

import json
import subprocess
import sys
import threading
from dataclasses import replace
from http.client import HTTPConnection
from pathlib import Path
from typing import Any
from urllib.error import HTTPError
from urllib.request import Request, urlopen

import pytest

from src.integration.local_route_quarantine import (
    QUARANTINED_ROUTE_ENVIRONMENT_ALIASES_V1,
    QUARANTINED_ROUTE_ENVIRONMENT_V1,
    CurrentLocalOperatorProfileBlockedV1,
    LocalRouteQuarantineRejectV1,
    quarantined_route_environment_rejections_v1,
)

REPO_ROOT = Path(__file__).resolve().parents[2]
RETIRED_ROUTE_VARIABLES = (
    "PERPS_WALLET_API_ENABLED",
    "ZUSD_TAU_WALLET_API_ENABLED",
    "ZUSD_MONETARY_WALLET_API_ENABLED",
)
RETIRED_ROUTE_ALIASES = (
    "PERPS_WALLET_API_ENABLE",
    "PERPS_WALLET_ENABLED",
    "PERPS_API_WALLET_ENABLED",
    "ZUSD_TAU_WALLET_API_ENABLE",
    "ZUSD_TAU_WALLET_ENABLED",
    "ZUSD_TAU_API_ENABLED",
    "ZUSD_MONETARY_WALLET_API_ENABLE",
    "ZUSD_MONETARY_WALLET_ENABLED",
    "ZUSD_MONETARY_API_ENABLED",
    "perps_wallet_api_enabled",
    "perps_wallet_api_enable",
    "perps_wallet_enabled",
    "perps_api_wallet_enabled",
    "zusd_tau_wallet_api_enabled",
    "zusd_tau_wallet_api_enable",
    "zusd_tau_wallet_enabled",
    "zusd_tau_api_enabled",
    "zusd_monetary_wallet_api_enabled",
    "zusd_monetary_wallet_api_enable",
    "zusd_monetary_wallet_enabled",
    "zusd_monetary_api_enabled",
)


@pytest.fixture(autouse=True)
def isolate_retired_tau_environment(monkeypatch: pytest.MonkeyPatch) -> None:
    assert QUARANTINED_ROUTE_ENVIRONMENT_V1 == RETIRED_ROUTE_VARIABLES
    assert QUARANTINED_ROUTE_ENVIRONMENT_ALIASES_V1 == RETIRED_ROUTE_ALIASES
    for name in RETIRED_ROUTE_VARIABLES + RETIRED_ROUTE_ALIASES:
        monkeypatch.delenv(name, raising=False)


@pytest.mark.parametrize("variable", RETIRED_ROUTE_VARIABLES)
@pytest.mark.parametrize("value", ("", "true", "TRUE", "1", "yes", " false ", "on"))
def test_given_retired_route_value_when_starting_twice_then_exact_reject_has_no_effect(
    monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture[str],
    variable: str,
    value: str,
) -> None:
    from src.integration import api_server

    monkeypatch.setenv(variable, value)
    events: list[str] = []
    monkeypatch.setattr(api_server, "_load_api_server_config", lambda: events.append("config"))
    monkeypatch.setattr(api_server, "_prewarm_api_modules", lambda: events.append("prewarm"))
    monkeypatch.setattr(api_server, "ThreadingHTTPServer", lambda *_args: events.append("server"))

    expected_reject = LocalRouteQuarantineRejectV1(
        code="QUARANTINED_ROUTE_ENV_VALUE",
        variable=variable,
    )
    assert quarantined_route_environment_rejections_v1({variable: value}) == (expected_reject,)
    assert api_server.main([]) == 2
    assert api_server.main([]) == 2
    assert events == []
    assert capsys.readouterr().out.splitlines() == [expected_reject.render()] * 2


@pytest.mark.parametrize("alias", RETIRED_ROUTE_ALIASES)
def test_given_retired_route_alias_when_starting_then_exact_reject_precedes_config(
    monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture[str],
    alias: str,
) -> None:
    from src.integration import api_server

    monkeypatch.setenv(alias, "false")
    events: list[str] = []
    monkeypatch.setattr(api_server, "_load_api_server_config", lambda: events.append("config"))
    monkeypatch.setattr(api_server, "_prewarm_api_modules", lambda: events.append("prewarm"))
    monkeypatch.setattr(api_server, "ThreadingHTTPServer", lambda *_args: events.append("server"))

    expected_reject = LocalRouteQuarantineRejectV1(
        code="QUARANTINED_ROUTE_ENV_ALIAS",
        variable=alias,
    )
    assert quarantined_route_environment_rejections_v1({alias: "false"}) == (expected_reject,)
    assert api_server.main([]) == 2
    assert events == []
    assert capsys.readouterr().out.splitlines() == [expected_reject.render()]


@pytest.mark.parametrize(
    ("field_name", "expected"),
    (
        (
            "perps_wallet_enabled",
            "Refusing to start: PERPS_WALLET_API_ENABLED depends on the retired Tau "
            "stream-8 application bridge; use a current-Tau ingress and ZenoLedger publication.",
        ),
        (
            "zusd_tau_wallet_enabled",
            "Refusing to start: ZUSD_TAU_WALLET_API_ENABLED requires Tau network-domain "
            "signature binding and durable submission reconciliation.",
        ),
        (
            "zusd_monetary_wallet_enabled",
            "Refusing to start: ZUSD_MONETARY_WALLET_API_ENABLED depends on the retired Tau "
            "stream-11 application bridge and lacks a verifier-owned execution clock.",
        ),
    ),
)
def test_given_parsed_retired_mode_when_starting_then_exact_backstop_rejects_without_effect(
    monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture[str],
    field_name: str,
    expected: str,
) -> None:
    from src.integration import api_server

    config = replace(api_server._load_api_server_config(), **{field_name: True})
    events: list[str] = []
    monkeypatch.setattr(api_server, "_load_api_server_config", lambda: config)
    monkeypatch.setattr(api_server, "_prewarm_api_modules", lambda: events.append("prewarm"))
    monkeypatch.setattr(api_server, "ThreadingHTTPServer", lambda *_args: events.append("server"))

    assert api_server.main([]) == 2
    assert events == []
    assert capsys.readouterr().out.splitlines() == [expected]


@pytest.mark.parametrize("allowed_value", (None, "false", "0"))
def test_given_allowed_retired_route_encoding_when_starting_then_reaches_server_path(
    monkeypatch: pytest.MonkeyPatch,
    allowed_value: str | None,
) -> None:
    from src.integration import api_server

    class ReachedServerConstruction(RuntimeError):
        pass

    for variable in RETIRED_ROUTE_VARIABLES:
        if allowed_value is None:
            monkeypatch.delenv(variable, raising=False)
        else:
            monkeypatch.setenv(variable, allowed_value)
    config = api_server._load_api_server_config()
    events: list[str] = []

    def load_config():
        events.append("config")
        return config

    def construct_server(*_args: object, **_kwargs: object) -> object:
        events.append("server")
        raise ReachedServerConstruction

    monkeypatch.setattr(api_server, "_load_api_server_config", load_config)
    monkeypatch.setattr(api_server, "_prewarm_api_modules", lambda: events.append("prewarm"))
    monkeypatch.setattr(api_server, "ThreadingHTTPServer", construct_server)

    with pytest.raises(ReachedServerConstruction):
        api_server.main([])
    assert events == ["config", "prewarm", "server"]


@pytest.mark.parametrize(
    ("current_name", "donor_name", "kwargs"),
    (
        (
            "_seed_api_state",
            "_seed_api_state_historical_donor",
            {
                "engine": object(),
                "project": "unused",
                "env": {},
                "roles": {},
                "chain_id": "unused",
                "tau_rpc_timeout_s": 1.0,
            },
        ),
        (
            "_materialize_release_native_collateral",
            "_materialize_release_native_collateral_historical_donor",
            {
                "engine": object(),
                "compose_project": "unused",
                "env": {},
                "roles": {},
                "amount_e8": 1,
            },
        ),
        (
            "_run_release_flow_smoke",
            "_run_release_flow_smoke_historical_donor",
            {
                "ui_base": "unused",
                "paths": object(),
                "manifest": {},
                "engine": object(),
                "compose_project": "unused",
                "env": {},
            },
        ),
        (
            "_run_cloudflare_quick_tunnel",
            "_run_cloudflare_quick_tunnel_historical_donor",
            {"opts": object(), "paths": object(), "manifest": {}},
        ),
        (
            "_zusd_transfer_payload",
            "_zusd_transfer_payload_historical_donor",
            {"ui_base": "unused", "roles": {}, "deadline": 0},
        ),
        (
            "_run_perps_wallet_cycle_smoke",
            "_run_perps_wallet_cycle_smoke_historical_donor",
            {
                "ui_base": "unused",
                "market_id": "unused",
                "roles": {},
                "deadline": 0,
                "zk_required": False,
            },
        ),
    ),
)
def test_given_all_lifecycle_historical_donors_when_called_then_refuse_before_effects(
    current_name: str,
    donor_name: str,
    kwargs: dict[str, object],
) -> None:
    from tools.zenoctl_testnet_local import lifecycle

    for name in (current_name, donor_name):
        operation = getattr(lifecycle, name)
        with pytest.raises(
            CurrentLocalOperatorProfileBlockedV1,
            match="current profile quarantines retired Tau value routes",
        ):
            operation(**kwargs)


def test_given_direct_asset_settlement_attachment_when_called_then_rejects_before_state_effects() -> None:
    from src.integration import api_server

    config = replace(
        api_server._load_api_server_config(),
        confidential_sealed_bid_asset_settlement_enabled=True,
    )
    server = type("InertServer", (), {})()

    with pytest.raises(RuntimeError, match="retired Tau value routes"):
        api_server._attach_api_server_state(server, config)
    assert vars(server) == {}


def test_given_direct_autotrader_attachment_when_called_then_rejects_before_state_effects() -> None:
    from src.integration import api_server

    config = replace(
        api_server._load_api_server_config(),
        perps_wallet_enabled=False,
        zusd_tau_wallet_enabled=False,
        zusd_monetary_wallet_enabled=False,
        autotrader_live_enabled=True,
        confidential_sealed_bid_asset_settlement_enabled=False,
    )
    server = type("InertServer", (), {})()

    with pytest.raises(RuntimeError, match="retired Tau value routes"):
        api_server._attach_api_server_state(server, config)
    assert vars(server) == {}


def test_given_persisted_retired_asset_success_when_loading_then_execution_claim_is_rejected() -> None:
    from src.integration.confidential_sealed_bid_api import SealedBidBatch

    persisted = {
        "batch_id": "batch",
        "units_for_sale": 1,
        "commit_epoch": 1,
        "reveal_deadline_epoch": 2,
        "default_bond_amount": 1,
        "phase": "settled",
        "commits": {},
        "reveals": {},
        "settlement": {},
        "bond_outcome": {},
        "asset_settlement": {"ok": True, "asset_settlement_executed": True},
    }

    with pytest.raises(ValueError, match="^retired_asset_settlement_state$"):
        SealedBidBatch.from_json(persisted)


def test_given_retired_asset_settlement_request_then_callback_channel_is_absent_and_state_untouched() -> None:
    import inspect

    from src.integration.confidential_sealed_bid_api import (
        handle_confidential_sealed_bid_request,
    )

    events: list[str] = []

    class InertTable:
        def settle(self, **_kwargs: object) -> None:
            events.append("settle")

    signature = inspect.signature(handle_confidential_sealed_bid_request)
    assert "asset_settlement_submitter" not in signature.parameters
    status, payload = handle_confidential_sealed_bid_request(
        "POST",
        "/api/confidential/sealed-bid/settle",
        b'{"batch_id":"batch","asset_settlement":{"mode":"local_ledger"}}',
        table=InertTable(),
    )

    assert status == 400
    assert payload == {
        "ok": False,
        "error": "unknown_fields",
        "fields": ["asset_settlement"],
    }
    assert events == []


def test_given_retired_http_paths_when_requested_then_modules_stay_unloaded_and_routes_are_absent() -> None:
    script = r'''
import http.client
import json
import sys
import threading

from src.integration import api_server

retired_modules = (
    "src.integration.perps_wallet_api",
    "src.integration.zusd_tau_wallet_api",
    "src.integration.zusd_monetary_wallet_api",
    "src.integration.autotrader_live_api",
)
assert all(name not in sys.modules for name in retired_modules)
httpd = api_server.ThreadingHTTPServer(("127.0.0.1", 0), api_server._Handler)
httpd.cors_origins = set()
httpd.rate_limiter = api_server.TokenBucketRateLimiter(rpm=0)
httpd.perps_api_enabled = True
httpd.perps_demo_api_unsafe_enabled = True
httpd.api_host = "127.0.0.1"
httpd.demo_api_token = ""
httpd.external_auth_enforced = True
httpd.autotrader_live_api_enabled = True
thread = threading.Thread(target=httpd.serve_forever, kwargs={"poll_interval": 0.01})
thread.start()
try:
    host, port = httpd.server_address[:2]
    for path in (
        "/api/perps/wallet/prepare",
        "/api/zusd/wallet/prepare",
        "/api/zusd/monetary/prepare",
        "/api/strategy/autotrader/prepare",
        "/api/strategy/autotrader/status",
    ):
        connection = http.client.HTTPConnection(host, port, timeout=2.0)
        connection.request("POST", path, body=b"{}", headers={"Content-Type": "application/json"})
        response = connection.getresponse()
        payload = json.loads(response.read().decode("utf-8"))
        connection.close()
        assert response.status == 404
        assert payload == {"error": "not_found", "ok": False}
    assert all(name not in sys.modules for name in retired_modules)
finally:
    httpd.shutdown()
    httpd.server_close()
    thread.join(timeout=2.0)
'''

    result = subprocess.run(
        [sys.executable, "-B", "-c", script],
        cwd=REPO_ROOT,
        check=False,
        capture_output=True,
        text=True,
        timeout=20,
    )

    assert result.returncode == 0, result.stderr


@pytest.mark.parametrize(
    ("module_name", "invoke"),
    (
        (
            "tools.zeno_ledger_make_feature_lane",
            lambda module, retired: module.build_feature_lane_manifest_v0(
                out_dir=Path("unread-out"),
                profile_path=Path("unread-profile"),
                genesis_snapshot_path=None,
                tau_app_state_path=retired,
                zusd_state_path=None,
                perp_state_path=None,
                oracle_state_path=None,
                oracle_reporter_state_path=None,
                upba_state_path=None,
                proof_mining_state_path=None,
                autotrader_state_path=None,
                confidential_state_path=None,
                tau_chain_balances_path=None,
                tau_chain_id=None,
                tau_enable_faucet=False,
                body_paths=[Path("unread-body")],
                module_versions_digest="unread",
                allow_missing_settlement=False,
                disable_intent_signatures=False,
            ),
        ),
        (
            "tools.zeno_ledger_run_local",
            lambda module, retired: module.build_local_block_v0(
                body_path=Path("unread-body"),
                out_dir=Path("unwritten-out"),
                time_ms=0,
                tau_app_state_path=retired,
                sequencer_set_hash="unread",
                data_availability_root="unread",
                proof_journal_hash="unread",
                config_digest="unread",
                module_versions_digest="unread",
                signature_set_root="unread",
            ),
        ),
    ),
)
def test_given_retired_tau_state_selector_when_called_then_rejects_before_file_effects(
    monkeypatch: pytest.MonkeyPatch,
    module_name: str,
    invoke,
) -> None:
    module = __import__(module_name, fromlist=["unused"])
    events: list[str] = []
    monkeypatch.setattr(Path, "read_text", lambda *_args, **_kwargs: events.append("read"))
    monkeypatch.setattr(Path, "write_text", lambda *_args, **_kwargs: events.append("write"))
    monkeypatch.setattr(Path, "mkdir", lambda *_args, **_kwargs: events.append("mkdir"))
    monkeypatch.setattr(subprocess, "run", lambda *_args, **_kwargs: events.append("subprocess"))

    with pytest.raises(ValueError, match="^RETIRED_TAU_APP_STATE_SELECTOR$"):
        invoke(module, Path("retired-tau-app-state"))
    assert events == []


@pytest.mark.parametrize(
    "command",
    (
        ["python3", "tools/zeno_ledger_run_local.py", "--tau-app-state=retired.json"],
        ["sh", "-c", "python tools/zeno_ledger_run_local.py --tau-app-state retired.json"],
        ["python3", "-m", "tools.zeno_ledger_run_local", "--tau-chain-id", "retired-chain"],
        ["python3", "tools/zeno_ledger_make_feature_lane.py", "--tau-chain-balances", "retired.json"],
        ["python3", "tools/zeno_ledger_make_feature_lane.py", "--clock-policy-schedule", "retired.json"],
    ),
)
def test_given_manifest_embeds_retired_tau_state_selector_then_no_command_or_report_runs(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    command: list[str],
) -> None:
    from tools import zeno_ledger_run_manifest as runner

    manifest_path = tmp_path / "manifest.json"
    manifest_path.write_text(
        json.dumps(
            {
                "schema": runner.MANIFEST_SCHEMA,
                "run_commands": [command],
                "verify_command": ["python3", "verify.py"],
            }
        ),
        encoding="utf-8",
    )
    events: list[str] = []
    monkeypatch.setattr(runner, "_run_command", lambda *_args, **_kwargs: events.append("run"))
    monkeypatch.setattr(runner, "_write_json", lambda *_args, **_kwargs: events.append("write"))

    with pytest.raises(ValueError, match="^RETIRED_TAU_APP_STATE_SELECTOR$"):
        runner.run_manifest_v0(manifest_path=manifest_path, cwd=tmp_path)
    assert events == []


@pytest.mark.parametrize(
    "command",
    (
        (
            "python3",
            "tools/check_current_tau_compatibility_v1.py",
            "--tau-testnet-repo",
            "tau-testnet",
            "--tau-lang-repo",
            "tau-lang",
        ),
        ("python3", "tools/check_tau_formal_contract_artifacts.py", "--tau-bin", "tau"),
        (
            "python3",
            "tools/zeno_ledger_export_tau_packet.py",
            "--tau-network-id",
            "network",
            "--tau-adapter-ref",
            "adapter",
        ),
    ),
)
def test_given_current_tau_command_when_manifest_is_checked_then_retirement_guard_allows_it(
    command: tuple[str, ...],
) -> None:
    from tools import zeno_ledger_run_manifest as runner

    runner._reject_retired_tau_app_state_commands((command,))


@pytest.mark.parametrize(
    ("pre_state", "operations"),
    (
        ({"schema": "zenodex/tau_app_state/v1", "dex_state": {}}, {}),
        ({"schema": "zenodex/dex_snapshot/v1"}, {"10": []}),
        ({"schema": "zenodex/dex_snapshot/v1"}, {"7": {"mint": []}}),
    ),
)
def test_given_public_node_retired_tau_state_when_appending_then_rejects_before_mutation(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    pre_state: dict[str, object],
    operations: dict[str, object],
) -> None:
    from tools import zeno_ledger_node as node

    bundle_root = tmp_path / "bundle"
    pre_state_path = tmp_path / "pre-state.json"
    (tmp_path / "writer.lock").write_bytes(b"")
    events: list[str] = []
    monkeypatch.setattr(
        node,
        "load_node_status_v0",
        lambda _data_dir: {"bundle_root": str(bundle_root)},
    )
    monkeypatch.setattr(
        node,
        "_read_public_manifest",
        lambda _bundle_root: {"sequencer_id": "sequencer", "chain_id": "chain"},
    )
    monkeypatch.setattr(
        node,
        "_live_base_paths",
        lambda **_kwargs: {
            "latest_height": 0,
            "pre_snapshot_path": str(pre_state_path),
            "prev_header_path": str(tmp_path / "prev-header.json"),
        },
    )

    def load_json(path: Path) -> dict[str, object]:
        if path.name == "manifest.json":
            return {"sequencer_set_hash": "unused", "config_digest": "unused", "module_versions_digest": "unused"}
        return pre_state

    monkeypatch.setattr(node, "_load_json_object", load_json)
    monkeypatch.setattr(node, "_write_json", lambda *_args, **_kwargs: events.append("write"))
    monkeypatch.setattr(
        node,
        "_attach_tokenomics_buyback_burn_event_v0",
        lambda **_kwargs: events.append("tokenomics"),
    )
    monkeypatch.setattr(
        node,
        "build_local_block_v0",
        lambda **_kwargs: events.append("build"),
    )

    with pytest.raises(ValueError, match="^RETIRED_TAU_APP_STATE_SELECTOR$"):
        node.append_dex_transaction_v0(
            data_dir=tmp_path,
            tx={"operations": operations},
            time_ms=0,
            min_lp_position_age_seconds=0,
            lp_duration_risk_policy=None,
        )

    assert events == []
    assert not (tmp_path / "live_bodies").exists()
    assert not (tmp_path / "live_chain_balances").exists()


@pytest.mark.parametrize(
    "append_kind",
    ("dex", "faucet", "reward", "autogovnext", "pull"),
)
@pytest.mark.parametrize(
    "retired_wrapper",
    (
        {"schema": "zenodex/tau_app_state/v1", "dex_state": {}},
        {"schema": "zenodex/tau_app_state/v1"},
        {"schema": "zenodex/tau_app_state/v1", "dex_state": None},
        {"schema": "zenodex/tau_app_state/v1", "dex_state": []},
    ),
)
def test_given_persisted_tau_wrapper_when_any_public_node_writer_runs_then_exact_reject_has_no_authoritative_effect(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    append_kind: str,
    retired_wrapper: dict[str, object],
) -> None:
    from src.integration.zeno_ledger_v0 import (
        build_header_v0,
        canonical_header_hash_v0,
        compute_app_hash_v0,
    )
    from tools import zeno_ledger_node as node

    data_dir = tmp_path / "node"
    bundle_root = tmp_path / "bundle"
    bootstrap_path = bundle_root / "bootstrap" / "manifest.json"
    header_path = data_dir / "live_ledger" / "headers" / "1.json"
    snapshot_path = data_dir / "live_ledger" / "snapshots" / "1.json"
    for path in (bootstrap_path, header_path, snapshot_path):
        path.parent.mkdir(parents=True, exist_ok=True)

    chain_id = "retired-wrapper-node-testnet"
    app_hash = compute_app_hash_v0(
        {
            "chain_id": chain_id,
            "height": 1,
            "post_state_root": node.ZERO_ROOT,
            "evidence_root": node.ZERO_ROOT,
            "config_digest": node.ZERO_ROOT,
            "module_versions_digest": node.ZERO_ROOT,
        }
    )
    header = build_header_v0(
        chain_id=chain_id,
        height=1,
        time_ms=1,
        prev_header_hash=node.ZERO_ROOT,
        sequencer_set_hash=node.ZERO_ROOT,
        ingress_root=node.ZERO_ROOT,
        tx_root=node.ZERO_ROOT,
        pre_state_root=node.ZERO_ROOT,
        post_state_root=node.ZERO_ROOT,
        app_hash=app_hash,
        evidence_root=node.ZERO_ROOT,
        body_root=node.ZERO_ROOT,
        data_availability_root=node.ZERO_ROOT,
        proof_journal_hash=node.ZERO_ROOT,
        config_digest=node.ZERO_ROOT,
        module_versions_digest=node.ZERO_ROOT,
        signature_set_root=node.ZERO_ROOT,
    )
    bootstrap_path.write_text(
        json.dumps(
            {
                "sequencer_set_hash": node.ZERO_ROOT,
                "config_digest": node.ZERO_ROOT,
                "module_versions_digest": node.ZERO_ROOT,
            },
            sort_keys=True,
        ),
        encoding="utf-8",
    )
    header_path.write_text(json.dumps(header, sort_keys=True), encoding="utf-8")
    snapshot_path.write_text(json.dumps(retired_wrapper), encoding="utf-8")
    (data_dir / "writer.lock").write_bytes(b"")
    (data_dir / "live_state.json").write_text(
        json.dumps(
            {
                "schema": node.NODE_LIVE_STATE_SCHEMA,
                "latest_height": 1,
                "latest_header_path": str(header_path),
                "latest_snapshot_path": str(snapshot_path),
                "latest_header_hash": canonical_header_hash_v0(header),
                "latest_app_hash": app_hash,
            },
            sort_keys=True,
        ),
        encoding="utf-8",
    )
    node_status = {
        "bundle_root": str(bundle_root),
        "chain_id": chain_id,
        "latest_height": 0,
        "last_header_hash": node.ZERO_ROOT,
        "last_app_hash": node.ZERO_ROOT,
    }
    monkeypatch.setattr(node, "load_node_status_v0", lambda _data_dir: node_status)
    monkeypatch.setattr(
        node,
        "_read_public_manifest",
        lambda _bundle_root: {"chain_id": chain_id, "sequencer_id": "sequencer"},
    )
    peer_events: list[str] = []
    monkeypatch.setattr(
        node,
        "check_peer_status_v0",
        lambda **_kwargs: peer_events.append("peer"),
    )

    invocations = {
        "dex": lambda: node.append_dex_transaction_v0(
            data_dir=data_dir,
            tx={"operations": {}},
            time_ms=2,
            min_lp_position_age_seconds=0,
            lp_duration_risk_policy=None,
        ),
        "faucet": lambda: node.append_testnet_faucet_v0(
            data_dir=data_dir,
            to_pubkey="0x" + "11" * 48,
            asset="asset",
            amount=1,
            time_ms=2,
            tx_id="retired-wrapper-faucet",
        ),
        "reward": lambda: node.append_tokenomics_reward_claim_v0(
            data_dir=data_dir,
            payload={},
            time_ms=2,
        ),
        "autogovnext": lambda: node.append_autogovnext_admission_v1(
            data_dir=data_dir,
            request={},
            time_ms=2,
        ),
        "pull": lambda: node.pull_live_from_peer_v0(
            data_dir=data_dir,
            peer_url="http://peer.invalid",
            min_lp_position_age_seconds=0,
            lp_duration_risk_policy=None,
        ),
    }
    before = {
        path.relative_to(tmp_path): path.read_bytes()
        for path in sorted(tmp_path.rglob("*"))
        if path.is_file()
    }

    if append_kind == "dex":
        with pytest.raises(ValueError, match="^RETIRED_TAU_APP_STATE_SELECTOR$"):
            node.make_node_http_server_v0(data_dir=data_dir, host="127.0.0.1", port=0)

    with pytest.raises(ValueError, match="^RETIRED_TAU_APP_STATE_SELECTOR$"):
        invocations[append_kind]()

    after = {
        path.relative_to(tmp_path): path.read_bytes()
        for path in sorted(tmp_path.rglob("*"))
        if path.is_file()
    }
    assert after == before
    assert peer_events == []


@pytest.mark.parametrize(
    "retired_wrapper",
    (
        {"schema": "zenodex/tau_app_state/v1", "dex_state": {}},
        {"schema": "zenodex/tau_app_state/v1"},
        {"schema": "zenodex/tau_app_state/v1", "dex_state": None},
        {"schema": "zenodex/tau_app_state/v1", "dex_state": []},
    ),
)
def test_given_tau_wrapper_bootstrap_when_node_starts_then_reject_precedes_local_artifacts(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    retired_wrapper: dict[str, object],
) -> None:
    from tools import zeno_ledger_node as node

    bundle_root = tmp_path / "bundle"
    manifest_path = bundle_root / "bootstrap" / "manifest.json"
    header_path = bundle_root / "bootstrap" / "ledger" / "headers" / "0.json"
    snapshot_path = bundle_root / "bootstrap" / "ledger" / "snapshots" / "0.json"
    header_path.parent.mkdir(parents=True)
    snapshot_path.parent.mkdir(parents=True)
    header_path.write_text("{}", encoding="utf-8")
    manifest_path.write_text("{}", encoding="utf-8")
    snapshot_path.write_text(json.dumps(retired_wrapper), encoding="utf-8")
    monkeypatch.setattr(
        node,
        "_read_public_manifest",
        lambda _bundle_root: {"bootstrap_manifest_path": "bootstrap/manifest.json"},
    )
    events: list[str] = []
    monkeypatch.setattr(
        node,
        "run_operator_rehearsal_v0",
        lambda **_kwargs: events.append("operator"),
    )
    data_dir = tmp_path / "unwritten-node"

    with pytest.raises(ValueError, match="^RETIRED_TAU_APP_STATE_SELECTOR$"):
        node.run_node_once_v0(
            bundle_root=bundle_root,
            node_id="retired-wrapper-node",
            data_dir=data_dir,
        )

    assert events == []
    assert not data_dir.exists()


@pytest.mark.parametrize(
    "retired_wrapper",
    (
        {"schema": "zenodex/tau_app_state/v1", "dex_state": {}},
        {"schema": "zenodex/tau_app_state/v1"},
        {"schema": "zenodex/tau_app_state/v1", "dex_state": None},
        {"schema": "zenodex/tau_app_state/v1", "dex_state": []},
    ),
)
def test_given_persisted_status_and_tau_bootstrap_when_http_node_restarts_then_exact_reject_has_no_effect(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    retired_wrapper: dict[str, object],
) -> None:
    from tools import zeno_ledger_node as node

    data_dir = tmp_path / "node"
    bundle_root = tmp_path / "bundle"
    manifest_path = bundle_root / "bootstrap" / "manifest.json"
    header_path = bundle_root / "bootstrap" / "ledger" / "headers" / "0.json"
    snapshot_path = bundle_root / "bootstrap" / "ledger" / "snapshots" / "0.json"
    data_dir.mkdir()
    header_path.parent.mkdir(parents=True)
    snapshot_path.parent.mkdir(parents=True)
    manifest_path.write_text("{}", encoding="utf-8")
    header_path.write_text("{}", encoding="utf-8")
    snapshot_path.write_text(json.dumps(retired_wrapper), encoding="utf-8")
    status: dict[str, object] = {
        "schema": node.NODE_STATUS_SCHEMA,
        "bundle_root": str(bundle_root),
    }
    status["node_status_hash"] = node._node_status_hash(status)
    (data_dir / "node_status.json").write_text(
        json.dumps(status, sort_keys=True),
        encoding="utf-8",
    )
    monkeypatch.setattr(
        node,
        "_read_public_manifest",
        lambda _bundle_root: {"bootstrap_manifest_path": "bootstrap/manifest.json"},
    )
    server_events: list[str] = []
    monkeypatch.setattr(
        node,
        "ThreadingHTTPServer",
        lambda *_args, **_kwargs: server_events.append("server"),
    )
    before = {
        path.relative_to(tmp_path): path.read_bytes()
        for path in sorted(tmp_path.rglob("*"))
        if path.is_file()
    }

    with pytest.raises(ValueError, match="^RETIRED_TAU_APP_STATE_SELECTOR$"):
        node.make_node_http_server_v0(data_dir=data_dir, host="127.0.0.1", port=0)

    after = {
        path.relative_to(tmp_path): path.read_bytes()
        for path in sorted(tmp_path.rglob("*"))
        if path.is_file()
    }
    assert after == before
    assert server_events == []


@pytest.mark.parametrize("retired_stream", ("7", "10"))
def test_given_retired_stream_with_existing_tx_id_when_single_appends_then_reject_precedes_idempotence_lookup(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    retired_stream: str,
) -> None:
    from tools import zeno_ledger_node as node

    events: list[str] = []
    monkeypatch.setattr(
        node,
        "load_node_status_v0",
        lambda _data_dir: events.append("status"),
    )
    monkeypatch.setattr(
        node,
        "_existing_append_report_for_tx_id_v0",
        lambda **_kwargs: events.append("idempotence"),
    )

    with pytest.raises(ValueError, match="^RETIRED_TAU_APP_STATE_SELECTOR$"):
        node._append_dex_transaction_v0_locked(
            data_dir=tmp_path / "unwritten-node",
            tx={"tx_id": "historical-id", "operations": {retired_stream: {}}},
            time_ms=0,
            min_lp_position_age_seconds=0,
            lp_duration_risk_policy=None,
        )

    assert events == []
    assert not (tmp_path / "unwritten-node").exists()


@pytest.mark.parametrize("endpoint", ("tx", "tx/batch"))
@pytest.mark.parametrize("retired_stream", ("7", "10"))
def test_given_retired_stream_when_follower_http_ingress_receives_it_then_reject_precedes_forwarding(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    endpoint: str,
    retired_stream: str,
) -> None:
    from tools import zeno_ledger_node as node

    forwarded: list[str] = []
    monkeypatch.setattr(
        node,
        "_post_json_url",
        lambda *_args, **_kwargs: forwarded.append("forward"),
    )
    data_dir = tmp_path / "unwritten-node"
    server = node.make_node_http_server_v0(
        data_dir=data_dir,
        host="127.0.0.1",
        port=0,
        enable_testnet_intake=True,
        allow_unauthenticated_testnet_writes=True,
        submit_peer_url="http://peer.invalid",
    )
    thread = threading.Thread(target=server.serve_forever, daemon=True)
    thread.start()
    tx = {"tx_id": "historical-http", "operations": {retired_stream: {}}}
    request_payload: dict[str, object] = {"tx": tx} if endpoint == "tx" else {"txs": [tx]}
    request = Request(
        f"http://127.0.0.1:{server.server_port}/{endpoint}",
        data=json.dumps(request_payload).encode("utf-8"),
        headers={"Content-Type": "application/json"},
        method="POST",
    )
    try:
        with pytest.raises(HTTPError) as exc_info:
            urlopen(request, timeout=5)  # noqa: S310 - isolated loopback server
        assert exc_info.value.code == 400
        response = json.loads(exc_info.value.read().decode("utf-8"))
        assert response == {"error": "RETIRED_TAU_APP_STATE_SELECTOR", "ok": False}
    finally:
        server.shutdown()
        thread.join(timeout=5)
        server.server_close()

    assert forwarded == []
    assert not data_dir.exists()


@pytest.mark.parametrize("retired_stream", ("7", "10"))
def test_given_retired_stream_when_batch_appends_then_reject_precedes_node_reads(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    retired_stream: str,
) -> None:
    from tools import zeno_ledger_node as node

    events: list[str] = []
    monkeypatch.setattr(
        node,
        "load_node_status_v0",
        lambda _data_dir: events.append("status"),
    )

    with pytest.raises(ValueError, match="^RETIRED_TAU_APP_STATE_SELECTOR$"):
        node._append_dex_transactions_v0_locked(
            data_dir=tmp_path / "unwritten-node",
            txs=({"tx_id": "retired", "operations": {retired_stream: {}}},),
            time_ms=0,
            min_lp_position_age_seconds=0,
            lp_duration_risk_policy=None,
        )

    assert events == []
    assert not (tmp_path / "unwritten-node").exists()


@pytest.mark.parametrize("retired_stream", ("7", "10"))
def test_given_peer_retired_stream_when_pulling_then_reject_precedes_header_and_disk(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    retired_stream: str,
) -> None:
    from tools import zeno_ledger_node as node

    data_dir = tmp_path / "unwritten-node"
    bundle_root = tmp_path / "bundle"
    events: list[str] = []
    monkeypatch.setattr(
        node,
        "check_peer_status_v0",
        lambda **_kwargs: {"ok": True},
    )
    monkeypatch.setattr(
        node,
        "load_node_status_v0",
        lambda _data_dir: {"bundle_root": str(bundle_root)},
    )
    monkeypatch.setattr(node, "_read_public_manifest", lambda _root: {})
    monkeypatch.setattr(node, "_load_json_object", lambda _path: {})
    monkeypatch.setattr(
        node,
        "_live_base_paths",
        lambda **_kwargs: {
            "latest_height": 0,
            "prev_header_path": str(tmp_path / "prev-header.json"),
            "pre_snapshot_path": str(tmp_path / "pre-snapshot.json"),
        },
    )

    def fetch(url: str) -> dict[str, object]:
        if url.endswith("/live"):
            events.append("live")
            return {"ok": True, "live": True, "state": {"latest_height": 1}}
        if url.endswith("/live/body/1"):
            events.append("body")
            return {
                "transactions": [
                    {"tx_id": "retired-peer", "operations": {retired_stream: {}}}
                ]
            }
        events.append("header")
        return {}

    monkeypatch.setattr(node, "_fetch_json_url", fetch)

    with pytest.raises(ValueError, match="^RETIRED_TAU_APP_STATE_SELECTOR$"):
        node._pull_live_from_peer_v0_locked(
            data_dir=data_dir,
            peer_url="http://peer.invalid",
            min_lp_position_age_seconds=0,
            lp_duration_risk_policy=None,
        )

    assert events == ["live", "body"]
    assert not data_dir.exists()


def test_given_retired_tau_signing_command_then_exact_reject_precedes_vault_read(
    monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture[str],
) -> None:
    from tools import zenodex_local_signer as signer

    events: list[str] = []
    monkeypatch.setattr(
        signer,
        "read_local_signer_vault",
        lambda _path: events.append("vault-read"),
    )

    result = signer.main(
        [
            "sign-tau-transaction-payload",
            "--vault",
            "unread-vault",
            "--chain-id",
            "retired-chain",
            "--payload-json",
            "{}",
        ]
    )

    assert result == 1
    assert events == []
    assert capsys.readouterr().err.strip() == (
        "zenodex-local-signer: RETIRED_TAU_TRANSACTION_SIGNING_ROUTE"
    )


def test_given_direct_retired_tau_signing_call_then_typed_reject_precedes_vault_access() -> None:
    from src.integration.zenodex_local_signer import (
        LocalSignerVault,
        RetiredTauTransactionSigningRouteError,
    )

    vault = object.__new__(LocalSignerVault)

    with pytest.raises(
        RetiredTauTransactionSigningRouteError,
        match="^RETIRED_TAU_TRANSACTION_SIGNING_ROUTE$",
    ):
        vault.sign_tau_transaction_payload(
            passphrase="unread-passphrase",
            payload={"sender_pubkey": "unread-pubkey"},
            chain_id="unread-chain",
        )


@pytest.mark.parametrize(
    ("body", "declared_length"),
    (
        pytest.param(b"{", 1, id="malformed-json"),
        pytest.param(None, 1_000_001, id="oversized-body-withheld"),
    ),
)
@pytest.mark.parametrize("query", ("", "?x=1"), ids=("exact-path", "query-variant"))
def test_given_retired_tau_http_signing_route_then_http_410_precedes_signer_access(
    body: bytes | None,
    declared_length: int,
    query: str,
) -> None:
    from tools import zenodex_local_signer as signer

    sensitive_events: list[str] = []
    server_errors: list[str] = []

    class RefusalOnlyServer(signer.ThreadingHTTPServer):
        def __getattribute__(self, name: str) -> Any:
            if name in {"vault", "passphrase", "chain_id"}:
                sensitive_events.append(f"access:{name}")
                raise AssertionError(f"retired HTTP route accessed server.{name}")
            return super().__getattribute__(name)

        def handle_error(self, request: Any, client_address: Any) -> None:
            server_errors.append(f"handler-error:{client_address!r}")

    server = RefusalOnlyServer(
        ("127.0.0.1", 0),
        signer._LocalSignerHttpHandler,
    )
    server.allowed_origins = {"http://127.0.0.1:5173"}
    thread = threading.Thread(target=server.serve_forever, daemon=True)
    thread.start()
    connection = HTTPConnection("127.0.0.1", server.server_port, timeout=5)
    try:
        connection.putrequest(
            "POST",
            f"/sign-tau-transaction-payload{query}",
        )
        connection.putheader("Content-Type", "application/json")
        connection.putheader("Content-Length", str(declared_length))
        connection.putheader("Origin", "http://127.0.0.1:5173")
        connection.endheaders()
        if body is not None:
            connection.send(body)
        response = connection.getresponse()
        assert response.status == 410
        assert json.loads(response.read().decode("utf-8")) == {
            "error": "RETIRED_TAU_TRANSACTION_SIGNING_ROUTE",
            "ok": False,
        }
    finally:
        connection.close()
        server.shutdown()
        thread.join(timeout=5)
        server.server_close()
    assert sensitive_events == []
    assert server_errors == []


@pytest.mark.parametrize(
    "selector",
    (
        ("--tau-chain-balances", "unread-balances"),
        ("--tau-chain-id", "retired-chain"),
        ("--tau-enable-faucet",),
    ),
)
def test_given_feature_lane_tau_companion_selector_then_rejects_before_paths(
    tmp_path: Path,
    selector: tuple[str, ...],
) -> None:
    result = subprocess.run(
        [
            sys.executable,
            "-B",
            str(REPO_ROOT / "tools/zeno_ledger_make_feature_lane.py"),
            "--out-dir",
            "unwritten-out",
            "--profile",
            "unread-profile",
            "--body",
            "unread-body",
            "--zusd-state",
            "unread-zusd-state",
            *selector,
        ],
        cwd=tmp_path,
        check=False,
        capture_output=True,
        text=True,
        timeout=20,
    )

    assert result.returncode == 1
    assert json.loads(result.stdout)["errors"] == [
        "RETIRED_TAU_BRIDGE_COMPANION_SELECTOR"
    ]
    assert not (tmp_path / "unwritten-out").exists()


@pytest.mark.parametrize(
    "selector",
    (
        ("--tau-chain-balances", "unread-balances"),
        ("--tau-chain-id", "retired-chain"),
        ("--tau-enable-faucet",),
        ("--clock-policy-schedule", "unread-clock-policy"),
    ),
)
def test_given_local_block_tau_companion_selector_then_rejects_before_paths(
    tmp_path: Path,
    selector: tuple[str, ...],
) -> None:
    result = subprocess.run(
        [
            sys.executable,
            "-B",
            str(REPO_ROOT / "tools/zeno_ledger_run_local.py"),
            "--body",
            "unread-body",
            "--out-dir",
            "unwritten-out",
            "--time-ms",
            "0",
            "--sequencer-set-hash",
            "unread",
            "--config-digest",
            "unread",
            "--module-versions-digest",
            "unread",
            *selector,
        ],
        cwd=tmp_path,
        check=False,
        capture_output=True,
        text=True,
        timeout=20,
    )

    assert result.returncode == 1
    assert json.loads(result.stdout)["errors"] == [
        "RETIRED_TAU_BRIDGE_COMPANION_SELECTOR"
    ]
    assert not (tmp_path / "unwritten-out").exists()


@pytest.mark.parametrize(
    "command",
    (
        (
            "tools/zeno_ledger_make_feature_lane.py",
            "--out-dir",
            "unwritten-out",
            "--profile",
            "unread-profile",
            "--body",
            "unread-body",
            "--tau-app-state",
            "unread-tau-state",
        ),
        (
            "tools/zeno_ledger_run_local.py",
            "--body",
            "unread-body",
            "--out-dir",
            "unwritten-out",
            "--time-ms",
            "0",
            "--tau-app-state=unread-tau-state",
            "--sequencer-set-hash",
            "unread",
            "--config-digest",
            "unread",
            "--module-versions-digest",
            "unread",
        ),
    ),
)
def test_given_retired_tau_state_cli_selector_then_exact_json_rejects_before_paths(
    tmp_path: Path,
    command: tuple[str, ...],
) -> None:
    result = subprocess.run(
        [sys.executable, "-B", str(REPO_ROOT / command[0]), *command[1:]],
        cwd=tmp_path,
        check=False,
        capture_output=True,
        text=True,
        timeout=20,
    )

    assert result.returncode == 1
    assert json.loads(result.stdout) == {
        "errors": ["RETIRED_TAU_APP_STATE_SELECTOR"],
        "ok": False,
        "schema": (
            "zenodex.zeno_ledger.make_feature_lane_report.v0"
            if "make_feature_lane" in command[0]
            else "zenodex.zeno_ledger.run_local_report.v0"
        ),
        "status": "rejected",
    }
    assert not (tmp_path / "unwritten-out").exists()
