from pathlib import Path

from tools.zeno_ledger_public_tunnel_host import (
    build_cloudflared_command_v0,
    build_public_tunnel_ready_report_v0,
    is_writer_proxy_path_v0,
    parse_cloudflared_quick_tunnel_url_v0,
)


def test_public_tunnel_gateway_routes_writer_paths() -> None:
    assert is_writer_proxy_path_v0("/health")
    assert is_writer_proxy_path_v0("/status?verbose=1")
    assert is_writer_proxy_path_v0("/network")
    assert is_writer_proxy_path_v0("/live/header/7")
    assert is_writer_proxy_path_v0("/live/body/7")
    assert is_writer_proxy_path_v0("/tx")
    assert is_writer_proxy_path_v0("/faucet")

    assert not is_writer_proxy_path_v0("/public_network_config.json")
    assert not is_writer_proxy_path_v0("/manifest.json")
    assert not is_writer_proxy_path_v0("/bootstrap/feature_suite.json")


def test_cloudflared_quick_tunnel_url_parser() -> None:
    assert (
        parse_cloudflared_quick_tunnel_url_v0(
            "2026-06-01 INF +--------------------------------------------------------------------------------------------+"
        )
        is None
    )
    assert (
        parse_cloudflared_quick_tunnel_url_v0(
            "2026-06-01 INF |  https://seed-alpha-123.trycloudflare.com                                      |"
        )
        == "https://seed-alpha-123.trycloudflare.com"
    )


def test_cloudflared_command_modes() -> None:
    assert build_cloudflared_command_v0(
        local_url="http://127.0.0.1:1234",
        mode="docker-host",
        image="cloudflare/cloudflared:latest",
    ) == [
        "docker",
        "run",
        "--rm",
        "--network",
        "host",
        "cloudflare/cloudflared:latest",
        "tunnel",
        "--no-autoupdate",
        "--url",
        "http://127.0.0.1:1234",
    ]
    assert build_cloudflared_command_v0(
        local_url="http://127.0.0.1:1234",
        mode="local-binary",
        image="ignored",
    ) == ["cloudflared", "tunnel", "--no-autoupdate", "--url", "http://127.0.0.1:1234"]


def test_public_tunnel_ready_report_uses_tunnel_url_for_config_and_writer() -> None:
    report = build_public_tunnel_ready_report_v0(
        out_dir=Path("/tmp/out"),
        data_dir=Path("/tmp/data"),
        tunnel_url="https://seed-alpha-123.trycloudflare.com",
        gateway_port=3333,
        writer_port=4444,
        network_config_path=Path("/tmp/out/public_network_config.json"),
        build_report={"ok": True, "covered_feature_count": 10},
        node_report={"ok": True, "latest_height": 6},
        network_config={
            "network_id": "net",
            "chain_id": "chain",
            "network_config_hash": "0xabc",
        },
        machine_b_token_symbol="tZENO",
        write_auth_token_path=Path("/tmp/out/secrets/token"),
        machine_b_peer_auth_token_file="/tmp/peer.token",
        cloudflared_command=["cloudflared", "tunnel"],
    )

    assert report["ok"] is True
    assert report["gateway_url"] == "https://seed-alpha-123.trycloudflare.com"
    assert report["config_url"] == "https://seed-alpha-123.trycloudflare.com/public_network_config.json"
    assert report["writer_url"] == "https://seed-alpha-123.trycloudflare.com"
    assert report["mirror_base_url"] == "https://seed-alpha-123.trycloudflare.com/"
    assert report["write_auth_required"] is True
    assert report["machine_b_acceptance_command"][3] == (
        "https://seed-alpha-123.trycloudflare.com/public_network_config.json"
    )
