from __future__ import annotations

from pathlib import Path

import pytest

from tools.zeno_ledger_multidocker_scenario import (
    _require_http_base_url,
    build_multidocker_plan_v0,
    validate_controller_config_v0,
)
from tools.zeno_ledger_multidocker_wes_disaster_search import (
    WES_SRC,
    build_multidocker_wes_candidates,
    check_multidocker_wes_candidate,
    run_multidocker_wes_disaster_search,
)


def test_multidocker_plan_rejects_machine_count_and_empty_ids() -> None:
    assert build_multidocker_plan_v0(machine_count=2, network_id="n", chain_id="c")["machine_count"] == 2

    with pytest.raises(ValueError, match="machine_count"):
        build_multidocker_plan_v0(machine_count=4, network_id="n", chain_id="c")
    with pytest.raises(ValueError, match="non-empty"):
        build_multidocker_plan_v0(machine_count=2, network_id="", chain_id="c")


def test_multidocker_url_validation_rejects_credentials_queries_fragments_and_non_http() -> None:
    assert _require_http_base_url("http://machine-a.local:8787", name="url") == "http://machine-a.local:8787"
    assert _require_http_base_url("https://example.test/base/", name="url") == "https://example.test/base"

    for bad in (
        "file:///etc/passwd",
        "ftp://example.test/bundle.tar.gz",
        "http://user:pass@example.test:8787",
        "http://example.test:8787/?x=1",
        "http://example.test:8787/#frag",
        "not-a-url",
    ):
        with pytest.raises(ValueError):
            _require_http_base_url(bad, name="url")


def test_multidocker_controller_config_enforces_role_cardinality_and_urls() -> None:
    valid = validate_controller_config_v0(
        machine_count=3,
        writer_url="http://node-a:8787",
        forwarder_url="http://node-b:8787",
        readonly_url="http://node-c:8787",
        node_data_dirs=[Path("/tmp/a"), Path("/tmp/b"), Path("/tmp/c")],
    )
    assert valid["ok"] is True

    missing = validate_controller_config_v0(
        machine_count=3,
        writer_url="http://node-a:8787",
        forwarder_url="http://node-b:8787",
        readonly_url=None,
        node_data_dirs=[Path("/tmp/a"), Path("/tmp/b"), Path("/tmp/c")],
    )
    assert missing["ok"] is False
    assert "readonly_url_required" in missing["errors"]

    extra = validate_controller_config_v0(
        machine_count=2,
        writer_url="http://node-a:8787",
        forwarder_url="http://node-b:8787",
        readonly_url="http://node-c:8787",
        node_data_dirs=[Path("/tmp/a"), Path("/tmp/b")],
    )
    assert extra["ok"] is False
    assert "readonly_url_not_allowed_for_two_machine_run" in extra["errors"]

    bad_url = validate_controller_config_v0(
        machine_count=2,
        writer_url="http://user:pass@node-a:8787",
        forwarder_url="http://node-b:8787",
        readonly_url=None,
        node_data_dirs=[Path("/tmp/a"), Path("/tmp/b")],
    )
    assert bad_url["ok"] is False
    assert "writer_url_invalid" in bad_url["errors"]


pytestmark_wes = pytest.mark.skipif(
    not WES_SRC.exists(),
    reason="external/WitnessEnergySearch is required for the WES disaster search",
)


@pytestmark_wes
def test_multidocker_wes_candidates_cover_disaster_families() -> None:
    candidates = build_multidocker_wes_candidates()
    families = {candidate.payload["family"] for candidate in candidates if isinstance(candidate.payload, dict)}

    assert {
        "plan",
        "node_hash",
        "url",
        "controller_config",
        "archive",
        "post_json",
        "auth_env",
    } <= families
    assert all(candidate.expected_checker == "zeno_ledger_multidocker_disaster_boundary_checker" for candidate in candidates)


@pytestmark_wes
def test_multidocker_wes_checker_rejects_invalid_boundary_controls() -> None:
    candidates = build_multidocker_wes_candidates()
    by_case = {
        candidate.payload["case_id"]: candidate
        for candidate in candidates
        if isinstance(candidate.payload, dict)
    }

    for case_id in (
        "url_file_scheme",
        "url_embedded_credentials",
        "controller_missing_readonly",
        "archive_path_escape",
        "archive_symlink",
        "post_request_too_large",
        "auth_env_unset",
    ):
        result = check_multidocker_wes_candidate(by_case[case_id])
        assert result.result.value == "near_miss"
        assert result.telemetry["accepted"] is False

    valid = check_multidocker_wes_candidate(by_case["controller_valid_three"])
    assert valid.result.value == "near_miss"
    assert valid.telemetry["accepted"] is True


@pytestmark_wes
def test_multidocker_wes_disaster_search_smoke(tmp_path: Path) -> None:
    report = run_multidocker_wes_disaster_search(
        budget=12,
        top_k=6,
        out_dir=tmp_path / "wes_multidocker_disaster",
    )

    assert report["schema"] == "zenodex/zeno_ledger/multidocker_wes_disaster_search/v0"
    assert report["ok"] is True
    assert report["safety"]["wes_ranks_only"] is True
    assert report["safety"]["deterministic_checker_authoritative"] is True
    assert report["safety"]["invalid_accept_count"] == 0
    assert report["summary"]["model_online_useful_at_k"] > 0
