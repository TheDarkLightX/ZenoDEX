from __future__ import annotations

import argparse
import contextlib
import hashlib
import json
import socket
import subprocess
import sys
import time
import urllib.error
import urllib.parse
import urllib.request
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[2]
CLI = ROOT / "tools" / "zenodex_oracle.py"


def _run(*args: str) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        [sys.executable, str(CLI), *args],
        cwd=ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )


def _run_json_ok(*args: str) -> dict[str, object]:
    proc = _run(*args)
    assert proc.returncode == 0, proc.stderr
    payload = json.loads(proc.stdout)
    assert isinstance(payload, dict)
    return payload


def _prepare_authorization_dispute_fixture(home: Path) -> dict[str, str]:
    query_id = "sha256:" + "8" * 64
    _run_json_ok("--json", "init", "--home", str(home))
    _run_json_ok("--json", "identity", "create", "--home", str(home))
    _run_json_ok(
        "--json",
        "query",
        "register",
        "--home",
        str(home),
        "--base-asset",
        "AGRS",
        "--quote-asset",
        "ZDEX",
        "--query-id",
        query_id,
        "--min-reporters",
        "1",
        "--report-reward-e8",
        "0",
        "--freshness-window-epochs",
        "3",
    )
    reporter = _run_json_ok(
        "--json",
        "reporter",
        "register",
        "--home",
        str(home),
        "--query-id",
        query_id,
        "--required-bond-e8",
        "1",
    )
    _run_json_ok(
        "--json",
        "reporter",
        "bond",
        "--home",
        str(home),
        "--amount-e8",
        "1",
    )
    report = _run_json_ok(
        "--json",
        "report",
        "submit",
        "--home",
        str(home),
        "--query-id",
        query_id,
        "--price-e8",
        "123456789",
        "--source-observed-epoch",
        "10",
        "--source-id",
        "source:manual",
    )
    aggregate = _run_json_ok(
        "--json",
        "aggregate",
        "build",
        "--home",
        str(home),
        "--query-id",
        query_id,
        "--epoch",
        "11",
    )
    accepted_read = _run_json_ok(
        "--json",
        "read",
        "accept",
        "--home",
        str(home),
        "--aggregate-id",
        str(aggregate["aggregate_id"]),
        "--consumer-module",
        "zenodex.zusd",
        "--profile-id",
        "critical-zusd-v1",
    )
    return {
        "query_id": query_id,
        "reporter_id": str(reporter["reporter_id"]),
        "report_id": str(report["report_id"]),
        "read_id": str(accepted_read["read_id"]),
    }


def _authorization_build_args(home: Path, read_id: str) -> list[str]:
    return [
        "--json",
        "authorization",
        "build",
        "--home",
        str(home),
        "--read-id",
        read_id,
        "--action-kind",
        "mint",
        "--action-id",
        "sha256:" + "2" * 64,
        "--action-facts-hash",
        "sha256:" + "3" * 64,
        "--pre-state-hash",
        "sha256:" + "4" * 64,
        "--now-epoch",
        "12",
    ]


def _exact_economic_envelope(
    runtime_action: dict[str, object],
    *,
    reporter_count: int = 1,
    reporter_bond_required_e8: int = 1,
) -> dict[str, object]:
    runtime_notional = runtime_action.get("runtime_notional_value_e8")
    notional_value_e8 = (
        runtime_notional
        if type(runtime_notional) is int
        else runtime_action["runtime_value_e8"]
    )
    assert type(notional_value_e8) is int
    max_extractable_value_e8 = min(1, notional_value_e8)
    return {
        "schema": "zenodex.oracle.economic_security_envelope.v1",
        "query_id": runtime_action["query_id"],
        "consumer_module": runtime_action["consumer_module"],
        "action_kind": runtime_action["action_kind"],
        "notional_value_e8": notional_value_e8,
        "max_extractable_value_e8": max_extractable_value_e8,
        "attack_cost_floor_e8": max_extractable_value_e8,
        "required_attack_margin_bps": 0,
        "reporter_count": reporter_count,
        "reporter_reward_budget_e8": 0,
        "reporter_reward_per_report_e8": 0,
        "honest_reporter_cost_e8": 0,
        "honest_reporter_risk_premium_e8": 0,
        "reporter_bond_required_e8": reporter_bond_required_e8,
        "slash_fraction_bps": 10_000,
        "expected_cheat_gain_e8": max_extractable_value_e8,
        "deterrence_margin_bps": 0,
        "dispute_reward_e8": 0,
        "dispute_budget_e8": 0,
        "fee_paid_e8": 0,
        "reporter_fee_share_e8": 0,
        "treasury_fee_share_e8": 0,
        "burn_fee_share_e8": 0,
    }


def _content_addressed_authorization_fixture(tag: str) -> dict[str, object]:
    authorization: dict[str, object] = {"fixture_tag": tag}
    return {
        "authorization_id": _semantic_hash(
            "zeno_oracle.oracle_authorization.v1",
            authorization,
        ),
        "authorization": authorization,
        "schema": "zeno_oracle.oracle_authorization_bundle.v1",
    }


def _canonical_bytes(payload: dict[str, object]) -> bytes:
    return json.dumps(payload, sort_keys=True, separators=(",", ":"), ensure_ascii=True).encode(
        "utf-8"
    )


def _semantic_hash(domain: str, payload: dict[str, object]) -> str:
    digest = hashlib.sha256(domain.encode("utf-8") + b"\x00" + _canonical_bytes(payload)).hexdigest()
    return f"sha256:{digest}"


def _free_port() -> int:
    with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as sock:
        sock.bind(("127.0.0.1", 0))
        return int(sock.getsockname()[1])


def _http_json(url: str) -> dict[str, object]:
    with urllib.request.urlopen(url, timeout=5) as response:
        return json.loads(response.read().decode("utf-8"))


def _http_post_json(url: str, payload: dict[str, object]) -> tuple[int, dict[str, object]]:
    body = json.dumps(payload).encode("utf-8")
    request = urllib.request.Request(
        url,
        data=body,
        headers={"Content-Type": "application/json"},
        method="POST",
    )
    try:
        with urllib.request.urlopen(request, timeout=5) as response:
            return response.status, json.loads(response.read().decode("utf-8"))
    except urllib.error.HTTPError as exc:
        return exc.code, json.loads(exc.read().decode("utf-8"))


def _http_post_raw_json(url: str, body: bytes) -> tuple[int, dict[str, object]]:
    request = urllib.request.Request(
        url,
        data=body,
        headers={"Content-Type": "application/json"},
        method="POST",
    )
    try:
        with urllib.request.urlopen(request, timeout=5) as response:
            return response.status, json.loads(response.read().decode("utf-8"))
    except urllib.error.HTTPError as exc:
        return exc.code, json.loads(exc.read().decode("utf-8"))


def _http_options_json(url: str) -> tuple[int, dict[str, str], dict[str, object]]:
    request = urllib.request.Request(url, method="OPTIONS")
    with urllib.request.urlopen(request, timeout=5) as response:
        payload = json.loads(response.read().decode("utf-8"))
        return response.status, dict(response.headers.items()), payload


def test_version_reports_non_authoritative_pre_mvp_cli() -> None:
    proc = _run("--json", "version")
    data = json.loads(proc.stdout)
    validator_help = _run("validator", "--help")

    assert proc.returncode == 0
    assert data["name"] == "zenodex-oracle"
    assert data["production_authority"] is False
    assert "zeno_oracle.oracle_authorization.v1" in data["supported_schema_versions"]
    assert validator_help.returncode == 0
    assert "replay" in validator_help.stdout
    assert "receipt" in validator_help.stdout
    assert "authorization" in validator_help.stdout


def test_authorization_runtime_request_is_exact_owned_and_closed() -> None:
    from tools.zenodex_oracle import _authorization_runtime_from_args

    # Arrange: the accepted read defines the four producer-side bindings.
    read = {
        "consumer_module": "zenodex.zusd",
        "profile_id": "critical-zusd-v1",
        "query_id": "sha256:" + "1" * 64,
        "value_e8": 123_456_789,
        "observed_epoch": 12,
    }
    runtime_action = {
        "consumer_module": "zenodex.zusd",
        "action_kind": "mint",
        "action_id": "sha256:" + "2" * 64,
        "action_facts_hash": "sha256:" + "3" * 64,
        "pre_state_hash": "sha256:" + "4" * 64,
        "profile_id": "critical-zusd-v1",
        "query_id": read["query_id"],
        "runtime_value_e8": read["value_e8"],
        "now_epoch": 12,
        "max_freshness_window_epochs": 2,
    }

    # Act: parse to an immutable owned value, then mutate the caller object.
    runtime, source = _authorization_runtime_from_args(
        argparse.Namespace(runtime_action=runtime_action),
        read,
    )
    runtime_action["runtime_value_e8"] = 7

    # Assert.
    assert source == "consumer_runtime_exact"
    assert runtime.runtime_value_e8 == 123_456_789
    assert runtime.max_freshness_window_epochs == 2


@pytest.mark.parametrize(
    ("mutation", "expected_error"),
    [
        ({"runtime_value_e8": True}, "runtime_value_e8 must be an int"),
        ({"runtime_value_e8": 123_456_790}, "runtime_action runtime_value_e8 does not match accepted read"),
        ({"unknown_authority": "caller"}, "runtime_action has unknown fields: unknown_authority"),
    ],
)
def test_authorization_runtime_request_rejects_hostile_or_ambiguous_values(
    mutation: dict[str, object],
    expected_error: str,
) -> None:
    from tools.zenodex_oracle import _authorization_runtime_from_args

    # Arrange.
    read = {
        "consumer_module": "zenodex.zusd",
        "profile_id": "critical-zusd-v1",
        "query_id": "sha256:" + "1" * 64,
        "value_e8": 123_456_789,
        "observed_epoch": 12,
    }
    runtime_action: dict[str, object] = {
        "consumer_module": "zenodex.zusd",
        "action_kind": "mint",
        "action_id": "sha256:" + "2" * 64,
        "action_facts_hash": "sha256:" + "3" * 64,
        "pre_state_hash": "sha256:" + "4" * 64,
        "profile_id": "critical-zusd-v1",
        "query_id": read["query_id"],
        "runtime_value_e8": read["value_e8"],
        "now_epoch": 12,
        "max_freshness_window_epochs": 2,
    }
    runtime_action.update(mutation)

    # Act / Assert.
    with pytest.raises((SystemExit, ValueError), match=expected_error):
        _authorization_runtime_from_args(
            argparse.Namespace(runtime_action=runtime_action),
            read,
        )


def test_authorization_exact_retry_repairs_matching_orphan_receipt(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    import tools.zenodex_oracle as oracle_cli

    # Arrange: the receipt write succeeds, then the append-only index write
    # faults at the one recoverable persistence boundary.
    home = tmp_path / "oracle-home"
    bundle = _content_addressed_authorization_fixture("orphan-retry")
    append_index_row = oracle_cli._append_authorization_index_row

    def fail_append(_path: Path, _payload: dict[str, object]) -> None:
        raise OSError("fault injection after receipt write")

    monkeypatch.setattr(oracle_cli, "_append_authorization_index_row", fail_append)

    # Act: the first attempt faults; an exact retry sees the matching canonical
    # receipt and reconstructs the missing index row.
    with pytest.raises(OSError, match="fault injection"):
        oracle_cli._persist_authorization_bundle(home, bundle)
    monkeypatch.setattr(
        oracle_cli,
        "_append_authorization_index_row",
        append_index_row,
    )
    receipt_path, idempotent_replay, reconciled_orphan = (
        oracle_cli._persist_authorization_bundle(home, bundle)
    )

    # Assert.
    assert receipt_path.exists()
    assert idempotent_replay is True
    assert reconciled_orphan is True
    rows = oracle_cli._iter_jsonl(oracle_cli._authorizations_log_path(home))
    assert rows == [bundle]


def test_authorization_receipt_write_uses_same_directory_atomic_replace_and_fsync(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    import tools.zenodex_oracle as oracle_cli

    # Arrange.
    receipt_path = tmp_path / "receipts" / "authorizations" / "sha256_a.json"
    receipt_path.parent.mkdir(parents=True)
    bundle = {
        "authorization_id": "sha256:" + "a" * 64,
        "schema": "zeno_oracle.oracle_authorization_bundle.v1",
    }
    events: list[tuple[str, Path | None]] = []
    real_mkstemp = oracle_cli.tempfile.mkstemp
    real_fsync = oracle_cli.os.fsync
    real_replace = oracle_cli.os.replace

    def tracked_mkstemp(*args: object, **kwargs: object) -> tuple[int, str]:
        fd, raw_path = real_mkstemp(*args, **kwargs)
        temp_path = Path(raw_path)
        events.append(("temp", temp_path))
        assert temp_path.parent == receipt_path.parent
        return fd, raw_path

    def tracked_fsync(fd: int) -> None:
        events.append(("file_fsync", None))
        real_fsync(fd)

    def tracked_replace(source: str | Path, destination: str | Path) -> None:
        source_path = Path(source)
        destination_path = Path(destination)
        events.append(("replace", destination_path))
        assert source_path.parent == destination_path.parent == receipt_path.parent
        real_replace(source, destination)

    def tracked_directory_fsync(path: Path) -> None:
        events.append(("directory_fsync", path))

    monkeypatch.setattr(oracle_cli.tempfile, "mkstemp", tracked_mkstemp)
    monkeypatch.setattr(oracle_cli.os, "fsync", tracked_fsync)
    monkeypatch.setattr(oracle_cli.os, "replace", tracked_replace)
    monkeypatch.setattr(oracle_cli, "_fsync_directory", tracked_directory_fsync)

    # Act.
    oracle_cli._write_authorization_receipt_atomic(receipt_path, bundle)

    # Assert: the canonical path becomes visible only after the temp file is
    # flushed, and the containing directory is synced after the rename.
    event_names = [name for name, _path in events]
    assert event_names == ["temp", "file_fsync", "replace", "directory_fsync"]
    assert events[-1] == ("directory_fsync", receipt_path.parent)
    assert oracle_cli._load_json(receipt_path) == bundle
    assert list(receipt_path.parent.glob(f".{receipt_path.name}.*.tmp")) == []


def test_authorization_crash_before_receipt_replace_publishes_nothing_then_retries(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    import tools.zenodex_oracle as oracle_cli

    # Arrange.
    home = tmp_path / "oracle-home"
    bundle = _content_addressed_authorization_fixture("before-replace")
    receipt_path = oracle_cli._authorization_receipt_path(
        home,
        bundle["authorization_id"],
    )
    real_replace = oracle_cli.os.replace

    def fail_receipt_replace(source: str | Path, destination: str | Path) -> None:
        if Path(destination) == receipt_path:
            raise OSError("fault injection before receipt replace")
        real_replace(source, destination)

    monkeypatch.setattr(oracle_cli.os, "replace", fail_receipt_replace)

    # Act: the pre-linearization crash prefix publishes neither durable object.
    with pytest.raises(OSError, match="before receipt replace"):
        oracle_cli._persist_authorization_bundle(home, bundle)

    # Assert, then retry with the fault removed.
    assert not receipt_path.exists()
    assert not oracle_cli._authorizations_log_path(home).exists()
    assert list(receipt_path.parent.glob(f".{receipt_path.name}.*.tmp")) == []

    monkeypatch.setattr(oracle_cli.os, "replace", real_replace)
    result = oracle_cli._persist_authorization_bundle(home, bundle)
    assert result == (receipt_path, False, False)
    assert oracle_cli._load_json(receipt_path) == bundle
    assert oracle_cli._authorization_rows(home) == [bundle]


def test_authorization_retry_recovers_after_receipt_replace_directory_fsync_fault(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    import tools.zenodex_oracle as oracle_cli

    # Arrange.
    home = tmp_path / "oracle-home"
    bundle = _content_addressed_authorization_fixture("after-replace")
    receipt_path = oracle_cli._authorization_receipt_path(
        home,
        bundle["authorization_id"],
    )
    real_directory_fsync = oracle_cli._fsync_directory
    faulted = False

    def fail_once_after_receipt_replace(path: Path) -> None:
        nonlocal faulted
        if path == receipt_path.parent and receipt_path.exists() and not faulted:
            faulted = True
            raise OSError("fault injection after receipt replace")
        real_directory_fsync(path)

    monkeypatch.setattr(oracle_cli, "_fsync_directory", fail_once_after_receipt_replace)

    # Act.
    with pytest.raises(OSError, match="after receipt replace"):
        oracle_cli._persist_authorization_bundle(home, bundle)

    # Assert: the canonical receipt is the recoverable linearized prefix. An
    # exact retry syncs it and reconstructs one index row.
    assert receipt_path.exists()
    assert not oracle_cli._authorizations_log_path(home).exists()
    monkeypatch.setattr(oracle_cli, "_fsync_directory", real_directory_fsync)
    result = oracle_cli._persist_authorization_bundle(home, bundle)
    assert result == (receipt_path, True, True)
    assert oracle_cli._authorization_rows(home) == [bundle]


def test_authorization_retry_rebuilds_torn_trailing_index_from_receipt(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    import tools.zenodex_oracle as oracle_cli

    # Arrange.
    home = tmp_path / "oracle-home"
    bundle = _content_addressed_authorization_fixture("torn-index")
    index_path = oracle_cli._authorizations_log_path(home)
    append_index_row = oracle_cli._append_authorization_index_row

    def write_torn_prefix_then_fail(path: Path, payload: dict[str, object]) -> None:
        path.parent.mkdir(parents=True, exist_ok=True)
        complete_line = oracle_cli._authorization_index_line_bytes(payload)
        path.write_bytes(complete_line[: len(complete_line) // 2])
        raise OSError("fault injection during index append")

    monkeypatch.setattr(
        oracle_cli,
        "_append_authorization_index_row",
        write_torn_prefix_then_fail,
    )

    # Act.
    with pytest.raises(OSError, match="during index append"):
        oracle_cli._persist_authorization_bundle(home, bundle)

    # Assert the reader ignores only the unterminated tail. Exact retry rebuilds
    # the derived index from the canonical receipt and leaves one complete row.
    assert index_path.read_bytes()
    assert not index_path.read_bytes().endswith(b"\n")
    assert oracle_cli._authorization_rows(home) == []
    verification_errors: list[str] = []
    oracle_cli._verify_stored_receipt_files(home, verification_errors)
    assert any(
        "is not present in authorizations log" in error
        for error in verification_errors
    )
    monkeypatch.setattr(
        oracle_cli,
        "_append_authorization_index_row",
        append_index_row,
    )
    receipt_path = oracle_cli._authorization_receipt_path(
        home,
        bundle["authorization_id"],
    )
    result = oracle_cli._persist_authorization_bundle(home, bundle)
    assert result == (receipt_path, True, True)
    assert index_path.read_bytes().endswith(b"\n")
    assert oracle_cli._authorization_rows(home) == [bundle]


def test_authorization_index_is_explicitly_rebuildable_from_canonical_receipts(
    tmp_path: Path,
) -> None:
    import tools.zenodex_oracle as oracle_cli

    # Arrange: persist in reverse identity order, then lose the derived index.
    home = tmp_path / "oracle-home"
    fixtures = sorted(
        (
            _content_addressed_authorization_fixture("rebuild-one"),
            _content_addressed_authorization_fixture("rebuild-two"),
        ),
        key=lambda bundle: str(bundle["authorization_id"]),
    )
    bundle_1, bundle_2 = fixtures
    oracle_cli._persist_authorization_bundle(home, bundle_2)
    oracle_cli._persist_authorization_bundle(home, bundle_1)
    index_path = oracle_cli._authorizations_log_path(home)
    index_path.unlink()

    # Act.
    rebuilt_rows = oracle_cli._rebuild_authorization_index(home)

    # Assert: canonical receipts reconstruct one deterministic row per identity.
    assert rebuilt_rows == [bundle_1, bundle_2]
    assert oracle_cli._authorization_rows(home) == [bundle_1, bundle_2]
    assert index_path.read_bytes().endswith(b"\n")


def test_authorization_index_recovery_rejects_corruption_before_torn_tail(
    tmp_path: Path,
) -> None:
    import tools.zenodex_oracle as oracle_cli

    # Arrange: a canonical receipt exists, while the derived index contains a
    # malformed completed first record followed by an unterminated tail.
    home = tmp_path / "oracle-home"
    bundle = _content_addressed_authorization_fixture("corrupt-before-tail")
    receipt_path, _, _ = oracle_cli._persist_authorization_bundle(home, bundle)
    index_path = oracle_cli._authorizations_log_path(home)
    corrupted_bytes = b'{"authorization_id":}\n{"authorization_id":"sha256:'
    index_path.write_bytes(corrupted_bytes)
    receipt_bytes = receipt_path.read_bytes()

    # Act / Assert: neither read-only validation nor recovery treats corruption
    # in a newline-terminated record as a permissible final crash fragment.
    with pytest.raises(SystemExit, match=r":1: invalid authorization index JSON"):
        oracle_cli._authorization_rows(home)
    assert index_path.read_bytes() == corrupted_bytes
    with pytest.raises(SystemExit, match=r":1: invalid authorization index JSON"):
        oracle_cli._persist_authorization_bundle(home, bundle)
    assert index_path.read_bytes() == corrupted_bytes
    assert receipt_path.read_bytes() == receipt_bytes


def test_authorization_rows_reject_duplicate_completed_rows_without_repair(
    tmp_path: Path,
) -> None:
    import tools.zenodex_oracle as oracle_cli

    # Arrange.
    home = tmp_path / "oracle-home"
    bundle = _content_addressed_authorization_fixture("duplicate-index")
    oracle_cli._persist_authorization_bundle(home, bundle)
    index_path = oracle_cli._authorizations_log_path(home)
    one_row = index_path.read_bytes()
    duplicate_rows = one_row + one_row
    index_path.write_bytes(duplicate_rows)

    # Act / Assert.
    with pytest.raises(SystemExit, match="duplicate index rows"):
        oracle_cli._authorization_rows(home)
    assert index_path.read_bytes() == duplicate_rows


def test_authorization_rows_reject_completed_row_receipt_mismatch_without_repair(
    tmp_path: Path,
) -> None:
    import tools.zenodex_oracle as oracle_cli

    # Arrange.
    home = tmp_path / "oracle-home"
    bundle = _content_addressed_authorization_fixture("index-receipt-mismatch")
    receipt_path, _, _ = oracle_cli._persist_authorization_bundle(home, bundle)
    index_path = oracle_cli._authorizations_log_path(home)
    tampered = dict(bundle)
    tampered["schema"] = "zeno_oracle.oracle_authorization_bundle.v0"
    tampered_bytes = oracle_cli._authorization_index_line_bytes(tampered)
    index_path.write_bytes(tampered_bytes)
    receipt_bytes = receipt_path.read_bytes()

    # Act / Assert.
    with pytest.raises(SystemExit, match="collision with different durable bundle"):
        oracle_cli._authorization_rows(home)
    assert index_path.read_bytes() == tampered_bytes
    assert receipt_path.read_bytes() == receipt_bytes


@pytest.mark.parametrize("surface", ["persist", "receipt"])
def test_authorization_durable_state_rejects_content_address_mismatch(
    tmp_path: Path,
    surface: str,
) -> None:
    import tools.zenodex_oracle as oracle_cli

    home = tmp_path / "oracle-home"
    bundle = _content_addressed_authorization_fixture("content-address")
    if surface == "receipt":
        receipt_path, _, _ = oracle_cli._persist_authorization_bundle(home, bundle)
    tampered = json.loads(json.dumps(bundle))
    tampered["authorization"]["fixture_tag"] = "tampered"

    if surface == "persist":
        with pytest.raises(
            SystemExit,
            match="authorization_id does not match authorization content",
        ):
            oracle_cli._persist_authorization_bundle(home, tampered)
        assert not (home / "data" / "oracle_authorizations.jsonl").exists()
        assert list((home / "receipts" / "authorizations").glob("*.json")) == []
    else:
        receipt_path.write_bytes(oracle_cli._authorization_receipt_bytes(tampered))
        with pytest.raises(
            SystemExit,
            match="authorization_id does not match authorization content",
        ):
            oracle_cli._authorization_rows(home)


@pytest.mark.parametrize("corrupt_surface", ["index", "receipt"])
def test_authorization_rows_reject_duplicate_json_keys(
    tmp_path: Path,
    corrupt_surface: str,
) -> None:
    import tools.zenodex_oracle as oracle_cli

    # Arrange.
    home = tmp_path / "oracle-home"
    bundle = _content_addressed_authorization_fixture("duplicate-json-key")
    authorization_id = str(bundle["authorization_id"])
    receipt_path, _, _ = oracle_cli._persist_authorization_bundle(home, bundle)
    index_path = oracle_cli._authorizations_log_path(home)
    duplicate_key_bytes = (
        "{"
        f'"authorization_id":"{authorization_id}",'
        f'"authorization_id":"{authorization_id}",'
        '"schema":"zeno_oracle.oracle_authorization_bundle.v1"'
        "}\n"
    ).encode("ascii")
    corrupt_path = index_path if corrupt_surface == "index" else receipt_path
    corrupt_path.write_bytes(duplicate_key_bytes)

    # Act / Assert.
    expected = (
        "duplicate authorization index JSON key"
        if corrupt_surface == "index"
        else "duplicate canonical authorization receipt JSON key"
    )
    with pytest.raises(SystemExit, match=expected):
        oracle_cli._authorization_rows(home)
    assert corrupt_path.read_bytes() == duplicate_key_bytes


@pytest.mark.parametrize("corrupt_surface", ["index", "receipt"])
def test_authorization_rows_reject_nonfinite_json_constants(
    tmp_path: Path,
    corrupt_surface: str,
) -> None:
    import tools.zenodex_oracle as oracle_cli

    home = tmp_path / "oracle-home"
    bundle = _content_addressed_authorization_fixture("nonfinite-json")
    authorization_id = str(bundle["authorization_id"])
    receipt_path, _, _ = oracle_cli._persist_authorization_bundle(home, bundle)
    index_path = oracle_cli._authorizations_log_path(home)
    nonfinite_bytes = (
        "{"
        f'"authorization_id":"{authorization_id}",'
        '"schema":"zeno_oracle.oracle_authorization_bundle.v1",'
        '"poison":NaN'
        "}\n"
    ).encode("ascii")
    corrupt_path = index_path if corrupt_surface == "index" else receipt_path
    corrupt_path.write_bytes(nonfinite_bytes)

    expected = (
        "non-finite authorization index JSON constant: NaN"
        if corrupt_surface == "index"
        else "non-finite canonical authorization receipt JSON constant: NaN"
    )
    with pytest.raises(SystemExit, match=expected):
        oracle_cli._authorization_rows(home)
    assert corrupt_path.read_bytes() == nonfinite_bytes


def test_authorization_persistence_uses_exclusive_cross_process_lock(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    import tools.zenodex_oracle as oracle_cli

    calls: list[int] = []
    real_flock = oracle_cli.fcntl.flock

    def tracked_flock(fd: int, operation: int) -> None:
        calls.append(operation)
        real_flock(fd, operation)

    monkeypatch.setattr(oracle_cli.fcntl, "flock", tracked_flock)
    bundle = _content_addressed_authorization_fixture("exclusive-lock")

    oracle_cli._persist_authorization_bundle(tmp_path, bundle)

    assert calls == [oracle_cli.fcntl.LOCK_EX, oracle_cli.fcntl.LOCK_UN]
    assert (tmp_path / "data" / "oracle_authorizations.lock").exists()


def test_dispute_commit_before_authorization_rejects_without_authorization_write(
    tmp_path: Path,
) -> None:
    # Arrange.
    home = tmp_path / "oracle-home"
    fixture = _prepare_authorization_dispute_fixture(home)
    _run_json_ok(
        "--json",
        "dispute",
        "open",
        "--home",
        str(home),
        "--report-id",
        fixture["report_id"],
        "--reporter-id",
        fixture["reporter_id"],
        "--bond-e8",
        "1",
        "--reason",
        "linearization-test",
        "--epoch",
        "12",
    )

    # Act.
    authorization = _run(*_authorization_build_args(home, fixture["read_id"]))

    # Assert: dispute-first ordering rejects before either authorization write.
    assert authorization.returncode != 0
    assert "disputed reports" in authorization.stderr
    assert not (home / "data" / "oracle_authorizations.jsonl").exists()
    assert list((home / "receipts" / "authorizations").glob("*.json")) == []


def test_authorization_commit_before_later_dispute_remains_historical_artifact(
    tmp_path: Path,
) -> None:
    # Arrange.
    home = tmp_path / "oracle-home"
    fixture = _prepare_authorization_dispute_fixture(home)
    authorization = _run_json_ok(*_authorization_build_args(home, fixture["read_id"]))
    receipt_path = Path(str(authorization["receipt_path"]))
    index_path = home / "data" / "oracle_authorizations.jsonl"
    receipt_bytes = receipt_path.read_bytes()
    index_bytes = index_path.read_bytes()

    # Act.
    _run_json_ok(
        "--json",
        "dispute",
        "open",
        "--home",
        str(home),
        "--report-id",
        fixture["report_id"],
        "--reporter-id",
        fixture["reporter_id"],
        "--bond-e8",
        "1",
        "--reason",
        "historical-artifact-test",
        "--epoch",
        "13",
    )
    retry = _run(*_authorization_build_args(home, fixture["read_id"]))

    # Assert: authorization-first ordering keeps its historical bytes. The
    # later dispute blocks new issuance; settlement revocation is separate.
    assert retry.returncode != 0
    assert "disputed reports" in retry.stderr
    assert receipt_path.read_bytes() == receipt_bytes
    assert index_path.read_bytes() == index_bytes


def test_authorization_build_snapshots_and_persists_under_one_non_nested_lock(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture[str],
) -> None:
    import tools.zenodex_oracle as oracle_cli

    # Arrange.
    home = tmp_path / "oracle-home"
    fixture = _prepare_authorization_dispute_fixture(home)
    events: list[str] = []
    lock_held = False
    lock_depth = 0
    real_lock = oracle_cli._authorization_persistence_lock
    real_load_disputes = oracle_cli._load_disputes
    real_persist_locked = oracle_cli._persist_authorization_bundle_locked

    @contextlib.contextmanager
    def tracked_lock(lock_home: Path):
        nonlocal lock_depth, lock_held
        assert lock_depth == 0
        lock_depth += 1
        with real_lock(lock_home):
            lock_held = True
            events.append("lock_enter")
            try:
                yield
            finally:
                lock_held = False
        events.append("lock_exit")
        lock_depth -= 1

    def tracked_load_disputes(load_home: Path) -> dict[str, object]:
        assert lock_held
        events.append("dispute_snapshot")
        return real_load_disputes(load_home)

    def tracked_persist_locked(
        persist_home: Path,
        bundle: dict[str, object],
    ) -> tuple[Path, bool, bool]:
        assert lock_held
        events.append("persist_locked")
        return real_persist_locked(persist_home, bundle)

    def reject_nested_persist(*_args: object, **_kwargs: object) -> None:
        raise AssertionError("authorization build attempted nested lock acquisition")

    monkeypatch.setattr(oracle_cli, "_authorization_persistence_lock", tracked_lock)
    monkeypatch.setattr(oracle_cli, "_load_disputes", tracked_load_disputes)
    monkeypatch.setattr(
        oracle_cli,
        "_persist_authorization_bundle_locked",
        tracked_persist_locked,
    )
    monkeypatch.setattr(oracle_cli, "_persist_authorization_bundle", reject_nested_persist)
    args = argparse.Namespace(
        home=str(home),
        read_id=fixture["read_id"],
        action_kind="mint",
        action_id="sha256:" + "2" * 64,
        action_facts_hash="sha256:" + "3" * 64,
        pre_state_hash="sha256:" + "4" * 64,
        now_epoch=12,
        min_evidence_class="O3",
        economic_envelope_id="econ:local-dev-v1",
        json=True,
    )

    # Act.
    result = oracle_cli.cmd_authorization_build(args)
    capsys.readouterr()

    # Assert.
    assert result == 0
    assert events == ["lock_enter", "dispute_snapshot", "persist_locked", "lock_exit"]
    assert lock_depth == 0
    assert lock_held is False


def test_dispute_open_and_resolve_share_authorization_linearization_lock(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture[str],
) -> None:
    import tools.zenodex_oracle as oracle_cli

    # Arrange.
    home = tmp_path / "oracle-home"
    fixture = _prepare_authorization_dispute_fixture(home)
    events: list[str] = []
    lock_held = False
    lock_depth = 0
    real_lock = oracle_cli._authorization_persistence_lock
    real_load_disputes = oracle_cli._load_disputes
    real_write_registry = oracle_cli._write_dispute_registry_durable
    real_append_jsonl = oracle_cli._append_jsonl

    @contextlib.contextmanager
    def tracked_lock(lock_home: Path):
        nonlocal lock_depth, lock_held
        assert lock_depth == 0
        lock_depth += 1
        with real_lock(lock_home):
            lock_held = True
            events.append("lock_enter")
            try:
                yield
            finally:
                lock_held = False
        events.append("lock_exit")
        lock_depth -= 1

    def tracked_load_disputes(load_home: Path) -> dict[str, object]:
        assert lock_held
        events.append("dispute_snapshot")
        return real_load_disputes(load_home)

    def tracked_write_registry(
        write_home: Path,
        disputes: dict[str, object],
    ) -> None:
        assert lock_held
        events.append("registry_commit")
        real_write_registry(write_home, disputes)

    def tracked_append(path: Path, payload: dict[str, object]) -> None:
        if path == oracle_cli._disputes_log_path(home):
            assert lock_held
            events.append("dispute_log_append")
        real_append_jsonl(path, payload)

    monkeypatch.setattr(oracle_cli, "_authorization_persistence_lock", tracked_lock)
    monkeypatch.setattr(oracle_cli, "_load_disputes", tracked_load_disputes)
    monkeypatch.setattr(oracle_cli, "_write_dispute_registry_durable", tracked_write_registry)
    monkeypatch.setattr(oracle_cli, "_append_jsonl", tracked_append)
    open_args = argparse.Namespace(
        home=str(home),
        report_id=fixture["report_id"],
        reporter_id=fixture["reporter_id"],
        bond_e8="1",
        reason="lock-order-test",
        epoch=12,
        dispute_id=None,
        force=False,
        json=True,
    )

    # Act / Assert: open mutation is fully enclosed by the shared lock.
    assert oracle_cli.cmd_dispute_open(open_args) == 0
    opened = json.loads(capsys.readouterr().out)
    assert events == [
        "lock_enter",
        "dispute_snapshot",
        "registry_commit",
        "dispute_log_append",
        "lock_exit",
    ]

    events.clear()
    resolve_args = argparse.Namespace(
        home=str(home),
        dispute_id=opened["dispute_id"],
        outcome="rejected",
        slash_e8=None,
        epoch=13,
        force=False,
        json=True,
    )
    assert oracle_cli.cmd_dispute_resolve(resolve_args) == 0
    capsys.readouterr()
    assert events == [
        "lock_enter",
        "dispute_snapshot",
        "registry_commit",
        "dispute_log_append",
        "lock_exit",
    ]
    assert lock_depth == 0
    assert lock_held is False


def test_exact_authorization_api_rejects_unknown_request_fields(tmp_path: Path) -> None:
    from tools.zenodex_oracle import _write_endpoint_payload

    status, payload = _write_endpoint_payload(
        tmp_path,
        "/api/oracle/authorization/build-exact",
        {
            "read_id": "sha256:" + "1" * 64,
            "caller_selected_root": "sha256:" + "2" * 64,
        },
    )

    assert status == 400
    assert payload["ok"] is False
    assert payload["error"] == (
        "exact authorization request has unknown fields: caller_selected_root"
    )


def test_authorization_runtime_request_rejects_mapping_subclass() -> None:
    from tools.zenodex_oracle import _authorization_runtime_from_args

    class HostileRuntime(dict[str, object]):
        pass

    # Arrange.
    read = {
        "consumer_module": "zenodex.zusd",
        "profile_id": "critical-zusd-v1",
        "query_id": "sha256:" + "1" * 64,
        "value_e8": 123_456_789,
        "observed_epoch": 12,
    }
    hostile = HostileRuntime(
        consumer_module="zenodex.zusd",
        action_kind="mint",
        action_id="sha256:" + "2" * 64,
        action_facts_hash="sha256:" + "3" * 64,
        pre_state_hash="sha256:" + "4" * 64,
        profile_id="critical-zusd-v1",
        query_id=read["query_id"],
        runtime_value_e8=read["value_e8"],
        now_epoch=12,
    )

    # Act / Assert.
    with pytest.raises(ValueError, match="runtime_action must be an exact object"):
        _authorization_runtime_from_args(
            argparse.Namespace(runtime_action=hostile),
            read,
        )


def test_critical_profile_detection_accepts_namespaced_profile_ids() -> None:
    from tools.zenodex_oracle import _is_critical_profile

    assert _is_critical_profile("critical-zusd-v1") is True
    assert _is_critical_profile("profile:zusd-critical-o3-v1") is True
    assert _is_critical_profile("profile/trigger_critical.o3") is True
    assert _is_critical_profile("devnet-zusd-v1") is False
    assert _is_critical_profile("profile:devnet-noncritical-v1") is False


def test_init_and_identity_create_do_not_print_private_key(tmp_path: Path) -> None:
    home = tmp_path / "oracle"

    init = _run("--json", "init", "--home", str(home))
    created = _run("--json", "identity", "create", "--home", str(home))
    shown = _run("--json", "identity", "show", "--home", str(home))

    assert init.returncode == 0
    assert created.returncode == 0
    assert shown.returncode == 0
    created_data = json.loads(created.stdout)
    shown_data = json.loads(shown.stdout)
    assert "secret_key" not in created_data
    assert "secret_key" not in shown_data
    assert shown_data["reporter_id"] == created_data["reporter_id"]
    assert (home / "config.toml").exists()
    assert (home / "keys" / "reporter.key.json").exists()


def test_query_registry_list_and_show(tmp_path: Path) -> None:
    registry = tmp_path / "queries.json"
    query_id = "sha256:" + "1" * 64
    registry.write_text(
        json.dumps(
            {
                "queries": [
                    {
                        "query_id": query_id,
                        "query_type": "spot_price",
                        "base_asset": "AGRS",
                        "quote_asset": "ZDEX",
                        "scale": 100000000,
                    }
                ]
            }
        ),
        encoding="utf-8",
    )

    listed = _run("--json", "query", "list", "--registry", str(registry))
    shown = _run("--json", "query", "show", "--registry", str(registry), "--query-id", query_id)

    assert listed.returncode == 0
    assert json.loads(listed.stdout)["count"] == 1
    assert shown.returncode == 0
    assert json.loads(shown.stdout)["query"]["base_asset"] == "AGRS"


def test_local_query_register_creates_feed_policy(tmp_path: Path) -> None:
    home = tmp_path / "oracle"

    assert _run("--json", "init", "--home", str(home)).returncode == 0
    registered = _run(
        "--json",
        "query",
        "register",
        "--home",
        str(home),
        "--base-asset",
        "agrs",
        "--quote-asset",
        "zdex",
        "--evidence-floor",
        "O3",
        "--min-reporters",
        "5",
        "--freshness-window-epochs",
        "4",
        "--max-deviation-bps",
        "80",
        "--high-uncertainty-confidence-e8",
        "250000",
        "--asset-class",
        "rwa",
        "--jurisdiction",
        "US",
        "--market-hours-policy-id",
        "us-business-days-v1",
        "--valuation-policy-id",
        "appraisal-nav-v1",
    )
    registered_data = json.loads(registered.stdout)
    listed = _run("--json", "query", "list", "--home", str(home))
    shown = _run(
        "--json",
        "query",
        "show",
        "--home",
        str(home),
        "--query-id",
        registered_data["query_id"],
    )

    assert registered.returncode == 0
    assert registered_data["query"]["base_asset"] == "AGRS"
    assert registered_data["query"]["quote_asset"] == "ZDEX"
    assert registered_data["query"]["asset_class"] == "rwa"
    assert registered_data["query"]["jurisdiction"] == "US"
    assert registered_data["query"]["market_hours_policy_id"] == "us-business-days-v1"
    assert registered_data["query"]["valuation_policy_id"] == "appraisal-nav-v1"
    assert registered_data["query"]["evidence_floor"] == "O3"
    assert registered_data["query"]["min_reporters"] == 5
    assert listed.returncode == 0
    assert json.loads(listed.stdout)["count"] == 1
    assert shown.returncode == 0
    assert json.loads(shown.stdout)["query"]["max_deviation_bps"] == 80


def test_local_query_register_supports_equity_and_rwa_metadata(tmp_path: Path) -> None:
    home = tmp_path / "oracle"

    assert _run("--json", "init", "--home", str(home)).returncode == 0
    equity = _run(
        "--json",
        "query",
        "register",
        "--home",
        str(home),
        "--query-type",
        "settlement_price",
        "--base-asset",
        "AAPL",
        "--quote-asset",
        "USD",
        "--asset-class",
        "equity",
        "--market-hours-policy-id",
        "nasdaq-regular-hours-v1",
        "--valuation-policy-id",
        "official-close-v1",
        "--min-reporters",
        "3",
    )
    equity_data = json.loads(equity.stdout)
    status = _run(
        "--json",
        "query",
        "status",
        "--home",
        str(home),
        "--query-id",
        equity_data["query_id"],
        "--now-epoch",
        "1",
    )
    status_all = _run(
        "--json",
        "query",
        "status",
        "--home",
        str(home),
        "--all",
        "--now-epoch",
        "1",
    )
    status_data = json.loads(status.stdout)["feed_status"]

    assert equity.returncode == 0
    assert equity_data["query"]["query_type"] == "settlement_price"
    assert equity_data["query"]["asset_class"] == "equity"
    assert equity_data["query"]["market_hours_policy_id"] == "nasdaq-regular-hours-v1"
    assert equity_data["query"]["valuation_policy_id"] == "official-close-v1"
    assert status.returncode == 0
    assert status_data["asset_class"] == "equity"
    assert status_data["market_hours_policy_id"] == "nasdaq-regular-hours-v1"
    assert "devnet-only" in status_data["status"]
    assert status_all.returncode == 0
    status_all_data = json.loads(status_all.stdout)
    assert status_all_data["count"] == 1
    assert status_all_data["feed_statuses"][0]["asset_class"] == "equity"


def test_source_registry_register_list_show_and_submit_binding(tmp_path: Path) -> None:
    home = tmp_path / "oracle"
    query_id = "sha256:" + "8" * 64

    assert _run("--json", "init", "--home", str(home)).returncode == 0
    assert _run("--json", "identity", "create", "--home", str(home)).returncode == 0
    assert (
        _run(
            "--json",
            "query",
            "register",
            "--home",
            str(home),
            "--base-asset",
            "AGRS",
            "--quote-asset",
            "ZDEX",
            "--query-id",
            query_id,
            "--source-policy-id",
            "source-policy:registered-diverse-v1",
            "--min-reporters",
            "1",
            "--report-reward-e8",
            "0",
        ).returncode
        == 0
    )
    assert (
        _run(
            "--json",
            "reporter",
            "register",
            "--home",
            str(home),
            "--query-id",
            query_id,
            "--required-bond-e8",
            "1",
        ).returncode
        == 0
    )
    assert _run("--json", "reporter", "bond", "--home", str(home), "--amount-e8", "1").returncode == 0
    missing_source = _run(
        "--json",
        "report",
        "submit",
        "--home",
        str(home),
        "--query-id",
        query_id,
        "--price-e8",
        "123",
        "--source-observed-epoch",
        "10",
        "--source-id",
        "source:cex-a",
    )
    registered_source = _run(
        "--json",
        "source",
        "register",
        "--home",
        str(home),
        "--source-id",
        "source:cex-a",
        "--source-kind",
        "cex",
        "--operator-id",
        "operator:cex-a",
        "--control-group-id",
        "control:cex-a",
        "--venue-id",
        "venue:cex-a",
        "--data-family-id",
        "price:cex-last-trade",
        "--transport-id",
        "api:https:cex-a",
        "--asset-class",
        "crypto",
        "--query-id",
        query_id,
        "--assurance-class",
        "S3",
        "--epoch",
        "9",
    )
    listed = _run("--json", "source", "list", "--home", str(home), "--active-only")
    shown = _run(
        "--json",
        "source",
        "show",
        "--home",
        str(home),
        "--source-id",
        "source:cex-a",
    )
    submitted = _run(
        "--json",
        "report",
        "submit",
        "--home",
        str(home),
        "--query-id",
        query_id,
        "--price-e8",
        "123",
        "--source-observed-epoch",
        "10",
        "--source-id",
        "source:cex-a",
    )
    aggregate = _run("--json", "aggregate", "build", "--home", str(home), "--query-id", query_id, "--epoch", "11")
    replay = _run("--json", "verify", "local-state", "--home", str(home))

    assert missing_source.returncode != 0
    assert "not registered" in missing_source.stderr
    assert registered_source.returncode == 0
    registered_data = json.loads(registered_source.stdout)
    assert registered_data["source"]["source_control_group_id"] == "control:cex-a"
    assert registered_data["source"]["assurance_class"] == "S3"
    assert listed.returncode == 0
    assert json.loads(listed.stdout)["count"] == 1
    assert shown.returncode == 0
    assert json.loads(shown.stdout)["source"]["venue_id"] == "venue:cex-a"
    assert submitted.returncode == 0
    report = json.loads((home / "data" / "reports.jsonl").read_text(encoding="utf-8").splitlines()[0])
    assert report["source_state_at_submit"]["source_id"] == "source:cex-a"
    assert report["source_state_at_submit"]["source_control_group_id"] == "control:cex-a"
    assert aggregate.returncode == 0
    aggregate_data = json.loads(aggregate.stdout)["aggregate"]
    assert aggregate_data["source_registry_root"].startswith("sha256:")
    assert aggregate_data["reporter_registry_root"].startswith("sha256:")
    assert replay.returncode == 0
    assert json.loads(replay.stdout)["ok"] is True


def test_registered_source_policy_rejects_source_control_group_collision() -> None:
    from tools.zenodex_oracle import _aggregate_from_reports

    query = {
        "query_id": "sha256:" + "3" * 64,
        "evidence_floor": "O3",
        "min_reporters": 2,
        "source_policy_id": "source-policy:registered-diverse-v1",
    }
    reports = [
        {
            "report_id": "sha256:" + "4" * 64,
            "query_id": query["query_id"],
            "reporter_id": "reporter:a",
            "source_id": "source:a",
            "price_e8": 100,
            "source_observed_epoch": 10,
            "source_state_at_submit": {
                "active": True,
                "source_id": "source:a",
                "source_control_group_id": "control:same",
                "venue_id": "venue:a",
                "data_family_id": "price:a",
                "transport_id": "api:a",
                "assurance_class": "S3",
            },
        },
        {
            "report_id": "sha256:" + "5" * 64,
            "query_id": query["query_id"],
            "reporter_id": "reporter:b",
            "source_id": "source:b",
            "price_e8": 101,
            "source_observed_epoch": 10,
            "source_state_at_submit": {
                "active": True,
                "source_id": "source:b",
                "source_control_group_id": "control:same",
                "venue_id": "venue:b",
                "data_family_id": "price:b",
                "transport_id": "api:b",
                "assurance_class": "S3",
            },
        },
    ]

    try:
        _aggregate_from_reports(query=query, reports=reports, epoch=11)
    except SystemExit as exc:
        assert "source_control_group_id" in str(exc)
    else:
        raise AssertionError("registered source policy must reject shared source control groups")


def test_registered_source_policy_rejects_registered_dimension_collisions() -> None:
    from tools.zenodex_oracle import _aggregate_from_reports

    query = {
        "query_id": "sha256:" + "3" * 64,
        "evidence_floor": "O3",
        "min_reporters": 2,
        "source_policy_id": "source-policy:registered-diverse-v1",
    }
    base_sources = [
        {
            "active": True,
            "source_id": "source:a",
            "source_control_group_id": "control:a",
            "venue_id": "venue:a",
            "data_family_id": "price:a",
            "transport_id": "api:a",
            "assurance_class": "S3",
        },
        {
            "active": True,
            "source_id": "source:b",
            "source_control_group_id": "control:b",
            "venue_id": "venue:b",
            "data_family_id": "price:b",
            "transport_id": "api:b",
            "assurance_class": "S3",
        },
    ]

    for dimension in ("venue_id", "data_family_id", "transport_id"):
        sources = [dict(item) for item in base_sources]
        sources[1][dimension] = sources[0][dimension]
        reports = [
            {
                "report_id": "sha256:" + "4" * 64,
                "query_id": query["query_id"],
                "reporter_id": "reporter:a",
                "source_id": "source:a",
                "price_e8": 100,
                "source_observed_epoch": 10,
                "source_state_at_submit": sources[0],
            },
            {
                "report_id": "sha256:" + "5" * 64,
                "query_id": query["query_id"],
                "reporter_id": "reporter:b",
                "source_id": "source:b",
                "price_e8": 101,
                "source_observed_epoch": 10,
                "source_state_at_submit": sources[1],
            },
        ]

        try:
            _aggregate_from_reports(query=query, reports=reports, epoch=11)
        except SystemExit as exc:
            assert dimension in str(exc)
        else:
            raise AssertionError(f"registered source policy must reject shared {dimension}")


def test_registered_source_policy_rejects_incomplete_or_misbound_source_snapshot() -> None:
    from tools.zenodex_oracle import _aggregate_from_reports

    query = {
        "query_id": "sha256:" + "3" * 64,
        "evidence_floor": "O3",
        "min_reporters": 2,
        "source_policy_id": "source-policy:registered-diverse-v1",
    }
    good_source = {
        "active": True,
        "source_id": "source:a",
        "source_control_group_id": "control:a",
        "venue_id": "venue:a",
        "data_family_id": "price:a",
        "transport_id": "api:a",
        "assurance_class": "S3",
    }
    second_source = {
        "active": True,
        "source_id": "source:b",
        "source_control_group_id": "control:b",
        "venue_id": "venue:b",
        "data_family_id": "price:b",
        "transport_id": "api:b",
        "assurance_class": "S3",
    }
    bad_cases = [
        ("missing_dimension", {**second_source, "data_family_id": ""}, "data_family_id"),
        ("source_id_mismatch", {**second_source, "source_id": "source:c"}, "match report source_id"),
    ]

    for _name, bad_source, expected_error in bad_cases:
        reports = [
            {
                "report_id": "sha256:" + "4" * 64,
                "query_id": query["query_id"],
                "reporter_id": "reporter:a",
                "source_id": "source:a",
                "price_e8": 100,
                "source_observed_epoch": 10,
                "source_state_at_submit": good_source,
            },
            {
                "report_id": "sha256:" + "5" * 64,
                "query_id": query["query_id"],
                "reporter_id": "reporter:b",
                "source_id": "source:b",
                "price_e8": 101,
                "source_observed_epoch": 10,
                "source_state_at_submit": bad_source,
            },
        ]

        try:
            _aggregate_from_reports(query=query, reports=reports, epoch=11)
        except SystemExit as exc:
            assert expected_error in str(exc)
        else:
            raise AssertionError(f"registered source policy must reject {expected_error}")


def test_registered_independent_policy_rejects_reporter_source_control_overlap() -> None:
    from tools.zenodex_oracle import _aggregate_from_reports

    query = {
        "query_id": "sha256:" + "3" * 64,
        "evidence_floor": "O3",
        "min_reporters": 2,
        "source_policy_id": "source-policy:registered-independent-v1",
    }
    reports = [
        {
            "report_id": "sha256:" + "4" * 64,
            "query_id": query["query_id"],
            "reporter_id": "reporter:a",
            "source_id": "source:a",
            "price_e8": 100,
            "source_observed_epoch": 10,
            "reporter_state_at_submit": {"control_group_id": "control:shared"},
            "source_state_at_submit": {
                "active": True,
                "source_id": "source:a",
                "source_control_group_id": "control:shared",
                "venue_id": "venue:a",
                "data_family_id": "price:a",
                "transport_id": "api:a",
                "assurance_class": "S3",
            },
        },
        {
            "report_id": "sha256:" + "5" * 64,
            "query_id": query["query_id"],
            "reporter_id": "reporter:b",
            "source_id": "source:b",
            "price_e8": 101,
            "source_observed_epoch": 10,
            "reporter_state_at_submit": {"control_group_id": "control:reporter-b"},
            "source_state_at_submit": {
                "active": True,
                "source_id": "source:b",
                "source_control_group_id": "control:source-b",
                "venue_id": "venue:b",
                "data_family_id": "price:b",
                "transport_id": "api:b",
                "assurance_class": "S3",
            },
        },
    ]

    try:
        _aggregate_from_reports(query=query, reports=reports, epoch=11)
    except SystemExit as exc:
        assert "reporter/source control_group overlap" in str(exc)
    else:
        raise AssertionError("registered independent policy must reject reporter/source control overlap")


def test_source_deactivation_blocks_new_reports(tmp_path: Path) -> None:
    home = tmp_path / "oracle"
    query_id = "sha256:" + "7" * 64

    assert _run("--json", "init", "--home", str(home)).returncode == 0
    assert _run("--json", "identity", "create", "--home", str(home)).returncode == 0
    assert (
        _run(
            "--json",
            "query",
            "register",
            "--home",
            str(home),
            "--base-asset",
            "AGRS",
            "--quote-asset",
            "ZDEX",
            "--query-id",
            query_id,
            "--source-policy-id",
            "source-policy:registered-diverse-v1",
            "--min-reporters",
            "1",
            "--report-reward-e8",
            "0",
        ).returncode
        == 0
    )
    assert (
        _run(
            "--json",
            "reporter",
            "register",
            "--home",
            str(home),
            "--query-id",
            query_id,
            "--required-bond-e8",
            "1",
        ).returncode
        == 0
    )
    assert _run("--json", "reporter", "bond", "--home", str(home), "--amount-e8", "1").returncode == 0
    assert (
        _run(
            "--json",
            "source",
            "register",
            "--home",
            str(home),
            "--source-id",
            "source:twap-a",
            "--source-kind",
            "twap",
            "--control-group-id",
            "control:twap-a",
            "--venue-id",
            "venue:twap-a",
            "--data-family-id",
            "price:twap-a",
            "--transport-id",
            "api:twap-a",
            "--query-id",
            query_id,
        ).returncode
        == 0
    )
    deactivated = _run(
        "--json",
        "source",
        "deactivate",
        "--home",
        str(home),
        "--source-id",
        "source:twap-a",
        "--epoch",
        "12",
    )
    submitted = _run(
        "--json",
        "report",
        "submit",
        "--home",
        str(home),
        "--query-id",
        query_id,
        "--price-e8",
        "123",
        "--source-observed-epoch",
        "13",
        "--source-id",
        "source:twap-a",
    )

    assert deactivated.returncode == 0
    assert json.loads(deactivated.stdout)["source"]["active"] is False
    assert submitted.returncode != 0
    assert "not active" in submitted.stderr


def test_replay_rejects_tampered_registered_source_snapshot(tmp_path: Path) -> None:
    home = tmp_path / "oracle"
    query_id = "sha256:" + "9" * 64

    assert _run("--json", "init", "--home", str(home)).returncode == 0
    assert _run("--json", "identity", "create", "--home", str(home)).returncode == 0
    assert (
        _run(
            "--json",
            "query",
            "register",
            "--home",
            str(home),
            "--base-asset",
            "AGRS",
            "--quote-asset",
            "ZDEX",
            "--query-id",
            query_id,
            "--source-policy-id",
            "source-policy:registered-diverse-v1",
            "--min-reporters",
            "1",
            "--report-reward-e8",
            "0",
        ).returncode
        == 0
    )
    assert (
        _run(
            "--json",
            "reporter",
            "register",
            "--home",
            str(home),
            "--query-id",
            query_id,
            "--required-bond-e8",
            "1",
        ).returncode
        == 0
    )
    assert _run("--json", "reporter", "bond", "--home", str(home), "--amount-e8", "1").returncode == 0
    assert (
        _run(
            "--json",
            "source",
            "register",
            "--home",
            str(home),
            "--source-id",
            "source:cex-a",
            "--source-kind",
            "cex",
            "--control-group-id",
            "control:cex-a",
            "--venue-id",
            "venue:cex-a",
            "--data-family-id",
            "price:cex-last-trade",
            "--transport-id",
            "api:https:cex-a",
            "--query-id",
            query_id,
            "--assurance-class",
            "S3",
        ).returncode
        == 0
    )
    assert (
        _run(
            "--json",
            "report",
            "submit",
            "--home",
            str(home),
            "--query-id",
            query_id,
            "--price-e8",
            "123",
            "--source-observed-epoch",
            "10",
            "--source-id",
            "source:cex-a",
        ).returncode
        == 0
    )
    clean = _run("--json", "verify", "local-state", "--home", str(home))
    reports_path = home / "data" / "reports.jsonl"
    report = json.loads(reports_path.read_text(encoding="utf-8").splitlines()[0])
    report["reporter_state_at_submit"]["control_group_id"] = "control:borrowed-reporter"
    report["source_state_at_submit"]["venue_id"] = "venue:borrowed"
    reports_path.write_text(json.dumps(report, sort_keys=True) + "\n", encoding="utf-8")
    tampered = _run("--json", "verify", "local-state", "--home", str(home))
    errors = json.loads(tampered.stdout)["errors"]

    assert clean.returncode == 0
    assert tampered.returncode == 2
    assert any("reporter_state_hash mismatch" in error for error in errors)
    assert any("source_state_hash mismatch" in error for error in errors)


def test_dashboard_snapshot_and_local_api_server(tmp_path: Path) -> None:
    home = tmp_path / "oracle"
    query_id = "sha256:" + "4" * 64

    assert _run("--json", "init", "--home", str(home)).returncode == 0
    assert _run("--json", "identity", "create", "--home", str(home)).returncode == 0
    assert (
        _run(
            "--json",
            "query",
            "register",
            "--home",
            str(home),
            "--base-asset",
            "AGRS",
            "--quote-asset",
            "ZDEX",
            "--query-id",
            query_id,
            "--min-reporters",
            "1",
            "--report-reward-e8",
            "0",
            "--freshness-window-epochs",
            "3",
        ).returncode
        == 0
    )
    assert (
        _run(
            "--json",
            "reporter",
            "register",
            "--home",
            str(home),
            "--query-id",
            query_id,
            "--required-bond-e8",
            "1",
        ).returncode
        == 0
    )
    assert _run("--json", "reporter", "bond", "--home", str(home), "--amount-e8", "1").returncode == 0
    assert (
        _run(
            "--json",
            "report",
            "submit",
            "--home",
            str(home),
            "--query-id",
            query_id,
            "--price-e8",
            "123",
            "--source-observed-epoch",
            "10",
            "--source-id",
            "source:manual",
        ).returncode
        == 0
    )
    aggregate = _run("--json", "aggregate", "build", "--home", str(home), "--query-id", query_id, "--epoch", "11")
    aggregate_id = json.loads(aggregate.stdout)["aggregate_id"]
    assert (
        _run(
            "--json",
            "read",
            "accept",
            "--home",
            str(home),
            "--aggregate-id",
            aggregate_id,
            "--consumer-module",
            "zenodex.zusd",
            "--profile-id",
            "critical-zusd-v1",
        ).returncode
        == 0
    )

    snapshot = _run(
        "--json",
        "dashboard",
        "snapshot",
        "--home",
        str(home),
        "--now-epoch",
        "11",
    )
    snapshot_data = json.loads(snapshot.stdout)

    assert snapshot.returncode == 0
    assert snapshot_data["schema"] == "zeno_oracle.dashboard_snapshot.v1"
    assert snapshot_data["summary"]["feed_status_count"] == 1
    assert snapshot_data["summary"]["accepted_read_count"] == 1
    assert snapshot_data["summary"]["replay_ok"] is True
    assert snapshot_data["feed_statuses"][0]["latest_value_e8"] == 123

    port = _free_port()
    proc = subprocess.Popen(
        [
            sys.executable,
            str(CLI),
            "serve",
            "--home",
            str(home),
            "--host",
            "127.0.0.1",
            "--port",
            str(port),
            "--now-epoch",
            "11",
            "--quiet",
        ],
        cwd=ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    try:
        assert proc.stdout is not None
        ready = json.loads(proc.stdout.readline())
        assert ready["ok"] is True
        assert "/api/oracle/dashboard" in ready["paths"]
        assert "/api/oracle/authority" in ready["paths"]
        base = f"http://127.0.0.1:{port}"
        health = None
        for _attempt in range(20):
            try:
                health = _http_json(f"{base}/api/oracle/health")
                break
            except OSError:
                time.sleep(0.05)
        assert health is not None
        authority = _http_json(f"{base}/api/oracle/authority")
        feeds = _http_json(f"{base}/api/oracle/feeds")
        replay = _http_json(f"{base}/api/oracle/replay")
        dashboard = _http_json(f"{base}/api/oracle/dashboard")

        assert health["ok"] is True
        assert health["production_authority"] is False
        assert authority["status"] == "blocked"
        assert dashboard["authority_status"]["status"] == "blocked"
        assert feeds["count"] == 1
        assert feeds["feed_statuses"][0]["query_id"] == query_id
        assert replay["ok"] is True
        assert dashboard["summary"]["accepted_read_count"] == 1
    finally:
        proc.terminate()
        try:
            proc.wait(timeout=5)
        except subprocess.TimeoutExpired:
            proc.kill()
            proc.wait(timeout=5)


def test_local_api_write_endpoints_are_explicitly_enabled(tmp_path: Path) -> None:
    home = tmp_path / "oracle"
    assert _run("--json", "init", "--home", str(home)).returncode == 0

    disabled_port = _free_port()
    disabled = subprocess.Popen(
        [
            sys.executable,
            str(CLI),
            "serve",
            "--home",
            str(home),
            "--host",
            "127.0.0.1",
            "--port",
            str(disabled_port),
            "--quiet",
        ],
        cwd=ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    try:
        assert disabled.stdout is not None
        disabled_ready = json.loads(disabled.stdout.readline())
        assert disabled_ready["write_paths_enabled"] is False
        status, rejected = _http_post_json(
            f"http://127.0.0.1:{disabled_port}/api/oracle/query/register",
            {"base_asset": "AGRS", "quote_asset": "ZDEX"},
        )
        assert status == 403
        assert rejected["error"] == "write_api_disabled"
    finally:
        disabled.terminate()
        try:
            disabled.wait(timeout=5)
        except subprocess.TimeoutExpired:
            disabled.kill()
            disabled.wait(timeout=5)

    port = _free_port()
    proc = subprocess.Popen(
        [
            sys.executable,
            str(CLI),
            "serve",
            "--home",
            str(home),
            "--host",
            "127.0.0.1",
            "--port",
            str(port),
            "--quiet",
            "--allow-writes",
            "--now-epoch",
            "12",
        ],
        cwd=ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    try:
        assert proc.stdout is not None
        ready = json.loads(proc.stdout.readline())
        assert ready["write_paths_enabled"] is True
        assert "/api/oracle/aggregate/build" in ready["write_paths"]
        assert "/api/oracle/read/accept" in ready["write_paths"]
        assert "/api/oracle/authorization/build" in ready["write_paths"]
        assert "/api/oracle/authorization/build-exact" in ready["write_paths"]
        assert "/api/oracle/dispute/open" in ready["write_paths"]
        assert "/api/oracle/dispute/resolve" in ready["write_paths"]
        assert "/api/oracle/query/fund" in ready["write_paths"]
        assert "/api/oracle/report/submit" in ready["write_paths"]
        assert "/api/oracle/rewards/pay" in ready["write_paths"]
        base = f"http://127.0.0.1:{port}"
        status, headers, options = _http_options_json(f"{base}/api/oracle/report/submit")
        assert status == 200
        assert options["ok"] is True
        assert "POST" in headers["Access-Control-Allow-Methods"]

        status, duplicate_key = _http_post_raw_json(
            f"{base}/api/oracle/identity/create",
            b'{"force":false,"force":true}',
        )
        assert status == 400
        assert "duplicate JSON key: force" in duplicate_key["error"]
        status, nonfinite = _http_post_raw_json(
            f"{base}/api/oracle/identity/create",
            b'{"force":NaN}',
        )
        assert status == 400
        assert "non-finite JSON constant: NaN" in nonfinite["error"]

        status, identity = _http_post_json(f"{base}/api/oracle/identity/create", {"force": True})
        assert status == 200
        assert identity["reporter_id"].startswith("sha256:")
        status, query = _http_post_json(
            f"{base}/api/oracle/query/register",
            {
                "base_asset": "AGRS",
                "quote_asset": "ZDEX",
                "query_id": "sha256:" + "1" * 64,
                "source_policy_id": "source-policy:registered-diverse-v1",
                "min_reporters": 1,
                "report_reward_e8": 17,
            },
        )
        assert status == 200
        query_id = query["query_id"]
        status, funded = _http_post_json(
            f"{base}/api/oracle/query/fund",
            {"query_id": query_id, "amount_e8": 20},
        )
        assert status == 200
        assert funded["reward_budget_e8"] == 20
        status, reporter = _http_post_json(
            f"{base}/api/oracle/reporter/register",
            {"query_id": query_id, "required_bond_e8": 1},
        )
        assert status == 200
        assert reporter["reporter_id"] == identity["reporter_id"]
        status, bond = _http_post_json(f"{base}/api/oracle/reporter/bond", {"amount_e8": 1})
        assert status == 200
        assert bond["active"] is True
        status, source = _http_post_json(
            f"{base}/api/oracle/source/register",
            {
                "source_id": "source:cex-a",
                "source_kind": "cex",
                "control_group_id": "control:cex-a",
                "venue_id": "venue:cex-a",
                "data_family_id": "price:cex-last-trade",
                "transport_id": "api:https:cex-a",
                "asset_class": "crypto",
                "query_id": query_id,
                "assurance_class": "S3",
            },
        )
        assert status == 200
        assert source["source"]["source_control_group_id"] == "control:cex-a"
        status, submitted = _http_post_json(
            f"{base}/api/oracle/report/submit",
            {
                "query_id": query_id,
                "price_e8": 123456789,
                "source_observed_epoch": 12,
                "source_id": "source:cex-a",
            },
        )
        assert status == 200
        assert submitted["report_id"].startswith("sha256:")
        assert submitted["reward_e8"] == 17
        assert submitted["pending_rewards_e8"] == 17

        status, dispute = _http_post_json(
            f"{base}/api/oracle/dispute/open",
            {
                "report_id": submitted["report_id"],
                "reporter_id": identity["reporter_id"],
                "bond_e8": 3,
                "reason": "api-test",
                "epoch": 12,
            },
        )
        assert status == 200
        assert dispute["dispute"]["status"] == "open"
        status, resolved = _http_post_json(
            f"{base}/api/oracle/dispute/resolve",
            {
                "dispute_id": dispute["dispute_id"],
                "outcome": "rejected",
                "epoch": 13,
            },
        )
        assert status == 200
        assert resolved["dispute"]["status"] == "rejected"

        status, aggregate = _http_post_json(
            f"{base}/api/oracle/aggregate/build",
            {"query_id": query_id, "epoch": 12},
        )
        assert status == 200
        assert aggregate["aggregate"]["value_e8"] == 123456789
        status, read = _http_post_json(
            f"{base}/api/oracle/read/accept",
            {
                "aggregate_id": aggregate["aggregate_id"],
                "consumer_module": "zenodex.zusd",
                "profile_id": "critical-zusd-v1",
            },
        )
        assert status == 200
        assert read["read"]["value_e8"] == 123456789
        assert read["read"]["expires_at_epoch"] == 14
        from tools.zenodex_oracle import _receipt_graph_from_read

        expected_graph_root = _receipt_graph_from_read(home, read["read"])["receipt_graph_root"]
        runtime_action = {
            "consumer_module": "zenodex.zusd",
            "action_kind": "mint",
            "action_id": "sha256:" + "2" * 64,
            "action_facts_hash": "sha256:" + "3" * 64,
            "pre_state_hash": "sha256:" + "4" * 64,
            "profile_id": "critical-zusd-v1",
            "query_id": query_id,
            "runtime_notional_value_e8": 123456789,
            "runtime_value_e8": 123456789,
            "now_epoch": 12,
            "max_freshness_window_epochs": 2,
        }
        economic_envelope = _exact_economic_envelope(runtime_action)

        status, missing_runtime = _http_post_json(
            f"{base}/api/oracle/authorization/build-exact",
            {
                "read_id": read["read_id"],
                "expected_receipt_graph_root": expected_graph_root,
                "economic_envelope": economic_envelope,
            },
        )
        assert status == 400
        assert missing_runtime["error"] == "runtime_action is required for API authorization build"

        status, missing_root = _http_post_json(
            f"{base}/api/oracle/authorization/build-exact",
            {
                "read_id": read["read_id"],
                "runtime_action": runtime_action,
                "economic_envelope": economic_envelope,
            },
        )
        assert status == 400
        assert missing_root["error"] == (
            "expected_receipt_graph_root is required for API authorization build"
        )

        status, missing_envelope = _http_post_json(
            f"{base}/api/oracle/authorization/build-exact",
            {
                "read_id": read["read_id"],
                "runtime_action": runtime_action,
                "expected_receipt_graph_root": expected_graph_root,
            },
        )
        assert status == 400
        assert missing_envelope["error"] == (
            "economic_envelope is required for exact authorization build"
        )

        status, caller_selected_envelope_id = _http_post_json(
            f"{base}/api/oracle/authorization/build-exact",
            {
                "read_id": read["read_id"],
                "runtime_action": runtime_action,
                "expected_receipt_graph_root": expected_graph_root,
                "economic_envelope": economic_envelope,
                "economic_envelope_id": "econ:caller-selected",
            },
        )
        assert status == 400
        assert caller_selected_envelope_id["error"] == (
            "exact authorization request has unknown fields: economic_envelope_id"
        )

        # A one-atom runtime mismatch must fail before creating any durable
        # authorization receipt or log row.
        mismatched_runtime = dict(runtime_action)
        mismatched_runtime["runtime_value_e8"] = 123456790
        status, rejected = _http_post_json(
            f"{base}/api/oracle/authorization/build-exact",
            {
                "read_id": read["read_id"],
                "runtime_action": mismatched_runtime,
                "expected_receipt_graph_root": expected_graph_root,
                "economic_envelope": economic_envelope,
            },
        )
        assert status == 400
        assert rejected["error"] == "runtime_action runtime_value_e8 does not match accepted read"
        assert not (home / "data" / "oracle_authorizations.jsonl").exists()
        assert list((home / "receipts" / "authorizations").glob("*.json")) == []

        weak_envelope = dict(economic_envelope)
        weak_envelope["attack_cost_floor_e8"] = 0
        status, rejected_envelope = _http_post_json(
            f"{base}/api/oracle/authorization/build-exact",
            {
                "read_id": read["read_id"],
                "runtime_action": runtime_action,
                "expected_receipt_graph_root": expected_graph_root,
                "economic_envelope": weak_envelope,
            },
        )
        assert status == 400
        assert "attack_cost_floor_below_required_margin" in rejected_envelope["error"]
        assert not (home / "data" / "oracle_authorizations.jsonl").exists()
        assert list((home / "receipts" / "authorizations").glob("*.json")) == []

        understated_envelope = dict(economic_envelope)
        understated_envelope["notional_value_e8"] = 123456788
        status, rejected_understatement = _http_post_json(
            f"{base}/api/oracle/authorization/build-exact",
            {
                "read_id": read["read_id"],
                "runtime_action": runtime_action,
                "expected_receipt_graph_root": expected_graph_root,
                "economic_envelope": understated_envelope,
            },
        )
        assert status == 400
        assert rejected_understatement["error"] == (
            "generated OracleAuthorization failed semantic binding check"
        )
        assert not (home / "data" / "oracle_authorizations.jsonl").exists()
        assert list((home / "receipts" / "authorizations").glob("*.json")) == []

        status, authorization = _http_post_json(
            f"{base}/api/oracle/authorization/build-exact",
            {
                "read_id": read["read_id"],
                "runtime_action": runtime_action,
                "expected_receipt_graph_root": expected_graph_root,
                "economic_envelope": economic_envelope,
            },
        )
        assert status == 200
        assert authorization["authorization"]["value_e8"] == 123456789
        assert authorization["receipt_graph"]["receipt_graph_root"].startswith("sha256:")
        assert authorization["runtime_action"] == runtime_action
        assert authorization["economic_envelope"] == economic_envelope
        assert authorization["authorization"]["economic_envelope_id"] == _semantic_hash(
            "zenodex.oracle.economic_envelope.v1",
            economic_envelope,
        )
        assert authorization["runtime_binding_source"] == "consumer_runtime_exact"
        assert authorization["idempotent_replay"] is False

        authorization_log = home / "data" / "oracle_authorizations.jsonl"
        authorization_log_before_rejections = authorization_log.read_bytes()
        receipt_bytes_before_rejections = {
            path.name: path.read_bytes()
            for path in (home / "receipts" / "authorizations").glob("*.json")
        }

        status, rejected_root = _http_post_json(
            f"{base}/api/oracle/authorization/build-exact",
            {
                "read_id": read["read_id"],
                "runtime_action": runtime_action,
                "expected_receipt_graph_root": "sha256:" + "0" * 64,
                "economic_envelope": economic_envelope,
            },
        )
        assert status == 400
        assert rejected_root["error"] == "receipt_graph_root does not match expected root"
        assert authorization_log.read_bytes() == authorization_log_before_rejections
        assert {
            path.name: path.read_bytes()
            for path in (home / "receipts" / "authorizations").glob("*.json")
        } == receipt_bytes_before_rejections

        status, repeated_authorization = _http_post_json(
            f"{base}/api/oracle/authorization/build-exact",
            {
                "read_id": read["read_id"],
                "runtime_action": runtime_action,
                "expected_receipt_graph_root": expected_graph_root,
                "economic_envelope": economic_envelope,
            },
        )
        assert status == 200
        assert repeated_authorization["authorization_id"] == authorization["authorization_id"]
        assert repeated_authorization["idempotent_replay"] is True
        assert authorization_log.read_bytes() == authorization_log_before_rejections
        verified = _http_json(
            f"{base}/api/oracle/verify-receipt?id={urllib.parse.quote(authorization['authorization_id'])}"
        )
        assert verified["ok"] is True
        assert verified["receipt_check"]["receipt_kind"] == "oracle_authorization_bundle"
        assert verified["receipt_check"]["typed_ok"] is True
        assert verified["receipt_check"]["economic_envelope_ok"] is True

        status, paid = _http_post_json(f"{base}/api/oracle/rewards/pay", {"amount_e8": 5})
        assert status == 200
        assert paid["paid_now_e8"] == 5
        assert paid["rewards"]["pending_rewards_e8"] == 12
        reward_verified = _http_json(
            f"{base}/api/oracle/verify-receipt?id={urllib.parse.quote(paid['reward_receipt']['reward_entry_id'])}"
        )
        assert reward_verified["ok"] is True
        assert reward_verified["receipt_check"]["receipt_kind"] == "reward_ledger_entry"

        dashboard = _http_json(f"{base}/api/oracle/dashboard")
        assert dashboard["summary"]["query_count"] == 1
        assert dashboard["summary"]["reporter_count"] == 1
        assert dashboard["summary"]["source_count"] == 1
        assert dashboard["summary"]["report_count"] == 1
        assert dashboard["summary"]["aggregate_count"] == 1
        assert dashboard["summary"]["accepted_read_count"] == 1
        assert dashboard["summary"]["authorization_count"] == 1
        assert dashboard["summary"]["pending_rewards_e8"] == 12
        assert dashboard["summary"]["paid_rewards_e8"] == 5
        assert dashboard["recent_reward_receipts"][-1]["reward_entry_id"] == paid["reward_receipt"]["reward_entry_id"]
        assert dashboard["recent_slash_receipts"] == []
        assert len(dashboard["disputes"]) == 1
        assert dashboard["disputes"][0]["status"] == "rejected"
    finally:
        proc.terminate()
        try:
            proc.wait(timeout=5)
        except subprocess.TimeoutExpired:
            proc.kill()
            proc.wait(timeout=5)


def test_report_dry_run_accepts_integer_prices_and_rejects_decimal_prices() -> None:
    good = _run(
        "--json",
        "report",
        "dry-run",
        "--query-id",
        "sha256:" + "2" * 64,
        "--price-e8",
        "123456789",
        "--source-observed-epoch",
        "42",
        "--reporter-id",
        "reporter:alice",
        "--source-id",
        "source:manual",
    )
    bad = _run(
        "--json",
        "report",
        "dry-run",
        "--query-id",
        "sha256:" + "2" * 64,
        "--price-e8",
        "1.23",
        "--source-observed-epoch",
        "42",
        "--reporter-id",
        "reporter:alice",
        "--source-id",
        "source:manual",
    )

    assert good.returncode == 0
    assert json.loads(good.stdout)["dry_run"] is True
    assert bad.returncode != 0
    assert "must be a positive integer" in bad.stderr


def test_o3_aggregate_rejects_duplicate_declared_sources() -> None:
    from tools.zenodex_oracle import _aggregate_from_reports

    query = {
        "query_id": "sha256:" + "3" * 64,
        "evidence_floor": "O3",
        "min_reporters": 2,
        "source_policy_id": "source-policy:declared-diverse-v1",
    }
    reports = [
        {
            "report_id": "sha256:" + "4" * 64,
            "query_id": query["query_id"],
            "reporter_id": "reporter:a",
            "source_id": "source:same",
            "price_e8": 100,
            "source_observed_epoch": 10,
        },
        {
            "report_id": "sha256:" + "5" * 64,
            "query_id": query["query_id"],
            "reporter_id": "reporter:b",
            "source_id": "source:same",
            "price_e8": 101,
            "source_observed_epoch": 10,
        },
    ]

    try:
        _aggregate_from_reports(query=query, reports=reports, epoch=11)
    except SystemExit as exc:
        assert "distinct source_id" in str(exc)
    else:
        raise AssertionError("duplicate declared source IDs should be rejected for O3 aggregates")


def test_o3_aggregate_rejects_duplicate_reporter_control_groups() -> None:
    from tools.zenodex_oracle import _aggregate_from_reports

    query = {
        "query_id": "sha256:" + "3" * 64,
        "evidence_floor": "O3",
        "min_reporters": 2,
        "source_policy_id": "source-policy:declared-diverse-v1",
    }
    reports = [
        {
            "report_id": "sha256:" + "4" * 64,
            "query_id": query["query_id"],
            "reporter_id": "reporter:a",
            "source_id": "source:a",
            "price_e8": 100,
            "source_observed_epoch": 10,
            "reporter_state_at_submit": {"control_group_id": "operator:same"},
        },
        {
            "report_id": "sha256:" + "5" * 64,
            "query_id": query["query_id"],
            "reporter_id": "reporter:b",
            "source_id": "source:b",
            "price_e8": 101,
            "source_observed_epoch": 10,
            "reporter_state_at_submit": {"control_group_id": "operator:same"},
        },
    ]

    try:
        _aggregate_from_reports(query=query, reports=reports, epoch=11)
    except SystemExit as exc:
        assert "control_group_id" in str(exc)
    else:
        raise AssertionError("duplicate reporter control groups should be rejected for O3 aggregates")


def test_replay_rejects_aggregate_with_duplicate_declared_sources(tmp_path: Path) -> None:
    from tools.zenodex_oracle import _verify_aggregates

    home = tmp_path / "oracle"
    (home / "data").mkdir(parents=True)
    query_id = "sha256:" + "3" * 64
    query = {
        "query_id": query_id,
        "evidence_floor": "O3",
        "min_reporters": 2,
        "source_policy_id": "source-policy:declared-diverse-v1",
    }
    reports = [
        {
            "report_id": "sha256:" + "4" * 64,
            "query_id": query_id,
            "reporter_id": "reporter:a",
            "source_id": "source:same",
            "price_e8": 100,
            "source_observed_epoch": 10,
        },
        {
            "report_id": "sha256:" + "5" * 64,
            "query_id": query_id,
            "reporter_id": "reporter:b",
            "source_id": "source:same",
            "price_e8": 101,
            "source_observed_epoch": 10,
        },
    ]
    aggregate = {
        "aggregate_id": "sha256:" + "6" * 64,
        "query_id": query_id,
        "included_report_ids": [report["report_id"] for report in reports],
        "aggregate_epoch": 11,
    }
    (home / "data" / "aggregates.jsonl").write_text(
        json.dumps(aggregate, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    errors: list[str] = []

    _verify_aggregates(home, reports, [query], errors)

    assert any("distinct source_id" in error for error in errors)


def test_policy_change_quarantines_old_aggregate(tmp_path: Path) -> None:
    home = tmp_path / "oracle"
    query_id = "sha256:" + "d" * 64

    assert _run("--json", "init", "--home", str(home)).returncode == 0
    assert _run("--json", "identity", "create", "--home", str(home)).returncode == 0
    assert (
        _run(
            "--json",
            "query",
            "register",
            "--home",
            str(home),
            "--base-asset",
            "AGRS",
            "--quote-asset",
            "ZDEX",
            "--query-id",
            query_id,
            "--min-reporters",
            "1",
            "--report-reward-e8",
            "0",
        ).returncode
        == 0
    )
    assert (
        _run(
            "--json",
            "reporter",
            "register",
            "--home",
            str(home),
            "--query-id",
            query_id,
            "--required-bond-e8",
            "1",
        ).returncode
        == 0
    )
    assert _run("--json", "reporter", "bond", "--home", str(home), "--amount-e8", "1").returncode == 0
    assert (
        _run(
            "--json",
            "report",
            "submit",
            "--home",
            str(home),
            "--query-id",
            query_id,
            "--price-e8",
            "123",
            "--source-observed-epoch",
            "10",
            "--source-id",
            "source:manual",
        ).returncode
        == 0
    )
    built = _run("--json", "aggregate", "build", "--home", str(home), "--query-id", query_id, "--epoch", "11")
    aggregate = json.loads(built.stdout)["aggregate"]

    changed_policy = _run(
        "--json",
        "query",
        "register",
        "--home",
        str(home),
        "--base-asset",
        "AGRS",
        "--quote-asset",
        "ZDEX",
        "--query-id",
        query_id,
        "--min-reporters",
        "1",
        "--report-reward-e8",
        "0",
        "--freshness-window-epochs",
        "9",
        "--force",
    )
    accepted = _run(
        "--json",
        "read",
        "accept",
        "--home",
        str(home),
        "--aggregate-id",
        aggregate["aggregate_id"],
        "--consumer-module",
        "zenodex.zusd",
        "--profile-id",
        "critical-zusd-v1",
    )
    replay = _run("--json", "verify", "local-state", "--home", str(home))
    replay_data = json.loads(replay.stdout)

    assert built.returncode == 0
    assert aggregate["query_policy_root"].startswith("sha256:")
    assert changed_policy.returncode == 0
    assert accepted.returncode != 0
    assert "query_policy_root does not match active query" in accepted.stderr
    assert replay.returncode == 2
    assert any("query_policy_root does not match replay" in error for error in replay_data["errors"])


def test_reporter_register_bond_submit_rewards_and_replay(tmp_path: Path) -> None:
    home = tmp_path / "oracle"
    query_id = "sha256:" + "c" * 64

    assert _run("--json", "init", "--home", str(home)).returncode == 0
    assert _run("--json", "identity", "create", "--home", str(home)).returncode == 0
    registered = _run(
        "--json",
        "reporter",
        "register",
        "--home",
        str(home),
        "--query-id",
        query_id,
        "--required-bond-e8",
        "1000",
        "--epoch",
        "7",
    )
    underbonded = _run(
        "--json",
        "report",
        "submit",
        "--home",
        str(home),
        "--query-id",
        query_id,
        "--price-e8",
        "123456789",
        "--source-observed-epoch",
        "42",
        "--source-id",
        "source:manual",
    )
    bonded = _run("--json", "reporter", "bond", "--home", str(home), "--amount-e8", "1000")
    submitted = _run(
        "--json",
        "report",
        "submit",
        "--home",
        str(home),
        "--query-id",
        query_id,
        "--price-e8",
        "123456789",
        "--source-observed-epoch",
        "42",
        "--source-id",
        "source:manual",
        "--reward-e8",
        "17",
    )
    rewards = _run("--json", "rewards", "inspect", "--home", str(home))
    replay = _run("--json", "verify", "local-state", "--home", str(home))

    assert registered.returncode == 0
    assert json.loads(registered.stdout)["active"] is False
    assert underbonded.returncode != 0
    assert "not active" in underbonded.stderr
    assert bonded.returncode == 0
    assert json.loads(bonded.stdout)["active"] is True
    assert submitted.returncode == 0
    submitted_data = json.loads(submitted.stdout)
    assert submitted_data["sequence"] == 1
    assert submitted_data["pending_rewards_e8"] == 17
    assert rewards.returncode == 0
    assert json.loads(rewards.stdout)["rewards"]["accepted_report_count"] == 1
    assert replay.returncode == 0
    assert json.loads(replay.stdout)["ok"] is True


def test_reporter_list_deactivate_and_sequence_replay(tmp_path: Path) -> None:
    home = tmp_path / "oracle"
    query_id = "sha256:" + "6" * 64

    assert _run("--json", "init", "--home", str(home)).returncode == 0
    assert _run("--json", "identity", "create", "--home", str(home)).returncode == 0
    assert (
        _run(
            "--json",
            "query",
            "register",
            "--home",
            str(home),
            "--base-asset",
            "AGRS",
            "--quote-asset",
            "ZDEX",
            "--query-id",
            query_id,
            "--report-reward-e8",
            "0",
        ).returncode
        == 0
    )
    registered = _run(
        "--json",
        "reporter",
        "register",
        "--home",
        str(home),
        "--query-id",
        query_id,
        "--required-bond-e8",
        "1",
    )
    reporter_id = json.loads(registered.stdout)["reporter_id"]
    assert _run("--json", "reporter", "bond", "--home", str(home), "--amount-e8", "1").returncode == 0
    assert (
        _run(
            "--json",
            "report",
            "submit",
            "--home",
            str(home),
            "--query-id",
            query_id,
            "--price-e8",
            "123",
            "--source-observed-epoch",
            "10",
            "--source-id",
            "source:manual",
        ).returncode
        == 0
    )
    listed = _run("--json", "reporter", "list", "--home", str(home), "--active-only")
    deactivated = _run(
        "--json",
        "reporter",
        "deactivate",
        "--home",
        str(home),
        "--reporter-id",
        reporter_id,
        "--epoch",
        "11",
    )
    blocked = _run(
        "--json",
        "report",
        "submit",
        "--home",
        str(home),
        "--query-id",
        query_id,
        "--price-e8",
        "124",
        "--source-observed-epoch",
        "11",
        "--source-id",
        "source:manual",
    )

    assert listed.returncode == 0
    assert json.loads(listed.stdout)["count"] == 1
    assert deactivated.returncode == 0
    assert json.loads(deactivated.stdout)["reporter"]["active"] is False
    assert blocked.returncode != 0
    assert "not active" in blocked.stderr

    registry_path = home / "data" / "reporter_registry.json"
    registry = json.loads(registry_path.read_text(encoding="utf-8"))
    registry["reporters"][reporter_id]["last_sequence"] = 0
    registry_path.write_text(json.dumps(registry, sort_keys=True, indent=2) + "\n", encoding="utf-8")
    replay = _run("--json", "verify", "local-state", "--home", str(home))
    replay_data = json.loads(replay.stdout)

    assert replay.returncode == 2
    assert any("last_sequence does not match replay" in error for error in replay_data["errors"])


def test_reporter_register_rejects_unknown_query_when_local_registry_exists(tmp_path: Path) -> None:
    home = tmp_path / "oracle"
    known_query = "sha256:" + "e" * 64
    unknown_query = "sha256:" + "f" * 64

    assert _run("--json", "init", "--home", str(home)).returncode == 0
    assert _run("--json", "identity", "create", "--home", str(home)).returncode == 0
    assert (
        _run(
            "--json",
            "query",
            "register",
            "--home",
            str(home),
            "--base-asset",
            "AGRS",
            "--quote-asset",
            "ZDEX",
            "--query-id",
            known_query,
        ).returncode
        == 0
    )

    rejected = _run(
        "--json",
        "reporter",
        "register",
        "--home",
        str(home),
        "--query-id",
        unknown_query,
    )

    assert rejected.returncode != 0
    assert "not in the local query registry" in rejected.stderr


def test_query_reward_budget_funding_payout_and_replay(tmp_path: Path) -> None:
    home = tmp_path / "oracle"
    query_id = "sha256:" + "a" * 64

    assert _run("--json", "init", "--home", str(home)).returncode == 0
    assert _run("--json", "identity", "create", "--home", str(home)).returncode == 0
    assert (
        _run(
            "--json",
            "query",
            "register",
            "--home",
            str(home),
            "--base-asset",
            "AGRS",
            "--quote-asset",
            "ZDEX",
            "--query-id",
            query_id,
            "--report-reward-e8",
            "17",
        ).returncode
        == 0
    )
    assert (
        _run(
            "--json",
            "reporter",
            "register",
            "--home",
            str(home),
            "--query-id",
            query_id,
            "--required-bond-e8",
            "100",
        ).returncode
        == 0
    )
    assert _run("--json", "reporter", "bond", "--home", str(home), "--amount-e8", "100").returncode == 0

    unfunded = _run(
        "--json",
        "report",
        "submit",
        "--home",
        str(home),
        "--query-id",
        query_id,
        "--price-e8",
        "100",
        "--source-observed-epoch",
        "2",
        "--source-id",
        "source:manual",
    )
    funded = _run("--json", "query", "fund", "--home", str(home), "--query-id", query_id, "--amount-e8", "50")
    submitted = _run(
        "--json",
        "report",
        "submit",
        "--home",
        str(home),
        "--query-id",
        query_id,
        "--price-e8",
        "100",
        "--source-observed-epoch",
        "2",
        "--source-id",
        "source:manual",
    )
    paid = _run("--json", "rewards", "pay", "--home", str(home), "--amount-e8", "5")
    replay = _run("--json", "verify", "local-state", "--home", str(home))
    shown = _run("--json", "query", "show", "--home", str(home), "--query-id", query_id)

    assert unfunded.returncode != 0
    assert "reward budget is insufficient" in unfunded.stderr
    assert funded.returncode == 0
    assert submitted.returncode == 0
    assert json.loads(submitted.stdout)["reward_e8"] == 17
    assert paid.returncode == 0
    paid_data = json.loads(paid.stdout)
    reward_receipt_path = Path(paid_data["receipt_path"])
    reward_receipt = json.loads(reward_receipt_path.read_text(encoding="utf-8"))
    reward_receipt_check = _run("--json", "verify", "receipt", str(reward_receipt_path))
    tampered_reward_receipt = dict(reward_receipt)
    tampered_reward_receipt["pending_rewards_e8"] = int(tampered_reward_receipt["pending_rewards_e8"]) + 1
    tampered_reward_receipt_path = tmp_path / "tampered_reward_receipt.json"
    tampered_reward_receipt_path.write_text(json.dumps(tampered_reward_receipt), encoding="utf-8")
    tampered_reward_receipt_check = _run("--json", "verify", "receipt", str(tampered_reward_receipt_path))

    assert paid_data["rewards"]["pending_rewards_e8"] == 12
    assert paid_data["rewards"]["paid_rewards_e8"] == 5
    assert paid_data["reward_receipt"]["reward_entry_id"].startswith("sha256:")
    assert reward_receipt_check.returncode == 0
    assert json.loads(reward_receipt_check.stdout)["receipt_kind"] == "reward_ledger_entry"
    assert tampered_reward_receipt_check.returncode == 2
    assert "reward_entry_id mismatch" in json.loads(tampered_reward_receipt_check.stdout)["errors"]
    assert replay.returncode == 0
    assert json.loads(replay.stdout)["ok"] is True
    assert json.loads(shown.stdout)["query"]["reward_spent_e8"] == 17

    reward_receipt_path.write_text(json.dumps(tampered_reward_receipt), encoding="utf-8")
    replay_tampered_reward_receipt = _run("--json", "verify", "local-state", "--home", str(home))
    replay_tampered_reward_receipt_data = json.loads(replay_tampered_reward_receipt.stdout)
    assert replay_tampered_reward_receipt.returncode == 2
    assert any(
        "stored receipt" in error and "reward_entry_id mismatch" in error
        for error in replay_tampered_reward_receipt_data["errors"]
    )
    reward_receipt_path.write_text(json.dumps(reward_receipt), encoding="utf-8")

    orphan_reward_receipt = {
        "schema": "zeno_oracle.reward_ledger_entry.v1",
        "reporter_id": "reporter:unknown",
        "pending_rewards_e8": 1,
        "paid_rewards_e8": 0,
        "accepted_report_count": 1,
        "slash_debt_e8": 0,
        "slashed_rewards_e8": 0,
        "production_authority": False,
    }
    orphan_reward_receipt["reward_entry_id"] = _semantic_hash(
        "zeno_oracle.reward_ledger_entry.v1",
        orphan_reward_receipt,
    )
    orphan_reward_receipt_path = (
        home
        / "receipts"
        / "rewards"
        / f"{orphan_reward_receipt['reward_entry_id'].replace(':', '_')}.json"
    )
    orphan_reward_receipt_path.write_text(json.dumps(orphan_reward_receipt), encoding="utf-8")
    replay_orphan_reward_receipt = _run("--json", "verify", "local-state", "--home", str(home))
    replay_orphan_reward_receipt_data = json.loads(replay_orphan_reward_receipt.stdout)
    assert replay_orphan_reward_receipt.returncode == 2
    assert any("references unknown reward reporter" in error for error in replay_orphan_reward_receipt_data["errors"])
    orphan_reward_receipt_path.unlink()


def test_aggregate_build_uses_report_receipts_and_replay_rejects_tamper(tmp_path: Path) -> None:
    home = tmp_path / "oracle"
    query_id = "sha256:" + "9" * 64

    assert _run("--json", "init", "--home", str(home)).returncode == 0
    assert _run("--json", "identity", "create", "--home", str(home)).returncode == 0
    assert (
        _run(
            "--json",
            "query",
            "register",
            "--home",
            str(home),
            "--base-asset",
            "AGRS",
            "--quote-asset",
            "ZDEX",
            "--query-id",
            query_id,
            "--min-reporters",
            "1",
            "--reward-budget-e8",
            "100",
            "--report-reward-e8",
            "7",
        ).returncode
        == 0
    )
    assert (
        _run(
            "--json",
            "reporter",
            "register",
            "--home",
            str(home),
            "--query-id",
            query_id,
            "--required-bond-e8",
            "1",
        ).returncode
        == 0
    )
    assert _run("--json", "reporter", "bond", "--home", str(home), "--amount-e8", "1").returncode == 0
    assert (
        _run(
            "--json",
            "report",
            "submit",
            "--home",
            str(home),
            "--query-id",
            query_id,
            "--price-e8",
            "123",
            "--source-observed-epoch",
            "10",
            "--source-id",
            "source:manual",
        ).returncode
        == 0
    )
    built = _run("--json", "aggregate", "build", "--home", str(home), "--query-id", query_id, "--epoch", "11")
    aggregate = json.loads(built.stdout)["aggregate"]
    accepted = _run(
        "--json",
        "read",
        "accept",
        "--home",
        str(home),
        "--aggregate-id",
        aggregate["aggregate_id"],
        "--consumer-module",
        "zenodex.zusd",
        "--profile-id",
        "critical-zusd-v1",
    )
    read = json.loads(accepted.stdout)["read"]
    report_receipt = json.loads((home / "data" / "reports.jsonl").read_text(encoding="utf-8").splitlines()[0])
    report_receipt_path = tmp_path / "report_receipt.json"
    aggregate_receipt_path = tmp_path / "aggregate_receipt.json"
    read_receipt_path = tmp_path / "read_receipt.json"
    report_receipt_path.write_text(json.dumps(report_receipt), encoding="utf-8")
    aggregate_receipt_path.write_text(json.dumps(aggregate), encoding="utf-8")
    read_receipt_path.write_text(json.dumps(read), encoding="utf-8")
    report_receipt_check = _run("--json", "verify", "receipt", str(report_receipt_path))
    aggregate_receipt_check = _run("--json", "validator", "receipt", str(aggregate_receipt_path))
    read_receipt_check = _run("--json", "verify", "receipt", str(read_receipt_path))
    tampered_report = dict(report_receipt)
    tampered_report["price_e8"] = 124
    tampered_report_path = tmp_path / "tampered_report_receipt.json"
    tampered_report_path.write_text(json.dumps(tampered_report), encoding="utf-8")
    tampered_report_check = _run("--json", "verify", "receipt", str(tampered_report_path))
    aggregate_without_policy_root = dict(aggregate)
    aggregate_without_policy_root.pop("query_policy_root")
    aggregate_without_policy_root["aggregate_id"] = _semantic_hash(
        "zeno_oracle.aggregate.v1",
        {
            key: value
            for key, value in aggregate_without_policy_root.items()
            if key != "aggregate_id"
        },
    )
    aggregate_without_policy_root_path = tmp_path / "aggregate_without_policy_root.json"
    aggregate_without_policy_root_path.write_text(
        json.dumps(aggregate_without_policy_root),
        encoding="utf-8",
    )
    aggregate_without_policy_root_check = _run(
        "--json",
        "validator",
        "receipt",
        str(aggregate_without_policy_root_path),
    )
    authorized = _run(
        "--json",
        "authorization",
        "build",
        "--home",
        str(home),
        "--read-id",
        read["read_id"],
        "--action-kind",
        "mint",
        "--action-id",
        "sha256:" + "7" * 64,
        "--action-facts-hash",
        "sha256:" + "6" * 64,
        "--pre-state-hash",
        "sha256:" + "5" * 64,
        "--now-epoch",
        "10",
    )
    replay_ok = _run("--json", "verify", "local-state", "--home", str(home))

    assert built.returncode == 0
    assert accepted.returncode == 0
    assert report_receipt_check.returncode == 0
    assert json.loads(report_receipt_check.stdout)["receipt_kind"] == "report"
    assert aggregate_receipt_check.returncode == 0
    assert json.loads(aggregate_receipt_check.stdout)["receipt_kind"] == "aggregate"
    assert read_receipt_check.returncode == 0
    assert json.loads(read_receipt_check.stdout)["receipt_kind"] == "accepted_read"
    assert tampered_report_check.returncode == 2
    assert "report_id mismatch" in json.loads(tampered_report_check.stdout)["errors"]
    assert aggregate_without_policy_root_check.returncode == 2
    assert "aggregate query_policy_root must be a sha256 reference" in json.loads(
        aggregate_without_policy_root_check.stdout
    )["errors"]
    assert authorized.returncode == 0
    authorized_data = json.loads(authorized.stdout)
    authorization_bundle = json.loads(Path(authorized_data["receipt_path"]).read_text(encoding="utf-8"))
    authorization = authorized_data["authorization"]
    receipt_graph = authorized_data["receipt_graph"]
    bundle_receipt_path = tmp_path / "authorization_bundle.json"
    bundle_receipt_path.write_text(json.dumps(authorization_bundle), encoding="utf-8")
    bundle_receipt_check = _run("--json", "verify", "receipt", str(bundle_receipt_path))
    graph_receipt_path = tmp_path / "receipt_graph.json"
    graph_receipt_path.write_text(json.dumps(receipt_graph), encoding="utf-8")
    graph_receipt_check = _run("--json", "verify", "receipt", str(graph_receipt_path))
    bundle_with_mismatched_graph = json.loads(json.dumps(authorization_bundle))
    bundle_with_mismatched_graph["receipt_graph"]["query_policy_root"] = "sha256:" + "0" * 64
    bundle_with_mismatched_graph["receipt_graph"]["receipt_graph_root"] = _semantic_hash(
        "zeno_oracle.receipt_graph.v1",
        {
            key: value
            for key, value in bundle_with_mismatched_graph["receipt_graph"].items()
            if key != "receipt_graph_root"
        },
    )
    bundle_with_mismatched_graph_path = tmp_path / "authorization_bundle_mismatched_graph.json"
    bundle_with_mismatched_graph_path.write_text(
        json.dumps(bundle_with_mismatched_graph),
        encoding="utf-8",
    )
    bundle_with_mismatched_graph_check = _run(
        "--json",
        "validator",
        "receipt",
        str(bundle_with_mismatched_graph_path),
    )
    bundle_with_ambiguous_bond = json.loads(json.dumps(authorization_bundle))
    ambiguous_leaf = bundle_with_ambiguous_bond["receipt_graph"][
        "report_leaf_commitments"
    ][0]
    if "bond_amount_e8" in ambiguous_leaf:
        ambiguous_leaf["bond_e8"] = ambiguous_leaf["bond_amount_e8"]
    else:
        ambiguous_leaf["bond_amount_e8"] = ambiguous_leaf["bond_e8"]
    bundle_with_ambiguous_bond["receipt_graph"]["report_leaf_root"] = _semantic_hash(
        "zeno_oracle.report_leaf_root.v1",
        {"reports": bundle_with_ambiguous_bond["receipt_graph"]["report_leaf_commitments"]},
    )
    bundle_with_ambiguous_bond["receipt_graph"]["receipt_graph_root"] = _semantic_hash(
        "zeno_oracle.receipt_graph.v1",
        {
            key: value
            for key, value in bundle_with_ambiguous_bond["receipt_graph"].items()
            if key != "receipt_graph_root"
        },
    )
    bundle_with_ambiguous_bond["authorization"]["receipt_graph_root"] = (
        bundle_with_ambiguous_bond["receipt_graph"]["receipt_graph_root"]
    )
    bundle_with_ambiguous_bond["authorization_id"] = _semantic_hash(
        "zeno_oracle.oracle_authorization.v1",
        bundle_with_ambiguous_bond["authorization"],
    )
    bundle_with_ambiguous_bond_path = tmp_path / "authorization_bundle_ambiguous_bond.json"
    bundle_with_ambiguous_bond_path.write_text(
        json.dumps(bundle_with_ambiguous_bond),
        encoding="utf-8",
    )
    bundle_with_ambiguous_bond_check = _run(
        "--json",
        "validator",
        "receipt",
        str(bundle_with_ambiguous_bond_path),
    )
    graph_without_dispute_root = dict(receipt_graph)
    graph_without_dispute_root.pop("dispute_state_root")
    graph_without_dispute_root["receipt_graph_root"] = _semantic_hash(
        "zeno_oracle.receipt_graph.v1",
        {
            key: value
            for key, value in graph_without_dispute_root.items()
            if key != "receipt_graph_root"
        },
    )
    graph_without_dispute_root_path = tmp_path / "receipt_graph_without_dispute_root.json"
    graph_without_dispute_root_path.write_text(json.dumps(graph_without_dispute_root), encoding="utf-8")
    graph_without_dispute_root_check = _run(
        "--json",
        "validator",
        "receipt",
        str(graph_without_dispute_root_path),
    )
    graph_with_misbound_leaf = json.loads(json.dumps(receipt_graph))
    graph_with_misbound_leaf["report_leaf_commitments"][0]["source_id"] = "source:borrowed"
    graph_with_misbound_leaf["report_leaf_commitments"][0]["source_state_hash"] = "sha256:" + "0" * 64
    graph_with_misbound_leaf["report_leaf_root"] = _semantic_hash(
        "zeno_oracle.report_leaf_root.v1",
        {"reports": graph_with_misbound_leaf["report_leaf_commitments"]},
    )
    graph_with_misbound_leaf["receipt_graph_root"] = _semantic_hash(
        "zeno_oracle.receipt_graph.v1",
        {
            key: value
            for key, value in graph_with_misbound_leaf.items()
            if key != "receipt_graph_root"
        },
    )
    graph_with_misbound_leaf_path = tmp_path / "receipt_graph_with_misbound_leaf.json"
    graph_with_misbound_leaf_path.write_text(json.dumps(graph_with_misbound_leaf), encoding="utf-8")
    graph_with_misbound_leaf_check = _run(
        "--json",
        "validator",
        "receipt",
        str(graph_with_misbound_leaf_path),
    )
    assert aggregate["value_e8"] == 123
    assert aggregate["reporter_count"] == 1
    assert read["value_e8"] == 123
    assert read["consumer_module"] == "zenodex.zusd"
    assert authorization["value_e8"] == 123
    assert authorization["pre_state_hash"] == "sha256:" + "5" * 64
    assert receipt_graph["read_id"] == read["read_id"]
    assert receipt_graph["dispute_state_root"].startswith("sha256:")
    assert receipt_graph["disputed_report_ids"] == []
    assert bundle_receipt_check.returncode == 0
    assert json.loads(bundle_receipt_check.stdout)["receipt_kind"] == "oracle_authorization_bundle"
    assert bundle_with_mismatched_graph_check.returncode == 2
    assert "authorization bundle query_policy_root does not match receipt_graph" in json.loads(
        bundle_with_mismatched_graph_check.stdout
    )["errors"]
    assert bundle_with_ambiguous_bond_check.returncode == 2
    assert any(
        "must contain exactly one bond field" in error
        for error in json.loads(bundle_with_ambiguous_bond_check.stdout)["errors"]
    )
    assert graph_receipt_check.returncode == 0
    assert json.loads(graph_receipt_check.stdout)["receipt_kind"] == "receipt_graph"
    assert graph_without_dispute_root_check.returncode == 2
    assert "receipt graph dispute_state_root must be a sha256 reference" in json.loads(
        graph_without_dispute_root_check.stdout
    )["errors"]
    assert graph_with_misbound_leaf_check.returncode == 2
    graph_with_misbound_leaf_errors = json.loads(graph_with_misbound_leaf_check.stdout)["errors"]
    assert any("source_state_hash mismatch" in error for error in graph_with_misbound_leaf_errors)
    assert any("included_source_ids" in error for error in graph_with_misbound_leaf_errors)
    assert replay_ok.returncode == 0
    status = _run(
        "--json",
        "query",
        "status",
        "--home",
        str(home),
        "--query-id",
        query_id,
        "--now-epoch",
        "11",
    )
    status_data = json.loads(status.stdout)["feed_status"]
    assert status.returncode == 0
    assert "fresh" in status_data["status"]
    assert "devnet-only" in status_data["status"]

    opened = _run(
        "--json",
        "dispute",
        "open",
        "--home",
        str(home),
        "--report-id",
        aggregate["included_report_ids"][0],
        "--reporter-id",
        json.loads((home / "data" / "reports.jsonl").read_text(encoding="utf-8").splitlines()[0])[
            "reporter_id"
        ],
        "--bond-e8",
        "1",
        "--reason",
        "status-check",
    )
    disputed_status = _run(
        "--json",
        "query",
        "status",
        "--home",
        str(home),
        "--query-id",
        query_id,
        "--now-epoch",
        "11",
    )
    assert opened.returncode == 0
    assert "disputed" in json.loads(disputed_status.stdout)["feed_status"]["status"]
    accept_disputed = _run(
        "--json",
        "read",
        "accept",
        "--home",
        str(home),
        "--aggregate-id",
        aggregate["aggregate_id"],
        "--consumer-module",
        "zenodex.zusd",
        "--profile-id",
        "critical-zusd-v1",
    )
    authorize_disputed = _run(
        "--json",
        "authorization",
        "build",
        "--home",
        str(home),
        "--read-id",
        read["read_id"],
        "--action-kind",
        "mint",
        "--action-id",
        "sha256:" + "7" * 64,
        "--action-facts-hash",
        "sha256:" + "6" * 64,
        "--pre-state-hash",
        "sha256:" + "5" * 64,
        "--now-epoch",
        "11",
    )
    assert accept_disputed.returncode != 0
    assert "disputed reports" in accept_disputed.stderr
    assert authorize_disputed.returncode != 0
    assert "disputed reports" in authorize_disputed.stderr
    replay_disputed = _run("--json", "verify", "local-state", "--home", str(home))
    replay_disputed_data = json.loads(replay_disputed.stdout)
    assert replay_disputed.returncode == 2
    assert any(
        "aggregate includes open or upheld disputed reports" in error
        for error in replay_disputed_data["errors"]
    )
    assert any(
        "receipt_graph_root does not match replay" in error
        for error in replay_disputed_data["errors"]
    )

    auth_log_path = home / "data" / "oracle_authorizations.jsonl"
    original_auth_log = auth_log_path.read_text(encoding="utf-8")
    tampered_auth = json.loads(original_auth_log.splitlines()[0])
    tampered_auth["authorization"]["receipt_graph_root"] = "sha256:" + "0" * 64
    auth_log_path.write_text(json.dumps(tampered_auth, sort_keys=True) + "\n", encoding="utf-8")
    replay_auth_bad = _run("--json", "verify", "local-state", "--home", str(home))
    auth_bad_data = json.loads(replay_auth_bad.stdout)

    assert replay_auth_bad.returncode == 2
    assert any(
        "authorization durable state invalid" in error
        and "collision with different durable bundle" in error
        for error in auth_bad_data["errors"]
    )

    auth_log_path.write_text(original_auth_log, encoding="utf-8")
    tampered_auth = json.loads(original_auth_log.splitlines()[0])
    tampered_auth["authorization"]["feed_registry_root"] = "sha256:" + "1" * 64
    auth_log_path.write_text(json.dumps(tampered_auth, sort_keys=True) + "\n", encoding="utf-8")
    replay_root_bad = _run("--json", "verify", "local-state", "--home", str(home))
    root_bad_data = json.loads(replay_root_bad.stdout)

    assert replay_root_bad.returncode == 2
    assert any(
        "authorization durable state invalid" in error
        and "collision with different durable bundle" in error
        for error in root_bad_data["errors"]
    )

    auth_log_path.write_text(original_auth_log, encoding="utf-8")
    report_log_path = home / "data" / "reports.jsonl"
    original_report_log = report_log_path.read_text(encoding="utf-8")
    tampered_report = json.loads(original_report_log.splitlines()[0])
    tampered_report["reporter_state_at_submit"]["control_group_id"] = "operator:tampered"
    report_log_path.write_text(json.dumps(tampered_report, sort_keys=True) + "\n", encoding="utf-8")
    replay_report_leaf_bad = _run("--json", "verify", "local-state", "--home", str(home))
    report_leaf_bad_data = json.loads(replay_report_leaf_bad.stdout)

    assert replay_report_leaf_bad.returncode == 2
    assert any(
        "receipt_graph does not match replay" in error or "receipt graph could not be replayed" in error
        for error in report_leaf_bad_data["errors"]
    )

    report_log_path.write_text(original_report_log, encoding="utf-8")
    log_path = home / "data" / "aggregates.jsonl"
    tampered = json.loads(log_path.read_text(encoding="utf-8").splitlines()[0])
    tampered["value_e8"] = 124
    log_path.write_text(json.dumps(tampered, sort_keys=True) + "\n", encoding="utf-8")
    replay_bad = _run("--json", "verify", "local-state", "--home", str(home))
    data = json.loads(replay_bad.stdout)

    assert replay_bad.returncode == 2
    assert any("value_e8 does not match replay" in error for error in data["errors"])


def test_dispute_upheld_slashes_reporter_and_replay_still_accepts_old_report(tmp_path: Path) -> None:
    home = tmp_path / "oracle"
    query_id = "sha256:" + "b" * 64

    assert _run("--json", "init", "--home", str(home)).returncode == 0
    assert _run("--json", "identity", "create", "--home", str(home)).returncode == 0
    assert (
        _run(
            "--json",
            "query",
            "register",
            "--home",
            str(home),
            "--base-asset",
            "AGRS",
            "--quote-asset",
            "ZDEX",
            "--query-id",
            query_id,
            "--reward-budget-e8",
            "100",
            "--report-reward-e8",
            "17",
        ).returncode
        == 0
    )
    registered = _run(
        "--json",
        "reporter",
        "register",
        "--home",
        str(home),
        "--query-id",
        query_id,
        "--required-bond-e8",
        "100",
    )
    reporter_id = json.loads(registered.stdout)["reporter_id"]
    assert _run("--json", "reporter", "bond", "--home", str(home), "--amount-e8", "100").returncode == 0
    submitted = _run(
        "--json",
        "report",
        "submit",
        "--home",
        str(home),
        "--query-id",
        query_id,
        "--price-e8",
        "100",
        "--source-observed-epoch",
        "2",
        "--source-id",
        "source:manual",
    )
    report_id = json.loads(submitted.stdout)["report_id"]
    opened = _run(
        "--json",
        "dispute",
        "open",
        "--home",
        str(home),
        "--report-id",
        report_id,
        "--reporter-id",
        reporter_id,
        "--bond-e8",
        "10",
        "--reason",
        "bad-source",
        "--epoch",
        "3",
    )
    dispute_id = json.loads(opened.stdout)["dispute_id"]
    listed_open = _run("--json", "dispute", "list", "--home", str(home), "--status", "open")
    shown_open = _run("--json", "dispute", "show", "--home", str(home), "--dispute-id", dispute_id)
    resolved = _run(
        "--json",
        "dispute",
        "resolve",
        "--home",
        str(home),
        "--dispute-id",
        dispute_id,
        "--outcome",
        "upheld",
        "--slash-e8",
        "120",
        "--epoch",
        "4",
    )
    listed_upheld = _run("--json", "dispute", "list", "--home", str(home), "--status", "upheld")
    reporter = _run("--json", "reporter", "show", "--home", str(home))
    rewards = _run("--json", "rewards", "inspect", "--home", str(home))
    replay = _run("--json", "verify", "local-state", "--home", str(home))
    resubmit = _run(
        "--json",
        "report",
        "submit",
        "--home",
        str(home),
        "--query-id",
        query_id,
        "--price-e8",
        "101",
        "--source-observed-epoch",
        "5",
        "--source-id",
        "source:manual",
    )

    assert opened.returncode == 0
    assert listed_open.returncode == 0
    assert shown_open.returncode == 0
    assert json.loads(listed_open.stdout)["count"] == 1
    assert json.loads(shown_open.stdout)["dispute"]["status"] == "open"
    assert resolved.returncode == 0
    assert listed_upheld.returncode == 0
    assert json.loads(listed_upheld.stdout)["count"] == 1
    resolved_data = json.loads(resolved.stdout)
    slash_result = resolved_data["slash_result"]
    slash_receipt_path = Path(resolved_data["slash_receipt_path"])
    slash_receipt = json.loads(slash_receipt_path.read_text(encoding="utf-8"))
    slash_receipt_check = _run("--json", "validator", "receipt", str(slash_receipt_path))
    tampered_slash_receipt = dict(slash_receipt)
    tampered_slash_receipt["slash_debt_e8"] = int(tampered_slash_receipt["slash_debt_e8"]) + 1
    tampered_slash_receipt_path = tmp_path / "tampered_slash_receipt.json"
    tampered_slash_receipt_path.write_text(json.dumps(tampered_slash_receipt), encoding="utf-8")
    tampered_slash_receipt_check = _run("--json", "validator", "receipt", str(tampered_slash_receipt_path))
    assert slash_result["bond_slashed_e8"] == 100
    assert slash_result["pending_reward_slashed_e8"] == 17
    assert slash_result["slash_debt_e8"] == 3
    assert resolved_data["slash_receipt"]["slash_settlement_id"].startswith("sha256:")
    assert slash_receipt_check.returncode == 0
    assert json.loads(slash_receipt_check.stdout)["receipt_kind"] == "slash_settlement"
    assert tampered_slash_receipt_check.returncode == 2
    tampered_slash_errors = json.loads(tampered_slash_receipt_check.stdout)["errors"]
    assert "slash_settlement_id mismatch" in tampered_slash_errors
    assert "slash settlement components do not sum to slash_e8" in tampered_slash_errors

    slash_receipt_path.write_text(json.dumps(tampered_slash_receipt), encoding="utf-8")
    replay_tampered_slash_receipt = _run("--json", "verify", "local-state", "--home", str(home))
    replay_tampered_slash_receipt_data = json.loads(replay_tampered_slash_receipt.stdout)
    assert replay_tampered_slash_receipt.returncode == 2
    assert any(
        "stored receipt" in error and "slash_settlement_id mismatch" in error
        for error in replay_tampered_slash_receipt_data["errors"]
    )
    slash_receipt_path.write_text(json.dumps(slash_receipt), encoding="utf-8")

    orphan_slash_receipt = dict(slash_receipt)
    orphan_slash_receipt["dispute_id"] = "sha256:" + "f" * 64
    orphan_slash_body = dict(orphan_slash_receipt)
    orphan_slash_body.pop("slash_settlement_id", None)
    orphan_slash_receipt["slash_settlement_id"] = _semantic_hash(
        "zeno_oracle.slash_settlement.v1",
        orphan_slash_body,
    )
    orphan_slash_receipt_path = (
        home
        / "receipts"
        / "slashes"
        / f"{orphan_slash_receipt['slash_settlement_id'].replace(':', '_')}.json"
    )
    orphan_slash_receipt_path.write_text(json.dumps(orphan_slash_receipt), encoding="utf-8")
    replay_orphan_slash_receipt = _run("--json", "verify", "local-state", "--home", str(home))
    replay_orphan_slash_receipt_data = json.loads(replay_orphan_slash_receipt.stdout)
    assert replay_orphan_slash_receipt.returncode == 2
    assert any(
        "does not match an upheld dispute resolution" in error
        for error in replay_orphan_slash_receipt_data["errors"]
    )
    orphan_slash_receipt_path.unlink()

    dispute_events = [
        json.loads(line)
        for line in (home / "data" / "disputes.jsonl").read_text(encoding="utf-8").splitlines()
    ]
    resolve_event = next(event for event in dispute_events if event["event"] == "resolve")
    assert resolve_event["slash_result"]["pending_reward_slashed_e8"] == 17
    reporter_data = json.loads(reporter.stdout)["reporter"]
    assert reporter_data["active"] is False
    assert reporter_data["slash_state"] == "slashed"
    reward_data = json.loads(rewards.stdout)["rewards"]
    assert reward_data["pending_rewards_e8"] == 0
    assert reward_data["slashed_rewards_e8"] == 17
    assert replay.returncode == 0
    assert json.loads(replay.stdout)["ok"] is True
    assert resubmit.returncode != 0
    assert "slash_state must be clear" in resubmit.stderr

    rewards_path = home / "data" / "rewards.json"
    tampered_rewards = json.loads(rewards_path.read_text(encoding="utf-8"))
    tampered_rewards["reporters"][reporter_id]["pending_rewards_e8"] = 17
    tampered_rewards["reporters"][reporter_id]["slashed_rewards_e8"] = 0
    rewards_path.write_text(json.dumps(tampered_rewards, sort_keys=True) + "\n", encoding="utf-8")
    replay_tampered_rewards = _run("--json", "verify", "local-state", "--home", str(home))
    tampered_data = json.loads(replay_tampered_rewards.stdout)

    assert replay_tampered_rewards.returncode == 2
    assert any("slashed_rewards_e8 does not match dispute slashes" in error for error in tampered_data["errors"])


def test_authorization_build_rejects_o2_read_by_default(tmp_path: Path) -> None:
    home = tmp_path / "oracle"
    query_id = "sha256:" + "8" * 64

    assert _run("--json", "init", "--home", str(home)).returncode == 0
    assert _run("--json", "identity", "create", "--home", str(home)).returncode == 0
    assert (
        _run(
            "--json",
            "query",
            "register",
            "--home",
            str(home),
            "--base-asset",
            "AGRS",
            "--quote-asset",
            "ZDEX",
            "--query-id",
            query_id,
            "--evidence-floor",
            "O2",
            "--min-reporters",
            "1",
            "--reward-budget-e8",
            "10",
            "--report-reward-e8",
            "1",
        ).returncode
        == 0
    )
    assert (
        _run(
            "--json",
            "reporter",
            "register",
            "--home",
            str(home),
            "--query-id",
            query_id,
            "--required-bond-e8",
            "1",
        ).returncode
        == 0
    )
    assert _run("--json", "reporter", "bond", "--home", str(home), "--amount-e8", "1").returncode == 0
    assert (
        _run(
            "--json",
            "report",
            "submit",
            "--home",
            str(home),
            "--query-id",
            query_id,
            "--price-e8",
            "123",
            "--source-observed-epoch",
            "10",
            "--source-id",
            "source:manual",
        ).returncode
        == 0
    )
    aggregate = json.loads(
        _run("--json", "aggregate", "build", "--home", str(home), "--query-id", query_id).stdout
    )["aggregate"]
    critical_read = _run(
        "--json",
        "read",
        "accept",
        "--home",
        str(home),
        "--aggregate-id",
        aggregate["aggregate_id"],
        "--consumer-module",
        "zenodex.zusd",
        "--profile-id",
        "critical-zusd-v1",
    )
    namespaced_critical_read = _run(
        "--json",
        "read",
        "accept",
        "--home",
        str(home),
        "--aggregate-id",
        aggregate["aggregate_id"],
        "--consumer-module",
        "zenodex.zusd",
        "--profile-id",
        "profile:zusd-critical-o3-v1",
    )
    devnet_read = _run(
        "--json",
        "read",
        "accept",
        "--home",
        str(home),
        "--aggregate-id",
        aggregate["aggregate_id"],
        "--consumer-module",
        "zenodex.zusd",
        "--profile-id",
        "devnet-zusd-v1",
    )
    read = json.loads(devnet_read.stdout)["read"]
    read_receipt_path = tmp_path / "o2_devnet_read.json"
    read_receipt_path.write_text(json.dumps(read), encoding="utf-8")
    read_receipt_check = _run("--json", "verify", "receipt", str(read_receipt_path))
    rejected = _run(
        "--json",
        "authorization",
        "build",
        "--home",
        str(home),
        "--read-id",
        read["read_id"],
        "--action-kind",
        "mint",
        "--action-id",
        "sha256:" + "7" * 64,
        "--action-facts-hash",
        "sha256:" + "6" * 64,
        "--pre-state-hash",
        "sha256:" + "5" * 64,
    )

    assert critical_read.returncode != 0
    assert "below required O3" in critical_read.stderr
    assert namespaced_critical_read.returncode != 0
    assert "below required O3" in namespaced_critical_read.stderr
    assert devnet_read.returncode == 0
    assert read_receipt_check.returncode == 0
    assert rejected.returncode != 0
    assert "below required O3" in rejected.stderr


def test_verify_receipt_rejects_critical_o2_read() -> None:
    body = {
        "schema": "zeno_oracle.accepted_read.v1",
        "aggregate_id": "sha256:" + "1" * 64,
        "query_id": "query:AGRS/ZDEX",
        "consumer_module": "zenodex.zusd",
        "profile_id": "critical-zusd-v1",
        "value_e8": 123,
        "value_hash": _semantic_hash(
            "zenodex.oracle.value.v1",
            {"observed_epoch": 10, "query_id": "query:AGRS/ZDEX", "value_e8": 123},
        ),
        "confidence_e8": 0,
        "deviation_bps": 0,
        "observed_epoch": 10,
        "expires_at_epoch": 11,
        "evidence_class": "O2",
        "production_authority": False,
    }
    payload = {**body, "read_id": _semantic_hash("zeno_oracle.accepted_read.v1", body)}
    from tools.zenodex_oracle import verify_standalone_receipt

    result = verify_standalone_receipt(payload)

    assert result["ok"] is False
    assert "accepted read evidence class O2 is below required O3" in result["errors"]


def test_local_replay_rejects_tampered_report_log_signature(tmp_path: Path) -> None:
    home = tmp_path / "oracle"
    query_id = "sha256:" + "d" * 64

    assert _run("--json", "init", "--home", str(home)).returncode == 0
    assert _run("--json", "identity", "create", "--home", str(home)).returncode == 0
    assert (
        _run(
            "--json",
            "reporter",
            "register",
            "--home",
            str(home),
            "--query-id",
            query_id,
            "--required-bond-e8",
            "1",
        ).returncode
        == 0
    )
    assert _run("--json", "reporter", "bond", "--home", str(home), "--amount-e8", "1").returncode == 0
    assert (
        _run(
            "--json",
            "report",
            "submit",
            "--home",
            str(home),
            "--query-id",
            query_id,
            "--price-e8",
            "100",
            "--source-observed-epoch",
            "2",
            "--source-id",
            "source:manual",
        ).returncode
        == 0
    )

    log_path = home / "data" / "reports.jsonl"
    entry = json.loads(log_path.read_text(encoding="utf-8").splitlines()[0])
    entry["signature"] = "local-dev-sha256:" + "0" * 64
    log_path.write_text(json.dumps(entry, sort_keys=True) + "\n", encoding="utf-8")

    replay = _run("--json", "verify", "local-state", "--home", str(home))
    data = json.loads(replay.stdout)

    assert replay.returncode == 2
    assert data["ok"] is False
    assert any("signature mismatch" in error for error in data["errors"])


def test_verify_authorization_rejects_runtime_value_mismatch(tmp_path: Path) -> None:
    query_id = "sha256:" + "3" * 64
    observed_epoch = 42
    value_e8 = 123456789
    value_hash = _semantic_hash(
        "zenodex.oracle.value.v1",
        {
            "observed_epoch": observed_epoch,
            "query_id": query_id,
            "value_e8": value_e8,
        },
    )
    payload = {
        "authorization": {
            "consumer_module": "zenodex.zusd",
            "action_kind": "mint",
            "action_id": "sha256:" + "4" * 64,
            "action_facts_hash": "sha256:" + "5" * 64,
            "pre_state_hash": "sha256:" + "6" * 64,
            "profile_id": "critical-zusd-v1",
            "query_id": query_id,
            "value_e8": value_e8,
            "value_hash": value_hash,
            "confidence_e8": 10000,
            "deviation_bps": 32,
            "observed_epoch": observed_epoch,
            "expires_at_epoch": 44,
            "feed_id": "feed:agrs-zdex:v1",
            "feed_registry_root": "sha256:" + "7" * 64,
            "query_policy_root": "sha256:" + "8" * 64,
            "source_registry_root": "sha256:" + "9" * 64,
            "reporter_registry_root": "sha256:" + "a" * 64,
            "evidence_class": "O3",
            "economic_envelope_id": "econ:small-notional-v1",
            "receipt_graph_root": "sha256:" + "b" * 64,
        },
        "runtime_action": {
            "consumer_module": "zenodex.zusd",
            "action_kind": "mint",
            "action_id": "sha256:" + "4" * 64,
            "action_facts_hash": "sha256:" + "5" * 64,
            "pre_state_hash": "sha256:" + "6" * 64,
            "profile_id": "critical-zusd-v1",
            "query_id": query_id,
            "runtime_value_e8": value_e8 + 1,
            "now_epoch": 43,
        },
    }
    path = tmp_path / "authorization.json"
    path.write_text(json.dumps(payload), encoding="utf-8")

    proc = _run("--json", "verify", "authorization", str(path))
    validator_proc = _run("--json", "validator", "authorization", str(path))
    data = json.loads(proc.stdout)
    validator_data = json.loads(validator_proc.stdout)

    assert proc.returncode == 2
    assert data["opaque_ok"] is True
    assert data["typed_ok"] is False
    assert "runtime_value_e8 mismatch" in data["typed_errors"]
    assert validator_proc.returncode == 2
    assert validator_data == data
