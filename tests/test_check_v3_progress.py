from __future__ import annotations

import copy
import json
import subprocess
from collections.abc import Callable
from pathlib import Path

import pytest

from tools import check_v3_progress as checker


def _ledger() -> dict[str, object]:
    return json.loads((checker.REPO_ROOT / checker.DEFAULT_LEDGER).read_text(encoding="utf-8"))


def _write(tmp_path: Path, value: object) -> Path:
    path = tmp_path / "progress.json"
    path.write_text(json.dumps(value), encoding="utf-8")
    return path


def _check(tmp_path: Path, value: object, **kwargs: object) -> dict[str, object]:
    return checker.check_v3_progress(
        root=checker.REPO_ROOT,
        ledger_path=_write(tmp_path, value),
        **kwargs,
    )


def _code(report: dict[str, object]) -> str:
    return report["findings"][0]["code"]  # type: ignore[index]


@pytest.fixture(scope="module")
def replay_material() -> tuple[dict[str, object], list[dict[str, str]]]:
    ledger, _, _, trusted_tools = checker._validate_ledger(
        checker.REPO_ROOT,
        checker.REPO_ROOT / checker.DEFAULT_LEDGER,
    )
    return ledger, trusted_tools


def _passing_junit(case_count: int, *, duplicate: bool = False) -> str:
    cases = [
        f'<testcase classname="tests.integration.test_replay" name="test_case_{number:03d}" />'
        for number in range(case_count)
    ]
    if duplicate:
        cases[-1] = cases[0]
    return f'<testsuite tests="{case_count}">{"".join(cases)}</testsuite>'


def _fake_completed(command: list[str]) -> subprocess.CompletedProcess[str]:
    return subprocess.CompletedProcess(command, 0, "", "")


def _fake_replay_run(
    monkeypatch: pytest.MonkeyPatch,
    writer: Callable[[Path], None],
) -> list[dict[str, object]]:
    calls: list[dict[str, object]] = []
    original_run = checker.subprocess.run

    def fake_run(command: list[str], **kwargs: object) -> subprocess.CompletedProcess[str]:
        if command[0] == "git":
            return original_run(command, **kwargs)
        calls.append({"command": command, **kwargs})
        junit_path = Path(command[command.index("--junitxml") + 1])
        writer(junit_path)
        return _fake_completed(command)

    monkeypatch.setattr(checker.subprocess, "run", fake_run)
    return calls


def test_default_derives_pinned_inventory_without_promoting_any_closure() -> None:
    report = checker.check_v3_progress()

    assert report["ok"] is True, report
    inventory = report["baseline_inventory"]
    assert len(inventory["capability_ids"]) == 103
    assert len(inventory["route_ids"]) == 4
    assert len(inventory["exclusions"]) == 4
    assert [task["id"] for task in inventory["tasks"]] == [f"W{number:02d}" for number in range(14)]
    assert all(task["status"] == "OPEN" for task in inventory["tasks"])
    assert inventory["normative_registry"] == {
        "requirement_row_count": 152,
        "target_count": 142,
        "status": "SEPARATE_UNPOOLED",
    }
    assert report["claim_ceiling"] == checker.CLAIM_CEILING
    assert report["closure_gates"] == {
        "capability_closure": "UNAVAILABLE",
        "formal_core_closure": "UNAVAILABLE",
        "whole_product_closure": "UNAVAILABLE",
    }
    assert "completion_percentage" not in report
    assert all(
        value is False
        for key, value in report.items()
        if key
        in {
            "formal_core_complete",
            "whole_value_movement_safe",
            "whole_product_complete",
            "production_promotion",
        }
    )


def test_duplicate_json_and_forged_execution_fields_fail_closed(tmp_path: Path) -> None:
    duplicate = tmp_path / "duplicate.json"
    duplicate.write_text('{"schema":"x","schema":"y"}', encoding="utf-8")
    duplicate_report = checker.check_v3_progress(ledger_path=duplicate)
    assert duplicate_report["ok"] is False
    assert _code(duplicate_report) == "DUPLICATE_JSON_KEY"

    forged = _ledger()
    forged["work_records"][2]["exit_code"] = 0  # type: ignore[index]
    forged_report = _check(tmp_path, forged)
    assert forged_report["ok"] is False
    assert _code(forged_report) == "RECORD_FIELDS"
    assert forged_report["formal_core_complete"] is False


def test_scope_repetition_and_json_command_injection_are_rejected(tmp_path: Path) -> None:
    scope = _ledger()
    scope["work_records"][2]["declared_scope_paths"].pop()  # type: ignore[index]
    scope_report = _check(tmp_path, scope)
    assert scope_report["ok"] is False
    assert _code(scope_report) == "OUT_OF_SCOPE_EDIT"

    repeated = _ledger()
    duplicate = copy.deepcopy(repeated["work_records"][2])  # type: ignore[index]
    duplicate["id"] = "SUPPORT-DUPLICATE-RECEIPT-COPY-20260908"
    repeated["work_records"].append(duplicate)  # type: ignore[index]
    repeated_report = _check(tmp_path, repeated)
    assert repeated_report["ok"] is False
    assert _code(repeated_report) == "REPEATED_SUPPORT_WORK"

    injected = _ledger()
    injected["work_records"][2]["argv"] = ["sh", "-c", "false"]  # type: ignore[index]
    injected_report = _check(tmp_path, injected)
    assert injected_report["ok"] is False
    assert _code(injected_report) == "RECORD_FIELDS"


def test_trusted_tool_and_scope_drift_cannot_be_replayed_as_current(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    tool_drift = _ledger()
    tool_drift["trusted_local_tools"][0]["sha256"] = "0" * 64  # type: ignore[index]
    tool_report = _check(tmp_path, tool_drift)
    assert tool_report["ok"] is False
    assert _code(tool_report) == "TRUSTED_TOOL_DRIFT"

    monkeypatch.setattr(checker, "_working_scope_hash", lambda *_: "0" * 64)
    stale_report = checker.check_v3_progress()
    assert stale_report["ok"] is True, stale_report
    assert stale_report["records"][2]["status"] == "STALE_SOURCE"  # type: ignore[index]
    assert stale_report["formal_core_complete"] is False


def test_only_an_appended_correction_may_repeat_its_exact_subject(tmp_path: Path) -> None:
    corrected = _ledger()
    correction = copy.deepcopy(corrected["work_records"][2])  # type: ignore[index]
    correction["id"] = "CORRECTION-RECEIPT-COPY-20260908"
    correction["kind"] = "CORRECTION"
    correction["supersedes"] = "SUPPORT-RECEIPT-COPY-SIMPLIFICATION-20260908"
    correction["rationale"]["stop_condition"] = (
        "Correct the record wording while retaining the same bounded support subject."
    )
    corrected["work_records"].append(correction)  # type: ignore[index]

    report = _check(tmp_path, corrected)
    assert report["ok"] is True, report
    assert len(report["records"]) == len(_ledger()["work_records"]) + 1
    assert report["formal_core_complete"] is False


def test_trusted_cli_baseline_checks_a_preserved_prefix(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    baseline = _ledger()
    raw = json.dumps(baseline).encode("utf-8")
    original = checker._git_blob

    def baseline_blob(root: Path, commit: str, path: str) -> bytes | None:
        if path == checker.DEFAULT_LEDGER.as_posix():
            return raw
        return original(root, commit, path)

    monkeypatch.setattr(checker, "_git_blob", baseline_blob)
    current = copy.deepcopy(baseline["work_records"])
    history = checker._baseline_history(
        checker.REPO_ROOT,
        checker.REPO_ROOT / checker.DEFAULT_LEDGER,
        current,
        "2f769e7ba2d578b3518f91c882a56430072f7f70",
    )
    assert history["status"] == "PRESERVED"

    current[0]["id"] = "SUPPORT-REWRITTEN-20260908"
    with pytest.raises(checker.ProgressReject, match="trusted baseline prefix") as exc_info:
        checker._baseline_history(
            checker.REPO_ROOT,
            checker.REPO_ROOT / checker.DEFAULT_LEDGER,
            current,
            "2f769e7ba2d578b3518f91c882a56430072f7f70",
        )
    assert exc_info.value.code == "BASELINE_REWRITE"


def test_junit_parser_rejects_empty_and_nonpass_and_normalizes_node_ids(
    tmp_path: Path,
) -> None:
    empty = tmp_path / "empty.xml"
    empty.write_text("<testsuite />", encoding="utf-8")
    with pytest.raises(checker.ProgressReject, match="no testcases") as exc_info:
        checker._junit_inventory(empty)
    assert exc_info.value.code == "EMPTY_JUNIT"

    skipped = tmp_path / "skipped.xml"
    skipped.write_text(
        '<testsuite><testcase classname="tests.integration.test_example" '
        'name="test_case"><skipped type="pytest.xfail" /></testcase></testsuite>',
        encoding="utf-8",
    )
    with pytest.raises(checker.ProgressReject, match="skipped") as exc_info:
        checker._junit_inventory(skipped)
    assert exc_info.value.code == "JUNIT_NONPASS"

    passing = tmp_path / "passing.xml"
    passing.write_text(
        '<testsuite><testcase classname="tests.integration.test_example" '
        'name="test_case" /><testcase '
        'classname="tests.integration.test_example.TestExample" '
        'name="test_method" /></testsuite>',
        encoding="utf-8",
    )
    inventory = checker._junit_inventory(passing)
    expected = (
        "tests/integration/test_example.py::TestExample::test_method\n"
        "tests/integration/test_example.py::test_case\n"
    ).encode("utf-8")
    assert inventory == {
        "test_count": 2,
        "inventory_sha256": checker._sha256(expected),
    }


def test_unknown_replay_gate_and_missing_pair_are_rejected() -> None:
    unknown = checker.check_v3_progress(replay_gate="not-a-gate")
    assert unknown["ok"] is False
    assert _code(unknown) == "UNKNOWN_GATE"

    assert checker.main(["--replay"]) == 1
    assert checker.main(["--gate", "receipt_copy_boundaries_v1"]) == 1


@pytest.mark.parametrize(
    ("mode", "expected_code"),
    [
        ("timeout", "REPLAY_TIMEOUT"),
        ("oserror", "REPLAY_EXECUTION"),
        ("nonzero", "REPLAY_NONZERO"),
    ],
)
def test_replay_process_failures_fail_closed(
    monkeypatch: pytest.MonkeyPatch,
    replay_material: tuple[dict[str, object], list[dict[str, str]]],
    mode: str,
    expected_code: str,
) -> None:
    ledger, trusted_tools = replay_material

    def fake_run(command: list[str], **kwargs: object) -> subprocess.CompletedProcess[str]:
        if mode == "timeout":
            raise subprocess.TimeoutExpired(command, kwargs["timeout"])
        if mode == "oserror":
            raise OSError("synthetic unavailable runner")
        return subprocess.CompletedProcess(command, 1, "", "synthetic failure")

    monkeypatch.setattr(checker.subprocess, "run", fake_run)
    with pytest.raises(checker.ProgressReject) as exc_info:
        checker._replay_gate(
            checker.REPO_ROOT,
            ledger,
            trusted_tools,
            "receipt_copy_boundaries_v1",
        )
    assert exc_info.value.code == expected_code


@pytest.mark.parametrize(
    ("payload", "expected_code"),
    [
        ("<broken", "MALFORMED_JUNIT"),
        ("<testsuite />", "EMPTY_JUNIT"),
        (
            '<testsuite><testcase classname="tests.integration.test_replay" '
            'name="test_case"><skipped /></testcase></testsuite>',
            "JUNIT_NONPASS",
        ),
        (
            '<testsuite><testcase classname="tests.integration.test_replay" '
            'name="test_case"><skipped type="pytest.xfail" /></testcase></testsuite>',
            "JUNIT_NONPASS",
        ),
        (
            '<testsuite><testcase classname="tests.integration.test_replay" '
            'name="test_case"><failure /></testcase></testsuite>',
            "JUNIT_NONPASS",
        ),
        (
            '<testsuite><testcase classname="tests.integration.test_replay" '
            'name="test_case"><error /></testcase></testsuite>',
            "JUNIT_NONPASS",
        ),
        (
            '<testsuite failures="1"><testcase '
            'classname="tests.integration.test_replay" name="test_case" /></testsuite>',
            "JUNIT_NONPASS",
        ),
        (
            '<testsuite errors="1"><testcase '
            'classname="tests.integration.test_replay" name="test_case" /></testsuite>',
            "JUNIT_NONPASS",
        ),
        (
            '<testsuite skipped="1"><testcase '
            'classname="tests.integration.test_replay" name="test_case" /></testsuite>',
            "JUNIT_NONPASS",
        ),
        (
            "<testsuite><error /></testsuite>",
            "JUNIT_NONPASS",
        ),
        ("<testsuite><failure /></testsuite>", "JUNIT_NONPASS"),
        ("<testsuite><skipped /></testsuite>", "JUNIT_NONPASS"),
    ],
)
def test_replay_rejects_malformed_and_contradicted_junit(
    monkeypatch: pytest.MonkeyPatch,
    replay_material: tuple[dict[str, object], list[dict[str, str]]],
    payload: str,
    expected_code: str,
) -> None:
    ledger, trusted_tools = replay_material
    _fake_replay_run(monkeypatch, lambda path: path.write_text(payload, encoding="utf-8"))

    with pytest.raises(checker.ProgressReject) as exc_info:
        checker._replay_gate(
            checker.REPO_ROOT,
            ledger,
            trusted_tools,
            "receipt_copy_boundaries_v1",
        )
    assert exc_info.value.code == expected_code


def test_replay_requires_its_fresh_junit_not_an_old_artifact(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    replay_material: tuple[dict[str, object], list[dict[str, str]]],
) -> None:
    (tmp_path / "old-replay.xml").write_text(_passing_junit(164), encoding="utf-8")
    ledger, trusted_tools = replay_material
    _fake_replay_run(monkeypatch, lambda _path: None)

    with pytest.raises(checker.ProgressReject) as exc_info:
        checker._replay_gate(
            checker.REPO_ROOT,
            ledger,
            trusted_tools,
            "receipt_copy_boundaries_v1",
        )
    assert exc_info.value.code == "MISSING_FILE"


def test_replay_rejects_wrong_count_inventory_and_duplicate_nodes(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    replay_material: tuple[dict[str, object], list[dict[str, str]]],
) -> None:
    ledger, trusted_tools = replay_material

    _fake_replay_run(
        monkeypatch,
        lambda path: path.write_text(_passing_junit(1), encoding="utf-8"),
    )
    with pytest.raises(checker.ProgressReject) as exc_info:
        checker._replay_gate(
            checker.REPO_ROOT,
            ledger,
            trusted_tools,
            "receipt_copy_boundaries_v1",
        )
    assert exc_info.value.code == "REPLAY_TEST_COUNT"

    monkeypatch.undo()
    _fake_replay_run(
        monkeypatch,
        lambda path: path.write_text(_passing_junit(164), encoding="utf-8"),
    )
    with pytest.raises(checker.ProgressReject) as exc_info:
        checker._replay_gate(
            checker.REPO_ROOT,
            ledger,
            trusted_tools,
            "receipt_copy_boundaries_v1",
        )
    assert exc_info.value.code == "REPLAY_INVENTORY"

    monkeypatch.undo()
    _fake_replay_run(
        monkeypatch,
        lambda path: path.write_text(_passing_junit(164, duplicate=True), encoding="utf-8"),
    )
    with pytest.raises(checker.ProgressReject) as exc_info:
        checker._replay_gate(
            checker.REPO_ROOT,
            ledger,
            trusted_tools,
            "receipt_copy_boundaries_v1",
        )
    assert exc_info.value.code == "DUPLICATE_JUNIT_NODE"


@pytest.mark.parametrize("mutation", ["pre_source", "pre_support", "post_checker", "post_support"])
def test_replay_rejects_pre_and_post_source_scope_and_checker_drift(
    monkeypatch: pytest.MonkeyPatch,
    replay_material: tuple[dict[str, object], list[dict[str, str]]],
    tmp_path: Path,
    mutation: str,
) -> None:
    ledger, trusted_tools = replay_material
    original_source_hashes = checker._source_hashes
    original_scope_hash = checker._working_scope_hash
    runner_calls = 0

    def source_hashes(root: Path, paths: object) -> dict[str, str]:
        result = original_source_hashes(root, paths)
        if mutation == "pre_source" and runner_calls == 0:
            result[next(iter(result))] = "0" * 64
        if mutation == "post_checker" and runner_calls == 1:
            result["tools/check_v3_progress.py"] = "0" * 64
        return result

    def scope_hash(root: Path, gate_id: str) -> str:
        if mutation == "pre_support" and runner_calls == 0:
            return "0" * 64
        if mutation == "post_support" and runner_calls == 1:
            return "0" * 64
        return original_scope_hash(root, gate_id)

    def fake_run(command: list[str], **_kwargs: object) -> subprocess.CompletedProcess[str]:
        nonlocal runner_calls
        runner_calls += 1
        junit_path = Path(command[command.index("--junitxml") + 1])
        junit_path.write_text(_passing_junit(164), encoding="utf-8")
        return _fake_completed(command)

    monkeypatch.setattr(checker, "_source_hashes", source_hashes)
    monkeypatch.setattr(checker, "_working_scope_hash", scope_hash)
    sample = tmp_path / "drift.xml"
    sample.write_text(_passing_junit(164), encoding="utf-8")
    monkeypatch.setitem(
        checker.GATE_CATALOG["receipt_copy_boundaries_v1"],
        "expected_inventory_sha256",
        checker._junit_inventory(sample)["inventory_sha256"],
    )
    monkeypatch.setattr(checker.subprocess, "run", fake_run)

    with pytest.raises(checker.ProgressReject) as exc_info:
        checker._replay_gate(
            checker.REPO_ROOT,
            ledger,
            trusted_tools,
            "receipt_copy_boundaries_v1",
        )
    assert exc_info.value.code == "REPLAY_SOURCE_DRIFT"
    assert runner_calls == (0 if mutation.startswith("pre_") else 1)


def test_controlled_replay_uses_fixed_argv_and_leaves_closures_false(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path: Path,
) -> None:
    sample = tmp_path / "passing.xml"
    sample.write_text(_passing_junit(164), encoding="utf-8")
    expected = checker._junit_inventory(sample)
    gate = checker.GATE_CATALOG["receipt_copy_boundaries_v1"]
    monkeypatch.setitem(gate, "expected_inventory_sha256", expected["inventory_sha256"])
    calls = _fake_replay_run(
        monkeypatch,
        lambda path: path.write_text(_passing_junit(164), encoding="utf-8"),
    )

    report = checker.check_v3_progress(replay_gate="receipt_copy_boundaries_v1")

    assert report["ok"] is True, report
    assert report["replay"]["status"] == "SUPPORT_REPLAY_VERIFIED"  # type: ignore[index]
    assert calls[0]["command"][:7] == [
        checker.sys.executable,
        "-m",
        "pytest",
        "-q",
        "-p",
        "no:cacheprovider",
        "--junitxml",
    ]
    assert "--ledger" not in calls[0]["command"]
    assert "--root" not in calls[0]["command"]
    assert calls[0]["cwd"] == checker.REPO_ROOT
    assert calls[0]["shell"] is False
    assert calls[0]["stdin"] == subprocess.DEVNULL
    assert calls[0]["timeout"] == 180
    assert calls[0]["env"] == checker._fixed_environment()
    assert report["claim_ceiling"] == {
        "formal_core_complete": False,
        "whole_value_movement_safe": False,
        "production_promotion": False,
        "whole_product_complete": False,
        "closed_value_movement_gate_count": 0,
    }
    assert report["formal_core_complete"] is False
    assert report["whole_value_movement_safe"] is False
    assert report["whole_product_complete"] is False
    assert report["production_promotion"] is False


def test_active_correction_replays_the_unsuperseded_record(
    monkeypatch: pytest.MonkeyPatch,
    replay_material: tuple[dict[str, object], list[dict[str, str]]],
    tmp_path: Path,
) -> None:
    ledger, _ = replay_material
    corrected = copy.deepcopy(ledger)
    correction = copy.deepcopy(corrected["work_records"][2])
    correction["id"] = "CORRECTION-RECEIPT-COPY-REPLAY-20260908"
    correction["kind"] = "CORRECTION"
    correction["supersedes"] = "SUPPORT-RECEIPT-COPY-SIMPLIFICATION-20260908"
    correction["rationale"]["stop_condition"] = (
        "Preserve the same replay subject after a wording correction."
    )
    corrected["work_records"].append(correction)
    ledger_path = _write(tmp_path, corrected)
    replay_ledger, _, _, trusted_tools = checker._validate_ledger(checker.REPO_ROOT, ledger_path)
    sample = tmp_path / "correction.xml"
    sample.write_text(_passing_junit(164), encoding="utf-8")
    monkeypatch.setitem(
        checker.GATE_CATALOG["receipt_copy_boundaries_v1"],
        "expected_inventory_sha256",
        checker._junit_inventory(sample)["inventory_sha256"],
    )
    _fake_replay_run(
        monkeypatch,
        lambda path: path.write_text(_passing_junit(164), encoding="utf-8"),
    )

    replay = checker._replay_gate(
        checker.REPO_ROOT,
        replay_ledger,
        trusted_tools,
        "receipt_copy_boundaries_v1",
    )
    assert replay["status"] == "SUPPORT_REPLAY_VERIFIED"


def test_ancestor_symlink_and_wrong_source_bindings_are_rejected(
    tmp_path: Path,
) -> None:
    root = tmp_path / "root"
    outside = tmp_path / "outside"
    root.mkdir()
    outside.mkdir()
    (outside / "payload.txt").write_text("outside", encoding="utf-8")
    (root / "nested").symlink_to(outside, target_is_directory=True)
    with pytest.raises(checker.ProgressReject) as exc_info:
        checker._working_blob(root, "nested/payload.txt")
    assert exc_info.value.code == "PATH_ESCAPE"

    acceptance = _ledger()
    acceptance["work_records"][2]["acceptance_contract"]["sha256"] = "0" * 64  # type: ignore[index]
    acceptance_report = _check(tmp_path, acceptance)
    assert acceptance_report["ok"] is False
    assert _code(acceptance_report) == "ACCEPTANCE_CONTRACT"

    review = _ledger()
    review["work_records"][2]["review_binding"]["reviewed_subject_commit"] = "0" * 40  # type: ignore[index]
    review_report = _check(tmp_path, review)
    assert review_report["ok"] is False
    assert _code(review_report) == "REVIEW_BINDING"


def test_immutable_inventory_decodes_the_exact_bytes_that_were_hashed(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    immutable_inputs = _ledger()["immutable_inputs"]
    plan_path = checker.REPO_ROOT / "docs/research/ZENODEX_WHOLE_PROGRAM_PLAN_V3.json"
    manifest_path = checker.REPO_ROOT / "docs/research/ZENODEX_M6_CAPABILITY_MANIFEST_V1.json"
    tampered_plan = json.loads(plan_path.read_text(encoding="utf-8"))
    tampered_manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    for lanes in (
        tampered_plan["requirements_floor"]["lanes"],
        tampered_manifest["lanes"],
    ):
        capabilities = lanes[0]["capabilities"]
        capabilities[capabilities.index("generic_transfer")] = "tampered_transfer"
    staged = {
        plan_path: json.dumps(tampered_plan).encode("utf-8"),
        manifest_path: json.dumps(tampered_manifest).encode("utf-8"),
    }
    reads: dict[Path, int] = {}
    original_read = checker._read_regular

    def staged_read(path: Path, **kwargs: object) -> bytes:
        reads[path] = reads.get(path, 0) + 1
        if reads[path] == 2 and path in staged:
            return staged[path]
        return original_read(path, **kwargs)

    monkeypatch.setattr(checker, "_read_regular", staged_read)
    inventory = checker._derive_inventory(checker.REPO_ROOT, immutable_inputs)

    assert "ASSET_TRANSFER:generic_transfer" in inventory["capability_ids"]
    assert "ASSET_TRANSFER:tampered_transfer" not in inventory["capability_ids"]
    assert reads[plan_path] == 1
    assert reads[manifest_path] == 1


def test_rename_observations_apply_each_side_file_extension(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    before = b"def preserved_before_name() -> None:\n    return None\n"
    after = b"plain text after rename\n"

    def historical_blob(_root: Path, commit: str, path: str) -> bytes | None:
        if (commit, path) == ("a" * 40, "subject_before.py"):
            return before
        if (commit, path) == ("b" * 40, "subject_after.txt"):
            return after
        return None

    monkeypatch.setattr(checker, "_git_blob", historical_blob)
    observations = checker._change_observations(
        checker.REPO_ROOT,
        "a" * 40,
        "b" * 40,
        [
            {
                "status": "R",
                "before_path": "subject_before.py",
                "after_path": "subject_after.txt",
            }
        ],
    )

    assert observations[0]["before"]["ast"]["status"] == "PYTHON"
    assert observations[0]["before"]["ast"]["function_count"] == 1
    assert observations[0]["after"]["ast"]["status"] == "NOT_APPLICABLE"
