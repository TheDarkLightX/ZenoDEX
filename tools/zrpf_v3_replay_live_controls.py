"""Host-boundary negative controls for the retained ZRPF V3 replay binary."""

from __future__ import annotations

import importlib
import json
import os
import shutil
import tempfile
from dataclasses import dataclass
from pathlib import Path
from typing import Any

_MODULE_PREFIX = "tools." if __package__ else ""
support = importlib.import_module(f"{_MODULE_PREFIX}zrpf_v3_replay_evidence_support")
process_runner = importlib.import_module(f"{_MODULE_PREFIX}zrpf_v3_replay_process")

MAX_REJECT_OUTPUT = 64 * 1024
REJECTION_FIELDS = {
    "context",
    "error_code",
    "ok",
    "schema",
    "status",
    "verifier_code",
}


@dataclass(frozen=True)
class ExpectedReject:
    case_id: str
    error_code: str
    context: str


def run_negative_controls(
    command_path: str,
    pass_fds: tuple[int, ...],
    env: dict[str, str],
    target_directory: Path,
) -> list[dict[str, Any]]:
    with tempfile.TemporaryDirectory(
        prefix="zrpf-replay-neg-",
        dir=target_directory,
    ) as raw:
        root = Path(raw)
        return [
            _altered_leaf(command_path, pass_fds, env, root),
            _swapped_l1(command_path, pass_fds, env, root),
            _extra_inventory(command_path, pass_fds, env, root),
            _missing_inventory(command_path, pass_fds, env, root),
            _receipt_symlink(command_path, pass_fds, env, root),
            _receipt_fifo(command_path, pass_fds, env, root),
            _directory_symlink(command_path, pass_fds, env, root),
            _reject(
                command_path,
                pass_fds,
                [],
                env,
                ExpectedReject("no_arguments", "usage", "replay"),
            ),
        ]


def _altered_leaf(
    command_path: str,
    pass_fds: tuple[int, ...],
    env: dict[str, str],
    root: Path,
) -> dict[str, Any]:
    case = _copy_receipts(root, "altered")
    path = case / support.RECEIPTS[0][0]
    altered = bytearray(path.read_bytes())
    altered[0] ^= 1
    path.write_bytes(altered)
    expected = ExpectedReject(
        "altered_leaf",
        "receipt_artifact_binding",
        support.RECEIPTS[0][0],
    )
    return _reject(command_path, pass_fds, [str(case)], env, expected)


def _swapped_l1(
    command_path: str,
    pass_fds: tuple[int, ...],
    env: dict[str, str],
    root: Path,
) -> dict[str, Any]:
    case = _copy_receipts(root, "swapped")
    left = case / support.RECEIPTS[4][0]
    right = case / support.RECEIPTS[5][0]
    temporary = case / "swap.tmp"
    left.rename(temporary)
    right.rename(left)
    temporary.rename(right)
    expected = ExpectedReject(
        "swapped_l1",
        "receipt_artifact_binding",
        support.RECEIPTS[4][0],
    )
    return _reject(command_path, pass_fds, [str(case)], env, expected)


def _extra_inventory(
    command_path: str,
    pass_fds: tuple[int, ...],
    env: dict[str, str],
    root: Path,
) -> dict[str, Any]:
    case = _copy_receipts(root, "extra")
    (case / "extra").write_bytes(b"x")
    expected = ExpectedReject("extra_inventory", "bundle_inventory", "replay")
    return _reject(command_path, pass_fds, [str(case)], env, expected)


def _missing_inventory(
    command_path: str,
    pass_fds: tuple[int, ...],
    env: dict[str, str],
    root: Path,
) -> dict[str, Any]:
    case = _copy_receipts(root, "missing")
    (case / support.RECEIPTS[-1][0]).unlink()
    expected = ExpectedReject("missing_inventory", "bundle_inventory", "replay")
    return _reject(command_path, pass_fds, [str(case)], env, expected)


def _receipt_symlink(
    command_path: str,
    pass_fds: tuple[int, ...],
    env: dict[str, str],
    root: Path,
) -> dict[str, Any]:
    case = _copy_receipts(root, "symlink")
    path = case / support.RECEIPTS[0][0]
    path.unlink()
    path.symlink_to(support.RECEIPT_DIRECTORY / support.RECEIPTS[0][0])
    expected = ExpectedReject(
        "receipt_symlink",
        "receipt_artifact",
        support.RECEIPTS[0][0],
    )
    return _reject(command_path, pass_fds, [str(case)], env, expected)


def _receipt_fifo(
    command_path: str,
    pass_fds: tuple[int, ...],
    env: dict[str, str],
    root: Path,
) -> dict[str, Any]:
    case = _copy_receipts(root, "fifo")
    path = case / support.RECEIPTS[0][0]
    path.unlink()
    os.mkfifo(path)
    expected = ExpectedReject(
        "receipt_fifo",
        "receipt_artifact",
        support.RECEIPTS[0][0],
    )
    return _reject(command_path, pass_fds, [str(case)], env, expected)


def _directory_symlink(
    command_path: str,
    pass_fds: tuple[int, ...],
    env: dict[str, str],
    root: Path,
) -> dict[str, Any]:
    case = _copy_receipts(root, "directory-target")
    link = root / "directory-link"
    link.symlink_to(case, target_is_directory=True)
    expected = ExpectedReject("directory_symlink", "bundle_directory", "replay")
    return _reject(command_path, pass_fds, [str(link)], env, expected)


def _copy_receipts(root: Path, label: str) -> Path:
    destination = root / label
    shutil.copytree(support.RECEIPT_DIRECTORY, destination)
    return destination


def _reject(
    command_path: str,
    pass_fds: tuple[int, ...],
    arguments: list[str],
    env: dict[str, str],
    expected: ExpectedReject,
) -> dict[str, Any]:
    process = process_runner.run_bounded(
        process_runner.ProcessRequest(
            command=(command_path, *arguments),
            cwd=support.REPO_ROOT,
            env=env,
            timeout_seconds=30,
            output_limit_bytes=MAX_REJECT_OUTPUT,
            profile=process_runner.ProcessProfile.REPLAY,
            pass_fds=pass_fds,
        )
    )
    if process.returncode != 1:
        raise RuntimeError("negative control exit code mismatch")
    if process.stdout:
        raise RuntimeError("negative control emitted stdout")
    record = support.strict_json_loads(process.stderr)
    if not isinstance(record, dict) or set(record) != REJECTION_FIELDS or any(
        (
            record.get("ok") is not False,
            record.get("status") != "rejected",
            record.get("error_code") != expected.error_code,
            record.get("context") != expected.context,
        )
    ):
        raise RuntimeError("negative control rejection mismatch")
    canonical = (
        json.dumps(record, sort_keys=True, separators=(",", ":"), ensure_ascii=True)
        + "\n"
    ).encode("ascii")
    if process.stderr != canonical:
        raise RuntimeError("negative control rejection was not canonical")
    return {
        "case_id": expected.case_id,
        "context": expected.context,
        "error_code": expected.error_code,
        "passed": True,
    }
