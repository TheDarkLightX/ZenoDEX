#!/usr/bin/env python3
from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
import sys
from pathlib import Path
from typing import Any, Iterable, Mapping

REPO_ROOT = Path(__file__).resolve().parents[1]
DEFAULT_MANIFEST = REPO_ROOT / "tools" / "runtime_shell_assurance_manifest.json"
MAX_JSON_BYTES = 4 * 1024 * 1024

REQUIRED_SOLVERS = ("z3", "cvc5")
REQUIRED_SOURCE_PATHS = (
    "src/kernels/dex/perp_epoch_isolated_v3.yaml",
    "generated/perp_python/perp_epoch_isolated_v3_ref.py",
    "src/kernels/dex/perp_epoch_clearinghouse_2p_v0_1.yaml",
    "src/kernels/dex/perp_epoch_clearinghouse_3p_transfer_v0_1.yaml",
    "src/kernels/dex/proof_mining_manager_v1.yaml",
    "src/kernels/dex/dex_global_conservation_v1.yaml",
    "src/kernels/python/perp_epoch_isolated_v3_adapter.py",
    "src/kernels/python/perp_epoch_clearinghouse_2p_v0_1_adapter.py",
    "src/kernels/python/perp_epoch_clearinghouse_3p_transfer_v0_1_adapter.py",
    "src/kernels/python/proof_mining_manager_v1_adapter.py",
    "src/kernels/python/dex_global_conservation_v1_adapter.py",
    "src/core/oracle_current_dispute_status_v1.py",
    "src/integration/perp_engine.py",
    "src/integration/zeno_oracle_authorization.py",
    "tests/kernels/test_python_adapter_wrappers.py",
    "tests/core/test_perp_v2/test_oracle_equiv.py",
    "tests/core/test_perp_v2/test_parity_with_generated_ref.py",
    "tests/kernels/test_perp_epoch_isolated_v3_generated_ref_sync.py",
    "tests/kernels/test_proof_mining_manager_v1_adapter.py",
    "tests/kernels/test_runtime_shell_adapters.py",
    "tests/core/test_oracle_current_dispute_status_v1.py",
    "tests/integration/test_oracle_authorization_semantic_binding.py",
    "tests/integration/test_perp_engine.py",
    "tests/integration/test_perp_engine_clearinghouse_np_oracle_authorization.py",
    "tests/integration/test_perp_engine_oracle_authorization.py",
    "tests/integration/test_perp_engine_partial_liquidate.py",
    "tools/zenodex_oracle_aggregate_adapter.py",
    "tests/test_zenodex_oracle_aggregate_adapter.py",
    "tools/run_runtime_shell_assurance_gate.sh",
    "tools/check_runtime_shell_assurance_manifest.py",
)
REQUIRED_MODELS = (
    (
        "perp_epoch_isolated_v3",
        "src/kernels/dex/perp_epoch_isolated_v3.yaml",
        "src.kernels.python.perp_epoch_isolated_v3_adapter:make_adapter",
    ),
    (
        "perp_epoch_clearinghouse_2p_v0_1",
        "src/kernels/dex/perp_epoch_clearinghouse_2p_v0_1.yaml",
        "src.kernels.python.perp_epoch_clearinghouse_2p_v0_1_adapter:make_adapter",
    ),
    (
        "perp_epoch_clearinghouse_3p_transfer_v0_1",
        "src/kernels/dex/perp_epoch_clearinghouse_3p_transfer_v0_1.yaml",
        "src.kernels.python.perp_epoch_clearinghouse_3p_transfer_v0_1_adapter:make_adapter",
    ),
    (
        "proof_mining_manager_v1",
        "src/kernels/dex/proof_mining_manager_v1.yaml",
        "src.kernels.python.proof_mining_manager_v1_adapter:make_adapter",
    ),
    (
        "dex_global_conservation_v1",
        "src/kernels/dex/dex_global_conservation_v1.yaml",
        "src.kernels.python.dex_global_conservation_v1_adapter:make_adapter",
    ),
)
REQUIRED_REGRESSION_TESTS = (
    "tests/core/test_perp_v2/test_oracle_equiv.py",
    "tests/core/test_perp_v2/test_parity_with_generated_ref.py",
    "tests/kernels/test_perp_epoch_isolated_v3_generated_ref_sync.py",
    "tests/kernels/test_python_adapter_wrappers.py",
    "tests/kernels/test_proof_mining_manager_v1_adapter.py",
    "tests/kernels/test_runtime_shell_adapters.py",
    "tests/core/test_oracle_current_dispute_status_v1.py",
    "tests/integration/test_oracle_authorization_semantic_binding.py",
    "tests/integration/test_perp_engine.py",
    "tests/integration/test_perp_engine_clearinghouse_np_oracle_authorization.py",
    "tests/integration/test_perp_engine_oracle_authorization.py",
    "tests/integration/test_perp_engine_partial_liquidate.py",
    "tests/test_zenodex_oracle_aggregate_adapter.py",
)


class ManifestError(RuntimeError):
    pass


def _require(condition: bool, message: str) -> None:
    if not condition:
        raise ManifestError(message)


def _as_dict(obj: Any, *, ctx: str) -> Mapping[str, Any]:
    _require(type(obj) is dict, f"{ctx}: expected exact object")
    return obj


def _as_list(obj: Any, *, ctx: str) -> list[Any]:
    _require(type(obj) is list, f"{ctx}: expected array")
    return obj


def _as_str(obj: Any, *, ctx: str) -> str:
    _require(type(obj) is str and bool(obj), f"{ctx}: expected non-empty string")
    return obj


def _require_json_bool(value: object, *, ctx: str) -> bool:
    if isinstance(value, bool):
        return value
    raise ManifestError(f"{ctx}: expected bool")


def _require_json_int(value: object, *, ctx: str) -> int:
    if isinstance(value, int) and not isinstance(value, bool):
        return value
    raise ManifestError(f"{ctx}: expected int")


def _require_true(value: object, *, ctx: str) -> None:
    _require(_require_json_bool(value, ctx=ctx) is True, f"{ctx}=false")


def _reject_duplicate_keys(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise ManifestError(f"duplicate JSON key: {key}")
        result[key] = value
    return result


def _reject_json_constant(value: str) -> None:
    raise ManifestError(f"non-standard JSON constant: {value}")


def _load_json(path: Path) -> Any:
    try:
        size = path.stat().st_size
        _require(size <= MAX_JSON_BYTES, f"JSON file too large: {path}: {size}>{MAX_JSON_BYTES}")
        return json.loads(
            path.read_text(encoding="utf-8"),
            object_pairs_hook=_reject_duplicate_keys,
            parse_constant=_reject_json_constant,
        )
    except ManifestError:
        raise
    except Exception as exc:
        raise ManifestError(f"failed to read JSON {path}: {exc}") from exc


def _repo_file(raw_path: Any, *, ctx: str) -> Path:
    rel_text = _as_str(raw_path, ctx=ctx)
    rel = Path(rel_text)
    _require(not rel.is_absolute(), f"{ctx}: path must be repository-relative")
    _require(
        all(part not in {"", ".", ".."} for part in rel.parts),
        f"{ctx}: path must be canonical and repository-relative",
    )
    root = REPO_ROOT.resolve()
    current = root
    for part in rel.parts:
        current = current / part
        _require(not current.is_symlink(), f"{ctx}: symlink path component rejected: {rel_text}")
    resolved = current.resolve()
    try:
        resolved.relative_to(root)
    except ValueError as exc:
        raise ManifestError(f"{ctx}: path escapes repository: {rel_text}") from exc
    _require(resolved.is_file(), f"{ctx}: missing file: {rel_text}")
    return resolved


def _sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as fh:
        for chunk in iter(lambda: fh.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def _sha256_tree(paths: Iterable[Path], *, root: Path) -> str:
    h = hashlib.sha256()
    files: list[Path] = []
    ignored_parts = {".git", "__pycache__", ".mypy_cache", ".pytest_cache"}
    ignored_suffixes = {".pyc", ".pyo"}

    for base in paths:
        if base.is_file():
            files.append(base)
            continue
        if not base.is_dir():
            continue
        for path in sorted(base.rglob("*")):
            if not path.is_file():
                continue
            if any(part in ignored_parts for part in path.parts):
                continue
            if path.suffix in ignored_suffixes:
                continue
            files.append(path)

    for path in files:
        rel = path.relative_to(root).as_posix().encode("utf-8")
        h.update(rel)
        h.update(b"\0")
        h.update(_sha256_file(path).encode("ascii"))
        h.update(b"\0")
    return h.hexdigest()


def _git_stdout(*args: str) -> str:
    esso_root = REPO_ROOT / "external" / "ESSO"
    try:
        proc = subprocess.run(
            ["git", "-C", str(esso_root), *args],
            check=True,
            capture_output=True,
            text=True,
        )
    except FileNotFoundError as exc:
        raise ManifestError("git is required for runtime shell assurance manifest checks") from exc
    except subprocess.CalledProcessError as exc:
        detail = (exc.stderr or exc.stdout or "").strip() or str(exc)
        raise ManifestError(f"failed to inspect ESSO checkout: {detail}") from exc
    return proc.stdout.strip()


def _solver_version(cmd: str) -> str:
    try:
        proc = subprocess.run([cmd, "--version"], check=True, capture_output=True, text=True)
    except FileNotFoundError as exc:
        raise ManifestError(f"required solver {cmd!r} is missing") from exc
    except subprocess.CalledProcessError as exc:
        detail = (exc.stderr or exc.stdout or "").strip() or str(exc)
        raise ManifestError(f"failed to get version for solver {cmd!r}: {detail}") from exc
    return proc.stdout.strip().splitlines()[0]


def _check_source_files(entries: list[Mapping[str, Any]]) -> None:
    for index, raw_entry in enumerate(entries):
        entry = _as_dict(raw_entry, ctx=f"source_files[{index}]")
        rel = _as_str(entry.get("path"), ctx=f"source_files[{index}].path")
        expected = _as_str(entry.get("sha256"), ctx=f"source_files[{index}].sha256")
        _require(len(expected) == 64, f"source_files[{index}].sha256: expected 64 hex characters")
        try:
            int(expected, 16)
        except ValueError as exc:
            raise ManifestError(f"source_files[{index}].sha256: expected lowercase hex") from exc
        path = _repo_file(rel, ctx=f"source_files[{index}].path")
        actual = _sha256_file(path)
        _require(actual == expected, f"source hash mismatch for {rel}: {actual} != {expected}")


def _check_shell_lint(entry: Mapping[str, Any]) -> None:
    report_path = _repo_file(entry.get("report_path"), ctx="shell_lint.report_path")
    report = _as_dict(_load_json(report_path), ctx=str(report_path))
    _require_true(report.get("ok"), ctx=f"{report_path}: ok")
    _require(report.get("command") == "shell-lint", f"{report_path}: command mismatch")
    _require(report.get("ir_hash") == entry["ir_hash"], f"{report_path}: ir_hash mismatch")

    adapter = _as_dict(report.get("adapter"), ctx=f"{report_path}: adapter")
    _require(adapter.get("spec") == entry["adapter_spec"], f"{report_path}: adapter spec mismatch")

    expected = _as_dict(report.get("expected"), ctx=f"{report_path}: expected")
    got = _as_dict(report.get("got"), ctx=f"{report_path}: got")
    _require(expected.get("actions") == entry["actions"], f"{report_path}: expected actions mismatch")
    _require(expected.get("effects") == entry["effects"], f"{report_path}: expected effects mismatch")
    _require(got.get("actions") == entry["actions"], f"{report_path}: got actions mismatch")
    _require(got.get("effects") == entry["effects"], f"{report_path}: got effects mismatch")
    _require(report.get("issues") == [], f"{report_path}: shell-lint reported issues")


def _check_verify_shell(entry: Mapping[str, Any]) -> None:
    report_path = _repo_file(entry.get("report_path"), ctx="verify_shell.report_path")
    report = _as_dict(_load_json(report_path), ctx=str(report_path))
    _require_true(report.get("ok"), ctx=f"{report_path}: ok")
    _require(report.get("command") == "verify-shell", f"{report_path}: command mismatch")
    _require(report.get("ir_hash") == entry["ir_hash"], f"{report_path}: ir_hash mismatch")
    _require(report.get("mode") == entry["mode"], f"{report_path}: mode mismatch")
    _require(
        _require_json_int(report.get("seed"), ctx=f"{report_path}: seed")
        == _require_json_int(entry.get("seed"), ctx=f"{report_path}: expected seed"),
        f"{report_path}: seed mismatch",
    )
    _require(
        _require_json_int(report.get("traces"), ctx=f"{report_path}: traces")
        == _require_json_int(entry.get("traces"), ctx=f"{report_path}: expected traces"),
        f"{report_path}: traces mismatch",
    )
    _require(
        _require_json_int(report.get("max_steps"), ctx=f"{report_path}: max_steps")
        == _require_json_int(entry.get("max_steps"), ctx=f"{report_path}: expected max_steps"),
        f"{report_path}: max_steps mismatch",
    )
    _require(
        _require_json_int(report.get("determinism_trials"), ctx=f"{report_path}: determinism_trials")
        == _require_json_int(entry.get("determinism_trials"), ctx=f"{report_path}: expected determinism_trials"),
        f"{report_path}: determinism_trials mismatch",
    )
    _require(report.get("failure") is None, f"{report_path}: verify-shell failure is not null")

    adapter = _as_dict(report.get("adapter"), ctx=f"{report_path}: adapter")
    _require(adapter.get("spec") == entry["adapter_spec"], f"{report_path}: adapter spec mismatch")
    report_model_raw = _as_str(report.get("model"), ctx=f"{report_path}: model")
    expected_model_raw = _as_str(entry.get("kernel_path"), ctx=f"{report_path}: expected model")
    report_model = Path(report_model_raw)
    if not report_model.is_absolute():
        report_model = REPO_ROOT / report_model
    expected_model = REPO_ROOT / expected_model_raw
    _require(report_model.resolve() == expected_model.resolve(), f"{report_path}: model file mismatch")

    determinism = _as_dict(report.get("determinism"), ctx=f"{report_path}: determinism")
    _require_true(determinism.get("ok"), ctx=f"{report_path}: determinism.ok")
    fingerprints = _as_list(
        determinism.get("fingerprints"),
        ctx=f"{report_path}: determinism.fingerprints",
    )
    _require(
        all(type(fingerprint) is str and fingerprint for fingerprint in fingerprints),
        f"{report_path}: determinism.fingerprints must contain non-empty strings",
    )
    trials = _require_json_int(entry.get("determinism_trials"), ctx=f"{report_path}: expected trials")
    _require(len(fingerprints) == trials, f"{report_path}: fingerprint count mismatch")
    _require(len(set(fingerprints)) == 1, f"{report_path}: fingerprints diverged")
    _require(fingerprints[0] == entry["fingerprint"], f"{report_path}: fingerprint mismatch")


def _check_manifest_inventory(manifest: Mapping[str, Any]) -> None:
    toolchain = _as_dict(manifest.get("toolchain"), ctx="toolchain")
    solvers = _as_dict(toolchain.get("solvers"), ctx="toolchain.solvers")
    _require(
        tuple(solvers.keys()) == REQUIRED_SOLVERS,
        "required inventory mismatch: toolchain.solvers",
    )

    source_entries = _as_list(manifest.get("source_files"), ctx="source_files")
    source_paths = tuple(
        _as_str(_as_dict(entry, ctx=f"source_files[{index}]").get("path"), ctx=f"source_files[{index}].path")
        for index, entry in enumerate(source_entries)
    )
    _require(source_paths == REQUIRED_SOURCE_PATHS, "required inventory mismatch: source_files")

    shell_entries = _as_list(manifest.get("shell_lint"), ctx="shell_lint")
    shell_inventory = tuple(
        (
            _as_str(_as_dict(entry, ctx=f"shell_lint[{index}]").get("report_path"), ctx="report_path"),
            _as_str(_as_dict(entry, ctx=f"shell_lint[{index}]").get("adapter_spec"), ctx="adapter_spec"),
        )
        for index, entry in enumerate(shell_entries)
    )
    required_shell_inventory = tuple(
        (
            f"internal/esso_verify/runtime_shell_assurance/{model_id}/shell_lint.json",
            adapter_spec,
        )
        for model_id, _kernel_path, adapter_spec in REQUIRED_MODELS
    )
    _require(shell_inventory == required_shell_inventory, "required inventory mismatch: shell_lint")

    verify_entries = _as_list(manifest.get("verify_shell"), ctx="verify_shell")
    verify_inventory = tuple(
        (
            _as_str(_as_dict(entry, ctx=f"verify_shell[{index}]").get("report_path"), ctx="report_path"),
            _as_str(_as_dict(entry, ctx=f"verify_shell[{index}]").get("kernel_path"), ctx="kernel_path"),
            _as_str(_as_dict(entry, ctx=f"verify_shell[{index}]").get("adapter_spec"), ctx="adapter_spec"),
        )
        for index, entry in enumerate(verify_entries)
    )
    required_verify_inventory = tuple(
        (
            f"internal/esso_verify/runtime_shell_assurance/{model_id}/verify_shell.json",
            kernel_path,
            adapter_spec,
        )
        for model_id, kernel_path, adapter_spec in REQUIRED_MODELS
    )
    _require(verify_inventory == required_verify_inventory, "required inventory mismatch: verify_shell")

    regression_tests = tuple(
        _as_str(value, ctx=f"adapter_regression_tests[{index}]")
        for index, value in enumerate(
            _as_list(manifest.get("adapter_regression_tests"), ctx="adapter_regression_tests")
        )
    )
    _require(
        regression_tests == REQUIRED_REGRESSION_TESTS,
        "required inventory mismatch: adapter_regression_tests",
    )


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Check the pinned runtime shell assurance manifest.")
    parser.add_argument("--manifest", default=str(DEFAULT_MANIFEST), help="Path to runtime shell assurance manifest JSON")
    args = parser.parse_args(argv)

    manifest_path = Path(args.manifest).resolve()
    manifest = _as_dict(_load_json(manifest_path), ctx=str(manifest_path))

    _require(
        _require_json_int(manifest.get("manifest_version"), ctx="manifest_version") == 1,
        "unsupported runtime shell assurance manifest version",
    )
    _check_manifest_inventory(manifest)

    toolchain = _as_dict(manifest.get("toolchain"), ctx="toolchain")
    esso_root = REPO_ROOT / "external" / "ESSO"
    _require(esso_root.exists(), f"ESSO not found at {esso_root}")
    esso_head = _git_stdout("rev-parse", "HEAD")
    esso_tree = _sha256_tree([esso_root / "pyproject.toml", esso_root / "ESSO"], root=esso_root)
    _require(esso_head == toolchain["esso_code_hash"], "ESSO code hash drifted from runtime shell manifest")
    _require(esso_tree == toolchain["esso_tree_sha256"], "ESSO tree drifted from runtime shell manifest")

    expected_solvers = _as_dict(toolchain.get("solvers"), ctx="toolchain.solvers")
    for solver_name, expected_version in expected_solvers.items():
        solver = _as_str(solver_name, ctx="toolchain.solvers key")
        version = _as_str(expected_version, ctx=f"toolchain.solvers.{solver}")
        _require(_solver_version(solver) == version, f"solver version drift for {solver}")

    _check_source_files(_as_list(manifest.get("source_files"), ctx="source_files"))
    for entry in _as_list(manifest.get("shell_lint"), ctx="shell_lint"):
        _check_shell_lint(_as_dict(entry, ctx="shell_lint entry"))
    for entry in _as_list(manifest.get("verify_shell"), ctx="verify_shell"):
        _check_verify_shell(_as_dict(entry, ctx="verify_shell entry"))

    for index, rel in enumerate(
        _as_list(manifest.get("adapter_regression_tests"), ctx="adapter_regression_tests")
    ):
        _repo_file(rel, ctx=f"adapter_regression_tests[{index}]")

    print("ok")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except ManifestError as exc:
        print(f"error: {exc}", file=sys.stderr)
        raise SystemExit(1) from exc
