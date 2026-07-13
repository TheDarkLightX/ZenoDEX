#!/usr/bin/env python3
"""Check or natively replay the retained V4 Spot value-leaf evidence.

Static mode verifies canonical bytes, exact identities, Git trees, receipt
structure, and the governed seal-mutation relation. It never verifies a RISC0
seal. Live mode first passes static validation, builds the pinned host verifier
from its separate source commit, and then runs the positive and negative
cryptographic receipt boundaries.
"""

from __future__ import annotations

import argparse
import importlib
import json
import os
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any

if __package__:
    _MODULE_PREFIX = "tools."
else:
    sys.path.insert(0, Path(__file__).resolve().parent.as_posix())
    _MODULE_PREFIX = ""
support = importlib.import_module(
    f"{_MODULE_PREFIX}zrpf_v4_spot_value_leaf_evidence_support"
)
environment = importlib.import_module(f"{_MODULE_PREFIX}zrpf_v3_replay_environment")
process_runner = importlib.import_module(f"{_MODULE_PREFIX}zrpf_v3_replay_process")
sealed_executable = importlib.import_module(
    f"{_MODULE_PREFIX}zrpf_v3_replay_sealed_executable"
)
source_snapshot = importlib.import_module(
    f"{_MODULE_PREFIX}zrpf_v3_replay_source_snapshot"
)
toolchain = importlib.import_module(f"{_MODULE_PREFIX}zrpf_v3_replay_toolchain")
common = support.common

MAX_GIT_OUTPUT_BYTES = 4 * 1024 * 1024


@dataclass(frozen=True)
class StaticMaterials:
    artifacts_checked: int
    supporting_inputs_checked: int
    canonical_receipts_checked: bool
    exact_mutation_relation_checked: bool


@dataclass(frozen=True)
class LiveReplay:
    binary_sha256: str
    binary_size_bytes: int
    binary_transport: str
    dev_mode_stderr: bytes
    positive_stdout: bytes
    mutation_stderr: bytes
    recorded_binary_identity_match: bool
    toolchain_versions: dict[str, str]


def load_manifest(
    path: Path = support.DEFAULT_MANIFEST,
) -> tuple[dict[str, Any] | None, list[str]]:
    """Load one strict canonical manifest for CLI and boundary-atlas use."""

    try:
        loaded = common.load_manifest(path)
    except (OSError, ValueError) as exc:
        return None, [f"manifest rejected: {exc}"]
    if not isinstance(loaded.document, dict):
        return None, ["manifest root must be an object"]
    return loaded.document, []


def check_manifest(
    path: Path = support.DEFAULT_MANIFEST,
    *,
    repo_root: Path = support.REPO_ROOT,
) -> dict[str, Any]:
    document, errors = load_manifest(path)
    if document is None:
        return _static_report(errors)
    return validate_manifest(document, repo_root=repo_root)


def validate_manifest(
    document: Any,
    *,
    repo_root: Path = support.REPO_ROOT,
) -> dict[str, Any]:
    """Validate publisher bytes without promoting cryptographic execution."""

    if not isinstance(document, dict):
        return _static_report(["manifest root must be an object"])
    errors: list[str] = []
    canonical = common.canonical_manifest_bytes(document)
    manifest_sha256 = common.sha256_bytes(canonical)
    if manifest_sha256 != support.EXPECTED_MANIFEST_SHA256:
        errors.append("manifest canonical SHA-256 differs from governed anchor")
    _compare_exact(document, support.expected_manifest(), "manifest", errors)
    proof_anchor = _validate_git_anchor(
        repo_root,
        support.PROOF_SOURCE_COMMIT,
        support.PROOF_SOURCE_TREE,
        "proof-generation",
        errors,
    )
    verifier_anchor = _validate_git_anchor(
        repo_root,
        support.VERIFIER_SOURCE_COMMIT,
        support.VERIFIER_SOURCE_TREE,
        "native-verifier",
        errors,
    )
    _validate_toolchain_lock_at_anchor(repo_root, errors)
    materials = _validate_materials(document, repo_root, errors)
    return _static_report(
        errors,
        manifest_sha256=manifest_sha256,
        proof_anchor=proof_anchor,
        verifier_anchor=verifier_anchor,
        materials=materials,
    )


def _compare_exact(actual: Any, expected: Any, label: str, errors: list[str]) -> None:
    if type(actual) is not type(expected):
        errors.append(f"{label} type mismatch")
        return
    if isinstance(expected, dict):
        missing = sorted(set(expected) - set(actual))
        unknown = sorted(set(actual) - set(expected))
        if missing:
            errors.append(f"{label} missing fields: {','.join(missing)}")
        if unknown:
            errors.append(f"{label} has unknown fields: {','.join(unknown)}")
        for key in sorted(set(actual) & set(expected)):
            _compare_exact(actual[key], expected[key], f"{label}.{key}", errors)
        return
    if isinstance(expected, list):
        if len(actual) != len(expected):
            errors.append(f"{label} length mismatch")
            return
        for index, (left, right) in enumerate(zip(actual, expected, strict=True)):
            _compare_exact(left, right, f"{label}[{index}]", errors)
        return
    if actual != expected:
        errors.append(f"{label} value mismatch")


def _validate_git_anchor(
    repo_root: Path,
    commit: str,
    expected_tree: str,
    label: str,
    errors: list[str],
) -> bool:
    try:
        observed_tree = _git_bytes(
            repo_root,
            ("show", "-s", "--format=%T", f"{commit}^{{commit}}"),
        ).decode("ascii").strip()
    except (RuntimeError, UnicodeDecodeError):
        errors.append(f"{label} source anchor is unavailable")
        return False
    if observed_tree != expected_tree:
        errors.append(f"{label} source tree mismatch")
        return False
    return True


def _validate_toolchain_lock_at_anchor(repo_root: Path, errors: list[str]) -> None:
    relative = support.expected_manifest()["native_replay_verifier"][
        "toolchain_lock_path"
    ]
    try:
        raw = _git_bytes(
            repo_root,
            ("show", f"{support.VERIFIER_SOURCE_COMMIT}:{relative}"),
        )
    except RuntimeError:
        errors.append("native-verifier toolchain lock is unavailable")
        return
    expected = support.expected_manifest()["native_replay_verifier"][
        "toolchain_lock_sha256"
    ]
    if common.sha256_bytes(raw) != expected:
        errors.append("native-verifier toolchain lock SHA-256 mismatch")


def _git_bytes(repo_root: Path, arguments: tuple[str, ...]) -> bytes:
    result = process_runner.run_bounded(
        process_runner.ProcessRequest(
            command=("/usr/bin/git", *arguments),
            cwd=repo_root,
            env=environment.clean_environment(),
            timeout_seconds=30,
            output_limit_bytes=MAX_GIT_OUTPUT_BYTES,
            profile=process_runner.ProcessProfile.TOOL,
        )
    )
    if result.returncode != 0 or result.stderr:
        raise RuntimeError("Git source-anchor query failed")
    return result.stdout


def _validate_materials(
    document: dict[str, Any],
    repo_root: Path,
    errors: list[str],
) -> StaticMaterials:
    artifact_count = 0
    supporting_count = 0
    canonical_receipts = False
    mutation_relation = False
    try:
        root = common.resolve_relative_directory(
            repo_root,
            support.EVIDENCE_ROOT_RELATIVE,
        )
        inventory, inventory_errors = common.artifact_inventory(root)
        errors.extend(inventory_errors)
        expected_inventory = sorted(row["path"] for row in support.ARTIFACTS)
        if inventory != expected_inventory:
            errors.append("V4 evidence artifact inventory mismatch")
        materials = {
            row["id"]: common.load_artifact(root, row)
            for row in support.ARTIFACTS
        }
        artifact_count = len(materials)
        canonical_receipts = _validate_receipts(materials, errors)
        mutation_relation = _validate_mutation(document, materials, errors)
    except (OSError, ValueError) as exc:
        errors.append(f"V4 receipt material validation failed: {exc}")
    try:
        supporting_count = _validate_supporting_inputs(repo_root, errors)
    except (OSError, ValueError) as exc:
        errors.append(f"V4 supporting-input validation failed: {exc}")
    return StaticMaterials(
        artifacts_checked=artifact_count,
        supporting_inputs_checked=supporting_count,
        canonical_receipts_checked=canonical_receipts,
        exact_mutation_relation_checked=mutation_relation,
    )


def _validate_receipts(
    materials: dict[str, Any],
    errors: list[str],
) -> bool:
    if set(materials) != {row["id"] for row in support.ARTIFACTS}:
        errors.append("V4 evidence artifact IDs mismatch")
        return False
    ok = True
    by_id = {row["id"]: row for row in support.ARTIFACTS}
    for artifact_id, material in materials.items():
        try:
            journal_size, journal_sha256 = common.receipt_journal_facts(
                material.document
            )
            _validate_receipt_profile(material.document)
        except ValueError as exc:
            errors.append(f"{artifact_id} receipt structure rejected: {exc}")
            ok = False
            continue
        row = by_id[artifact_id]
        if (
            journal_size != row["journal_size_bytes"]
            or journal_sha256 != row["journal_sha256"]
        ):
            errors.append(f"{artifact_id} journal binding mismatch")
            ok = False
    return ok


def _validate_receipt_profile(document: Any) -> None:
    if not isinstance(document, dict):
        raise ValueError("receipt root is not an object")
    metadata = document.get("metadata")
    if not isinstance(metadata, dict) or set(metadata) != {"verifier_parameters"}:
        raise ValueError("receipt metadata field set mismatch")
    if not support.exact_type_and_value(
        metadata["verifier_parameters"], support.VERIFIER_PARAMETERS
    ):
        raise ValueError("receipt metadata verifier parameters mismatch")
    succinct = document.get("inner", {}).get("Succinct")
    expected_fields = {
        "claim",
        "control_id",
        "control_inclusion_proof",
        "hashfn",
        "seal",
        "verifier_parameters",
    }
    if not isinstance(succinct, dict) or set(succinct) != expected_fields:
        raise ValueError("Succinct receipt field set mismatch")
    if succinct.get("hashfn") != support.RECEIPT_PROFILE["hash_function"]:
        raise ValueError("Succinct hash function mismatch")
    if not support.exact_type_and_value(succinct.get("control_id"), support.CONTROL_ID):
        raise ValueError("Succinct control ID mismatch")
    if not support.exact_type_and_value(
        succinct.get("verifier_parameters"), support.VERIFIER_PARAMETERS
    ):
        raise ValueError("Succinct verifier parameters mismatch")
    seal = succinct.get("seal")
    if not isinstance(seal, list) or len(seal) != support.MUTATION_CONTROL["seal_word_count"]:
        raise ValueError("Succinct seal word count mismatch")


def _validate_mutation(
    document: dict[str, Any],
    materials: dict[str, Any],
    errors: list[str],
) -> bool:
    control = document.get("mutation_control")
    if not isinstance(control, dict):
        return False
    source_id = control.get("source_artifact_id")
    candidate_id = control.get("candidate_artifact_id")
    if not isinstance(source_id, str) or not isinstance(candidate_id, str):
        errors.append("mutation-control artifact IDs are malformed")
        return False
    source = materials.get(source_id)
    candidate = materials.get(candidate_id)
    if source is None or candidate is None:
        errors.append("mutation-control artifacts are unavailable")
        return False
    try:
        facts = common.exact_succinct_seal_word_one_xor_one(
            source.document,
            candidate.document,
        )
    except ValueError as exc:
        errors.append(f"V4 exact seal mutation rejected: {exc}")
        return False
    expected = support.MUTATION_CONTROL
    if any(
        (
            facts.word_count != expected["seal_word_count"],
            facts.word_index != expected["seal_word_index"],
            facts.original_word ^ facts.mutated_word != expected["xor_mask"],
        )
    ):
        errors.append("V4 exact seal mutation facts mismatch")
        return False
    return True


def _validate_supporting_inputs(
    repo_root: Path,
    errors: list[str],
) -> int:
    checked = 0
    for row in support.SUPPORTING_INPUTS:
        raw = common.read_relative_regular_file(
            repo_root,
            row["path"],
            max_bytes=common.MAX_ARTIFACT_BYTES,
        )
        if len(raw) != row["size_bytes"] or common.sha256_bytes(raw) != row["sha256"]:
            errors.append(f"supporting input identity mismatch: {row['id']}")
            continue
        value = common.strict_json_loads(raw)
        if raw != common.canonical_artifact_bytes(value, row["encoding"]):
            errors.append(f"supporting input JSON is noncanonical: {row['id']}")
            continue
        if row["kind"] == "spot_v1_source_proof_wrapper":
            if common.source_proof_receipt_sha256(value) != row["embedded_receipt_sha256"]:
                errors.append("source wrapper embedded receipt mismatch")
                continue
        else:
            journal_size, journal_sha256 = common.receipt_journal_facts(value)
            if (
                journal_size != row["journal_size_bytes"]
                or journal_sha256 != row["journal_sha256"]
            ):
                errors.append("adapter supporting receipt journal mismatch")
                continue
        checked += 1
    return checked


def _static_report(
    errors: list[str],
    *,
    manifest_sha256: str | None = None,
    proof_anchor: bool = False,
    verifier_anchor: bool = False,
    materials: StaticMaterials | None = None,
) -> dict[str, Any]:
    material = materials or StaticMaterials(0, 0, False, False)
    return {
        "errors": errors,
        "facts": {
            "artifact_files_checked": material.artifacts_checked,
            "canonical_receipts_checked": material.canonical_receipts_checked,
            "exact_mutation_relation_checked": material.exact_mutation_relation_checked,
            "execution_checked": False,
            "manifest_sha256": manifest_sha256,
            "mutation_receipt_cryptographically_rejected": False,
            "native_verifier_source_anchor_checked": verifier_anchor,
            "positive_receipt_cryptographically_verified": False,
            "proof_source_anchor_checked": proof_anchor,
            "scoped_native_replay_claim_allowed": False,
            "supporting_inputs_checked": material.supporting_inputs_checked,
        },
        "mode": "static",
        "ok": not errors,
        "schema": support.REPORT_SCHEMA,
    }


def live_check(
    risc0_home: Path,
    target_directory: Path,
    *,
    manifest_path: Path = support.DEFAULT_MANIFEST,
    repo_root: Path = support.REPO_ROOT,
) -> dict[str, Any]:
    static = check_manifest(manifest_path, repo_root=repo_root)
    if not static["ok"]:
        return static | {
            "live": {"executed": False, "verified": False},
            "mode": "live",
        }
    replay = _build_and_replay(risc0_home, target_directory, repo_root)
    facts = dict(static["facts"])
    facts.update(
        {
            "execution_checked": True,
            "mutation_receipt_cryptographically_rejected": True,
            "positive_receipt_cryptographically_verified": True,
            "scoped_native_replay_claim_allowed": True,
        }
    )
    return static | {
        "facts": facts,
        "live": _live_facts(replay),
        "mode": "live",
        "ok": True,
    }


def _build_and_replay(
    risc0_home: Path,
    target_directory: Path,
    repo_root: Path,
) -> LiveReplay:
    target = environment.create_private_target(
        _external_target_path(target_directory, repo_root)
    )
    with source_snapshot.SourceSnapshot(
        repo_root,
        target,
        support.VERIFIER_SOURCE_COMMIT,
        support.VERIFIER_SOURCE_TREE,
    ) as source_root:
        paths, versions = toolchain.verify_toolchain(risc0_home.resolve(), source_root)
        workspace = source_root / support.expected_manifest()[
            "native_replay_verifier"
        ]["workspace"]
        environment.validate_cargo_config_ancestors(workspace)
        build_env = environment.build_environment(paths, target)
        build_env["CARGO_BUILD_JOBS"] = str(
            support.expected_manifest()["native_replay_verifier"]["build_jobs"]
        )
        _run_build(paths["cargo"], source_root, target, build_env)
        _require_snapshot_identity(source_root)
        staged = _stage_inputs(repo_root, target)
        binary = target / "release/prove_spot_value_leaf_v4"
        with sealed_executable.SealedExecutable(binary) as executable:
            recorded_identity_match = _check_binary_identity(executable.identity)
            positive, dev_mode, mutation = _run_receipt_controls(
                executable,
                staged,
                target,
            )
            identity = executable.identity
    return LiveReplay(
        binary_sha256=identity.sha256,
        binary_size_bytes=identity.size_bytes,
        binary_transport=identity.transport,
        dev_mode_stderr=dev_mode,
        positive_stdout=positive,
        mutation_stderr=mutation,
        recorded_binary_identity_match=recorded_identity_match,
        toolchain_versions=versions,
    )


def _external_target_path(target: Path, repo_root: Path) -> Path:
    parent = target.parent.resolve(strict=True)
    candidate = parent / target.name
    root = repo_root.resolve(strict=True)
    if candidate == root or candidate.is_relative_to(root):
        raise RuntimeError("target directory must be outside the repository")
    return candidate


def _run_build(cargo: Path, source_root: Path, target: Path, env: dict[str, str]) -> None:
    expected = support.expected_manifest()
    verifier = expected["native_replay_verifier"]
    native = expected["native_replay"]
    command = (
        str(cargo),
        "build",
        "--frozen",
        "--release",
        "-p",
        verifier["package"],
        "--bin",
        verifier["binary"],
    )
    result = process_runner.run_bounded(
        process_runner.ProcessRequest(
            command=command,
            cwd=source_root / verifier["workspace"],
            env=env,
            timeout_seconds=native["build_timeout_seconds"],
            output_limit_bytes=native["max_process_output_bytes"],
            profile=process_runner.ProcessProfile.BUILD,
        )
    )
    if result.returncode != 0:
        raise RuntimeError("native verifier build failed")
    if result.stdout:
        raise RuntimeError("native verifier build produced unexpected stdout")
    if not (target / "release/prove_spot_value_leaf_v4").is_file():
        raise RuntimeError("native verifier build output is absent")


def _require_snapshot_identity(source_root: Path) -> None:
    head = _git_bytes(source_root, ("rev-parse", "HEAD^{commit}"))
    tree = _git_bytes(source_root, ("show", "-s", "--format=%T", "HEAD"))
    status = _git_bytes(source_root, ("status", "--porcelain=v1", "--untracked-files=all"))
    if (
        head.decode("ascii").strip() != support.VERIFIER_SOURCE_COMMIT
        or tree.decode("ascii").strip() != support.VERIFIER_SOURCE_TREE
        or status
    ):
        raise RuntimeError("native verifier source snapshot changed during build")


def _stage_inputs(repo_root: Path, target: Path) -> dict[str, Path]:
    directory = target / "replay-inputs"
    directory.mkdir(mode=0o700)
    staged: dict[str, Path] = {}
    artifact_root = common.resolve_relative_directory(
        repo_root,
        support.EVIDENCE_ROOT_RELATIVE,
    )
    rows = [
        *support.ARTIFACTS,
        *support.SUPPORTING_INPUTS,
    ]
    for row in rows:
        source_root = artifact_root if row in support.ARTIFACTS else repo_root
        raw = common.read_relative_regular_file(
            source_root,
            row["path"],
            max_bytes=common.MAX_ARTIFACT_BYTES,
        )
        destination = directory / f"{row['id']}.json"
        _write_create_new(destination, raw)
        staged[row["id"]] = destination
    return staged


def _write_create_new(path: Path, raw: bytes) -> None:
    descriptor = os.open(
        path,
        os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_CLOEXEC,
        0o600,
    )
    try:
        view = memoryview(raw)
        offset = 0
        while offset < len(view):
            written = os.write(descriptor, view[offset:])
            if written <= 0:
                raise RuntimeError("staged replay input write failed")
            offset += written
        os.fsync(descriptor)
    finally:
        os.close(descriptor)


def _check_binary_identity(identity: Any) -> bool:
    expected = support.expected_manifest()["native_replay_verifier"]
    if identity.transport != expected["expected_executable_transport"]:
        raise RuntimeError("native verifier executable transport mismatch")
    if identity.size_bytes <= 0 or identity.size_bytes > 64 * 1024 * 1024:
        raise RuntimeError("native verifier executable size is outside the bound")
    return bool(
        identity.sha256 == expected["recorded_executable_sha256"]
        and identity.size_bytes == expected["recorded_executable_size_bytes"]
    )


def _run_receipt_controls(
    executable: Any,
    staged: dict[str, Path],
    target: Path,
) -> tuple[bytes, bytes, bytes]:
    clean_env = environment.clean_environment()
    positive = _run_verifier(
        executable,
        staged,
        target,
        clean_env,
        support.ARTIFACTS[0]["id"],
    )
    dev_env = clean_env | {"RISC0_DEV_MODE": "1"}
    dev = _run_verifier(
        executable,
        staged,
        target,
        dev_env,
        support.ARTIFACTS[0]["id"],
    )
    if positive.returncode != 0:
        raise RuntimeError("positive native receipt replay failed")
    if positive.stderr:
        raise RuntimeError("positive native receipt replay produced stderr")
    _require_exact_json_output(positive.stdout, support.EXPECTED_POSITIVE_REPORT)
    if dev.returncode != 1 or dev.stdout:
        raise RuntimeError("ambient dev mode did not reach the exact reject boundary")
    _require_exact_json_output(dev.stderr, support.EXPECTED_DEV_MODE_REJECT_REPORT)
    mutation = _run_verifier(
        executable,
        staged,
        target,
        clean_env,
        support.ARTIFACTS[1]["id"],
    )
    if mutation.returncode != 1 or mutation.stdout:
        raise RuntimeError("mutation receipt did not reach the exact reject boundary")
    _require_exact_json_output(mutation.stderr, support.EXPECTED_REJECT_REPORT)
    return positive.stdout, dev.stderr, mutation.stderr


def _run_verifier(
    executable: Any,
    staged: dict[str, Path],
    target: Path,
    env: dict[str, str],
    receipt_id: str,
) -> subprocess.CompletedProcess[bytes]:
    native = support.expected_manifest()["native_replay"]
    command = (
        executable.command_path,
        "--verify-receipt",
        str(staged[receipt_id]),
        "--source-proof",
        str(staged["retained-spot-v1-source-wrapper"]),
        "--adapter-receipt",
        str(staged["retained-v1-adapter-ordinal-zero"]),
    )
    return process_runner.run_bounded(
        process_runner.ProcessRequest(
            command=command,
            cwd=target,
            env=env,
            timeout_seconds=native["replay_timeout_seconds"],
            output_limit_bytes=native["max_process_output_bytes"],
            profile=process_runner.ProcessProfile.REPLAY,
            pass_fds=executable.pass_fds,
        )
    )


def _require_exact_json_output(raw: bytes, expected: dict[str, Any]) -> None:
    try:
        document = common.strict_json_loads(raw)
    except ValueError as exc:
        raise RuntimeError("native verifier output JSON rejected") from exc
    if raw != support.canonical_compact_newline(document):
        raise RuntimeError("native verifier output is noncanonical")
    if not support.exact_type_and_value(document, expected):
        raise RuntimeError("native verifier output contract mismatch")


def _live_facts(replay: LiveReplay) -> dict[str, Any]:
    return {
        "dev_mode_environment_rejected": True,
        "dev_mode_reject_report_sha256": common.sha256_bytes(
            replay.dev_mode_stderr
        ),
        "dev_mode_reject_report_size_bytes": len(replay.dev_mode_stderr),
        "executed": True,
        "mutation_reject_report_sha256": common.sha256_bytes(replay.mutation_stderr),
        "mutation_reject_report_size_bytes": len(replay.mutation_stderr),
        "normal_positive_receipt_verified": True,
        "positive_report_sha256": common.sha256_bytes(replay.positive_stdout),
        "positive_report_size_bytes": len(replay.positive_stdout),
        "recorded_verifier_binary_identity_match": replay.recorded_binary_identity_match,
        "source_built_retained_receipt_v4_value_leaf_replay_verified": True,
        "toolchain_versions": replay.toolchain_versions,
        "verified": True,
        "verifier_binary_sha256": replay.binary_sha256,
        "verifier_binary_size_bytes": replay.binary_size_bytes,
        "verifier_binary_transport": replay.binary_transport,
        "verifier_source_commit": support.VERIFIER_SOURCE_COMMIT,
        "verifier_source_tree": support.VERIFIER_SOURCE_TREE,
    }


def parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--evidence", type=Path, default=support.DEFAULT_MANIFEST)
    parser.add_argument("--repo-root", type=Path, default=support.REPO_ROOT)
    parser.add_argument("--json", action="store_true")
    parser.add_argument("--live", action="store_true")
    parser.add_argument("--risc0-home", type=Path)
    parser.add_argument("--target-dir", type=Path)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    args = parse_args(argv)
    try:
        if args.live:
            if args.risc0_home is None or args.target_dir is None:
                raise RuntimeError("live mode requires --risc0-home and --target-dir")
            report = live_check(
                args.risc0_home,
                args.target_dir,
                manifest_path=args.evidence,
                repo_root=args.repo_root,
            )
        else:
            report = check_manifest(args.evidence, repo_root=args.repo_root)
    except (OSError, RuntimeError, ValueError, subprocess.SubprocessError) as exc:
        report = {
            "errors": [str(exc)],
            "mode": "live" if args.live else "static",
            "ok": False,
            "schema": support.REPORT_SCHEMA,
        }
    if args.json:
        print(json.dumps(report, sort_keys=True, separators=(",", ":")))
    else:
        print(json.dumps(report, indent=2, sort_keys=True))
    return 0 if report.get("ok") else 1


if __name__ == "__main__":
    sys.exit(main())
