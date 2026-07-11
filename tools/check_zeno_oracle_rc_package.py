#!/usr/bin/env python3
"""Fail-closed checker for a Zeno Oracle devnet RC package."""

from __future__ import annotations

import argparse
import hashlib
import json
import stat
import tarfile
from pathlib import Path, PurePosixPath
from typing import Any, Mapping

import yaml

REQUIRED_PACKAGE_FILES = {
    ".github/workflows/zeno-oracle-mvp.yml",
    "bin/zenodex-oracle",
    "scripts/check_zeno_oracle_rc_bundle.sh",
    "src/state/canonical.py",
    "tests/integration/test_dex_snapshot.py",
    "generated/perp_python/perp_epoch_clearinghouse_2p_v0_1_ref.py",
    "formal/tla/OracleRecoveryLifecycle.tla",
    "lean-mathlib/Proofs/ZenoOracleMathWitness.lean",
    "tools/check_claims_registry.py",
    "tools/check_cross_module_oracle_split_brain_v1.py",
    "tools/check_disaster_obligation_certificate.py",
    "tools/check_zeno_oracle_disaster_frontier.py",
    "tools/check_zeno_oracle_frontier_obligation_projection.py",
    "tools/check_zeno_oracle_goal_completion_audit.py",
    "tools/check_zeno_oracle_live_economics_policy.py",
    "tools/check_zeno_oracle_rc_package.py",
    "tools/check_zenoproof_production_governance_policy.py",
    "tools/zeno_oracle_disaster_class_corpus.py",
    "tools/zeno_oracle_esso_zusd_recovery_replay.py",
    "tools/zeno_oracle_tla_recovery_replay.py",
    "tools/zeno_oracle_ltlf_recovery_replay.py",
    "tools/zeno_oracle_o3_receipt_flow_replay.py",
    "tools/zeno_oracle_disaster_obligation_certificate_manifest.json",
    "tools/zeno_oracle_math_witness_sweep.jl",
    "tools/zenodex_oracle_cli.py",
    "tools/zenodex_oracle_devnet_service.py",
    "tools/zenodex_oracle_reporter_economics_replay.py",
    "tools/zenodex_oracle_reporter_token_settlement_replay.py",
    "scripts/check_zeno_oracle_devnet_alpha.sh",
    "docs/ZENO_ORACLE_DEVNET_ALPHA.md",
    "docs/ZENO_ORACLE_CLI_V1.md",
    "docs/ZENO_ORACLE_PRODUCTION_GATES.md",
    "docs/ZENO_DISASTER_STATE_MINIMIZATION_GOAL.md",
    "docs/claims_registry.yaml",
    "docs/papers/zeno-oracle-whitepaper/main.pdf",
    "docs/papers/zeno-oracle-whitepaper/ZenoOracleWhitepaper.pdf",
    "assets/branding/zeno-oracle/zeno_oracle_icon_256.png",
    "assets/branding/zeno-oracle/zeno_oracle_icon_512.png",
}
REQUIRED_NOT_CLAIMS = {
    "does_not_claim_production_oracle_network",
    "does_not_claim_onchain_feed_governance",
    "does_not_claim_live_public_reporter_economics",
    "does_not_claim_platform_native_binary",
    "does_not_claim_production_code_signing",
    "does_not_claim_production_zenoproof_governance",
    "does_not_claim_generalized_math_proof_completion",
}
REPORT_SCHEMA = "zenodex.oracle.rc_package_check.v1"
AUTHENTICATED_MODE_ERROR = "receipt_and_sig_required_unless_local_only"


def _load_json(path: Path) -> Mapping[str, Any]:
    obj = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(obj, Mapping):
        raise ValueError(f"{path} must decode to an object")
    return obj


def _sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def _authenticated_package_binding_errors(*, tar_path: Path, package_dir: Path) -> list[str]:
    """Compare every packaged file with the externally authenticated tarball."""
    errors: list[str] = []
    tar_files: dict[str, tuple[int, str]] = {}
    roots: set[str] = set()
    try:
        with tarfile.open(tar_path, mode="r:gz") as archive:
            for member in archive.getmembers():
                member_path = PurePosixPath(member.name)
                if member_path.is_absolute() or ".." in member_path.parts or not member_path.parts:
                    errors.append("authenticated_tarball_path_invalid")
                    continue
                roots.add(member_path.parts[0])
                if member.isdir():
                    continue
                if not member.isfile() or len(member_path.parts) < 2:
                    errors.append(f"authenticated_tarball_unsupported_member:{member.name}")
                    continue
                file_obj = archive.extractfile(member)
                if file_obj is None:
                    errors.append(f"authenticated_tarball_file_unreadable:{member.name}")
                    continue
                digest = hashlib.sha256()
                while chunk := file_obj.read(1024 * 1024):
                    digest.update(chunk)
                rel_path = PurePosixPath(*member_path.parts[1:]).as_posix()
                if rel_path in tar_files:
                    errors.append(f"authenticated_tarball_duplicate_file:{rel_path}")
                tar_files[rel_path] = (member.size, digest.hexdigest())
    except (OSError, tarfile.TarError) as exc:
        return [f"authenticated_tarball_invalid:{exc}"]

    if len(roots) != 1:
        errors.append("authenticated_tarball_must_have_one_package_root")

    disk_files: dict[str, Path] = {}
    if package_dir.is_dir():
        for path in package_dir.rglob("*"):
            rel_path = path.relative_to(package_dir).as_posix()
            if path.is_symlink():
                errors.append(f"authenticated_package_symlink_forbidden:{rel_path}")
            elif path.is_file():
                disk_files[rel_path] = path

    tar_file_set = set(tar_files)
    disk_file_set = set(disk_files)
    for rel_path in sorted(tar_file_set - disk_file_set):
        errors.append(f"authenticated_package_file_missing:{rel_path}")
    for rel_path in sorted(disk_file_set - tar_file_set):
        errors.append(f"authenticated_package_file_unexpected:{rel_path}")
    for rel_path in sorted(tar_file_set & disk_file_set):
        expected_size, expected_sha256 = tar_files[rel_path]
        disk_path = disk_files[rel_path]
        if disk_path.stat().st_size != expected_size:
            errors.append(f"authenticated_package_file_size_mismatch:{rel_path}")
        elif _sha256_file(disk_path) != expected_sha256:
            errors.append(f"authenticated_package_file_sha256_mismatch:{rel_path}")
    return errors


def _file_index(manifest: Mapping[str, Any], errors: list[str]) -> dict[str, Mapping[str, Any]]:
    raw_files = manifest.get("files")
    if not isinstance(raw_files, list):
        errors.append("manifest_files_must_be_list")
        return {}
    index: dict[str, Mapping[str, Any]] = {}
    for idx, row in enumerate(raw_files):
        if not isinstance(row, Mapping):
            errors.append(f"manifest_files_{idx}_must_be_object")
            continue
        path = row.get("path")
        if not isinstance(path, str) or not path:
            errors.append(f"manifest_files_{idx}_path_must_be_nonempty_string")
            continue
        if path in index:
            errors.append(f"duplicate_manifest_file:{path}")
        index[path] = row
    return index


def _manifest_contains_path_or_child(file_index: Mapping[str, Mapping[str, Any]], rel_path: str) -> bool:
    prefix = rel_path.rstrip("/") + "/"
    return rel_path in file_index or any(path.startswith(prefix) for path in file_index)


def check_package(*, package_dir: Path, receipt_path: Path | None = None, sig_path: Path | None = None) -> dict[str, Any]:
    errors: list[str] = []
    manifest_path = package_dir / "ZEN_ORACLE_RC_MANIFEST.json"
    if not package_dir.is_dir():
        errors.append("package_dir_missing")
        manifest: Mapping[str, Any] = {}
    elif not manifest_path.is_file():
        errors.append("manifest_missing")
        manifest = {}
    else:
        try:
            manifest = _load_json(manifest_path)
        except Exception as exc:
            errors.append(f"manifest_invalid:{exc}")
            manifest = {}

    if manifest:
        if manifest.get("schema") != "zenodex.oracle.rc_manifest.v1":
            errors.append("manifest_schema_mismatch")
        if manifest.get("entrypoint") != "bin/zenodex-oracle":
            errors.append("entrypoint_mismatch")
        if manifest.get("python_entrypoint") != "tools/zenodex_oracle_cli.py":
            errors.append("python_entrypoint_mismatch")
        if manifest.get("devnet_alpha_gate") != "scripts/check_zeno_oracle_devnet_alpha.sh":
            errors.append("devnet_alpha_gate_mismatch")
        if manifest.get("package_replay_gate") != "scripts/check_zeno_oracle_rc_bundle.sh":
            errors.append("package_replay_gate_mismatch")
        if manifest.get("whitepaper") != "docs/papers/zeno-oracle-whitepaper/main.pdf":
            errors.append("whitepaper_mismatch")
        if manifest.get("whitepaper_author") != "Dana Edwards":
            errors.append("whitepaper_author_mismatch")
        not_claimed = manifest.get("not_claimed")
        if not isinstance(not_claimed, list):
            errors.append("not_claimed_must_be_list")
        else:
            missing = sorted(REQUIRED_NOT_CLAIMS - {str(item) for item in not_claimed if isinstance(item, str)})
            errors.extend(f"missing_not_claim:{item}" for item in missing)

        file_index = _file_index(manifest, errors)
        claims_registry_path = package_dir / "docs" / "claims_registry.yaml"
        if claims_registry_path.is_file():
            try:
                registry = yaml.safe_load(claims_registry_path.read_text(encoding="utf-8"))
                if not isinstance(registry, Mapping):
                    errors.append("claims_registry_must_be_object")
                else:
                    claims = registry.get("claims")
                    if not isinstance(claims, list):
                        errors.append("claims_registry_claims_must_be_list")
                    else:
                        for claim_index, claim in enumerate(claims):
                            if not isinstance(claim, Mapping):
                                errors.append(f"claims_registry_claim_{claim_index}_must_be_object")
                                continue
                            evidence = claim.get("evidence")
                            if not isinstance(evidence, Mapping):
                                errors.append(f"claims_registry_claim_{claim_index}_evidence_must_be_object")
                                continue
                            files = evidence.get("files")
                            if files is None:
                                continue
                            if not isinstance(files, list):
                                errors.append(f"claims_registry_claim_{claim_index}_files_must_be_list")
                                continue
                            for file_index_in_claim, rel_path in enumerate(files):
                                if not isinstance(rel_path, str) or not rel_path:
                                    errors.append(
                                        f"claims_registry_claim_{claim_index}_file_{file_index_in_claim}_must_be_string"
                                    )
                                    continue
                                if rel_path.startswith("/") or ".." in Path(rel_path).parts:
                                    errors.append(f"claims_registry_file_outside_package:{rel_path}")
                                    continue
                                if not _manifest_contains_path_or_child(file_index, rel_path):
                                    errors.append(f"claims_registry_file_missing_from_manifest:{rel_path}")
                                if not (package_dir / rel_path).exists():
                                    errors.append(f"claims_registry_file_missing_on_disk:{rel_path}")
            except Exception as exc:
                errors.append(f"claims_registry_invalid:{exc}")
        else:
            errors.append("claims_registry_missing")

        missing_files = sorted(REQUIRED_PACKAGE_FILES - set(file_index))
        errors.extend(f"missing_required_file:{path}" for path in missing_files)
        for rel_path, row in sorted(file_index.items()):
            path = package_dir / rel_path
            if not path.is_file():
                errors.append(f"manifest_file_missing_on_disk:{rel_path}")
                continue
            if not isinstance(row.get("size_bytes"), int) or isinstance(row.get("size_bytes"), bool):
                errors.append(f"manifest_file_size_invalid:{rel_path}")
            elif int(row["size_bytes"]) != path.stat().st_size:
                errors.append(f"manifest_file_size_mismatch:{rel_path}")
            if not isinstance(row.get("sha256"), str) or len(str(row["sha256"])) != 64:
                errors.append(f"manifest_file_sha256_invalid:{rel_path}")
            elif str(row["sha256"]) != _sha256_file(path):
                errors.append(f"manifest_file_sha256_mismatch:{rel_path}")
        entrypoint_path = package_dir / "bin" / "zenodex-oracle"
        if not entrypoint_path.is_file():
            errors.append("entrypoint_missing_on_disk")
        elif not (entrypoint_path.stat().st_mode & (stat.S_IXUSR | stat.S_IXGRP | stat.S_IXOTH)):
            errors.append("entrypoint_not_executable")
        package_replay_path = package_dir / "scripts" / "check_zeno_oracle_rc_bundle.sh"
        if not package_replay_path.is_file():
            errors.append("package_replay_gate_missing_on_disk")
        elif not (package_replay_path.stat().st_mode & (stat.S_IXUSR | stat.S_IXGRP | stat.S_IXOTH)):
            errors.append("package_replay_gate_not_executable")

    receipt: Mapping[str, Any] | None = None
    authenticated_tar_path: Path | None = None
    if receipt_path is not None:
        if not receipt_path.is_file():
            errors.append("receipt_missing")
        else:
            try:
                receipt = _load_json(receipt_path)
            except Exception as exc:
                errors.append(f"receipt_invalid:{exc}")
        if receipt is not None:
            if receipt.get("schema") != "zenodex.oracle.rc_package_receipt.v1":
                errors.append("receipt_schema_mismatch")
            if receipt.get("signature_schema") != "zenodex.oracle.devnet_package_signature.v1":
                errors.append("receipt_signature_schema_mismatch")
            tar_path_raw = receipt.get("path")
            if isinstance(tar_path_raw, str) and tar_path_raw:
                tar_path = Path(tar_path_raw)
                if not tar_path.is_absolute():
                    tar_path = receipt_path.parent / tar_path.name
                if tar_path.is_file():
                    authenticated_tar_path = tar_path
                    if receipt.get("sha256") != _sha256_file(tar_path):
                        errors.append("receipt_tarball_sha256_mismatch")
                    if receipt.get("size_bytes") != tar_path.stat().st_size:
                        errors.append("receipt_tarball_size_mismatch")
                else:
                    errors.append("receipt_tarball_missing")
            else:
                errors.append("receipt_path_must_be_nonempty_string")
            signature = receipt.get("signature")
            sha256 = receipt.get("sha256")
            if isinstance(signature, str) and isinstance(sha256, str):
                expected_signature = hashlib.sha256(f"zenodex-oracle-devnet-alpha-rc:{sha256}".encode("utf-8")).hexdigest()
                if signature != expected_signature:
                    errors.append("receipt_signature_mismatch")
            else:
                errors.append("receipt_signature_fields_invalid")

    if sig_path is not None:
        if not sig_path.is_file():
            errors.append("sig_missing")
        elif receipt is not None and isinstance(receipt.get("signature"), str):
            if sig_path.read_text(encoding="utf-8").strip() != receipt["signature"]:
                errors.append("sig_file_mismatch")

    if authenticated_tar_path is not None:
        errors.extend(
            _authenticated_package_binding_errors(
                tar_path=authenticated_tar_path,
                package_dir=package_dir,
            )
        )

    status = "accepted" if not errors else "rejected"
    return {
        "schema": REPORT_SCHEMA,
        "ok": status == "accepted",
        "status": status,
        "package_dir": str(package_dir),
        "manifest": None
        if not manifest
        else {
            "version": manifest.get("version"),
            "entrypoint": manifest.get("entrypoint"),
            "file_count": manifest.get("file_count"),
            "required_file_count": len(REQUIRED_PACKAGE_FILES),
        },
        "receipt_checked": receipt_path is not None,
        "signature_checked": sig_path is not None,
        "errors": errors,
        "not_claimed": sorted(REQUIRED_NOT_CLAIMS),
    }


def _cli_authentication_errors(*, receipt_path: Path | None, sig_path: Path | None, local_only: bool) -> list[str]:
    """DbC: authenticated CLI mode must receive both external authenticity artifacts."""
    if local_only:
        return []
    if receipt_path is not None and sig_path is not None:
        return []
    return [AUTHENTICATED_MODE_ERROR]


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Check a Zeno Oracle devnet RC package directory")
    parser.add_argument("--package-dir", required=True, type=Path)
    parser.add_argument("--receipt", type=Path)
    parser.add_argument("--sig", type=Path)
    parser.add_argument(
        "--local-only-manifest-check",
        action="store_true",
        help=(
            "allow an unauthenticated package-local manifest check; "
            "do not use this mode as an integrity or authenticity boundary"
        ),
    )
    args = parser.parse_args(argv)

    result = check_package(package_dir=args.package_dir, receipt_path=args.receipt, sig_path=args.sig)
    result["errors"].extend(
        _cli_authentication_errors(
            receipt_path=args.receipt,
            sig_path=args.sig,
            local_only=args.local_only_manifest_check,
        )
    )
    result["status"] = "accepted" if not result["errors"] else "rejected"
    result["ok"] = result["status"] == "accepted"
    result["authenticated_mode"] = not args.local_only_manifest_check
    print(json.dumps(result, indent=2, sort_keys=True))
    return 0 if result["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
