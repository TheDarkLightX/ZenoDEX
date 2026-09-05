"""Acquire bounded local evidence for an isolated BLS input preparation.

Installed distribution files, observed stdlib files and the interpreter are
measured, not attested. Loaded-code correspondence and OS integrity remain
external premises. No evidence here authorizes a production release.
"""

from __future__ import annotations

import hashlib
import importlib.metadata
import json
import os
import stat
import sys
import sysconfig
from pathlib import Path, PurePosixPath
from typing import Any

from packaging.requirements import Requirement
from packaging.utils import canonicalize_name
from py_ecc.bls import G2Basic

from src.integration.economic_command_bls_signature_verifier_v1 import (
    BLS_ECONOMIC_COMMAND_SIGNATURE_ALGORITHM_V1,
    make_bls_economic_command_signature_verifier_backend_v1,
)

MAX_FILE_BYTES = 32 * 1024 * 1024
MAX_SNAPSHOT_BYTES = 128 * 1024 * 1024
MAX_FILES = 8192
ARTIFACT = "src/integration/economic_command_bls_signature_verifier_v1.py"
PUBLIC_TEST_SCALAR = 25


def canonical(value: object) -> bytes:
    return json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=True).encode()


def sha256(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def read_regular(path: Path, maximum: int = MAX_FILE_BYTES) -> bytes:
    """Acquire a stable, bounded regular file; no symlink/FIFO final component."""
    if not hasattr(os, "O_NOFOLLOW"):
        raise ValueError("evidence acquisition requires O_NOFOLLOW")
    descriptor = os.open(path, os.O_RDONLY | os.O_NONBLOCK | os.O_NOFOLLOW)
    try:
        before = os.fstat(descriptor)
        if not stat.S_ISREG(before.st_mode) or not 0 <= before.st_size <= maximum:
            raise ValueError("evidence file type or size")
        with os.fdopen(os.dup(descriptor), "rb") as stream:
            raw = stream.read(maximum + 1)
        after = os.fstat(descriptor)

        def coordinates(row):
            return row.st_dev, row.st_ino, row.st_size, row.st_mtime_ns, row.st_ctime_ns

        if coordinates(before) != coordinates(after) or len(raw) != before.st_size:
            raise ValueError("evidence file changed during acquisition")
        return raw
    finally:
        os.close(descriptor)


def closed_json(raw: bytes) -> dict:
    def pairs(rows):
        result = {}
        for key, value in rows:
            if key in result:
                raise ValueError("duplicate evidence JSON key")
            result[key] = value
        return result

    value = json.loads(raw, object_pairs_hook=pairs)
    if type(value) is not dict:
        raise ValueError("evidence JSON must be an object")
    return value


def _relative(label: str) -> str:
    path = PurePosixPath(label)
    if path.is_absolute() or ".." in path.parts or str(path) != label:
        raise ValueError("evidence member path")
    return label


def snapshot_files(files: dict[str, Path], destination: Path) -> dict:
    if len(files) > MAX_FILES:
        raise ValueError("evidence file count")
    rows, total = [], 0
    for label, path in sorted(files.items()):
        raw = read_regular(path)
        total += len(raw)
        if total > MAX_SNAPSHOT_BYTES:
            raise ValueError("evidence snapshot byte ceiling")
        target = destination / _relative(label)
        target.parent.mkdir(parents=True, exist_ok=True)
        with target.open("xb") as stream:
            stream.write(raw)
        rows.append({"path": label, "sha256": sha256(raw), "bytes": len(raw)})
    return {"files": rows, "total_bytes": total}


def verify_snapshot(manifest: dict, directory: Path) -> None:
    rows = manifest["files"]
    paths = [row["path"] for row in rows]
    if paths != sorted(set(paths)) or len(paths) > MAX_FILES:
        raise ValueError("snapshot manifest ordering/count")
    total = 0
    for row in rows:
        raw = read_regular(directory / _relative(row["path"]))
        if len(raw) != row["bytes"] or sha256(raw) != row["sha256"]:
            raise ValueError("snapshot content drift")
        total += len(raw)
    if total != manifest["total_bytes"] or total > MAX_SNAPSHOT_BYTES:
        raise ValueError("snapshot total drift")


def _distribution_files(distribution, name):
    if distribution.files is not None:
        return distribution.files, "installed RECORD inventory"
    # Ubuntu's existing packaging tool has no RECORD. Inventory its exact two
    # installed directories explicitly; this is evidence tooling, not BLS code.
    if name != "packaging":
        raise ValueError(f"installed dependency has no file inventory: {name}")
    base = Path(distribution.locate_file(""))
    directories = (base / "packaging", base / f"packaging-{distribution.version}.dist-info")
    if any(not path.is_dir() for path in directories):
        raise ValueError("packaging tool inventory directories missing")
    paths = tuple(
        path.relative_to(base)
        for directory in directories
        for path in directory.rglob("*")
        if path.is_file()
    )
    return paths, "bounded filesystem inventory; packaging tool RECORD unavailable"


def _installed_closure() -> tuple[list[dict], dict[str, Path]]:
    """Resolve active base dependencies, without installing or selecting extras."""
    pending, seen, rows, files = ["py-ecc", "packaging"], set(), [], {}
    while pending:
        name = canonicalize_name(pending.pop())
        if name in seen:
            continue
        seen.add(name)
        distribution = importlib.metadata.distribution(name)
        active = []
        for text in distribution.requires or ():
            requirement = Requirement(text)
            if requirement.marker and not requirement.marker.evaluate({"extra": ""}):
                continue
            if requirement.extras or requirement.url:
                raise ValueError("unqualified dependency extra or URL")
            dependency = importlib.metadata.distribution(requirement.name)
            if dependency.version not in requirement.specifier:
                raise ValueError("installed dependency violates declared constraint")
            active.append(text)
            pending.append(requirement.name)
        omitted = []
        inventory, inventory_kind = _distribution_files(distribution, name)
        for relative in inventory:
            label = str(relative)
            if relative.suffix == ".pyc" or relative.name == "direct_url.json":
                omitted.append(label)
                continue
            files[f"distributions/{name}/{_relative(label)}"] = Path(
                str(distribution.locate_file(relative))
            )
        rows.append(
            {
                "name": name,
                "version": distribution.version,
                "active_requirements": sorted(active),
                "omitted": sorted(omitted),
                "inventory_kind": inventory_kind,
            }
        )
    return sorted(rows, key=lambda row: row["name"]), files


def bls_control_report() -> dict:
    backend = make_bls_economic_command_signature_verifier_backend_v1()
    key = G2Basic.SkToPk(PUBLIC_TEST_SCALAR)
    message = b"zenodex/isolated-bls-evidence/v1:public-control"
    signature = G2Basic.Sign(PUBLIC_TEST_SCALAR, message)
    common: dict[str, Any] = dict(
        signature_algorithm=BLS_ECONOMIC_COMMAND_SIGNATURE_ALGORITHM_V1,
        signer_public_key="0x" + key.hex(),
        message_bytes=message,
        signature_bytes=signature,
    )
    cases: list[tuple[str, dict[str, Any], bool]] = [
        ("genuine_exact_raw", {}, True),
        ("wrong_message", {"message_bytes": message + b"!"}, False),
        ("foreign_key", {"signer_public_key": "0x" + G2Basic.SkToPk(26).hex()}, False),
        (
            "legacy_prehash",
            {"signature_bytes": G2Basic.Sign(PUBLIC_TEST_SCALAR, hashlib.sha256(message).digest())},
            False,
        ),
        ("short_signature", {"signature_bytes": signature[:-1]}, False),
        ("noncanonical_key", {"signer_public_key": "0X" + key.hex()}, False),
        ("wrong_algorithm", {"signature_algorithm": "BLS12_381_G2_POP_V1"}, False),
    ]
    results = []
    for name, changed, expected in cases:
        actual = backend.verify_command_signature(**(common | changed))
        if actual is not expected:
            raise ValueError(f"real BLS control failed: {name}")
        results.append({"name": name, "accepted": actual})
    return {
        "schema": "zenodex/isolated-bls-controls/v1",
        "public_test_scalar": PUBLIC_TEST_SCALAR,
        "public_key": "0x" + key.hex(),
        "message_hex": message.hex(),
        "signature_hex": signature.hex(),
        "results": results,
        "production_release_qualified": False,
    }


def _observed_runtime_files() -> tuple[dict[str, Path], list[str]]:
    stdlib = Path(sysconfig.get_path("stdlib")).resolve()
    files = {"interpreter/python": Path(sys.executable).resolve()}
    builtins = []
    for name, module in sorted(tuple(sys.modules.items())):
        file = getattr(module, "__file__", None)
        if file is None:
            builtins.append(name)
            continue
        path = Path(file).resolve()
        if path.is_relative_to(stdlib) and "site-packages" not in path.parts and path.is_file():
            files["stdlib/" + path.relative_to(stdlib).as_posix()] = path
    return files, builtins


def _source_files(repo: Path) -> dict[str, Path]:
    source_files = {p.relative_to(repo).as_posix(): p for p in (repo / "src").rglob("*.py")}
    for name in (
        "tools/isolated_bls_evidence_v1.py",
        "tools/prepare_isolated_bls_proof_v1.py",
        "tools/isolated_bls_proof_inputs_v1.py",
        "tests/test_prepare_isolated_bls_proof_v1.py",
        "tests/data/isolated_bls_proof_seed_v1.json",
        "zk/asset_transfer_route_composer_risc0/check_reference.py",
    ):
        source_files[name] = repo / name
    return source_files


def acquire_evidence(repo: Path, output: Path) -> dict:
    """Retain actual preimages before constructing a profile or signing intent."""
    output.mkdir(exist_ok=False)
    report = bls_control_report()
    distributions, runtime_files = _installed_closure()
    observed, builtins = _observed_runtime_files()
    runtime_files.update(observed)
    source_files = _source_files(repo)
    source = snapshot_files(source_files, output / "source")
    runtime = snapshot_files(runtime_files, output / "runtime")
    runtime.update(
        distributions=distributions,
        interpreter_version=sys.version,
        observed_modules_without_file=builtins,
        scope="installed base distributions plus observed stdlib; loaded-code/OS correspondence is an external premise",
    )
    contract = {
        "algorithm": BLS_ECONOMIC_COMMAND_SIGNATURE_ALGORITHM_V1,
        "public_key": "lowercase 0x plus compressed G1, 48 bytes",
        "signature": "compressed G2, 96 bytes",
        "message": "exact economic-command-intent-authentication-message-v1 bytes; no prehash",
        "selection_purpose": "ISOLATED_QUALIFICATION",
        "production_authority": False,
    }
    implementation = {
        "artifact": ARTIFACT,
        "sha256": sha256(read_regular(repo / ARTIFACT)),
        "loaded_code_correspondence_attested": False,
    }
    objects = {
        "source-manifest.json": source,
        "runtime-manifest.json": runtime,
        "bls-controls.json": report,
        "contract.json": contract,
        "implementation.json": implementation,
    }
    for name, value in objects.items():
        (output / name).write_bytes(canonical(value))
    roots = {name: "0x" + sha256(canonical(value)) for name, value in objects.items()}
    (output / "evidence-roots.json").write_bytes(canonical(roots))
    return roots


def load_evidence(directory: Path) -> tuple[dict, dict]:
    names = (
        "source-manifest.json",
        "runtime-manifest.json",
        "bls-controls.json",
        "contract.json",
        "implementation.json",
    )
    roots = closed_json(read_regular(directory / "evidence-roots.json"))
    objects = {}
    for name in names:
        raw = read_regular(directory / name)
        objects[name] = closed_json(raw)
        if raw != canonical(objects[name]) or roots[name] != "0x" + sha256(raw):
            raise ValueError("evidence root or canonical encoding drift")
    verify_snapshot(objects["source-manifest.json"], directory / "source")
    verify_snapshot(objects["runtime-manifest.json"], directory / "runtime")
    return roots, objects


def require_current_evidence(repo: Path, objects: dict) -> None:
    """Reject reuse after changes to the acquired source or installed files."""
    source = objects["source-manifest.json"]
    verify_snapshot(source, repo)
    if set(_source_files(repo)) != {row["path"] for row in source["files"]}:
        raise ValueError("current source inventory drift")
    runtime = objects["runtime-manifest.json"]
    distributions, files = _installed_closure()
    if distributions != runtime["distributions"] or sys.version != runtime["interpreter_version"]:
        raise ValueError("current interpreter or dependency resolution drift")
    files["interpreter/python"] = Path(sys.executable).resolve()
    stdlib = Path(sysconfig.get_path("stdlib")).resolve()
    for row in runtime["files"]:
        name = row["path"]
        if name.startswith("stdlib/"):
            files[name] = stdlib / _relative(name[len("stdlib/") :])
        if name not in files:
            raise ValueError("current runtime inventory drift")
        raw = read_regular(files[name])
        if sha256(raw) != row["sha256"] or len(raw) != row["bytes"]:
            raise ValueError("current runtime content drift")
    if bls_control_report() != objects["bls-controls.json"]:
        raise ValueError("current BLS control replay drift")
