#!/usr/bin/env python3
"""Build deterministic release SBOMs from checked-in lockfiles."""

from __future__ import annotations

import argparse
import base64
import binascii
import hashlib
import json
import re
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
REQ_RE = re.compile(r"^([A-Za-z0-9_.-]+)==([^\\\s]+)")
REQ_HASH_RE = re.compile(r"--hash=([A-Za-z0-9_.-]+):([A-Fa-f0-9]+)")
HASH_ALGORITHMS = {
    "sha256": ("SHA-256", 32),
    "sha384": ("SHA-384", 48),
    "sha512": ("SHA-512", 64),
}


def _canonical_json(data: dict[str, Any]) -> str:
    return json.dumps(data, indent=2, sort_keys=True) + "\n"


def _normalize_name(name: str) -> str:
    return name.replace("_", "-").lower()


def _hash_entry_from_hex(algorithm: str, content: str, *, source: Path) -> dict[str, str]:
    key = algorithm.lower().replace("_", "").replace("-", "")
    if key not in HASH_ALGORITHMS:
        raise ValueError(f"{source} uses unsupported hash algorithm {algorithm!r}")
    cyclonedx_alg, byte_len = HASH_ALGORITHMS[key]
    expected_hex_len = byte_len * 2
    if len(content) != expected_hex_len:
        raise ValueError(
            f"{source} has {algorithm!r} hash with {len(content)} hex characters, expected {expected_hex_len}"
        )
    return {"alg": cyclonedx_alg, "content": content.lower()}


def _hash_entries_from_sri(integrity: str, *, source: Path) -> list[dict[str, str]]:
    entries: list[dict[str, str]] = []
    for token in integrity.split():
        algorithm, separator, encoded = token.partition("-")
        if not separator:
            continue
        key = algorithm.lower().replace("_", "").replace("-", "")
        if key not in HASH_ALGORITHMS:
            continue
        cyclonedx_alg, byte_len = HASH_ALGORITHMS[key]
        try:
            digest = base64.b64decode(encoded, validate=True)
        except (binascii.Error, ValueError) as exc:
            raise ValueError(f"{source} has invalid SRI hash for {algorithm!r}") from exc
        if len(digest) != byte_len:
            raise ValueError(f"{source} has invalid {algorithm!r} digest length {len(digest)}")
        entries.append({"alg": cyclonedx_alg, "content": digest.hex()})
    unique = {json.dumps(item, sort_keys=True): item for item in entries}
    return sorted(unique.values(), key=lambda item: (item["alg"], item["content"]))


def _python_components(lockfile: Path) -> list[dict[str, Any]]:
    if not lockfile.is_file():
        raise FileNotFoundError(f"{lockfile} does not exist")
    components: dict[str, dict[str, Any]] = {}
    current_key: str | None = None
    for raw_line in lockfile.read_text(encoding="utf-8").splitlines():
        stripped = raw_line.strip()
        match = REQ_RE.match(stripped)
        if match is not None:
            name, version = match.groups()
            key = _normalize_name(name)
            components[key] = {
                "bom-ref": f"pkg:pypi/{key}@{version}",
                "hashes": [],
                "name": key,
                "purl": f"pkg:pypi/{key}@{version}",
                "type": "library",
                "version": version,
            }
            current_key = key
            continue
        if current_key is None:
            continue
        for algorithm, content in REQ_HASH_RE.findall(stripped):
            components[current_key]["hashes"].append(
                _hash_entry_from_hex(algorithm, content, source=lockfile)
            )
    for component in components.values():
        unique = {json.dumps(item, sort_keys=True): item for item in component["hashes"]}
        hashes = sorted(unique.values(), key=lambda item: (item["alg"], item["content"]))
        if not hashes:
            raise ValueError(f"{lockfile} has no package hashes for {component['name']}")
        component["hashes"] = hashes
    return [components[key] for key in sorted(components)]


def _npm_components(lockfile: Path) -> list[dict[str, Any]]:
    if not lockfile.is_file():
        raise FileNotFoundError(f"{lockfile} does not exist")
    data = json.loads(lockfile.read_text(encoding="utf-8"))
    packages = data.get("packages")
    if not isinstance(packages, dict):
        raise ValueError(f"{lockfile} packages must be an object")
    components: dict[str, dict[str, Any]] = {}
    for path, payload in packages.items():
        if path == "" or not isinstance(payload, dict):
            continue
        name = payload.get("name")
        version = payload.get("version")
        if not isinstance(name, str) or not name or not isinstance(version, str) or not version:
            if path.startswith("node_modules/"):
                name = path.removeprefix("node_modules/")
            else:
                continue
        purl_name = str(name).replace("@", "%40", 1) if str(name).startswith("@") else str(name)
        component: dict[str, Any] = {
            "bom-ref": f"pkg:npm/{purl_name}@{version}",
            "name": str(name),
            "purl": f"pkg:npm/{purl_name}@{version}",
            "type": "library",
            "version": str(version),
        }
        integrity = payload.get("integrity")
        if isinstance(integrity, str) and integrity:
            hashes = _hash_entries_from_sri(integrity, source=lockfile)
            if hashes:
                component["hashes"] = hashes
        components[component["bom-ref"]] = component
    return [components[key] for key in sorted(components)]


def _bom(*, name: str, components: list[dict[str, Any]]) -> dict[str, Any]:
    serial_input = json.dumps(
        {"components": components, "name": name},
        separators=(",", ":"),
        sort_keys=True,
    )
    serial_hex = hashlib.sha256(serial_input.encode("utf-8")).hexdigest()[:32]
    serial_uuid = f"{serial_hex[:8]}-{serial_hex[8:12]}-{serial_hex[12:16]}-{serial_hex[16:20]}-{serial_hex[20:32]}"
    return {
        "bomFormat": "CycloneDX",
        "components": components,
        "metadata": {
            "component": {
                "name": name,
                "type": "application",
            },
            "tools": [
                {
                    "name": "tools/build_release_sboms.py",
                    "vendor": "ZenoDEX",
                }
            ],
        },
        "serialNumber": f"urn:uuid:{serial_uuid}",
        "specVersion": "1.5",
        "version": 1,
    }


def build_release_sboms(
    *,
    out_dir: Path,
    core_lock: Path = ROOT / "requirements-core.lock.txt",
    agents_lock: Path = ROOT / "requirements-agents.lock.txt",
    ui_lock: Path = ROOT / "tools/dex-ui/package-lock.json",
) -> dict[str, Any]:
    out_dir.mkdir(parents=True, exist_ok=True)
    outputs: list[dict[str, Any]] = []
    for name, lockfile, builder in (
        ("requirements-core", core_lock, _python_components),
        ("requirements-agents", agents_lock, _python_components),
    ):
        components = builder(lockfile)
        path = out_dir / f"{name}.cdx.json"
        path.write_text(_canonical_json(_bom(name=name, components=components)), encoding="utf-8")
        outputs.append({"path": str(path), "component_count": len(components)})

    if ui_lock.is_file():
        components = _npm_components(ui_lock)
        path = out_dir / "dex-ui.cdx.json"
        path.write_text(_canonical_json(_bom(name="dex-ui", components=components)), encoding="utf-8")
        outputs.append({"path": str(path), "component_count": len(components)})

    return {
        "schema": "zenodex.release_sbom_build.v0",
        "ok": True,
        "outputs": outputs,
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out-dir", type=Path, required=True)
    parser.add_argument("--core-lock", type=Path, default=ROOT / "requirements-core.lock.txt")
    parser.add_argument("--agents-lock", type=Path, default=ROOT / "requirements-agents.lock.txt")
    parser.add_argument("--ui-lock", type=Path, default=ROOT / "tools/dex-ui/package-lock.json")
    parser.add_argument("--pretty", action="store_true")
    args = parser.parse_args(argv)
    report = build_release_sboms(
        out_dir=args.out_dir,
        core_lock=args.core_lock,
        agents_lock=args.agents_lock,
        ui_lock=args.ui_lock,
    )
    print(json.dumps(report, indent=2 if args.pretty else None, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
