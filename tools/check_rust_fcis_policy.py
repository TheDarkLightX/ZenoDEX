#!/usr/bin/env python3
"""Fail-closed Rust functional-core policy and inventory validator.

This checker is intentionally conservative. It does not prove the Rust core
correct. It prevents authority promotion from outrunning the repository's
machine-readable surface inventory and establishes a no-regression ratchet for
host effects, interior mutability, unordered collections, floating point, unsafe
code, and panic-family calls in production core source.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
import tomllib
from dataclasses import dataclass
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
DEFAULT_MANIFEST = ROOT / "docs/runtime/RUST_VALUE_MOVEMENT_INVENTORY_V1.json"
CORE_ROOT = ROOT / "rust-runtime/crates/zenodex-runtime-core/src"
CORE_LIB = CORE_ROOT / "lib.rs"
TOOLCHAIN = ROOT / "rust-runtime/rust-toolchain.toml"
CARGO_LOCK = ROOT / "rust-runtime/Cargo.lock"
PUBLIC_TESTNET = ROOT / "config/deploy/public-testnet.yaml"
PRODUCTION_STRICT = ROOT / "config/deploy/production-strict.yaml"

SCHEMA = "zenodex.rust_value_movement_inventory.v1"
RUST_AUTHORITY_MODES = {"rust_authority", "rust_authority_with_python_shadow"}
INTERNAL_AUTHORITY = {"internal_support"}

PROFILE_SURFACE_ALIASES = {
    "zusd_single_vault": "zusd",
    "perp_stateful_isolated": "perp_stateful",
}

HARD_FORBIDDEN_PATTERNS: tuple[tuple[str, re.Pattern[str]], ...] = (
    ("unsafe construct", re.compile(r"\bunsafe\s*(?:fn|trait|impl|\{)")),
    ("HashMap", re.compile(r"\bHashMap\b")),
    ("HashSet", re.compile(r"\bHashSet\b")),
    ("Cell", re.compile(r"\bCell\b")),
    ("RefCell", re.compile(r"\bRefCell\b")),
    ("UnsafeCell", re.compile(r"\bUnsafeCell\b")),
    ("Mutex", re.compile(r"\bMutex\b")),
    ("RwLock", re.compile(r"\bRwLock\b")),
    (
        "atomic type",
        re.compile(r"\bAtomic(?:Bool|U8|U16|U32|U64|Usize|I8|I16|I32|I64|Isize|Ptr)\b"),
    ),
    ("system time", re.compile(r"\bstd::time\b")),
    ("environment access", re.compile(r"\bstd::env\b")),
    ("filesystem access", re.compile(r"\bstd::fs\b")),
    ("network access", re.compile(r"\bstd::net\b")),
    ("thread access", re.compile(r"\bstd::thread\b")),
    ("randomness", re.compile(r"\brand(?:::|\b)")),
    ("floating point f32", re.compile(r"\bf32\b")),
    ("floating point f64", re.compile(r"\bf64\b")),
    ("panic macro", re.compile(r"\bpanic!\s*\(")),
    ("todo macro", re.compile(r"\btodo!\s*\(")),
    ("unimplemented macro", re.compile(r"\bunimplemented!\s*\(")),
    ("unwrap call", re.compile(r"\.unwrap\s*\(")),
)


@dataclass(frozen=True)
class AuthorityProfile:
    default: str
    per_surface: dict[str, str]
    promoted: tuple[str, ...]


class ValidationError(Exception):
    """Raised for malformed validator inputs, not policy failures."""


def _load_json(path: Path) -> dict[str, Any]:
    try:
        raw = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        raise ValidationError(f"cannot load manifest {path}: {exc}") from exc
    if not isinstance(raw, dict):
        raise ValidationError("manifest root must be an object")
    return raw


def _production_source(text: str) -> str:
    """Return the production prefix and remove line comments.

    Core modules currently put their unit/proptest module after the first
    ``#[cfg(test)]`` marker. The policy intentionally ignores that test-only
    suffix. Line comments and Rust doc comments are removed to avoid matching
    policy terminology in prose.
    """

    prefix = text.split("#[cfg(test)]", 1)[0]
    return "\n".join(line.split("//", 1)[0] for line in prefix.splitlines())


def _public_modules(lib_text: str) -> set[str]:
    return set(re.findall(r"^pub\s+mod\s+([a-zA-Z0-9_]+)\s*;", lib_text, flags=re.MULTILINE))


def _parse_authority_profile(path: Path) -> AuthorityProfile:
    """Parse the small runtime_authority_policy YAML subset without a YAML dependency."""

    default = ""
    per_surface: dict[str, str] = {}
    promoted: list[str] = []
    in_policy = False
    subsection = ""

    for raw_line in path.read_text(encoding="utf-8").splitlines():
        stripped = raw_line.strip()
        if not stripped or stripped.startswith("#"):
            continue
        indent = len(raw_line) - len(raw_line.lstrip(" "))
        if stripped == "runtime_authority_policy:":
            in_policy = True
            subsection = ""
            continue
        if not in_policy:
            continue
        if indent == 0:
            break
        if stripped.startswith("default:"):
            default = stripped.split(":", 1)[1].strip()
            continue
        if stripped == "per_surface:":
            subsection = "per_surface"
            continue
        if stripped == "promoted_surfaces:":
            subsection = "promoted"
            continue
        if subsection == "per_surface" and ":" in stripped and not stripped.startswith("-"):
            key, value = stripped.split(":", 1)
            per_surface[key.strip()] = value.strip()
        elif subsection == "promoted" and stripped.startswith("-"):
            promoted.append(stripped[1:].strip())

    if not default:
        raise ValidationError(f"{path}: missing runtime authority default")
    return AuthorityProfile(default=default, per_surface=per_surface, promoted=tuple(promoted))


def _exception_table(manifest: dict[str, Any], errors: list[str]) -> dict[tuple[str, str], int]:
    table: dict[tuple[str, str], int] = {}
    exceptions = manifest.get("temporary_policy_exceptions")
    if not isinstance(exceptions, list):
        errors.append("temporary_policy_exceptions must be a list")
        return table
    for index, item in enumerate(exceptions):
        if not isinstance(item, dict):
            errors.append(f"temporary_policy_exceptions[{index}] must be an object")
            continue
        path = item.get("path")
        token = item.get("token")
        max_count = item.get("max_count")
        blocker = item.get("blocker")
        reason = item.get("reason")
        if not isinstance(path, str) or not path:
            errors.append(f"temporary_policy_exceptions[{index}].path is invalid")
            continue
        if not isinstance(token, str) or not token:
            errors.append(f"temporary_policy_exceptions[{index}].token is invalid")
            continue
        if not isinstance(max_count, int) or isinstance(max_count, bool) or max_count < 0:
            errors.append(f"temporary_policy_exceptions[{index}].max_count is invalid")
            continue
        if not isinstance(blocker, str) or not blocker:
            errors.append(f"temporary_policy_exceptions[{index}].blocker is invalid")
        if not isinstance(reason, str) or not reason:
            errors.append(f"temporary_policy_exceptions[{index}].reason is invalid")
        key = (path, token)
        if key in table:
            errors.append(f"duplicate policy exception for {path!r} {token!r}")
        table[key] = max_count
    return table


def validate_manifest(manifest: dict[str, Any]) -> list[str]:
    errors: list[str] = []
    if manifest.get("schema") != SCHEMA:
        errors.append(f"schema must equal {SCHEMA!r}")

    release_claim = manifest.get("release_claim")
    if not isinstance(release_claim, dict):
        errors.append("release_claim must be an object")
    else:
        status = release_claim.get("status")
        if status not in {"blocked", "released"}:
            errors.append("release_claim.status must be blocked or released")
        if not isinstance(release_claim.get("reason"), str) or not release_claim.get("reason"):
            errors.append("release_claim.reason must be non-empty")

    required_modules_raw = manifest.get("required_core_modules")
    if not isinstance(required_modules_raw, list) or not all(
        isinstance(item, str) and item for item in required_modules_raw
    ):
        errors.append("required_core_modules must be a non-empty string list")
        required_modules: set[str] = set()
    else:
        required_modules = set(required_modules_raw)
        if len(required_modules) != len(required_modules_raw):
            errors.append("required_core_modules contains duplicates")

    if not CORE_LIB.exists():
        errors.append(f"missing Rust core library {CORE_LIB.relative_to(ROOT)}")
        actual_modules: set[str] = set()
    else:
        lib_text = CORE_LIB.read_text(encoding="utf-8")
        actual_modules = _public_modules(lib_text)
        if "#![forbid(unsafe_code)]" not in lib_text:
            errors.append("Rust core lib.rs must contain #![forbid(unsafe_code)]")

    missing_from_inventory = sorted(actual_modules - required_modules)
    stale_inventory_modules = sorted(required_modules - actual_modules)
    if missing_from_inventory:
        errors.append(f"Rust pub modules missing from inventory: {missing_from_inventory}")
    if stale_inventory_modules:
        errors.append(f"inventory modules absent from Rust lib.rs: {stale_inventory_modules}")

    surfaces = manifest.get("surfaces")
    if not isinstance(surfaces, list) or not surfaces:
        errors.append("surfaces must be a non-empty list")
        surfaces = []

    ids: set[str] = set()
    modules_seen: dict[str, str] = {}
    for index, surface in enumerate(surfaces):
        label = f"surfaces[{index}]"
        if not isinstance(surface, dict):
            errors.append(f"{label} must be an object")
            continue
        surface_id = surface.get("surface_id")
        if not isinstance(surface_id, str) or not surface_id:
            errors.append(f"{label}.surface_id is invalid")
            continue
        if surface_id in ids:
            errors.append(f"duplicate surface_id {surface_id!r}")
        ids.add(surface_id)

        kind = surface.get("kind")
        if kind not in {"value_moving", "authority_support"}:
            errors.append(f"{surface_id}: invalid kind {kind!r}")

        modules = surface.get("rust_modules")
        if (
            not isinstance(modules, list)
            or not modules
            or not all(isinstance(item, str) and item for item in modules)
        ):
            errors.append(f"{surface_id}: rust_modules must be a non-empty string list")
            modules = []
        for module in modules:
            previous = modules_seen.get(module)
            if previous is not None:
                errors.append(
                    f"Rust module {module!r} is assigned to both {previous!r} and {surface_id!r}"
                )
            modules_seen[module] = surface_id
            path = CORE_ROOT / f"{module}.rs"
            if not path.exists():
                errors.append(f"{surface_id}: missing Rust module file {path.relative_to(ROOT)}")

        for field in (
            "rust_entrypoints",
            "python_sources",
            "formal_artifacts",
            "value_domains",
            "known_blockers",
        ):
            value = surface.get(field)
            if not isinstance(value, list) or not all(isinstance(item, str) for item in value):
                errors.append(f"{surface_id}: {field} must be a string list")

        formal_artifacts = surface.get("formal_artifacts")
        if isinstance(formal_artifacts, list):
            for artifact in formal_artifacts:
                if not isinstance(artifact, str) or not artifact:
                    continue
                artifact_path = ROOT / artifact
                if not artifact_path.exists():
                    errors.append(f"{surface_id}: formal_artifact does not exist: {artifact}")

        public_authority = surface.get("public_testnet_authority")
        production_authority = surface.get("production_strict_authority")
        cbc_grade = surface.get("cbc_grade")
        release_status = surface.get("release_status")
        effect_ownership = surface.get("effect_ownership")
        atomic_commit = surface.get("atomic_commit")

        if public_authority not in set(manifest.get("authority_modes", [])) | INTERNAL_AUTHORITY:
            errors.append(f"{surface_id}: invalid public_testnet_authority")
        if (
            production_authority
            not in set(manifest.get("authority_modes", [])) | INTERNAL_AUTHORITY
        ):
            errors.append(f"{surface_id}: invalid production_strict_authority")
        if cbc_grade not in set(manifest.get("cbc_grades", [])):
            errors.append(f"{surface_id}: invalid cbc_grade")
        if release_status not in {"eligible", "blocked"}:
            errors.append(f"{surface_id}: release_status must be eligible or blocked")
        if not isinstance(effect_ownership, str) or not effect_ownership:
            errors.append(f"{surface_id}: effect_ownership must be non-empty")
        if not isinstance(atomic_commit, str) or not atomic_commit:
            errors.append(f"{surface_id}: atomic_commit must be non-empty")

        if production_authority in RUST_AUTHORITY_MODES and cbc_grade != "full":
            errors.append(f"{surface_id}: production Rust authority requires full CBC grade")
        if (
            public_authority in RUST_AUTHORITY_MODES
            and cbc_grade != "full"
            and release_status != "blocked"
        ):
            errors.append(f"{surface_id}: partial Rust authority must remain release-blocked")
        if (
            kind == "value_moving"
            and atomic_commit != "proved_linearizable_atomic_candidate_commit"
        ):
            if release_status != "blocked":
                errors.append(
                    f"{surface_id}: value-moving surface without proved atomic commit must be blocked"
                )
        if kind == "value_moving" and public_authority in RUST_AUTHORITY_MODES:
            if effect_ownership in {"not_applicable", ""}:
                errors.append(
                    f"{surface_id}: Rust value authority requires explicit effect ownership status"
                )

    if set(modules_seen) != required_modules:
        missing = sorted(required_modules - set(modules_seen))
        extra = sorted(set(modules_seen) - required_modules)
        if missing:
            errors.append(f"required modules not assigned to a surface: {missing}")
        if extra:
            errors.append(f"surface modules not declared required: {extra}")

    if not TOOLCHAIN.exists():
        errors.append("missing rust-runtime/rust-toolchain.toml")
    else:
        try:
            toolchain = tomllib.loads(TOOLCHAIN.read_text(encoding="utf-8"))
        except tomllib.TOMLDecodeError as exc:
            errors.append(f"invalid rust toolchain TOML: {exc}")
        else:
            channel = toolchain.get("toolchain", {}).get("channel")
            if not isinstance(channel, str) or re.fullmatch(r"\d+\.\d+\.\d+", channel) is None:
                errors.append(
                    "Rust toolchain channel must be an exact x.y.z release, not stable/beta/nightly"
                )

    if not CARGO_LOCK.exists():
        errors.append("rust-runtime/Cargo.lock must be committed")

    try:
        public_profile = _parse_authority_profile(PUBLIC_TESTNET)
        strict_profile = _parse_authority_profile(PRODUCTION_STRICT)
    except (OSError, ValidationError) as exc:
        errors.append(str(exc))
    else:
        if strict_profile.default != "python_authority":
            errors.append("production-strict authority default must remain python_authority")
        if strict_profile.per_surface or strict_profile.promoted:
            errors.append(
                "production-strict may not promote Rust surfaces while release claim is blocked"
            )

        for surface in surfaces:
            if not isinstance(surface, dict):
                continue
            surface_id = surface.get("surface_id")
            if not isinstance(surface_id, str):
                continue
            profile_surface = PROFILE_SURFACE_ALIASES.get(surface_id, surface_id)
            expected = surface.get("public_testnet_authority")
            if expected in INTERNAL_AUTHORITY:
                continue
            observed = public_profile.per_surface.get(profile_surface, public_profile.default)
            if observed != expected:
                errors.append(
                    f"{surface_id}: inventory public-testnet authority {expected!r} != profile {observed!r}"
                )
            promoted = profile_surface in public_profile.promoted
            if expected in RUST_AUTHORITY_MODES and expected != "rust_shadow" and not promoted:
                errors.append(
                    f"{surface_id}: Rust authority is not listed in public-testnet promoted_surfaces"
                )
            if expected in {"python_authority", "rust_shadow"} and promoted:
                errors.append(f"{surface_id}: non-Rust authority must not be listed as promoted")

    exception_table = _exception_table(manifest, errors)
    for path in sorted(CORE_ROOT.glob("*.rs")):
        rel = path.relative_to(ROOT).as_posix()
        source = _production_source(path.read_text(encoding="utf-8"))
        for description, pattern in HARD_FORBIDDEN_PATTERNS:
            matches = list(pattern.finditer(source))
            if matches:
                errors.append(f"{rel}: forbidden {description} appears {len(matches)} time(s)")
        for token in (".expect(",):
            count = source.count(token)
            allowed = exception_table.get((rel, token), 0)
            if count > allowed:
                errors.append(f"{rel}: {token!r} count {count} exceeds ratchet allowance {allowed}")

    for (rel, token), allowed in exception_table.items():
        path = ROOT / rel
        if not path.exists():
            errors.append(f"policy exception references missing file {rel}")
            continue
        count = _production_source(path.read_text(encoding="utf-8")).count(token)
        if count > allowed:
            errors.append(f"policy exception {rel} {token!r}: observed {count} > allowed {allowed}")

    if release_claim and release_claim.get("status") == "released":
        blocked_surfaces = [
            surface.get("surface_id")
            for surface in surfaces
            if isinstance(surface, dict) and surface.get("release_status") != "eligible"
        ]
        if blocked_surfaces:
            errors.append(f"released claim has blocked surfaces: {blocked_surfaces}")
        if manifest.get("temporary_policy_exceptions"):
            errors.append("released claim may not retain temporary policy exceptions")

    return errors


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest", type=Path, default=DEFAULT_MANIFEST)
    parser.add_argument("--pretty", action="store_true")
    args = parser.parse_args(argv)

    try:
        manifest = _load_json(args.manifest)
    except ValidationError as exc:
        print(str(exc), file=sys.stderr)
        return 2

    errors = validate_manifest(manifest)
    result = {
        "schema": "zenodex.rust_fcis_policy_validation.v1",
        "manifest": str(
            args.manifest.relative_to(ROOT) if args.manifest.is_relative_to(ROOT) else args.manifest
        ),
        "ok": not errors,
        "error_count": len(errors),
        "errors": errors,
    }
    print(json.dumps(result, indent=2 if args.pretty else None, sort_keys=True))
    return 0 if not errors else 1


if __name__ == "__main__":
    raise SystemExit(main())
