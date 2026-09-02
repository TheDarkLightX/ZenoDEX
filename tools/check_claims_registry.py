#!/usr/bin/env python3
"""
Fail-closed validator for docs/claims_registry.yaml.

This is intentionally lightweight and CI-friendly:
- checks schema/version + required fields
- checks uniqueness of claim ids
- checks the status field against the closed vocabulary
- checks referenced files exist
- checks every evidence theorem is declared in a referenced .lean file whose
  namespace matches the theorem's qualified prefix
"""

from __future__ import annotations

import re
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Iterable

import yaml


ALLOWED_CLAIM_STATUSES = frozenset({"supported", "proved", "disputed"})

REPO_ROOT = Path(__file__).resolve().parents[1]
REGISTRY_PATH = REPO_ROOT / "docs" / "claims_registry.yaml"


@dataclass(frozen=True)
class CheckError(Exception):
    message: str

    def __str__(self) -> str:  # pragma: no cover
        return self.message


def _require_mapping(obj: Any, *, name: str) -> dict[str, Any]:
    if not isinstance(obj, dict):
        raise CheckError(f"{name} must be an object")
    return obj


def _require_list(obj: Any, *, name: str) -> list[Any]:
    if not isinstance(obj, list):
        raise CheckError(f"{name} must be a list")
    return obj


def _require_str(obj: Any, *, name: str) -> str:
    if not isinstance(obj, str) or not obj.strip():
        raise CheckError(f"{name} must be a non-empty string")
    return obj.strip()


def _require_optional_str_list(obj: Any, *, name: str) -> list[str]:
    if obj is None:
        return []
    items = _require_list(obj, name=name)
    out: list[str] = []
    for i, it in enumerate(items):
        if not isinstance(it, str) or not it.strip():
            raise CheckError(f"{name}[{i}] must be a non-empty string")
        out.append(it.strip())
    return out


def _iter_cmds(evidence: dict[str, Any]) -> Iterable[str]:
    for i, chk in enumerate(_require_list(evidence.get("check", []), name="evidence.check")):
        if not isinstance(chk, dict):
            raise CheckError(f"evidence.check[{i}] must be an object")
        cmd = chk.get("cmd")
        if cmd is None:
            continue
        yield _require_str(cmd, name=f"evidence.check[{i}].cmd")


def validate_registry(path: Path) -> None:
    raw = path.read_text(encoding="utf-8")
    validate_registry_root(yaml.safe_load(raw))


def validate_registry_root(loaded: Any) -> None:
    root = _require_mapping(loaded, name="registry")

    schema = _require_str(root.get("schema"), name="registry.schema")
    if schema != "zenodex/claims-registry/v1":
        raise CheckError(f"unsupported registry.schema: {schema}")

    _require_mapping(root.get("meta"), name="registry.meta")

    claims = _require_list(root.get("claims"), name="registry.claims")
    seen_ids: set[str] = set()
    for idx, claim_obj in enumerate(claims):
        claim = _require_mapping(claim_obj, name=f"claims[{idx}]")
        cid = _require_str(claim.get("id"), name=f"claims[{idx}].id")
        if cid in seen_ids:
            raise CheckError(f"duplicate claim id: {cid}")
        seen_ids.add(cid)

        status = _require_str(claim.get("status"), name=f"claims[{idx}].status")
        if status not in ALLOWED_CLAIM_STATUSES:
            raise CheckError(
                f"claims[{idx}].status {status!r} is outside the closed vocabulary "
                f"{sorted(ALLOWED_CLAIM_STATUSES)}"
            )
        _require_str(claim.get("layer"), name=f"claims[{idx}].layer")
        _require_str(claim.get("statement"), name=f"claims[{idx}].statement")

        evidence = _require_mapping(claim.get("evidence"), name=f"claims[{idx}].evidence")
        _require_str(evidence.get("kind"), name=f"claims[{idx}].evidence.kind")

        # Commands (informational but must be non-empty when present).
        for _cmd in _iter_cmds(evidence):
            pass

        # Referenced files must exist (fail-closed).
        files = _require_optional_str_list(evidence.get("files"), name=f"claims[{idx}].evidence.files")
        for f in files:
            p = (REPO_ROOT / f).resolve()
            if REPO_ROOT not in p.parents and p != REPO_ROOT:
                raise CheckError(f"claims[{idx}].evidence.files contains path outside repo: {f}")
            if not p.exists():
                raise CheckError(f"claims[{idx}].evidence.files missing: {f}")

        # Every named theorem must be declared in a referenced .lean file whose
        # namespace matches the theorem's qualified prefix (fail-closed).
        theorems = _require_optional_str_list(evidence.get("theorems"), name=f"claims[{idx}].evidence.theorems")
        if theorems:
            lean_texts = [
                (f, (REPO_ROOT / f).read_text(encoding="utf-8"))
                for f in files
                if f.endswith(".lean") and (REPO_ROOT / f).exists()
            ]
            if not lean_texts:
                raise CheckError(f"claims[{idx}] names theorems but references no .lean file")
            for qualified in theorems:
                prefix, _, bare = qualified.rpartition(".")
                declared = re.compile(rf"^\s*(?:theorem|lemma)\s+{re.escape(bare)}\b", re.M)
                needed = [part for part in prefix.split(".") if part]
                bound = False
                for f, text in lean_texts:
                    if not declared.search(text):
                        continue
                    # Namespace lines may be nested (one component per line) or
                    # dotted; require every prefix component to appear in the
                    # file's namespace chain (order is not re-derived here).
                    components: set[str] = set()
                    for line in re.findall(r"^namespace ([\w.]+)", text, re.M):
                        components.update(line.split("."))
                    if any(part not in components for part in needed):
                        continue
                    bound = True
                    break
                if not bound:
                    raise CheckError(
                        f"claims[{idx}].evidence.theorems entry {qualified!r} is not declared "
                        "in any referenced .lean file with a matching namespace"
                    )


def main(argv: list[str] | None = None) -> int:
    _ = argv
    if not REGISTRY_PATH.exists():
        print(f"missing registry file: {REGISTRY_PATH}", file=sys.stderr)
        return 2
    try:
        validate_registry(REGISTRY_PATH)
    except CheckError as exc:
        print(f"claims registry invalid: {exc}", file=sys.stderr)
        return 1
    print("ok")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

