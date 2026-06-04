#!/usr/bin/env python3
"""Build and verify a PUBLIC spot-proof receipt.

The spot-DEX formal proofs (ESSO models, Lean theorems, Rust Kani harnesses) are
run by toolchains that are NOT available in ordinary PR CI: ``external/ESSO`` and
``external/mathlib4`` are gitignored, and the Kani sweep is a scheduled/manual
workflow. This mirrors the kernel-assurance pattern
(``tools/check_kernel_assurance_public_receipt.py``): a privileged ``build`` run
(with the toolchains) records each proof's verdict + the sha256 of its tracked
source file(s) into a committed, self-contained public receipt; a public ``check``
run (no toolchains) re-hashes the same tracked sources and validates the receipt.

What ``check`` guarantees (and what it does NOT):
* GUARANTEES: the proof sources committed today are byte-identical to the ones a
  ``build`` run recorded a VERIFIED verdict for, and the receipt is tamper-evident
  (canonical receipt_sha256). So a proof source cannot drift without either a CI
  failure or a fresh ``build`` (which re-runs the proof).
* DOES NOT: re-run the solver/prover on every PR. The heavy verification stays in
  the privileged ``build`` step (and the scheduled/manual proof workflows). ``check``
  is integrity + freshness, exactly like the kernel-assurance public receipt.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import subprocess
import sys
from pathlib import Path
from typing import Any, Mapping

ROOT = Path(__file__).resolve().parents[1]
DEFAULT_MANIFEST = ROOT / "tools" / "spot_proof_public_manifest.json"
DEFAULT_RECEIPT = ROOT / "docs" / "assurance" / "spot_proof_public_receipt.json"
RECEIPT_SCHEMA = "zenodex.spot_proof.public_receipt.v1"


class ReceiptError(ValueError):
    pass


def _canonical_json_bytes(obj: Any) -> bytes:
    return json.dumps(obj, sort_keys=True, separators=(",", ":"), ensure_ascii=False).encode("utf-8")


def _sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def _sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def _load_json_object(path: Path, *, name: str) -> dict[str, Any]:
    try:
        obj = json.loads(path.read_text(encoding="utf-8"))
    except FileNotFoundError as exc:
        raise ReceiptError(f"{name} missing: {path}") from exc
    except Exception as exc:
        raise ReceiptError(f"{name} is not valid JSON: {path}: {exc}") from exc
    if not isinstance(obj, dict):
        raise ReceiptError(f"{name} must be a JSON object: {path}")
    return obj


def _require_string(obj: Any, *, name: str) -> str:
    if not isinstance(obj, str) or not obj:
        raise ReceiptError(f"{name} must be a non-empty string")
    return obj


def _manifest_proofs(manifest: Mapping[str, Any]) -> dict[str, Mapping[str, Any]]:
    proofs = manifest.get("proofs")
    if not isinstance(proofs, list) or not proofs:
        raise ReceiptError("manifest.proofs must be a non-empty list")
    out: dict[str, Mapping[str, Any]] = {}
    for i, entry in enumerate(proofs):
        if not isinstance(entry, Mapping):
            raise ReceiptError(f"manifest.proofs[{i}] must be an object")
        pid = _require_string(entry.get("id"), name=f"manifest.proofs[{i}].id")
        tool = _require_string(entry.get("tool"), name=f"{pid}.tool")
        if tool not in ("esso-verify-multi", "lean-lake-build"):
            raise ReceiptError(f"{pid}.tool unsupported: {tool!r}")
        srcs = entry.get("source_files")
        if not isinstance(srcs, list) or not srcs or not all(isinstance(s, str) and s for s in srcs):
            raise ReceiptError(f"{pid}.source_files must be a non-empty list of paths")
        _require_string(entry.get("required_verdict"), name=f"{pid}.required_verdict")
        if pid in out:
            raise ReceiptError(f"duplicate manifest proof id: {pid}")
        out[pid] = entry
    return out


def _source_hashes(entry: Mapping[str, Any], *, pid: str) -> list[dict[str, str]]:
    out: list[dict[str, str]] = []
    for rel in entry["source_files"]:
        p = ROOT / rel
        if not p.is_file():
            raise ReceiptError(f"{pid}: source file missing: {rel}")
        out.append({"path": rel, "sha256": _sha256_file(p)})
    return out


# --- proof runners (build side only; require the toolchains) ------------------


def _run_esso(model_rel: str) -> dict[str, Any]:
    env = dict(os.environ, PYTHONPATH=str(ROOT / "external" / "ESSO"))
    proc = subprocess.run(
        [sys.executable, "-m", "ESSO", "verify-multi", model_rel, "--solvers", "z3,cvc5"],
        capture_output=True, text=True, env=env, cwd=str(ROOT), timeout=600,
    )
    payload = json.loads(proc.stdout)
    if payload.get("ok") is not True:
        raise ReceiptError(f"ESSO verify-multi not ok for {model_rel}")
    r = payload["report"]
    return {
        "verdict": r["verdict"],
        "ir_hash": r["ir_hash"],
        "passed_queries": r["passed_queries"],
        "solvers": r["tool_versions"]["solvers"],
        "solvers_agreed": r["solvers_agreed"],
    }


def _run_lean(module: str, source_rels: list[str]) -> dict[str, Any]:
    proc = subprocess.run(
        ["lake", "build", module], capture_output=True, text=True,
        cwd=str(ROOT / "lean-mathlib"), timeout=1800,
    )
    if proc.returncode != 0:
        raise ReceiptError(f"lake build failed for {module}: {proc.stderr[-400:]}")
    # lake build SUCCEEDS even with `sorry` (it is a warning, not an error), so the
    # NO_SORRY verdict must be earned by an explicit token check on the sources.
    import re

    forbidden = re.compile(r"\b(sorry|admit|sorryAx)\b|\baxiom\b")
    for rel in source_rels:
        if forbidden.search((ROOT / rel).read_text(encoding="utf-8")):
            raise ReceiptError(f"{module}: forbidden token (sorry/admit/axiom) in {rel}")
    toolchain = (ROOT / "lean-mathlib" / "lean-toolchain").read_text(encoding="utf-8").strip()
    return {"verdict": "BUILT_NO_SORRY", "lean_toolchain": toolchain, "module": module}


def _build_proof_entry(entry: Mapping[str, Any]) -> dict[str, Any]:
    pid = entry["id"]
    tool = entry["tool"]
    out: dict[str, Any] = {"id": pid, "tool": tool, "source_files": _source_hashes(entry, pid=pid)}
    if tool == "esso-verify-multi":
        result = _run_esso(entry["source_files"][0])
    elif tool == "lean-lake-build":
        result = _run_lean(_require_string(entry.get("module"), name=f"{pid}.module"), list(entry["source_files"]))
    else:  # pragma: no cover - guarded by _manifest_proofs
        raise ReceiptError(f"{pid}.tool unsupported: {tool!r}")
    if result["verdict"] != entry["required_verdict"]:
        raise ReceiptError(f"{pid}: verdict {result['verdict']} != required {entry['required_verdict']}")
    out["result"] = result
    return out


# --- receipt build / verify ---------------------------------------------------


def _receipt_hash_body(receipt: Mapping[str, Any]) -> dict[str, Any]:
    return {k: v for k, v in receipt.items() if k != "receipt_sha256"}


def build_receipt(manifest: Mapping[str, Any], *, manifest_sha256: str, manifest_relpath: str) -> dict[str, Any]:
    proofs = [_build_proof_entry(e) for e in (_manifest_proofs(manifest)[pid] for pid in sorted(_manifest_proofs(manifest)))]
    receipt: dict[str, Any] = {
        "schema": RECEIPT_SCHEMA,
        "ok": True,
        "manifest": manifest_relpath,
        "manifest_sha256": manifest_sha256,
        "private_toolchain_source_included": False,
        "proofs": proofs,
    }
    receipt["receipt_sha256"] = _sha256_bytes(_canonical_json_bytes(_receipt_hash_body(receipt)))
    return receipt


def verify_receipt(receipt: Mapping[str, Any], *, manifest: Mapping[str, Any], manifest_sha256: str) -> list[str]:
    errors: list[str] = []

    if receipt.get("schema") != RECEIPT_SCHEMA:
        errors.append(f"schema: expected {RECEIPT_SCHEMA}, got {receipt.get('schema')!r}")
    if receipt.get("ok") is not True:
        errors.append("receipt.ok must be true")
    if receipt.get("manifest_sha256") != manifest_sha256:
        errors.append(f"manifest_sha256 mismatch: expected {manifest_sha256}, got {receipt.get('manifest_sha256')!r}")
    if receipt.get("private_toolchain_source_included") is not False:
        errors.append("private_toolchain_source_included must be false")

    # receipt is tamper-evident
    supplied = receipt.get("receipt_sha256")
    if not isinstance(supplied, str) or not supplied:
        errors.append("receipt_sha256 missing")
    else:
        actual = _sha256_bytes(_canonical_json_bytes(_receipt_hash_body(receipt)))
        if supplied != actual:
            errors.append(f"receipt_sha256 mismatch: expected {actual}, got {supplied}")

    try:
        manifest_by_id = _manifest_proofs(manifest)
    except ReceiptError as exc:
        errors.append(f"manifest: {exc}")
        return errors

    receipt_proofs = receipt.get("proofs")
    if not isinstance(receipt_proofs, list):
        errors.append("receipt.proofs must be a list")
        return errors
    receipt_by_id = {p.get("id"): p for p in receipt_proofs if isinstance(p, Mapping)}

    missing = sorted(set(manifest_by_id) - set(receipt_by_id))
    extra = sorted(set(receipt_by_id) - set(manifest_by_id))
    if missing:
        errors.append(f"receipt missing proofs from manifest: {missing}")
    if extra:
        errors.append(f"receipt has proofs outside manifest: {extra}")

    for pid in sorted(set(manifest_by_id) & set(receipt_by_id)):
        m = manifest_by_id[pid]
        r = receipt_by_id[pid]
        # verdict matches the manifest requirement
        result = r.get("result")
        if not isinstance(result, Mapping) or result.get("verdict") != m.get("required_verdict"):
            errors.append(f"{pid}: receipt verdict {result.get('verdict') if isinstance(result, Mapping) else None!r} != required {m.get('required_verdict')!r}")
        # the tracked sources today must byte-match the receipt's pinned hashes
        try:
            current = {h["path"]: h["sha256"] for h in _source_hashes(m, pid=pid)}
        except ReceiptError as exc:
            errors.append(f"{pid}: {exc}")
            continue
        pinned = {h.get("path"): h.get("sha256") for h in (r.get("source_files") or []) if isinstance(h, Mapping)}
        if pinned != current:
            errors.append(f"{pid}: source hashes drifted from the receipt (re-run `build`): pinned={pinned} current={current}")

    return errors


def check_receipt_file(receipt_path: Path = DEFAULT_RECEIPT, manifest_path: Path = DEFAULT_MANIFEST) -> dict[str, Any]:
    errors: list[str] = []
    try:
        manifest = _load_json_object(manifest_path, name="spot-proof manifest")
        manifest_sha256 = _sha256_file(manifest_path)
        receipt = _load_json_object(receipt_path, name="spot-proof public receipt")
        errors.extend(verify_receipt(receipt, manifest=manifest, manifest_sha256=manifest_sha256))
    except ReceiptError as exc:
        errors.append(str(exc))
    except Exception as exc:  # noqa: BLE001 - a release checker fails closed on ANY error
        errors.append(f"{type(exc).__name__}: {exc}")
    return {
        "schema": "zenodex.spot_proof.public_receipt_check.v1",
        "ok": not errors,
        "receipt": str(receipt_path),
        "manifest": str(manifest_path),
        "errors": errors,
    }


def _cmd_build(args: argparse.Namespace) -> int:
    manifest_path = Path(args.manifest).expanduser().resolve()
    out_path = Path(args.out).expanduser().resolve()
    manifest = _load_json_object(manifest_path, name="spot-proof manifest")
    try:
        manifest_relpath = manifest_path.relative_to(ROOT).as_posix()
    except ValueError:
        manifest_relpath = str(manifest_path)
    receipt = build_receipt(manifest, manifest_sha256=_sha256_file(manifest_path), manifest_relpath=manifest_relpath)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps(receipt, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(json.dumps({"ok": True, "out": str(out_path), "proofs": [p["id"] for p in receipt["proofs"]]}))
    return 0


def _cmd_check(args: argparse.Namespace) -> int:
    report = check_receipt_file(
        receipt_path=Path(args.receipt).expanduser().resolve(),
        manifest_path=Path(args.manifest).expanduser().resolve(),
    )
    print(json.dumps(report, indent=2 if args.pretty else None, sort_keys=True))
    return 0 if report["ok"] else 1


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Build or verify the public spot-proof receipt.")
    sub = parser.add_subparsers(dest="command")
    b = sub.add_parser("build", help="Run the proofs (needs toolchains) and emit the committed receipt.")
    b.add_argument("--manifest", default=str(DEFAULT_MANIFEST))
    b.add_argument("--out", default=str(DEFAULT_RECEIPT))
    b.set_defaults(func=_cmd_build)
    c = sub.add_parser("check", help="Verify the committed receipt (no toolchains; CI entrypoint).")
    c.add_argument("--receipt", default=str(DEFAULT_RECEIPT))
    c.add_argument("--manifest", default=str(DEFAULT_MANIFEST))
    c.add_argument("--pretty", action="store_true")
    c.set_defaults(func=_cmd_check)
    parser.set_defaults(func=_cmd_check, receipt=str(DEFAULT_RECEIPT), manifest=str(DEFAULT_MANIFEST), pretty=False)
    args = parser.parse_args(argv)
    try:
        return int(args.func(args))
    except ReceiptError as exc:
        print(json.dumps({"ok": False, "errors": [str(exc)]}))
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
