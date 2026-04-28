from __future__ import annotations

import hashlib
import json
import re
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Mapping, Sequence

import yaml
from jsonschema import Draft202012Validator, FormatChecker

from src.fire.pathing_v1 import fire_formal_assurance_claims_path, fire_formal_assurance_claims_schema_path


FIRE_FORMAL_ASSURANCE_CLAIMS_SCHEMA = "zenodex/fire-formal-assurance-claims/v1"
FIRE_FORMAL_ASSURANCE_CLAIMS_CHECK_REPORT_SCHEMA = "zenodex/fire-formal-assurance-claims-check-report/v1"
LEAN_PROOF_RECEIPT_SCHEMA = "zenodex/lean-proof-receipt/v1"

SETTLEMENT_ADMISSIBILITY_STATEMENT = "FIREVAccept(O, I, Gamma, w, C) -> SettlementSafe(O, I, w, C)"
REQUIRED_EVIDENCE_LEVELS = ("proved", "contract", "implemented", "tested_discovery", "hypothesis")
REQUIRED_RECEIPT_BINDINGS = ("object_hash", "instance_hash", "cert_sha256", "witness_hash", "delta_hash")
NON_AUTHORITATIVE_SURFACES = frozenset({"compiler", "refiner", "registry", "ui_docs"})
REQUIRED_FORBIDDEN_CLAIMS = frozenset(
    {
        "compiler_bug_free",
        "verifier_bug_free",
        "compiler_formally_verified_without_proof_receipt",
        "verifier_formally_verified_without_proof_receipt",
        "acceptance_receipt_authorizes_settlement",
        "private_esso_required_for_public_runtime",
    }
)
LEAN_TRUST_ESCAPE_RE = re.compile(r"\b(sorry|admit|axiom|unsafe|sorryAx)\b")
LEAN_DECLARATION_KINDS = ("theorem", "lemma", "def", "abbrev", "structure", "inductive", "class")


class FireFormalAssuranceClaimsError(RuntimeError):
    pass


@dataclass(frozen=True)
class FireFormalAssuranceClaimsVerification:
    manifest_path: Path
    schema_path: Path
    manifest_sha256: str
    component_count: int
    formally_verified_components: tuple[str, ...]
    settlement_authority_components: tuple[str, ...]
    non_authoritative_components: tuple[str, ...]
    weakest_assurance_level: str

    def to_report_dict(self) -> dict[str, object]:
        return {
            "schema": FIRE_FORMAL_ASSURANCE_CLAIMS_CHECK_REPORT_SCHEMA,
            "ok": True,
            "manifest_path": str(self.manifest_path),
            "schema_path": str(self.schema_path),
            "manifest_sha256": self.manifest_sha256,
            "component_count": self.component_count,
            "formally_verified_components": list(self.formally_verified_components),
            "settlement_authority_components": list(self.settlement_authority_components),
            "non_authoritative_components": list(self.non_authoritative_components),
            "weakest_assurance_level": self.weakest_assurance_level,
        }


def _sha256_file(path: Path) -> str:
    return "sha256:" + hashlib.sha256(path.read_bytes()).hexdigest()


def _lean_toolchain(repo_root: Path) -> str:
    path = repo_root / "lean-mathlib" / "lean-toolchain"
    _expect(path.is_file(), "Lean proof receipt checking requires lean-mathlib/lean-toolchain")
    value = path.read_text(encoding="utf-8").strip()
    _expect(bool(value), "lean-mathlib/lean-toolchain must be non-empty")
    return value


def _is_sha256(value: object) -> bool:
    return (
        isinstance(value, str)
        and value.startswith("sha256:")
        and len(value) == 71
        and all(ch in "0123456789abcdef" for ch in value[7:])
    )


def _as_mapping(value: object, *, ctx: str) -> Mapping[str, object]:
    if not isinstance(value, Mapping):
        raise FireFormalAssuranceClaimsError(f"{ctx}: expected object")
    return value


def _as_sequence(value: object, *, ctx: str) -> Sequence[object]:
    if not isinstance(value, Sequence) or isinstance(value, (str, bytes, bytearray)):
        raise FireFormalAssuranceClaimsError(f"{ctx}: expected array")
    return value


def _as_bool(value: object, *, ctx: str) -> bool:
    if not isinstance(value, bool):
        raise FireFormalAssuranceClaimsError(f"{ctx}: expected bool")
    return bool(value)


def _load_yaml(path: Path) -> Mapping[str, object]:
    try:
        payload = yaml.safe_load(path.read_text(encoding="utf-8"))
    except Exception as exc:
        raise FireFormalAssuranceClaimsError(f"failed to read YAML {path}: {exc}") from exc
    return _as_mapping(payload, ctx=str(path))


def _load_json(path: Path) -> Mapping[str, object]:
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except Exception as exc:
        raise FireFormalAssuranceClaimsError(f"failed to read JSON {path}: {exc}") from exc
    return _as_mapping(payload, ctx=str(path))


def _error_path(error: Any) -> str:
    if not error.path:
        return "/"
    return "/" + "/".join(str(item) for item in error.path)


def _validate_schema(payload: Mapping[str, object], *, schema_path: Path) -> None:
    schema = _load_json(schema_path)
    validator = Draft202012Validator(schema, format_checker=FormatChecker())
    errors = sorted(validator.iter_errors(payload), key=lambda item: tuple(item.path))
    if errors:
        first = errors[0]
        raise FireFormalAssuranceClaimsError(f"schema_invalid:{_error_path(first)}:{first.message}")


def _expect(condition: bool, message: str) -> None:
    if not condition:
        raise FireFormalAssuranceClaimsError(message)


def _string_set(values: object, *, ctx: str) -> set[str]:
    result: set[str] = set()
    for idx, value in enumerate(_as_sequence(values, ctx=ctx)):
        _expect(isinstance(value, str) and bool(value), f"{ctx}[{idx}]: expected non-empty string")
        result.add(value)
    return result


def _string_tuple(values: object, *, ctx: str) -> tuple[str, ...]:
    result: list[str] = []
    for idx, value in enumerate(_as_sequence(values, ctx=ctx)):
        _expect(isinstance(value, str) and bool(value), f"{ctx}[{idx}]: expected non-empty string")
        result.append(value)
    return tuple(result)


def _component_paths_exist(component: Mapping[str, object], *, repo_root: Path) -> None:
    component_id = str(component["id"])
    for rel in _string_tuple(component.get("paths"), ctx=f"components[{component_id}].paths"):
        path = repo_root / rel
        _expect(path.exists(), f"{component_id}: missing declared path {rel}")


def _require_nonempty_str(value: object, *, ctx: str) -> str:
    _expect(isinstance(value, str) and bool(value), f"{ctx}: expected non-empty string")
    return str(value)


def _strip_lean_comments(text: str) -> str:
    out: list[str] = []
    idx = 0
    block_depth = 0
    while idx < len(text):
        nxt = text[idx : idx + 2]
        if block_depth > 0:
            if nxt == "/-":
                block_depth += 1
                idx += 2
                continue
            if nxt == "-/":
                block_depth -= 1
                idx += 2
                continue
            if text[idx] == "\n":
                out.append("\n")
            idx += 1
            continue
        if nxt == "/-":
            block_depth = 1
            idx += 2
            continue
        if nxt == "--":
            while idx < len(text) and text[idx] != "\n":
                idx += 1
            continue
        out.append(text[idx])
        idx += 1
    return "".join(out)


def _lean_decl_pattern(name: str) -> re.Pattern[str]:
    kinds = "|".join(LEAN_DECLARATION_KINDS)
    return re.compile(rf"\b(?:{kinds})\s+{re.escape(name)}\b")


def _check_lean_theorem_bindings(
    *,
    stripped_source: str,
    theorems: object,
    component_id: str,
    receipt_idx: int,
    module_idx: int,
    rel: str,
) -> None:
    theorem_items = _as_sequence(
        theorems,
        ctx=f"{component_id}.proof_receipts[{receipt_idx}].modules[{module_idx}].theorems",
    )
    _expect(
        bool(theorem_items),
        f"{component_id}.proof_receipts[{receipt_idx}].modules[{module_idx}].theorems must be non-empty",
    )
    seen: set[str] = set()
    for theorem_idx, theorem in enumerate(theorem_items):
        name = _require_nonempty_str(
            theorem,
            ctx=f"{component_id}.proof_receipts[{receipt_idx}].modules[{module_idx}].theorems[{theorem_idx}]",
        )
        _expect(
            name not in seen,
            f"{component_id}.proof_receipts[{receipt_idx}].modules[{module_idx}].theorems duplicate: {name}",
        )
        seen.add(name)
        _expect(
            _lean_decl_pattern(name).search(stripped_source) is not None,
            f"{component_id}: proof receipt theorem {name!r} not found as a declaration in {rel}",
        )


def _check_lean_module_trust_hygiene(
    stripped_source: str,
    *,
    component_id: str,
    rel: str,
) -> None:
    for line_no, line in enumerate(stripped_source.splitlines(), start=1):
        match = LEAN_TRUST_ESCAPE_RE.search(line)
        if match is not None:
            raise FireFormalAssuranceClaimsError(
                f"{component_id}: proof receipt module contains Lean trust escape "
                f"{match.group(1)!r} at {rel}:{line_no}"
            )


def _check_proof_receipt_module_hashes(
    receipt_payload: Mapping[str, object],
    *,
    repo_root: Path,
    component_id: str,
    receipt_idx: int,
    declared_checker: str,
) -> None:
    modules = _as_sequence(
        receipt_payload.get("modules"),
        ctx=f"{component_id}.proof_receipts[{receipt_idx}].modules",
    )
    _expect(bool(modules), f"{component_id}.proof_receipts[{receipt_idx}]: proof receipt must bind at least one module")
    for module_idx, module_obj in enumerate(modules):
        module = _as_mapping(
            module_obj,
            ctx=f"{component_id}.proof_receipts[{receipt_idx}].modules[{module_idx}]",
        )
        module_name = _require_nonempty_str(
            module.get("module"),
            ctx=f"{component_id}.proof_receipts[{receipt_idx}].modules[{module_idx}].module",
        )
        if declared_checker == "lean":
            _expect(
                module_name.startswith("Proofs."),
                f"{component_id}.proof_receipts[{receipt_idx}].modules[{module_idx}].module must be under Proofs.*",
            )
        rel = module.get("path")
        _expect(
            isinstance(rel, str) and bool(rel),
            f"{component_id}.proof_receipts[{receipt_idx}].modules[{module_idx}].path must be non-empty",
        )
        expected_sha = module.get("sha256")
        _expect(
            _is_sha256(expected_sha),
            f"{component_id}.proof_receipts[{receipt_idx}].modules[{module_idx}].sha256 must be sha256-prefixed",
        )
        module_path = repo_root / rel
        _expect(module_path.is_file(), f"{component_id}: proof receipt module file missing: {rel}")
        actual_sha = _sha256_file(module_path)
        _expect(
            actual_sha == expected_sha,
            f"{component_id}: proof receipt module hash mismatch for {rel}: {actual_sha} != {expected_sha}",
        )
        if declared_checker == "lean":
            stripped = _strip_lean_comments(module_path.read_text(encoding="utf-8"))
            _check_lean_module_trust_hygiene(stripped, component_id=component_id, rel=rel)
            _check_lean_theorem_bindings(
                stripped_source=stripped,
                theorems=module.get("theorems"),
                component_id=component_id,
                receipt_idx=receipt_idx,
                module_idx=module_idx,
                rel=rel,
            )


def _check_proof_receipt_commands(
    receipt_payload: Mapping[str, object],
    *,
    component_id: str,
    receipt_idx: int,
) -> None:
    commands = _as_sequence(
        receipt_payload.get("commands"),
        ctx=f"{component_id}.proof_receipts[{receipt_idx}].commands",
    )
    _expect(bool(commands), f"{component_id}.proof_receipts[{receipt_idx}].commands must be non-empty")
    for cmd_idx, command_obj in enumerate(commands):
        command = _as_mapping(
            command_obj,
            ctx=f"{component_id}.proof_receipts[{receipt_idx}].commands[{cmd_idx}]",
        )
        _require_nonempty_str(
            command.get("cwd"),
            ctx=f"{component_id}.proof_receipts[{receipt_idx}].commands[{cmd_idx}].cwd",
        )
        _require_nonempty_str(
            command.get("cmd"),
            ctx=f"{component_id}.proof_receipts[{receipt_idx}].commands[{cmd_idx}].cmd",
        )


def _check_proof_receipt_integrity(
    receipt_payload: Mapping[str, object],
    *,
    repo_root: Path,
    component_id: str,
    receipt_idx: int,
    declared_checker: str,
    declared_result: str,
) -> None:
    if declared_checker == "lean":
        schema = receipt_payload.get("schema")
        _expect(
            schema == LEAN_PROOF_RECEIPT_SCHEMA,
            f"{component_id}: Lean proof receipt schema mismatch at index {receipt_idx}: {schema!r}",
        )
        receipt_toolchain = _require_nonempty_str(
            receipt_payload.get("lean_toolchain"),
            ctx=f"{component_id}.proof_receipts[{receipt_idx}].lean_toolchain",
        )
        expected_toolchain = _lean_toolchain(repo_root)
        _expect(
            receipt_toolchain == expected_toolchain,
            f"{component_id}: Lean proof receipt toolchain mismatch at index {receipt_idx}: "
            f"{receipt_toolchain!r} != {expected_toolchain!r}",
        )
    receipt_checker = receipt_payload.get("checker")
    _expect(
        receipt_checker == declared_checker,
        f"{component_id}: proof receipt checker mismatch at index {receipt_idx}: {receipt_checker!r} != {declared_checker!r}",
    )
    receipt_result = receipt_payload.get("result")
    _expect(
        receipt_result == declared_result,
        f"{component_id}: proof receipt result mismatch at index {receipt_idx}: {receipt_result!r} != {declared_result!r}",
    )
    _check_proof_receipt_commands(receipt_payload, component_id=component_id, receipt_idx=receipt_idx)
    _check_proof_receipt_module_hashes(
        receipt_payload,
        repo_root=repo_root,
        component_id=component_id,
        receipt_idx=receipt_idx,
        declared_checker=declared_checker,
    )


def _check_formal_verification(
    component: Mapping[str, object],
    *,
    repo_root: Path,
) -> bool:
    component_id = str(component["id"])
    formal = _as_mapping(component.get("formal_verification"), ctx=f"{component_id}.formal_verification")
    claimed = _as_bool(formal.get("claimed"), ctx=f"{component_id}.formal_verification.claimed")
    status = formal.get("status")
    proof_receipts = _as_sequence(formal.get("proof_receipts"), ctx=f"{component_id}.proof_receipts")

    if claimed:
        _expect(status == "formally_verified", f"{component_id}: claimed formal verification must use formally_verified status")
        _expect(bool(proof_receipts), f"{component_id}: formal verification claim requires at least one proof receipt")
    else:
        _expect(status != "formally_verified", f"{component_id}: formally_verified status requires claimed=true")

    for idx, receipt_obj in enumerate(proof_receipts):
        receipt = _as_mapping(receipt_obj, ctx=f"{component_id}.proof_receipts[{idx}]")
        rel = receipt.get("path")
        _expect(isinstance(rel, str) and bool(rel), f"{component_id}.proof_receipts[{idx}].path must be non-empty")
        path = repo_root / rel
        _expect(path.is_file(), f"{component_id}: proof receipt file missing: {rel}")
        expected_sha = receipt.get("sha256")
        if expected_sha is not None:
            _expect(isinstance(expected_sha, str), f"{component_id}.proof_receipts[{idx}].sha256 must be a string")
            actual_sha = _sha256_file(path)
            _expect(actual_sha == expected_sha, f"{component_id}: proof receipt hash mismatch for {rel}: {actual_sha} != {expected_sha}")
        checker = receipt.get("checker")
        _expect(checker in {"lean", "esso", "smt", "other"}, f"{component_id}: unsupported proof checker {checker!r}")
        result = receipt.get("result")
        _expect(result in {"proved", "verified"}, f"{component_id}: unsupported proof receipt result {result!r}")
        receipt_payload = _load_json(path)
        _check_proof_receipt_integrity(
            receipt_payload,
            repo_root=repo_root,
            component_id=component_id,
            receipt_idx=idx,
            declared_checker=str(checker),
            declared_result=str(result),
        )

    return claimed


def _check_component(
    component: Mapping[str, object],
    *,
    repo_root: Path,
) -> tuple[bool, bool, bool]:
    component_id = str(component["id"])
    surface = component.get("surface")
    _expect(isinstance(surface, str) and bool(surface), f"{component_id}: missing surface")
    can_authorize = _as_bool(component.get("can_authorize_settlement"), ctx=f"{component_id}.can_authorize_settlement")
    claims_bug_free = _as_bool(component.get("claims_bug_free"), ctx=f"{component_id}.claims_bug_free")
    _expect(not claims_bug_free, f"{component_id}: bug-free claims are forbidden")
    _component_paths_exist(component, repo_root=repo_root)

    if surface in NON_AUTHORITATIVE_SURFACES:
        _expect(not can_authorize, f"{component_id}: non-authoritative surface cannot authorize settlement")

    if component_id == "fire_acceptance_receipt_v1":
        _expect(not can_authorize, "fire_acceptance_receipt_v1: package acceptance cannot authorize settlement")
        _expect(component.get("authorizes_settlement") is False, "fire_acceptance_receipt_v1: authorizes_settlement must be false")

    if can_authorize:
        _expect(component.get("requires_firev_receipt_ok") is True, f"{component_id}: settlement authority requires FIREVReceiptOK")
        _expect(
            _string_tuple(component.get("required_receipt_bindings"), ctx=f"{component_id}.required_receipt_bindings")
            == REQUIRED_RECEIPT_BINDINGS,
            f"{component_id}: required receipt bindings must be exactly {REQUIRED_RECEIPT_BINDINGS}",
        )
        _expect(component.get("fails_closed_on_missing_receipt") is True, f"{component_id}: missing receipt must fail closed")

    formally_verified = _check_formal_verification(component, repo_root=repo_root)
    return formally_verified, can_authorize, surface in NON_AUTHORITATIVE_SURFACES


def _weakest_assurance_level(components: Sequence[Mapping[str, object]]) -> str:
    ranks = {level: idx for idx, level in enumerate(REQUIRED_EVIDENCE_LEVELS)}
    weakest = max(ranks[str(component["assurance_level"])] for component in components)
    return REQUIRED_EVIDENCE_LEVELS[weakest]


def verify_fire_formal_assurance_claims_file(
    manifest_path: Path | None = None,
    *,
    schema_path: Path | None = None,
    repo_root: Path | None = None,
) -> tuple[bool, str | None, FireFormalAssuranceClaimsVerification | None]:
    resolved_manifest_path = (manifest_path or fire_formal_assurance_claims_path()).resolve()
    resolved_schema_path = (schema_path or fire_formal_assurance_claims_schema_path()).resolve()
    resolved_repo_root = (repo_root.resolve() if repo_root is not None else resolved_manifest_path.parents[3])
    try:
        payload = _load_yaml(resolved_manifest_path)
        _validate_schema(payload, schema_path=resolved_schema_path)

        theorem = _as_mapping(payload.get("theorem"), ctx="theorem")
        _expect(theorem.get("statement") == SETTLEMENT_ADMISSIBILITY_STATEMENT, "theorem.statement mismatch")

        lattice = _as_mapping(payload.get("evidence_lattice"), ctx="evidence_lattice")
        _expect(
            _string_tuple(lattice.get("levels"), ctx="evidence_lattice.levels") == REQUIRED_EVIDENCE_LEVELS,
            "evidence_lattice.levels mismatch",
        )
        _expect(payload.get("public_runtime_requires_private_esso") is False, "public runtime must not require private ESSO")

        authority = _as_mapping(payload.get("settlement_authority"), ctx="settlement_authority")
        _expect(authority.get("predicate") == "FIREVReceiptOK", "settlement authority predicate mismatch")
        _expect(
            _string_tuple(authority.get("required_bindings"), ctx="settlement_authority.required_bindings")
            == REQUIRED_RECEIPT_BINDINGS,
            "settlement authority receipt binding mismatch",
        )
        _expect(authority.get("missing_or_mismatch_behavior") == "reject", "settlement authority must reject on missing/mismatch")
        authoritative_surfaces = _string_set(
            authority.get("only_authoritative_surfaces"),
            ctx="settlement_authority.only_authoritative_surfaces",
        )
        _expect(authoritative_surfaces == {"FIRE-V", "FIRE-VCore"}, "settlement authority surfaces mismatch")

        forbidden = _string_set(payload.get("forbidden_public_claims"), ctx="forbidden_public_claims")
        missing_forbidden = sorted(REQUIRED_FORBIDDEN_CLAIMS - forbidden)
        _expect(not missing_forbidden, f"missing forbidden public claims: {missing_forbidden}")

        gate = _as_mapping(payload.get("claim_gate"), ctx="claim_gate")
        _expect(gate.get("fail_closed") is True, "claim gate must fail closed")
        _expect(gate.get("formal_claim_requires_checked_receipt") is True, "formal claims must require checked receipts")
        _expect(gate.get("bug_free_claim_allowed") is False, "bug-free claim gate must stay false")
        _expect(
            gate.get("acceptance_receipt_authorizes_settlement_allowed") is False,
            "acceptance receipt settlement authority gate must stay false",
        )

        raw_components = _as_sequence(payload.get("components"), ctx="components")
        components = [_as_mapping(component, ctx=f"components[{idx}]") for idx, component in enumerate(raw_components)]
        ids = [str(component.get("id")) for component in components]
        _expect(len(set(ids)) == len(ids), "component ids must be unique")

        formally_verified: list[str] = []
        authority_components: list[str] = []
        non_authoritative_components: list[str] = []
        for component in components:
            component_id = str(component["id"])
            is_formally_verified, can_authorize, is_non_authoritative = _check_component(
                component,
                repo_root=resolved_repo_root,
            )
            if is_formally_verified:
                formally_verified.append(component_id)
            if can_authorize:
                authority_components.append(component_id)
            if is_non_authoritative:
                non_authoritative_components.append(component_id)

        verification = FireFormalAssuranceClaimsVerification(
            manifest_path=resolved_manifest_path,
            schema_path=resolved_schema_path,
            manifest_sha256=_sha256_file(resolved_manifest_path),
            component_count=len(components),
            formally_verified_components=tuple(sorted(formally_verified)),
            settlement_authority_components=tuple(sorted(authority_components)),
            non_authoritative_components=tuple(sorted(non_authoritative_components)),
            weakest_assurance_level=_weakest_assurance_level(components),
        )
        return True, None, verification
    except FireFormalAssuranceClaimsError as exc:
        return False, str(exc), None


__all__ = [
    "FIRE_FORMAL_ASSURANCE_CLAIMS_CHECK_REPORT_SCHEMA",
    "FIRE_FORMAL_ASSURANCE_CLAIMS_SCHEMA",
    "FireFormalAssuranceClaimsVerification",
    "verify_fire_formal_assurance_claims_file",
]
