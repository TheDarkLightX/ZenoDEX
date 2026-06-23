from __future__ import annotations

from pathlib import Path


def fire_root_dir() -> Path:
    return Path(__file__).resolve().parent


def fire_spec_dir() -> Path:
    return fire_root_dir() / "spec"


def fire_ir_schema_path() -> Path:
    return fire_spec_dir() / "fire-ir.schema.json"


def fire_instance_schema_path() -> Path:
    return fire_spec_dir() / "fire-instance.schema.json"


def fire_cert_schema_path() -> Path:
    return fire_spec_dir() / "fire-cert.schema.json"


def fire_cert_rules_schema_path() -> Path:
    return fire_spec_dir() / "fire-cert-rules.schema.json"


def fire_compile_receipt_schema_path() -> Path:
    return fire_spec_dir() / "fire-compile-receipt.schema.json"


def fire_kernel_receipt_schema_path() -> Path:
    return fire_spec_dir() / "fire-kernel-receipt.schema.json"


def fire_kernel_eval_receipt_schema_path() -> Path:
    return fire_spec_dir() / "fire-kernel-eval-receipt.schema.json"


def fire_kernel_settlement_receipt_schema_path() -> Path:
    return fire_spec_dir() / "fire-kernel-settlement-receipt.schema.json"


def fire_kernel_replay_receipt_schema_path() -> Path:
    return fire_spec_dir() / "fire-kernel-replay-receipt.schema.json"


def fire_verifier_rules_path() -> Path:
    return fire_spec_dir() / "verifier-rules.yaml"


def fire_formal_assurance_claims_path() -> Path:
    return fire_spec_dir() / "formal-assurance-claims.yaml"


def fire_formal_assurance_claims_schema_path() -> Path:
    return fire_spec_dir() / "fire-formal-assurance-claims.schema.json"


def fire_lock_schema_path() -> Path:
    return fire_spec_dir() / "fire-lock.schema.json"


def fire_replay_input_schema_path() -> Path:
    return fire_spec_dir() / "fire-replay-input.schema.json"


def fire_object_package_schema_path() -> Path:
    return fire_spec_dir() / "object-package.schema.json"


def fire_acceptance_receipt_schema_path() -> Path:
    return fire_spec_dir() / "fire-acceptance-receipt.schema.json"


def fire_stdlib_dir() -> Path:
    return fire_root_dir() / "stdlib"


def fire_stdlib_objects_dir() -> Path:
    return fire_stdlib_dir() / "objects"


def fire_zpl_dir() -> Path:
    return fire_root_dir() / "zpl"


def legacy_fire_kernel_dir() -> Path:
    return fire_root_dir().parents[1] / "src" / "kernels" / "dex"


def legacy_fire_spec_dir() -> Path:
    return fire_root_dir().parents[1] / "src" / "kernels" / "fire_specs"


def legacy_fire_zpl_dir() -> Path:
    return fire_root_dir().parents[1] / "src" / "kernels" / "zpl"


def preferred_fire_spec_dirs() -> tuple[Path, ...]:
    return (fire_stdlib_objects_dir(), legacy_fire_spec_dir())


def preferred_fire_zpl_dirs() -> tuple[Path, ...]:
    return (fire_zpl_dir(), legacy_fire_zpl_dir())


def resolve_fire_spec_path(name: str | Path) -> Path:
    candidate = Path(name)
    if candidate.is_absolute():
        return candidate
    if candidate.parent != Path("."):
        return candidate

    filename = candidate.name
    if not filename.endswith(".json"):
        filename = f"{filename}.json"
    for base in preferred_fire_spec_dirs():
        resolved = base / filename
        if resolved.exists():
            return resolved
    return preferred_fire_spec_dirs()[0] / filename


def resolve_fire_zpl_path(name: str | Path) -> Path:
    candidate = Path(name)
    if candidate.is_absolute():
        return candidate
    if candidate.parent != Path("."):
        return candidate

    filename = candidate.name
    if not filename.endswith(".zpl"):
        filename = f"{filename}.zpl"
    for base in preferred_fire_zpl_dirs():
        resolved = base / filename
        if resolved.exists():
            return resolved
    return preferred_fire_zpl_dirs()[0] / filename


def default_fire_esso_kernel_model_paths() -> tuple[Path, ...]:
    kernel_dir = legacy_fire_kernel_dir()
    return (
        kernel_dir / "fire_burn_boost_call_v1.yaml",
        kernel_dir / "fire_fee_note_v1.yaml",
        kernel_dir / "fire_lp_loss_cover_v1.yaml",
    )


__all__ = [
    "fire_root_dir",
    "fire_spec_dir",
    "fire_ir_schema_path",
    "fire_instance_schema_path",
    "fire_cert_schema_path",
    "fire_cert_rules_schema_path",
    "fire_compile_receipt_schema_path",
    "fire_kernel_receipt_schema_path",
    "fire_kernel_eval_receipt_schema_path",
    "fire_kernel_settlement_receipt_schema_path",
    "fire_kernel_replay_receipt_schema_path",
    "fire_verifier_rules_path",
    "fire_formal_assurance_claims_path",
    "fire_formal_assurance_claims_schema_path",
    "fire_lock_schema_path",
    "fire_replay_input_schema_path",
    "fire_object_package_schema_path",
    "fire_acceptance_receipt_schema_path",
    "fire_stdlib_dir",
    "fire_stdlib_objects_dir",
    "fire_zpl_dir",
    "legacy_fire_kernel_dir",
    "legacy_fire_spec_dir",
    "legacy_fire_zpl_dir",
    "default_fire_esso_kernel_model_paths",
    "preferred_fire_spec_dirs",
    "preferred_fire_zpl_dirs",
    "resolve_fire_spec_path",
    "resolve_fire_zpl_path",
]
