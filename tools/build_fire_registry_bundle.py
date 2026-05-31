from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any, Sequence

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from src.fire.compiler.compiler_registry_v1 import (  # noqa: E402
    compile_fire_object,
    compile_fire_zpl_object,
    get_fire_compiler_entry,
    list_fire_compiler_entries,
)
from src.fire.compiler.fmos_v1 import build_fmos_manifest, render_fmos_object_card  # noqa: E402
from src.fire.registry.instance_v1 import (  # noqa: E402
    FireSettlementWindow,
    load_fire_object_instance,
    verify_fire_object_instance_against_manifest,
)
from src.fire.registry.lock_v1 import load_fire_object_dependency_lock  # noqa: E402
from src.fire.registry.bundle_v1 import (  # noqa: E402
    FireRegistryBundleManifest,
    write_fire_registry_bundle,
)


BUILD_REPORT_SCHEMA = "zenodex/fire-registry-bundle-build-report/v1"


def _load_optional_json(path: Path | None) -> dict[str, object] | None:
    if path is None:
        return None
    payload = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(payload, dict):
        raise TypeError(f"{path.name} JSON must be an object")
    return payload


def _render_report(
    *,
    object_id: str,
    bundle_dir: Path,
    bundle_manifest: FireRegistryBundleManifest,
    bundle_file_sha256: str,
    certificate: Any,
    manifest: Any,
    instance_manifest: Any,
    object_lock: Any,
    zpl_source_file: Path | None,
) -> dict[str, object]:
    replay_receipt_path = None
    replay_input_path = None
    compile_receipt_path = None
    kernel_receipt_path = None
    kernel_eval_receipt_path = None
    kernel_settlement_receipt_path = None
    kernel_replay_receipt_path = None
    proof_tree_cert_path = None
    if bundle_manifest.replay_input_path is not None:
        replay_input_path = str((bundle_dir / bundle_manifest.replay_input_path).resolve())
    if bundle_manifest.compile_receipt_path is not None:
        compile_receipt_path = str((bundle_dir / bundle_manifest.compile_receipt_path).resolve())
    if bundle_manifest.kernel_receipt_path is not None:
        kernel_receipt_path = str((bundle_dir / bundle_manifest.kernel_receipt_path).resolve())
    if bundle_manifest.kernel_eval_receipt_path is not None:
        kernel_eval_receipt_path = str((bundle_dir / bundle_manifest.kernel_eval_receipt_path).resolve())
    if bundle_manifest.kernel_settlement_receipt_path is not None:
        kernel_settlement_receipt_path = str((bundle_dir / bundle_manifest.kernel_settlement_receipt_path).resolve())
    if bundle_manifest.kernel_replay_receipt_path is not None:
        kernel_replay_receipt_path = str((bundle_dir / bundle_manifest.kernel_replay_receipt_path).resolve())
    if bundle_manifest.proof_tree_certificate_path is not None:
        proof_tree_cert_path = str((bundle_dir / bundle_manifest.proof_tree_certificate_path).resolve())
    if bundle_manifest.replay_receipt_path is not None:
        replay_receipt_path = str((bundle_dir / bundle_manifest.replay_receipt_path).resolve())
    object_card_text = (bundle_dir / bundle_manifest.object_card_path).read_text(encoding="utf-8")
    report = {
        "schema": BUILD_REPORT_SCHEMA,
        "ok": True,
        "object_id": object_id,
        "object_name": bundle_manifest.object_name,
        "object_version": bundle_manifest.object_version,
        "object_family": bundle_manifest.object_family,
        "bundle_dir": str(bundle_dir.resolve()),
        "bundle_manifest_path": str((bundle_dir / "bundle_manifest.json").resolve()),
        "object_manifest_path": str((bundle_dir / bundle_manifest.object_manifest_path).resolve()),
        "instance_manifest_path": str((bundle_dir / bundle_manifest.object_instance_path).resolve()),
        "object_lock_path": str((bundle_dir / bundle_manifest.object_lock_path).resolve()),
        "certificate_path": str((bundle_dir / bundle_manifest.certificate_path).resolve()),
        "compile_receipt_path": compile_receipt_path,
        "kernel_receipt_path": kernel_receipt_path,
        "kernel_eval_receipt_path": kernel_eval_receipt_path,
        "kernel_settlement_receipt_path": kernel_settlement_receipt_path,
        "kernel_replay_receipt_path": kernel_replay_receipt_path,
        "proof_tree_cert_path": proof_tree_cert_path,
        "proof_tree_cert_non_authoritative": proof_tree_cert_path is not None,
        "object_card_path": str((bundle_dir / bundle_manifest.object_card_path).resolve()),
        "object_card_noncanonical": True,
        "object_card_text": object_card_text,
        "replay_input_path": replay_input_path,
        "replay_receipt_path": replay_receipt_path,
        "bundle_hash": bundle_manifest.bundle_hash,
        "bundle_file_sha256": bundle_file_sha256,
        "object_hash": manifest.manifest_hash,
        "manifest_hash": manifest.manifest_hash,
        "instance_hash": instance_manifest.instance_hash,
        "lock_hash": object_lock.lock_hash,
        "cert_sha256": manifest.cert_sha256,
        "certificate_instance_gate_claims": (
            None if certificate.instance_gate_claims is None else certificate.instance_gate_claims.to_dict()
        ),
        "artifact_lower": manifest.artifact_lower,
        "artifact_upper": manifest.artifact_upper,
        "holder_collateral_required": manifest.holder_collateral_required,
        "writer_collateral_required": manifest.writer_collateral_required,
        "instance_nonce": instance_manifest.nonce,
        "instance_maturity": instance_manifest.maturity,
        "instance_settlement_window": (
            None
            if instance_manifest.settlement_window is None
            else instance_manifest.settlement_window.to_dict()
        ),
    }
    gate_ok, gate_err, gate_report = verify_fire_object_instance_against_manifest(
        instance_manifest,
        object_manifest=manifest,
    )
    report["instance_gates"] = gate_report.to_dict()
    report["instance_gates"]["ok"] = gate_ok
    report["instance_gates"]["error"] = gate_err
    if zpl_source_file is not None:
        report["zpl_source_file"] = str(zpl_source_file.resolve())
    return report


def _add_common_args(parser: argparse.ArgumentParser) -> None:
    parser.add_argument("--bundle-dir", type=Path, required=True, help="Directory to write the FIRE registry bundle into")
    parser.add_argument("--instance-nonce", help="Optional canonical instance nonce recorded in instance_manifest.json")
    parser.add_argument("--holder-party-id", default="role:holder", help="Canonical holder party id recorded in instance_manifest.json")
    parser.add_argument("--writer-party-id", default="role:writer", help="Canonical writer party id recorded in instance_manifest.json")
    parser.add_argument("--maturity", help="Optional ISO-8601 maturity timestamp recorded in instance_manifest.json")
    parser.add_argument("--settlement-window-start", help="Optional ISO-8601 settlement-window start timestamp")
    parser.add_argument("--settlement-window-end", help="Optional ISO-8601 settlement-window end timestamp")
    parser.add_argument(
        "--zpl-source",
        type=Path,
        help="Optional ZPL source file to compile and check against the canonical FIRE FMOS spec before bundle build",
    )
    parser.add_argument(
        "--replay-input",
        type=Path,
        help="Optional JSON replay input to include as replay_input.json in the bundle",
    )
    parser.add_argument(
        "--replay-receipt",
        type=Path,
        help="Optional JSON replay receipt to include as replay_receipt.json in the bundle",
    )
    parser.add_argument(
        "--emit-proof-tree-cert",
        action="store_true",
        help="Emit a non-authoritative draft proof-tree cert sidecar as proof_tree_certificate.json",
    )
    parser.add_argument("--pretty", action="store_true", help="Pretty-print the JSON build report")


def _build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description="Build a deterministic FIRE registry bundle from typed object terms.")
    subparsers = parser.add_subparsers(dest="object_id", required=True)

    for entry in list_fire_compiler_entries():
        subparser = subparsers.add_parser(entry.object_id, help=entry.cli_help)
        _add_common_args(subparser)
        for field in entry.term_fields:
            subparser.add_argument(
                field.cli_flag,
                dest=field.name,
                type=int,
                required=True,
                help=f"{field.description} [{field.unit}; {field.minimum}..{field.maximum}]",
            )

    return parser


def main(argv: Sequence[str] | None = None) -> int:
    parser = _build_parser()
    args = parser.parse_args(argv)

    try:
        replay_receipt = _load_optional_json(args.replay_receipt)
        replay_input = _load_optional_json(args.replay_input)
        if (args.settlement_window_start is None) != (args.settlement_window_end is None):
            raise ValueError("settlement window start/end must be provided together")
        settlement_window = None
        if args.settlement_window_start is not None and args.settlement_window_end is not None:
            settlement_window = FireSettlementWindow(start=args.settlement_window_start, end=args.settlement_window_end)
        entry = get_fire_compiler_entry(args.object_id)
        raw_terms = {field.name: getattr(args, field.name) for field in entry.term_fields}
        if args.zpl_source is not None:
            compiled = compile_fire_zpl_object(args.zpl_source, raw_terms)
        else:
            compiled = compile_fire_object(args.object_id, raw_terms)
        manifest = build_fmos_manifest(compiled.spec, compiled.artifact)
        bundle_manifest, bundle_file_sha256 = write_fire_registry_bundle(
            args.bundle_dir,
            artifact=compiled.artifact,
            build_manifest=lambda artifact: build_fmos_manifest(compiled.spec, artifact),
            render_object_card=lambda artifact: render_fmos_object_card(compiled.spec, artifact),
            instance_nonce=args.instance_nonce,
            instance_parties={
                "holder": args.holder_party_id,
                "writer": args.writer_party_id,
            },
            instance_maturity=args.maturity,
            instance_settlement_window=settlement_window,
            replay_input=replay_input,
            replay_receipt=replay_receipt,
            emit_proof_tree_certificate=args.emit_proof_tree_cert,
        )
    except (OSError, RuntimeError, ValueError, TypeError, json.JSONDecodeError) as exc:
        print(str(exc), file=sys.stderr)
        return 1

    report = _render_report(
        object_id=args.object_id,
        bundle_dir=args.bundle_dir,
        bundle_manifest=bundle_manifest,
        bundle_file_sha256=bundle_file_sha256,
        certificate=compiled.artifact.certificate,
        manifest=manifest,
        instance_manifest=load_fire_object_instance(args.bundle_dir / bundle_manifest.object_instance_path)[0],
        object_lock=load_fire_object_dependency_lock(args.bundle_dir / bundle_manifest.object_lock_path)[0],
        zpl_source_file=args.zpl_source,
    )
    if args.pretty:
        print(json.dumps(report, indent=2, sort_keys=True))
    else:
        print(json.dumps(report, sort_keys=True, separators=(",", ":")))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
