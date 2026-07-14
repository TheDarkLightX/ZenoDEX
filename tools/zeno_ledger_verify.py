#!/usr/bin/env python3
"""Verify a ZenoLedger v0 header/body sequence."""

from __future__ import annotations

import argparse
import json
import os
import stat
import sys
from pathlib import Path
from typing import Any, Mapping, NoReturn

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.core.dex import DexState  # noqa: E402
from src.integration.dex_engine import DexEngineConfig  # noqa: E402
from src.integration.zeno_ledger_authenticated_proof_verification_v1 import (  # noqa: E402
    MAX_PROOF_ARTIFACT_BYTES,
    PinnedZenoLedgerRisc0VerifierV1,
    VerifierExecutableFormatV1,
)
from src.integration.zeno_ledger_profile import (  # noqa: E402
    validate_checkpoint_structural_compatibility_v0,
    validate_zeno_ledger_profile_v0,
    zeno_ledger_profile_requires_proof_authority_v0,
)
from src.integration.zeno_ledger_proof_authority_consumer_v1 import (  # noqa: E402
    GovernedProofAuthorityBindingV1,
    ProofAuthorityDecisionV1,
    make_proof_authority_requirement_v1,
    proof_authority_not_required_v1,
    resolve_proof_authority_v1,
)
from src.integration.zeno_ledger_replay import (  # noqa: E402
    load_replay_snapshot_v0,
    parse_replay_engine_config_v0,
    parse_replay_engine_config_v1,
    replay_engine_config_digest_v0,
    replay_engine_config_digest_v1,
    validate_replay_bound_block_v0,
)
from src.integration.zeno_ledger_strict_spot_authority_v1 import (  # noqa: E402
    MAX_STRICT_REQUEST_BYTES,
    PinnedStrictSpotAuthorityVerifierV1,
    parse_strict_spot_request_payload_bytes_v1,
)
from src.integration.zeno_ledger_v0 import (  # noqa: E402
    canonical_header_hash_v0,
    validate_checkpoint_header_binding_v0,
    validate_header_body_roots_v0,
    validate_header_v0,
    validate_proof_metadata_header_binding_v0,
    validate_proof_metadata_v0,
)
from src.state.canonical import canonical_json_bytes  # noqa: E402

ZERO_ROOT = "0x" + "00" * 32
REPORT_SCHEMA = "zenodex.zeno_ledger.verify_report.v0"
RISC0_PROOF_METADATA_REPORT_SCHEMA = "zenodex.zeno_ledger.risc0_proof_metadata_report.v0"
TEE_PROOF_METADATA_REPORT_SCHEMA = "zenodex.zeno_ledger.tee_proof_metadata_report.v0"
REPLAY_BOUND_MODE = "replay_bound"
STRUCTURAL_DIAGNOSTIC_MODE = "structural_diagnostic"
VERIFY_MODES = frozenset({REPLAY_BOUND_MODE, STRUCTURAL_DIAGNOSTIC_MODE})


def _load_json_object(path: Path) -> Mapping[str, Any]:
    obj = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(obj, Mapping):
        raise ValueError(f"{path} must decode to a JSON object")
    return obj


def _require_bool(value: object, *, name: str) -> bool:
    if not isinstance(value, bool):
        raise TypeError(f"{name} must be a bool")
    return value


def _require_str(value: object, *, name: str) -> str:
    if not isinstance(value, str) or value == "":
        raise ValueError(f"{name} must be a non-empty str")
    return value


def _read_bounded_regular_file(
    path: Path,
    *,
    max_bytes: int = MAX_PROOF_ARTIFACT_BYTES,
) -> bytes:
    if not isinstance(max_bytes, int) or isinstance(max_bytes, bool) or max_bytes <= 0:
        raise ValueError("bounded file byte limit must be a positive int")
    nofollow = getattr(os, "O_NOFOLLOW", None)
    if nofollow is None:
        raise ValueError("platform lacks O_NOFOLLOW for proof artifact input")
    flags = os.O_RDONLY | nofollow | getattr(os, "O_CLOEXEC", 0) | getattr(os, "O_NONBLOCK", 0)
    fd = os.open(path, flags)
    try:
        before = os.fstat(fd)
        if not stat.S_ISREG(before.st_mode):
            raise ValueError("bounded input must be a regular file")
        if before.st_size <= 0 or before.st_size > max_bytes:
            raise ValueError("bounded input byte length is invalid")
        chunks: list[bytes] = []
        total = 0
        while total <= max_bytes:
            chunk = os.read(fd, min(64 * 1024, max_bytes + 1 - total))
            if not chunk:
                break
            chunks.append(chunk)
            total += len(chunk)
        raw = b"".join(chunks)
        after = os.fstat(fd)
    finally:
        os.close(fd)
    stable_identity = (
        before.st_dev,
        before.st_ino,
        before.st_mode,
        before.st_size,
        before.st_mtime_ns,
        before.st_ctime_ns,
    ) == (
        after.st_dev,
        after.st_ino,
        after.st_mode,
        after.st_size,
        after.st_mtime_ns,
        after.st_ctime_ns,
    )
    if not stable_identity or len(raw) != before.st_size:
        raise ValueError("bounded input changed during read")
    return raw


def _load_strict_authority_json_object(path: Path) -> Mapping[str, Any]:
    raw = _read_bounded_regular_file(path, max_bytes=MAX_STRICT_REQUEST_BYTES)
    value = json.loads(
        raw.decode("utf-8"),
        object_pairs_hook=_reject_duplicate_json_keys,
        parse_float=_reject_json_float,
        parse_constant=_reject_json_constant,
    )
    if not isinstance(value, dict):
        raise ValueError(f"{path} must decode to a JSON object")
    if canonical_json_bytes(value) != raw:
        raise ValueError(f"{path} must use canonical JSON bytes")
    return value


def _load_range_json_object(
    path: Path,
    *,
    strict_authority: bool,
) -> Mapping[str, Any]:
    if strict_authority:
        return _load_strict_authority_json_object(path)
    return _load_json_object(path)


def _reject_duplicate_json_keys(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f"duplicate JSON key: {key}")
        result[key] = value
    return result


def _reject_json_float(_value: str) -> NoReturn:
    raise ValueError("floating-point JSON numbers are forbidden")


def _reject_json_constant(_value: str) -> NoReturn:
    raise ValueError("non-finite JSON numbers are forbidden")


def verify_zeno_ledger_v0(
    *,
    headers_dir: Path,
    bodies_dir: Path,
    checkpoints_dir: Path | None,
    profile_path: Path | None,
    from_height: int,
    to_height: int,
    trusted_prev_header_hash: str = ZERO_ROOT,
    proof_metadata_dir: Path | None = None,
    proof_verification_report_dir: Path | None = None,
    require_proof_verification_report: bool = False,
    proof_artifacts_dir: Path | None = None,
    proof_authority_verifier: object | None = None,
    strict_spot_request_payloads_dir: Path | None = None,
    strict_spot_authority_verifier: object | None = None,
    verifier_registry: Mapping[str, Any] | None = None,
    mode: str,
    pre_snapshots_dir: Path | None = None,
    engine_config_path: Path | None = None,
    require_rejection_receipt_replay: bool = False,
) -> dict[str, Any]:
    errors: list[str] = []
    checked_heights: list[int] = []
    proof_metadata_checked_heights: list[int] = []
    proof_verification_checked_heights: list[int] = []
    governed_proof_authority_checked_heights: list[int] = []
    last_header_hash: str | None = None
    last_post_state_root: str | None = None
    last_app_hash: str | None = None
    expected_prev_hash = trusted_prev_header_hash
    previous_header: dict[str, Any] | None = None
    replay_state: DexState | None = None
    replay_config: DexEngineConfig | None = None
    replay_config_document: dict[str, Any] | None = None
    replay_config_digest: str | None = None
    governed_proof_authority_binding: GovernedProofAuthorityBindingV1 | None = None
    proof_authority_required = False
    proof_authority_decision = proof_authority_not_required_v1()

    legacy_authority_requested = any(
        value is not None for value in (proof_artifacts_dir, proof_authority_verifier)
    )
    strict_authority_requested = any(
        value is not None
        for value in (strict_spot_request_payloads_dir, strict_spot_authority_verifier)
    )
    if legacy_authority_requested and strict_authority_requested:
        errors.append("proof_authority_paths_are_mutually_exclusive")
    if legacy_authority_requested and not all(
        value is not None
        for value in (proof_artifacts_dir, proof_authority_verifier, verifier_registry)
    ):
        errors.append("proof_observation_inputs_incomplete")
    if strict_authority_requested and not all(
        value is not None
        for value in (
            strict_spot_request_payloads_dir,
            strict_spot_authority_verifier,
            verifier_registry,
        )
    ):
        errors.append("strict_spot_authority_inputs_incomplete")
    if (
        verifier_registry is not None
        and not legacy_authority_requested
        and not strict_authority_requested
    ):
        errors.append("proof_observation_inputs_incomplete")
    authority_inputs_present = legacy_authority_requested or strict_authority_requested

    if mode not in VERIFY_MODES:
        errors.append("verify_mode_invalid")
    replay_bound = mode == REPLAY_BOUND_MODE
    if replay_bound:
        if pre_snapshots_dir is None:
            errors.append("replay_bound_requires_pre_snapshots_dir")
        elif not pre_snapshots_dir.is_dir():
            errors.append("pre_snapshots_dir_missing")
        if engine_config_path is None:
            errors.append("replay_bound_requires_engine_config")
        elif not engine_config_path.is_file():
            errors.append("engine_config_missing")
        if require_rejection_receipt_replay is not True:
            errors.append("replay_bound_requires_rejection_receipt_replay")
        if not errors and engine_config_path is not None:
            try:
                config_input = _load_range_json_object(
                    engine_config_path,
                    strict_authority=strict_authority_requested,
                )
                if strict_authority_requested:
                    (
                        replay_config,
                        governed_proof_authority_binding,
                        replay_config_document,
                    ) = parse_replay_engine_config_v1(config_input)
                    replay_config_digest = replay_engine_config_digest_v1(
                        replay_config_document
                    )
                else:
                    replay_config, replay_config_document = parse_replay_engine_config_v0(
                        config_input
                    )
                    replay_config_digest = replay_engine_config_digest_v0(
                        replay_config_document
                    )
            except Exception as exc:
                errors.append(f"engine_config_invalid:{exc}")
    elif (
        any(value is not None for value in (pre_snapshots_dir, engine_config_path))
        or require_rejection_receipt_replay
    ):
        errors.append("structural_diagnostic_rejects_replay_inputs")

    if from_height < 0:
        errors.append("from_height_must_be_nonnegative")
    if to_height < from_height:
        errors.append("to_height_before_from_height")
    if not headers_dir.is_dir():
        errors.append("headers_dir_missing")
    if not bodies_dir.is_dir():
        errors.append("bodies_dir_missing")
    if proof_metadata_dir is not None and not proof_metadata_dir.is_dir():
        errors.append("proof_metadata_dir_missing")
    if proof_verification_report_dir is not None and not proof_verification_report_dir.is_dir():
        errors.append("proof_verification_report_dir_missing")
    if require_proof_verification_report and proof_verification_report_dir is None:
        errors.append("require_proof_verification_report_requires_dir")
    if proof_verification_report_dir is not None and proof_metadata_dir is None:
        errors.append("proof_verification_report_requires_proof_metadata_dir")
    if proof_artifacts_dir is not None and not proof_artifacts_dir.is_dir():
        errors.append("proof_artifacts_dir_missing")
    if (
        strict_spot_request_payloads_dir is not None
        and not strict_spot_request_payloads_dir.is_dir()
    ):
        errors.append("strict_spot_request_payloads_dir_missing")
    typed_proof_authority_verifier: PinnedZenoLedgerRisc0VerifierV1 | None = None
    if proof_authority_verifier is not None:
        if type(proof_authority_verifier) is not PinnedZenoLedgerRisc0VerifierV1:
            errors.append("proof_authority_verifier_type_invalid")
        else:
            typed_proof_authority_verifier = proof_authority_verifier
    typed_strict_spot_authority_verifier: PinnedStrictSpotAuthorityVerifierV1 | None = None
    if strict_spot_authority_verifier is not None:
        if type(strict_spot_authority_verifier) is not PinnedStrictSpotAuthorityVerifierV1:
            errors.append("strict_spot_authority_verifier_type_invalid")
        else:
            typed_strict_spot_authority_verifier = strict_spot_authority_verifier
    if strict_authority_requested and from_height != to_height:
        errors.append("strict_spot_authority_v1_requires_singleton_range")
    profile: dict[str, Any] | None = None
    if profile_path is not None:
        if checkpoints_dir is None:
            errors.append("profile_requires_checkpoints_dir")
        elif not profile_path.is_file():
            errors.append("profile_missing")
        else:
            try:
                profile = dict(
                    _load_range_json_object(
                        profile_path,
                        strict_authority=strict_authority_requested,
                    )
                )
                validate_zeno_ledger_profile_v0(profile)
                proof_authority_required = zeno_ledger_profile_requires_proof_authority_v0(profile)
                proof_authority_decision = resolve_proof_authority_v1(
                    requirement=make_proof_authority_requirement_v1(
                        profile=profile,
                        replay_config_digest=replay_config_digest,
                        expected_policy_id=(
                            governed_proof_authority_binding.policy_id
                            if governed_proof_authority_binding is not None
                            else None
                        ),
                        from_height=from_height,
                        to_height=to_height,
                    ),
                    governed_binding=governed_proof_authority_binding,
                    authenticated_result=None,
                )
                if proof_authority_required and proof_metadata_dir is None:
                    errors.append("profile_requires_proof_metadata_dir")
                if (
                    proof_authority_required
                    and replay_bound
                    and not authority_inputs_present
                ):
                    errors.append("profile_requires_governed_proof_authority_binding")
            except Exception as exc:
                errors.append(f"profile_invalid:{exc}")
    if authority_inputs_present and (not replay_bound or not proof_authority_required):
        errors.append("proof_observation_inputs_require_replay_bound_profile")
    if errors:
        return _report(
            errors=errors,
            checked_heights=checked_heights,
            proof_metadata_checked_heights=proof_metadata_checked_heights,
            proof_verification_checked_heights=proof_verification_checked_heights,
            governed_proof_authority_checked_heights=(governed_proof_authority_checked_heights),
            last_header_hash=last_header_hash,
            last_post_state_root=last_post_state_root,
            last_app_hash=last_app_hash,
            mode=mode,
            replay_config_digest=replay_config_digest,
            proof_authority_decision=proof_authority_decision,
        )

    for height in range(from_height, to_height + 1):
        header_path = headers_dir / f"{height}.json"
        body_path = bodies_dir / f"{height}.json"
        if not header_path.is_file():
            errors.append(f"header_missing:{height}")
            break
        if not body_path.is_file():
            errors.append(f"body_missing:{height}")
            break

        try:
            header = dict(
                _load_range_json_object(
                    header_path,
                    strict_authority=strict_authority_requested,
                )
            )
            body = dict(
                _load_range_json_object(
                    body_path,
                    strict_authority=strict_authority_requested,
                )
            )
            proof_metadata: dict[str, Any] | None = None
            checkpoint: dict[str, Any] | None = None
            block_pre_state: DexState | None = None
            validate_header_v0(header)
            if header["height"] != height:
                raise ValueError(f"header height mismatch for file {height}")
            if header["prev_header_hash"] != expected_prev_hash:
                raise ValueError(f"prev_header_hash mismatch at height {height}")
            if replay_bound:
                if (
                    replay_config is None
                    or replay_config_digest is None
                    or pre_snapshots_dir is None
                ):
                    raise ValueError("replay-bound inputs unavailable")
                snapshot_path = pre_snapshots_dir / f"{height}.json"
                if replay_state is None and not snapshot_path.is_file():
                    raise ValueError(f"anchor pre-state snapshot missing at height {height}")
                pre_snapshot = (
                    _load_range_json_object(
                        snapshot_path,
                        strict_authority=strict_authority_requested,
                    )
                    if snapshot_path.is_file()
                    else None
                )
                if replay_state is None:
                    if pre_snapshot is None:
                        raise ValueError("anchor pre-state snapshot unavailable")
                    block_pre_state, _canonical_snapshot = load_replay_snapshot_v0(
                        pre_snapshot
                    )
                else:
                    block_pre_state = replay_state
                replay_state = validate_replay_bound_block_v0(
                    header=header,
                    body=body,
                    pre_snapshot=pre_snapshot,
                    config=replay_config,
                    config_digest=replay_config_digest,
                    parent_header=previous_header,
                    carried_state=replay_state,
                )
            else:
                validate_header_body_roots_v0(header, body)
            if proof_metadata_dir is not None:
                proof_metadata_path = proof_metadata_dir / f"{height}.json"
                if not proof_metadata_path.is_file():
                    raise ValueError(f"proof metadata missing at height {height}")
                proof_metadata = dict(
                    _load_range_json_object(
                        proof_metadata_path,
                        strict_authority=strict_authority_requested,
                    )
                )
                validate_proof_metadata_header_binding_v0(proof_metadata, header)
                proof_metadata_checked_heights.append(height)
                if proof_verification_report_dir is not None:
                    report_path = proof_verification_report_dir / f"{height}.json"
                    if not report_path.is_file():
                        raise ValueError(f"proof verification report missing at height {height}")
                    proof_verification_report = dict(
                        _load_range_json_object(
                            report_path,
                            strict_authority=strict_authority_requested,
                        )
                    )
                    validate_proof_verification_report_v0(
                        report=proof_verification_report,
                        proof_metadata=proof_metadata,
                        header=header,
                    )
                    proof_verification_checked_heights.append(height)
            if checkpoints_dir is not None:
                checkpoint_path = checkpoints_dir / f"{height}.json"
                if not checkpoint_path.is_file():
                    raise ValueError(f"checkpoint missing at height {height}")
                checkpoint = dict(
                    _load_range_json_object(
                        checkpoint_path,
                        strict_authority=strict_authority_requested,
                    )
                )
                validate_checkpoint_header_binding_v0(checkpoint, header)
                if profile is not None:
                    validate_checkpoint_structural_compatibility_v0(
                        checkpoint=checkpoint,
                        profile=profile,
                    )
            if proof_authority_required and replay_bound:
                if strict_authority_requested:
                    if (
                        proof_metadata is None
                        or checkpoint is None
                        or profile is None
                        or replay_config_document is None
                        or governed_proof_authority_binding is None
                        or strict_spot_request_payloads_dir is None
                        or typed_strict_spot_authority_verifier is None
                        or verifier_registry is None
                        or block_pre_state is None
                        or replay_state is None
                    ):
                        raise ValueError("strict Spot proof authority inputs unavailable")
                    payload_path = strict_spot_request_payloads_dir / f"{height}.json"
                    if not payload_path.is_file():
                        raise ValueError(
                            f"strict Spot request payload missing at height {height}"
                        )
                    payload = parse_strict_spot_request_payload_bytes_v1(
                        _read_bounded_regular_file(
                            payload_path,
                            max_bytes=MAX_STRICT_REQUEST_BYTES,
                        )
                    )
                    proof_authority_decision = (
                        typed_strict_spot_authority_verifier.verify_and_resolve(
                            spot_request_payload=payload,
                            proof_metadata=proof_metadata,
                            header=header,
                            checkpoint=checkpoint,
                            replay_config=replay_config_document,
                            profile=profile,
                            verifier_registry=verifier_registry,
                            pre_state=block_pre_state,
                            post_state=replay_state,
                        )
                    )
                    if not proof_authority_decision.satisfied:
                        raise ValueError(
                            "strict Spot verifier did not satisfy proof authority"
                        )
                    governed_proof_authority_checked_heights.append(height)
                else:
                    if (
                        proof_metadata is None
                        or checkpoint is None
                        or profile is None
                        or replay_config_digest is None
                        or proof_artifacts_dir is None
                        or typed_proof_authority_verifier is None
                        or verifier_registry is None
                    ):
                        raise ValueError("governed proof authority inputs unavailable")
                    if (
                        typed_proof_authority_verifier.executable_format
                        is not VerifierExecutableFormatV1.STATIC_ELF_X86_64
                    ):
                        raise ValueError("proof_authority_verifier_must_be_static_elf")
                    # V0 commits neither the authority-manifest digest nor the
                    # registry ID. Preserve this legacy path as unavailable.
                    pending = proof_authority_decision.pending_report()
                    obligation_id = (
                        pending.get("obligation_id")
                        if pending is not None
                        else "proof_authority_pending_obligation_missing"
                    )
                    raise ValueError(
                        "governed_proof_authority_binding_unavailable_v0:"
                        f"{obligation_id}"
                    )
            last_header_hash = canonical_header_hash_v0(header)
            last_post_state_root = str(header["post_state_root"])
            last_app_hash = str(header["app_hash"])
            expected_prev_hash = last_header_hash
            previous_header = header
            checked_heights.append(height)
        except Exception as exc:
            errors.append(f"height_{height}_invalid:{exc}")
            break

    return _report(
        errors=errors,
        checked_heights=checked_heights,
        proof_metadata_checked_heights=proof_metadata_checked_heights,
        proof_verification_checked_heights=proof_verification_checked_heights,
        governed_proof_authority_checked_heights=governed_proof_authority_checked_heights,
        last_header_hash=last_header_hash,
        last_post_state_root=last_post_state_root,
        last_app_hash=last_app_hash,
        mode=mode,
        replay_config_digest=replay_config_digest,
        proof_authority_decision=proof_authority_decision,
    )


def _report(
    *,
    errors: list[str],
    checked_heights: list[int],
    proof_metadata_checked_heights: list[int],
    proof_verification_checked_heights: list[int],
    governed_proof_authority_checked_heights: list[int],
    last_header_hash: str | None,
    last_post_state_root: str | None,
    last_app_hash: str | None,
    mode: str,
    replay_config_digest: str | None,
    proof_authority_decision: ProofAuthorityDecisionV1,
) -> dict[str, Any]:
    ok = not errors
    replay_bound = mode == REPLAY_BOUND_MODE
    if errors and replay_bound:
        checked_heights = []
        proof_metadata_checked_heights = []
        proof_verification_checked_heights = []
        governed_proof_authority_checked_heights = []
        last_header_hash = None
        last_post_state_root = None
        last_app_hash = None
    range_verified = ok and replay_bound
    return {
        "schema": REPORT_SCHEMA,
        "ok": ok,
        "status": (
            "range_verified"
            if range_verified
            else "structural_diagnostic_accepted"
            if ok
            else "rejected"
        ),
        "mode": mode,
        "authority_scope": "replay_bound_range_v0" if range_verified else "none",
        "range_verified": range_verified,
        "header_linkage_checked": ok,
        "state_continuity_checked": range_verified,
        "state_replay_checked": range_verified,
        "receipt_replay_checked": range_verified,
        "config_binding_checked": range_verified,
        "replay_config_digest": replay_config_digest,
        "checked_heights": checked_heights,
        "proof_metadata_checked_heights": proof_metadata_checked_heights,
        "proof_verification_checked_heights": proof_verification_checked_heights,
        "governed_proof_authority_checked_heights": (governed_proof_authority_checked_heights),
        "proof_authority_status": proof_authority_decision.status.value,
        "proof_authority_pending_obligation": proof_authority_decision.pending_report(),
        "proof_authority_required": proof_authority_decision.required,
        "proof_authority_satisfied": proof_authority_decision.satisfied,
        "proof_authority_capable": proof_authority_decision.capable,
        "settlement_authority": False,
        "production_authority": False,
        "last_header_hash": last_header_hash,
        "last_post_state_root": last_post_state_root,
        "last_app_hash": last_app_hash,
        "errors": errors,
    }


def validate_proof_verification_report_v0(
    *,
    report: Mapping[str, Any],
    proof_metadata: Mapping[str, Any],
    header: Mapping[str, Any],
) -> None:
    validate_header_v0(dict(header))
    metadata = dict(proof_metadata)
    validate_proof_metadata_v0(metadata)
    obj = dict(_load_mapping(report, name="proof_verification_report"))
    schema = _require_str(obj.get("schema"), name="proof_verification_report.schema")
    if schema not in {RISC0_PROOF_METADATA_REPORT_SCHEMA, TEE_PROOF_METADATA_REPORT_SCHEMA}:
        raise ValueError("proof_verification_report schema is not supported")
    if _require_bool(obj.get("ok"), name="proof_verification_report.ok") is not True:
        raise ValueError("proof_verification_report must be accepted")
    if (
        _require_bool(obj.get("header_bound"), name="proof_verification_report.header_bound")
        is not True
    ):
        raise ValueError("proof_verification_report must be header-bound")
    for key in ("proof_kind", "program_id", "verifier_id", "toolchain_lock_hash"):
        if obj.get(key) != metadata.get(key):
            raise ValueError(f"proof_verification_report/metadata {key} mismatch")
    if obj["proof_journal_hash"] != header["proof_journal_hash"]:
        raise ValueError("proof_verification_report/header proof_journal_hash mismatch")
    proof_kind = metadata["proof_kind"]
    if proof_kind == "risc0_zkvm_v0":
        if schema != RISC0_PROOF_METADATA_REPORT_SCHEMA:
            raise ValueError("risc0 proof metadata requires risc0 verification report")
        if (
            _require_bool(
                obj.get("risc0_verified"), name="proof_verification_report.risc0_verified"
            )
            is not True
        ):
            raise ValueError("risc0 proof verification report must be verifier-backed")
    elif proof_kind == "tee_attestation_v0":
        if schema != TEE_PROOF_METADATA_REPORT_SCHEMA:
            raise ValueError("TEE proof metadata requires TEE verification report")
        if (
            _require_bool(obj.get("tee_verified"), name="proof_verification_report.tee_verified")
            is not True
        ):
            raise ValueError("TEE proof verification report must be verifier-backed")
        if obj.get("tee_measurement_hash") != metadata.get("tee_measurement_hash"):
            raise ValueError("proof_verification_report/metadata tee_measurement_hash mismatch")
    else:
        raise ValueError("proof verification report is only defined for Risc0 and TEE metadata")


def _load_mapping(value: object, *, name: str) -> Mapping[str, Any]:
    if not isinstance(value, Mapping):
        raise ValueError(f"{name} must be a JSON object")
    return value


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Verify a ZenoLedger v0 header/body sequence")
    parser.add_argument("--headers-dir", required=True, type=Path)
    parser.add_argument("--bodies-dir", required=True, type=Path)
    parser.add_argument("--checkpoints-dir", type=Path)
    parser.add_argument("--proof-metadata-dir", type=Path)
    parser.add_argument("--proof-verification-report-dir", type=Path)
    parser.add_argument("--require-proof-verification-report", action="store_true")
    parser.add_argument("--profile", type=Path)
    parser.add_argument("--from-height", required=True, type=int)
    parser.add_argument("--to-height", required=True, type=int)
    parser.add_argument("--trusted-prev-header-hash", default=ZERO_ROOT)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--structural-only", action="store_true")
    mode.add_argument("--require-state-replay", action="store_true")
    parser.add_argument("--pre-snapshots-dir", type=Path)
    parser.add_argument("--engine-config", type=Path)
    parser.add_argument("--require-rejection-receipt-replay", action="store_true")
    args = parser.parse_args(argv)

    result = verify_zeno_ledger_v0(
        headers_dir=args.headers_dir,
        bodies_dir=args.bodies_dir,
        checkpoints_dir=args.checkpoints_dir,
        profile_path=args.profile,
        from_height=args.from_height,
        to_height=args.to_height,
        trusted_prev_header_hash=args.trusted_prev_header_hash,
        proof_metadata_dir=args.proof_metadata_dir,
        proof_verification_report_dir=args.proof_verification_report_dir,
        require_proof_verification_report=bool(args.require_proof_verification_report),
        mode=REPLAY_BOUND_MODE if args.require_state_replay else STRUCTURAL_DIAGNOSTIC_MODE,
        pre_snapshots_dir=args.pre_snapshots_dir,
        engine_config_path=args.engine_config,
        require_rejection_receipt_replay=bool(args.require_rejection_receipt_replay),
    )
    print(json.dumps(result, indent=2, sort_keys=True))
    return 0 if result["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
