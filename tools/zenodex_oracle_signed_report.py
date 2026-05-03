#!/usr/bin/env python3
"""Verify first-shell Zeno Oracle signed reporter submissions."""

from __future__ import annotations

import argparse
import copy
import hashlib
import json
import re
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Mapping

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from src.state.canonical import canonical_json_bytes, domain_sep_bytes

try:  # pragma: no cover - availability is asserted by tests in this checkout.
    from py_ecc.bls import G2Basic

    _BLS_AVAILABLE = True
except Exception:  # pragma: no cover
    G2Basic = None  # type: ignore[assignment]
    _BLS_AVAILABLE = False


SUBMISSION_SCHEMA = "zenodex.oracle.signed_report_submission.v1"
REPORT_SCHEMA = "zenodex.oracle.signed_report.v1"
SIGNING_PAYLOAD_SCHEMA = "zenodex.oracle.signed_report_payload.v1"
RESULT_SCHEMA = "zenodex.oracle.signed_report_verify_result.v1"
MAX_SUBMISSION_BYTES = 500_000
MAX_REPORTS = 64
MAX_AMOUNT = 10**24
MAX_SEQUENCE = 2**63 - 1
SHA256_RE = re.compile(r"^sha256:[0-9a-f]{64}$")
TOKEN_RE = re.compile(r"^[a-z][a-z0-9_.:-]{0,127}$")
HEX_RE = re.compile(r"^(0x)?[0-9a-fA-F]+$")
TOP_LEVEL_KEYS = {
    "schema",
    "submission_id",
    "chain_id",
    "reporter_id",
    "reporter_pubkey",
    "reports",
}
REPORT_KEYS = {
    "schema",
    "report_id",
    "payload_hash",
    "query_id",
    "source_id",
    "value_e8",
    "observed_epoch",
    "sequence",
    "previous_report_id",
    "signature",
}
NOT_CLAIMED = [
    "does_not_claim_report_value_true",
    "does_not_claim_reporter_honesty",
    "does_not_claim_reporter_registered_or_bonded",
    "does_not_claim_production_oracle_network_live",
]
_SAMPLE_SUBMISSION_CACHE: dict[str, Any] | None = None


@dataclass(frozen=True)
class SignedReportVerifyResult:
    status: str
    errors: list[str]
    submission_id: str | None = None
    reporter_id: str | None = None
    reporter_pubkey: str | None = None
    chain_id: str | None = None
    report_count: int | None = None
    first_sequence: int | None = None
    last_sequence: int | None = None
    last_report_id: str | None = None

    def to_json_obj(self) -> dict[str, Any]:
        return {
            "schema": RESULT_SCHEMA,
            "ok": self.status == "accepted",
            "status": self.status,
            "submission_id": self.submission_id,
            "reporter_id": self.reporter_id,
            "reporter_pubkey": self.reporter_pubkey,
            "chain_id": self.chain_id,
            "report_count": self.report_count,
            "first_sequence": self.first_sequence,
            "last_sequence": self.last_sequence,
            "last_report_id": self.last_report_id,
            "errors": list(self.errors),
            "not_claimed": NOT_CLAIMED,
        }


def sample_hash(tag: str) -> str:
    return "sha256:" + hashlib.sha256(tag.encode("utf-8")).hexdigest()


def _content_hash(obj: Mapping[str, Any], *, omit_key: str) -> str:
    body = {key: value for key, value in obj.items() if key != omit_key}
    return "sha256:" + hashlib.sha256(canonical_json_bytes(body)).hexdigest()


def submission_content_hash(obj: Mapping[str, Any]) -> str:
    return _content_hash(obj, omit_key="submission_id")


def report_content_hash(obj: Mapping[str, Any]) -> str:
    return _content_hash(obj, omit_key="report_id")


def signing_payload(
    *,
    chain_id: str,
    reporter_id: str,
    reporter_pubkey: str,
    report: Mapping[str, Any],
) -> dict[str, Any]:
    return {
        "schema": SIGNING_PAYLOAD_SCHEMA,
        "chain_id": chain_id,
        "reporter_id": reporter_id,
        "reporter_pubkey": reporter_pubkey,
        "query_id": report.get("query_id"),
        "source_id": report.get("source_id"),
        "value_e8": report.get("value_e8"),
        "observed_epoch": report.get("observed_epoch"),
        "sequence": report.get("sequence"),
        "previous_report_id": report.get("previous_report_id"),
    }


def payload_content_hash(payload: Mapping[str, Any]) -> str:
    return "sha256:" + hashlib.sha256(canonical_json_bytes(payload)).hexdigest()


def _oracle_report_message_hash(*, chain_id: str, payload_bytes: bytes) -> bytes:
    msg = domain_sep_bytes(f"oracle_report_sig:{chain_id}", version=1) + payload_bytes
    return hashlib.sha256(msg).digest()


def _strip_0x(value: str) -> str:
    return value[2:] if value.startswith("0x") else value


def _hex_bytes(value: str, *, expected_nbytes: int, name: str) -> bytes:
    if not isinstance(value, str) or not HEX_RE.match(value):
        raise ValueError(f"{name}_must_be_hex")
    raw = _strip_0x(value)
    if len(raw) != expected_nbytes * 2:
        raise ValueError(f"{name}_must_be_{expected_nbytes}_bytes")
    return bytes.fromhex(raw)


def _verify_bls_signature(
    *,
    reporter_pubkey: str,
    signature: str,
    chain_id: str,
    payload_bytes: bytes,
) -> tuple[bool, str | None, bool]:
    if not _BLS_AVAILABLE or G2Basic is None:
        return False, "signature_backend_unavailable", True
    try:
        pubkey_bytes = _hex_bytes(reporter_pubkey, expected_nbytes=48, name="reporter_pubkey")
        signature_bytes = _hex_bytes(signature, expected_nbytes=96, name="signature")
        ok = bool(G2Basic.Verify(pubkey_bytes, _oracle_report_message_hash(chain_id=chain_id, payload_bytes=payload_bytes), signature_bytes))
        return ok, None if ok else "invalid_signature", False
    except Exception as exc:
        return False, f"signature_verification_error:{exc}", False


def _sign_report_payload(*, private_key: int, chain_id: str, payload_bytes: bytes) -> str:
    if not _BLS_AVAILABLE or G2Basic is None:
        raise RuntimeError("py_ecc.bls.G2Basic unavailable")
    signature = G2Basic.Sign(
        int(private_key),
        _oracle_report_message_hash(chain_id=chain_id, payload_bytes=payload_bytes),
    )
    return "0x" + signature.hex()


def _build_report(
    *,
    private_key: int,
    chain_id: str,
    reporter_id: str,
    reporter_pubkey: str,
    query_id: str,
    source_id: str,
    value_e8: int,
    observed_epoch: int,
    sequence: int,
    previous_report_id: str | None,
) -> dict[str, Any]:
    report: dict[str, Any] = {
        "schema": REPORT_SCHEMA,
        "query_id": query_id,
        "source_id": source_id,
        "value_e8": value_e8,
        "observed_epoch": observed_epoch,
        "sequence": sequence,
        "previous_report_id": previous_report_id,
    }
    payload = signing_payload(
        chain_id=chain_id,
        reporter_id=reporter_id,
        reporter_pubkey=reporter_pubkey,
        report=report,
    )
    payload_bytes = canonical_json_bytes(payload)
    report["payload_hash"] = payload_content_hash(payload)
    report["signature"] = _sign_report_payload(
        private_key=private_key,
        chain_id=chain_id,
        payload_bytes=payload_bytes,
    )
    report["report_id"] = report_content_hash(report)
    return report


def _build_sample_submission() -> dict[str, Any]:
    if not _BLS_AVAILABLE or G2Basic is None:
        raise RuntimeError("py_ecc.bls.G2Basic unavailable")
    private_key = 42
    reporter_pubkey = "0x" + G2Basic.SkToPk(private_key).hex()
    chain_id = "zenodex.oracle.local"
    reporter_id = "reporter.sample"
    first = _build_report(
        private_key=private_key,
        chain_id=chain_id,
        reporter_id=reporter_id,
        reporter_pubkey=reporter_pubkey,
        query_id=sample_hash("zenodex.oracle.query.perps.index_price_e8"),
        source_id="source.dex.pool.local",
        value_e8=100_000_000,
        observed_epoch=100,
        sequence=0,
        previous_report_id=None,
    )
    second = _build_report(
        private_key=private_key,
        chain_id=chain_id,
        reporter_id=reporter_id,
        reporter_pubkey=reporter_pubkey,
        query_id=sample_hash("zenodex.oracle.query.perps.index_price_e8"),
        source_id="source.dex.pool.local",
        value_e8=101_000_000,
        observed_epoch=101,
        sequence=1,
        previous_report_id=str(first["report_id"]),
    )
    submission = {
        "schema": SUBMISSION_SCHEMA,
        "chain_id": chain_id,
        "reporter_id": reporter_id,
        "reporter_pubkey": reporter_pubkey,
        "reports": [first, second],
    }
    submission["submission_id"] = submission_content_hash(submission)
    return submission


def sample_submission() -> dict[str, Any]:
    global _SAMPLE_SUBMISSION_CACHE  # pylint: disable=global-statement
    if _SAMPLE_SUBMISSION_CACHE is None:
        _SAMPLE_SUBMISSION_CACHE = _build_sample_submission()
    return copy.deepcopy(_SAMPLE_SUBMISSION_CACHE)


def _is_hash(value: object) -> bool:
    return isinstance(value, str) and bool(SHA256_RE.match(value))


def _unknown_fields(
    obj: Mapping[str, Any],
    *,
    allowed: set[str],
    label: str,
    errors: list[str],
) -> None:
    for key in obj.keys():
        if not isinstance(key, str):
            errors.append(f"{label}_field_must_be_string")
        elif key not in allowed:
            errors.append(f"unknown_{label}_field:{key}")


def _hash(obj: Mapping[str, Any], key: str, errors: list[str]) -> str | None:
    value = obj.get(key)
    if not _is_hash(value):
        errors.append(f"{key}_must_be_sha256")
        return None
    return str(value)


def _token(obj: Mapping[str, Any], key: str, errors: list[str]) -> str | None:
    value = obj.get(key)
    if not isinstance(value, str) or not TOKEN_RE.match(value):
        errors.append(f"{key}_must_be_token")
        return None
    return str(value)


def _hex_field(obj: Mapping[str, Any], key: str, errors: list[str], *, nbytes: int) -> str | None:
    value = obj.get(key)
    if not isinstance(value, str):
        errors.append(f"{key}_must_be_hex")
        return None
    try:
        _hex_bytes(value, expected_nbytes=nbytes, name=key)
    except ValueError as exc:
        errors.append(str(exc))
        return None
    return str(value)


def _int_between(
    obj: Mapping[str, Any],
    key: str,
    errors: list[str],
    *,
    minimum: int,
    maximum: int,
) -> int | None:
    value = obj.get(key)
    if not isinstance(value, int) or isinstance(value, bool) or value < minimum or value > maximum:
        errors.append(f"{key}_must_be_int_between_{minimum}_and_{maximum}")
        return None
    return int(value)


def _previous_report_id(report: Mapping[str, Any], errors: list[str]) -> str | None:
    value = report.get("previous_report_id")
    if value is None:
        return None
    if not _is_hash(value):
        errors.append("previous_report_id_must_be_null_or_sha256")
        return None
    return str(value)


def _reports(obj: Mapping[str, Any], errors: list[str]) -> list[Mapping[str, Any]]:
    raw = obj.get("reports")
    if not isinstance(raw, list):
        errors.append("reports_must_be_list")
        return []
    if not raw:
        errors.append("reports_must_be_nonempty")
    if len(raw) > MAX_REPORTS:
        errors.append(f"reports_exceed_max:{len(raw)}>{MAX_REPORTS}")
    reports: list[Mapping[str, Any]] = []
    for pos, report in enumerate(raw[:MAX_REPORTS]):
        if not isinstance(report, Mapping):
            errors.append(f"report_{pos}_must_be_object")
            continue
        reports.append(report)
    return reports


def verify_signed_report_submission(obj: Mapping[str, Any]) -> SignedReportVerifyResult:
    errors: list[str] = []
    inconclusive = False
    _unknown_fields(obj, allowed=TOP_LEVEL_KEYS, label="submission", errors=errors)
    if obj.get("schema") != SUBMISSION_SCHEMA:
        errors.append("submission_schema_mismatch")

    submission_id = _hash(obj, "submission_id", errors)
    if submission_id is not None:
        try:
            expected_submission_id = submission_content_hash(obj)
        except (TypeError, ValueError):
            expected_submission_id = None
            errors.append(f"submission_content_hash_unencodable:{submission_id}")
        if expected_submission_id is not None and submission_id != expected_submission_id:
            errors.append(f"submission_content_hash_mismatch:{submission_id}")

    chain_id = _token(obj, "chain_id", errors)
    reporter_id = _token(obj, "reporter_id", errors)
    reporter_pubkey = _hex_field(obj, "reporter_pubkey", errors, nbytes=48)
    reports = _reports(obj, errors)

    report_ids: list[str] = []
    sequences: list[int] = []
    previous_report_id: str | None = None
    last_report_id: str | None = None
    for pos, report in enumerate(reports):
        _unknown_fields(report, allowed=REPORT_KEYS, label=f"report_{pos}", errors=errors)
        if report.get("schema") != REPORT_SCHEMA:
            errors.append(f"report_{pos}_schema_mismatch")
        report_id = _hash(report, "report_id", errors)
        if report_id is not None:
            try:
                expected_report_id = report_content_hash(report)
            except (TypeError, ValueError):
                expected_report_id = None
                errors.append(f"report_content_hash_unencodable:{pos}")
            if expected_report_id is not None and report_id != expected_report_id:
                errors.append(f"report_content_hash_mismatch:{pos}")
            report_ids.append(report_id)
        payload_hash = _hash(report, "payload_hash", errors)
        _hash(report, "query_id", errors)
        _token(report, "source_id", errors)
        _int_between(report, "value_e8", errors, minimum=1, maximum=MAX_AMOUNT)
        _int_between(report, "observed_epoch", errors, minimum=0, maximum=MAX_SEQUENCE)
        sequence = _int_between(report, "sequence", errors, minimum=0, maximum=MAX_SEQUENCE)
        previous = _previous_report_id(report, errors)
        signature = _hex_field(report, "signature", errors, nbytes=96)

        if sequence is not None:
            sequences.append(sequence)
            expected_sequence = pos
            if sequence != expected_sequence:
                errors.append(f"sequence_not_contiguous:{pos}")
            if sequence == 0 and previous is not None:
                errors.append("first_report_previous_report_id_must_be_null")
            if sequence > 0 and previous is None:
                errors.append(f"previous_report_id_required:{pos}")
        if pos > 0 and previous != previous_report_id:
            errors.append(f"previous_report_id_chain_mismatch:{pos}")
        if pos == 0 and previous is not None:
            errors.append("first_report_chain_mismatch")

        if chain_id is not None and reporter_id is not None and reporter_pubkey is not None:
            try:
                payload = signing_payload(
                    chain_id=chain_id,
                    reporter_id=reporter_id,
                    reporter_pubkey=reporter_pubkey,
                    report=report,
                )
                payload_bytes = canonical_json_bytes(payload)
                expected_payload_hash = payload_content_hash(payload)
            except (TypeError, ValueError):
                payload_bytes = None
                expected_payload_hash = None
                errors.append(f"payload_unencodable:{pos}")
            if expected_payload_hash is not None and payload_hash is not None and payload_hash != expected_payload_hash:
                errors.append(f"payload_hash_mismatch:{pos}")
            if payload_bytes is not None and signature is not None:
                ok, err, backend_missing = _verify_bls_signature(
                    reporter_pubkey=reporter_pubkey,
                    signature=signature,
                    chain_id=chain_id,
                    payload_bytes=payload_bytes,
                )
                if backend_missing:
                    inconclusive = True
                if not ok and err is not None:
                    errors.append(f"{err}:{pos}")

        previous_report_id = report_id
        last_report_id = report_id

    duplicate_report_ids = sorted({report_id for report_id in report_ids if report_ids.count(report_id) > 1})
    for report_id in duplicate_report_ids:
        errors.append(f"duplicate_report_id:{report_id}")
    duplicate_sequences = sorted({sequence for sequence in sequences if sequences.count(sequence) > 1})
    for sequence in duplicate_sequences:
        errors.append(f"duplicate_sequence:{sequence}")

    status = "accepted"
    if inconclusive:
        status = "inconclusive"
    elif errors:
        status = "rejected"
    return SignedReportVerifyResult(
        status=status,
        errors=errors,
        submission_id=submission_id,
        reporter_id=reporter_id,
        reporter_pubkey=reporter_pubkey,
        chain_id=chain_id,
        report_count=len(reports),
        first_sequence=min(sequences) if sequences else None,
        last_sequence=max(sequences) if sequences else None,
        last_report_id=last_report_id,
    )


def _load_json(path: Path) -> Mapping[str, Any]:
    size = path.stat().st_size
    if size > MAX_SUBMISSION_BYTES:
        raise ValueError(f"signed_report_file_too_large:{size}>{MAX_SUBMISSION_BYTES}")
    with path.open("r", encoding="utf-8") as handle:
        obj = json.load(handle)
    if not isinstance(obj, Mapping):
        raise ValueError("signed report root must be a JSON object")
    return obj


def _write_result(result: SignedReportVerifyResult, output: Path | None) -> None:
    text = json.dumps(result.to_json_obj(), indent=2, sort_keys=True) + "\n"
    if output is None:
        sys.stdout.write(text)
    else:
        output.write_text(text, encoding="utf-8")


def cmd_verify(args: argparse.Namespace) -> int:
    try:
        submission = _load_json(Path(args.submission))
    except Exception as exc:  # pragma: no cover - exercised through CLI tests
        result = SignedReportVerifyResult(status="inconclusive", errors=[f"signed_report_load_failed:{exc}"])
        _write_result(result, Path(args.output) if args.output else None)
        return 3

    result = verify_signed_report_submission(submission)
    _write_result(result, Path(args.output) if args.output else None)
    if result.status == "accepted":
        return 0
    if result.status == "inconclusive":
        return 3
    return 2


def cmd_sample(args: argparse.Namespace) -> int:
    text = json.dumps(sample_submission(), indent=2, sort_keys=True) + "\n"
    if args.output:
        Path(args.output).write_text(text, encoding="utf-8")
    else:
        sys.stdout.write(text)
    return 0


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="command", required=True)

    verify = subparsers.add_parser("verify", help="verify an Oracle signed report submission")
    verify.add_argument("submission", help="path to a signed report submission JSON file")
    verify.add_argument("--output", help="optional output path for the verifier result JSON")
    verify.set_defaults(func=cmd_verify)

    sample = subparsers.add_parser("sample", help="emit a minimal accepted signed report submission")
    sample.add_argument("--output", help="optional output path for the sample submission JSON")
    sample.set_defaults(func=cmd_sample)
    return parser


def main(argv: list[str] | None = None) -> int:
    parser = build_parser()
    args = parser.parse_args(argv)
    return int(args.func(args))


if __name__ == "__main__":
    raise SystemExit(main())
