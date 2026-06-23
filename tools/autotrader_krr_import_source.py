#!/usr/bin/env python3
"""Fetch or ingest a public source into a deterministic KRR snapshot artifact."""

from __future__ import annotations

import argparse
import json
import mimetypes
import sys
from datetime import datetime, timezone
from pathlib import Path
from typing import Any
from urllib.parse import urlparse
from urllib.request import Request, urlopen

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.agents.krr_bundle_artifacts import (  # noqa: E402
    KRREvidenceRecord,
    KRRSourceSnapshot,
)
from src.state.canonical import sha256_hex  # noqa: E402

_DEFAULT_MAX_SOURCE_BYTES = 25 * 1024 * 1024


def _iso_now() -> str:
    return datetime.now(timezone.utc).replace(microsecond=0).isoformat().replace("+00:00", "Z")


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--source-id", required=True)
    ap.add_argument(
        "--source-class",
        required=True,
        choices=("official_api", "official_doc", "protocol_doc", "research_paper", "research_dataset", "news", "other"),
    )
    ap.add_argument("--source-uri", required=True, help="https:// URL, file:// URI, or local file path")
    ap.add_argument("--title")
    ap.add_argument("--license")
    ap.add_argument("--media-type", help="Optional override")
    ap.add_argument(
        "--trust-ceiling",
        default="advisory",
        choices=("advisory", "attested", "verified", "protocol"),
    )
    ap.add_argument("--parser-id", default="raw_snapshot")
    ap.add_argument("--parser-version", default="v1")
    ap.add_argument("--observed-at", help="Optional event/observation timestamp (defaults to fetched_at)")
    ap.add_argument("--text-encoding", default="utf-8")
    ap.add_argument("--user-agent", default="zenodex-krr-import/1.0")
    ap.add_argument("--allow-insecure-http", action="store_true")
    ap.add_argument(
        "--max-bytes",
        type=int,
        default=_DEFAULT_MAX_SOURCE_BYTES,
        help="Hard maximum source body size in bytes.",
    )
    ap.add_argument("--snapshot-out", required=True)
    ap.add_argument("--body-out", help="Optional raw body output path")
    ap.add_argument("--text-out", help="Optional decoded text output path")
    ap.add_argument("--evidence-out", help="Optional full-document evidence record output path")
    ap.add_argument("--pretty", action="store_true")
    return ap.parse_args(argv)


def _content_length(headers: Any) -> int | None:
    raw = headers.get("Content-Length") if hasattr(headers, "get") else None
    if raw is None:
        return None
    text = str(raw).strip()
    return int(text) if text.isdigit() else None


def _read_limited(stream: Any, *, max_bytes: int, label: str) -> bytes:
    if not isinstance(max_bytes, int) or isinstance(max_bytes, bool) or max_bytes <= 0:
        raise ValueError("max_bytes must be positive")
    chunks: list[bytes] = []
    total = 0
    while True:
        chunk = stream.read(min(65536, int(max_bytes) + 1 - total))
        if not chunk:
            break
        if not isinstance(chunk, (bytes, bytearray)):
            chunk = str(chunk).encode("utf-8", errors="replace")
        chunks.append(bytes(chunk))
        total += len(chunk)
        if total > int(max_bytes):
            raise ValueError(f"{label} exceeds max_bytes")
    return b"".join(chunks)


def _load_source_bytes(
    *,
    source_uri: str,
    user_agent: str,
    allow_insecure_http: bool,
    max_bytes: int,
) -> tuple[bytes, str | None, int | None, bool]:
    parsed = urlparse(source_uri)
    if parsed.scheme in {"https", "http"}:
        if parsed.scheme == "http" and not allow_insecure_http:
            raise ValueError("plain http is not allowed without --allow-insecure-http")
        request = Request(source_uri, headers={"User-Agent": user_agent})
        with urlopen(request, timeout=30.0) as response:  # noqa: S310 - explicit trusted import tool
            length = _content_length(response.headers)
            if length is not None and length > int(max_bytes):
                raise ValueError("remote source exceeds max_bytes")
            body = _read_limited(response, max_bytes=int(max_bytes), label="remote source")
            media_type = response.headers.get_content_type()
            status = getattr(response, "status", None)
        return body, media_type, status, parsed.scheme == "https"
    if parsed.scheme == "file":
        path = Path(parsed.path).expanduser().resolve()
    elif parsed.scheme == "":
        path = Path(source_uri).expanduser().resolve()
    else:
        raise ValueError("source-uri must use https, file, or a local path")
    if path.stat().st_size > int(max_bytes):
        raise ValueError("local source exceeds max_bytes")
    body = path.read_bytes()
    media_type, _ = mimetypes.guess_type(str(path))
    return body, media_type, None, True


def _write_text(path: str | None, text: str) -> None:
    if path is None:
        return
    out = Path(path).expanduser().resolve()
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(text, encoding="utf-8")


def _write_bytes(path: str | None, data: bytes) -> None:
    if path is None:
        return
    out = Path(path).expanduser().resolve()
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_bytes(data)


def main(argv: list[str] | None = None) -> int:
    args = _parse_args(argv)
    try:
        body, detected_media_type, http_status, transport_secure = _load_source_bytes(
            source_uri=str(args.source_uri),
            user_agent=str(args.user_agent),
            allow_insecure_http=bool(args.allow_insecure_http),
            max_bytes=int(args.max_bytes),
        )
        fetched_at = _iso_now()
        observed_at = str(args.observed_at or fetched_at)
        media_type = str(args.media_type or detected_media_type or "application/octet-stream")
        content_sha256 = sha256_hex(body)
        snapshot_id = f"{args.source_id}.{content_sha256[2:14]}"
        text_value: str | None = None
        text_sha256: str | None = None
        try:
            text_value = body.decode(str(args.text_encoding), errors="strict")
            text_sha256 = sha256_hex(text_value.strip().encode("utf-8"))
        except UnicodeDecodeError:
            text_value = None
            text_sha256 = None

        snapshot = KRRSourceSnapshot(
            snapshot_id=snapshot_id,
            source_id=str(args.source_id),
            source_class=str(args.source_class),
            source_uri=str(args.source_uri),
            fetched_at=fetched_at,
            observed_at=observed_at,
            media_type=media_type,
            content_sha256=content_sha256,
            content_bytes=len(body),
            trust_ceiling=str(args.trust_ceiling),
            parser_id=str(args.parser_id),
            parser_version=str(args.parser_version),
            license=args.license,
            title=args.title,
            transport_secure=transport_secure,
            http_status=http_status,
            text_sha256=text_sha256,
        )
        evidence = None
        if args.evidence_out:
            if text_value is None or text_sha256 is None:
                raise ValueError("cannot emit evidence without decodable text content")
            evidence = KRREvidenceRecord(
                evidence_id=f"{snapshot.snapshot_id}.full",
                snapshot_id=snapshot.snapshot_id,
                locator={"kind": "full_document", "bytes": len(body)},
                extracted_at=fetched_at,
                excerpt_sha256=text_sha256,
                excerpt_text=text_value,
            )

        snapshot_payload = {
            "schema": "zenodex/krr-source-import/v1",
            "ok": True,
            "snapshot": snapshot.to_dict(),
            "body_sha256": content_sha256,
            "body_bytes": len(body),
            "text_decoded": text_value is not None,
            "evidence": None if evidence is None else evidence.to_dict(),
        }
        text = json.dumps(snapshot_payload, indent=2 if args.pretty else None, sort_keys=True) + "\n"
        sys.stdout.write(text)

        snapshot_out = Path(args.snapshot_out).expanduser().resolve()
        snapshot_out.parent.mkdir(parents=True, exist_ok=True)
        snapshot_out.write_text(
            json.dumps(snapshot.to_dict(), indent=2 if args.pretty else None, sort_keys=True) + "\n",
            encoding="utf-8",
        )
        _write_bytes(args.body_out, body)
        if text_value is not None:
            _write_text(args.text_out, text_value)
        if args.evidence_out and evidence is not None:
            evidence_out = Path(args.evidence_out).expanduser().resolve()
            evidence_out.parent.mkdir(parents=True, exist_ok=True)
            evidence_out.write_text(
                json.dumps(evidence.to_dict(), indent=2 if args.pretty else None, sort_keys=True) + "\n",
                encoding="utf-8",
            )
        return 0
    except Exception as exc:
        payload = {
            "schema": "zenodex/krr-source-import/v1",
            "ok": False,
            "error": f"{type(exc).__name__}: {exc}",
        }
        sys.stderr.write(json.dumps(payload, indent=2 if args.pretty else None, sort_keys=True) + "\n")
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
