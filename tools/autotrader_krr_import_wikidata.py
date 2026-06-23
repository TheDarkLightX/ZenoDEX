#!/usr/bin/env python3
"""Import bounded Wikidata artifacts into the offline KRR pipeline."""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Mapping
from urllib.parse import urlparse
from urllib.request import Request, urlopen

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.agents.krr_bundle_artifacts import (  # noqa: E402
    KRRCanonicalClaim,
    KRREvidenceRecord,
    KRRSourceSnapshot,
)
from src.state.canonical import sha256_hex  # noqa: E402

_DEFAULT_ENTITY_BASE_URL = "https://www.wikidata.org/wiki/Special:EntityData"
_DEFAULT_DUMP_BASE_URL = "https://dumps.wikimedia.org/wikidatawiki/entities"
_DEFAULT_DUMP_FILE = "latest-all.json.bz2"
_DEFAULT_ENTITY_MAX_BYTES = 5 * 1024 * 1024
_DEFAULT_LARGE_DOWNLOAD_THRESHOLD = 10 * 1024 * 1024 * 1024
_FINANCIAL_TRADING_REFERENCE_PROFILE: dict[str, dict[str, str]] = {
    "P31": {"fact_family": "wikidata_entity", "attribute_key": "instance_of"},
    "P17": {"fact_family": "issuer_reference", "attribute_key": "country"},
    "P159": {"fact_family": "issuer_reference", "attribute_key": "headquarters_location"},
    "P249": {"fact_family": "listing_reference", "attribute_key": "ticker_symbol"},
    "P414": {"fact_family": "listing_reference", "attribute_key": "stock_exchange"},
    "P452": {"fact_family": "issuer_reference", "attribute_key": "industry"},
    "P749": {"fact_family": "ownership_reference", "attribute_key": "parent_organization"},
    "P856": {"fact_family": "issuer_reference", "attribute_key": "official_website"},
    "P946": {"fact_family": "instrument_identifier", "attribute_key": "isin"},
    "P1278": {"fact_family": "entity_identifier", "attribute_key": "lei"},
    "P1320": {"fact_family": "entity_identifier", "attribute_key": "opencorporates_id"},
    "P355": {"fact_family": "ownership_reference", "attribute_key": "subsidiary"},
}
_PROFILE_MAP: dict[str, dict[str, dict[str, str]]] = {
    "generic": {},
    "financial-trading-reference": _FINANCIAL_TRADING_REFERENCE_PROFILE,
}


def _iso_now() -> str:
    return datetime.now(timezone.utc).replace(microsecond=0).isoformat().replace("+00:00", "Z")


def _require_supported_remote_url(url: str, *, allow_insecure_http: bool) -> None:
    parsed = urlparse(url)
    if parsed.scheme == "https":
        return
    if parsed.scheme == "http" and allow_insecure_http:
        return
    raise ValueError("remote Wikidata URLs must use https unless --allow-insecure-http is set")


def _safe_file_token(value: str) -> str:
    out: list[str] = []
    for ch in value:
        if ch.isalnum() or ch in "._-":
            out.append(ch)
        else:
            out.append("_")
    return "".join(out).strip("._") or "x"


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument(
        "--mode",
        choices=("entity", "dump-manifest", "dump-download"),
        required=True,
    )
    ap.add_argument("--entity-id", action="append", default=[])
    ap.add_argument("--entity-id-file", help="Optional newline-delimited entity id file")
    ap.add_argument("--languages", default="en", help="Comma-separated metadata languages to extract")
    ap.add_argument(
        "--profile",
        choices=tuple(sorted(_PROFILE_MAP.keys())),
        default="generic",
        help="Optional bounded statement profile to extract in addition to metadata claims",
    )
    ap.add_argument(
        "--emit-metadata-claims",
        action=argparse.BooleanOptionalAction,
        default=True,
        help="Emit simple metadata claim candidates such as labels and descriptions",
    )
    ap.add_argument("--entity-base-url", default=_DEFAULT_ENTITY_BASE_URL)
    ap.add_argument("--dump-base-url", default=_DEFAULT_DUMP_BASE_URL)
    ap.add_argument("--dump-file-name", default=_DEFAULT_DUMP_FILE)
    ap.add_argument("--dump-out", help="Output path for dump-download mode")
    ap.add_argument("--snapshot-out", help="Optional snapshot artifact output path for dump-download mode")
    ap.add_argument("--out-dir", help="Output directory for entity mode")
    ap.add_argument("--manifest-out", help="Optional JSON manifest/report output path")
    ap.add_argument("--user-agent", default="zenodex-krr-wikidata-import/1.0")
    ap.add_argument("--timeout-s", type=float, default=30.0)
    ap.add_argument("--chunk-bytes", type=int, default=1 << 20)
    ap.add_argument(
        "--entity-max-bytes",
        type=int,
        default=_DEFAULT_ENTITY_MAX_BYTES,
        help="Hard maximum bytes for a single Wikidata entity HTTP response.",
    )
    ap.add_argument("--max-bytes", type=int, help="Optional hard maximum for remote dump size")
    ap.add_argument(
        "--large-download-threshold-bytes",
        type=int,
        default=_DEFAULT_LARGE_DOWNLOAD_THRESHOLD,
        help="Downloads above this size require --allow-large-download",
    )
    ap.add_argument("--allow-large-download", action="store_true")
    ap.add_argument("--allow-insecure-http", action="store_true")
    ap.add_argument("--pretty", action="store_true")
    return ap.parse_args(argv)


def _entity_ids_from_args(args: argparse.Namespace) -> list[str]:
    raw_ids = list(str(raw).strip() for raw in args.entity_id if str(raw).strip())
    if args.entity_id_file:
        path = Path(args.entity_id_file).expanduser().resolve()
        raw_ids.extend(line.strip() for line in path.read_text(encoding="utf-8").splitlines() if line.strip())
    entity_ids: list[str] = []
    seen: set[str] = set()
    for raw in raw_ids:
        normalized = raw.upper()
        if not normalized or normalized in seen:
            continue
        if normalized[0] not in {"Q", "P"} or not normalized[1:].isdigit() or normalized[1] == "0":
            raise ValueError(f"unsupported Wikidata entity id: {raw}")
        seen.add(normalized)
        entity_ids.append(normalized)
    if not entity_ids:
        raise ValueError("entity mode requires at least one --entity-id or --entity-id-file")
    return entity_ids


def _language_list(raw: str) -> tuple[str, ...]:
    out: list[str] = []
    seen: set[str] = set()
    for token in str(raw).split(","):
        lang = token.strip().lower()
        if not lang or lang in seen:
            continue
        seen.add(lang)
        out.append(lang)
    return tuple(out or ("en",))


def _content_length(headers: Mapping[str, str]) -> int | None:
    raw = headers.get("content-length")
    if raw is None:
        return None
    text = str(raw).strip()
    return int(text) if text.isdigit() else None


def _read_limited(response: Any, *, max_bytes: int, label: str) -> bytes:
    if not isinstance(max_bytes, int) or isinstance(max_bytes, bool) or max_bytes <= 0:
        raise ValueError("max_bytes must be positive")
    chunks: list[bytes] = []
    total = 0
    while True:
        chunk = response.read(min(65536, int(max_bytes) + 1 - total))
        if not chunk:
            break
        if not isinstance(chunk, (bytes, bytearray)):
            chunk = str(chunk).encode("utf-8", errors="replace")
        chunks.append(bytes(chunk))
        total += len(chunk)
        if total > int(max_bytes):
            raise ValueError(f"{label} exceeds max_bytes")
    return b"".join(chunks)


def _http_request(
    *,
    url: str,
    user_agent: str,
    timeout_s: float,
    allow_insecure_http: bool,
    method: str = "GET",
    max_response_bytes: int = _DEFAULT_ENTITY_MAX_BYTES,
) -> tuple[bytes, dict[str, str], int, bool]:
    _require_supported_remote_url(url, allow_insecure_http=allow_insecure_http)
    request = Request(url, headers={"User-Agent": user_agent}, method=method)
    with urlopen(request, timeout=timeout_s) as response:  # noqa: S310 - explicit network import tool
        headers = {str(key).lower(): str(value) for key, value in response.headers.items()}
        length = _content_length(headers)
        if length is not None and length > int(max_response_bytes):
            raise ValueError(f"remote response exceeds max_response_bytes: {length} > {int(max_response_bytes)}")
        body = _read_limited(response, max_bytes=int(max_response_bytes), label="remote response")
        status = int(getattr(response, "status", 200))
    return body, headers, status, urlparse(url).scheme == "https"


def _http_head(
    *,
    url: str,
    user_agent: str,
    timeout_s: float,
    allow_insecure_http: bool,
) -> tuple[dict[str, str], int, bool]:
    _require_supported_remote_url(url, allow_insecure_http=allow_insecure_http)
    request = Request(url, headers={"User-Agent": user_agent}, method="HEAD")
    with urlopen(request, timeout=timeout_s) as response:  # noqa: S310 - explicit network import tool
        headers = {str(key).lower(): str(value) for key, value in response.headers.items()}
        status = int(getattr(response, "status", 200))
    return headers, status, urlparse(url).scheme == "https"


def _write_json(path: str | Path | None, payload: Mapping[str, Any], *, pretty: bool) -> str | None:
    if path is None:
        return None
    out = Path(path).expanduser().resolve()
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(
        json.dumps(dict(payload), indent=2 if pretty else None, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    return str(out)


def _size_metrics(content_length_bytes: int | None) -> dict[str, Any]:
    if content_length_bytes is None or content_length_bytes < 0:
        return {
            "content_length_bytes": None,
            "content_length_gb": None,
            "content_length_gib": None,
        }
    return {
        "content_length_bytes": int(content_length_bytes),
        "content_length_gb": round(float(content_length_bytes) / (1000.0**3), 3),
        "content_length_gib": round(float(content_length_bytes) / (1024.0**3), 3),
    }


def _canonical_entity_text(entity_obj: Mapping[str, Any]) -> str:
    return json.dumps(dict(entity_obj), sort_keys=True, separators=(",", ":"), ensure_ascii=False)


def _build_entity_claims(
    *,
    entity_id: str,
    source_id: str,
    evidence_id: str,
    entity_obj: Mapping[str, Any],
    languages: tuple[str, ...],
) -> tuple[KRRCanonicalClaim, ...]:
    claims: list[KRRCanonicalClaim] = []
    entity_type = str(entity_obj.get("type", "")).strip()
    if entity_type:
        claims.append(
            KRRCanonicalClaim(
                claim_id=f"{entity_id}.entity_type",
                entity_id=entity_id,
                fact_family="wikidata_entity",
                attribute_key="entity_type",
                value=entity_type,
                evidence_ids=(evidence_id,),
                source_ids=(source_id,),
                valid_from=str(entity_obj.get("modified") or "") or None,
            )
        )
    labels = entity_obj.get("labels", {})
    descriptions = entity_obj.get("descriptions", {})
    if not isinstance(labels, Mapping):
        labels = {}
    if not isinstance(descriptions, Mapping):
        descriptions = {}
    for lang in languages:
        label_row = labels.get(lang)
        if isinstance(label_row, Mapping):
            label_value = str(label_row.get("value", "")).strip()
            if label_value:
                claims.append(
                    KRRCanonicalClaim(
                        claim_id=f"{entity_id}.label.{lang}",
                        entity_id=entity_id,
                        fact_family="wikidata_label",
                        attribute_key=f"label.{lang}",
                        value=label_value,
                        evidence_ids=(evidence_id,),
                        source_ids=(source_id,),
                        valid_from=str(entity_obj.get("modified") or "") or None,
                    )
                )
        desc_row = descriptions.get(lang)
        if isinstance(desc_row, Mapping):
            description_value = str(desc_row.get("value", "")).strip()
            if description_value:
                claims.append(
                    KRRCanonicalClaim(
                        claim_id=f"{entity_id}.description.{lang}",
                        entity_id=entity_id,
                        fact_family="wikidata_description",
                        attribute_key=f"description.{lang}",
                        value=description_value,
                        evidence_ids=(evidence_id,),
                        source_ids=(source_id,),
                        valid_from=str(entity_obj.get("modified") or "") or None,
                    )
                )
    return tuple(claims)


def _statement_value_to_claim_parts(
    datavalue: object,
) -> tuple[object, str | None, str | None] | None:
    if not isinstance(datavalue, Mapping):
        return None
    value = datavalue.get("value")
    if isinstance(value, Mapping):
        if "id" in value:
            entity_id = str(value.get("id", "")).strip()
            if entity_id:
                return entity_id, None, None
        if "value" in value and "language" in value:
            text = str(value.get("value", "")).strip()
            if text:
                return text, None, None
        if "time" in value:
            time_text = str(value.get("time", "")).strip()
            if time_text:
                return time_text, None, None
        if "amount" in value:
            amount_text = str(value.get("amount", "")).strip()
            unit = str(value.get("unit", "")).strip() or None
            if amount_text:
                unit_token = None
                if unit:
                    tail = unit.rsplit("/", 1)[-1].strip()
                    if tail.startswith("Q") and tail[1:].isdigit():
                        unit_token = tail
                return amount_text, unit_token, None
    if isinstance(value, (str, int, float)):
        return value, None, None
    return None


def _statement_rank_priority(statement: Mapping[str, Any]) -> int | None:
    rank = str(statement.get("rank", "")).strip()
    if rank == "preferred":
        return 0
    if rank == "normal":
        return 1
    return None


def _select_profile_statements(claim_rows: object) -> tuple[Mapping[str, Any], ...]:
    if not isinstance(claim_rows, list):
        return ()
    ranked: list[tuple[int, Mapping[str, Any]]] = []
    for row in claim_rows:
        if not isinstance(row, Mapping):
            continue
        priority = _statement_rank_priority(row)
        if priority is None:
            continue
        ranked.append((priority, row))
    if not ranked:
        return ()
    best = min(priority for priority, _ in ranked)
    return tuple(row for priority, row in ranked if priority == best)


def _build_profile_statement_artifacts(
    *,
    entity_id: str,
    source_id: str,
    snapshot_id: str,
    entity_obj: Mapping[str, Any],
    profile_name: str,
) -> tuple[tuple[KRREvidenceRecord, ...], tuple[KRRCanonicalClaim, ...]]:
    profile = _PROFILE_MAP.get(profile_name, {})
    if not profile:
        return (), ()
    claims_obj = entity_obj.get("claims")
    if not isinstance(claims_obj, Mapping):
        return (), ()
    evidence_rows: list[KRREvidenceRecord] = []
    claims: list[KRRCanonicalClaim] = []
    for property_id, spec in profile.items():
        selected_rows = _select_profile_statements(claims_obj.get(property_id))
        for index, statement in enumerate(selected_rows, start=1):
            mainsnak = statement.get("mainsnak")
            if not isinstance(mainsnak, Mapping):
                continue
            if str(mainsnak.get("snaktype", "")).strip() != "value":
                continue
            parts = _statement_value_to_claim_parts(mainsnak.get("datavalue"))
            if parts is None:
                continue
            value, unit, currency = parts
            statement_id = str(statement.get("id", "")).strip()
            evidence_id = f"{entity_id}.{property_id}.{index}.statement"
            excerpt_text = json.dumps(dict(mainsnak), sort_keys=True, separators=(",", ":"), ensure_ascii=False)
            evidence_rows.append(
                KRREvidenceRecord(
                    evidence_id=evidence_id,
                    snapshot_id=snapshot_id,
                    locator={
                        "kind": "wikidata_statement",
                        "entity_id": entity_id,
                        "property_id": property_id,
                        "statement_id": statement_id or None,
                        "rank": str(statement.get("rank", "")).strip() or None,
                    },
                    extracted_at=_iso_now(),
                    excerpt_sha256=sha256_hex(excerpt_text.encode("utf-8")),
                    excerpt_text=excerpt_text,
                    valid_from=str(entity_obj.get("modified") or "") or None,
                    claim_family=spec["fact_family"],
                )
            )
            claims.append(
                KRRCanonicalClaim(
                    claim_id=f"{entity_id}.{property_id}.{index}",
                    entity_id=entity_id,
                    fact_family=spec["fact_family"],
                    attribute_key=spec["attribute_key"],
                    value=value,
                    evidence_ids=(evidence_id,),
                    source_ids=(source_id,),
                    valid_from=str(entity_obj.get("modified") or "") or None,
                    unit=unit,
                    currency=currency,
                )
            )
    return tuple(evidence_rows), tuple(claims)


def _handle_entity_mode(args: argparse.Namespace) -> dict[str, Any]:
    if not args.out_dir:
        raise ValueError("entity mode requires --out-dir")
    entity_ids = _entity_ids_from_args(args)
    languages = _language_list(args.languages)
    profile_name = str(args.profile)
    out_dir = Path(args.out_dir).expanduser().resolve()
    snapshots_dir = out_dir / "source_snapshots"
    evidence_dir = out_dir / "evidence_records"
    claims_dir = out_dir / "canonical_claims"
    raw_dir = out_dir / "raw"
    for path in (snapshots_dir, evidence_dir, claims_dir, raw_dir):
        path.mkdir(parents=True, exist_ok=True)

    rows: list[dict[str, Any]] = []
    for entity_id in entity_ids:
        entity_url = f"{str(args.entity_base_url).rstrip('/')}/{entity_id}.json"
        body, headers, status, secure = _http_request(
            url=entity_url,
            user_agent=str(args.user_agent),
            timeout_s=float(args.timeout_s),
            allow_insecure_http=bool(args.allow_insecure_http),
            max_response_bytes=int(args.entity_max_bytes),
        )
        raw_text = body.decode("utf-8")
        payload = json.loads(raw_text)
        if not isinstance(payload, Mapping):
            raise ValueError(f"Wikidata entity payload must be an object: {entity_id}")
        entities = payload.get("entities")
        if not isinstance(entities, Mapping):
            raise ValueError(f"Wikidata payload missing entities map: {entity_id}")
        entity_obj = entities.get(entity_id)
        if not isinstance(entity_obj, Mapping):
            raise ValueError(f"Wikidata payload missing entity {entity_id}")
        canonical_text = _canonical_entity_text(entity_obj)
        source_id = f"wikidata.entity.{entity_id}"
        content_sha = sha256_hex(body)
        snapshot = KRRSourceSnapshot(
            snapshot_id=f"{source_id}.{content_sha[2:14]}",
            source_id=source_id,
            source_class="official_api",
            source_uri=entity_url,
            fetched_at=_iso_now(),
            observed_at=str(entity_obj.get("modified") or _iso_now()),
            media_type=headers.get("content-type", "application/json"),
            content_sha256=content_sha,
            content_bytes=len(body),
            trust_ceiling="attested",
            parser_id="wikidata_entity_json",
            parser_version="v1",
            title=str(entity_obj.get("id") or entity_id),
            transport_secure=secure,
            http_status=status,
            text_sha256=sha256_hex(raw_text.strip().encode("utf-8")),
            notes=tuple(
                note
                for note in (
                    f"entity_id={entity_id}",
                    f"revision={entity_obj.get('lastrevid')}",
                )
                if note
            ),
        )
        evidence = KRREvidenceRecord(
            evidence_id=f"{entity_id}.entity_json.full",
            snapshot_id=snapshot.snapshot_id,
            locator={
                "kind": "wikidata_entity_json",
                "entity_id": entity_id,
                "revision": int(entity_obj.get("lastrevid", 0) or 0),
            },
            extracted_at=_iso_now(),
            excerpt_sha256=sha256_hex(canonical_text.encode("utf-8")),
            excerpt_text=canonical_text,
            valid_from=str(entity_obj.get("modified") or "") or None,
            claim_family="wikidata_entity",
        )
        metadata_claims = (
            _build_entity_claims(
                entity_id=entity_id,
                source_id=source_id,
                evidence_id=evidence.evidence_id,
                entity_obj=entity_obj,
                languages=languages,
            )
            if bool(args.emit_metadata_claims)
            else ()
        )
        profile_evidence_rows, profile_claims = _build_profile_statement_artifacts(
            entity_id=entity_id,
            source_id=source_id,
            snapshot_id=snapshot.snapshot_id,
            entity_obj=entity_obj,
            profile_name=profile_name,
        )
        claims = tuple(metadata_claims) + tuple(profile_claims)

        raw_path = raw_dir / f"{_safe_file_token(entity_id)}.json"
        raw_path.write_text(raw_text, encoding="utf-8")
        snapshot_path = snapshots_dir / f"{_safe_file_token(entity_id)}.json"
        snapshot_path.write_text(json.dumps(snapshot.to_dict(), indent=2, sort_keys=True) + "\n", encoding="utf-8")
        evidence_path = evidence_dir / f"{_safe_file_token(entity_id)}.json"
        evidence_path.write_text(json.dumps(evidence.to_dict(), indent=2, sort_keys=True) + "\n", encoding="utf-8")
        extra_evidence_paths: list[str] = []
        for extra_evidence in profile_evidence_rows:
            extra_evidence_path = evidence_dir / f"{_safe_file_token(extra_evidence.evidence_id)}.json"
            extra_evidence_path.write_text(
                json.dumps(extra_evidence.to_dict(), indent=2, sort_keys=True) + "\n",
                encoding="utf-8",
            )
            extra_evidence_paths.append(str(extra_evidence_path))
        claim_paths: list[str] = []
        for claim in claims:
            claim_path = claims_dir / f"{_safe_file_token(claim.claim_id)}.json"
            claim_path.write_text(json.dumps(claim.to_dict(), indent=2, sort_keys=True) + "\n", encoding="utf-8")
            claim_paths.append(str(claim_path))
        rows.append(
            {
                "entity_id": entity_id,
                "entity_url": entity_url,
                "raw_path": str(raw_path),
                "snapshot_path": str(snapshot_path),
                "evidence_path": str(evidence_path),
                "extra_evidence_paths": extra_evidence_paths,
                "claim_paths": claim_paths,
                "claim_count": len(claim_paths),
                "revision": int(entity_obj.get("lastrevid", 0) or 0),
                "modified": entity_obj.get("modified"),
                "labels_available": sorted(entity_obj.get("labels", {}).keys()) if isinstance(entity_obj.get("labels"), Mapping) else [],
            }
        )

    return {
        "schema": "zenodex/krr-wikidata-import/v1",
        "ok": True,
        "mode": "entity",
        "profile": profile_name,
        "entity_base_url": str(args.entity_base_url),
        "languages": list(languages),
        "entity_count": len(rows),
        "entities": rows,
    }


def _dump_url(args: argparse.Namespace) -> str:
    return f"{str(args.dump_base_url).rstrip('/')}/{str(args.dump_file_name).strip()}"


def _handle_dump_manifest_mode(args: argparse.Namespace) -> dict[str, Any]:
    dump_url = _dump_url(args)
    headers, status, secure = _http_head(
        url=dump_url,
        user_agent=str(args.user_agent),
        timeout_s=float(args.timeout_s),
        allow_insecure_http=bool(args.allow_insecure_http),
    )
    content_length_raw = headers.get("content-length")
    content_length = int(content_length_raw) if content_length_raw and content_length_raw.isdigit() else None
    payload = {
        "schema": "zenodex/krr-wikidata-import/v1",
        "ok": True,
        "mode": "dump-manifest",
        "dump_url": dump_url,
        "http_status": status,
        "transport_secure": secure,
        "last_modified": headers.get("last-modified"),
        "etag": headers.get("etag"),
        "content_type": headers.get("content-type"),
    }
    payload.update(_size_metrics(content_length))
    return payload


def _handle_dump_download_mode(args: argparse.Namespace) -> dict[str, Any]:
    if not args.dump_out:
        raise ValueError("dump-download mode requires --dump-out")
    dump_url = _dump_url(args)
    headers, status, secure = _http_head(
        url=dump_url,
        user_agent=str(args.user_agent),
        timeout_s=float(args.timeout_s),
        allow_insecure_http=bool(args.allow_insecure_http),
    )
    content_length_raw = headers.get("content-length")
    content_length = int(content_length_raw) if content_length_raw and content_length_raw.isdigit() else None
    if content_length is None and args.max_bytes is None and not bool(args.allow_large_download):
        raise ValueError("remote dump missing content-length; set --max-bytes or --allow-large-download")
    if args.max_bytes is not None and content_length is not None and content_length > int(args.max_bytes):
        raise ValueError("remote dump exceeds --max-bytes")
    if (
        content_length is not None
        and content_length > int(args.large_download_threshold_bytes)
        and not bool(args.allow_large_download)
    ):
        raise ValueError("remote dump exceeds large-download threshold; rerun with --allow-large-download")

    _require_supported_remote_url(dump_url, allow_insecure_http=bool(args.allow_insecure_http))
    request = Request(dump_url, headers={"User-Agent": str(args.user_agent)})
    out_path = Path(args.dump_out).expanduser().resolve()
    out_path.parent.mkdir(parents=True, exist_ok=True)
    hasher = hashlib.sha256()
    byte_count = 0
    try:
        with urlopen(request, timeout=float(args.timeout_s)) as response:  # noqa: S310 - explicit network import tool
            with out_path.open("wb") as handle:
                while True:
                    chunk = response.read(int(args.chunk_bytes))
                    if not chunk:
                        break
                    if args.max_bytes is not None and byte_count + len(chunk) > int(args.max_bytes):
                        raise ValueError("remote dump exceeds --max-bytes")
                    handle.write(chunk)
                    hasher.update(chunk)
                    byte_count += len(chunk)
    except Exception:
        try:
            out_path.unlink()
        except FileNotFoundError:
            pass
        raise

    snapshot_payload = None
    snapshot_path = None
    if args.snapshot_out:
        snapshot = KRRSourceSnapshot(
            snapshot_id=f"wikidata.dump.{_safe_file_token(str(args.dump_file_name))}.{hasher.hexdigest()[:12]}",
            source_id=f"wikidata.dump.{_safe_file_token(str(args.dump_file_name))}",
            source_class="official_api",
            source_uri=dump_url,
            fetched_at=_iso_now(),
            observed_at=_iso_now(),
            media_type=headers.get("content-type", "application/octet-stream"),
            content_sha256="0x" + hasher.hexdigest(),
            content_bytes=byte_count,
            trust_ceiling="attested",
            parser_id="wikidata_dump",
            parser_version="v1",
            title=str(args.dump_file_name),
            transport_secure=secure,
            http_status=status,
            notes=(f"last_modified={headers.get('last-modified')}",),
        )
        snapshot_payload = snapshot.to_dict()
        snapshot_path = _write_json(args.snapshot_out, snapshot_payload, pretty=bool(args.pretty))

    payload = {
        "schema": "zenodex/krr-wikidata-import/v1",
        "ok": True,
        "mode": "dump-download",
        "dump_url": dump_url,
        "dump_out": str(out_path),
        "http_status": status,
        "transport_secure": secure,
        "last_modified": headers.get("last-modified"),
        "etag": headers.get("etag"),
        "content_type": headers.get("content-type"),
        "downloaded_sha256": "0x" + hasher.hexdigest(),
        "downloaded_bytes": byte_count,
        "snapshot_path": snapshot_path,
        "snapshot": snapshot_payload,
    }
    payload.update(_size_metrics(content_length))
    return payload


def main(argv: list[str] | None = None) -> int:
    args = _parse_args(argv)
    try:
        if args.mode == "entity":
            payload = _handle_entity_mode(args)
        elif args.mode == "dump-manifest":
            payload = _handle_dump_manifest_mode(args)
        elif args.mode == "dump-download":
            payload = _handle_dump_download_mode(args)
        else:
            raise ValueError(f"unsupported mode: {args.mode}")

        text = json.dumps(payload, indent=2 if args.pretty else None, sort_keys=True) + "\n"
        sys.stdout.write(text)
        _write_json(args.manifest_out, payload, pretty=bool(args.pretty))
        return 0
    except Exception as exc:
        payload = {
            "schema": "zenodex/krr-wikidata-import/v1",
            "ok": False,
            "error": f"{type(exc).__name__}: {exc}",
        }
        sys.stderr.write(json.dumps(payload, indent=2 if args.pretty else None, sort_keys=True) + "\n")
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
