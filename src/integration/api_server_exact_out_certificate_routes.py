from __future__ import annotations

from typing import Any, Callable


WriteJson = Callable[[int, object], None]
ParseExactOutQuote = Callable[[object], Any]

_BUILD_EXACT_OUT_CERTIFICATE_ENDPOINT = "/api/dex/build_exact_out_route_certificate"
_VERIFY_EXACT_OUT_CERTIFICATE_ENDPOINT = "/api/dex/verify_exact_out_route_certificate"


def _handle_build_exact_out_route_certificate(
    obj: dict[str, object],
    parse_exact_out_quote: ParseExactOutQuote,
    write_json: WriteJson,
) -> None:
    quotes_obj = obj.get("quotes")
    if not isinstance(quotes_obj, list) or not quotes_obj:
        write_json(400, {"ok": False, "error": "bad_quotes"})
        return
    try:
        from src.integration.exact_out_route_certificate import (  # pylint: disable=import-outside-toplevel
            build_exact_out_route_canonical_certificate,
        )

        quotes = tuple(parse_exact_out_quote(quote_obj) for quote_obj in quotes_obj)
        certificate = build_exact_out_route_canonical_certificate(quotes)
        write_json(200, {"ok": True, "certificate": certificate.to_dict()})
    except Exception:
        write_json(
            400,
            {"ok": False, "error": "bad_exact_out_certificate_request", "details": "request failed"},
        )


def _handle_verify_exact_out_route_certificate(
    obj: dict[str, object],
    write_json: WriteJson,
) -> None:
    certificate = obj.get("certificate")
    if not isinstance(certificate, dict):
        write_json(400, {"ok": False, "error": "bad_certificate"})
        return
    try:
        from src.integration.exact_out_route_certificate import (  # pylint: disable=import-outside-toplevel
            verify_exact_out_route_canonical_certificate_payload,
        )

        ok, err = verify_exact_out_route_canonical_certificate_payload(certificate)
        write_json(200, {"ok": bool(ok), "error": ("ok" if ok else str(err))})
    except Exception:
        write_json(
            400,
            {"ok": False, "error": "verify_exact_out_certificate_error", "details": "request failed"},
        )


def maybe_handle_exact_out_certificate_route(
    *,
    path: str,
    obj: dict[str, object],
    parse_exact_out_quote: ParseExactOutQuote,
    write_json: WriteJson,
) -> bool:
    if path == _BUILD_EXACT_OUT_CERTIFICATE_ENDPOINT:
        _handle_build_exact_out_route_certificate(obj, parse_exact_out_quote, write_json)
        return True
    if path == _VERIFY_EXACT_OUT_CERTIFICATE_ENDPOINT:
        _handle_verify_exact_out_route_certificate(obj, write_json)
        return True
    return False
