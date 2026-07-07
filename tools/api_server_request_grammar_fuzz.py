"""
Deterministic grammar-based request-envelope explorer for `src.integration.api_server`.

This is a real grammar-backed HTTP-boundary fuzzer for the request parsing layer.
It focuses on boundary envelopes before endpoint-specific business logic:
- CORS origin-list parsing
- Bearer-token authorization shape
- Content-Length / raw-body handling
- JSON body decoding
- DEX request front-envelope dispatch

The explorer records unique `(outcome, path)` pairs by tracing executed lines through
`api_server.py`. It is bounded, deterministic, and intended for offline discovery
and regression pinning, not as acceptance proof for functional-core correctness.
It also performs one-step local repairs and small field sweeps so nearby guard
boundaries can be crossed deliberately.
"""
# ruff: noqa: E402,I001

from __future__ import annotations

import argparse
import copy
import hashlib
import heapq
import io
import json
import sys
import types
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any, Callable, Sequence

ROOT_DIR = Path(__file__).resolve().parents[1]
if str(ROOT_DIR) not in sys.path:
    sys.path.insert(0, str(ROOT_DIR))

from src.integration import api_server  # noqa: E402
from src.integration import api_server_dex_dispatch as _api_server_dex_dispatch  # noqa: E402,F401


RunnerFn = Callable[[object], str]
RepairFn = Callable[[str, object], Sequence["GrammarCase"]]


@dataclass(frozen=True)
class GrammarCase:
    derivation: str
    payload: object


@dataclass(frozen=True)
class BoundaryCase:
    derivation: str
    outcome_label: str
    path_id: str
    path_length: int


@dataclass(frozen=True)
class GrammarTargetReport:
    target: str
    total_cases: int
    unique_outcome_count: int
    unique_path_count: int
    cases: tuple[BoundaryCase, ...]


@dataclass(frozen=True)
class MinimizedWitness:
    target: str
    derivation: str
    outcome_label: str
    path_id: str
    path_length: int
    original_size: int
    minimized_size: int
    payload: object


@dataclass(frozen=True)
class GrammarTarget:
    name: str
    runner: RunnerFn
    trace_files: tuple[Path, ...]
    cases: tuple[GrammarCase, ...]
    repair_fn: RepairFn | None = None


API_SERVER_FILE = Path(api_server.__file__).resolve()
DEX_API_HELPERS_FILE = ROOT_DIR / "src" / "integration" / "_dex_api_helpers.py"
DEX_DISPATCH_RECEIPT_HANDLERS_FILE = ROOT_DIR / "src" / "integration" / "dex_dispatch_receipt_handlers.py"


class _FakeServer:
    cors_origins: set[str]
    demo_api_token: str
    dex_api_enabled: bool
    external_auth_enforced: bool

    def __init__(
        self,
        *,
        cors_origins: set[str] | None = None,
        demo_api_token: str = "",
        dex_api_enabled: bool = True,
        external_auth_enforced: bool = False,
    ) -> None:
        self.cors_origins = set() if cors_origins is None else set(cors_origins)
        self.demo_api_token = str(demo_api_token)
        self.dex_api_enabled = bool(dex_api_enabled)
        self.external_auth_enforced = bool(external_auth_enforced)


class _HandlerHarness:
    def __init__(
        self,
        *,
        headers: dict[str, str] | None = None,
        body: bytes = b"",
        cors_origins: set[str] | None = None,
        demo_api_token: str = "",
        dex_api_enabled: bool = True,
        external_auth_enforced: bool = False,
    ) -> None:
        self.handler = object.__new__(api_server._Handler)
        self.handler.server = _FakeServer(
            cors_origins=cors_origins,
            demo_api_token=demo_api_token,
            dex_api_enabled=dex_api_enabled,
            external_auth_enforced=external_auth_enforced,
        )
        self.handler.client_address = ("127.0.0.1", 12345)
        self.handler.headers = {} if headers is None else dict(headers)
        self.handler.rfile = io.BytesIO(body)
        self.handler.wfile = io.BytesIO()
        self.handler.close_connection = False
        self.captured: dict[str, Any] = {}

        def fake_write_json(this, status, obj, *, cors_origin):  # type: ignore[no-untyped-def]
            self.captured["status"] = int(status)
            self.captured["obj"] = obj
            self.captured["cors_origin"] = cors_origin

        self.handler._write_json = types.MethodType(fake_write_json, self.handler)


def _hash_path(lines: Sequence[str]) -> str:
    digest = hashlib.sha256("\n".join(lines).encode("utf-8")).hexdigest()
    return digest[:16]


def _stable_jsonable(value: object) -> object:
    if isinstance(value, dict):
        return {str(k): _stable_jsonable(v) for k, v in sorted(value.items(), key=lambda item: str(item[0]))}
    if isinstance(value, list):
        return [_stable_jsonable(v) for v in value]
    if isinstance(value, tuple):
        return {"__tuple__": [_stable_jsonable(v) for v in value]}
    if isinstance(value, bytes):
        return {"__bytes__": value.hex()}
    if isinstance(value, bytearray):
        return {"__bytes__": bytes(value).hex()}
    return value


def _payload_fingerprint(payload: object) -> str:
    return json.dumps(_stable_jsonable(payload), sort_keys=True, separators=(",", ":"), ensure_ascii=True)


def _trace_outcome(*, runner: RunnerFn, payload: object, trace_files: Sequence[Path]) -> tuple[str, str, int]:
    trace_names = {str(path.resolve()) for path in trace_files}
    lines: list[str] = []
    last_loc: str | None = None

    def tracer(frame, event, arg):  # type: ignore[no-untyped-def]
        nonlocal last_loc
        if event == "line":
            filename = str(Path(frame.f_code.co_filename).resolve())
            if filename in trace_names:
                loc = f"{Path(filename).name}:{frame.f_lineno}"
                if loc != last_loc:
                    lines.append(loc)
                    last_loc = loc
        return tracer

    previous = sys.gettrace()
    try:
        sys.settrace(tracer)
        try:
            outcome = runner(payload)
        except Exception as exc:  # pragma: no cover - exercised by callers
            outcome = f"{type(exc).__name__}:{exc}"
    finally:
        sys.settrace(previous)
    return outcome, _hash_path(lines), len(lines)


def _frontier_category(derivation: str) -> int:
    if derivation.startswith("repair:"):
        return 0
    if derivation.startswith("sweep:"):
        return 1
    return 2


def _run_parse_cors_origins(payload: object) -> str:
    origins = sorted(api_server._parse_cors_origins(str(payload)))
    if not origins:
        return "ok:none"
    return "ok:" + "|".join(origins)


def _run_demo_auth(payload: object) -> str:
    if not isinstance(payload, dict):
        raise TypeError("payload must be a dict")
    harness = _HandlerHarness(
        headers=payload.get("headers") if isinstance(payload.get("headers"), dict) else None,
        demo_api_token=str(payload.get("token", "")),
        external_auth_enforced=False,
    )
    return f"ok:{int(harness.handler._demo_auth_ok())}"


def _run_read_raw_body(payload: object) -> str:
    if not isinstance(payload, dict):
        raise TypeError("payload must be a dict")
    headers = payload.get("headers") if isinstance(payload.get("headers"), dict) else None
    body = payload.get("body", b"")
    if not isinstance(body, (bytes, bytearray)):
        raise TypeError("body must be bytes")
    harness = _HandlerHarness(headers=headers, body=bytes(body))
    raw, err = harness.handler._read_raw_body_with_error(int(payload.get("max_bytes", 65536)))
    if err is not None:
        return f"err:{err[0]}:{err[1]}:close={int(harness.handler.close_connection)}"
    if raw is None:
        return f"ok:none:close={int(harness.handler.close_connection)}"
    return f"ok:{len(raw)}:close={int(harness.handler.close_connection)}"


def _run_read_json_body(payload: object) -> str:
    if not isinstance(payload, dict):
        raise TypeError("payload must be a dict")
    headers = payload.get("headers") if isinstance(payload.get("headers"), dict) else None
    body = payload.get("body", b"")
    if not isinstance(body, (bytes, bytearray)):
        raise TypeError("body must be bytes")
    harness = _HandlerHarness(headers=headers, body=bytes(body))
    obj = harness.handler._read_json_body(int(payload.get("max_bytes", 65536)))
    if obj is None:
        return "ok:none"
    return "ok:" + "|".join(sorted(obj))


def _run_dex_request_envelope(payload: object) -> str:
    if not isinstance(payload, dict):
        raise TypeError("payload must be a dict")
    harness = _HandlerHarness(
        headers=payload.get("headers") if isinstance(payload.get("headers"), dict) else None,
        cors_origins=set(payload.get("cors_origins", [])) if isinstance(payload.get("cors_origins"), list) else None,
        demo_api_token=str(payload.get("token", "")),
        dex_api_enabled=bool(payload.get("dex_api_enabled", True)),
        external_auth_enforced=bool(payload.get("external_auth_enforced", not bool(payload.get("token", "")))),
    )
    handled = harness.handler._maybe_handle_dex_api(
        method=str(payload.get("method", "POST")),
        path=str(payload.get("path", "/api/dex/impact_preview")),
        cors_origin=payload.get("cors_origin") if isinstance(payload.get("cors_origin"), str) else None,
        raw_body=payload.get("raw_body") if isinstance(payload.get("raw_body"), (bytes, bytearray)) or payload.get("raw_body") is None else None,
    )
    if not handled:
        return "pass:false"
    status = int(harness.captured["status"])
    obj = harness.captured["obj"]
    if isinstance(obj, dict) and obj.get("ok") is True:
        return f"handled:{status}:ok"
    if isinstance(obj, dict):
        return f"handled:{status}:{obj.get('error', 'unknown')}"
    return f"handled:{status}:nonjson"


def _derive_authorization_repairs(outcome: str, payload: object) -> Sequence[GrammarCase]:
    if not isinstance(payload, dict):
        return ()
    headers = payload.get("headers")
    if not isinstance(headers, dict):
        headers = {}
    repairs: list[GrammarCase] = []
    if outcome == "ok:0":
        fixed = copy.deepcopy(payload)
        fixed["headers"] = {**headers, "Authorization": f"Bearer {payload.get('token', '')}"}
        repairs.append(GrammarCase("repair:auth->bearer-correct", fixed))
        disabled = copy.deepcopy(payload)
        disabled["token"] = ""
        repairs.append(GrammarCase("repair:auth->token-unset", disabled))
    elif outcome == "ok:1" and str(payload.get("token", "")):
        fixed = copy.deepcopy(payload)
        fixed["headers"] = {**headers, "Authorization": "Bearer wrong"}
        repairs.append(GrammarCase("repair:auth->bearer-wrong", fixed))
    return tuple(repairs)


def _derive_raw_body_repairs(outcome: str, payload: object) -> Sequence[GrammarCase]:
    if not isinstance(payload, dict):
        return ()
    repairs: list[GrammarCase] = []
    headers = payload.get("headers")
    body = payload.get("body", b"{}")
    if not isinstance(body, (bytes, bytearray)):
        return ()
    fixed = copy.deepcopy(payload)
    fixed["headers"] = {"Content-Length": str(len(body))}
    if outcome.startswith("err:400:invalid_content_length") or outcome == "ok:none:close=0":
        repairs.append(GrammarCase("repair:raw_body->set-exact-length", fixed))
    if outcome.startswith("err:413:body_too_large"):
        shrunken = copy.deepcopy(payload)
        shrunken["headers"] = {"Content-Length": "2"}
        shrunken["body"] = b"{}"
        repairs.append(GrammarCase("repair:raw_body->shrink-body", shrunken))
    if outcome == "ok:0:close=0":
        positive = copy.deepcopy(payload)
        positive["headers"] = {"Content-Length": "2"}
        positive["body"] = b"{}"
        repairs.append(GrammarCase("repair:raw_body->positive-length", positive))
    if outcome.startswith("ok:") and ":close=0" in outcome:
        length_str = None
        if isinstance(headers, dict):
            raw_length = headers.get("Content-Length")
            if isinstance(raw_length, str):
                length_str = raw_length
        try:
            length = int(length_str) if length_str is not None else None
        except Exception:
            length = None
        if isinstance(length, int) and length > 1:
            shorter = copy.deepcopy(payload)
            shorter["headers"] = {"Content-Length": str(length - 1)}
            repairs.append(GrammarCase("sweep:raw_body->length-minus-one", shorter))
    return tuple(repairs)


def _derive_json_body_repairs(outcome: str, payload: object) -> Sequence[GrammarCase]:
    if not isinstance(payload, dict):
        return ()
    repairs: list[GrammarCase] = []
    valid = b'{"x":1}'
    fixed = copy.deepcopy(payload)
    fixed["headers"] = {"Content-Length": str(len(valid))}
    fixed["body"] = valid
    if outcome == "ok:none":
        repairs.append(GrammarCase("repair:json_body->valid-object", fixed))
    elif outcome in {"ok:x", "ok:a|b"}:
        array_case = copy.deepcopy(payload)
        array_case["headers"] = {"Content-Length": "5"}
        array_case["body"] = b"[1,2]"
        repairs.append(GrammarCase("repair:json_body->array-payload", array_case))
    return tuple(repairs)


def _valid_impact_preview_body() -> bytes:
    return json.dumps(
        {
            "reserve_in": 1000,
            "reserve_out": 1000,
            "amount_in": 10,
            "fee_bps": 30,
            "pending_volume_same_direction": 0,
            "confidence_bps": 9500,
        },
        separators=(",", ":"),
    ).encode("utf-8")


def _impact_preview_body_with_overrides(**overrides: Any) -> bytes:
    body = {
        "reserve_in": 1000,
        "reserve_out": 1000,
        "amount_in": 10,
        "fee_bps": 30,
        "pending_volume_same_direction": 0,
        "confidence_bps": 9500,
    }
    body.update(overrides)
    return json.dumps(body, separators=(",", ":")).encode("utf-8")


def _derive_dex_envelope_repairs(outcome: str, payload: object) -> Sequence[GrammarCase]:
    if not isinstance(payload, dict):
        return ()
    repairs: list[GrammarCase] = []
    valid_body = _valid_impact_preview_body()
    if outcome == "pass:false":
        repaired = copy.deepcopy(payload)
        repaired["dex_api_enabled"] = True
        repaired["path"] = "/api/dex/impact_preview"
        repaired["method"] = "POST"
        repaired["raw_body"] = valid_body
        repairs.append(GrammarCase("repair:dex_req->enable-dex-route", repaired))
    elif outcome == "handled:401:unauthorized":
        repaired = copy.deepcopy(payload)
        headers = repaired.get("headers")
        if not isinstance(headers, dict):
            headers = {}
        repaired["headers"] = {**headers, "Authorization": f"Bearer {repaired.get('token', '')}"}
        repaired["raw_body"] = valid_body
        repairs.append(GrammarCase("repair:dex_req->authorized", repaired))
    elif outcome == "handled:405:method_not_allowed":
        repaired = copy.deepcopy(payload)
        repaired["method"] = "POST"
        repaired["raw_body"] = valid_body
        repairs.append(GrammarCase("repair:dex_req->post-method", repaired))
    elif outcome == "handled:400:missing_body":
        repaired = copy.deepcopy(payload)
        repaired["raw_body"] = valid_body
        repairs.append(GrammarCase("repair:dex_req->valid-body", repaired))
    elif outcome in {"handled:400:bad_json", "handled:400:bad_body", "handled:400:impact_preview_error"}:
        repaired = copy.deepcopy(payload)
        repaired["raw_body"] = valid_body
        repairs.append(GrammarCase("repair:dex_req->valid-impact-preview", repaired))
    elif outcome == "handled:404:not_found":
        repaired = copy.deepcopy(payload)
        repaired["path"] = "/api/dex/impact_preview"
        repaired["raw_body"] = valid_body
        repairs.append(GrammarCase("repair:dex_req->known-path", repaired))
    elif outcome == "handled:200:ok":
        malformed = copy.deepcopy(payload)
        malformed["raw_body"] = b"{broken"
        repairs.append(GrammarCase("repair:dex_req->break-json", malformed))
        repairs.extend(
            (
                GrammarCase(
                    "sweep:dex_req->bad-reserve-out",
                    {**copy.deepcopy(payload), "raw_body": _impact_preview_body_with_overrides(reserve_out="bad")},
                ),
                GrammarCase(
                    "sweep:dex_req->bad-amount-in",
                    {**copy.deepcopy(payload), "raw_body": _impact_preview_body_with_overrides(amount_in="bad")},
                ),
                GrammarCase(
                    "sweep:dex_req->bad-fee-bps",
                    {**copy.deepcopy(payload), "raw_body": _impact_preview_body_with_overrides(fee_bps="bad")},
                ),
                GrammarCase(
                    "sweep:dex_req->bad-pending-same-dir",
                    {
                        **copy.deepcopy(payload),
                        "raw_body": _impact_preview_body_with_overrides(pending_volume_same_direction="bad"),
                    },
                ),
                GrammarCase(
                    "sweep:dex_req->bad-confidence-bps",
                    {**copy.deepcopy(payload), "raw_body": _impact_preview_body_with_overrides(confidence_bps="bad")},
                ),
            )
        )
    return tuple(repairs)


def _derive_no_repairs(outcome: str, payload: object) -> Sequence[GrammarCase]:
    del outcome, payload
    return ()


TARGETS: tuple[GrammarTarget, ...] = (
    GrammarTarget(
        name="cors_origins",
        runner=_run_parse_cors_origins,
        trace_files=(API_SERVER_FILE,),
        repair_fn=_derive_no_repairs,
        cases=(
            GrammarCase("CorsList->Empty", ""),
            GrammarCase("CorsList->Whitespace", "   "),
            GrammarCase("CorsList->OneOrigin", "https://a.example"),
            GrammarCase("CorsList->TwoOriginsWithSpaces", " https://a.example , https://b.example "),
            GrammarCase("CorsList->WildcardIgnored", "*"),
            GrammarCase("CorsList->MixedWildcardAndTrusted", "https://a.example,*,https://b.example"),
            GrammarCase("CorsList->DuplicateAndBlankCollapsed", "https://a.example,,https://a.example"),
        ),
    ),
    GrammarTarget(
        name="demo_auth",
        runner=_run_demo_auth,
        trace_files=(API_SERVER_FILE,),
        repair_fn=_derive_authorization_repairs,
        cases=(
            GrammarCase("Auth->TokenUnset_NoHeader", {"token": "", "headers": {}}),
            GrammarCase("Auth->TokenSet_NoHeader", {"token": "sekret", "headers": {}}),
            GrammarCase("Auth->TokenSet_BasicHeader", {"token": "sekret", "headers": {"Authorization": "Basic sekret"}}),
            GrammarCase("Auth->TokenSet_BearerMissingToken", {"token": "sekret", "headers": {"Authorization": "Bearer"}}),
            GrammarCase("Auth->TokenSet_BearerWrongToken", {"token": "sekret", "headers": {"Authorization": "Bearer wrong"}}),
            GrammarCase("Auth->TokenSet_BearerCorrect", {"token": "sekret", "headers": {"Authorization": "Bearer sekret"}}),
            GrammarCase("Auth->TokenSet_BearerMixedCase", {"token": "sekret", "headers": {"Authorization": "bEaReR sekret"}}),
            GrammarCase("Auth->TokenSet_ExtraParts", {"token": "sekret", "headers": {"Authorization": "Bearer sekret extra"}}),
        ),
    ),
    GrammarTarget(
        name="raw_body",
        runner=_run_read_raw_body,
        trace_files=(API_SERVER_FILE,),
        repair_fn=_derive_raw_body_repairs,
        cases=(
            GrammarCase("RawBody->NoContentLength", {"headers": {}, "body": b"{}"}),
            GrammarCase("RawBody->InvalidContentLength", {"headers": {"Content-Length": "abc"}, "body": b"{}"}),
            GrammarCase("RawBody->ZeroLength", {"headers": {"Content-Length": "0"}, "body": b"{}"}),
            GrammarCase("RawBody->NegativeLength", {"headers": {"Content-Length": "-1"}, "body": b"{}"}),
            GrammarCase("RawBody->ExactLength", {"headers": {"Content-Length": "2"}, "body": b"{}"}),
            GrammarCase("RawBody->TruncatedRead", {"headers": {"Content-Length": "4"}, "body": b"{}"}),
            GrammarCase("RawBody->AtLimit", {"headers": {"Content-Length": "8"}, "body": b"12345678", "max_bytes": 8}),
            GrammarCase("RawBody->TooLarge", {"headers": {"Content-Length": "9"}, "body": b"123456789", "max_bytes": 8}),
        ),
    ),
    GrammarTarget(
        name="json_body",
        runner=_run_read_json_body,
        trace_files=(API_SERVER_FILE,),
        repair_fn=_derive_json_body_repairs,
        cases=(
            GrammarCase("JsonBody->NoContentLength", {"headers": {}, "body": b'{"x":1}'}),
            GrammarCase("JsonBody->InvalidContentLength", {"headers": {"Content-Length": "abc"}, "body": b'{"x":1}'}),
            GrammarCase("JsonBody->ZeroLength", {"headers": {"Content-Length": "0"}, "body": b'{"x":1}'}),
            GrammarCase("JsonBody->TooLarge", {"headers": {"Content-Length": "9"}, "body": b'{"x":1234}', "max_bytes": 8}),
            GrammarCase("JsonBody->BadUtf8", {"headers": {"Content-Length": "1"}, "body": b'\xff'}),
            GrammarCase("JsonBody->BadJson", {"headers": {"Content-Length": "15"}, "body": b'{"x": json bad}'}),
            GrammarCase("JsonBody->ArrayPayload", {"headers": {"Content-Length": "5"}, "body": b'[1,2]'}),
            GrammarCase("JsonBody->ObjectPayload", {"headers": {"Content-Length": "7"}, "body": b'{"x":1}'}),
            GrammarCase("JsonBody->TwoKeyObject", {"headers": {"Content-Length": "15"}, "body": b'{"a":1,"b":2}'}),
        ),
    ),
    GrammarTarget(
        name="dex_request_envelope",
        runner=_run_dex_request_envelope,
        trace_files=(API_SERVER_FILE, DEX_API_HELPERS_FILE, DEX_DISPATCH_RECEIPT_HANDLERS_FILE),
        repair_fn=_derive_dex_envelope_repairs,
        cases=(
            GrammarCase("DexReq->NonDexPath", {"method": "POST", "path": "/api/perps/markets", "raw_body": b'{}'}),
            GrammarCase("DexReq->DexDisabled", {"method": "POST", "path": "/api/dex/impact_preview", "dex_api_enabled": False, "raw_body": b'{}'}),
            GrammarCase("DexReq->Unauthorized", {"method": "POST", "path": "/api/dex/impact_preview", "token": "sekret", "headers": {}, "raw_body": b'{}'}),
            GrammarCase(
                "DexReq->UnauthorizedWithDeadFields",
                {
                    "method": "POST",
                    "path": "/api/dex/impact_preview",
                    "token": "sekret",
                    "headers": {},
                    "raw_body": b'{}',
                    "cors_origin": "https://dead.example",
                    "cors_origins": ["https://dead.example"],
                    "dead_blob": {"x": 1, "y": [2, 3]},
                },
            ),
            GrammarCase("DexReq->WrongMethod", {"method": "GET", "path": "/api/dex/impact_preview", "raw_body": b'{}'}),
            GrammarCase("DexReq->MissingBody", {"method": "POST", "path": "/api/dex/impact_preview", "raw_body": None}),
            GrammarCase("DexReq->BadJson", {"method": "POST", "path": "/api/dex/impact_preview", "raw_body": b'{broken'}),
            GrammarCase("DexReq->BadBody", {"method": "POST", "path": "/api/dex/impact_preview", "raw_body": b'[1,2]'}),
            GrammarCase(
                "DexReq->ImpactPreviewValid",
                {
                    "method": "POST",
                    "path": "/api/dex/impact_preview",
                    "raw_body": json.dumps(
                        {
                            "reserve_in": 1000,
                            "reserve_out": 1000,
                            "amount_in": 10,
                            "fee_bps": 30,
                            "pending_volume_same_direction": 0,
                            "confidence_bps": 9500,
                        },
                        separators=(",", ":"),
                    ).encode("utf-8"),
                },
            ),
            GrammarCase(
                "DexReq->ImpactPreviewError",
                {
                    "method": "POST",
                    "path": "/api/dex/impact_preview",
                    "raw_body": json.dumps(
                        {
                            "reserve_in": "bad",
                            "reserve_out": 1000,
                            "amount_in": 10,
                            "fee_bps": 30,
                        },
                        separators=(",", ":"),
                    ).encode("utf-8"),
                },
            ),
            GrammarCase(
                "DexReq->UnknownDexPath",
                {
                    "method": "POST",
                    "path": "/api/dex/not_real",
                    "raw_body": b'{}',
                },
            ),
        ),
    ),
)

TARGET_INDEX = {target.name: target for target in TARGETS}


def _payload_size(payload: object) -> int:
    return len(_payload_fingerprint(payload))


def _find_case(target_name: str, derivation: str) -> GrammarCase:
    target = TARGET_INDEX[target_name]
    for case in target.cases:
        if case.derivation == derivation:
            return case
    raise KeyError(f"unknown derivation for {target_name}: {derivation}")


def _minimization_candidates(payload: object) -> tuple[object, ...]:
    if not isinstance(payload, dict):
        return ()
    candidates: list[object] = []
    for key in sorted(payload):
        trimmed = copy.deepcopy(payload)
        del trimmed[key]
        candidates.append(trimmed)

    headers = payload.get("headers")
    if isinstance(headers, dict):
        for key in sorted(headers):
            trimmed = copy.deepcopy(payload)
            del trimmed["headers"][key]
            candidates.append(trimmed)

    cors_origins = payload.get("cors_origins")
    if isinstance(cors_origins, list):
        for idx in range(len(cors_origins)):
            trimmed = copy.deepcopy(payload)
            del trimmed["cors_origins"][idx]
            candidates.append(trimmed)

    return tuple(candidates)


def minimize_case(target_name: str, derivation: str, *, max_rounds: int = 16) -> MinimizedWitness:
    if target_name == "all":
        raise KeyError("minimize_case requires a concrete target")
    target = TARGET_INDEX[target_name]
    case = _find_case(target_name, derivation)
    current = copy.deepcopy(case.payload)
    outcome_label, path_id, path_length = _trace_outcome(
        runner=target.runner,
        payload=current,
        trace_files=target.trace_files,
    )
    original_size = _payload_size(current)
    current_size = original_size

    rounds = 0
    while rounds < max_rounds:
        rounds += 1
        best_payload: object | None = None
        best_size = current_size
        best_path_length = path_length
        for candidate in _minimization_candidates(current):
            candidate_size = _payload_size(candidate)
            if candidate_size >= best_size:
                continue
            cand_outcome, cand_path_id, cand_path_length = _trace_outcome(
                runner=target.runner,
                payload=candidate,
                trace_files=target.trace_files,
            )
            if cand_outcome != outcome_label or cand_path_id != path_id:
                continue
            best_payload = candidate
            best_size = candidate_size
            best_path_length = cand_path_length
        if best_payload is None:
            break
        current = best_payload
        current_size = best_size
        path_length = best_path_length

    return MinimizedWitness(
        target=target_name,
        derivation=derivation,
        outcome_label=outcome_label,
        path_id=path_id,
        path_length=path_length,
        original_size=original_size,
        minimized_size=current_size,
        payload=current,
    )


def explore_target(name: str) -> GrammarTargetReport:
    target = TARGET_INDEX[name]
    seen_pairs: set[tuple[str, str]] = set()
    seen_outcomes: set[str] = set()
    seen_paths: set[str] = set()
    seen_payloads: set[str] = set()
    cases: list[BoundaryCase] = []
    frontier: list[tuple[int, int, int, GrammarCase]] = [
        (0, _frontier_category(case.derivation), idx, case) for idx, case in enumerate(target.cases)
    ]
    heapq.heapify(frontier)
    next_order = len(frontier)

    while frontier:
        depth, _, _, case = heapq.heappop(frontier)
        payload_fp = _payload_fingerprint(case.payload)
        if payload_fp in seen_payloads:
            continue
        seen_payloads.add(payload_fp)
        outcome, path_id, path_length = _trace_outcome(
            runner=target.runner,
            payload=case.payload,
            trace_files=target.trace_files,
        )
        pair = (outcome, path_id)
        if pair in seen_pairs:
            continue
        seen_pairs.add(pair)
        seen_outcomes.add(outcome)
        seen_paths.add(path_id)
        cases.append(
            BoundaryCase(
                derivation=case.derivation,
                outcome_label=outcome,
                path_id=path_id,
                path_length=path_length,
            )
        )
        if depth >= 1 or target.repair_fn is None:
            continue
        followups = tuple(target.repair_fn(outcome, case.payload))
        for repair_index, repair_case in enumerate(followups):
            heapq.heappush(
                frontier,
                (
                    depth + 1,
                    _frontier_category(repair_case.derivation),
                    next_order + repair_index,
                    repair_case,
                ),
            )
        next_order += len(followups)

    return GrammarTargetReport(
        target=name,
        total_cases=len(cases),
        unique_outcome_count=len(seen_outcomes),
        unique_path_count=len(seen_paths),
        cases=tuple(sorted(cases, key=lambda item: (item.outcome_label, item.derivation, item.path_id))),
    )


def explore_all_targets() -> tuple[GrammarTargetReport, ...]:
    return tuple(explore_target(target.name) for target in TARGETS)


def _reports_json(reports: Sequence[GrammarTargetReport]) -> dict[str, Any]:
    return {
        "schema": "zenodex/api-server-request-grammar-fuzz/v1",
        "reports": [asdict(report) for report in reports],
    }


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Deterministic grammar-based request-envelope explorer for api_server.")
    parser.add_argument(
        "--target",
        default="all",
        choices=("all",) + tuple(sorted(TARGET_INDEX)),
        help="Boundary target to explore.",
    )
    parser.add_argument("--format", default="json", choices=("json", "text"))
    parser.add_argument("--minimize-derivation", help="minimize one named derivation while preserving its outcome/path pair")
    args = parser.parse_args(list(argv) if argv is not None else None)

    if args.minimize_derivation:
        if args.target == "all":
            parser.error("--minimize-derivation requires a concrete --target")
        witness = minimize_case(args.target, args.minimize_derivation)
        if args.format == "json":
            print(
                json.dumps(
                    {
                        "schema": "zenodex/api-server-request-minimized-witness/v1",
                        "witness": {
                            **asdict(witness),
                            "payload": _stable_jsonable(witness.payload),
                        },
                    },
                    indent=2,
                    sort_keys=True,
                )
            )
            return 0
        print(f"[{witness.target}] {witness.derivation}")
        print(f"outcome={witness.outcome_label} path={witness.path_id} len={witness.path_length}")
        print(f"size={witness.original_size}->{witness.minimized_size}")
        print(json.dumps(_stable_jsonable(witness.payload), indent=2, sort_keys=True))
        return 0

    reports = explore_all_targets() if args.target == "all" else (explore_target(args.target),)
    if args.format == "json":
        print(json.dumps(_reports_json(reports), indent=2, sort_keys=True))
        return 0

    for report in reports:
        print(f"[{report.target}] cases={report.total_cases} outcomes={report.unique_outcome_count} paths={report.unique_path_count}")
        for case in report.cases:
            print(f"  - {case.derivation}: {case.outcome_label} path={case.path_id} len={case.path_length}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
