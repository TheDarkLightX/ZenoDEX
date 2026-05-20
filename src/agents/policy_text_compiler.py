from __future__ import annotations

import hashlib
import re
from dataclasses import dataclass
from typing import Any

from .policy_compiler import PolicyCompilationResult, compile_policy_candidate
from .strategy_ir import AUTOTRADER_TAU_POLICY_SPECS

_KV_LINE_RE = re.compile(r"^\s*([a-zA-Z_][a-zA-Z0-9_]*)\s*:\s*(.*?)\s*$")
_SAFE_TOKEN_RE = re.compile(r"^[A-Za-z0-9_.:-]{1,128}$")
_BOOL_TRUE = {"1", "true", "yes", "on"}
_BOOL_FALSE = {"0", "false", "no", "off"}
_DCA_SENTENCE_RE = re.compile(
    r"^\s*dca\s+"
    r"(?P<fixed_order_size>\d+)\s+"
    r"(?P<asset_in>[A-Za-z0-9_.:-]+)\s+"
    r"(?:into|to|for)\s+"
    r"(?P<asset_out>[A-Za-z0-9_.:-]+)\s+"
    r"every\s+(?P<cadence_epochs>\d+)\s+epochs?"
    r"(?P<rest>.*)$",
    re.IGNORECASE,
)
_WINDOW_RANGE_RE = re.compile(
    r"\b(?:window|from\s+epoch)\s+(?P<valid_from>\d+)\s+(?:to|-|until)\s+(?P<valid_until>\d+)\b",
    re.IGNORECASE,
)
_UNTIL_EPOCH_RE = re.compile(r"\buntil\s+epoch\s+(?P<valid_until>\d+)\b", re.IGNORECASE)
_SLIPPAGE_RE = re.compile(r"\bmax\s+slippage\s+(?P<max_slippage_bps>\d+)\s+bps\b", re.IGNORECASE)
_WINDOW_CAP_RE = re.compile(r"\bper\s+window\s+max\s+(?P<per_window_max>\d+)\b", re.IGNORECASE)
_LIFETIME_CAP_RE = re.compile(r"\blifetime\s+max\s+(?P<lifetime_max>\d+)\b", re.IGNORECASE)
_LIVE_ORDERS_RE = re.compile(r"\bmax\s+live\s+orders\s+(?P<max_live_orders>\d+)\b", re.IGNORECASE)
_ORACLE_RE = re.compile(
    r"\bmax\s+oracle\s+staleness\s+(?P<max_oracle_staleness_epochs>\d+)\s+epochs?\b",
    re.IGNORECASE,
)
_BACKEND_RE = re.compile(r"\bbackend\s+(?P<policy_backend>local|tau)\b", re.IGNORECASE)
_REQUIRE_RECEIPTS_RE = re.compile(
    r"\bquote\s+receipts?\s+(?P<require_quote_receipts>required|disabled)\b",
    re.IGNORECASE,
)
_KILL_SWITCH_RE = re.compile(r"\bkill\s+switch\s+(?P<kill_switch_enabled>enabled|disabled)\b", re.IGNORECASE)
_MIN_SPACING_RE = re.compile(
    r"\bmin\s+order\s+spacing\s+(?P<min_order_spacing_epochs>\d+)\s+epochs?\b",
    re.IGNORECASE,
)


@dataclass(frozen=True)
class PolicyTextCompilation:
    candidate: dict[str, Any]
    compiled: PolicyCompilationResult
    source_form: str
    explain: tuple[str, ...]


def _safe_token(value: str, *, name: str) -> str:
    text = str(value).strip()
    if not _SAFE_TOKEN_RE.fullmatch(text):
        raise ValueError(f"{name} contains unsupported characters: {value!r}")
    return text


def _safe_int(value: str, *, name: str, minimum: int = 0, maximum: int = 0xFFFFFFFF) -> int:
    if not re.fullmatch(r"\d+", str(value).strip()):
        raise ValueError(f"{name} must be a non-negative integer: {value!r}")
    out = int(str(value).strip())
    if out < minimum or out > maximum:
        raise ValueError(f"{name} out of range: {out}")
    return out


def _bool_from_text(value: str, *, name: str) -> bool:
    text = str(value).strip().lower()
    if text in _BOOL_TRUE:
        return True
    if text in _BOOL_FALSE:
        return False
    raise ValueError(f"{name} must be a boolean-like value")


def _default_strategy_id(text: str) -> str:
    digest = hashlib.sha256(text.encode("utf-8")).hexdigest()[:16]
    return f"auto.{digest}"


def _kv_candidate_from_text(text: str, *, owner_pubkey: str | None) -> dict[str, Any] | None:
    rows: dict[str, str] = {}
    for raw_line in text.splitlines():
        line = raw_line.strip()
        if not line or line.startswith("#"):
            continue
        m = _KV_LINE_RE.match(raw_line)
        if not m:
            return None
        rows[m.group(1).strip().lower()] = m.group(2).strip()
    if not rows:
        return None
    if "template" not in rows:
        raise ValueError("key-value policy text must define template")

    template = rows["template"].strip().lower()
    candidate: dict[str, Any] = {
        "strategy_id": _safe_token(rows.get("strategy_id", _default_strategy_id(text)), name="strategy_id"),
        "owner_pubkey": _safe_token(rows.get("owner_pubkey", owner_pubkey or ""), name="owner_pubkey"),
        "policy_backend": rows.get("backend", rows.get("policy_backend", "local")).strip().lower(),
        "template": template,
        "asset_universe": [],
        "notional_caps": {
            "per_order_max": _safe_int(rows.get("per_order_max", "0"), name="per_order_max"),
            "per_window_max": _safe_int(rows.get("per_window_max", "0"), name="per_window_max"),
            "lifetime_max": _safe_int(rows.get("lifetime_max", "0"), name="lifetime_max"),
        },
        "risk_limits": {
            "max_slippage_bps": _safe_int(rows.get("max_slippage_bps", "50"), name="max_slippage_bps", maximum=10_000),
            "max_oracle_staleness_epochs": _safe_int(
                rows.get("max_oracle_staleness_epochs", "3"),
                name="max_oracle_staleness_epochs",
                minimum=1,
            ),
            "require_quote_receipts": _bool_from_text(
                rows.get("require_quote_receipts", "true"),
                name="require_quote_receipts",
            ),
        },
        "strategy_window": {
            "valid_from_epoch": _safe_int(rows.get("valid_from_epoch", "0"), name="valid_from_epoch"),
            "valid_until_epoch": _safe_int(rows.get("valid_until_epoch", "0"), name="valid_until_epoch"),
            "min_order_spacing_epochs": _safe_int(
                rows.get("min_order_spacing_epochs", "0"),
                name="min_order_spacing_epochs",
            ),
            "budget_window_epochs": _safe_int(
                rows.get("budget_window_epochs", "0"),
                name="budget_window_epochs",
            ),
        },
        "controls": {
            "kill_switch_enabled": _bool_from_text(
                rows.get("kill_switch_enabled", "true"),
                name="kill_switch_enabled",
            ),
            "max_live_orders": _safe_int(rows.get("max_live_orders", "1"), name="max_live_orders", minimum=1),
            "max_intents_per_order": _safe_int(
                rows.get("max_intents_per_order", "16"),
                name="max_intents_per_order",
                minimum=1,
            ),
        },
        "template_params": {},
    }
    template_params: dict[str, Any] = {}
    known_top_level = {
        "strategy_id",
        "owner_pubkey",
        "template",
        "backend",
        "policy_backend",
        "per_order_max",
        "per_window_max",
        "lifetime_max",
        "max_slippage_bps",
        "max_oracle_staleness_epochs",
        "require_quote_receipts",
        "valid_from_epoch",
        "valid_until_epoch",
        "min_order_spacing_epochs",
        "budget_window_epochs",
        "kill_switch_enabled",
        "max_live_orders",
        "max_intents_per_order",
        "tau_policy_spec",
        "tau_policy_specs",
        "asset_universe",
        "allowed_actions",
    }
    for key, value in rows.items():
        if key in known_top_level:
            continue
        if key in {"fixed_order_size", "cadence_epochs", "trigger_price", "ladder_levels", "per_level_size"}:
            template_params[key] = _safe_int(value, name=key, minimum=1)
        elif key in {"asset_in", "asset_out"}:
            template_params[key] = _safe_token(value, name=key)
        else:
            template_params[key] = value
    candidate["template_params"] = template_params

    if "asset_universe" in rows:
        assets = [_safe_token(part, name="asset_universe") for part in rows["asset_universe"].split(",") if part.strip()]
    else:
        assets = []
        for key in ("asset_in", "asset_out"):
            template_value = template_params.get(key)
            if isinstance(template_value, str) and template_value not in assets:
                assets.append(template_value)
    if len(assets) < 2:
        raise ValueError("key-value policy text must define asset_universe or asset_in/asset_out")
    candidate["asset_universe"] = assets

    if "allowed_actions" in rows:
        candidate["allowed_actions"] = [part.strip() for part in rows["allowed_actions"].split(",") if part.strip()]

    if candidate["policy_backend"] == "tau":
        if "tau_policy_specs" in rows:
            candidate["tau_policy_specs"] = [part.strip() for part in rows["tau_policy_specs"].split(",") if part.strip()]
        else:
            candidate["tau_policy_specs"] = list(AUTOTRADER_TAU_POLICY_SPECS)
    return candidate


def _sentence_candidate_from_text(text: str, *, owner_pubkey: str | None) -> dict[str, Any]:
    m = _DCA_SENTENCE_RE.match(text.strip())
    if not m:
        raise ValueError(
            "unsupported policy text; use controlled DCA text or explicit key:value policy lines"
        )
    fixed_order_size = _safe_int(m.group("fixed_order_size"), name="fixed_order_size", minimum=1)
    cadence_epochs = _safe_int(m.group("cadence_epochs"), name="cadence_epochs", minimum=1)
    asset_in = _safe_token(m.group("asset_in"), name="asset_in")
    asset_out = _safe_token(m.group("asset_out"), name="asset_out")
    if asset_in == asset_out:
        raise ValueError("asset_in and asset_out must differ")
    rest = m.group("rest") or ""

    valid_from_epoch = 0
    valid_until_epoch = cadence_epochs
    window_m = _WINDOW_RANGE_RE.search(rest)
    if window_m:
        valid_from_epoch = _safe_int(window_m.group("valid_from"), name="valid_from_epoch")
        valid_until_epoch = _safe_int(window_m.group("valid_until"), name="valid_until_epoch")
    else:
        until_m = _UNTIL_EPOCH_RE.search(rest)
        if until_m:
            valid_until_epoch = _safe_int(until_m.group("valid_until"), name="valid_until_epoch")

    max_slippage_bps = 50
    slippage_m = _SLIPPAGE_RE.search(rest)
    if slippage_m:
        max_slippage_bps = _safe_int(
            slippage_m.group("max_slippage_bps"),
            name="max_slippage_bps",
            maximum=10_000,
        )

    per_window_max = fixed_order_size
    window_cap_m = _WINDOW_CAP_RE.search(rest)
    if window_cap_m:
        per_window_max = _safe_int(window_cap_m.group("per_window_max"), name="per_window_max", minimum=fixed_order_size)

    lifetime_max = per_window_max
    lifetime_cap_m = _LIFETIME_CAP_RE.search(rest)
    if lifetime_cap_m:
        lifetime_max = _safe_int(lifetime_cap_m.group("lifetime_max"), name="lifetime_max", minimum=per_window_max)

    max_live_orders = 1
    live_orders_m = _LIVE_ORDERS_RE.search(rest)
    if live_orders_m:
        max_live_orders = _safe_int(live_orders_m.group("max_live_orders"), name="max_live_orders", minimum=1)

    max_oracle_staleness_epochs = 3
    oracle_m = _ORACLE_RE.search(rest)
    if oracle_m:
        max_oracle_staleness_epochs = _safe_int(
            oracle_m.group("max_oracle_staleness_epochs"),
            name="max_oracle_staleness_epochs",
            minimum=1,
        )

    backend = "local"
    backend_m = _BACKEND_RE.search(rest)
    if backend_m:
        backend = backend_m.group("policy_backend").strip().lower()

    require_quote_receipts = True
    receipts_m = _REQUIRE_RECEIPTS_RE.search(rest)
    if receipts_m:
        require_quote_receipts = receipts_m.group("require_quote_receipts").strip().lower() == "required"

    kill_switch_enabled = True
    kill_switch_m = _KILL_SWITCH_RE.search(rest)
    if kill_switch_m:
        kill_switch_enabled = kill_switch_m.group("kill_switch_enabled").strip().lower() == "enabled"

    min_order_spacing_epochs = 0
    min_spacing_m = _MIN_SPACING_RE.search(rest)
    if min_spacing_m:
        min_order_spacing_epochs = _safe_int(
            min_spacing_m.group("min_order_spacing_epochs"),
            name="min_order_spacing_epochs",
        )

    candidate: dict[str, Any] = {
        "strategy_id": _default_strategy_id(text),
        "owner_pubkey": _safe_token(owner_pubkey or "", name="owner_pubkey"),
        "policy_backend": backend,
        "template": "dca",
        "asset_universe": [asset_in, asset_out],
        "notional_caps": {
            "per_order_max": fixed_order_size,
            "per_window_max": per_window_max,
            "lifetime_max": lifetime_max,
        },
        "risk_limits": {
            "max_slippage_bps": max_slippage_bps,
            "max_oracle_staleness_epochs": max_oracle_staleness_epochs,
            "require_quote_receipts": require_quote_receipts,
        },
        "strategy_window": {
            "valid_from_epoch": valid_from_epoch,
            "valid_until_epoch": valid_until_epoch,
            "min_order_spacing_epochs": min_order_spacing_epochs,
            "budget_window_epochs": 0,
        },
        "controls": {
            "kill_switch_enabled": kill_switch_enabled,
            "max_live_orders": max_live_orders,
            "max_intents_per_order": 16,
        },
        "template_params": {
            "fixed_order_size": fixed_order_size,
            "cadence_epochs": cadence_epochs,
            "asset_in": asset_in,
            "asset_out": asset_out,
        },
    }
    if backend == "tau":
        candidate["tau_policy_specs"] = list(AUTOTRADER_TAU_POLICY_SPECS)
    return candidate


def compile_policy_text(
    text: str,
    *,
    owner_pubkey: str | None = None,
) -> PolicyTextCompilation:
    if not isinstance(text, str):
        raise TypeError("text must be a string")
    normalized_text = text.strip()
    if not normalized_text:
        raise ValueError("policy text must be non-empty")

    kv_candidate = _kv_candidate_from_text(normalized_text, owner_pubkey=owner_pubkey)
    source_form = "kv"
    candidate = kv_candidate
    if candidate is None:
        source_form = "sentence"
        candidate = _sentence_candidate_from_text(normalized_text, owner_pubkey=owner_pubkey)

    compiled = compile_policy_candidate(candidate, owner_pubkey=owner_pubkey)
    explain = (
        f"source_form={source_form}",
        f"template={compiled.strategy.template.value}",
        f"backend={compiled.strategy.policy_backend.value}",
        f"strategy_id={compiled.strategy.strategy_id}",
        *compiled.explain,
    )
    return PolicyTextCompilation(
        candidate=candidate,
        compiled=compiled,
        source_form=source_form,
        explain=tuple(explain),
    )
