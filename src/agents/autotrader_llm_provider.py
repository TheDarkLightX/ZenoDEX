"""Local LLM provider adapters for the AutoTrader chatbot.

Providers in this module are parse-hint sources only. They may translate user
language into bounded feature updates, requested controls, tags, and a short
explanation. They do not authorize trades, execute strategies, sign intents, or
affect deterministic policy guards.
"""

from __future__ import annotations

import json
import math
import os
import urllib.error
import urllib.parse
import urllib.request
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Literal, Mapping, Protocol, Sequence

from ..energy.autotrader_energy import AUTOTRADER_FEATURE_NAMES
from ..energy.zeno_jepa import AUTOTRADER_CONTROL_IDS

AUTOTRADER_LLM_PARSE_HINT_SCHEMA = "zenodex/agents/autotrader_llm_parse_hint/v1"
AUTOTRADER_LLM_PROVIDER_CONFIG_SCHEMA = "zenodex/agents/autotrader_llm_provider_config/v1"
AutoTraderLLMProviderKind = Literal["deterministic", "local_openai_compatible"]

_LOCAL_HOSTS = {"localhost", "127.0.0.1", "::1"}
_AUTHORITY_KEYS = {
    "approve",
    "approved",
    "authorize",
    "authorized",
    "can_execute",
    "execute",
    "execution_approved",
    "guard_ok",
    "policy_ok",
    "sign",
    "signed",
    "submit",
    "trade_authorized",
}


@dataclass(frozen=True)
class AutoTraderLanguageProviderResult:
    """Strict parse-hint packet returned by a language provider."""

    provider: str
    llm_calls: int
    local_only: bool
    model: str | None
    schema_valid: bool
    feature_updates: dict[str, float]
    intent_tags: tuple[str, ...]
    requested_controls: tuple[str, ...]
    explanation: str
    error: str | None = None
    raw_response_chars: int = 0
    fallback_provider_used: bool = False

    def to_metadata(self) -> dict[str, Any]:
        return {
            "provider": self.provider,
            "llm_calls": self.llm_calls,
            "local_only": self.local_only,
            "model": self.model,
            "schema_valid": self.schema_valid,
            "intent_tags": list(self.intent_tags),
            "requested_controls": list(self.requested_controls),
            "explanation": self.explanation,
            "error": self.error,
            "raw_response_chars": self.raw_response_chars,
            "fallback_provider_used": self.fallback_provider_used,
            "llm_authorizes_trade": False,
        }


@dataclass(frozen=True)
class AutoTraderLocalLLMProviderConfig:
    """Validated configuration for user-supplied local language providers."""

    provider_kind: AutoTraderLLMProviderKind = "deterministic"
    provider_label: str = "deterministic"
    base_url: str | None = None
    model: str | None = None
    api_key_env: str | None = None
    timeout_seconds: float = 2.0
    max_output_chars: int = 4096
    allow_non_loopback: bool = False
    license_label: str | None = None
    user_accepts_model_license_responsibility: bool = False
    user_accepts_local_endpoint_risk: bool = False
    user_acknowledges_no_trade_authority: bool = False

    def __post_init__(self) -> None:
        if self.provider_kind not in ("deterministic", "local_openai_compatible"):
            raise ValueError("provider_kind must be deterministic or local_openai_compatible")
        if not self.provider_label:
            raise ValueError("provider_label must be non-empty")
        if self.timeout_seconds <= 0.0:
            raise ValueError("timeout_seconds must be positive")
        if self.max_output_chars <= 0:
            raise ValueError("max_output_chars must be positive")
        if self.provider_kind == "deterministic":
            return
        if not self.base_url:
            raise ValueError("base_url is required for local_openai_compatible")
        if not self.model:
            raise ValueError("model is required for local_openai_compatible")
        if not self.user_accepts_model_license_responsibility:
            raise ValueError("user_accepts_model_license_responsibility must be true")
        if not self.user_accepts_local_endpoint_risk:
            raise ValueError("user_accepts_local_endpoint_risk must be true")
        if not self.user_acknowledges_no_trade_authority:
            raise ValueError("user_acknowledges_no_trade_authority must be true")
        _validate_local_url(self.base_url, allow_non_loopback=self.allow_non_loopback)
        if self.api_key_env is not None and not self.api_key_env:
            raise ValueError("api_key_env must be non-empty when provided")

    def to_metadata(self) -> dict[str, Any]:
        return {
            "schema": AUTOTRADER_LLM_PROVIDER_CONFIG_SCHEMA,
            "provider_kind": self.provider_kind,
            "provider_label": self.provider_label,
            "base_url": self.base_url,
            "model": self.model,
            "api_key_env": self.api_key_env,
            "timeout_seconds": self.timeout_seconds,
            "max_output_chars": self.max_output_chars,
            "allow_non_loopback": self.allow_non_loopback,
            "license_label": self.license_label,
            "user_accepts_model_license_responsibility": (
                self.user_accepts_model_license_responsibility
            ),
            "user_accepts_local_endpoint_risk": self.user_accepts_local_endpoint_risk,
            "user_acknowledges_no_trade_authority": self.user_acknowledges_no_trade_authority,
            "stores_api_key_material": False,
        }


class AutoTraderLanguageProvider(Protocol):
    """Protocol for local parse-hint providers."""

    provider_id: str

    def parse(
        self,
        *,
        query: str,
        normalized_query: str,
        base_features: Mapping[str, float],
        requested_controls: Sequence[str],
        intent_tags: Sequence[str],
    ) -> AutoTraderLanguageProviderResult:
        """Return bounded parse hints for one user query."""


class LocalOpenAICompatibleLLMProvider:
    """Adapter for user-supplied local OpenAI-compatible chat servers.

    The default endpoint shape matches llama.cpp, vLLM, Ollama OpenAI mode, and
    many local runners. The adapter refuses non-loopback endpoints by default.
    """

    provider_id = "local_openai_compatible_llm"

    def __init__(
        self,
        *,
        base_url: str,
        model: str,
        timeout_seconds: float = 2.0,
        api_key: str | None = None,
        max_output_chars: int = 4096,
        allow_non_loopback: bool = False,
    ) -> None:
        if not base_url:
            raise ValueError("base_url must be non-empty")
        if not model:
            raise ValueError("model must be non-empty")
        if timeout_seconds <= 0.0:
            raise ValueError("timeout_seconds must be positive")
        if max_output_chars <= 0:
            raise ValueError("max_output_chars must be positive")
        _validate_local_url(base_url, allow_non_loopback=allow_non_loopback)
        self.base_url = base_url
        self.model = model
        self.timeout_seconds = timeout_seconds
        self.api_key = api_key
        self.max_output_chars = max_output_chars
        self.allow_non_loopback = allow_non_loopback

    def parse(
        self,
        *,
        query: str,
        normalized_query: str,
        base_features: Mapping[str, float],
        requested_controls: Sequence[str],
        intent_tags: Sequence[str],
    ) -> AutoTraderLanguageProviderResult:
        del normalized_query, base_features
        payload = {
            "model": self.model,
            "messages": [
                {"role": "system", "content": _provider_system_prompt()},
                {"role": "user", "content": query},
            ],
            "temperature": 0.0,
            "max_tokens": 256,
        }
        body = json.dumps(payload, separators=(",", ":")).encode("utf-8")
        headers = {"Content-Type": "application/json"}
        if self.api_key:
            headers["Authorization"] = f"Bearer {self.api_key}"
        request = urllib.request.Request(
            self.base_url,
            data=body,
            headers=headers,
            method="POST",
        )
        try:
            with urllib.request.urlopen(request, timeout=self.timeout_seconds) as response:
                raw = response.read(self.max_output_chars + 1).decode("utf-8", errors="replace")
        except (OSError, urllib.error.URLError, TimeoutError) as exc:
            return AutoTraderLanguageProviderResult(
                provider=self.provider_id,
                llm_calls=1,
                local_only=not self.allow_non_loopback,
                model=self.model,
                schema_valid=False,
                feature_updates={},
                intent_tags=tuple(intent_tags),
                requested_controls=tuple(requested_controls),
                explanation="",
                error=f"provider_call_failed:{exc.__class__.__name__}",
                fallback_provider_used=True,
            )
        if len(raw) > self.max_output_chars:
            return AutoTraderLanguageProviderResult(
                provider=self.provider_id,
                llm_calls=1,
                local_only=not self.allow_non_loopback,
                model=self.model,
                schema_valid=False,
                feature_updates={},
                intent_tags=tuple(intent_tags),
                requested_controls=tuple(requested_controls),
                explanation="",
                error="provider_response_too_large",
                raw_response_chars=len(raw),
                fallback_provider_used=True,
            )
        parsed = _parse_openai_compatible_response(raw)
        return validate_autotrader_llm_parse_hint(
            parsed,
            provider=self.provider_id,
            llm_calls=1,
            local_only=not self.allow_non_loopback,
            model=self.model,
            fallback_intent_tags=intent_tags,
            fallback_requested_controls=requested_controls,
            raw_response_chars=len(raw),
        )


def autotrader_llm_provider_config_from_dict(
    payload: Mapping[str, Any],
) -> AutoTraderLocalLLMProviderConfig:
    """Parse and validate a provider configuration dictionary."""

    if not isinstance(payload, Mapping):
        raise TypeError("provider config payload must be an object")
    schema = payload.get("schema")
    if schema not in (None, AUTOTRADER_LLM_PROVIDER_CONFIG_SCHEMA):
        raise ValueError("provider config schema mismatch")
    provider_kind = str(payload.get("provider_kind", "deterministic"))
    if provider_kind not in ("deterministic", "local_openai_compatible"):
        raise ValueError("provider_kind must be deterministic or local_openai_compatible")
    return AutoTraderLocalLLMProviderConfig(
        provider_kind=provider_kind,  # type: ignore[arg-type]
        provider_label=str(payload.get("provider_label", provider_kind)),
        base_url=_optional_string(payload.get("base_url")),
        model=_optional_string(payload.get("model")),
        api_key_env=_optional_string(payload.get("api_key_env")),
        timeout_seconds=float(payload.get("timeout_seconds", 2.0)),
        max_output_chars=int(payload.get("max_output_chars", 4096)),
        allow_non_loopback=_require_bool(payload.get("allow_non_loopback", False), name="allow_non_loopback"),
        license_label=_optional_string(payload.get("license_label")),
        user_accepts_model_license_responsibility=_require_bool(
            payload.get("user_accepts_model_license_responsibility", False),
            name="user_accepts_model_license_responsibility",
        ),
        user_accepts_local_endpoint_risk=_require_bool(
            payload.get("user_accepts_local_endpoint_risk", False),
            name="user_accepts_local_endpoint_risk",
        ),
        user_acknowledges_no_trade_authority=_require_bool(
            payload.get("user_acknowledges_no_trade_authority", False),
            name="user_acknowledges_no_trade_authority",
        ),
    )


def load_autotrader_llm_provider_config_file(
    path: str | Path,
) -> AutoTraderLocalLLMProviderConfig:
    """Load a JSON provider config file without accepting API key material."""

    payload = json.loads(Path(path).expanduser().resolve().read_text(encoding="utf-8"))
    return autotrader_llm_provider_config_from_dict(payload)


def build_autotrader_language_provider_from_config(
    config: AutoTraderLocalLLMProviderConfig,
) -> AutoTraderLanguageProvider | None:
    """Build a provider from validated config.

    The deterministic provider is represented by None because the chatbot's
    built-in parser remains the fallback path.
    """

    if config.provider_kind == "deterministic":
        return None
    api_key = os.environ.get(config.api_key_env) if config.api_key_env else None
    return LocalOpenAICompatibleLLMProvider(
        base_url=str(config.base_url),
        model=str(config.model),
        timeout_seconds=config.timeout_seconds,
        api_key=api_key,
        max_output_chars=config.max_output_chars,
        allow_non_loopback=config.allow_non_loopback,
    )


def validate_autotrader_llm_parse_hint(
    payload: Mapping[str, Any] | None,
    *,
    provider: str,
    llm_calls: int,
    local_only: bool,
    model: str | None,
    fallback_intent_tags: Sequence[str] = (),
    fallback_requested_controls: Sequence[str] = (),
    raw_response_chars: int = 0,
) -> AutoTraderLanguageProviderResult:
    """Validate the narrow parse-hint schema accepted from local LLMs."""

    if not isinstance(payload, Mapping):
        return _invalid_result(
            provider=provider,
            llm_calls=llm_calls,
            local_only=local_only,
            model=model,
            fallback_intent_tags=fallback_intent_tags,
            fallback_requested_controls=fallback_requested_controls,
            error="provider_payload_not_object",
            raw_response_chars=raw_response_chars,
        )
    if _contains_authority_key(payload):
        return _invalid_result(
            provider=provider,
            llm_calls=llm_calls,
            local_only=local_only,
            model=model,
            fallback_intent_tags=fallback_intent_tags,
            fallback_requested_controls=fallback_requested_controls,
            error="provider_payload_contains_authority_field",
            raw_response_chars=raw_response_chars,
        )
    schema = payload.get("schema")
    if schema not in (None, AUTOTRADER_LLM_PARSE_HINT_SCHEMA):
        return _invalid_result(
            provider=provider,
            llm_calls=llm_calls,
            local_only=local_only,
            model=model,
            fallback_intent_tags=fallback_intent_tags,
            fallback_requested_controls=fallback_requested_controls,
            error="provider_payload_schema_mismatch",
            raw_response_chars=raw_response_chars,
        )
    feature_updates_raw = payload.get("feature_updates", {})
    if not isinstance(feature_updates_raw, Mapping):
        return _invalid_result(
            provider=provider,
            llm_calls=llm_calls,
            local_only=local_only,
            model=model,
            fallback_intent_tags=fallback_intent_tags,
            fallback_requested_controls=fallback_requested_controls,
            error="feature_updates_not_object",
            raw_response_chars=raw_response_chars,
        )
    feature_updates: dict[str, float] = {}
    for key, value in feature_updates_raw.items():
        if key not in AUTOTRADER_FEATURE_NAMES:
            return _invalid_result(
                provider=provider,
                llm_calls=llm_calls,
                local_only=local_only,
                model=model,
                fallback_intent_tags=fallback_intent_tags,
                fallback_requested_controls=fallback_requested_controls,
                error=f"unknown_feature:{key}",
                raw_response_chars=raw_response_chars,
            )
        if not isinstance(value, (int, float)) or isinstance(value, bool):
            return _invalid_result(
                provider=provider,
                llm_calls=llm_calls,
                local_only=local_only,
                model=model,
                fallback_intent_tags=fallback_intent_tags,
                fallback_requested_controls=fallback_requested_controls,
                error=f"feature_value_not_number:{key}",
                raw_response_chars=raw_response_chars,
            )
        feature_value = float(value)
        if not math.isfinite(feature_value) or feature_value < 0.0 or feature_value > 1.0:
            return _invalid_result(
                provider=provider,
                llm_calls=llm_calls,
                local_only=local_only,
                model=model,
                fallback_intent_tags=fallback_intent_tags,
                fallback_requested_controls=fallback_requested_controls,
                error=f"feature_value_out_of_bounds:{key}",
                raw_response_chars=raw_response_chars,
            )
        feature_updates[str(key)] = feature_value
    controls = _validate_string_list(
        payload.get("requested_controls", []),
        allowed=set(AUTOTRADER_CONTROL_IDS),
        field_name="requested_controls",
    )
    tags = _validate_string_list(
        payload.get("intent_tags", []),
        allowed=None,
        field_name="intent_tags",
    )
    if isinstance(controls, str):
        return _invalid_result(
            provider=provider,
            llm_calls=llm_calls,
            local_only=local_only,
            model=model,
            fallback_intent_tags=fallback_intent_tags,
            fallback_requested_controls=fallback_requested_controls,
            error=controls,
            raw_response_chars=raw_response_chars,
        )
    if isinstance(tags, str):
        return _invalid_result(
            provider=provider,
            llm_calls=llm_calls,
            local_only=local_only,
            model=model,
            fallback_intent_tags=fallback_intent_tags,
            fallback_requested_controls=fallback_requested_controls,
            error=tags,
            raw_response_chars=raw_response_chars,
        )
    explanation = payload.get("explanation", "")
    if not isinstance(explanation, str):
        return _invalid_result(
            provider=provider,
            llm_calls=llm_calls,
            local_only=local_only,
            model=model,
            fallback_intent_tags=fallback_intent_tags,
            fallback_requested_controls=fallback_requested_controls,
            error="explanation_not_string",
            raw_response_chars=raw_response_chars,
        )
    return AutoTraderLanguageProviderResult(
        provider=provider,
        llm_calls=llm_calls,
        local_only=local_only,
        model=model,
        schema_valid=True,
        feature_updates=feature_updates,
        intent_tags=tuple(dict.fromkeys((*fallback_intent_tags, *tags))),
        requested_controls=tuple(dict.fromkeys((*fallback_requested_controls, *controls))),
        explanation=explanation[:512],
        raw_response_chars=raw_response_chars,
    )


def _invalid_result(
    *,
    provider: str,
    llm_calls: int,
    local_only: bool,
    model: str | None,
    fallback_intent_tags: Sequence[str],
    fallback_requested_controls: Sequence[str],
    error: str,
    raw_response_chars: int,
) -> AutoTraderLanguageProviderResult:
    return AutoTraderLanguageProviderResult(
        provider=provider,
        llm_calls=llm_calls,
        local_only=local_only,
        model=model,
        schema_valid=False,
        feature_updates={},
        intent_tags=tuple(fallback_intent_tags),
        requested_controls=tuple(fallback_requested_controls),
        explanation="",
        error=error,
        raw_response_chars=raw_response_chars,
        fallback_provider_used=True,
    )


def _validate_string_list(
    value: Any,
    *,
    allowed: set[str] | None,
    field_name: str,
) -> tuple[str, ...] | str:
    if not isinstance(value, list):
        return f"{field_name}_not_list"
    out: list[str] = []
    for item in value:
        if not isinstance(item, str):
            return f"{field_name}_item_not_string"
        normalized = item.strip()
        if not normalized or len(normalized) > 64:
            return f"{field_name}_item_invalid_length"
        if allowed is not None and normalized not in allowed:
            return f"{field_name}_unknown:{normalized}"
        out.append(normalized)
    return tuple(dict.fromkeys(out))


def _optional_string(value: Any) -> str | None:
    if value is None:
        return None
    if not isinstance(value, str):
        raise ValueError("optional string field must be a string when present")
    return value


def _require_bool(value: object, *, name: str) -> bool:
    if not isinstance(value, bool):
        raise ValueError(f"{name} must be a bool")
    return value


def _contains_authority_key(payload: Mapping[str, Any]) -> bool:
    for key, value in payload.items():
        if str(key).lower() in _AUTHORITY_KEYS:
            return True
        if isinstance(value, Mapping) and _contains_authority_key(value):
            return True
        if isinstance(value, list):
            for item in value:
                if isinstance(item, Mapping) and _contains_authority_key(item):
                    return True
    return False


def _parse_openai_compatible_response(raw: str) -> Mapping[str, Any] | None:
    try:
        response = json.loads(raw)
    except json.JSONDecodeError:
        return _json_object_from_text(raw)
    choices = response.get("choices") if isinstance(response, Mapping) else None
    if not isinstance(choices, list) or not choices:
        if isinstance(response, Mapping):
            return response
        return None
    first = choices[0]
    if not isinstance(first, Mapping):
        return None
    message = first.get("message")
    content: Any
    if isinstance(message, Mapping):
        content = message.get("content")
    else:
        content = first.get("text")
    if isinstance(content, list):
        content = "".join(
            str(part.get("text", "")) if isinstance(part, Mapping) else str(part)
            for part in content
        )
    if not isinstance(content, str):
        return None
    return _json_object_from_text(content)


def _json_object_from_text(text: str) -> Mapping[str, Any] | None:
    start = text.find("{")
    end = text.rfind("}")
    if start < 0 or end < start:
        return None
    try:
        parsed = json.loads(text[start : end + 1])
    except json.JSONDecodeError:
        return None
    return parsed if isinstance(parsed, Mapping) else None


def _validate_local_url(base_url: str, *, allow_non_loopback: bool) -> None:
    parsed = urllib.parse.urlparse(base_url)
    if parsed.scheme not in {"http", "https"}:
        raise ValueError("base_url must use http or https")
    if not parsed.netloc:
        raise ValueError("base_url must include a host")
    if allow_non_loopback:
        return
    host = parsed.hostname
    if host not in _LOCAL_HOSTS:
        raise ValueError("base_url must be loopback unless allow_non_loopback=True")


def _provider_system_prompt() -> str:
    features = ", ".join(AUTOTRADER_FEATURE_NAMES)
    controls = ", ".join(AUTOTRADER_CONTROL_IDS)
    return (
        "Return strict JSON only. You are a local parse-hint provider for ZenoDEX "
        "AutoTrader. Do not approve, authorize, execute, sign, or bypass policy. "
        f"Schema: {AUTOTRADER_LLM_PARSE_HINT_SCHEMA}. "
        "Use keys schema, feature_updates, requested_controls, intent_tags, explanation. "
        f"Feature update keys must be from: {features}. Values must be numbers in [0,1]. "
        f"Requested controls must be from: {controls}."
    )


__all__ = [
    "AUTOTRADER_LLM_PARSE_HINT_SCHEMA",
    "AUTOTRADER_LLM_PROVIDER_CONFIG_SCHEMA",
    "AutoTraderLanguageProvider",
    "AutoTraderLanguageProviderResult",
    "AutoTraderLLMProviderKind",
    "AutoTraderLocalLLMProviderConfig",
    "LocalOpenAICompatibleLLMProvider",
    "autotrader_llm_provider_config_from_dict",
    "build_autotrader_language_provider_from_config",
    "load_autotrader_llm_provider_config_file",
    "validate_autotrader_llm_parse_hint",
]
