"""Test-only language-provider fixtures for AutoTrader advisor tests."""

from __future__ import annotations

import json
from typing import Any, Mapping, Sequence

from src.agents.autotrader_llm_provider import (
    AutoTraderLanguageProviderResult,
    validate_autotrader_llm_parse_hint,
)


class FixedAutoTraderLanguageProvider:
    """Return one fixed parse-hint payload through the production validator."""

    provider_id = "fixed_autotrader_language_test_provider"

    def __init__(self, payload: Mapping[str, Any], *, model: str = "fixed-test-provider") -> None:
        self._payload = dict(payload)
        self._model = model

    def parse(
        self,
        *,
        query: str,
        normalized_query: str,
        base_features: Mapping[str, float],
        requested_controls: Sequence[str],
        intent_tags: Sequence[str],
    ) -> AutoTraderLanguageProviderResult:
        del query, normalized_query, base_features
        return validate_autotrader_llm_parse_hint(
            self._payload,
            provider=self.provider_id,
            llm_calls=1,
            local_only=True,
            model=self._model,
            fallback_intent_tags=intent_tags,
            fallback_requested_controls=requested_controls,
            raw_response_chars=len(json.dumps(self._payload, sort_keys=True)),
        )


__all__ = ["FixedAutoTraderLanguageProvider"]
