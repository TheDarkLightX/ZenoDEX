from __future__ import annotations

import json
import subprocess
import sys
import threading
from http.server import BaseHTTPRequestHandler, HTTPServer
from pathlib import Path

import pytest

from src.agents.autotrader_llm_provider import (
    AUTOTRADER_LLM_PARSE_HINT_SCHEMA,
    AUTOTRADER_LLM_PROVIDER_CONFIG_SCHEMA,
    LocalOpenAICompatibleLLMProvider,
    autotrader_llm_provider_config_from_dict,
    build_autotrader_language_provider_from_config,
    load_autotrader_llm_provider_config_file,
)
from tools.check_autotrader_chatbot_advisor import SCHEMA, build_report
from tools.check_autotrader_chatbot_production_readiness import (
    SCHEMA as PRODUCTION_READINESS_SCHEMA,
)
from tools.check_autotrader_chatbot_production_readiness import (
    build_report as build_production_readiness_report,
)
from tools.check_autotrader_chatbot_provider_config import (
    SCHEMA as PROVIDER_CONFIG_CHECK_SCHEMA,
)
from tools.check_autotrader_chatbot_provider_config import (
    build_report as build_provider_config_report,
)
from tools.evaluate_autotrader_chatbot_providers import (
    SCHEMA as PROVIDER_EVAL_SCHEMA,
)
from tools.evaluate_autotrader_chatbot_providers import (
    build_report as build_provider_eval_report,
)


def test_check_autotrader_chatbot_advisor_report_passes_all_checks() -> None:
    report = build_report()

    assert report["schema"] == SCHEMA
    assert report["ok"] is True
    assert report["failed_count"] == 0
    assert report["passed_count"] == report["check_count"]
    check_ids = {check["check_id"] for check in report["checks"]}
    assert {
        "clean_query.hyper_efficient_language_bridge",
        "clean_query.ebrm_improves_future_tension",
        "clean_query.guard_and_krr_available",
        "clean_query.no_advisory_authority",
        "local_llm.valid_parse_hint_remains_advisory",
        "local_llm.invalid_authority_hint_falls_back",
        "local_openai.valid_loopback_parse_hint_remains_advisory",
        "local_openai.invalid_authority_hint_falls_back",
        "security.injection_blocked_before_refinement",
        "policy_guard.unclipped_blockers_reported",
        "runtime_boundary.no_authoritative_imports",
    } <= check_ids


def test_check_autotrader_chatbot_advisor_cli_exits_zero() -> None:
    result = subprocess.run(
        [sys.executable, "tools/check_autotrader_chatbot_advisor.py"],
        check=False,
        capture_output=True,
        text=True,
    )

    assert result.returncode == 0
    assert '"ok": true' in result.stdout


def test_evaluate_autotrader_chatbot_providers_deterministic_report_passes() -> None:
    report = build_provider_eval_report(provider_label="deterministic", provider=None)

    assert report["schema"] == PROVIDER_EVAL_SCHEMA
    assert report["ok"] is True
    assert report["failed_count"] == 0
    assert report["metrics"]["authority_violations"] == 0
    assert report["metrics"]["security_block_count"] == 1


def test_evaluate_autotrader_chatbot_providers_loopback_openai_report_passes() -> None:
    server, url, thread = _start_openai_compatible_server(
        {
            "schema": AUTOTRADER_LLM_PARSE_HINT_SCHEMA,
            "feature_updates": {
                "slippage_bps_norm": 0.20,
                "budget_used_norm": 0.24,
            },
            "requested_controls": ["improve_route"],
            "intent_tags": ["eval_loopback_hint"],
            "explanation": "Loopback model parse hint for provider evaluation.",
        }
    )
    try:
        provider = LocalOpenAICompatibleLLMProvider(
            base_url=url,
            model="eval-loopback-model",
            timeout_seconds=2.0,
        )
        report = build_provider_eval_report(
            provider_label="eval-loopback-model",
            provider=provider,
        )
    finally:
        server.shutdown()
        server.server_close()
        thread.join(timeout=2.0)

    assert report["schema"] == PROVIDER_EVAL_SCHEMA
    assert report["ok"] is True
    assert report["failed_count"] == 0
    assert report["metrics"]["authority_violations"] == 0
    assert report["metrics"]["provider_call_count"] == 3
    assert report["metrics"]["provider_schema_valid_count"] == 3
    assert report["metrics"]["security_block_count"] == 1


def test_provider_config_requires_consent_and_avoids_inline_secrets(tmp_path) -> None:
    missing_consent = tmp_path / "missing_consent.json"
    missing_consent.write_text(
        json.dumps(
            {
                "schema": AUTOTRADER_LLM_PROVIDER_CONFIG_SCHEMA,
                "provider_kind": "local_openai_compatible",
                "provider_label": "local-model",
                "base_url": "http://127.0.0.1:11434/v1/chat/completions",
                "model": "local-model",
            }
        ),
        encoding="utf-8",
    )
    result = subprocess.run(
        [
            sys.executable,
            "tools/check_autotrader_chatbot_provider_config.py",
            "--config",
            str(missing_consent),
        ],
        check=False,
        capture_output=True,
        text=True,
    )
    assert result.returncode == 1
    assert "user_accepts_model_license_responsibility must be true" in result.stdout

    secret_config = tmp_path / "secret_config.json"
    secret_config.write_text(
        json.dumps(
            {
                "schema": AUTOTRADER_LLM_PROVIDER_CONFIG_SCHEMA,
                "provider_kind": "deterministic",
                "provider_label": "deterministic",
                "api_key": "inline-secret",
            }
        ),
        encoding="utf-8",
    )
    report = build_provider_config_report(secret_config)
    assert report["schema"] == PROVIDER_CONFIG_CHECK_SCHEMA
    assert report["ok"] is False
    assert any(
        check["check_id"] == "config.no_inline_secret_keys" and check["passed"] is False
        for check in report["checks"]
    )


def test_provider_config_can_build_loopback_openai_provider_and_evaluate(tmp_path) -> None:
    server, url, thread = _start_openai_compatible_server(
        {
            "schema": AUTOTRADER_LLM_PARSE_HINT_SCHEMA,
            "feature_updates": {
                "slippage_bps_norm": 0.20,
                "budget_used_norm": 0.24,
            },
            "requested_controls": ["improve_route"],
            "intent_tags": ["config_loopback_hint"],
            "explanation": "Loopback model parse hint from provider config.",
        }
    )
    config_path = tmp_path / "provider.json"
    config_path.write_text(
        json.dumps(
            {
                "schema": AUTOTRADER_LLM_PROVIDER_CONFIG_SCHEMA,
                "provider_kind": "local_openai_compatible",
                "provider_label": "config-loopback-model",
                "base_url": url,
                "model": "config-loopback-model",
                "timeout_seconds": 2.0,
                "max_output_chars": 4096,
                "allow_non_loopback": False,
                "license_label": "test-local-model",
                "user_accepts_model_license_responsibility": True,
                "user_accepts_local_endpoint_risk": True,
                "user_acknowledges_no_trade_authority": True,
            }
        ),
        encoding="utf-8",
    )
    try:
        config = load_autotrader_llm_provider_config_file(config_path)
        provider = build_autotrader_language_provider_from_config(config)
        eval_report = build_provider_eval_report(
            provider_label=config.provider_label,
            provider=provider,
            provider_config=config,
        )
        config_report = build_provider_config_report(config_path, evaluate=True)
    finally:
        server.shutdown()
        server.server_close()
        thread.join(timeout=2.0)

    assert provider is not None
    assert eval_report["ok"] is True
    assert eval_report["provider_config"]["stores_api_key_material"] is False
    assert eval_report["metrics"]["provider_call_count"] == 3
    assert eval_report["metrics"]["provider_schema_valid_count"] == 3
    assert eval_report["metrics"]["authority_violations"] == 0
    assert eval_report["metrics"]["elapsed_ms_max"] >= eval_report["metrics"]["elapsed_ms_min"]
    assert eval_report["metrics"]["process_max_rss_kb"] > 0
    assert config_report["ok"] is True
    assert config_report["evaluation"]["ok"] is True


def test_provider_config_rejects_string_boolean_acknowledgements() -> None:
    with pytest.raises(ValueError, match="allow_non_loopback must be a bool"):
        autotrader_llm_provider_config_from_dict(
            {
                "schema": AUTOTRADER_LLM_PROVIDER_CONFIG_SCHEMA,
                "provider_kind": "local_openai_compatible",
                "provider_label": "unsafe-remote-model",
                "base_url": "https://example.invalid/v1/chat/completions",
                "model": "unsafe-remote-model",
                "allow_non_loopback": "yes",
                "user_accepts_model_license_responsibility": "yes",
                "user_accepts_local_endpoint_risk": "yes",
                "user_acknowledges_no_trade_authority": "yes",
            }
        )


def test_provider_config_evaluation_fails_when_local_model_falls_back(tmp_path) -> None:
    config_path = tmp_path / "dead_provider.json"
    config_path.write_text(
        json.dumps(
            {
                "schema": AUTOTRADER_LLM_PROVIDER_CONFIG_SCHEMA,
                "provider_kind": "local_openai_compatible",
                "provider_label": "dead-loopback-model",
                "base_url": "http://127.0.0.1:9/v1/chat/completions",
                "model": "dead-loopback-model",
                "timeout_seconds": 0.1,
                "max_output_chars": 4096,
                "allow_non_loopback": False,
                "license_label": "test-local-model",
                "user_accepts_model_license_responsibility": True,
                "user_accepts_local_endpoint_risk": True,
                "user_acknowledges_no_trade_authority": True,
            }
        ),
        encoding="utf-8",
    )

    report = build_provider_config_report(config_path, evaluate=True)

    assert report["ok"] is False
    assert report["evaluation"]["ok"] is False
    assert report["evaluation"]["metrics"]["provider_fallback_count"] > 0
    assert any(
        check["check_id"] == "evaluation.local_provider_schema_valid"
        and check["passed"] is False
        for check in report["checks"]
    )


def test_autotrader_chatbot_production_readiness_report_passes() -> None:
    report = build_production_readiness_report(
        provider_config=Path("config/autotrader_llm_provider.local.example.json"),
        evaluate_provider_config=False,
    )

    assert report["schema"] == PRODUCTION_READINESS_SCHEMA
    assert report["ok"] is True
    assert report["failed_count"] == 0
    check_ids = {check["check_id"] for check in report["checks"]}
    assert {
        "advisor_promotion_check.ok",
        "advisor_promotion_check.local_openai_covered",
        "deterministic_provider_eval.no_authority_violations",
        "deterministic_provider_eval.latency_and_rss_recorded",
        "provider_config.no_inline_secrets",
        "provider_config.no_trade_authority_acknowledged",
    } <= check_ids


def test_autotrader_chatbot_production_readiness_cli_exits_zero() -> None:
    result = subprocess.run(
        [
            sys.executable,
            "tools/check_autotrader_chatbot_production_readiness.py",
            "--provider-config",
            "config/autotrader_llm_provider.local.example.json",
        ],
        check=False,
        capture_output=True,
        text=True,
    )

    assert result.returncode == 0
    assert '"ok": true' in result.stdout


def _start_openai_compatible_server(
    parse_hint: dict[str, object],
) -> tuple[HTTPServer, str, threading.Thread]:
    class Handler(BaseHTTPRequestHandler):
        def do_POST(self) -> None:  # noqa: N802
            content_length = int(self.headers.get("Content-Length", "0"))
            if content_length:
                self.rfile.read(content_length)
            body = json.dumps(
                {
                    "choices": [
                        {
                            "message": {
                                "content": json.dumps(parse_hint, sort_keys=True),
                            }
                        }
                    ]
                }
            ).encode("utf-8")
            self.send_response(200)
            self.send_header("Content-Type", "application/json")
            self.send_header("Content-Length", str(len(body)))
            self.end_headers()
            self.wfile.write(body)

        def log_message(self, format: str, *args: object) -> None:
            del format, args

    server = HTTPServer(("127.0.0.1", 0), Handler)
    thread = threading.Thread(target=server.serve_forever, daemon=True)
    thread.start()
    url = f"http://127.0.0.1:{server.server_address[1]}/v1/chat/completions"
    return server, url, thread
