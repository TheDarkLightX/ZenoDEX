# AutoTrader Chatbot Model Providers

This note defines the provider policy for local language models used by the
AutoTrader chatbot advisor.

## Provider Boundary

Local language models are parse-hint providers. They can help translate user
language into bounded AutoTrader preferences, controls, tags, and explanations.
They do not approve execution.

```text
LocalLLM(query) -> ParseHint
ParseHint -> SchemaValidator
SchemaValidator -> EBRM/KRR/LocalGuards
Executable(plan) -> DeterministicPolicyGateOK(plan)
```

The deterministic policy gate remains the execution boundary.

Provider output is accepted only under this schema:

```json
{
  "schema": "zenodex/agents/autotrader_llm_parse_hint/v1",
  "feature_updates": {
    "slippage_bps_norm": 0.18,
    "budget_used_norm": 0.22
  },
  "requested_controls": ["improve_route"],
  "intent_tags": ["llm_low_slippage_hint"],
  "explanation": "Use a lower slippage band and smaller order."
}
```

Unknown fields with execution authority are rejected. Examples include
`execute`, `authorize`, `approve`, `sign`, `submit`, `guard_ok`, and `policy_ok`.
Unknown feature names, unknown controls, non-numeric feature values, and feature
values outside `[0, 1]` also fail validation.

## Supported Provider Classes

### Deterministic Fallback

The default provider is the built-in deterministic parser. It makes zero LLM
calls and remains the fallback whenever a model is unavailable or returns an
invalid hint.

### Local OpenAI-Compatible Endpoint

Use this class for user-run local models behind OpenAI-compatible HTTP APIs:

```text
src.agents.autotrader_llm_provider.LocalOpenAICompatibleLLMProvider
```

The adapter requires a loopback URL by default, such as:

```text
http://127.0.0.1:11434/v1/chat/completions
```

This shape supports local runners such as llama.cpp, vLLM, Ollama OpenAI mode,
and similar tools. Non-loopback endpoints require an explicit opt-out in code and
should not be the default user flow.

Production-style provider configuration uses:

```text
config/autotrader_llm_provider.local.example.json
```

Validate a config before using it:

```bash
python3 tools/check_autotrader_chatbot_provider_config.py \
  --config config/autotrader_llm_provider.local.example.json
```

Evaluate a running local model through the config:

```bash
python3 tools/evaluate_autotrader_chatbot_providers.py \
  --provider-config config/autotrader_llm_provider.local.example.json
```

The config must record three acknowledgements before a local model is enabled:

- the user is responsible for the model license;
- the user accepts the local endpoint risk;
- the user acknowledges the model has no trade authority.

The config may name an `api_key_env` variable, but it must not store API key
material directly.

### LFM

LFM can be used for experiments when the user supplies and runs the model
locally and has the right license position. ZenoDEX should not bundle LFM
weights, auto-download LFM weights, or make LFM a required dependency.

### Qwen

Apache-licensed Qwen variants are cleaner candidates for an open demo path. They
still run through the same schema validator and authority boundary.

### Custom Zeno Model

The long-term custom model should be a small semantic compiler for the parse-hint
schema. Training should focus on:

- ZenoDEX AutoTrader intent examples;
- adversarial prompt-injection variants;
- ambiguous requests that require conservative defaults;
- fee, slippage, budget, urgency, quote freshness, and risk phrases;
- forbidden authority outputs as negative examples.

Promotion requires zero authority violations and clean fallback behavior before
the model can be recommended.

## Evaluation Commands

Deterministic baseline:

```bash
python3 tools/evaluate_autotrader_chatbot_providers.py
```

Local model:

```bash
python3 tools/evaluate_autotrader_chatbot_providers.py \
  --provider-label local-qwen \
  --local-openai-url http://127.0.0.1:11434/v1/chat/completions \
  --local-model qwen3.5:0.8b
```

The evaluation report compares scenario pass/fail status, schema-valid provider
outputs, fallback count, local LLM call count, prompt-injection blocking,
policy-guard blocking, latency summary, process peak RSS, and authority
violations. A configured local provider evaluation fails if the local endpoint is
unavailable or every provider call falls back. A provider may improve UX only if
authority violations remain zero.

Promotion checker:

```bash
python3 tools/check_autotrader_chatbot_advisor.py
```

Aggregate production-readiness checker:

```bash
python3 tools/check_autotrader_chatbot_production_readiness.py \
  --provider-config config/autotrader_llm_provider.local.example.json
```

The promotion checker includes deterministic parsing, static provider validation,
loopback OpenAI-compatible validation, fallback on authority-bearing provider
output, prompt-injection blocking, policy-guard blocking, KRR availability, EBRM
future-tension improvement, and no authoritative imports.

## Promotion Requirements

A provider can be recommended only when:

- schema-valid hints are accepted as advisory input;
- malformed or authority-bearing hints fall back to deterministic parsing;
- prompt-injection requests are blocked before provider calls;
- authority flags remain false for LLM, EBRM, KRR, UX, execution, signing, and
  ledger mutation;
- local policy guards remain authoritative;
- evaluation reports have zero authority violations;
- the model license is acceptable for the intended distribution shape.
