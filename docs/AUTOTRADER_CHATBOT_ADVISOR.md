# AutoTrader Chatbot Advisor

The AutoTrader chatbot advisor is a production-candidate advisory engine for
turning bounded user language into an AutoTrader proposal packet. It is an
interface and explanation layer over existing policy guards, KRR advice, and
ZenoEnergy/JEPA UX scoring.

## Boundary

```text
LanguageBridge(query) -> ParsedIntent
EBRM(ParsedIntent, features) -> AdvisoryProposal
KRR(strategy, state) -> CheckAdvice
LocalGuards(strategy, proposal) -> PolicyVerdict
```

The chatbot can produce an advisory proposal only. Execution still depends on
the deterministic AutoTrader policy and live admission paths.

```text
Executable(plan) -> DeterministicPolicyGateOK(plan)
```

The advisor sets all authority flags to false for the language bridge, EBRM
refiner, KRR layer, UX card, execution, signing, and ledger mutation.

## Components

- `src/agents/autotrader_chatbot_advisor.py` contains the engine.
- `src/agents/autotrader_llm_provider.py` contains local BYOM provider adapters
  and parse-hint validation.
- `tools/check_autotrader_chatbot_advisor.py` replays the promotion check.
- `tools/evaluate_autotrader_chatbot_providers.py` compares deterministic and
  local OpenAI-compatible providers on fixed safety and UX scenarios.
- `tools/check_autotrader_chatbot_provider_config.py` validates local provider
  config consent, local-only policy, and secret-handling before use.
- `tools/check_autotrader_chatbot_production_readiness.py` aggregates the
  advisor, provider-evaluation, config, latency/RSS, and authority checks.
- `config/autotrader_llm_provider.local.example.json` is the example local model
  provider config.
- `docs/AUTOTRADER_CHATBOT_MODEL_PROVIDERS.md` defines the model-provider policy.
- `tests/agents/test_autotrader_chatbot_agent_advisor.py` covers query parsing,
  EBRM refinement, local provider parsing, loopback OpenAI-compatible parsing,
  security blocking, guard blocking, authority flags, and import-boundary
  separation.
- `tests/agents/test_autotrader_chatbot_check_tool.py` covers the checker and
  CLI exit behavior.

## Hyper-Efficient Language Bridge

The current language bridge is a bounded local parser:

```text
llm_calls = 0
token_estimate = ceil(prompt_chars / 4)
prompt limits fail closed
```

This keeps natural-language UX available without putting a remote or heavyweight
LLM on the hot path. A future hosted LLM can propose parse hints, but the same
bounded schema, prompt budgets, security prefilter, and deterministic guards
must remain authoritative.

## Local BYOM LLM Providers

The advisor also supports a local bring-your-own-model provider path. The model
must run on a loopback endpoint or inside the same local process and may return
only this narrow parse-hint object:

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

Provider output is rejected if it contains authority fields such as `execute`,
`authorize`, `approve`, `sign`, `submit`, `guard_ok`, or `policy_ok`. Unknown
features, unknown controls, non-numeric feature values, and out-of-range feature
values also fail validation. On validation failure, the advisor keeps the
deterministic parser result and marks `provider_fallback_used=true`.

This shape lets demos compare LFM, Qwen, and a custom Zeno model through the same
adapter. ZenoDEX should not bundle restricted model weights. LFM-style models can
be supported as user-supplied local providers when the user has the right license
position. Apache-licensed local models can be wired through the same interface.
The long-term custom model should be a small semantic compiler for this schema,
trained on ZenoDEX intent examples and adversarial policy-boundary cases.

## EBRM To Human

The EBRM layer uses bounded future-tension control search over known AutoTrader
controls. It returns a trace with before/after future tension and hand-energy
deltas. The UX card turns that trace and policy verdict into a compact user
message, suggested controls, and KRR-prioritized checks.

## Promotion Check

Run:

```bash
python3 tools/check_autotrader_chatbot_advisor.py
```

The checker requires:

- a clean query produces a policy-valid advisory candidate;
- the language bridge uses zero LLM calls and stays within the token budget;
- EBRM refinement lowers future tension;
- local guards pass for the clean proposal;
- KRR advice is available;
- a valid local LLM parse hint remains advisory and passes schema validation;
- an invalid local LLM authority hint falls back to deterministic parsing;
- the prompt-injection case blocks before refinement;
- the unsafe no-refinement case reports unclipped order and slippage blockers;
- authoritative runtime paths do not import the chatbot advisor.

## Provider Evaluation

Run the deterministic baseline:

```bash
python3 tools/evaluate_autotrader_chatbot_providers.py
```

Run a user-supplied local OpenAI-compatible model:

```bash
python3 tools/evaluate_autotrader_chatbot_providers.py \
  --provider-label local-qwen \
  --local-openai-url http://127.0.0.1:11434/v1/chat/completions \
  --local-model qwen3.5:0.8b
```

The same command shape works for LFM or a custom Zeno model when the user runs
the model locally behind an OpenAI-compatible endpoint. The report compares
scenario pass/fail status, schema-valid provider outputs, fallback count, local
LLM call count, prompt-injection blocking, policy-guard blocking, latency
summary, process peak RSS, and authority violations. A configured local provider
evaluation fails if the endpoint is unavailable or every provider call falls
back. A provider may improve UX only if authority violations remain zero.

Validate a provider config:

```bash
python3 tools/check_autotrader_chatbot_provider_config.py \
  --config config/autotrader_llm_provider.local.example.json
```

Run the aggregate production-readiness check:

```bash
python3 tools/check_autotrader_chatbot_production_readiness.py \
  --provider-config config/autotrader_llm_provider.local.example.json
```

## Non-Claims

This engine does not execute trades, sign intents, custody funds, authorize
settlement, write state roots, or replace deterministic guards. The security
prefilter is a deterministic guardrail, not a complete prompt-injection proof.
Production UI rollout still needs client integration and user testing.
