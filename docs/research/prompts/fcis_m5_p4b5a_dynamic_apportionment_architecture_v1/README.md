# FCIS M5-P4B5A dynamic apportionment architecture packet

**Status:** `SEMANTICALLY_APPROVED_FOR_RESEARCH`

**Checkpoint type:** review-only architecture research

**Runtime authority:** unchanged

This packet isolates the unresolved protocol-fee apportionment problem that
blocks P4B5A. It is designed for independent execution by multiple capable
agents using the same source-pinned contract and counterexamples.

Start with:

1. [PROBLEM_CONTRACT.md](PROBLEM_CONTRACT.md), the normative research
   contract.
2. [AGENT_PROMPT.md](AGENT_PROMPT.md), the self-contained prompt to give each
   agent.
3. [REVIEW_RUBRIC.md](REVIEW_RUBRIC.md), the common grading and automatic
   no-go rules.
4. [RESPONSE_TEMPLATE.md](RESPONSE_TEMPLATE.md), the requested result shape.
5. `CONTEXT_MANIFEST.json`, checked by `check_packet.py`.

## Current outcome

The architecture remains blocked:

```text
M5_P4B5A_BLOCKED_DYNAMIC_APPORTIONMENT
```

The retained composition boundary is:

```text
exact settlement replay
  -> controlled provisional protocol-fee values
  -> deterministic apportionment under an explicit policy lifecycle
  -> stable per-domain/per-asset apportionment state
  -> one net canonical balance patch
  -> one decision and atomic commit bundle
```

The unresolved choice is the apportionment machine and policy lifecycle. The
latest scalar-cursor proposal is valid only for fixed weights. It fails against
an adaptive policy authority.

## Baseline

```text
repository: TheDarkLightX/ZenoDEX
baseline source head: c4879d8a570ad0418ccb8778ab9ea401ad0c5aca
P4B5A ancestor: 6c4e7c6be89f76605e86c5532a4841d5e271611b
```

The baseline contains unmounted fee-accounting substrate. The local worktree
also contains contradictory uncommitted Python/Rust experiments. Those
experiments are excluded from this packet and carry no authority.

## How to give this to another agent

Give the agent the repository branch and this file:

```text
docs/research/prompts/
fcis_m5_p4b5a_dynamic_apportionment_architecture_v1/AGENT_PROMPT.md
```

Ask it to return one report following `RESPONSE_TEMPLATE.md`. Independent
agents should not see other agents' proposed answers before completing their
first pass.

Suggested output name:

```text
docs/research/
FCIS_M5_P4B5A_DYNAMIC_APPORTIONMENT_<AGENT>_REVIEW_20260728.md
```

## Replay

```bash
python3 \
  docs/research/FCIS_M5_P4B5A_APPORTIONMENT_COUNTEREXAMPLES_20260728.py

python3 \
  docs/research/FCIS_M5_P4B5A_DYNAMIC_APPORTIONMENT_COUNTEREXAMPLES_20260728.py

python3 \
  docs/research/prompts/fcis_m5_p4b5a_dynamic_apportionment_architecture_v1/check_packet.py
```

ESSO is optional for agents that have it installed. A missing ESSO, Lean, SMT,
or search tool must remain an explicit evidence gap.

## Authority

Agents may:

- inspect the pinned source and packet;
- search primary literature;
- write review-only models, proofs, and deterministic experiments;
- propose a packet amendment;
- return counterexamples and explicit no-go results.

Agents may not:

- edit or mount Python/Rust runtime authority;
- modify the frozen original packet or prior reviews;
- suppress a counterexample or weaken a law to obtain a pass;
- commit, push, merge, or change a PR unless separately authorized;
- claim production readiness from bounded or local evidence.
