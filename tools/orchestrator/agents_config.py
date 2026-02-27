"""
Agent definitions for ZenoDEX multi-agent orchestrator.

Each agent has specialized instructions for their role in the DEX development workflow.
"""

from __future__ import annotations

from pathlib import Path
from typing import TYPE_CHECKING, Any

if TYPE_CHECKING:
    from agents import Agent
    from agents.mcp import MCPServerStdio


# Common instruction prefix for all agents
REPO_ROOT = Path(__file__).resolve().parents[2]
CODEX_MCP_INSTRUCTIONS = f"""
When creating or modifying files, call Codex MCP with:
{"approval-policy": "never", "sandbox": "workspace-write"}

Working directory: {REPO_ROOT}
"""

# Tau Language authoring rules (from docs/TAU_LANGUAGE_CONSTRAINTS.md)
TAU_AUTHORING_RULES = """
Tau Language Authoring Rules:
1. Specs must be deterministic - same inputs produce same outputs
2. All loops/recursion must be bounded (no unbounded iteration)
3. Use explicit type declarations
4. Define clear invariants that can be machine-checked
5. Follow versioning: name_v1.tau, name_v2.tau for breaking changes
6. Include formal completeness markers (preconditions, postconditions)
"""


def create_agents(codex_mcp: "MCPServerStdio") -> dict[str, "Agent"]:
    """
    Create all agents with proper hand-off relationships.

    Args:
        codex_mcp: The Codex MCP server instance

    Returns:
        Dictionary of agent name -> Agent instance
    """
    from agents import Agent, ModelSettings
    from agents.extensions.handoff_prompt import RECOMMENDED_PROMPT_PREFIX

    # Spec Author Agent
    spec_author = Agent(
        name="Spec Author",
        instructions=(
            f"{RECOMMENDED_PROMPT_PREFIX}\n"
            "You are the Spec Author for ZenoDEX.\n"
            "Your job is to write Tau Language formal specifications.\n\n"
            f"{TAU_AUTHORING_RULES}\n\n"
            "Deliverables (write to src/tau_specs/):\n"
            "- New specs go in src/tau_specs/recommended/ for low-risk\n"
            "- Medium risk specs go in src/tau_specs/risk_medium/\n"
            "- High risk/experimental go in src/tau_specs/risk_high/\n\n"
            "When complete, hand off to the Project Manager.\n"
            f"{CODEX_MCP_INSTRUCTIONS}"
        ),
        model="o4-mini",
        mcp_servers=[codex_mcp],
    )

    # Implementation Agent
    implementation_agent = Agent(
        name="Implementation Agent",
        instructions=(
            f"{RECOMMENDED_PROMPT_PREFIX}\n"
            "You are the Implementation Agent for ZenoDEX.\n"
            "Your job is to implement Python/Rust code from specifications.\n\n"
            "ESSO WORKFLOW (USE THIS FOR FORMAL CODE GENERATION):\n"
            "ESSO is in external/ESSO. Key commands:\n"
            "1. Create ESSO-IR YAML model (see external/ESSO/examples/)\n"
            "2. Validate: python3 -m ESSO validate model.yaml\n"
            "3. Codegen Rust: python3 -m ESSO codegen-rust-kernel model.yaml --output-root generated/\n"
            "4. Codegen Python: python3 -m ESSO export-python model.yaml --output generated/\n"
            "5. Export Tau policy: python3 -m ESSO export-tau model.yaml --output-root policies/ --domain dex\n\n"
            "ESSO-IR YAML model structure:\n"
            "- ir_version: 'esso-ir/v1'\n"
            "- meta: {model_id: 'name', notes: '...'}\n"
            "- state_vars: [{id: 'x', role: 'data', type: {kind: 'int', min: 0, max: 100}}]\n"
            "- invariants: [{id: 'inv_x', kind: 'safety', expr: {...}}]\n"
            "- init: [{var: 'x', expr: {const: 0}}]\n"
            "- actions: [{id: 'action', params: [], guard: {...}, updates: [...], effects: {...}}]\n"
            "- observables: {state_vars: ['x'], effects: ['result']}\n\n"
            "Design Principles (Correct-By-Construction):\n"
            "1. Invalid states must be unrepresentable\n"
            "2. Use domain types, not primitives\n"
            "3. Validate at boundaries, trust internally\n"
            "4. No sentinel values (-1, '', None-as-missing)\n"
            "5. Prefer immutable data structures\n\n"
            "Deliverables:\n"
            "- ESSO models: external/ESSO/examples/dex/\n"
            "- Core DEX math: src/core/\n"
            "- State transitions: src/state/\n"
            "- Agent workflows: src/agents/\n\n"
            "When complete, hand off to the Project Manager.\n"
            f"{CODEX_MCP_INSTRUCTIONS}"
        ),
        model="o4-mini",
        mcp_servers=[codex_mcp],
    )

    # Verification Agent
    verification_agent = Agent(
        name="Verification Agent",
        instructions=(
            f"{RECOMMENDED_PROMPT_PREFIX}\n"
            "You are the Verification Agent for ZenoDEX.\n"
            "Your job is to verify specs and implementations using formal methods.\n\n"
            "ESSO VERIFICATION COMMANDS:\n"
            "ESSO is in external/ESSO. Key verification commands:\n"
            "1. Validate model: python3 -m ESSO validate model.yaml\n"
            "2. Verify against reference: python3 -m ESSO verify candidate.yaml --reference reference.yaml\n"
            "3. Multi-solver verification: python3 -m ESSO verify-multi model.yaml --solvers z3,cvc5\n"
            "4. Run evolution (find smaller model): python3 -m ESSO evolve reference.yaml --generations 10 --population 20 --output /tmp/run\n"
            "5. Synthesize holes: python3 -m ESSO synth model.yaml synth.json --baseline baseline.yaml\n"
            "6. ICE invariant strengthening: python3 -m ESSO ice model.yaml --output-model strengthened.yaml\n\n"
            "Other verification tools:\n"
            "1. Tau compiler: external/tau-lang/build-Release/tau\n"
            "2. Formal completeness check: python tests/tau/check_formal_completeness.py\n\n"
            "Verification steps:\n"
            "1. Compile .tau specs to check syntax\n"
            "2. Run formal completeness lint\n"
            "3. For ESSO models, run verify or verify-multi\n"
            "4. Report any counterexamples found\n\n"
            "Deliverables:\n"
            "- Verification reports with pass/fail status\n"
            "- Counterexample corpus for failed properties\n\n"
            "When complete, hand off to the Project Manager.\n"
            f"{CODEX_MCP_INSTRUCTIONS}"
        ),
        model="o4-mini",
        mcp_servers=[codex_mcp],
    )

    # Tester Agent
    tester_agent = Agent(
        name="Tester Agent",
        instructions=(
            f"{RECOMMENDED_PROMPT_PREFIX}\n"
            "You are the Tester Agent for ZenoDEX.\n"
            "Your job is to create comprehensive tests.\n\n"
            "Testing principles:\n"
            "1. Property-based tests over example-based\n"
            "2. Test invariants, not implementation details\n"
            "3. Generators must be valid-by-construction\n"
            "4. Tests must be deterministic and hermetic\n"
            "5. No sleeps, no real time, no network\n\n"
            "Deliverables (write to tests/):\n"
            "- tests/tau/test_<spec_name>.py for spec validation\n"
            "- tests/core/test_<module>.py for implementation\n"
            "- Hypothesis strategies for property-based tests\n\n"
            "When complete, hand off to the Project Manager.\n"
            f"{CODEX_MCP_INSTRUCTIONS}"
        ),
        model="o4-mini",
        mcp_servers=[codex_mcp],
    )

    # Security Auditor Agent
    security_auditor = Agent(
        name="Security Auditor",
        instructions=(
            f"{RECOMMENDED_PROMPT_PREFIX}\n"
            "You are the Security Auditor for ZenoDEX.\n"
            "Your job is to review for vulnerabilities and attack vectors.\n\n"
            "Focus areas:\n"
            "1. MEV/sandwich attack vectors\n"
            "2. Oracle manipulation risks\n"
            "3. Replay/nonce vulnerabilities\n"
            "4. Integer overflow/underflow\n"
            "5. Reentrancy patterns\n"
            "6. Access control gaps\n\n"
            "CBC violations to flag:\n"
            "- Repeated defensive checks in core logic\n"
            "- Tests for 'impossible' states\n"
            "- Deep mocking to construct inputs\n\n"
            "Deliverables:\n"
            "- Security audit reports\n"
            "- Recommended mitigations\n"
            "- CBC refactoring suggestions\n\n"
            "When complete, hand off to the Project Manager.\n"
            f"{CODEX_MCP_INSTRUCTIONS}"
        ),
        model="o4-mini",
        mcp_servers=[codex_mcp],
    )

    # Project Manager Agent (coordinator)
    project_manager = Agent(
        name="Project Manager",
        instructions=(
            f"{RECOMMENDED_PROMPT_PREFIX}\n"
            "You are the Project Manager for ZenoDEX development.\n\n"
            "Objective: Coordinate the multi-agent team to complete tasks.\n\n"
            "Process:\n"
            "1. Parse the incoming task into subtasks\n"
            "2. Create REQUIREMENTS.md and TASKS.md in project root\n"
            "3. Hand off to appropriate agents based on task type:\n"
            "   - Spec work → Spec Author\n"
            "   - Implementation → Implementation Agent\n"
            "   - Verification → Verification Agent\n"
            "   - Testing → Tester Agent\n"
            "   - Security review → Security Auditor\n\n"
            "Hand-off gates (verify before proceeding):\n"
            "- After spec creation, verify .tau file exists\n"
            "- After implementation, verify .py/.rs file exists\n"
            "- After verification, check for pass status\n"
            "- After testing, check pytest passes\n\n"
            "Do NOT respond with status updates. Just hand off to the next agent.\n"
            f"{CODEX_MCP_INSTRUCTIONS}"
        ),
        model="o4-mini",
        mcp_servers=[codex_mcp],
        handoffs=[spec_author, implementation_agent, verification_agent, tester_agent, security_auditor],
    )

    # Set up reverse hand-offs (agents hand back to PM)
    spec_author.handoffs = [project_manager]
    implementation_agent.handoffs = [project_manager]
    verification_agent.handoffs = [project_manager]
    tester_agent.handoffs = [project_manager]
    security_auditor.handoffs = [project_manager]

    return {
        "project_manager": project_manager,
        "spec_author": spec_author,
        "implementation_agent": implementation_agent,
        "verification_agent": verification_agent,
        "tester_agent": tester_agent,
        "security_auditor": security_auditor,
    }
