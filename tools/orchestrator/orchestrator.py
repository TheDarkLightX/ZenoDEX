"""
ZenoDEX Multi-Agent Orchestrator

Orchestrates specialized agents via OpenAI Agents SDK with Codex as MCP server.
Agents collaborate to develop the DEX: specs, implementation, verification, testing.
"""

from __future__ import annotations

import asyncio
import os
from pathlib import Path
from typing import TYPE_CHECKING

from dotenv import load_dotenv

if TYPE_CHECKING:
    from agents.mcp import MCPServerStdio

# Load environment variables
load_dotenv(override=True)

# Project paths
PROJECT_ROOT = Path(__file__).parent.parent.parent
EXTERNAL_DIR = PROJECT_ROOT / "external"
ESSO_PATH = EXTERNAL_DIR / "ESSO"
TAU_SPECS_DIR = PROJECT_ROOT / "src" / "tau_specs"


async def create_codex_mcp_server() -> "MCPServerStdio":
    """Create and return the Codex MCP server context manager."""
    from agents.mcp import MCPServerStdio

    return MCPServerStdio(
        name="Codex CLI",
        params={
            "command": "npx",
            "args": ["-y", "codex", "mcp-server"],
        },
        client_session_timeout_seconds=360000,
    )


def get_api_key() -> str:
    """Get OpenAI API key from environment."""
    api_key = os.getenv("OPENAI_API_KEY")
    if not api_key:
        raise ValueError(
            "OPENAI_API_KEY not found. "
            "Set it in .env file or environment variable."
        )
    return api_key


async def run_workflow(task: str, max_turns: int = 30) -> str:
    """
    Run the multi-agent workflow for a given task.

    Args:
        task: The task description to execute
        max_turns: Maximum agent turns before stopping

    Returns:
        Final output from the workflow
    """
    from agents import Agent, ModelSettings, Runner, set_default_openai_api
    from agents.extensions.handoff_prompt import RECOMMENDED_PROMPT_PREFIX

    set_default_openai_api(get_api_key())

    async with await create_codex_mcp_server() as codex_mcp:
        # Import agent definitions
        from .agents_config import create_agents

        agents = create_agents(codex_mcp)

        # Run with Project Manager as entry point
        result = await Runner.run(
            agents["project_manager"],
            task,
            max_turns=max_turns,
        )

        return result.final_output


async def main() -> None:
    """Entry point for direct execution."""
    import sys

    if len(sys.argv) < 2:
        print("Usage: python -m tools.orchestrator.orchestrator <task>")
        print("Example: python -m tools.orchestrator.orchestrator 'Create nonce_manager_v1.tau'")
        sys.exit(1)

    task = " ".join(sys.argv[1:])
    print(f"Starting workflow for: {task}")

    result = await run_workflow(task)
    print("\n" + "=" * 60)
    print("WORKFLOW COMPLETE")
    print("=" * 60)
    print(result)


if __name__ == "__main__":
    asyncio.run(main())
