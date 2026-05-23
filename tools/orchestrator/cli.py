"""
CLI for ZenoDEX Multi-Agent Orchestrator.

Usage:
    python -m tools.orchestrator.cli start
    python -m tools.orchestrator.cli run "Create nonce_manager_v1.tau spec"
"""

from __future__ import annotations

import argparse
import asyncio
import sys
from pathlib import Path


def main() -> int:
    """Main CLI entry point."""
    parser = argparse.ArgumentParser(
        prog="zenodex-orchestrator",
        description="ZenoDEX Multi-Agent Development Orchestrator",
    )
    subparsers = parser.add_subparsers(dest="command", help="Available commands")

    # 'run' command
    run_parser = subparsers.add_parser("run", help="Run a task through the agent workflow")
    run_parser.add_argument("task", type=str, help="Task description to execute")
    run_parser.add_argument(
        "--max-turns",
        type=int,
        default=30,
        help="Maximum agent turns (default: 30)",
    )

    # 'check' command
    check_parser = subparsers.add_parser("check", help="Check system dependencies")

    args = parser.parse_args()

    if args.command == "run":
        return run_task(args.task, args.max_turns)
    elif args.command == "check":
        return check_dependencies()
    else:
        parser.print_help()
        return 0


def run_task(task: str, max_turns: int) -> int:
    """Run a task through the orchestrator."""
    from .orchestrator import run_workflow

    print(f"🚀 Starting ZenoDEX Orchestrator")
    print(f"📋 Task: {task}")
    print(f"🔄 Max turns: {max_turns}")
    print("-" * 60)

    try:
        result = asyncio.run(run_workflow(task, max_turns))
        print("\n" + "=" * 60)
        print("✅ WORKFLOW COMPLETE")
        print("=" * 60)
        print(result)
        return 0
    except KeyboardInterrupt:
        print("\n⚠️ Workflow interrupted by user")
        return 130
    except Exception as e:
        print(f"\n❌ Workflow failed: {e}")
        return 1


def check_dependencies() -> int:
    """Check that all dependencies are available."""
    print("Checking ZenoDEX Orchestrator dependencies...\n")

    checks = []

    # Check Python packages
    try:
        import agents
        checks.append(("✅", "openai-agents", "installed"))
    except ImportError:
        checks.append((
            "❌",
            "openai-agents",
            "NOT INSTALLED - run: python3 -m pip install --require-hashes -r requirements-dev.lock.txt",
        ))

    try:
        import dotenv
        checks.append(("✅", "python-dotenv", "installed"))
    except ImportError:
        checks.append((
            "❌",
            "python-dotenv",
            "NOT INSTALLED - run: python3 -m pip install --require-hashes -r requirements-dev.lock.txt",
        ))

    # Check OPENAI_API_KEY
    import os
    if os.getenv("OPENAI_API_KEY"):
        checks.append(("✅", "OPENAI_API_KEY", "set"))
    else:
        checks.append(("❌", "OPENAI_API_KEY", "NOT SET - add to .env file"))

    # Check ESSO
    esso_path = Path(__file__).parent.parent.parent / "external" / "ESSO"
    if esso_path.exists():
        checks.append(("✅", "ESSO", f"found at {esso_path}"))
    else:
        checks.append(("❌", "ESSO", "NOT FOUND - run: git clone https://github.com/TheDarkLightX/ESSO.git external/ESSO"))

    # Check npx/codex
    import shutil
    if shutil.which("npx"):
        checks.append(("✅", "npx", "available"))
    else:
        checks.append(("❌", "npx", "NOT FOUND - install Node.js"))

    # Print results
    all_ok = True
    for status, name, message in checks:
        print(f"  {status} {name}: {message}")
        if status == "❌":
            all_ok = False

    print()
    if all_ok:
        print("✅ All dependencies satisfied!")
        return 0
    else:
        print("❌ Some dependencies missing. Please install them and try again.")
        return 1


if __name__ == "__main__":
    sys.exit(main())
