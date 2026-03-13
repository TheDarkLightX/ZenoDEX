"""ZenoDEX Multi-Agent Orchestrator package.

Keep package import lightweight so `python -m tools.orchestrator.cli check`
can report missing optional dependencies instead of crashing at import time.
"""

__all__ = ["run_workflow", "create_agents"]


def run_workflow(*args, **kwargs):
    """Lazily import the workflow runner."""
    from .orchestrator import run_workflow as _run_workflow

    return _run_workflow(*args, **kwargs)


def create_agents(*args, **kwargs):
    """Lazily import agent factory."""
    from .agents_config import create_agents as _create_agents

    return _create_agents(*args, **kwargs)
