"""Immutable advisory models for locally autonomous Tau Boolean choice spaces."""

from .examples import asymmetric_choices, balanced_anchor, planning_swarm, triangle_choices
from .models import AgentBlock, AgentDomain, AutonomyEnvelope, LocalChoice, SwarmProblem

__all__ = [
    "AgentBlock",
    "AgentDomain",
    "AutonomyEnvelope",
    "LocalChoice",
    "SwarmProblem",
    "asymmetric_choices",
    "balanced_anchor",
    "planning_swarm",
    "triangle_choices",
]
