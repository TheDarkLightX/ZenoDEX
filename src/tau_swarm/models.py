"""Immutable advisory local-choice models over bounded Tau Boolean contracts.

These values describe local domains for people or model agents.  They do not
confer credentials, invoke a native engine, or authorize an external effect.
"""

from __future__ import annotations

import json
from collections.abc import Mapping
from dataclasses import dataclass
from hashlib import sha256

from src.tau_composition.models import Contract, RepairMap, Requirement
from src.tau_composition.resources import check_terms
from src.tau_composition.terms import Term, variable


def _choice_pairs(
    pairs: object, *, message: str, allow_empty: bool,
) -> tuple[tuple[str, bool], ...]:
    """Validate one canonical, bounded coordinate/value tuple."""

    if type(pairs) is not tuple or len(pairs) > 256 or (not allow_empty and not pairs):
        raise ValueError(message)
    names: list[str] = []
    for pair in pairs:
        if type(pair) is not tuple or len(pair) != 2:
            raise ValueError(message)
        name, value = pair
        try:
            variable(name)
        except ValueError as exc:
            raise ValueError(message) from exc
        if type(value) is not bool:
            raise ValueError("local_choice_value_bool")
        names.append(name)
    if len(set(names)) != len(names):
        raise ValueError(message)
    return pairs


@dataclass(frozen=True, slots=True)
class LocalChoice:
    """One uncredentialed, canonical local proposal for an envelope snapshot."""

    owner: str
    environment: tuple[tuple[str, bool], ...]
    controls: tuple[tuple[str, bool], ...]
    envelope_id: str

    def __post_init__(self) -> None:
        try:
            variable(self.owner)
        except ValueError as exc:
            raise ValueError("local_choice_owner") from exc
        _choice_pairs(self.environment, message="local_choice_environment", allow_empty=True)
        _choice_pairs(self.controls, message="local_choice_controls", allow_empty=False)
        if type(self.envelope_id) is not str:
            raise ValueError("local_choice_envelope_id")


@dataclass(frozen=True, slots=True)
class AgentBlock:
    """One named owner of a nonempty, immutable set of proposal controls."""

    name: str
    controls: tuple[str, ...]

    def __post_init__(self) -> None:
        variable(self.name)
        if type(self.controls) is not tuple or not 1 <= len(self.controls) <= 256:
            raise ValueError("agent_block_controls_required")
        for control in self.controls:
            variable(control)
        if len(set(self.controls)) != len(self.controls):
            raise ValueError("duplicate_agent_control")


@dataclass(frozen=True, slots=True)
class SwarmProblem:
    """A global Boolean contract partitioned into local advisory agent blocks."""

    contract: Contract
    blocks: tuple[AgentBlock, ...]
    anchor: RepairMap

    def __post_init__(self) -> None:
        if not isinstance(self.contract, Contract):
            raise ValueError("swarm_contract_required")
        if type(self.blocks) is not tuple:
            raise ValueError("swarm_blocks_required")
        if not 1 <= len(self.blocks) <= 16:
            raise ValueError("swarm_block_count")
        if any(not isinstance(block, AgentBlock) for block in self.blocks):
            raise ValueError("swarm_block_type")
        names = tuple(block.name for block in self.blocks)
        if len(set(names)) != len(names):
            raise ValueError("duplicate_agent_block")
        assigned = tuple(control for block in self.blocks for control in block.controls)
        if len(set(assigned)) != len(assigned):
            raise ValueError("block_control_overlap")
        if set(assigned) != set(self.contract.controls):
            raise ValueError("block_control_partition")
        if not isinstance(self.anchor, RepairMap):
            raise ValueError("swarm_anchor_required")
        if tuple(name for name, _term in self.anchor.assignments) != self.contract.controls:
            raise ValueError("anchor_control_coverage")
        environment = frozenset(self.contract.environment)
        for _name, term in self.anchor.assignments:
            if term.variables() - environment:
                raise ValueError("anchor_reads_non_environment")
        check_terms(tuple(term for _name, term in self.anchor.assignments))

    def block(self, name: str) -> AgentBlock:
        """Return one declared block or the stable unknown-block rejection."""

        if type(name) is not str:
            raise ValueError("unknown_agent_block")
        for block in self.blocks:
            if block.name == name:
                return block
        raise ValueError("unknown_agent_block")


@dataclass(frozen=True, slots=True)
class AgentDomain:
    """A local residual whose zero set is the agent's permitted choices."""

    block: AgentBlock
    residual: Term

    def __post_init__(self) -> None:
        if not isinstance(self.block, AgentBlock):
            raise ValueError("agent_domain_block_required")
        if not isinstance(self.residual, Term):
            raise ValueError("agent_domain_residual_required")
        check_terms((self.residual,))


@dataclass(frozen=True, slots=True)
class AutonomyEnvelope:
    """A checked local-domain view of one advisory global swarm problem."""

    problem: SwarmProblem
    domains: tuple[AgentDomain, ...]
    expansion_order: tuple[str, ...]
    native_queries: int
    binary_sha256: str

    def __post_init__(self) -> None:
        if not isinstance(self.problem, SwarmProblem):
            raise ValueError("swarm_problem_required")
        if type(self.domains) is not tuple or len(self.domains) != len(self.problem.blocks):
            raise ValueError("ordered_agent_domains_required")
        if any(not isinstance(domain, AgentDomain) for domain in self.domains):
            raise ValueError("ordered_agent_domains_required")
        if tuple(domain.block for domain in self.domains) != self.problem.blocks:
            raise ValueError("ordered_agent_domains_required")
        environment = frozenset(self.problem.contract.environment)
        for domain in self.domains:
            allowed = environment | frozenset(domain.block.controls)
            if domain.residual.variables() - allowed:
                raise ValueError("domain_scope_leak")
        if type(self.expansion_order) is not tuple or any(
            type(name) is not str for name in self.expansion_order
        ):
            raise ValueError("expansion_order_permutation")
        names = tuple(block.name for block in self.problem.blocks)
        if len(self.expansion_order) != len(names) or set(self.expansion_order) != set(names):
            raise ValueError("expansion_order_permutation")
        if type(self.native_queries) is not int or self.native_queries < 0:
            raise ValueError("native_query_count")
        if type(self.binary_sha256) is not str:
            raise ValueError("binary_sha256_type")

    @property
    def subject_id(self) -> str:
        """Hash the semantic snapshot, excluding runtime-specific evidence counts."""

        contract = self.problem.contract
        payload = {
            "anchor": [
                {"name": name, "term": term.canonical_data()}
                for name, term in self.problem.anchor.assignments
            ],
            "blocks": [
                {"name": block.name, "controls": list(block.controls)}
                for block in self.problem.blocks
            ],
            "contract": {
                "name": contract.name,
                "environment": list(contract.environment),
                "controls": list(contract.controls),
                "requirements": [
                    {"name": requirement.name, "residual": requirement.residual.canonical_data()}
                    for requirement in contract.requirements
                ],
            },
            "domains": [
                {
                    "owner": domain.block.name,
                    "controls": list(domain.block.controls),
                    "residual": domain.residual.canonical_data(),
                }
                for domain in self.domains
            ],
            "expansion_order": list(self.expansion_order),
        }
        encoded = json.dumps(
            payload, sort_keys=True, separators=(",", ":"), ensure_ascii=True,
        ).encode("utf-8")
        return sha256(encoded).hexdigest()

    def _domain(self, name: str) -> AgentDomain:
        block = self.problem.block(name)
        for domain in self.domains:
            if domain.block == block:
                return domain
        raise RuntimeError("validated envelope lost an agent domain")

    def local_contract(self, name: str) -> Contract:
        """Return the zero-equation contract for one block and its environment."""

        domain = self._domain(name)
        index = self.domains.index(domain)
        return Contract(
            f"domain{index}",
            self.problem.contract.environment,
            domain.block.controls,
            (Requirement("zero", domain.residual),),
        )

    def permits(self, name: str, values: Mapping[str, bool]) -> bool:
        """Check exact environment-plus-local values against one local zero set."""

        if not isinstance(values, Mapping):
            raise ValueError("coordinate_values_required")
        return self.local_contract(name).satisfied(values)

    def choose(self, agent: str, values: Mapping[str, bool]) -> LocalChoice:
        """Bind one permitted local proposal to this exact envelope snapshot."""

        domain = self._domain(agent)
        if not self.permits(agent, values):
            raise ValueError("outside_agent_domain")
        return LocalChoice(
            owner=domain.block.name,
            environment=tuple(
                (name, values[name]) for name in self.problem.contract.environment
            ),
            controls=tuple((name, values[name]) for name in domain.block.controls),
            envelope_id=self.subject_id,
        )

    def combine_choices(self, choices: tuple[LocalChoice, ...]) -> dict[str, bool]:
        """Recheck ordered local proposals before returning one global advisory bundle."""

        if type(choices) is not tuple or len(choices) != len(self.problem.blocks):
            raise ValueError("ordered_local_choices_required")
        if any(not isinstance(choice, LocalChoice) for choice in choices):
            raise ValueError("ordered_local_choices_required")
        expected_id = self.subject_id
        expected_owners = tuple(block.name for block in self.problem.blocks)
        if tuple(choice.owner for choice in choices) != expected_owners:
            raise ValueError("choice_owner_order")
        if any(choice.envelope_id != expected_id for choice in choices):
            raise ValueError("choice_subject_mismatch")
        environment_names = self.problem.contract.environment
        expected_environment: tuple[tuple[str, bool], ...] | None = None
        candidate: dict[str, bool] = {}
        for block, choice in zip(self.problem.blocks, choices, strict=True):
            environment = _choice_pairs(
                choice.environment, message="local_choice_environment", allow_empty=True,
            )
            controls = _choice_pairs(
                choice.controls, message="local_choice_controls", allow_empty=False,
            )
            if tuple(name for name, _value in environment) != environment_names:
                raise ValueError("choice_environment_mismatch")
            if tuple(name for name, _value in controls) != block.controls:
                raise ValueError("choice_controls_mismatch")
            if expected_environment is None:
                expected_environment = environment
                candidate.update(environment)
            elif environment != expected_environment:
                raise ValueError("choice_environment_mismatch")
            candidate.update(controls)
        for block, choice in zip(self.problem.blocks, choices, strict=True):
            local_values = dict(choice.environment)
            local_values.update(choice.controls)
            if not self.permits(block.name, local_values):
                raise ValueError("outside_agent_domain")
        return self.check_bundle(candidate)

    def check_bundle(self, values: Mapping[str, bool]) -> dict[str, bool]:
        """Return an advisory copy after local-domain and global-contract checks."""

        if not isinstance(values, Mapping):
            raise ValueError("coordinate_values_required")
        self.problem.contract.validate_values(values)
        candidate = dict(values)
        environment = self.problem.contract.environment
        for domain in self.domains:
            local_values = {
                coordinate: candidate[coordinate]
                for coordinate in environment + domain.block.controls
            }
            if not self.permits(domain.block.name, local_values):
                raise ValueError("outside_agent_domain")
        if not self.problem.contract.satisfied(candidate):
            raise ValueError("global_contract_rejected")
        return candidate
