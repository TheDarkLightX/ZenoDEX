"""Original research workloads inspired by ZenoDEX's host-checked action flags.

These are proposal contracts, not replacements for mounted DEX business rules.
The chain and equality families are synthesis scaling controls.
"""

from __future__ import annotations

from .models import Contract, Requirement
from .terms import join, meet, negate, variable, xor


def coupled_recovery() -> Contract:
    paused, debit, credit = map(variable, ("paused", "debit", "credit"))
    return Contract("coupled_recovery", ("paused",), ("debit", "credit"), (
        Requirement("paused_forbids_debit", meet(paused, debit)),
        Requirement("paired_action_flags", xor(debit, credit)),
    ))


def conditional_cycle() -> Contract:
    mode, left, right = map(variable, ("mode", "left", "right"))
    return Contract("conditional_cycle", ("mode",), ("left", "right"), (
        Requirement("first", join(meet(negate(mode), left), meet(mode, negate(right)))),
        Requirement("second", join(meet(mode, left), meet(negate(mode), negate(right)))),
    ))


def action_permissions() -> Contract:
    """Liquidation proposal uses eight explicit host observations.

    This mirrors the shape of existing liquidation source-binding work, with
    an added mutually exclusive recovery action. Flags are observations only.
    """
    inputs = ("oracle_fresh", "maintenance_breach", "breaker_clear", "proof_valid",
              "binding_valid", "authorized", "position_open", "epoch_valid")
    controls = ("liquidate", "recover", "cancel")
    liquidate, recover, cancel = map(variable, controls)
    eligibility = meet(*(variable(name) for name in inputs))
    return Contract("action_permissions", inputs, controls, (
        Requirement("liquidation_eligibility", meet(liquidate, negate(eligibility))),
        Requirement("recovery_authorization", meet(recover, negate(variable("authorized")))),
        Requirement("exclusive_liquidation_recovery", meet(liquidate, recover)),
        Requirement("exclusive_cancel_liquidation", meet(cancel, liquidate)),
        Requirement("exclusive_cancel_recovery", meet(cancel, recover)),
    ))


def permission_chain(length: int = 8) -> Contract:
    """Proposal bit k requires bit k+1; this does not grant real permissions."""
    if type(length) is not int or not 1 <= length <= 64:
        raise ValueError("chain_length_domain")
    names = tuple(f"action{index:03d}" for index in range(length + 1))
    requirements = tuple(Requirement(
        f"requires{index:03d}", meet(variable(names[index]), negate(variable(names[index + 1]))),
    ) for index in range(length))
    return Contract("permission_chain", (), names, requirements)


def exclusion_pairs(length: int = 8) -> Contract:
    if type(length) is not int or not 1 <= length <= 64:
        raise ValueError("pair_count_domain")
    names = tuple(f"action{index:03d}" for index in range(2 * length))
    requirements = tuple(Requirement(
        f"exclusive{index:03d}", meet(variable(names[2 * index]), variable(names[2 * index + 1])),
    ) for index in range(length))
    return Contract("exclusion_pairs", (), names, requirements)


def changed_chain(contract: Contract) -> Contract:
    """One existing prerequisite becomes mutual, for incremental replay."""
    original = contract.requirements[-1]
    left, right = contract.controls[-2:]
    replacement = Requirement(original.name, join(
        original.residual, meet(variable(right), negate(variable(left))),
    ))
    return Contract(contract.name, contract.environment, contract.controls,
                    contract.requirements[:-1] + (replacement,))


def example(name: str, size: int = 8) -> Contract:
    if name == "coupled_recovery":
        return coupled_recovery()
    if name == "conditional_cycle":
        return conditional_cycle()
    if name == "action_permissions":
        return action_permissions()
    if name == "permission_chain":
        return permission_chain(size)
    if name == "exclusion_pairs":
        return exclusion_pairs(size)
    raise ValueError("unknown_example")
