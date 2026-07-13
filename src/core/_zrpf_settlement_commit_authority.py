"""Private authority boundary for the experimental ZRPF settlement kernel.

The current Semantic Epoch V2 receipt does not commit to the exact
``SettlementEffectPlanV1`` commitment or its action, authorization, cell,
message, carry, and reward roots.  Consequently this module cannot mint
production settlement authority.  It provides a sealed test-only input for
exercising the durable transaction mechanics while preserving that non-claim.
"""

from __future__ import annotations

from typing import NoReturn, final

from .recursive_stark_admission import _AuthenticatedRecursiveStarkRootFacts
from .zrpf_settlement_effect_plan import SettlementEffectPlanV1

SETTLEMENT_AUTHORITY_BLOCKED_REASON_V1 = "semantic_v2_missing_exact_settlement_effect_plan_binding"

_AUTHENTICATED_SETTLEMENT_COMMIT_SEAL_V1 = object()


class SettlementSemanticBindingUnavailableV1(RuntimeError):
    """Stable rejection while the receipt lacks the exact plan-binding ABI."""

    code = SETTLEMENT_AUTHORITY_BLOCKED_REASON_V1


@final
class _AuthenticatedSettlementCommitV1:
    """Sealed input to the atomicity-only settlement transaction kernel.

    The value proves only that its recursive-root marker has the existing
    private seal and that plan fields which are already comparable agree.  Its
    ``settlement_authority`` property is permanently false in V1.

    Python module privacy is not a hostile same-interpreter security boundary.
    Repository architecture tests therefore restrict private seal and
    constructor use to the dedicated transaction test module. No production
    adapter currently constructs this type.
    """

    __slots__ = ("_authenticated_root", "_plan", "_seal")
    _authenticated_root: _AuthenticatedRecursiveStarkRootFacts
    _plan: SettlementEffectPlanV1
    _seal: object

    def __init__(
        self,
        authenticated_root: _AuthenticatedRecursiveStarkRootFacts,
        plan: SettlementEffectPlanV1,
        *,
        seal: object,
    ) -> None:
        if seal is not _AUTHENTICATED_SETTLEMENT_COMMIT_SEAL_V1:
            raise TypeError("authenticated settlement commit requires the private seal")
        _validate_test_binding(authenticated_root, plan)
        object.__setattr__(self, "_authenticated_root", authenticated_root)
        object.__setattr__(self, "_plan", plan)
        object.__setattr__(self, "_seal", seal)

    def __init_subclass__(cls, **_kwargs: object) -> NoReturn:
        raise TypeError("authenticated settlement commit cannot be subclassed")

    def __setattr__(self, _name: str, _value: object) -> NoReturn:
        raise AttributeError("authenticated settlement commit is immutable")

    def __copy__(self) -> NoReturn:
        raise TypeError("authenticated settlement commit cannot be copied")

    def __deepcopy__(self, _memo: object) -> NoReturn:
        raise TypeError("authenticated settlement commit cannot be copied")

    def __reduce__(self) -> NoReturn:
        raise TypeError("authenticated settlement commit cannot be serialized")

    @property
    def authenticated_root(self) -> _AuthenticatedRecursiveStarkRootFacts:
        return self._authenticated_root

    @property
    def plan(self) -> SettlementEffectPlanV1:
        return self._plan

    @property
    def settlement_authority(self) -> bool:
        return False

    @property
    def authority_blocked_reason(self) -> str:
        return SETTLEMENT_AUTHORITY_BLOCKED_REASON_V1

    def _has_private_seal(self) -> bool:
        try:
            return (
                object.__getattribute__(self, "_seal") is _AUTHENTICATED_SETTLEMENT_COMMIT_SEAL_V1
            )
        except AttributeError:
            return False


def _bind_authenticated_settlement_commit_v1(
    _authenticated_root: _AuthenticatedRecursiveStarkRootFacts,
    _plan: SettlementEffectPlanV1,
) -> NoReturn:
    """Fail closed until Semantic V2 authenticates the exact plan surface."""

    raise SettlementSemanticBindingUnavailableV1(SETTLEMENT_AUTHORITY_BLOCKED_REASON_V1)


def _validate_test_binding(
    authenticated_root: _AuthenticatedRecursiveStarkRootFacts,
    plan: SettlementEffectPlanV1,
) -> None:
    if type(authenticated_root) is not _AuthenticatedRecursiveStarkRootFacts:
        raise TypeError("authenticated_root must be _AuthenticatedRecursiveStarkRootFacts")
    if not authenticated_root._has_private_seal():
        raise TypeError("authenticated_root lacks the private seal")
    if type(plan) is not SettlementEffectPlanV1:
        raise TypeError("plan must be exactly SettlementEffectPlanV1")
    facts = authenticated_root.facts
    if plan.source_root_journal_hash != facts.root_journal_hash:
        raise ValueError("plan source root does not match authenticated root")
    if plan.epoch_id != facts.epoch_id:
        raise ValueError("plan epoch does not match authenticated root")
    if plan.public_policy_hash != facts.public_policy_hash:
        raise ValueError("plan public policy does not match authenticated root")
    plan_messages = tuple(row.message_id for row in plan.message_effects)
    if plan_messages != facts.cross_shard_message_ids:
        raise ValueError("plan message IDs do not match authenticated root")
