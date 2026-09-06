"""Independent integer reference vectors for four bounded Tau policy probes.

The vectors are fixed offline qualification data.  They model only the unsigned
``bv[32]`` and ``sbf`` equations in the named Tau sources; this module neither
parses nor invokes Tau, a witness builder, or a runtime policy adapter.

``NonceManagerHistory`` records simulate caller-maintained nonce state.  They
cannot authenticate a caller, persist a nonce, authorize value movement, or
establish a production or refinement claim.
"""

from __future__ import annotations

from dataclasses import dataclass
from types import MappingProxyType
from typing import Callable, Final, Literal, Mapping, TypeAlias

UINT32_MAX: Final = 0xFFFFFFFF

SpecId: TypeAlias = Literal[
    "nonce_replay_guard_v1",
    "nonce_manager_v1",
    "transfer_hook_guard_v1",
    "zusd_transfer_guard_v1",
]
InputKind: TypeAlias = Literal["u32", "sbf"]
Evaluator: TypeAlias = Callable[[tuple[int, ...]], tuple[int, ...]]

SPEC_IDS: Final[tuple[SpecId, ...]] = (
    "nonce_replay_guard_v1",
    "nonce_manager_v1",
    "transfer_hook_guard_v1",
    "zusd_transfer_guard_v1",
)


@dataclass(frozen=True, slots=True)
class _InputRule:
    """One closed-domain input position for a reference spec."""

    name: str
    kind: InputKind


@dataclass(frozen=True, slots=True)
class QualificationCase:
    """One fixed input row and its complete immutable expected output vector.

    Cases are either manually listed witnesses or members of the separately
    generated exhaustive binary zUSD partition.
    """

    name: str
    spec_id: SpecId
    inputs: tuple[int, ...]
    expected_outputs: tuple[int, ...]

    def __post_init__(self) -> None:
        if not isinstance(self.name, str) or not self.name:
            raise ValueError("case name must be a nonempty string")
        _validate_inputs(self.spec_id, self.inputs)
        _validate_outputs(self.spec_id, self.expected_outputs)


@dataclass(frozen=True, slots=True)
class NonceManagerHistory:
    """A non-authoritative caller-state simulation with at most eight rows.

    Every row supplies the caller's current ``last_nonce`` in input position
    one.  A test harness advances that local value only after an accepted row.
    This data cannot authenticate a caller or update a persistent nonce store.
    """

    name: str
    initial_last_nonce: int
    final_last_nonce: int
    cases: tuple[QualificationCase, ...]

    def __post_init__(self) -> None:
        if not isinstance(self.name, str) or not self.name:
            raise ValueError("history name must be a nonempty string")
        _require_u32("initial_last_nonce", self.initial_last_nonce)
        _require_u32("final_last_nonce", self.final_last_nonce)
        if type(self.cases) is not tuple:
            raise TypeError("history cases must be a tuple")
        if not self.cases or len(self.cases) > 8:
            raise ValueError("history cases must contain one through eight rows")
        if any(type(case) is not QualificationCase for case in self.cases):
            raise TypeError("history cases must contain exact QualificationCase values")
        if any(case.spec_id != "nonce_manager_v1" for case in self.cases):
            raise ValueError("nonce-manager histories may contain only nonce_manager_v1 rows")


_INPUT_RULES: Final[Mapping[str, tuple[_InputRule, ...]]] = MappingProxyType(
    {
        "nonce_replay_guard_v1": (
            _InputRule("intent_nonce", "u32"),
            _InputRule("last_used_nonce", "u32"),
            _InputRule("expected_nonce", "u32"),
        ),
        "nonce_manager_v1": (
            _InputRule("nonce", "u32"),
            _InputRule("last_nonce", "u32"),
        ),
        "transfer_hook_guard_v1": (
            _InputRule("sender_balance_before", "u32"),
            _InputRule("sender_balance_after", "u32"),
            _InputRule("receiver_balance_before", "u32"),
            _InputRule("receiver_balance_after", "u32"),
            _InputRule("transfer_amount", "u32"),
            _InputRule("hook_approved", "sbf"),
        ),
        "zusd_transfer_guard_v1": (
            _InputRule("amount_positive", "sbf"),
            _InputRule("sender_has_balance", "sbf"),
            _InputRule("transfer_deltas_match", "sbf"),
            _InputRule("sender_auth_ok", "sbf"),
            _InputRule("recipient_valid", "sbf"),
            _InputRule("paused", "sbf"),
        ),
    }
)

_OUTPUT_WIDTHS: Final[Mapping[str, int]] = MappingProxyType(
    {
        "nonce_replay_guard_v1": 4,
        "nonce_manager_v1": 1,
        "transfer_hook_guard_v1": 4,
        "zusd_transfer_guard_v1": 4,
    }
)


def _require_int(field_name: str, value: object) -> int:
    if not isinstance(value, int) or isinstance(value, bool):
        raise TypeError(f"{field_name} must be an integer and not a boolean")
    return value


def _require_u32(field_name: str, value: object) -> int:
    integer = _require_int(field_name, value)
    if integer < 0 or integer > UINT32_MAX:
        raise ValueError(f"{field_name} must be in unsigned 32-bit range")
    return integer


def _require_sbf(field_name: str, value: object) -> int:
    integer = _require_int(field_name, value)
    if integer not in (0, 1):
        raise ValueError(f"{field_name} must be an sbf value of zero or one")
    return integer


def _validate_spec_id(spec_id: object) -> None:
    if not isinstance(spec_id, str):
        raise TypeError("spec_id must be a string")
    if spec_id not in SPEC_IDS:
        raise ValueError(f"unsupported reference spec: {spec_id!r}")


def _validate_inputs(spec_id: str, inputs: tuple[int, ...]) -> None:
    _validate_spec_id(spec_id)
    if type(inputs) is not tuple:
        raise TypeError("inputs must be an immutable tuple")
    rules = _INPUT_RULES[spec_id]
    if len(inputs) != len(rules):
        raise ValueError(f"{spec_id} requires exactly {len(rules)} inputs")
    for rule, value in zip(rules, inputs, strict=True):
        if rule.kind == "u32":
            _require_u32(rule.name, value)
        else:
            _require_sbf(rule.name, value)


def _validate_outputs(spec_id: str, outputs: tuple[int, ...]) -> None:
    _validate_spec_id(spec_id)
    if type(outputs) is not tuple:
        raise TypeError("expected_outputs must be an immutable tuple")
    output_width = _OUTPUT_WIDTHS[spec_id]
    if len(outputs) != output_width:
        raise ValueError(f"{spec_id} requires exactly {output_width} outputs")
    for index, value in enumerate(outputs):
        _require_sbf(f"expected_outputs[{index}]", value)


def _u32_add(left: int, right: int) -> int:
    return (left + right) & UINT32_MAX


def _u32_sub(left: int, right: int) -> int:
    return (left - right) & UINT32_MAX


def _evaluate_nonce_replay_guard(inputs: tuple[int, ...]) -> tuple[int, ...]:
    intent_nonce, last_used_nonce, expected_nonce = inputs
    params_ok = expected_nonce == _u32_add(last_used_nonce, 1)
    nonce_fresh = intent_nonce > last_used_nonce
    nonce_sequential = intent_nonce == expected_nonce
    nonce_replay_ok = params_ok and nonce_fresh and nonce_sequential
    return (
        int(params_ok),
        int(nonce_fresh),
        int(nonce_sequential),
        int(nonce_replay_ok),
    )


def _evaluate_nonce_manager(inputs: tuple[int, ...]) -> tuple[int, ...]:
    nonce, last_nonce = inputs
    no_overflow = last_nonce != UINT32_MAX
    nonce_monotonic = nonce > last_nonce
    nonce_gap_bounded = _u32_sub(nonce, last_nonce) <= 1000
    return (int(no_overflow and nonce_monotonic and nonce_gap_bounded),)


def _evaluate_transfer_hook_guard(inputs: tuple[int, ...]) -> tuple[int, ...]:
    (
        sender_balance_before,
        sender_balance_after,
        receiver_balance_before,
        receiver_balance_after,
        transfer_amount,
        hook_approved,
    ) = inputs
    balances_ok = (
        sender_balance_before >= sender_balance_after
        and receiver_balance_after >= receiver_balance_before
    )
    sender_ok = _u32_sub(sender_balance_before, sender_balance_after) == transfer_amount
    receiver_ok = _u32_sub(receiver_balance_after, receiver_balance_before) == transfer_amount
    sums_match = _u32_add(sender_balance_before, receiver_balance_before) == _u32_add(
        sender_balance_after, receiver_balance_after
    )
    # o2 is the source's combined delta-and-modular-conservation output.
    conservation_ok = sender_ok and receiver_ok and sums_match
    hook_ok = hook_approved == 1
    transfer_hook_ok = balances_ok and conservation_ok and hook_ok
    return (
        int(balances_ok),
        int(conservation_ok),
        int(hook_ok),
        int(transfer_hook_ok),
    )


def _evaluate_zusd_transfer_guard(inputs: tuple[int, ...]) -> tuple[int, ...]:
    (
        amount_positive,
        sender_has_balance,
        transfer_deltas_match,
        sender_auth_ok,
        recipient_valid,
        paused,
    ) = inputs
    structural_ok = amount_positive == 1 and sender_has_balance == 1 and transfer_deltas_match == 1
    policy_ok = sender_auth_ok == 1 and recipient_valid == 1 and paused == 0
    transfer_ok = structural_ok and policy_ok
    return (int(structural_ok), int(policy_ok), int(transfer_ok), int(transfer_ok))


_EVALUATORS: Final[Mapping[str, Evaluator]] = MappingProxyType(
    {
        "nonce_replay_guard_v1": _evaluate_nonce_replay_guard,
        "nonce_manager_v1": _evaluate_nonce_manager,
        "transfer_hook_guard_v1": _evaluate_transfer_hook_guard,
        "zusd_transfer_guard_v1": _evaluate_zusd_transfer_guard,
    }
)


def evaluate(spec_id: str, inputs: tuple[int, ...]) -> tuple[int, ...]:
    """Evaluate one exact, validated Tau-equation input row without Tau runtime I/O."""

    _validate_inputs(spec_id, inputs)
    return _EVALUATORS[spec_id](inputs)


_FIXED_CORPUS: Final[tuple[QualificationCase, ...]] = (
    QualificationCase(
        "nonce_replay_initial_accept",
        "nonce_replay_guard_v1",
        (1, 0, 1),
        (1, 1, 1, 1),
    ),
    QualificationCase(
        "nonce_replay_stale_caller_state_reaccepts_pointwise",
        "nonce_replay_guard_v1",
        (1, 0, 1),
        (1, 1, 1, 1),
    ),
    QualificationCase(
        "nonce_replay_zero_rejected",
        "nonce_replay_guard_v1",
        (0, 0, 1),
        (1, 0, 0, 0),
    ),
    QualificationCase(
        "nonce_replay_all_predicates_fail",
        "nonce_replay_guard_v1",
        (0, 0, 2),
        (0, 0, 0, 0),
    ),
    QualificationCase(
        "nonce_replay_expected_mismatch_with_same_nonce",
        "nonce_replay_guard_v1",
        (0, 0, 0),
        (0, 0, 1, 0),
    ),
    QualificationCase(
        "nonce_replay_fresh_wrong_expected",
        "nonce_replay_guard_v1",
        (1, 0, 0),
        (0, 1, 0, 0),
    ),
    QualificationCase(
        "nonce_replay_fresh_not_sequential",
        "nonce_replay_guard_v1",
        (2, 0, 1),
        (1, 1, 0, 0),
    ),
    QualificationCase(
        "nonce_replay_fresh_sequential_but_params_fail",
        "nonce_replay_guard_v1",
        (2, 0, 2),
        (0, 1, 1, 0),
    ),
    QualificationCase(
        "nonce_replay_wrap_params_and_sequence_not_fresh",
        "nonce_replay_guard_v1",
        (0, UINT32_MAX, 0),
        (1, 0, 1, 0),
    ),
    QualificationCase(
        "nonce_replay_max_neighbor_accept",
        "nonce_replay_guard_v1",
        (UINT32_MAX, UINT32_MAX - 1, UINT32_MAX),
        (1, 1, 1, 1),
    ),
    QualificationCase(
        "nonce_replay_unsigned_signed_seam_accept",
        "nonce_replay_guard_v1",
        (0x80000000, 0x7FFFFFFF, 0x80000000),
        (1, 1, 1, 1),
    ),
    QualificationCase(
        "nonce_manager_zero_replay",
        "nonce_manager_v1",
        (0, 0),
        (0,),
    ),
    QualificationCase(
        "nonce_manager_gap_999_accept",
        "nonce_manager_v1",
        (999, 0),
        (1,),
    ),
    QualificationCase(
        "nonce_manager_unsigned_signed_seam_accept",
        "nonce_manager_v1",
        (0x80000000, 0x7FFFFFFF),
        (1,),
    ),
    QualificationCase(
        "nonce_manager_history_replay_then_later_valid_step_1",
        "nonce_manager_v1",
        (1, 0),
        (1,),
    ),
    QualificationCase(
        "nonce_manager_history_replay_then_later_valid_step_2_replay",
        "nonce_manager_v1",
        (1, 1),
        (0,),
    ),
    QualificationCase(
        "nonce_manager_history_replay_then_later_valid_step_3_later_valid",
        "nonce_manager_v1",
        (2, 1),
        (1,),
    ),
    QualificationCase(
        "nonce_manager_history_gap_boundary_step_1_gap_1000",
        "nonce_manager_v1",
        (1000, 0),
        (1,),
    ),
    QualificationCase(
        "nonce_manager_history_gap_boundary_step_2_gap_1001_rejected",
        "nonce_manager_v1",
        (2001, 1000),
        (0,),
    ),
    QualificationCase(
        "nonce_manager_history_gap_boundary_step_3_later_gap_1000",
        "nonce_manager_v1",
        (2000, 1000),
        (1,),
    ),
    QualificationCase(
        "nonce_manager_history_exhaustion_step_1_accept_max",
        "nonce_manager_v1",
        (UINT32_MAX, UINT32_MAX - 1),
        (1,),
    ),
    QualificationCase(
        "nonce_manager_history_exhaustion_step_2_wrap_rejected",
        "nonce_manager_v1",
        (0, UINT32_MAX),
        (0,),
    ),
    QualificationCase(
        "nonce_manager_history_exhaustion_step_3_replay_rejected",
        "nonce_manager_v1",
        (UINT32_MAX, UINT32_MAX),
        (0,),
    ),
    QualificationCase(
        "transfer_hook_zero_amount_dust_allowed",
        "transfer_hook_guard_v1",
        (0, 0, 0, 0, 0, 1),
        (1, 1, 1, 1),
    ),
    QualificationCase(
        "transfer_hook_valid_one_atom",
        "transfer_hook_guard_v1",
        (10, 9, 3, 4, 1, 1),
        (1, 1, 1, 1),
    ),
    QualificationCase(
        "transfer_hook_conserved_but_wrong_deltas",
        "transfer_hook_guard_v1",
        (10, 9, 4, 5, 2, 1),
        (1, 0, 1, 0),
    ),
    QualificationCase(
        "transfer_hook_conserved_wrong_deltas_rejected_hook",
        "transfer_hook_guard_v1",
        (10, 9, 4, 5, 2, 0),
        (1, 0, 0, 0),
    ),
    QualificationCase(
        "transfer_hook_rejected_hook",
        "transfer_hook_guard_v1",
        (10, 9, 3, 4, 1, 0),
        (1, 1, 0, 0),
    ),
    QualificationCase(
        "transfer_hook_modular_sum_wrap_with_valid_deltas",
        "transfer_hook_guard_v1",
        (UINT32_MAX, UINT32_MAX - 1, 1, 2, 1, 1),
        (1, 1, 1, 1),
    ),
    QualificationCase(
        "transfer_hook_sender_underflow_keeps_o2_true",
        "transfer_hook_guard_v1",
        (0, UINT32_MAX, 10, 11, 1, 1),
        (0, 1, 1, 0),
    ),
    QualificationCase(
        "transfer_hook_sender_underflow_rejected_hook",
        "transfer_hook_guard_v1",
        (0, UINT32_MAX, 10, 11, 1, 0),
        (0, 1, 0, 0),
    ),
    QualificationCase(
        "transfer_hook_receiver_wrap_keeps_o2_true",
        "transfer_hook_guard_v1",
        (10, 9, UINT32_MAX, 0, 1, 1),
        (0, 1, 1, 0),
    ),
    QualificationCase(
        "transfer_hook_direction_and_delta_fail_approved",
        "transfer_hook_guard_v1",
        (0, 1, 0, 0, 1, 1),
        (0, 0, 1, 0),
    ),
    QualificationCase(
        "transfer_hook_direction_and_delta_fail_rejected_hook",
        "transfer_hook_guard_v1",
        (0, 1, 0, 0, 1, 0),
        (0, 0, 0, 0),
    ),
    QualificationCase(
        "zusd_transfer_allowed",
        "zusd_transfer_guard_v1",
        (1, 1, 1, 1, 1, 0),
        (1, 1, 1, 1),
    ),
    QualificationCase(
        "zusd_transfer_zero_amount_flag",
        "zusd_transfer_guard_v1",
        (0, 1, 1, 1, 1, 0),
        (0, 1, 0, 0),
    ),
    QualificationCase(
        "zusd_transfer_missing_balance",
        "zusd_transfer_guard_v1",
        (1, 0, 1, 1, 1, 0),
        (0, 1, 0, 0),
    ),
    QualificationCase(
        "zusd_transfer_delta_mismatch",
        "zusd_transfer_guard_v1",
        (1, 1, 0, 1, 1, 0),
        (0, 1, 0, 0),
    ),
    QualificationCase(
        "zusd_transfer_unauthorized",
        "zusd_transfer_guard_v1",
        (1, 1, 1, 0, 1, 0),
        (1, 0, 0, 0),
    ),
    QualificationCase(
        "zusd_transfer_invalid_recipient",
        "zusd_transfer_guard_v1",
        (1, 1, 1, 1, 0, 0),
        (1, 0, 0, 0),
    ),
    QualificationCase(
        "zusd_transfer_paused",
        "zusd_transfer_guard_v1",
        (1, 1, 1, 1, 1, 1),
        (1, 0, 0, 0),
    ),
    QualificationCase(
        "zusd_transfer_pause_then_unpause_paused",
        "zusd_transfer_guard_v1",
        (1, 1, 1, 1, 1, 1),
        (1, 0, 0, 0),
    ),
    QualificationCase(
        "zusd_transfer_pause_then_unpause_unpaused",
        "zusd_transfer_guard_v1",
        (1, 1, 1, 1, 1, 0),
        (1, 1, 1, 1),
    ),
)


def _zusd_truth_partition(inputs: tuple[int, ...]) -> tuple[int, ...]:
    """Encode the zUSD truth partition separately from the policy evaluator."""

    structural_ok = inputs[:3] == (1, 1, 1)
    policy_ok = inputs[3:] == (1, 1, 0)
    transfer_ok = structural_ok and policy_ok
    return (int(structural_ok), int(policy_ok), int(transfer_ok), int(transfer_ok))


_ZUSD_EXHAUSTIVE_TRUTH_PARTITION: Final[tuple[QualificationCase, ...]] = tuple(
    # Expected fields come from _zusd_truth_partition, never from evaluate().
    QualificationCase(
        f"zusd_transfer_truth_partition_{''.join(str(bit) for bit in inputs)}",
        "zusd_transfer_guard_v1",
        inputs,
        _zusd_truth_partition(inputs),
    )
    for inputs in (
        tuple((encoded >> index) & 1 for index in range(6)) for encoded in range(64)
    )
)

_CORPUS: Final[tuple[QualificationCase, ...]] = _FIXED_CORPUS + _ZUSD_EXHAUSTIVE_TRUTH_PARTITION

_CASES_BY_NAME: Final[Mapping[str, QualificationCase]] = MappingProxyType(
    {case.name: case for case in _CORPUS}
)

_NONCE_MANAGER_HISTORIES: Final[tuple[NonceManagerHistory, ...]] = (
    NonceManagerHistory(
        "replay_then_later_valid",
        initial_last_nonce=0,
        final_last_nonce=2,
        cases=(
            _CASES_BY_NAME["nonce_manager_history_replay_then_later_valid_step_1"],
            _CASES_BY_NAME["nonce_manager_history_replay_then_later_valid_step_2_replay"],
            _CASES_BY_NAME[
                "nonce_manager_history_replay_then_later_valid_step_3_later_valid"
            ],
        ),
    ),
    NonceManagerHistory(
        "gap_boundaries",
        initial_last_nonce=0,
        final_last_nonce=2000,
        cases=(
            _CASES_BY_NAME["nonce_manager_history_gap_boundary_step_1_gap_1000"],
            _CASES_BY_NAME[
                "nonce_manager_history_gap_boundary_step_2_gap_1001_rejected"
            ],
            _CASES_BY_NAME["nonce_manager_history_gap_boundary_step_3_later_gap_1000"],
        ),
    ),
    NonceManagerHistory(
        "exhaustion",
        initial_last_nonce=UINT32_MAX - 1,
        final_last_nonce=UINT32_MAX,
        cases=(
            _CASES_BY_NAME["nonce_manager_history_exhaustion_step_1_accept_max"],
            _CASES_BY_NAME["nonce_manager_history_exhaustion_step_2_wrap_rejected"],
            _CASES_BY_NAME["nonce_manager_history_exhaustion_step_3_replay_rejected"],
        ),
    ),
)


def corpus() -> tuple[QualificationCase, ...]:
    """Return the stable scalar rows; callers may batch at most eight independently."""

    return _CORPUS


def stateful_histories() -> tuple[NonceManagerHistory, ...]:
    """Return fixed caller-state simulations; these records carry no authority."""

    return _NONCE_MANAGER_HISTORIES


__all__ = (
    "NonceManagerHistory",
    "QualificationCase",
    "SPEC_IDS",
    "UINT32_MAX",
    "corpus",
    "evaluate",
    "stateful_histories",
)
