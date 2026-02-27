from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Callable, Hashable


@dataclass(frozen=True)
class IntDomain:
    """Integer domain description for BVA and boundary mining.

    Notes:
    - `include_bool` is useful because `bool` is a subclass of `int` in Python.
      Many ZenoDEX validators reject bools explicitly.
    """

    min_value: int
    max_value: int
    step: int = 1
    specials: tuple[int, ...] = ()
    include_oob: bool = True
    include_bool: bool = True
    include_none: bool = False

    def __post_init__(self) -> None:
        if int(self.step) <= 0:
            raise ValueError("step must be positive")
        if int(self.max_value) < int(self.min_value):
            raise ValueError("max_value must be >= min_value")


LabelFn = Callable[[Any], Hashable]
ConstraintFn = Callable[[dict[str, Any]], bool]


@dataclass(frozen=True)
class Scenario:
    name: str
    fn: Callable[..., Any]
    domains: dict[str, IntDomain]
    fixed_kwargs: dict[str, Any] = field(default_factory=dict)
    constraint: ConstraintFn | None = None

    # Labeling:
    # - If `label_fn` is set, labels are computed from the function output.
    # - Otherwise, if `trace_paths` is set, labels are execution-path signatures.
    # - Otherwise, labels fall back to `repr(output)`.
    label_fn: LabelFn | None = None
    trace_paths: tuple[str, ...] = ()

    # Budget knobs for the miner.
    seed: int = 0
    max_contexts: int = 12
    samples_per_context: int = 96
    exhaustive_threshold: int = 4096
    refine_scan_threshold: int = 256

    # Optional: extra random contexts per focus param (in addition to representative cartesian contexts).
    random_contexts: int = 0
    random_context_budget: int = 256

    # Optional: global (multi-parameter) boundary mining.
    global_samples: int = 0
    global_refine_steps: int = 2048
