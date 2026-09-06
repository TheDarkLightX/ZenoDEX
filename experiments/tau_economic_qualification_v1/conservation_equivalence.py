"""Source-bound QF_BV32 proof for one experimental Tau predicate elision.

Replay with ``python3 -B -m experiments.tau_economic_qualification_v1.conservation_equivalence``.
JSON on stdout describes checked obligations; any unknown, failed control or
source drift raises and exits nonzero. This is a manual mathematical translation
of pinned source, with Z3 as trusted solver. Tau compilation, exact interpreter
traces, performance and economic runtime authority remain separate obligations.
"""

from __future__ import annotations

import hashlib
import json
from dataclasses import asdict, dataclass
from pathlib import Path

import z3

from tools.current_tau_replay_io_v1 import _read_bounded_regular_file_v1

SOURCE_SHA256 = "64fa492391e9138b6d44bd39a0cdc4d1bba0f8c0b79d6d753a076838946a67c6"
SOURCE_PATH = "src/tau_specs/recommended/transfer_hook_guard_v1.tau"


@dataclass(frozen=True)
class SolverObligationV1:
    name: str
    expected: str
    observed: str


@dataclass(frozen=True)
class ConservationEquivalenceV1:
    source_sha256: str
    candidate_sha256: str
    solver_version: str
    obligations: tuple[SolverObligationV1, ...]
    claim: str = "pinned manual QF_BV32 output-predicate equivalence"
    runtime_qualified: bool = False
    performance_qualified: bool = False


def candidate_source(source: str) -> str:
    """Elide only the two redundant predicates from exact pinned source text."""
    if hashlib.sha256(source.encode("utf-8")).hexdigest() != SOURCE_SHA256:
        raise ValueError("CONSERVATION_EQUIVALENCE_SOURCE_DRIFT")
    fragments = (
        " && conservation_ok(sb, sa, rb, ra)",
        " && conservation_ok(i1[t]:bv[32], i2[t]:bv[32], i3[t]:bv[32], i4[t]:bv[32])",
    )
    for fragment in fragments:
        if source.count(fragment) != 1:
            raise ValueError("CONSERVATION_EQUIVALENCE_ELISION_SITE_COUNT")
        source = source.replace(fragment, "", 1)
    return source


def _check_obligation(name: str, query: z3.BoolRef, expected: str) -> SolverObligationV1:
    solver = z3.SolverFor("QF_BV")
    solver.set(timeout=5000)
    solver.add(query)
    observed = str(solver.check())
    if observed != expected:
        raise ValueError(f"CONSERVATION_EQUIVALENCE_NOT_ESTABLISHED:{name}:{observed}")
    return SolverObligationV1(name, expected, observed)


def check_conservation_equivalence(source: str) -> ConservationEquivalenceV1:
    """Check all bv32 tuples and both values of the hook-equals-top proposition.

    Equal output predicates preserve the entire original sbf output relation:
    true constrains output to top; false still permits every non-top element.
    No input or output sbf value is replaced by a Boolean-algebra bitwise value.
    """
    candidate = candidate_source(source)
    sb, sa, rb, ra, amount = z3.BitVecs("sb sa rb ra amount", 32)
    hook_top = z3.Bool("hook_equals_top")
    balances = z3.And(z3.UGE(sb, sa), z3.UGE(ra, rb))
    sender = sb - sa == amount
    receiver = ra - rb == amount
    conservation = sb + rb == sa + ra
    original = (
        balances, z3.And(sender, receiver, conservation), hook_top,
        z3.And(balances, sender, receiver, conservation, hook_top),
    )
    proposed = (
        balances, z3.And(sender, receiver), hook_top,
        z3.And(balances, sender, receiver, hook_top),
    )
    # Work in Z/(2^32), where the two equal deltas imply the sum equality.
    implication_miter = z3.And(sender, receiver, z3.Not(conservation))
    outputs_miter = z3.Or(*(left != right for left, right in zip(original, proposed, strict=True)))
    nonvacuity = z3.And(*original, sb == 1, sa == 0, rb == 0, ra == 1, amount == 1)
    # Fixed controls reveal unsoundly dropping either a direction or delta check.
    wrap_control = z3.And(
        sb == 0, sa == 2**32 - 1, rb == 0, ra == 1, amount == 1, hook_top,
        original[1], z3.Not(original[0]), z3.Not(original[3]),
    )
    missing_delta_control = z3.And(
        sb == 2, sa == 1, rb == 0, ra == 0, amount == 1, hook_top,
        balances, sender, z3.Not(original[1]), z3.Not(original[3]),
    )
    obligations = (
        _check_obligation("equal_deltas_imply_modular_conservation", implication_miter, "unsat"),
        _check_obligation("all_four_output_predicates_unchanged", outputs_miter, "unsat"),
        _check_obligation("one_atom_transfer_nonvacuity", nonvacuity, "sat"),
        _check_obligation("modular_wrap_still_rejected_by_direction", wrap_control, "sat"),
        _check_obligation("missing_receiver_delta_still_rejected", missing_delta_control, "sat"),
    )
    return ConservationEquivalenceV1(
        SOURCE_SHA256, hashlib.sha256(candidate.encode("utf-8")).hexdigest(),
        z3.get_version_string(), obligations,
    )


def main() -> int:
    root = Path(__file__).resolve().parents[2]
    source = _read_bounded_regular_file_v1(root / SOURCE_PATH, 16384, "spec").decode("ascii")
    print(json.dumps(asdict(check_conservation_equivalence(source)), sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
