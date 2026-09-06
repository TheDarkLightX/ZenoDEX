"""Render the standard-library Lean gate repair evidence declaration.

Replay: python3 -B -m experiments.v3_stdlib_lean_gate_repair_v1.render_evidence
Rendering pins the nine proof subjects, their ten tests, the shared gate helper,
the toolchain file, the note and this producer. It runs no compiler or test,
reads no log, records no outcome and qualifies no release. Earlier packets stay
unchanged.
"""

from experiments.v3_completion_followup_v1.render_evidence import _render

OWN = (
    "experiments/v3_stdlib_lean_gate_repair_v1/render_evidence.py",
    "docs/research/ZENODEX_STDLIB_LEAN_GATE_REPAIR_20260906.md",
)
GATE = ("tests/formal/lean_stdlib_gate_v1.py", "lean-mathlib/lean-toolchain")
# Subjects whose captured import closure is standard-library-only at base
# 40d6b89ec6037bea7a57316aa84a62c286be2f23. The true-key-winner subject imports
# Mathlib transitively and stays outside this gate.
PROOF_SUBJECTS = tuple(
    f"lean-mathlib/Proofs/{name}.lean" for name in (
        "ZenoDEXAutoTraderBinaryDecision", "ZenoDEXAutoTraderDecisionBinding",
        "ZenoDEXAutoTraderLiveReleaseCertificate",
        "ZenoDEXAutoTraderStageCertificate", "ZenoDEXExactInRouteCertificate",
        "ZenoDEXExactOutRouteCertificate",
        "ZenoDEXSettlementPriceHistoryCertificate", "SplitRoutingStaircase",
        "UniformBatchOptimality",
    )
)
SUBJECT_TESTS = tuple(
    f"tests/formal/test_lean_{name}.py" for name in (
        "autotrader_binary_decision", "autotrader_decision_binding",
        "autotrader_live_release_certificate", "autotrader_stage_certificate",
        "exact_in_route_certificate", "exact_out_route_certificate",
        "settlement_price_history_certificate", "split_routing_staircase",
        "uniform_batch_optimality",
    )
)
CONTROL_TESTS = ("tests/formal/test_lean_stdlib_gate_v1.py",)


def main() -> None:
    _render("stdlib-lean-gate-repair", OWN + GATE + PROOF_SUBJECTS,
            SUBJECT_TESTS + CONTROL_TESTS,
            claim="Each of nine standard-library-only Lean proof subjects compiles from a fresh capture under the pinned Lean 4.27.0 with warnings as errors, and one independently typed named theorem per subject is consumed through a setup manifest with transitive axioms limited to propext, Classical.choice and Quot.sound.",
            invariant="V3-STDLIB-LEAN-SOURCE-AND-CONSUMER-GATE",
            families=["formal"],
            change_kind="assurance_infrastructure", created_date="2026-09-06",
            rejection_reason="The gate is test-only and has no ledger write port. An absent installed pinned compiler is an explicit pytest skip. A nonzero exit, warning, timeout, forbidden source token, non-silent compile, consumer stderr, missing or duplicate axiom report or unapproved axiom fails the test and yields no receipt.",
            bounds=["nine unchanged proof subjects whose captured import closure is standard-library-only at the base commit; the Mathlib-dependent true-key-winner subject is excluded",
                    "installed Lean 4.27.0 resolved from the local Elan toolchain directory and checked against lean-toolchain: toolchain or version drift fails and an absent executable is an explicit skip",
                    "fresh temporary source tree and .olean per test with inherited LEAN_PATH and LEAN_SRC_PATH removed",
                    "one independent consumer per subject through a setup manifest naming only the fresh artifact: one explicit theorem type and one #print axioms line",
                    "forbidden source tokens sorry, admit, axiom, unsafe, native_decide, sorryAx and ofReduceBool",
                    "warnings as errors, nonzero exit, non-silent source compile, consumer stderr and the 120-second compiler timeout",
                    "exactly one axiom report per theorem, limited to propext, Classical.choice and Quot.sound",
                    "real pinned-compiler wrong-type consumer refusal on the unchanged binary decision subject",
                    "mocked missing, duplicate and nonstandard axiom report parsing and mocked nonzero and timeout shell refusals",
                    "retained UniformBatchOptimality declaration inventory and placeholder scan"],
            nonclaims=["An absent installed pinned compiler is an explicit pytest skip; a skipped run supplies no evidence and is never positive evidence.",
                       "The installed Lean compiler, core and standard-library bytes remain trusted; no compiler or library image hash is qualified.",
                       "Mocked subprocess and parser controls cover shell and report handling only; they do not qualify Lean execution.",
                       "No Lean theorem, toolchain, runtime, dependency, deployment or production source is changed; the repair replaces stale test skip guards only.",
                       "The excluded true-key-winner test and its Mathlib closure remain unchanged and unclaimed.",
                       "One named theorem per subject is consumed; the gate does not establish runtime refinement, Mathlib-wide closure, the complete formal core or whole-program completeness.",
                       "Execution logs are retained review material outside the repository; this packet records declared sources and carries no run outcome."])


if __name__ == "__main__":
    main()
