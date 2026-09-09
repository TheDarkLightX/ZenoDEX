"""Independent evidence for the bounded ZenoLacuna ports."""

from __future__ import annotations

import os
from dataclasses import FrozenInstanceError, replace
from pathlib import Path

import pytest

from src.kernels.python.external_signal_profile_decode_v2 import transform as trusted_decode
from src.kernels.python.external_signal_profile_encode_v2 import transform as trusted_encode
from src.tau_composition.runtime import TauQueryError, TauRuntime
from src.tau_workbench.programs import Program, analyze
from src.zenolacuna.migration import byte_roundtrip_scope, codec_scope
from src.zenolacuna.model import (
    Candidate,
    Evidence,
    Hypothesis,
    LacunaError,
    Outcome,
    OutcomeKind,
    Requirement,
    Scope,
)
from src.zenolacuna.ports.programs import pipeline_outputs, replay_pipeline
from src.zenolacuna.ports.signals import replay_signal_projection
from src.zenolacuna.ports.tau import compare
from src.zenolacuna.relations import semantic_classes
from tools.tau_signal_migration_case import legacy_payload


class _FakeTau:
    def __init__(self, result: bool | BaseException) -> None:
        self.result = result
        self.binary_sha256 = "f" * 64

    def valid(self, formula: str) -> bool:
        del formula
        if isinstance(self.result, BaseException):
            raise self.result
        return self.result


def _tau_scope(outcomes: tuple[Outcome, ...]) -> Scope:
    all_outcomes = tuple(range(len(outcomes)))
    return Scope(
        "tau-test-scope",
        ("c0",),
        outcomes,
        (0,),
        (all_outcomes,),
        (),
        (Hypothesis("all-outcomes", (all_outcomes,)),),
        (),
    )


def test_tau_errors_timeouts_and_malformed_results_are_unknown() -> None:
    scope = _tau_scope((Outcome("ok", "ok", OutcomeKind.ACCEPT),))
    errors: tuple[BaseException, ...] = (
        TauQueryError("native_timeout"),
        TauQueryError("residual_quantifier"),
        TauQueryError("native_result_shape"),
        OSError("tau unavailable"),
        TimeoutError("tau deadline"),
        ValueError("malformed residual"),
    )

    for error in errors:
        result = compare(_FakeTau(error), scope, ((0,),), ((0,),))
        assert result.evidence is Evidence.UNKNOWN
        assert result.equivalent is None
        assert result.code.startswith("SOLVER_UNKNOWN:")


def test_tau_positive_fake_verdict_disagreement_is_unknown() -> None:
    scope = _tau_scope(
        (
            Outcome("accepted", "accepted", OutcomeKind.ACCEPT),
            Outcome("rejected", "rejected", OutcomeKind.REJECT),
        )
    )

    result = compare(_FakeTau(True), scope, ((0,),), ((1,),))

    assert result.evidence is Evidence.UNKNOWN
    assert result.code == "SOLVER_DISAGREEMENT"
    assert result.equivalent is None


def test_tau_formula_and_independent_check_use_complete_observation_rows() -> None:
    scope = _tau_scope(
        (
            Outcome("first", "same", OutcomeKind.ACCEPT),
            Outcome("second", "same", OutcomeKind.ACCEPT),
        )
    )

    result = compare(_FakeTau(True), scope, ((0,),), ((1,),))

    assert result.evidence is Evidence.EXHAUSTIVE_FINITE
    assert result.code == "TAU_FINITE_RELATION_CHECKED"
    assert result.equivalent is True
    assert result.formula


@pytest.mark.skipif(not os.environ.get("TAU_BIN"), reason="TAU_BIN is not set")
def test_tau_native_check_is_optional_and_source_selected_by_environment() -> None:
    runtime = TauRuntime(os.environ["TAU_BIN"])
    scope = _tau_scope((Outcome("ok", "ok", OutcomeKind.ACCEPT),))

    result = compare(runtime, scope, ((0,),), ((0,),))

    assert result.evidence is Evidence.EXHAUSTIVE_FINITE
    assert result.equivalent is True


def test_restricted_program_rejects_top_level_side_effect_without_execution(tmp_path: Path) -> None:
    marker = tmp_path / "executed"
    source = (
        "import pathlib\n"
        f"open({str(marker)!r}, 'w').write('executed')\n"
        "def transform(x): return x\n"
    ).encode()
    program = Program("side_effect", source)

    with pytest.raises(LacunaError) as raised:
        pipeline_outputs((program,), 1)

    assert raised.value.code == "UNSUPPORTED_PROGRAM:source_shape"
    assert not marker.exists()


def _four_value_scope() -> tuple[Scope, Candidate]:
    relation = tuple((value,) for value in range(4))
    outcomes = tuple(
        Outcome(str(value), str(value), OutcomeKind.ACCEPT) for value in range(4)
    )
    scope = Scope(
        "four-value-domain",
        tuple(str(value) for value in range(4)),
        outcomes,
        (0, 1, 2, 3),
        relation,
        (Requirement("identity", (0, 1, 2, 3), relation, relation),),
        (Hypothesis("identity", relation),),
        (),
    )
    return scope, Candidate("identity", relation, (0, 1, 2, 3))


def test_replay_pipeline_rejects_three_inputs_for_claimed_four_value_domain() -> None:
    scope, candidate = _four_value_scope()
    identity = Program("identity", b"def transform(x): return x\n")

    with pytest.raises(LacunaError) as raised:
        replay_pipeline(scope, (0,), candidate, (identity,), 2, (0, 1, 2))

    assert raised.value.code == "INCOMPLETE_RUNTIME_DOMAIN"


def test_replay_pipeline_detects_mutant_only_on_fourth_input() -> None:
    scope, candidate = _four_value_scope()
    fourth_mutant = Program("fourth_mutant", b"def transform(x): return 0 if x == 3 else x\n")

    with pytest.raises(LacunaError) as raised:
        replay_pipeline(scope, (0,), candidate, (fourth_mutant,), 2, (0, 1, 2, 3))

    assert raised.value.code == "RUNTIME_MODEL_MISMATCH"


def test_integer_program_cannot_claim_a_runtime_rejection_from_an_outcome_label() -> None:
    scope, candidate = _four_value_scope()
    mislabeled = replace(scope, outcomes=scope.outcomes[:3] + (
        replace(scope.outcomes[3], kind=OutcomeKind.REJECT),
    ))
    identity = Program("identity", b"def transform(x): return x\n")

    with pytest.raises(LacunaError) as raised:
        replay_pipeline(mislabeled, (0,), candidate, (identity,), 2, (0, 1, 2, 3))

    assert raised.value.code == "RUNTIME_ENCODING_MISMATCH"


def test_byte_program_scope_checks_returned_sentinel_without_inventing_rejection_event() -> None:
    root = Path(__file__).resolve().parents[1]
    scope, candidate = byte_roundtrip_scope(root)
    programs = tuple(Program(f"program_{index}", (root / source.path).read_bytes())
                     for index, source in enumerate(scope.sources))

    report = replay_pipeline(scope, (0,), candidate, programs, 8, tuple(range(256)))

    assert all(outcome.kind is OutcomeKind.ACCEPT for outcome in scope.outcomes)
    assert candidate.allowed == tuple((x,) if x < 128 else (255,) for x in range(256))
    assert report.code == "RESTRICTED_PROGRAM_REPLAYED"
    assert report.claim.startswith("EXHAUSTIVE_RESTRICTED_INTEGER_PROGRAM;")


def test_codec_scope_has_eight_paired_xor_mutants_and_two_semantic_classes() -> None:
    scope, trials = codec_scope(Path(__file__).resolve().parents[1])

    assert len(trials) == 8
    assert len(scope.questions) == 1
    assert len(semantic_classes(scope, tuple(range(len(scope.hypotheses))))) == 2
    assert trials[0].mask == 0
    assert not trials[0].producer_mismatches
    assert not trials[0].consumer_mismatches
    for trial in trials[1:]:
        assert len(trial.producer_mismatches) == 128
        assert len(trial.consumer_mismatches) == 128


def test_codec_source_interpreter_matches_trusted_functions_over_every_byte() -> None:
    root = Path(__file__).resolve().parents[1]
    encoder = Program("trusted_encoder", (root / "src/kernels/python/external_signal_profile_encode_v2.py").read_bytes())
    decoder = Program("trusted_decoder", (root / "src/kernels/python/external_signal_profile_decode_v2.py").read_bytes())

    assert analyze(encoder, 8).outputs == tuple(trusted_encode(value) for value in range(256))
    assert analyze(decoder, 8).outputs == tuple(trusted_decode(value) for value in range(256))


def _runtime_fields() -> tuple[str, ...]:
    return tuple(sorted(legacy_payload(0)))


def test_signal_projection_missing_auth_and_freshness_is_model_omission() -> None:
    declared = tuple(field for field in _runtime_fields() if field not in {"auth_ok", "freshness_ok"})

    report = replay_signal_projection(declared)

    assert report.code == "MODEL_OMISSION"
    assert report.evidence is Evidence.UNKNOWN
    assert report.missing_fields == ("auth_ok", "freshness_ok")
    assert report.authority == "NONE"
    assert report.checked_inputs128 == 0


def test_signal_projection_unknown_field_is_model_omission() -> None:
    declared = tuple(sorted((*_runtime_fields(), "future_auth_mode")))

    report = replay_signal_projection(declared)

    assert report.code == "MODEL_OMISSION"
    assert report.evidence is Evidence.UNKNOWN
    assert report.unknown_fields == ("future_auth_mode",)
    assert report.missing_fields == ()
    assert report.authority == "NONE"


def test_signal_projection_full_fixed_v1_v2_fixture_is_exhaustive() -> None:
    report = replay_signal_projection(_runtime_fields())

    assert report.code == "SIGNAL_FIXTURE_PARITY"
    assert report.evidence is Evidence.EXHAUSTIVE_FINITE
    assert report.checked_inputs128 == 128
    assert report.missing_fields == ()
    assert report.unknown_fields == ()
    assert report.mismatches == ()
    assert report.authority == "NONE"
    assert len(report.source_sha256) == 5
    assert all(len(source_sha256) == 64 for source_sha256 in report.source_sha256)


def test_signal_projection_report_is_frozen() -> None:
    report = replay_signal_projection(_runtime_fields())

    with pytest.raises(FrozenInstanceError):
        report.code = "MODEL_OMISSION"  # type: ignore[misc]
