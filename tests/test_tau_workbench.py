"""Source-derived compatibility, exact quotient lifting and independent code replay."""

import json
import os
from dataclasses import asdict, replace
from itertools import product
from pathlib import Path

import pytest

from src.tau_composition.runtime import TauRuntime
from src.tau_workbench.catalog import build_catalog, central_counts
from src.tau_workbench.compiler import check_pipeline, compile_task, problem_for
from src.tau_workbench.examples import message_task, program
from src.tau_workbench.models import Stage, Task
from src.tau_workbench.native import replay_bundles


@pytest.fixture
def native() -> TauRuntime:
    path = os.environ.get("TAU_COMPOSITION_BIN")
    if not path:
        pytest.skip("explicit native Tau binary required")
    return TauRuntime(Path(path))


def test_complete_behavior_quotient_preserves_every_artifact_combination() -> None:
    catalog = build_catalog(message_task())
    assert tuple(len(classes) for classes in catalog.stages) == (4, 4, 4)
    assert tuple(tuple(len(cls.members) for cls in classes) for classes in catalog.stages) == (
        (2, 2, 2, 2), (2, 2, 2, 2), (2, 2, 2, 2))
    assert central_counts(message_task()) == {
        "cached_artifact_checks": 512, "quotient_class_checks": 64,
        "accepted_artifact_bundles": 392, "accepted_behavior_bundles": 49,
        "source_input_evaluations": 6144,
    }


def test_absent_selector_codes_are_excluded_from_the_normative_relation() -> None:
    original = message_task()
    encoder = Stage("encoder", original.stages[0].programs[:6])
    task = replace(original, stages=(encoder, *original.stages[1:]))
    problem = problem_for(task)
    # Encoder has three classes; binary selector 11 names no real artifact.
    for others in product((False, True), repeat=4):
        values = dict(zip(problem.contract.controls, (True, True, *others), strict=True))
        assert not problem.contract.satisfied(values)


def test_claimed_catalog_cannot_replace_source_analysis_in_public_spec_builder() -> None:
    observed = build_catalog(message_task())
    forged = replace(observed, legal=frozenset(product(range(4), repeat=3)))
    with pytest.raises(ValueError, match="task_type"):
        problem_for(forged)


def test_claimed_catalog_cannot_expand_public_central_count_bounds(monkeypatch) -> None:
    from src.tau_workbench import catalog as module
    observed = build_catalog(message_task())
    forged = replace(observed, stages=(observed.stages[0] * 100,) * 3)
    def forbidden(*args, **kwargs):
        pytest.fail("claimed catalog reached product enumeration")
    monkeypatch.setattr(module, "product", forbidden)
    with pytest.raises(ValueError, match="task_type"):
        central_counts(forged)


def test_native_python_checks_real_bundles_against_the_human_oracle() -> None:
    task = message_task()
    bundles = tuple(product(range(8), repeat=3))
    replay = replay_bundles(task, bundles)
    assert sum(outcome is None for outcome in replay.outcomes) == 392
    assert replay.component_inputs_checked == 6144
    bad = replay.outcomes[bundles.index((2, 0, 0))]
    assert bad is not None and asdict(bad) == {"input": 1, "expected": 1, "observed": 0}
    assert replay.source_hashes[0][0] == task.stages[0].programs[0].sha256
    catalog = build_catalog(task)
    for bundle, outcome in zip(bundles, replay.outcomes, strict=True):
        class_codes = tuple(next(code for code, cls in enumerate(classes)
                                 if task.stages[i].programs[index] in cls.members)
                            for i, (classes, index) in enumerate(zip(catalog.stages, bundle, strict=True)))
        assert (outcome is None) == (class_codes in catalog.legal)


def test_native_replay_binds_the_human_task_and_ordered_bundle_batch() -> None:
    task = message_task()
    bundles = ((0, 0, 4), (2, 0, 4))
    observed = replay_bundles(task, bundles)
    reordered = replay_bundles(task, bundles[::-1])
    changed = replay_bundles(replace(task, inputs=(0,), expected=(0,)), bundles)
    assert observed.task_id == task.subject_id != changed.task_id
    assert observed.bundle_sha256 != reordered.bundle_sha256
    assert observed.pipeline_inputs_checked == 128


def test_human_priority_selects_different_actual_implementation_freedoms(native) -> None:
    first = compile_task(message_task(), native, ("encoder", "adapter", "decoder"))
    reverse = compile_task(message_task(), native, ("decoder", "adapter", "encoder"))
    assert first.domains == ((0, 1, 2, 3), (0, 1, 2, 3), (2,))
    assert reverse.domains == ((0,), (0, 1, 2, 3), (0, 1, 2, 3))
    assert tuple(len(first.members(i)) for i in range(3)) == (8, 8, 2)
    assert tuple(len(reverse.members(i)) for i in range(3)) == (2, 8, 8)
    assert first.check_selection(("tag_v2_add", "identity", "tolerant_mod"))
    with pytest.raises(ValueError, match="selection_program"):
        first.check_selection(("tag_v2_add", "identity", "legacy_lt"))


def test_new_equivalent_source_can_be_admitted_without_tau_recompilation(native) -> None:
    compiled = compile_task(message_task(), native)
    before = len(native.records)
    replacement = program("new_decoder", "x - (x // 64) * 64")
    result = compiled.assess_replacement("decoder", replacement)
    assert result["status"] == "local_equivalent" and result["behavior_class"] == 2
    assert result["program_sha256"] == replacement.sha256
    assert result["authority"] == "NONE" and result["native_queries"] == 0
    assert len(native.records) == before
    check_pipeline(message_task(), (message_task().stages[0].programs[4],
                                    message_task().stages[1].programs[0], replacement))
    revision = (message_task().stages[0].programs[4],
                message_task().stages[1].programs[0], replacement)
    assert compiled.check_revision(revision) == revision


def test_initial_input_agreement_does_not_authorize_contextual_replacement(native) -> None:
    compiled = compile_task(message_task(), native)
    # Both decoders agree on 0..63. Another stage can produce 128..191.
    proposed = program("looks_right_on_payloads", "x if x < 64 else 0")
    assert compiled.assess_replacement("decoder", proposed)["status"] == "renegotiation_required"
    with pytest.raises(ValueError, match="pipeline_behavior_mismatch"):
        check_pipeline(message_task(), (message_task().stages[0].programs[4],
                                        message_task().stages[1].programs[0], proposed))


def test_unknown_behavior_requires_renegotiation_and_source_is_not_self_attestation(native) -> None:
    compiled = compile_task(message_task(), native)
    changed = program("tolerant_mask", "(x & 63) ^ 1")
    result = compiled.assess_replacement("decoder", changed)
    assert result["status"] == "renegotiation_required" and result["behavior_class"] is None
    assert result["program_sha256"] != message_task().stages[2].programs[4].sha256
    with pytest.raises(ValueError, match="revision_requires_renegotiation"):
        compiled.check_revision((message_task().stages[0].programs[0],
                                 message_task().stages[1].programs[0], changed))


def test_changed_human_expectation_invalidates_the_old_anchor_and_task_identity() -> None:
    original = message_task()
    altered = replace(original, expected=(1,) + original.expected[1:])
    assert original.subject_id != altered.subject_id
    with pytest.raises(ValueError, match="anchor_pipeline_invalid"):
        build_catalog(altered)


@pytest.mark.parametrize("values", [(True,), (-1,), (256,), (), [0]])
def test_task_domain_and_input_container_are_exact(values) -> None:
    with pytest.raises(ValueError, match="task_table"):
        replace(message_task(), inputs=values)


def test_unsupported_source_is_rejected_before_native_process(monkeypatch) -> None:
    from src.tau_workbench import native as module
    def forbidden(*args, **kwargs):
        pytest.fail("unsupported source reached native execution")
    monkeypatch.setattr(module, "_run_subprocess_with_output_caps", forbidden)
    bad = program("unsupported", "abs(x)")
    task = Task("unsupported_task", 8, (Stage("stage", (bad,)),), (0,), (0,), ("unsupported",))
    with pytest.raises(ValueError):
        replay_bundles(task, ((0,),))


def test_interpreter_disagreement_is_a_failure_even_when_native_pipeline_passes(monkeypatch) -> None:
    from src.tau_workbench import native as module
    real = module.analyze
    def mutant(program, bits):
        observed = real(program, bits)
        return replace(observed, outputs=(observed.outputs[0] ^ 1,) + observed.outputs[1:])
    monkeypatch.setattr(module, "analyze", mutant)
    with pytest.raises(ValueError, match="interpreter_native_disagreement"):
        replay_bundles(message_task(), ((0, 0, 4),))


@pytest.mark.parametrize("outcome, checked", [
    (None, 64),
    ({"input": 1, "expected": 1, "observed": 0}, 64),
    ({"input": 1, "expected": 1, "observed": 2}, 2),
])
def test_native_joint_outcomes_must_match_measured_component_composition(
    monkeypatch, outcome, checked,
) -> None:
    from src.tau_workbench import native as module
    task = message_task()
    tables = [[module.analyze(p, task.bits).outputs for p in stage.programs]
              for stage in task.stages]
    payload = json.dumps({"component_outputs": tables, "outcomes": [outcome],
                          "pipeline_inputs_checked": checked})
    monkeypatch.setattr(module, "_run_subprocess_with_output_caps", lambda *a, **kw: (0, payload, ""))
    with pytest.raises(ValueError, match="native_pipeline_disagreement"):
        replay_bundles(task, ((2, 0, 0),))
