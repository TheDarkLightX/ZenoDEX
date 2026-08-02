"""Deterministic property checks for F07 checkpoint lineage."""

from __future__ import annotations

import hypothesis.strategies as st
from hypothesis import given, settings

from experiments.fcis_m6_f07_checkpoint_check import (
    build_genesis_acceptance,
    build_source,
    recompute_checkpoint_with,
)
from src.core.fcis_m6_f07_checkpoint import (
    F07CheckpointAcceptanceV1,
    F07CheckpointRejectV1,
    build_f07_checkpoint_v1,
    validate_f07_checkpoint_v1,
)


@settings(max_examples=24, derandomize=True)  # type: ignore[untyped-decorator]
@given(  # type: ignore[untyped-decorator]
    field=st.sampled_from(
        (
            "prior_layout_root",
            "prior_history_root",
            "checkpoint_state_root",
            "deployment_config_root",
            "verifier_profile_root",
            "genesis_admission_root",
            "nullifier_accumulator_root",
            "authority_epoch_summary_root",
            "outbox_accumulator_root",
            "proof_root",
        )
    )
)
def test_source_recomputed_checkpoint_rejects_each_root_substitution(field: str) -> None:
    source = build_source()
    genesis = build_genesis_acceptance(source)
    result = build_f07_checkpoint_v1(source, genesis=genesis)
    assert type(result) is F07CheckpointAcceptanceV1

    forged = recompute_checkpoint_with(result.checkpoint, **{field: "0x" + "e" * 64})
    checked = validate_f07_checkpoint_v1(source, genesis=genesis, checkpoint=forged)

    assert type(checked) is F07CheckpointRejectV1
