from __future__ import annotations

from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
RUNNER = (
    ROOT
    / "zk/spot_settlement_v7_risc0/harness/src/bin/prove_spot_settlement_v7.rs"
)


def test_v7_candidate_artifacts_follow_sealed_verification() -> None:
    source = RUNNER.read_text(encoding="utf-8")

    proof = source.index("prove_and_verify_spot_settlement_v7_v1(")
    output = source.index(".firecracker_output()")
    mutation = source.index("exact_seal_mutation_reject(")
    persist = source.index("persist_verified_artifacts(")

    assert proof < output < mutation < persist
    assert "VerifiedSpotSettlementV7ErrorV1::ReceiptVerificationFailed" in source
    assert "ambient RISC0_DEV_MODE is forbidden" in source


def test_v7_runner_has_no_authority_promotion_labels() -> None:
    source = RUNNER.read_text(encoding="utf-8")

    assert '"release_authority": false' in source
    assert '"settlement_authority": false' in source
    assert '"production_authority": false' in source
    assert '"zero_knowledge_privacy": false' in source
