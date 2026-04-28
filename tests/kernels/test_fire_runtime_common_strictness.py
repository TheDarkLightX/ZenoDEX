from __future__ import annotations

from types import SimpleNamespace

from src.fire.runtime.burn_boost_call_v1 import (
    BurnBoostCallTerms,
    IR_HASH,
    _certificate_env,
    _compiled_state_from_artifact,
    build_manifest,
    compile_terms,
)
from src.fire.runtime.common_v1 import run_verified_settlement


class _StringDeltaRef:
    @staticmethod
    def Command(tag: str, args: dict[str, int]) -> SimpleNamespace:
        return SimpleNamespace(tag=tag, args=args)

    @staticmethod
    def step(_state: object, _command: object) -> SimpleNamespace:
        return SimpleNamespace(
            ok=True,
            state=SimpleNamespace(holder_delta="0", writer_delta=0),
            error=None,
        )


def test_run_verified_settlement_rejects_string_holder_delta() -> None:
    artifact = compile_terms(BurnBoostCallTerms(n_notional=10, strike_index=4, cap_index=3, source_upper=9))

    ok, err, state, receipt = run_verified_settlement(
        artifact,
        expected_ir_hash=IR_HASH,
        certificate_env=_certificate_env,
        manifest_builder=build_manifest,
        compiled_state_from_artifact=_compiled_state_from_artifact,
        ref_module=_StringDeltaRef,
        settle_args={
            "witness_final_in": 7,
            "holder_posted_in": 0,
            "writer_posted_in": 30,
        },
        witness_inputs={"witness_final": 7},
    )

    assert ok is False
    assert err == "settlement_state_invalid:settlement_state.holder_delta must be an int"
    assert state is None
    assert receipt is None
