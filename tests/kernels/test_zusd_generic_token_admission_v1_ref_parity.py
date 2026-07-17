from __future__ import annotations

import hashlib
import importlib.util
import re
import sys
from itertools import product
from pathlib import Path
from types import ModuleType

import pytest

from src.core.zusd_generic_token_admission import (
    MAX_TOKEN_UNITS,
    CanonicalZUSDCustodyClass,
    CanonicalZUSDSupplyState,
    GenericTokenAction,
    GenericTokenAdmissionCommand,
    TokenAssetClass,
    TokenWriterRole,
    evaluate_generic_token_admission_transition,
)

ACTION_TAG = {
    GenericTokenAction.TRANSFER: "evaluate_transfer",
    GenericTokenAction.MINT: "evaluate_mint",
    GenericTokenAction.BURN: "evaluate_burn",
}
ACTION_CODE = {
    GenericTokenAction.TRANSFER: 0,
    GenericTokenAction.MINT: 1,
    GenericTokenAction.BURN: 2,
}
EXPECTED_IR_HASH = "sha256:5c397e970673e80bb75d4461cf2af65f5f6294b7438cf0b2936528c0d9461492"
EXPECTED_MODEL_SOURCE_SHA256 = (
    "4f542927d11c48a44d29904715b3c6140889a49bb1602b0308746298700639fd"
)


def _paths() -> tuple[Path, Path]:
    root = Path(__file__).resolve().parents[2]
    model = root / "src" / "kernels" / "dex" / "zusd_generic_token_admission_v1.yaml"
    reference = (
        root
        / "generated"
        / "zusd_generic_token_admission_v1"
        / "python_ref"
        / "zusd_generic_token_admission_v1_ref.py"
    )
    return model, reference


def _load_reference() -> ModuleType:
    _, reference = _paths()
    module_name = "generated.zusd_generic_token_admission_v1.python_ref.reference"
    spec = importlib.util.spec_from_file_location(module_name, reference)
    if spec is None or spec.loader is None:
        raise AssertionError("could not load generated ESSO Python reference")
    module = importlib.util.module_from_spec(spec)
    sys.modules[module_name] = module
    spec.loader.exec_module(module)
    return module


def test_generated_reference_is_hash_bound_to_versioned_esso_ir() -> None:
    model, reference = _paths()
    source_hash = hashlib.sha256(model.read_bytes()).hexdigest()
    source = reference.read_text(encoding="utf-8")
    match = re.search(r"^IR hash: (sha256:[0-9a-f]{64})$", source, re.MULTILINE)
    assert match is not None
    assert source_hash == EXPECTED_MODEL_SOURCE_SHA256
    assert match.group(1) == EXPECTED_IR_HASH


@pytest.mark.parametrize("supply", (0, 1, MAX_TOKEN_UNITS))
def test_pure_core_matches_generated_reference_for_every_typed_case(supply: int) -> None:
    reference = _load_reference()
    cases = list(
        product(
            GenericTokenAction,
            TokenAssetClass,
            TokenWriterRole,
            CanonicalZUSDCustodyClass,
        )
    )
    assert len(cases) == 108

    for action, asset_class, writer_role, custody_class in cases:
        command = GenericTokenAdmissionCommand(
            action=action,
            asset_class=asset_class,
            writer_role=writer_role,
            recipient_custody_class=custody_class,
        )
        core = evaluate_generic_token_admission_transition(
            CanonicalZUSDSupplyState(supply),
            command,
        )
        actor_is_monetary_authority = (
            writer_role is TokenWriterRole.ZUSD_MONETARY_AUTHORITY
        )
        asset_is_canonical_zusd = asset_class is TokenAssetClass.CANONICAL_ZUSD
        recipient_is_reserved = custody_class.is_reserved_internal_custody
        result = reference.step(
            reference.State(canonical_supply_units=supply, violation_found=0),
            reference.Command(
                tag=ACTION_TAG[action],
                args={
                    "actor_is_monetary_authority": actor_is_monetary_authority,
                    "asset_is_canonical_zusd": asset_is_canonical_zusd,
                    "recipient_is_reserved_internal_custody": recipient_is_reserved,
                },
            ),
        )

        assert result.ok is True
        assert result.error is None
        assert result.state is not None
        assert result.effects is not None
        assert result.state.canonical_supply_units == core.post_state.total_supply_units
        assert result.state.violation_found == 0
        assert result.effects == {
            "actor_is_monetary_authority": actor_is_monetary_authority,
            "admitted": core.decision.admitted,
            "asset_is_canonical_zusd": asset_is_canonical_zusd,
            "canonical_zusd_supply_delta": core.decision.canonical_zusd_supply_delta,
            "exhaustive_case_ok": True,
            "operation_code": ACTION_CODE[action],
            "post_canonical_supply_units": core.post_state.total_supply_units,
            "recipient_is_reserved_internal_custody": recipient_is_reserved,
            "decision_code": int(core.decision.code),
            "rejection_noop": True,
        }


def test_generated_reference_rejects_out_of_domain_or_ambiguous_inputs() -> None:
    reference = _load_reference()
    args = {
        "actor_is_monetary_authority": False,
        "asset_is_canonical_zusd": True,
        "recipient_is_reserved_internal_custody": False,
    }
    command = reference.Command(tag="evaluate_transfer", args=args)
    assert reference.step(
        reference.State(canonical_supply_units=MAX_TOKEN_UNITS + 1, violation_found=0),
        command,
    ).ok is False
    assert reference.step(
        reference.init_state(),
        reference.Command(
            tag="evaluate_transfer",
            args={**args, "actor_is_monetary_authority": 0},
        ),
    ).ok is False
