from __future__ import annotations

import pytest

from src.core.confidential_extension_receipts import make_confidential_extension_receipt
from src.integration.confidential_runtime_receipts import (
    build_confidential_runtime_execution_receipt_v1,
)

NITRO_PCR0 = "a" * 96
NITRO_PCR8 = "b" * 96
POLICY_DIGEST = "0x" + ("d" * 64)
HASH = "0x" + ("e" * 64)


def _receipt() -> dict:
    return make_confidential_extension_receipt(
        extension_id="route-premium-v1",
        provider_id="provider-1",
        request_id="req-1",
        policy_version="tee-policy-v1",
        policy_digest=POLICY_DIGEST,
        measurement=f"nitro:pcr0:{NITRO_PCR0}:pcr8:{NITRO_PCR8}",
        do_execute=1,
        policy_ok=1,
        nonce_unused=1,
        output_bound_ok=1,
        current_epoch=10,
        attestation_epoch=8,
        max_attestation_age=2,
        fee_charged=7,
        receipt_fee=7,
        credit_before=40,
        credit_after=33,
        provider_balance_before=9,
        provider_balance_after=16,
    )


def _build_runtime_receipt(receipt: dict) -> dict:
    return build_confidential_runtime_execution_receipt_v1(
        receipt=receipt,
        execution_id="exec-1",
        execution_kind="private-route",
        result_code="ok",
        operator_status_hash=HASH,
        approved_measurements_hash=HASH,
        external_verifier_binding_hash=HASH,
    )


@pytest.mark.parametrize("host_flag", ["do_execute", "policy_ok", "output_bound_ok"])
def test_confidential_runtime_execution_receipt_rejects_bool_host_flags(host_flag: str) -> None:
    receipt = _receipt()
    receipt["body"]["host"][host_flag] = True

    with pytest.raises(ValueError, match=rf"receipt\.body\.host\.{host_flag} must be a bounded int"):
        _build_runtime_receipt(receipt)
