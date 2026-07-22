from __future__ import annotations

import copy
import json
from pathlib import Path

import pytest

from src.core.confidential_extension_receipts import (
    CONFIDENTIAL_MEASUREMENT_REGISTRY_SCHEMA,
    confidential_extension_receipt_hash,
    confidential_measurement_registry_hash,
    make_confidential_extension_receipt,
)
from src.core.quote_receipts import make_route_quote_receipt, receipt_hash
from src.core.routing import RouteHop, RouteLeg, RouteQuote
from src.state.immutable_json import snapshot_json_mapping
from src.state.pools import PoolState, PoolStatus, compute_pool_id
from tools.check_confidential_route_quote_bundle import (
    DEFAULT_EXTENSION_ID,
    REQUEST_BINDING_PREFIX,
    main,
    validate_confidential_route_quote_bundle_v0,
)

ASSET0 = "0x" + "11" * 32
ASSET1 = "0x" + "22" * 32
NITRO_PCR0 = "a" * 96
NITRO_PCR8 = "b" * 96
MEASUREMENT = f"nitro:pcr0:{NITRO_PCR0}:pcr8:{NITRO_PCR8}"
POLICY_DIGEST = "0x" + ("d" * 64)


def _pool() -> PoolState:
    return PoolState(
        pool_id=compute_pool_id(ASSET0, ASSET1, 30),
        asset0=ASSET0,
        asset1=ASSET1,
        reserve0=10_000,
        reserve1=10_000,
        fee_bps=30,
        lp_supply=20_000,
        status=PoolStatus.ACTIVE,
        created_at=7,
    )


def _quote_receipt() -> dict[str, object]:
    pool = _pool()
    quote = RouteQuote(
        asset_in=ASSET0,
        asset_out=ASSET1,
        amount_in=1_000,
        amount_out=906,
        legs=(
            RouteLeg(
                amount_in=1_000,
                amount_out=906,
                hops=(
                    RouteHop(
                        pool_id=pool.pool_id,
                        asset_in=ASSET0,
                        asset_out=ASSET1,
                        amount_in=1_000,
                        amount_out=906,
                    ),
                ),
            ),
        ),
    )
    return snapshot_json_mapping(
        make_route_quote_receipt(kind="exact_in", quote=quote, pools_by_id={pool.pool_id: pool}, quote_epoch=10),
        name="test_receipt",
    )


def _measurement_registry(
    *,
    provider_id: str = "provider-1",
    revoked: bool = False,
) -> dict[str, object]:
    registry: dict[str, object] = {
        "schema": CONFIDENTIAL_MEASUREMENT_REGISTRY_SCHEMA,
        "registry_id": "tee-route-quote-registry-v1",
        "entries": [
            {
                "provider_id": provider_id,
                "measurement": MEASUREMENT,
                "policy_digest": POLICY_DIGEST,
                "valid_from_epoch": 1,
                "valid_until_epoch": 20,
                "revoked": revoked,
            }
        ],
    }
    registry["registry_hash"] = confidential_measurement_registry_hash(registry)
    return registry


def _pool_manifest() -> dict[str, object]:
    pool = _pool()
    return {
        pool.pool_id: {
            "asset0": pool.asset0,
            "asset1": pool.asset1,
            "reserve0": pool.reserve0,
            "reserve1": pool.reserve1,
            "fee_bps": pool.fee_bps,
            "lp_supply": pool.lp_supply,
            "status": pool.status.value,
            "created_at": pool.created_at,
            "curve_tag": pool.curve_tag,
            "curve_params": pool.curve_params,
        }
    }


def _bundle() -> dict[str, object]:
    quote_receipt = _quote_receipt()
    quote_hash = str(quote_receipt["receipt_hash"])
    tee_receipt = make_confidential_extension_receipt(
        extension_id=DEFAULT_EXTENSION_ID,
        provider_id="provider-1",
        request_id=f"{REQUEST_BINDING_PREFIX}{quote_hash}",
        policy_version="tee-route-quote-policy-v1",
        policy_digest=POLICY_DIGEST,
        measurement=MEASUREMENT,
        do_execute=1,
        policy_ok=1,
        nonce_unused=1,
        output_bound_ok=1,
        current_epoch=10,
        attestation_epoch=9,
        max_attestation_age=2,
        fee_charged=7,
        receipt_fee=7,
        credit_before=40,
        credit_after=33,
        provider_balance_before=9,
        provider_balance_after=16,
    )
    return {
        "schema": "zenodex.confidential_route_quote_bundle.v0",
        "expected_extension_id": DEFAULT_EXTENSION_ID,
        "max_quote_age": 1,
        "measurement_registry": _measurement_registry(),
        "tee_receipt": tee_receipt,
        "quote_receipt": quote_receipt,
        "pools": _pool_manifest(),
    }


def test_confidential_route_quote_bundle_accepts_bound_tee_quote() -> None:
    report = validate_confidential_route_quote_bundle_v0(_bundle())

    assert report["ok"] is True
    assert report["tee_verified"] is True
    assert report["quote_verified"] is True
    assert report["quote_epoch"] == 10
    assert report["privacy_evidence"] == {
        "measurement_approval": True,
        "measurement_registry_checked": True,
        "extension_id_bound": True,
        "request_id_binds_quote_receipt": True,
        "host_guards_ok": True,
        "quote_epoch_fresh": True,
    }


def test_confidential_route_quote_bundle_rejects_unbound_tee_request_id() -> None:
    bundle = _bundle()
    receipt = copy.deepcopy(bundle["tee_receipt"])
    receipt["body"]["request_id"] = "quote_receipt:" + "0" * 64  # type: ignore[index]
    receipt["receipt_hash"] = confidential_extension_receipt_hash(receipt["body"])  # type: ignore[index]
    bundle["tee_receipt"] = receipt

    report = validate_confidential_route_quote_bundle_v0(bundle)

    assert report["ok"] is False
    assert "TEE request_id must bind quote receipt hash" in report["errors"]


def test_confidential_route_quote_bundle_rejects_tampered_quote_receipt() -> None:
    bundle = _bundle()
    quote_receipt = copy.deepcopy(bundle["quote_receipt"])
    quote_receipt["body"]["amount_out"] = 905  # type: ignore[index]
    quote_receipt["receipt_hash"] = receipt_hash(quote_receipt["body"])  # type: ignore[index]
    receipt = copy.deepcopy(bundle["tee_receipt"])
    receipt["body"]["request_id"] = f"{REQUEST_BINDING_PREFIX}{quote_receipt['receipt_hash']}"  # type: ignore[index]
    receipt["receipt_hash"] = confidential_extension_receipt_hash(receipt["body"])  # type: ignore[index]
    bundle["quote_receipt"] = quote_receipt
    bundle["tee_receipt"] = receipt

    report = validate_confidential_route_quote_bundle_v0(bundle)

    assert report["ok"] is False
    assert any("quote receipt rejected" in err for err in report["errors"])


def test_confidential_route_quote_bundle_rejects_stale_quote_epoch() -> None:
    bundle = _bundle()
    bundle["max_quote_age"] = 0
    quote_receipt = copy.deepcopy(bundle["quote_receipt"])
    quote_receipt["body"]["quote_epoch"] = 9  # type: ignore[index]
    quote_receipt["receipt_hash"] = receipt_hash(quote_receipt["body"])  # type: ignore[index]
    receipt = copy.deepcopy(bundle["tee_receipt"])
    receipt["body"]["request_id"] = f"{REQUEST_BINDING_PREFIX}{quote_receipt['receipt_hash']}"  # type: ignore[index]
    receipt["receipt_hash"] = confidential_extension_receipt_hash(receipt["body"])  # type: ignore[index]
    bundle["quote_receipt"] = quote_receipt
    bundle["tee_receipt"] = receipt

    report = validate_confidential_route_quote_bundle_v0(bundle)

    assert report["ok"] is False
    assert "quote epoch exceeds max_quote_age" in report["errors"]
    assert report["privacy_evidence"]["quote_epoch_fresh"] is False


def test_confidential_route_quote_bundle_rejects_future_quote_epoch() -> None:
    bundle = _bundle()
    quote_receipt = copy.deepcopy(bundle["quote_receipt"])
    quote_receipt["body"]["quote_epoch"] = 11  # type: ignore[index]
    quote_receipt["receipt_hash"] = receipt_hash(quote_receipt["body"])  # type: ignore[index]
    receipt = copy.deepcopy(bundle["tee_receipt"])
    receipt["body"]["request_id"] = f"{REQUEST_BINDING_PREFIX}{quote_receipt['receipt_hash']}"  # type: ignore[index]
    receipt["receipt_hash"] = confidential_extension_receipt_hash(receipt["body"])  # type: ignore[index]
    bundle["quote_receipt"] = quote_receipt
    bundle["tee_receipt"] = receipt

    report = validate_confidential_route_quote_bundle_v0(bundle)

    assert report["ok"] is False
    assert "quote epoch must not be in the future" in report["errors"]
    assert report["privacy_evidence"]["quote_epoch_fresh"] is False


def test_confidential_route_quote_bundle_rejects_revoked_measurement() -> None:
    bundle = _bundle()
    bundle["measurement_registry"] = _measurement_registry(revoked=True)

    report = validate_confidential_route_quote_bundle_v0(bundle)

    assert report["ok"] is False
    assert "receipt measurement is not active in measurement_registry" in report["errors"]
    assert report["privacy_evidence"]["measurement_approval"] is False


def test_confidential_route_quote_bundle_rejects_registry_provider_mismatch() -> None:
    bundle = _bundle()
    bundle["measurement_registry"] = _measurement_registry(provider_id="provider-2")

    report = validate_confidential_route_quote_bundle_v0(bundle)

    assert report["ok"] is False
    assert any(
        "receipt measurement/provider is not active in measurement_registry" in err
        for err in report["errors"]
    )


@pytest.mark.parametrize("host_flag", ["do_execute", "policy_ok", "nonce_unused", "output_bound_ok"])
def test_confidential_route_quote_bundle_rejects_bool_host_guard(host_flag: str) -> None:
    bundle = _bundle()
    receipt = copy.deepcopy(bundle["tee_receipt"])
    receipt["body"]["host"][host_flag] = True  # type: ignore[index]
    receipt["receipt_hash"] = confidential_extension_receipt_hash(receipt["body"])  # type: ignore[index]
    bundle["tee_receipt"] = receipt

    report = validate_confidential_route_quote_bundle_v0(bundle)

    assert report["ok"] is False
    assert f"TEE host.{host_flag} must be a 0/1 int" in report["errors"]
    assert report["privacy_evidence"]["host_guards_ok"] is False


def test_confidential_route_quote_bundle_cli_outputs_report(tmp_path: Path, capsys) -> None:
    bundle_path = tmp_path / "confidential_route_quote_bundle.json"
    bundle_path.write_text(json.dumps(_bundle(), indent=2, sort_keys=True), encoding="utf-8")

    code = main([str(bundle_path)])
    out = capsys.readouterr().out
    report = json.loads(out)

    assert code == 0
    assert report["ok"] is True
    assert report["schema"] == "zenodex.confidential_route_quote_bundle_report.v0"
