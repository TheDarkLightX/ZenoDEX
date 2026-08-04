"""BDD-style scenarios for non-authoritative Tau/ZenoLedger content parity."""

from __future__ import annotations

import hashlib
from dataclasses import replace

import pytest

from src.core.dex import DexState
from src.core.fcis_m6_global_state_projection_v1 import (
    M6_KNOWN_GLOBAL_PROJECTION_GAPS_V1,
    M6_PROJECTION_AUTHORITY_OBLIGATIONS_V1,
    M6ApplicationStateComponentV1,
    M6GlobalStateProjectionRejectCodeV1,
    M6GlobalStateProjectionRejectV1,
    M6ProjectionAuthorityObligationV1,
)
from src.integration.dex_snapshot import snapshot_from_state, state_from_snapshot
from src.integration.fcis_m6_global_state_qualification_v1 import (
    require_authoritative_global_state_projection_v1,
)
from src.integration.fcis_m6_projection_receipts_v1 import (
    M6ProjectionContentObservationV1,
    M6ProjectionContentParityReceiptV1,
    M6ProjectionSourceKindV1,
    is_verified_projection_content_observation_v1,
    is_verified_projection_content_parity_v1,
    verify_tau_zeno_ledger_content_parity_v1,
)
from src.integration.fcis_m6_projection_values_v1 import (
    M6ApplicationContentV1,
    is_verified_application_content_v1,
)
from src.integration.fcis_m6_tau_zenoledger_projection_v1 import (
    DEX_SNAPSHOT_SOURCE_SCHEMA_V1,
    M6_DEX_SNAPSHOT_FIELD_COMPONENTS_V1,
    M6_DEX_SNAPSHOT_REPRESENTATION_ONLY_FIELDS_V1,
    TAU_APP_STATE_SCHEMA_V1,
    project_tau_claimed_shared_spot_content_v1,
    project_zeno_ledger_header_shared_spot_content_v1,
)
from src.integration.zeno_ledger_v0 import (
    BATCH_CUTOFF_SCHEMA_V0,
    BODY_SCHEMA_V0,
    ZERO_ROOT_V0,
    build_header_v0,
    canonical_body_root_v0,
    compute_app_hash_v0,
    compute_evidence_root_v0,
    compute_ingress_root_v0,
    compute_tx_root_v0,
    dex_state_root_v0,
    hash_v0,
)
from src.integration.zusd_monetary_bridge import (
    ZUSDMonetaryConfig,
    init_monetary_state,
    zusd_monetary_state_to_obj,
)
from src.state.balances import BalanceTable
from src.state.canonical import canonical_json_bytes
from src.state.lp import LPTable

_ALICE = "0x" + "aa" * 48


def _root(label: str) -> str:
    return hash_v0("m6_projection_test_root", {"label": label})


def _dex_state(*, zusd_balance: int = 0) -> DexState:
    balances = BalanceTable()
    if zusd_balance:
        asset = ZUSDMonetaryConfig(chain_id="zenodex/research-chain").zusd_asset
        balances.set(_ALICE, asset, zusd_balance)
    return DexState(balances=balances, pools={}, lp_balances=LPTable())


def _bare_state() -> dict[str, object]:
    return snapshot_from_state(_dex_state()).data


def test_every_canonical_dex_snapshot_field_is_mapped_or_representation_only() -> None:
    declared_fields = {field for field, _component in M6_DEX_SNAPSHOT_FIELD_COMPONENTS_V1}.union(
        M6_DEX_SNAPSHOT_REPRESENTATION_ONLY_FIELDS_V1
    )
    assert declared_fields == set(_bare_state())
    components = tuple(component for _field, component in M6_DEX_SNAPSHOT_FIELD_COMPONENTS_V1)
    assert len(components) == len(set(components))


def test_lp_mint_age_is_a_logical_component_of_the_spot_commitment() -> None:
    pool_id = _root("lp-mint-age-pool")
    first_lp = LPTable()
    first_lp.set(_ALICE, pool_id, 1)
    first_lp.set_last_mint_timestamp(_ALICE, pool_id, 7)
    first_state = DexState(balances=BalanceTable(), pools={}, lp_balances=first_lp)
    first_snapshot = snapshot_from_state(first_state).data
    first = project_tau_claimed_shared_spot_content_v1(
        app_state=first_snapshot,
        claimed_app_hash=_app_hash(first_snapshot),
        claimed_source_position=7,
    )
    assert type(first) is M6ProjectionContentObservationV1
    assert M6ApplicationStateComponentV1.LP_MINT_AGE in first.content.coverage.covered_components

    second_lp = LPTable()
    second_lp.set(_ALICE, pool_id, 1)
    second_lp.set_last_mint_timestamp(_ALICE, pool_id, 8)
    second_state = DexState(balances=BalanceTable(), pools={}, lp_balances=second_lp)
    second_snapshot = snapshot_from_state(second_state).data
    second = project_tau_claimed_shared_spot_content_v1(
        app_state=second_snapshot,
        claimed_app_hash=_app_hash(second_snapshot),
        claimed_source_position=7,
    )
    assert type(second) is M6ProjectionContentObservationV1
    assert dex_state_root_v0(first_state) != dex_state_root_v0(second_state)
    assert first.content.content_root != second.content.content_root


def _wrapped_zusd_state(
    *,
    zusd_balance: int = 0,
    monetary_chain_id: str = "zenodex/research-chain",
) -> dict[str, object]:
    monetary = init_monetary_state(ZUSDMonetaryConfig(chain_id=monetary_chain_id))
    return {
        "schema": "zenodex/tau_app_state/v1",
        "version": 1,
        "dex_state": snapshot_from_state(_dex_state(zusd_balance=zusd_balance)).data,
        "proof_mining": None,
        "zusd_monetary": zusd_monetary_state_to_obj(monetary),
    }


def _app_hash(app_state: dict[str, object]) -> str:
    return hashlib.sha256(canonical_json_bytes(app_state)).hexdigest()


def _spot_state_root(app_state: dict[str, object]) -> str:
    dex_snapshot = (
        app_state["dex_state"]
        if app_state.get("schema") == "zenodex/tau_app_state/v1"
        else app_state
    )
    return dex_state_root_v0(state_from_snapshot(dex_snapshot))  # type: ignore[arg-type]


def _body() -> dict[str, object]:
    chain_id = "zenodex/research-chain"
    height = 7
    return {
        "schema": BODY_SCHEMA_V0,
        "chain_id": chain_id,
        "height": height,
        "ingress": {
            "batch_cutoff": {
                "schema": BATCH_CUTOFF_SCHEMA_V0,
                "chain_id": chain_id,
                "height": height,
                "cutoff_time_ms": 1,
                "cutoff_sequence": 1,
                "sequencer_id": "sequencer-0",
                "policy_id": "projection-test-v1",
                "policy_digest": _root("cutoff-policy"),
            },
            "ingress_receipts": [],
            "forced_inclusion_requests": [],
            "forced_inclusion_decisions": [],
        },
        "transactions": [],
        "settlement_envelopes": [],
        "evidence": {
            "upba_certificates": [],
            "price_grid_tables": [],
            "uniform_batch_hypergraph_roots": [],
            "oracle_packets": [],
            "proof_receipts": [],
            "rejection_receipts": [],
        },
    }


def _header(body: dict[str, object], *, post_state_root: str) -> dict[str, object]:
    evidence_root = compute_evidence_root_v0(body["evidence"])  # type: ignore[arg-type]
    config_digest = _root("config")
    versions_digest = _root("versions")
    app_hash = compute_app_hash_v0(
        {
            "chain_id": body["chain_id"],
            "height": body["height"],
            "post_state_root": post_state_root,
            "evidence_root": evidence_root,
            "config_digest": config_digest,
            "module_versions_digest": versions_digest,
        }
    )
    return build_header_v0(
        chain_id=str(body["chain_id"]),
        height=int(body["height"]),
        time_ms=1,
        prev_header_hash=ZERO_ROOT_V0,
        sequencer_set_hash=_root("sequencer-set"),
        ingress_root=compute_ingress_root_v0(body["ingress"]),  # type: ignore[arg-type]
        tx_root=compute_tx_root_v0(body["transactions"]),  # type: ignore[arg-type]
        pre_state_root=_root("pre-state"),
        post_state_root=post_state_root,
        app_hash=app_hash,
        evidence_root=evidence_root,
        body_root=canonical_body_root_v0(body),  # type: ignore[arg-type]
        data_availability_root=_root("data-availability"),
        proof_journal_hash=ZERO_ROOT_V0,
        config_digest=config_digest,
        module_versions_digest=versions_digest,
        signature_set_root=ZERO_ROOT_V0,
    )


def _tau(app_state: dict[str, object], *, position: int = 7) -> M6ProjectionContentObservationV1:
    result = project_tau_claimed_shared_spot_content_v1(
        app_state=app_state,
        claimed_app_hash=_app_hash(app_state),
        claimed_source_position=position,
    )
    assert type(result) is M6ProjectionContentObservationV1
    return result


def _ledger(app_state: dict[str, object]) -> M6ProjectionContentObservationV1:
    body = _body()
    result = project_zeno_ledger_header_shared_spot_content_v1(
        app_state=app_state,
        header=_header(body, post_state_root=_spot_state_root(app_state)),
        body=body,
    )
    assert type(result) is M6ProjectionContentObservationV1
    return result


def test_given_same_spot_content_when_two_structural_commitments_compare_then_receipt_is_content_only() -> (
    None
):
    app_state = _wrapped_zusd_state()
    tau = _tau(app_state, position=999_999)
    ledger = _ledger(app_state)
    parity = verify_tau_zeno_ledger_content_parity_v1(tau, ledger)
    assert type(parity) is M6ProjectionContentParityReceiptV1
    assert tau.source_kind is M6ProjectionSourceKindV1.TAU_CLAIMED_VIEW
    assert ledger.source_kind is M6ProjectionSourceKindV1.ZENO_LEDGER_HEADER_STATE_COMMITMENT
    assert tau.source_schema == TAU_APP_STATE_SCHEMA_V1
    assert ledger.source_schema == DEX_SNAPSHOT_SOURCE_SCHEMA_V1
    assert tau.content.canonical_source_bytes == canonical_json_bytes(app_state)
    assert ledger.content.canonical_source_bytes == canonical_json_bytes(app_state["dex_state"])
    assert tau.content.canonical_source_bytes != ledger.content.canonical_source_bytes
    assert tau.claimed_source_position == 999_999
    assert ledger.claimed_source_position == 7
    assert parity.global_gaps == M6_KNOWN_GLOBAL_PROJECTION_GAPS_V1
    assert parity.unmet_authority_obligations == M6_PROJECTION_AUTHORITY_OBLIGATIONS_V1
    assert is_verified_projection_content_parity_v1(parity)


def test_content_parity_cannot_authorize_global_state() -> None:
    app_state = _wrapped_zusd_state()
    parity = verify_tau_zeno_ledger_content_parity_v1(_tau(app_state), _ledger(app_state))
    result = require_authoritative_global_state_projection_v1(parity)
    assert type(result) is M6GlobalStateProjectionRejectV1
    assert result.code is M6GlobalStateProjectionRejectCodeV1.INCOMPLETE_GLOBAL_STATE
    assert result.global_gaps == M6_KNOWN_GLOBAL_PROJECTION_GAPS_V1
    assert result.unmet_obligations == M6_PROJECTION_AUTHORITY_OBLIGATIONS_V1


def test_tau_runtime_bare_state_encoding_is_admitted_as_bare_content() -> None:
    observation = _tau(_bare_state())
    assert observation.source_schema == DEX_SNAPSHOT_SOURCE_SCHEMA_V1
    assert M6ApplicationStateComponentV1.ACCOUNT_BALANCES in (
        observation.content.coverage.covered_components
    )
    assert M6ApplicationStateComponentV1.PROOF_MINING_STATE in (
        observation.content.coverage.missing_components
    )
    assert M6ApplicationStateComponentV1.ZUSD_MONETARY_STATE in (
        observation.content.coverage.missing_components
    )


def test_wrapped_null_null_state_is_rejected_as_noncanonical_tau_encoding() -> None:
    app_state = {
        "schema": "zenodex/tau_app_state/v1",
        "version": 1,
        "dex_state": _bare_state(),
        "proof_mining": None,
        "zusd_monetary": None,
    }
    result = project_tau_claimed_shared_spot_content_v1(
        app_state=app_state,
        claimed_app_hash=_app_hash(app_state),
        claimed_source_position=7,
    )
    assert type(result) is M6GlobalStateProjectionRejectV1
    assert result.code is M6GlobalStateProjectionRejectCodeV1.NON_CANONICAL_SOURCE


def test_economic_contradiction_remains_structural_content_and_blocks_authority() -> None:
    app_state = _wrapped_zusd_state(zusd_balance=1)
    observation = _tau(app_state)
    assert (
        M6ProjectionAuthorityObligationV1.GLOBAL_ECONOMIC_COHERENCE
        in observation.unmet_authority_obligations
    )
    parity = verify_tau_zeno_ledger_content_parity_v1(observation, _ledger(app_state))
    qualification = require_authoritative_global_state_projection_v1(parity)
    assert type(qualification) is M6GlobalStateProjectionRejectV1


def test_non_spot_zusd_difference_is_outside_parity_and_still_blocks_authority() -> None:
    tau_state = _wrapped_zusd_state(monetary_chain_id="zenodex/tau-zusd-context")
    ledger_state = _wrapped_zusd_state(monetary_chain_id="zenodex/ledger-zusd-context")
    tau = _tau(tau_state)
    ledger = _ledger(ledger_state)
    assert tau.source_state_root != ledger.source_state_root
    assert tau.content.content_root == ledger.content.content_root
    assert M6ApplicationStateComponentV1.ZUSD_MONETARY_STATE in (
        tau.content.coverage.missing_components
    )
    parity = verify_tau_zeno_ledger_content_parity_v1(tau, ledger)
    assert type(parity) is M6ProjectionContentParityReceiptV1
    qualification = require_authoritative_global_state_projection_v1(parity)
    assert type(qualification) is M6GlobalStateProjectionRejectV1
    assert qualification.code is M6GlobalStateProjectionRejectCodeV1.INCOMPLETE_GLOBAL_STATE


def test_self_consistent_unsigned_header_is_only_a_header_state_observation() -> None:
    observation = _ledger(_wrapped_zusd_state())
    assert (
        M6ProjectionAuthorityObligationV1.LEDGER_SELECTED_HEAD
        in observation.unmet_authority_obligations
    )
    assert (
        M6ProjectionAuthorityObligationV1.LEDGER_EXECUTION_ANCESTRY
        in observation.unmet_authority_obligations
    )


def test_observation_root_binds_source_position_while_content_root_does_not() -> None:
    app_state = _wrapped_zusd_state()
    first = _tau(app_state, position=7)
    second = _tau(app_state, position=8)
    assert first.content.content_root == second.content.content_root
    assert first.observation_root != second.observation_root


@pytest.mark.parametrize(
    "mutation",
    (
        lambda app: {**app, "surplus": 1},
        lambda app: {key: value for key, value in app.items() if key != "proof_mining"},
        lambda app: {**app, "schema": "zenodex/tau_app_state/v2"},
    ),
)
def test_malformed_wrapped_app_state_fails_closed(mutation: object) -> None:
    app_state = _wrapped_zusd_state()
    mutated = mutation(app_state)  # type: ignore[operator]
    result = project_tau_claimed_shared_spot_content_v1(
        app_state=mutated,
        claimed_app_hash=hashlib.sha256(canonical_json_bytes(mutated)).hexdigest(),
        claimed_source_position=7,
    )
    assert type(result) is M6GlobalStateProjectionRejectV1


def test_tau_claimed_hash_substitution_is_rejected() -> None:
    result = project_tau_claimed_shared_spot_content_v1(
        app_state=_wrapped_zusd_state(),
        claimed_app_hash="00" * 32,
        claimed_source_position=7,
    )
    assert type(result) is M6GlobalStateProjectionRejectV1
    assert result.code is M6GlobalStateProjectionRejectCodeV1.SOURCE_COMMITMENT_MISMATCH


def test_ledger_post_state_substitution_is_rejected() -> None:
    app_state = _wrapped_zusd_state()
    body = _body()
    result = project_zeno_ledger_header_shared_spot_content_v1(
        app_state=app_state,
        header=_header(body, post_state_root=_root("foreign-state")),
        body=body,
    )
    assert type(result) is M6GlobalStateProjectionRejectV1
    assert result.code is M6GlobalStateProjectionRejectCodeV1.SOURCE_COMMITMENT_MISMATCH


def test_crossed_ledger_body_is_rejected() -> None:
    app_state = _wrapped_zusd_state()
    body = _body()
    header = _header(body, post_state_root=_spot_state_root(app_state))
    result = project_zeno_ledger_header_shared_spot_content_v1(
        app_state=app_state,
        header=header,
        body={**body, "height": 8},
    )
    assert type(result) is M6GlobalStateProjectionRejectV1
    assert result.code is M6GlobalStateProjectionRejectCodeV1.INVALID_SOURCE


def test_different_content_does_not_receive_parity() -> None:
    result = verify_tau_zeno_ledger_content_parity_v1(
        _tau(_wrapped_zusd_state()),
        _ledger(_wrapped_zusd_state(zusd_balance=1)),
    )
    assert type(result) is M6GlobalStateProjectionRejectV1
    assert result.code is M6GlobalStateProjectionRejectCodeV1.PROJECTION_MISMATCH


def test_two_tau_observations_do_not_impersonate_cross_source_parity() -> None:
    tau = _tau(_wrapped_zusd_state())
    result = verify_tau_zeno_ledger_content_parity_v1(tau, tau)
    assert type(result) is M6GlobalStateProjectionRejectV1
    assert result.code is M6GlobalStateProjectionRejectCodeV1.SOURCE_LINEAGE_MISMATCH


def test_content_observation_and_parity_constructors_are_not_public_authority() -> None:
    app_state = _wrapped_zusd_state()
    tau = _tau(app_state)
    parity = verify_tau_zeno_ledger_content_parity_v1(tau, _ledger(app_state))
    assert type(parity) is M6ProjectionContentParityReceiptV1
    assert is_verified_application_content_v1(tau.content)
    assert is_verified_projection_content_observation_v1(tau)
    with pytest.raises(TypeError, match="source decoding"):
        replace(tau.content)
    with pytest.raises(TypeError, match="source admission"):
        replace(tau)
    with pytest.raises(TypeError, match="parity verifier"):
        replace(parity)


def test_hostile_post_construction_mutation_is_detected() -> None:
    app_state = _wrapped_zusd_state()
    tau = _tau(app_state)
    ledger = _ledger(app_state)
    object.__setattr__(tau.content, "content_root", _root("mutated"))
    result = verify_tau_zeno_ledger_content_parity_v1(tau, ledger)
    assert type(result) is M6GlobalStateProjectionRejectV1
    assert result.code is M6GlobalStateProjectionRejectCodeV1.INVALID_SOURCE


def test_boolean_claimed_position_is_rejected() -> None:
    app_state = _wrapped_zusd_state()
    result = project_tau_claimed_shared_spot_content_v1(
        app_state=app_state,
        claimed_app_hash=_app_hash(app_state),
        claimed_source_position=True,
    )
    assert type(result) is M6GlobalStateProjectionRejectV1
    assert result.code is M6GlobalStateProjectionRejectCodeV1.WRONG_EXACT_TYPE


def test_wrong_parity_input_cannot_reach_qualification() -> None:
    result = require_authoritative_global_state_projection_v1(M6ApplicationContentV1)
    assert result.code is M6GlobalStateProjectionRejectCodeV1.INVALID_SOURCE
