from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path

import pytest

from src.fire.compiler.compiler_registry_v1 import (
    _verify_fire_spec_runtime_compatibility,
    compile_fire_object,
    compile_fire_zpl_object,
    get_fire_compiler_entry,
    list_fire_compiler_entries,
    verify_fire_object_composition,
)
from src.fire.compiler.fmos_v1 import (
    FireMathObjectSpec,
    FireTermFieldSpec,
    build_fmos_manifest,
    render_fmos_object_card,
    verify_fmos_composition,
)
from src.fire.compiler.object_compiler_v1 import source_bound_expr
from src.fire.registry.object_manifest_v1 import FireContractProvenance, FireWitnessRequirement
from src.fire.verifier.cert_v1 import FireCertEnv, FireInterval


def test_list_fire_compiler_entries_exposes_all_supported_object_ids() -> None:
    object_ids = {entry.object_id for entry in list_fire_compiler_entries()}
    assert object_ids == {"burn_boost_call_v1", "fee_note_v1", "lp_loss_cover_v1"}


def test_compile_fire_object_compiles_burn_family_from_raw_terms() -> None:
    compiled = compile_fire_object(
        "burn_boost_call_v1",
        {
            "n_notional": 10,
            "strike_index": 4,
            "cap_index": 3,
            "source_upper": 9,
        },
    )

    assert compiled.object_name == "BurnBoostCall"
    assert build_fmos_manifest(compiled.spec, compiled.artifact).object_name == "BurnBoostCall"
    assert compiled.artifact.artifact_lower == 0
    assert compiled.artifact.artifact_upper == 30
    card = render_fmos_object_card(compiled.spec, compiled.artifact)
    assert "BurnBoostCall v1" in card
    assert "Instance gate claim evidence:" in card


def test_compile_fire_object_compiles_fee_family_from_raw_terms() -> None:
    compiled = compile_fire_object(
        "fee_note_v1",
        {
            "n_notional": 10,
            "cap_index": 7,
            "source_upper": 2,
        },
    )

    assert compiled.object_name == "FeeNote"
    assert build_fmos_manifest(compiled.spec, compiled.artifact).object_name == "FeeNote"
    assert compiled.artifact.artifact_lower == 0
    assert compiled.artifact.artifact_upper == 20


def test_compile_fire_object_compiles_lp_family_from_raw_terms() -> None:
    compiled = compile_fire_object(
        "lp_loss_cover_v1",
        {
            "n_notional": 2,
            "deductible": 5,
            "cap_amount": 40,
            "hodl_lower": 30,
            "hodl_upper": 80,
            "lpv_lower": 10,
            "lpv_upper": 60,
        },
    )

    assert compiled.object_name == "LPLossCover"
    assert build_fmos_manifest(compiled.spec, compiled.artifact).object_name == "LPLossCover"
    assert compiled.artifact.artifact_lower == 0
    assert compiled.artifact.artifact_upper == 80


def test_compile_fire_object_rejects_missing_fields() -> None:
    with pytest.raises(ValueError, match="missing FIRE term fields"):
        compile_fire_object(
            "burn_boost_call_v1",
            {
                "n_notional": 10,
                "strike_index": 4,
                "cap_index": 3,
            },
        )


def test_compile_fire_object_rejects_extra_fields() -> None:
    with pytest.raises(ValueError, match="unexpected FIRE term fields"):
        compile_fire_object(
            "fee_note_v1",
            {
                "n_notional": 10,
                "cap_index": 7,
                "source_upper": 2,
                "extra": 1,
            },
        )


def test_get_fire_compiler_entry_rejects_unknown_object_id() -> None:
    with pytest.raises(KeyError, match="unsupported FIRE object_id"):
        get_fire_compiler_entry("unknown")


def test_verify_fire_object_composition_rejects_unit_mismatch() -> None:
    producer = compile_fire_object(
        "burn_boost_call_v1",
        {
            "n_notional": 10,
            "strike_index": 4,
            "cap_index": 3,
            "source_upper": 9,
        },
    )

    ok, err = verify_fire_object_composition(
        producer=producer,
        consumer_object_id="fee_note_v1",
        consumer_raw_terms={
            "n_notional": 10,
            "cap_index": 7,
            "source_upper": 20,
        },
        bindings={"settlement_payoff": "fee_final"},
    )

    assert ok is False
    assert err == "composition_unit_mismatch:settlement_payoff:fee_final"


@dataclass(frozen=True)
class _SyntheticTerms:
    source_upper: int


@dataclass(frozen=True)
class _SyntheticArtifact:
    terms: _SyntheticTerms
    artifact_lower: int
    artifact_upper: int


def _synthetic_spec(
    *,
    object_id: str,
    source_name: str,
    output_name: str,
    source_upper: int,
    source_contracts: dict[str, FireContractProvenance] | None = None,
    witness_contracts: dict[str, FireContractProvenance] | None = None,
    witness_name: str | None = None,
) -> tuple[FireMathObjectSpec, _SyntheticTerms]:
    terms = _SyntheticTerms(source_upper=source_upper)
    spec = FireMathObjectSpec(
        object_id=object_id,
        object_name=object_id,
        cli_help=object_id,
        object_version="v1",
        object_family="synthetic",
        settlement_asset="zUSD",
        payoff_summary="synthetic source passthrough",
        ir_hash="sha256:" + ("a" if object_id == "producer" else "b") * 64,
        term_fields=(
            FireTermFieldSpec(
                name="source_upper",
                description="synthetic upper bound",
                unit="Amount[zUSD]",
                minimum=0,
                maximum=1000,
            ),
        ),
        source_units={source_name: "Amount[zUSD]"},
        source_interfaces={},
        source_contracts={} if source_contracts is None else source_contracts,
        output_units={output_name: "Amount[zUSD]"},
        primary_output_unit="Amount[zUSD]",
        terms_type=_SyntheticTerms,
        artifact_type=object,
        expression_builder=lambda _: source_bound_expr(source_name),
        certificate_env_builder=lambda local_terms: FireCertEnv(
            exact_values={},
            source_bounds={source_name: FireInterval(lower=0, upper=local_terms.source_upper)},
        ),
        source_interval_builder=lambda local_terms: {source_name: FireInterval(lower=0, upper=local_terms.source_upper)},
        output_interval_builder=lambda local_terms: {output_name: FireInterval(lower=0, upper=local_terms.source_upper)},
        compile_state=lambda _: None,
        compiled_state_from_artifact=lambda _: None,
        witness_builder=lambda _: ()
        if witness_name is None
        else (
            FireWitnessRequirement(
                name=witness_name,
                freshness="1 block",
                lower=0,
                upper=terms.source_upper,
                contract=(
                    None
                    if witness_contracts is None or witness_name not in witness_contracts
                    else witness_contracts[witness_name]
                ),
            ),
        ),
        witness_contracts={} if witness_contracts is None else witness_contracts,
    )
    return spec, terms


def test_verify_fmos_composition_accepts_subset_bound_guarantee() -> None:
    producer_spec, producer_terms = _synthetic_spec(
        object_id="producer",
        source_name="producer_input",
        output_name="producer_output",
        source_upper=30,
    )
    consumer_spec, consumer_terms = _synthetic_spec(
        object_id="consumer",
        source_name="consumer_source",
        output_name="consumer_output",
        source_upper=50,
    )

    ok, err = verify_fmos_composition(
        producer_spec=producer_spec,
        producer_terms=producer_terms,
        consumer_spec=consumer_spec,
        consumer_terms=consumer_terms,
        bindings={"producer_output": "consumer_source"},
    )

    assert ok is True
    assert err is None


def test_verify_fire_spec_runtime_compatibility_detects_source_contract_provenance_mismatch() -> None:
    source_spec, source_terms = _synthetic_spec(
        object_id="synthetic_contract_source",
        source_name="index_final",
        output_name="settlement_payoff",
        source_upper=9,
        source_contracts={"index_final": FireContractProvenance(name="source_contract", role="source:index_final")},
    )
    canonical_spec, canonical_terms = _synthetic_spec(
        object_id="synthetic_contract_source",
        source_name="index_final",
        output_name="settlement_payoff",
        source_upper=9,
        source_contracts={"index_final": FireContractProvenance(name="canonical_contract", role="source:index_final")},
    )

    ok, err = _verify_fire_spec_runtime_compatibility(
        source_spec=source_spec,
        source_artifact=_SyntheticArtifact(terms=source_terms, artifact_lower=0, artifact_upper=9),
        canonical_spec=canonical_spec,
        canonical_artifact=_SyntheticArtifact(terms=canonical_terms, artifact_lower=0, artifact_upper=9),
    )

    assert ok is False
    assert err == "source_contract_provenance_mismatch"


def test_verify_fire_spec_runtime_compatibility_detects_witness_contract_provenance_mismatch() -> None:
    source_spec, source_terms = _synthetic_spec(
        object_id="synthetic_contract_witness",
        source_name="index_final",
        output_name="settlement_payoff",
        source_upper=9,
        witness_name="Witness[X]",
        witness_contracts={"Witness[X]": FireContractProvenance(name="source_witness_contract", role="witness:Witness[X]")},
    )
    canonical_spec, canonical_terms = _synthetic_spec(
        object_id="synthetic_contract_witness",
        source_name="index_final",
        output_name="settlement_payoff",
        source_upper=9,
        witness_name="Witness[X]",
        witness_contracts={"Witness[X]": FireContractProvenance(name="canonical_witness_contract", role="witness:Witness[X]")},
    )

    ok, err = _verify_fire_spec_runtime_compatibility(
        source_spec=source_spec,
        source_artifact=_SyntheticArtifact(terms=source_terms, artifact_lower=0, artifact_upper=9),
        canonical_spec=canonical_spec,
        canonical_artifact=_SyntheticArtifact(terms=canonical_terms, artifact_lower=0, artifact_upper=9),
    )

    assert ok is False
    assert err == "witness_contract_provenance_mismatch"


def test_compile_fire_zpl_object_compiles_canonical_burn_source() -> None:
    repo_root = Path(__file__).resolve().parents[2]
    compiled = compile_fire_zpl_object(
        repo_root / "src" / "kernels" / "zpl" / "burn_boost_call_v1.zpl",
        {
            "n_notional": 10,
            "strike_index": 4,
            "cap_index": 3,
            "source_upper": 9,
        },
    )

    assert compiled.object_id == "burn_boost_call_v1"
    assert compiled.artifact.artifact_upper == 30


def test_compile_fire_zpl_object_accepts_semantically_equivalent_burn_source(tmp_path: Path) -> None:
    repo_root = Path(__file__).resolve().parents[2]
    source_text = (repo_root / "src" / "kernels" / "zpl" / "burn_boost_call_v1.zpl").read_text(encoding="utf-8")
    equivalent_source = tmp_path / "burn_boost_call_v1_equiv.zpl"
    equivalent_source.write_text(
        source_text.replace(
            "positive_part(sub(source_bound(burn_final), exact_param(strike_index)))",
            "max(sub(source_bound(burn_final), exact_param(strike_index)), const(0))",
        ),
        encoding="utf-8",
    )

    compiled = compile_fire_zpl_object(
        equivalent_source,
        {
            "n_notional": 10,
            "strike_index": 4,
            "cap_index": 3,
            "source_upper": 9,
        },
    )

    assert compiled.object_id == "burn_boost_call_v1"
    assert compiled.artifact.artifact_upper == 30


def test_compile_fire_zpl_object_rejects_drift_from_canonical_spec(tmp_path: Path) -> None:
    repo_root = Path(__file__).resolve().parents[2]
    source_text = (repo_root / "src" / "kernels" / "zpl" / "burn_boost_call_v1.zpl").read_text(encoding="utf-8")
    drifted_source = tmp_path / "burn_boost_call_v1_drifted.zpl"
    drifted_source.write_text(
        source_text.replace("summary \"N * min(max(BurnIndex_T - K, 0), Cap)\";", "summary \"drifted\";", 1),
        encoding="utf-8",
    )

    with pytest.raises(
        ValueError,
        match=r"line 7, col 1 .*compiled ZPL source is runtime-incompatible for burn_boost_call_v1: static_spec_mismatch:payoff_summary",
    ):
        compile_fire_zpl_object(
            drifted_source,
            {
                "n_notional": 10,
                "strike_index": 4,
                "cap_index": 3,
                "source_upper": 9,
            },
        )


def test_compile_fire_zpl_object_reports_named_contract_drift_at_contract_span(tmp_path: Path) -> None:
    repo_root = Path(__file__).resolve().parents[2]
    source_text = (repo_root / "src" / "kernels" / "zpl" / "burn_boost_call_v1.zpl").read_text(encoding="utf-8")
    contract_source = source_text.replace(
        "contract burn_contract Index const:0 term:source_upper;",
        "contract burn_contract Index const:1 term:source_upper;",
        1,
    )
    drifted_source = tmp_path / "burn_boost_call_v1_contract_drifted.zpl"
    drifted_source.write_text(contract_source, encoding="utf-8")

    with pytest.raises(
        ValueError,
        match=r"line 13, col 1 .*compiled ZPL source is runtime-incompatible for burn_boost_call_v1: source_requirements_mismatch:contract",
    ) as exc_info:
        compile_fire_zpl_object(
            drifted_source,
            {
                "n_notional": 10,
                "strike_index": 4,
                "cap_index": 3,
                "source_upper": 9,
            },
        )
    assert (
        "[contract burn_contract for import burn_final <- burn_index_v1.burn_final -> "
        "expected producer guarantee burn_index_v1.burn_final for burn_final: Index in [0, 9]]"
    ) in str(exc_info.value)


def test_compile_fire_zpl_object_preserves_named_contract_provenance_in_manifest(tmp_path: Path) -> None:
    repo_root = Path(__file__).resolve().parents[2]
    source_text = (repo_root / "src" / "kernels" / "zpl" / "burn_boost_call_v1.zpl").read_text(encoding="utf-8")
    source_file = tmp_path / "burn_boost_call_v1_contract_ok.zpl"
    source_file.write_text(source_text, encoding="utf-8")

    compiled = compile_fire_zpl_object(
        source_file,
        {
            "n_notional": 10,
            "strike_index": 4,
            "cap_index": 3,
            "source_upper": 9,
        },
    )
    manifest = build_fmos_manifest(compiled.spec, compiled.artifact)

    assert manifest.imported_interfaces[0].contract == FireContractProvenance(
        name="burn_contract",
        role="import:burn_index_v1.burn_final",
    )
    assert manifest.witnesses[0].contract == FireContractProvenance(
        name="burn_contract",
        role="witness:BurnCertificate[TDEX]",
    )


def test_compile_fire_zpl_object_reports_named_witness_contract_drift_at_contract_span(tmp_path: Path) -> None:
    repo_root = Path(__file__).resolve().parents[2]
    source_text = (repo_root / "src" / "kernels" / "zpl" / "burn_boost_call_v1.zpl").read_text(encoding="utf-8")
    contract_source = source_text.replace(
        'contract burn_contract Index const:0 term:source_upper;\nimport burn_final burn_index_v1 burn_final contract:burn_contract;\nwitness "BurnCertificate[TDEX]" "1 epoch" contract:burn_contract;',
        'contract burn_contract Index const:0 term:source_upper;\ncontract witness_contract Index const:1 term:source_upper;\nimport burn_final burn_index_v1 burn_final contract:burn_contract;\nwitness "BurnCertificate[TDEX]" "1 epoch" contract:witness_contract;',
        1,
    )
    drifted_source = tmp_path / "burn_boost_call_v1_witness_contract_drifted.zpl"
    drifted_source.write_text(contract_source, encoding="utf-8")

    with pytest.raises(
        ValueError,
        match=r"line 14, col 1 .*compiled ZPL source is runtime-incompatible for burn_boost_call_v1: witness_contract_provenance_mismatch",
    ) as exc_info:
        compile_fire_zpl_object(
            drifted_source,
            {
                "n_notional": 10,
                "strike_index": 4,
                "cap_index": 3,
                "source_upper": 9,
            },
        )
    assert (
        "[contract witness_contract for witness BurnCertificate[TDEX] -> "
        "expected contract provenance burn_contract role witness:BurnCertificate[TDEX] for BurnCertificate[TDEX]]"
    ) in str(exc_info.value)
