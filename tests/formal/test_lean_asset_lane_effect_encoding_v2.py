"""Retained bounded checks for frozen canonical effect-plan encoding.

The final harness pins a reviewed Lean source and compiles it on the existing
finite outcome/effect-plan closure.  Ten actual typed Python issue, burn,
transfer, and rejection plans are independently rendered as complete canonical
JSON bytes, then compared to direct finite Lean ``EffectPlan`` literals.
This is a bounded bridge.  It does not establish arbitrary serializer/runtime
equivalence, root or occurrence authority, or a nonempty external-outbox plan.
"""

from __future__ import annotations

import hashlib
import json
import re
import subprocess
from collections.abc import Callable
from dataclasses import dataclass, replace
from pathlib import Path
from typing import TypeVar

import pytest

from src.core.asset_transfer_module_v2 import transition_asset_transfer_v2
from src.core.asset_transfer_types_v2 import AssetClassV2, AssetTransferAcceptedV2
from src.core.global_settlement_effect_plan_v2 import GlobalEconomicEffectPlanV2
from src.core.global_settlement_effect_values_v2 import (
    AssetConservationRowV2,
    EconomicEffectRowV2,
    ExternalOutboxEnqueueV2,
    FeeConservationRowV2,
    LaneWriteV2,
)
from src.core.global_settlement_primitives_v2 import GLOBAL_SETTLEMENT_ABI_V2
from src.core.global_settlement_types_v2 import AssetSupplyV2, canonical_global_bytes_v2
from src.core.managed_asset_lifecycle_module_v2 import transition_managed_asset_lifecycle_v2
from src.core.managed_asset_lifecycle_result_v2 import (
    ManagedAssetLifecycleAcceptedV2,
    ManagedAssetLifecycleCommandV2,
    ManagedAssetLifecycleRejectedV2,
)
from src.core.managed_asset_lifecycle_state_v2 import (
    ManagedAssetLifecycleContextV2,
    ManagedAssetLifecyclePolicyV2,
    ManagedAssetLifecycleStateV2,
)
from tests.formal.test_lean_asset_lane_finite_effect_plan_v2 import _managed_context
from tests.formal.test_lean_asset_lane_finite_effect_plan_v2 import (
    effect_plan_lean as effect_plan_lean,
)
from tests.formal.test_lean_asset_transfer_finite_effect_plan_v2 import (
    transfer_effect_plan_lean as transfer_effect_plan_lean,
)
from tests.formal.test_lean_asset_transfer_finite_outcome_v2 import (
    AUTHORITY,
    GLOBAL,
    I128,
    ORIGIN,
    ROOT,
    U128,
    _command,
    _context,
    _state,
)
from tests.formal.test_lean_asset_transfer_finite_outcome_v2 import (
    transfer_consumer_lean as transfer_consumer_lean,
)
from tests.formal.test_lean_asset_transfer_finite_outcome_v2 import (
    transfer_outcome_lean as transfer_outcome_lean,
)
from tests.formal.test_lean_managed_asset_finite_outcome_v2 import (
    accounting_lean as accounting_lean,
)
from tests.formal.test_lean_managed_asset_finite_outcome_v2 import (
    byte_accounting_lean as byte_accounting_lean,
)
from tests.formal.test_lean_managed_asset_finite_outcome_v2 import (
    composition_lean as composition_lean,
)
from tests.formal.test_lean_managed_asset_finite_outcome_v2 import (
    finite_recomposition_lean as finite_recomposition_lean,
)
from tests.formal.test_lean_managed_asset_finite_outcome_v2 import lean as lean
from tests.formal.test_lean_managed_asset_finite_outcome_v2 import outcome_lean as outcome_lean
from tests.formal.test_lean_managed_asset_finite_outcome_v2 import (
    row_growth_lean as row_growth_lean,
)
from tests.formal.test_lean_managed_asset_finite_outcome_v2 import (
    shared_lean as shared_lean,
)
from tests.formal.test_lean_registered_supply_support_v1 import LeanSubject, _compile

PLAN_FIELD_ORDER = (
    "asset_conservation",
    "external_outbox_enqueue",
    "fee_conservation",
    "lane_writes",
    "occurrence_consumptions",
    "rows",
    "schema",
)
ROW_FIELD_ORDER = ("asset", "custody_domain", "delta_atoms", "kind", "principal")
ASSET_CONSERVATION_FIELD_ORDER = (
    "asset",
    "authorized_burn_atoms",
    "authorized_issue_atoms",
    "owned_and_custodied_post_atoms",
    "owned_and_custodied_pre_atoms",
    "supply_post_atoms",
    "supply_pre_atoms",
)
FEE_CONSERVATION_FIELD_ORDER = (
    "asset",
    "carried_residue_atoms",
    "current_allocations_atoms",
    "fee_charged_atoms",
)
LANE_WRITE_FIELD_ORDER = ("lane_id", "post_root", "pre_root")
RowT = TypeVar("RowT")

MODULE = "AssetLaneEffectEncodingV2"
NAMESPACE = f"Proofs.{MODULE}"
REPO_ROOT = Path(__file__).resolve().parents[2]
SOURCE = REPO_ROOT / "lean-mathlib" / "Proofs" / f"{MODULE}.lean"

# Frozen by the proof owner; the repo fixture additionally binds this exact
# source after integration before compiling any consumer.
SOURCE_SHA256 = "9c4968abd414d2156941fb00ba3ff61ad5f46c8ec994cc35b55e13b24398f924"

THEOREM_DECLARATIONS = (
    ("private", "digitChar_utf8Size"),
    ("private", "ofList_cons_byteSize"),
    ("private", "digitsCore_byteSize"),
    ("public", "nat_decimal_bytes_le"),
    ("public", "decimalBytes_nonnegative"),
    ("public", "decimalBytes_u128"),
    ("public", "decimalBytes_i128"),
    ("public", "effectRowBytes_length"),
    ("public", "assetConservationBytes_length"),
    ("public", "feeConservationBytes_length"),
    ("public", "laneWriteBytes_length"),
    ("public", "outboxBytes_length"),
    ("public", "planBytes_length"),
    ("public", "tokenCost_raw_bound"),
    ("public", "tokenCost_token_bound"),
    ("public", "tokenCost_root_bound"),
    ("public", "effect_kind_cost_bound"),
    ("public", "lane_id_cost_bound"),
    ("public", "effectRowBytes_bound"),
    ("public", "assetConservationBytes_bound"),
    ("public", "feeConservationBytes_bound"),
    ("public", "laneWriteBytes_bound"),
    ("public", "weight_bound"),
    ("public", "arrayBytes_bound"),
    ("public", "small_plan_bytes_bounded"),
    ("public", "managed_plan_bytes_bounded"),
    ("public", "transfer_plan_bytes_bounded"),
    ("public", "planBytes_empty"),
    ("public", "planBytes_empty_length"),
    ("public", "managed_rejected_bytes"),
    ("public", "transfer_rejected_bytes"),
)
PUBLIC_THEOREM_NAMES = (
    "Numeric.nat_decimal_bytes_le",
    "Numeric.decimalBytes_nonnegative",
    "Numeric.decimalBytes_u128",
    "Numeric.decimalBytes_i128",
    "effectRowBytes_length",
    "assetConservationBytes_length",
    "feeConservationBytes_length",
    "laneWriteBytes_length",
    "outboxBytes_length",
    "planBytes_length",
    "tokenCost_raw_bound",
    "tokenCost_token_bound",
    "tokenCost_root_bound",
    "effect_kind_cost_bound",
    "lane_id_cost_bound",
    "effectRowBytes_bound",
    "assetConservationBytes_bound",
    "feeConservationBytes_bound",
    "laneWriteBytes_bound",
    "weight_bound",
    "arrayBytes_bound",
    "small_plan_bytes_bounded",
    "managed_plan_bytes_bounded",
    "transfer_plan_bytes_bounded",
    "planBytes_empty",
    "planBytes_empty_length",
    "managed_rejected_bytes",
    "transfer_rejected_bytes",
)
STANDARD_AXIOMS = {"propext", "Quot.sound", "Classical.choice"}

OPEN_PREAMBLE = f"""open Proofs
open Proofs.GlobalSettlementCoreV2
open {NAMESPACE}
set_option warningAsError true
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
"""
PREAMBLE = f"import {NAMESPACE}\n{OPEN_PREAMBLE}"

# These direct public contracts cover the codec, its signed decimal endpoint,
# its exact empty encoding, and the two finite-construction byte bounds.  The
# declaration inventory and axiom audit below cover every public theorem.
PUBLIC_TYPES = {
    "Numeric.decimalBytes": "Int → B.Bytes",
    "effectRowBytes": "EconomicEffectRow → B.Bytes",
    "assetConservationBytes": "AssetConservationRow → B.Bytes",
    "feeConservationBytes": "FeeConservationRow → B.Bytes",
    "laneWriteBytes": "LaneWrite → B.Bytes",
    "outboxBytes": "ExternalOutboxEnqueue → B.Bytes",
    "planBytes": "EffectPlan → B.Bytes",
    "planBytes_length": "∀ plan : EffectPlan, (planBytes plan).length = planCost plan",
    "Numeric.decimalBytes_nonnegative": "∀ (n : Int), 0 ≤ n → Numeric.decimalBytes n = B.number n",
    "Numeric.decimalBytes_u128": "∀ (n : Int), FitsU128 n → (Numeric.decimalBytes n).length ≤ 39",
    "Numeric.decimalBytes_i128": "∀ (n : Int), FitsI128 n → (Numeric.decimalBytes n).length ≤ 40",
    "managed_plan_bytes_bounded": """∀ {digest : B.Bytes → String} {ctx : M.Context} {pre : FM.State}
      {command : M.Command}, FM.Structural pre → M.CommandWellFormed command →
        B.ValidToken command.accountOwner → RootObserverSyntax digest →
        (∀ occurrence, ctx.occurrence = some occurrence →
          NonzeroCanonicalRoot occurrence.occurrenceId) →
        (FM.transition digest ctx pre command).verdict = .accepted →
          (planBytes (Proofs.AssetLaneFiniteEffectPlanV2.managedPlan digest ctx pre command)).length ≤ 8192""",
    "transfer_plan_bytes_bounded": """∀ {digest : B.Bytes → String} {ctx : T.Context} {pre : FT.State}
      {command : T.Command}, FT.Structural pre → FT.CommandAdmission command →
        RootObserverSyntax digest →
        (∀ occurrence, ctx.occurrence = some occurrence →
          NonzeroCanonicalRoot occurrence.occurrenceId) →
        (FT.transition digest ctx pre command).verdict = .accepted →
          (planBytes (Proofs.AssetTransferFiniteEffectPlanV2.transferPlan digest ctx pre command)).length ≤ 8192""",
    "planBytes_empty": """planBytes EffectPlan.empty =
      B.raw \"{\\\"asset_conservation\\\":[],\\\"external_outbox_enqueue\\\":[],\\\"fee_conservation\\\":[],\\\"lane_writes\\\":[],\\\"occurrence_consumptions\\\":[],\\\"rows\\\":[],\\\"schema\\\":\\\"zenodex/global-settlement-abi/v2\\\"}\"""",
    "planBytes_empty_length": "(planBytes EffectPlan.empty).length = 176",
    "managed_rejected_bytes": """∀ {digest : B.Bytes → String} {ctx : M.Context} {pre : FM.State}
      {command : M.Command} {code : ManagedAssetFiniteOutcomeV2.RejectCode},
        (FM.transition digest ctx pre command).verdict = .rejected code →
          planBytes (Proofs.AssetLaneFiniteEffectPlanV2.managedPlan digest ctx pre command) = planBytes EffectPlan.empty""",
    "transfer_rejected_bytes": """∀ {digest : B.Bytes → String} {ctx : T.Context} {pre : FT.State}
      {command : T.Command} {code : AssetTransferFiniteOutcomeV2.RejectCode},
        (FT.transition digest ctx pre command).verdict = .rejected code →
          planBytes (Proofs.AssetTransferFiniteEffectPlanV2.transferPlan digest ctx pre command) = planBytes EffectPlan.empty""",
}

CORPUS_SHA256 = {
    "empty_rejection": "f9874930c0795050b6bd6c5408037eaa51b874e6f6acb5d6e500d4f01eeb8159",
    "managed_issue_from_zero": "2ea0b5a2c8cc90f1ac68e440556236368ab5013e31e0db64a82b99874f9367fb",
    "managed_full_burn": "6a8acec871adc53543694371707e396e4e1884ac365cb5efdc9f1df5e9621494",
    "transfer_fee_zero": "963cbca310f2af585b77cc6fdfe0684f62198446092f068c7302ec8032637ed9",
    "transfer_fee_distinct_collector": "df91ef996c135734191adb4ca574728e995e5ee17265bd4c74226618e7a72692",
    "transfer_fee_collector_sender": "608906976a6c1ea58cce7aedd6fbb9a04095d29878a59f579b82fcc7124a924d",
    "transfer_fee_collector_recipient": "d4519698514aa71b28065689e8f7a10886114239d9d487e59e34c86145c841ab",
    "transfer_escaped_max_tokens": "b79c51bd00f5f3a64e489f1582a839ab09617894a91701bc9c7ffd51212b4e0b",
    "transfer_i128_min_debit": "b764c694a0041387c569c244c1f5c47bdb2c4dbb04d6db28f179a0bb9e0ac745",
    "transfer_u128_max_supply": "e1e72e650f5ea815a962425cbf373dec17c0fc6ad74a4f031bd38f9a050062a9",
}


@dataclass(frozen=True)
class EncodingCase:
    name: str
    plan: GlobalEconomicEffectPlanV2


def _plan_wire(plan: GlobalEconomicEffectPlanV2) -> dict[str, object]:
    """Independent bounded wire oracle for every effect-plan field."""

    return {
        "schema": GLOBAL_SETTLEMENT_ABI_V2,
        "rows": [
            {
                "kind": row.kind.value,
                "principal": row.principal,
                "asset": row.asset,
                "custody_domain": row.custody_domain,
                "delta_atoms": row.delta_atoms,
            }
            for row in plan.rows
        ],
        "asset_conservation": [
            {
                "asset": row.asset,
                "owned_and_custodied_pre_atoms": row.owned_and_custodied_pre_atoms,
                "owned_and_custodied_post_atoms": row.owned_and_custodied_post_atoms,
                "supply_pre_atoms": row.supply_pre_atoms,
                "supply_post_atoms": row.supply_post_atoms,
                "authorized_issue_atoms": row.authorized_issue_atoms,
                "authorized_burn_atoms": row.authorized_burn_atoms,
            }
            for row in plan.asset_conservation
        ],
        "fee_conservation": [
            {
                "asset": row.asset,
                "fee_charged_atoms": row.fee_charged_atoms,
                "current_allocations_atoms": row.current_allocations_atoms,
                "carried_residue_atoms": row.carried_residue_atoms,
            }
            for row in plan.fee_conservation
        ],
        "lane_writes": [
            {
                "lane_id": row.lane_id.value,
                "pre_root": row.pre_root,
                "post_root": row.post_root,
            }
            for row in plan.lane_writes
        ],
        "occurrence_consumptions": list(plan.occurrence_consumptions),
        "external_outbox_enqueue": [
            {
                "effect_id": row.effect_id,
                "destination_id": row.destination_id,
                "payload_hash": row.payload_hash,
                "adapter_profile_root": row.adapter_profile_root,
            }
            for row in plan.external_outbox_enqueue
        ],
    }


def _oracle_bytes(plan: GlobalEconomicEffectPlanV2) -> bytes:
    return json.dumps(
        _plan_wire(plan), sort_keys=True, ensure_ascii=True, separators=(",", ":")
    ).encode("ascii")


def _managed_cases() -> tuple[EncodingCase, ...]:
    policy = ManagedAssetLifecyclePolicyV2(
        "A",
        AssetClassV2.REGISTERED_ORDINARY_TOKEN,
        ORIGIN,
        8,
        "issuer",
        AUTHORITY,
        AUTHORITY,
        True,
    )
    pre = ManagedAssetLifecycleStateV2(ROOT, (policy,), (), (AssetSupplyV2("A", 0),))
    issue = ManagedAssetLifecycleCommandV2(
        "managed_asset_issue",
        "A",
        AssetClassV2.REGISTERED_ORDINARY_TOKEN,
        ORIGIN,
        8,
        AUTHORITY,
        "alice",
        1,
    )
    rejected = transition_managed_asset_lifecycle_v2(
        ManagedAssetLifecycleContextV2(1, ROOT, GLOBAL, None), pre, issue
    )
    assert isinstance(rejected, ManagedAssetLifecycleRejectedV2)
    accepted_issue = transition_managed_asset_lifecycle_v2(_managed_context(issue), pre, issue)
    assert isinstance(accepted_issue, ManagedAssetLifecycleAcceptedV2)
    burn = replace(issue, command_kind="managed_asset_burn")
    accepted_burn = transition_managed_asset_lifecycle_v2(
        _managed_context(burn), accepted_issue.post_state, burn
    )
    assert isinstance(accepted_burn, ManagedAssetLifecycleAcceptedV2)
    return (
        EncodingCase("empty_rejection", rejected.effects),
        EncodingCase("managed_issue_from_zero", accepted_issue.effects),
        EncodingCase("managed_full_burn", accepted_burn.effects),
    )


def _transfer_cases() -> tuple[EncodingCase, ...]:
    escaped_sender = "s" + '"' * 159
    escaped_collector = "c" + '"' * 159
    escaped_recipient = "r" + "\\" * 159
    assert len(escaped_sender.encode("ascii")) == 160
    assert len(escaped_collector.encode("ascii")) == 160
    assert len(escaped_recipient.encode("ascii")) == 160
    assert I128 == (1 << 127) - 1
    assert U128 == (1 << 128) - 1
    vectors = (
        ("transfer_fee_zero", _state(5), _command(3)),
        ("transfer_fee_distinct_collector", _state(10, fee=2), _command(3)),
        (
            "transfer_fee_collector_sender",
            _state(5, fee=2, collector="sender"),
            _command(3),
        ),
        (
            "transfer_fee_collector_recipient",
            _state(5, fee=2, collector="recipient"),
            _command(3),
        ),
        (
            "transfer_escaped_max_tokens",
            _state(
                5,
                owner=escaped_sender,
                collector=escaped_collector,
                fee=2,
            ),
            _command(3, sender=escaped_sender, recipient=escaped_recipient),
        ),
        ("transfer_i128_min_debit", _state(I128 + 1, fee=1), _command(I128)),
        ("transfer_u128_max_supply", _state(U128, supply=U128), _command(I128)),
    )
    cases: list[EncodingCase] = []
    for name, state, command in vectors:
        result = transition_asset_transfer_v2(_context(command), state, command)
        assert isinstance(result, AssetTransferAcceptedV2), name
        cases.append(EncodingCase(name, result.effects))
    return tuple(cases)


def _corpus() -> tuple[EncodingCase, ...]:
    corpus = _managed_cases() + _transfer_cases()
    assert tuple(case.name for case in corpus) == tuple(CORPUS_SHA256)
    return corpus


def test_runtime_corpus_is_exact_complete_bytes() -> None:
    corpus = _corpus()
    assert len(corpus) == 10
    for case in corpus:
        actual = canonical_global_bytes_v2(case.plan)
        expected = _oracle_bytes(case.plan)
        assert actual == expected
        assert hashlib.sha256(actual).hexdigest() == CORPUS_SHA256[case.name]
        decoded = json.loads(actual)
        assert tuple(decoded) == PLAN_FIELD_ORDER
        assert all(tuple(row) == ROW_FIELD_ORDER for row in decoded["rows"])
        assert all(
            tuple(row) == ASSET_CONSERVATION_FIELD_ORDER for row in decoded["asset_conservation"]
        )
        assert all(
            tuple(row) == FEE_CONSERVATION_FIELD_ORDER for row in decoded["fee_conservation"]
        )
        assert all(tuple(row) == LANE_WRITE_FIELD_ORDER for row in decoded["lane_writes"])
        assert decoded["external_outbox_enqueue"] == []

    encoded = {case.name: _oracle_bytes(case.plan) for case in corpus}
    assert encoded["empty_rejection"] == (
        b'{"asset_conservation":[],"external_outbox_enqueue":[],"fee_conservation":[],'
        b'"lane_writes":[],"occurrence_consumptions":[],"rows":[],'
        b'"schema":"zenodex/global-settlement-abi/v2"}'
    )
    assert b'\\"' in encoded["transfer_escaped_max_tokens"]
    assert b"\\\\" in encoded["transfer_escaped_max_tokens"]


def test_oracle_distinguishes_missing_schema_reordered_fields_and_wrong_escape() -> None:
    corpus = {case.name: case for case in _corpus()}
    encoded = _oracle_bytes(corpus["transfer_escaped_max_tokens"].plan)
    missing_schema = _plan_wire(corpus["transfer_escaped_max_tokens"].plan)
    del missing_schema["schema"]
    assert (
        json.dumps(missing_schema, sort_keys=True, ensure_ascii=True, separators=(",", ":")).encode(
            "ascii"
        )
        != encoded
    )
    assert (
        json.dumps(
            _plan_wire(corpus["transfer_escaped_max_tokens"].plan),
            sort_keys=False,
            ensure_ascii=True,
            separators=(",", ":"),
        ).encode("ascii")
        != encoded
    )
    assert encoded.replace(b'\\"', b'"', 1) != encoded


@pytest.fixture(scope="module")
def effect_encoding_lean(transfer_effect_plan_lean: LeanSubject) -> LeanSubject:
    """Compile the frozen encoder as the next module in the finite closure."""

    assert re.fullmatch(r"[0-9a-f]{64}", SOURCE_SHA256), (
        "a frozen AssetLaneEffectEncodingV2 source SHA-256 is required"
    )
    source = SOURCE.read_bytes()
    assert hashlib.sha256(source).hexdigest() == SOURCE_SHA256
    path = transfer_effect_plan_lean.source / "Proofs" / f"{MODULE}.lean"
    path.write_bytes(source)
    result = _compile(
        transfer_effect_plan_lean,
        path,
        transfer_effect_plan_lean.library / "Proofs" / f"{MODULE}.olean",
    )
    assert result.returncode == 0, result.stdout + result.stderr
    assert result.stdout == result.stderr == ""
    return transfer_effect_plan_lean


def _consumer(subject: LeanSubject, name: str, body: str) -> subprocess.CompletedProcess[str]:
    path = subject.source / f"{name}.lean"
    path.write_text(PREAMBLE + body)
    return _compile(subject, path)


def _raw_consumer(subject: LeanSubject, name: str, source: str) -> subprocess.CompletedProcess[str]:
    path = subject.source / f"{name}.lean"
    path.write_text(source)
    return _compile(subject, path)


def _axiom_names(output: str) -> set[str]:
    return {
        item.strip()
        for group in re.findall(r"depends on axioms:\s*\[([^]]*)\]", output)
        for item in group.split(",")
        if item.strip()
    }


def test_axiom_parser_rejects_unexpected_axioms() -> None:
    parsed = _axiom_names("example depends on axioms: [sorryAx, unexpectedAxiom]")
    assert parsed == {"sorryAx", "unexpectedAxiom"}
    assert parsed - STANDARD_AXIOMS == {"sorryAx", "unexpectedAxiom"}


def test_frozen_encoding_surface_signatures_and_standard_axioms(
    effect_encoding_lean: LeanSubject,
) -> None:
    source = SOURCE.read_text()
    assert hashlib.sha256(source.encode()).hexdigest() == SOURCE_SHA256
    declared = tuple(
        ("private" if private else "public", name)
        for private, name in re.findall(r"^(private )?theorem\s+(\w+)", source, flags=re.MULTILINE)
    )
    assert declared == THEOREM_DECLARATIONS
    assert len(declared) == len({name for _, name in declared})
    assert tuple(name for visibility, name in declared if visibility == "public") == tuple(
        name.rsplit(".", 1)[-1] for name in PUBLIC_THEOREM_NAMES
    )
    assert len(PUBLIC_THEOREM_NAMES) == 28
    executable = re.sub(r"/\-.*?\-/", "", source, flags=re.DOTALL)
    assert (
        re.search(
            r"\b(?:sorry|sorryAx|admit|axiom|unsafe|native_decide|implemented_by)\b",
            executable,
        )
        is None
    )
    # A type ascription rejects a same-named declaration whose assumptions or
    # conclusion drift.  Compile each independently to keep large finite-plan
    # theorem elaboration within the retained fixture's bounded process budget.
    for index, (name, signature) in enumerate(PUBLIC_TYPES.items()):
        result = _consumer(
            effect_encoding_lean,
            f"AssetLaneEffectEncodingSignature{index}",
            f"example : {signature} := @{NAMESPACE}.{name}",
        )
        assert result.returncode == 0, result.stdout + result.stderr
        assert result.stdout == result.stderr == ""

    axiom_output: list[str] = []
    for start in range(0, len(PUBLIC_THEOREM_NAMES), 7):
        axiom_probes = "\n".join(
            f"#print axioms {NAMESPACE}.{name}" for name in PUBLIC_THEOREM_NAMES[start : start + 7]
        )
        result = _consumer(
            effect_encoding_lean,
            f"AssetLaneEffectEncodingAxioms{start}",
            axiom_probes,
        )
        assert result.returncode == 0, result.stdout + result.stderr
        assert result.stderr == ""
        axiom_output.append(result.stdout)

    output = "".join(axiom_output)
    reports = output.count("depends on axioms") + output.count("does not depend on any axioms")
    assert reports == len(PUBLIC_THEOREM_NAMES)
    assert _axiom_names(output) <= STANDARD_AXIOMS


_LEAN_EFFECT_KIND = {
    "ACCOUNT_MOVEMENT": ".accountMovement",
    "ISSUE": ".issue",
    "BURN": ".burn",
    "FEE_ALLOCATION": ".feeAllocation",
}
_LEAN_LANE_ID = {"ASSET_TRANSFER": ".assetTransfer"}


def _lean_string(value: str) -> str:
    return json.dumps(value, ensure_ascii=True)


def _lean_effect_row(row: EconomicEffectRowV2) -> str:
    return (
        f"⟨{_LEAN_EFFECT_KIND[row.kind.value]}, {_lean_string(row.principal)}, "
        f"{_lean_string(row.asset)}, {_lean_string(row.custody_domain)}, "
        f"{row.delta_atoms}⟩"
    )


def _lean_asset_conservation_row(row: AssetConservationRowV2) -> str:
    return (
        f"⟨{_lean_string(row.asset)}, {row.owned_and_custodied_pre_atoms}, "
        f"{row.owned_and_custodied_post_atoms}, {row.supply_pre_atoms}, "
        f"{row.supply_post_atoms}, {row.authorized_issue_atoms}, "
        f"{row.authorized_burn_atoms}⟩"
    )


def _lean_fee_conservation_row(row: FeeConservationRowV2) -> str:
    return (
        f"⟨{_lean_string(row.asset)}, {row.fee_charged_atoms}, "
        f"{row.current_allocations_atoms}, {row.carried_residue_atoms}⟩"
    )


def _lean_lane_write(row: LaneWriteV2) -> str:
    return (
        f"⟨{_LEAN_LANE_ID[row.lane_id.value]}, {_lean_string(row.pre_root)}, "
        f"{_lean_string(row.post_root)}⟩"
    )


def _lean_outbox_row(row: ExternalOutboxEnqueueV2) -> str:
    return (
        f"⟨{_lean_string(row.effect_id)}, {_lean_string(row.destination_id)}, "
        f"{_lean_string(row.payload_hash)}, {_lean_string(row.adapter_profile_root)}⟩"
    )


def _lean_list(rows: tuple[RowT, ...], render: Callable[[RowT], str]) -> str:
    return "[" + ", ".join(render(row) for row in rows) + "]"


def _lean_plan(plan: GlobalEconomicEffectPlanV2) -> str:
    """A direct finite carrier literal, independent of Lean transitions."""

    fields = (
        _lean_list(plan.rows, _lean_effect_row),
        _lean_list(plan.asset_conservation, _lean_asset_conservation_row),
        _lean_list(plan.fee_conservation, _lean_fee_conservation_row),
        _lean_list(plan.lane_writes, _lean_lane_write),
        "[" + ", ".join(_lean_string(root) for root in plan.occurrence_consumptions) + "]",
        _lean_list(plan.external_outbox_enqueue, _lean_outbox_row),
    )
    return "⟨" + ", ".join(fields) + "⟩"


CASE_PREAMBLE = f"""import {NAMESPACE}

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

open Proofs Proofs.GlobalSettlementCoreV2
open {NAMESPACE}

namespace IndependentEffectEncodingCases

def render (bytes : B.Bytes) : String :=
  String.intercalate \",\" (bytes.map (fun byte => toString byte.toNat))
"""


def _case_source(cases: tuple[EncodingCase, ...]) -> str:
    declarations: list[str] = []
    for index, case in enumerate(cases):
        declarations.extend(
            (
                f"def plan{index} : EffectPlan := {_lean_plan(case.plan)}",
                f"#eval IO.println (render (planBytes plan{index}))",
            )
        )
    return CASE_PREAMBLE + "\n\n".join(declarations) + "\nend IndependentEffectEncodingCases\n"


def _parse_byte_rows(output: str) -> list[bytes]:
    rows: list[bytes] = []
    for line in output.splitlines():
        assert line
        values = line.split(",")
        assert all(value.isdecimal() for value in values), line
        rows.append(bytes(int(value) for value in values))
    return rows


def test_actual_complete_python_plan_bytes_match_direct_lean_encoder(
    effect_encoding_lean: LeanSubject,
) -> None:
    corpus = _corpus()
    observed: list[tuple[str, bytes]] = []
    for start in range(0, len(corpus), 3):
        batch = corpus[start : start + 3]
        result = _raw_consumer(
            effect_encoding_lean,
            f"AssetLaneEffectEncodingCases{start}",
            _case_source(batch),
        )
        assert result.returncode == 0, result.stdout + result.stderr
        assert result.stderr == ""
        rows = _parse_byte_rows(result.stdout)
        assert len(rows) == len(batch)
        observed.extend((case.name, row) for case, row in zip(batch, rows, strict=True))

    assert tuple(name for name, _ in observed) == tuple(CORPUS_SHA256)
    for case, (_, actual) in zip(corpus, observed, strict=True):
        expected = _oracle_bytes(case.plan)
        assert actual == expected
        assert hashlib.sha256(actual).hexdigest() == CORPUS_SHA256[case.name]


NUMERIC_CONSUMER = r"""
namespace IndependentEffectEncodingNumbers

example : Numeric.decimalBytes (-10) = [45, 49, 48] := by decide +kernel
example : Numeric.decimalBytes 0 = [48] := by decide +kernel
example : Numeric.decimalBytes (2^128 - 1) =
    B.raw "340282366920938463463374607431768211455" := by decide +kernel
example : Numeric.decimalBytes (-(2^127)) =
    B.raw "-170141183460469231731687303715884105728" := by decide +kernel
example : Numeric.decimalBytes (2^127 - 1) =
    B.raw "170141183460469231731687303715884105727" := by decide +kernel
example : (Numeric.decimalBytes (10^38 - 1)).length = 38 := by decide +kernel
example : (Numeric.decimalBytes (10^38)).length = 39 := by decide +kernel

end IndependentEffectEncodingNumbers
"""


def test_signed_decimal_boundary_observations_are_exact(
    effect_encoding_lean: LeanSubject,
) -> None:
    result = _consumer(
        effect_encoding_lean,
        "AssetLaneEffectEncodingNumbers",
        NUMERIC_CONSUMER,
    )
    assert result.returncode == 0, result.stdout + result.stderr
    assert result.stdout == result.stderr == ""


RAW_NEGATIVE_PREAMBLE = f"""import {NAMESPACE}

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

open Proofs Proofs.GlobalSettlementCoreV2
open {NAMESPACE}
"""


def _semantic_false_control(subject: LeanSubject, name: str, body: str, fragment: str) -> None:
    result = _raw_consumer(subject, name, RAW_NEGATIVE_PREAMBLE + body)
    output = result.stdout + result.stderr
    assert result.returncode == 1, output
    assert result.stderr == ""
    assert result.stdout.count("error:") == 1, output
    assert fragment in output, output
    assert "Tactic `decide` proved that the proposition" in output
    assert "is false" in output
    assert "unknown module" not in output
    assert "unknown identifier" not in output
    assert "failed to synthesize" not in output


SEMANTIC_FALSE_CONTROLS = (
    (
        "AssetLaneEffectEncodingFalseMissingSchema",
        "example : planBytes EffectPlan.empty = B.raw "
        '"{\\"asset_conservation\\":[],\\"external_outbox_enqueue\\":[],\\"fee_conservation\\":[],'
        '\\"lane_writes\\":[],\\"occurrence_consumptions\\":[],\\"rows\\":[]}" := by\n'
        "  decide +kernel\n",
        "planBytes EffectPlan.empty",
    ),
    (
        "AssetLaneEffectEncodingFalseFieldOrder",
        "example : planBytes EffectPlan.empty = B.raw "
        '"{\\"rows\\":[],\\"asset_conservation\\":[],\\"external_outbox_enqueue\\":[],'
        '\\"fee_conservation\\":[],\\"lane_writes\\":[],\\"occurrence_consumptions\\":[],'
        '\\"schema\\":\\"zenodex/global-settlement-abi/v2\\"}" := by\n'
        "  decide +kernel\n",
        "planBytes EffectPlan.empty",
    ),
    (
        "AssetLaneEffectEncodingFalseQuoteEscape",
        "def quoted : EconomicEffectRow := "
        '⟨.accountMovement, "a\\"b", "A", "accounts", 1⟩\n'
        "example : effectRowBytes quoted = B.raw "
        '"{\\"asset\\":\\"A\\",\\"custody_domain\\":\\"accounts\\",\\"delta_atoms\\":1,'
        '\\"kind\\":\\"ACCOUNT_MOVEMENT\\",\\"principal\\":\\"a\\"b\\"}" := by\n'
        "  decide +kernel\n",
        "effectRowBytes quoted",
    ),
)


def test_missing_schema_changed_field_order_and_wrong_quote_escape_are_semantic_false_controls(
    effect_encoding_lean: LeanSubject,
) -> None:
    for name, body, fragment in SEMANTIC_FALSE_CONTROLS:
        _semantic_false_control(effect_encoding_lean, name, body, fragment)
