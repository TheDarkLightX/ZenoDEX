"""Connected margin V2: universal Lean derivation plus finite Python correspondence.

``Proofs/PerpsMarginGlobalV2.lean`` derives the joint asset/margin/global
outcome of one margin command from the existing account kernel
(``PerpsMarginTransitionV1.stepMarket``) and the proved claim episode
(``PerpsMarginClaimsV2.advance``), and shows that the constructed successor,
effect plan and terminal plan satisfy every field of the shared
``GlobalEconomicStateRefinementV2.Verified`` relation. The typed consumer below
pins those theorem statements and their axioms.

The finite gate feeds the actual Python producer's inputs to the Lean
reference. Opaque digests (lane roots, global root, command body hash, claim
identifier) are supplied to Lean as finite tables of the runtime's own hashes,
so agreement covers the explicitly encoded economic abstraction. Origin and
managed policies, transfer-fee metadata, full outbox records, input statements
and refinement bindings are not all represented in that abstraction. Separate
Python checks retain their frame and binding obligations; ambiguous abstract
digest keys fail the gate. This is finite correspondence on the scenario family
below; it is not complete byte equivalence or universal source refinement. Python/Rust
parity for the same producer is the separate ``test_perps_margin_global_rust_v2``
gate. Canonical bytes, hashing, authentication, receipts, the origin-registry
binding and publication remain outside both the model and this gate.

Only the five Std-only source modules are compiled, into a fresh temporary
tree, with the installed pinned compiler. No Lake build, cache or network.
"""

from __future__ import annotations

import hashlib
import importlib.util
import json
import sys
import types
from dataclasses import dataclass, replace
from pathlib import Path
from typing import Any, TypeAlias

import pytest

from src.core.asset_lane_custody_coordinator_v2 import (
    AssetLaneCustodyAcceptedV2,
    transition_asset_lane_custody_v2,
)
from src.core.asset_lane_custody_global_v2 import derive_asset_lane_custody_global_post_v2
from src.core.asset_lane_custody_state_v2 import AssetLaneCustodyStateV2
from src.core.asset_lane_state_v2 import AssetLaneContextV2
from src.core.asset_transfer_types_v2 import AssetClassV2, AssetTransferStateV2
from src.core.global_economic_proof_v2 import EconomicCommandOccurrenceV2
from src.core.global_economic_state_v2 import GlobalEconomicStateV2, LaneStateRootV2
from src.core.global_settlement_types_v2 import (
    ALL_LANE_IDS_V2,
    MAX_ATOMS_V2,
    MAX_DELTA_ATOMS_V2,
    MAX_U64_V2,
    ZERO_ROOT_V2,
    AssetSupplyV2,
    EconomicAmountV2,
    LaneIdV2,
    TerminalObligationStatusV2,
    TerminalObligationV2,
    hash_economic_command_body_v2,
    hash_global_v2,
)
from src.core.perps_margin_global_v2 import (
    PerpsMarginGlobalAcceptedV2,
    PerpsMarginGlobalRejectedV2,
    PerpsMarginOracleV2,
    transition_perps_margin_global_v2,
)
from src.core.perps_margin_state_v2 import PerpsMarginStateV2, margin_claim_id_v2
from src.core.perps_margin_types_v1 import (
    PerpsMarginAccountStatusV1,
    PerpsMarginCommandV1,
    PerpsMarginStateV1,
)
from tests.core.test_asset_lane_coordinator_v2 import (
    _managed_policy,
    _registry,
    _root,
    _transfer_command,
    _transfer_policy,
)
from tests.core.test_asset_lane_custody_v2 import custody_state
from tests.core.test_perps_margin_global_v2 import (
    CLOSE,
    DEPOSIT,
    WITHDRAW,
    _command,
    _initial,
    _occurrence,
)
from tests.core.test_perps_margin_module_v1 import _state
from tests.formal.lean_stdlib_gate_v1 import (
    FORBIDDEN_SOURCE_TOKENS,
    LEAN_PROJECT,
    TheoremReference,
    _check_axioms,
    _pinned_lean_executable,
    _run,
)

ROOT = Path(__file__).resolve().parents[2]
NS = "ZenoDEX.PerpsMarginGlobalV2"
MODULES = (
    "Proofs.GlobalSettlementCoreV2",
    "Proofs.GlobalEconomicStateRefinementV2",
    "Proofs.PerpsMarginTransitionV1",
    "Proofs.PerpsMarginClaimsV2",
    "Proofs.PerpsMarginGlobalV2",
)
PRELUDE = """import Proofs.PerpsMarginGlobalV2
open Proofs.GlobalSettlementCoreV2
open Proofs.GlobalEconomicStateRefinementV2
open ZenoDEX.PerpsMarginTransitionV1 (Account Command MarketState lookupAccount putAccount stepMarket)
open ZenoDEX.PerpsMarginGlobalV2
"""
REFERENCES = tuple(TheoremReference(f"{NS}.{name}", kind) for name, kind in (
    ("accepted_verified", """∀ (d : Digests) (pre : Joint) (r : Request) (acc : Accepted),
      Invariant d pre → step d pre r = .ok acc →
      (d.marginRoot acc.post.margin = d.marginRoot pre.margin → acc.post.margin = pre.margin) →
      Verified (view d pre.frame) acc.effects acc.terminalPlan ⟨[]⟩ [r.occurrence.shared]
        (view d acc.post.frame)"""),
    ("accepted_global_witness", """∀ (d : Digests) (pre : Joint) (r : Request) (acc : Accepted),
      Invariant d pre → step d pre r = .ok acc →
      (d.marginRoot acc.post.margin = d.marginRoot pre.margin → acc.post.margin = pre.margin) →
      ∃ global : Proofs.GlobalEconomicStateRefinementV2.Accepted (view d pre.frame),
        global.post = view d acc.post.frame ∧ global.effects = acc.effects ∧
        global.terminalPlan = acc.terminalPlan ∧ global.oraclePlan = ⟨[]⟩ ∧
        global.occurrences = [r.occurrence.shared]"""),
    ("economic_facts", """∀ (pre : Joint) (r : Request) (market : MarketState),
      stepMarket (economicContext pre r) pre.margin.market r.command = .ok market →
      ∃ b, EconomicFacts pre r market b"""),
    ("advanceClaims_correspond", """∀ (pre : Joint), MarginAdmitted pre.margin → ∀ (b : Account)
      (fresh : Identifier),
      (advanceClaims pre.margin.market.asset pre.margin.bindings pre.frame.terminals b fresh).map
          (fun pair => claimsView
            ⟨{ pre.margin.market with accounts := putAccount b pre.margin.market.accounts },
              pair.1⟩ pair.2) =
        ZenoDEX.PerpsMarginClaimsV2.advance (claimsView pre.margin pre.frame.terminals) b fresh"""),
    ("invariant_wellFormed", """∀ (d : Digests) (state : Joint), Invariant d state →
      ZenoDEX.PerpsMarginClaimsV2.WellFormed (claimsView state.margin state.frame.terminals)"""),
    ("liabilities_le_custody_total", """∀ (L C : List AmountRow) (a : Asset),
      (∀ r ∈ C, 0 ≤ r.amountAtoms) →
      (∀ dm, amountForAssetDomain L a dm ≤ amountForAssetDomain C a dm) →
      amountForAsset L a ≤ amountForAsset C a"""),
    ("rejected_is_exact_noop", """∀ (d : Digests) (pre : Joint) (r : Request) (code : Reject),
      step d pre r = .error code → advanceMargin d pre r = pre"""),
    ("invariant_preserved", """∀ (d : Digests) (pre : Joint) (r : Request) (acc : Accepted),
      Invariant d pre → step d pre r = .ok acc → Invariant d acc.post"""),
    ("frame_invariant", """∀ (d : Digests) (pre : Joint) (u : FrameUpdate) (post : Joint),
      Invariant d pre → frameStep d pre u = some post → Invariant d post"""),
    ("run_invariant", """∀ (d : Digests) (inputs : List Input) (start : Joint),
      Invariant d start → Invariant d (run d inputs start)"""),
    ("inactive_terminal_history", """∀ (d : Digests) (inputs : List Input) (start : Joint),
      Invariant d start → ∀ (id : Identifier) (old : TerminalObligation),
      terminalLookup start.frame.terminals id = some old → old.status ≠ .open →
      terminalLookup (run d inputs start).frame.terminals id = some old"""),
    ("closed_account_history", """∀ (d : Digests) (inputs : List Input) (start : Joint) (a : Account),
      lookupAccount a.id start.margin.market.accounts = some a → a.closed = true →
      lookupAccount a.id (run d inputs start).margin.market.accounts = some a"""),
    ("capacity_keeps_lifecycle", """∀ (d : Digests) (pre : Joint) (r : Request) (acc : Accepted),
      Invariant d pre → pre.frame.terminals.length = globalRowCeiling →
      step d pre r = .ok acc → acc.post.frame.terminals.length = globalRowCeiling"""),
    ("refill_blocked_at_capacity", """∀ (d : Digests) (pre : Joint) (r : Request) (acc : Accepted),
      Invariant d pre → pre.frame.terminals.length = globalRowCeiling →
      bindingOf pre.margin.bindings r.command.accountId = none → r.command.kind = .deposit →
      step d pre r ≠ .ok acc"""),
    ("Scenario.history_accepted", """[(step Scenario.digests (Scenario.stage 0)
        (Scenario.request 1 .deposit "acc-a" 25 1)).toBool,
      (step Scenario.digests (Scenario.stage 1) (Scenario.request 2 .deposit "acc-b" 25 1)).toBool,
      (step Scenario.digests (Scenario.stage 2) (Scenario.request 3 .withdraw "acc-a" 10 2)).toBool,
      (step Scenario.digests (Scenario.stage 3) (Scenario.request 4 .withdraw "acc-a" 15 3)).toBool,
      (frameStep Scenario.digests (Scenario.stage 4) (Scenario.transfer 5)).isSome,
      (step Scenario.digests (Scenario.stage 5) (Scenario.request 6 .deposit "acc-a" 20 4)).toBool,
      (step Scenario.digests (Scenario.stage 6) (Scenario.request 7 .withdraw "acc-a" 20 5)).toBool,
      (step Scenario.digests (Scenario.stage 7) (Scenario.request 8 .close "acc-a" 0 6)).toBool] =
      List.replicate 8 true"""),
    ("Scenario.start_invariant", "Invariant Scenario.digests Scenario.start"),
    ("Scenario.final_invariant", "Invariant Scenario.digests Scenario.final"),
    ("Scenario.closed_reopen_rejected", """step Scenario.digests (Scenario.stage 8)
        (Scenario.request 9 .deposit "acc-a" 1 7) = .error (.margin .accountClosed) ∧
      Scenario.final = Scenario.stage 8"""),
    ("Scenario.same_owner_accounts_distinct", """(Scenario.stage 2).margin.bindings =
        [⟨"acc-a", "cacc-ao1"⟩, ⟨"acc-b", "cacc-bo2"⟩] ∧
      (Scenario.stage 2).frame.custody =
        [⟨"acc-a", Scenario.usd, marginDomain, 25⟩, ⟨"acc-b", Scenario.usd, marginDomain, 25⟩] ∧
      (Scenario.stage 2).frame.liabilities = [⟨"alice", Scenario.usd, marginDomain, 50⟩] ∧
      (Scenario.stage 2).margin.market.accounts.map Account.nonce = [1, 1]"""),
    ("Scenario.unauthorized_conserving_movement_rejected", """step Scenario.digests (Scenario.stage 2) Scenario.steal =
        .error (.margin .unauthorizedSubject) ∧
      advanceMargin Scenario.digests (Scenario.stage 2) Scenario.steal = Scenario.stage 2 ∧
      step Scenario.digests (Scenario.stage 2) Scenario.foreignOwner =
        .error (.margin .accountOwnerMismatch)"""),
    ("Scenario.changed_tables_with_old_asset_root_rejected", """step Scenario.digests Scenario.changedAssetsOnly
          (Scenario.request 3 .withdraw "acc-a" 10 2) = .error .projectionMismatch ∧
      step Scenario.digests Scenario.changedFrameOnly (Scenario.request 3 .withdraw "acc-a" 10 2) =
        .error .projectionMismatch ∧
      step Scenario.digests Scenario.changedBoth (Scenario.request 3 .withdraw "acc-a" 10 2) =
        .error .projectionMismatch"""),
    ("Scenario.width_neighbors", """(step Scenario.digests Scenario.bigStart
        (Scenario.request 1 .deposit "acc-a" (2 ^ 127 - 1) 1)).toBool = true ∧
      step Scenario.digests Scenario.bigStart (Scenario.request 1 .deposit "acc-a" (2 ^ 127) 1) =
        .error (.margin .effectDeltaOverflow) ∧
      step Scenario.digests Scenario.start (Scenario.request 1 .deposit "acc-a" 101 1) =
        .error .insufficientBalance ∧
      step Scenario.digests Scenario.topStart Scenario.topRequest = .error .occurrenceContextMismatch"""),
    ("Scenario.drained_claims_immutable", """terminalLookup Scenario.final.frame.terminals "cacc-ao1" =
        some ⟨"cacc-ao1", .perpsMarket, "alice", Scenario.usd, marginDomain, 15, .drained⟩ ∧
      terminalLookup Scenario.final.frame.terminals "cacc-ao6" =
        some ⟨"cacc-ao6", .perpsMarket, "alice", Scenario.usd, marginDomain, 20, .drained⟩"""),
    ("Scenario.omitted_owner_aggregation_fails_projection", """¬ MarginProjection Scenario.digests (Scenario.stage 2).margin
        { (Scenario.stage 2).frame with liabilities :=
          [⟨"acc-a", Scenario.usd, marginDomain, 25⟩, ⟨"acc-b", Scenario.usd, marginDomain, 25⟩] } ∧
      ¬ MarginProjection Scenario.digests (Scenario.stage 2).margin
        { (Scenario.stage 2).frame with liabilities := [⟨"alice", Scenario.usd, marginDomain, 25⟩] }"""),
    ("Scenario.refill_with_reused_claim_rejected", """step { Scenario.digests with claimId := fun _ _ _ => "cacc-ao1" }
        (Scenario.stage 5) (Scenario.request 6 .deposit "acc-a" 20 4) = .error .successorRejected"""),
    ("Scenario.rejection_consumes_nothing", """advance Scenario.digests (Scenario.stage 8)
          (.margin (Scenario.request 9 .deposit "acc-a" 1 7)) = Scenario.stage 8 ∧
      (Scenario.stage 8).margin.market.accounts.map Account.nonce = [6, 1] ∧
      (Scenario.stage 8).frame.replay.length = 8 ∧ Scenario.consumedMutant ≠ Scenario.stage 8"""),
))
LANES = {
    "ASSET_TRANSFER": "assetTransfer", "SPOT_LIQUIDITY": "spotLiquidity",
    "FARM_INCENTIVES": "farmIncentives", "ZDEX_TOKENOMICS": "zdexTokenomics",
    "ZUSD_MONETARY": "zusdMonetary", "PERPS_MARKET": "perpsMarket", "ORACLE_MARKET": "oracleMarket",
    "SEALED_AUCTION": "sealedAuction", "STRATEGY_ESCROW": "strategyEscrow",
    "PROOF_REWARDS": "proofRewards", "EXTERNAL_CUSTODY": "externalCustody",
    "GOVERNANCE_MIGRATION": "governanceMigration",
}
KINDS = {DEPOSIT: "deposit", WITHDRAW: "withdraw", CLOSE: "close"}
GLOBAL_CODES = {
    "OCCURRENCE_CONTEXT_MISMATCH": ".occurrenceContextMismatch",
    "REPLAY_ALREADY_CONSUMED": ".replayAlreadyConsumed",
    "OCCURRENCE_COMMAND_MISMATCH": ".occurrenceCommandMismatch",
    "PROJECTION_MISMATCH": ".projectionMismatch",
    "UNKNOWN_COLLATERAL": ".unknownCollateral",
    "DISABLED_COLLATERAL": ".disabledCollateral",
    "UNSUPPORTED_COLLATERAL": ".unsupportedCollateral",
    "INSUFFICIENT_BALANCE": ".insufficientBalance",
    "SUCCESSOR_REJECTED": ".successorRejected",
}
MARGIN_CODES = {
    code: f".margin .{name}" for code, name in zip(
        (
            "RELEASE_MISMATCH UNKNOWN_COMMAND HALTED_MARKET MARKET_DRAIN_ONLY MARKET_MISMATCH "
            "ASSET_MISMATCH UNAUTHORIZED_SUBJECT UNEXPECTED_ORACLE_AUTHORITY ACCOUNT_MISSING "
            "ACCOUNT_LIMIT ACCOUNT_OWNER_MISMATCH ACCOUNT_CLOSED NONCE_OVERFLOW NONCE_MISMATCH "
            "ORACLE_AUTHORITY_MISSING ORACLE_PRICE_MISMATCH INVALID_CLOSE_AMOUNT POSITION_OPEN "
            "COLLATERAL_REMAINS ZERO_AMOUNT EFFECT_DELTA_OVERFLOW BALANCE_OVERFLOW "
            "INSUFFICIENT_COLLATERAL ARITHMETIC_OVERFLOW MAINTENANCE_BREACH"
        ).split(),
        (
            "releaseMismatch unknownCommand haltedMarket marketDrainOnly marketMismatch "
            "assetMismatch unauthorizedSubject unexpectedOracleAuthority accountMissing "
            "accountLimit accountOwnerMismatch accountClosed nonceOverflow nonceMismatch "
            "oracleAuthorityMissing oraclePriceMismatch invalidCloseAmount positionOpen "
            "collateralRemains zeroAmount effectDeltaOverflow balanceOverflow "
            "insufficientCollateral arithmeticOverflow maintenanceBreach"
        ).split(),
        strict=True,
    )
}


@dataclass(frozen=True)
class Compiled:
    executable: Path
    directory: Path
    artifacts: dict[str, list[str]]
    source_hashes: dict[str, str]


def _setup(path: Path, module: str, artifacts: dict[str, list[str]]) -> Path:
    path.write_text(json.dumps({
        "name": module, "package?": None, "isModule": False, "imports?": None,
        "importArts": artifacts, "dynlibs": [], "plugins": [], "options": {},
    }), encoding="utf-8")
    return path


@pytest.fixture(scope="module")
def compiled(tmp_path_factory: pytest.TempPathFactory) -> Compiled:
    directory = tmp_path_factory.mktemp("lean-perps-global-v2")
    executable = _pinned_lean_executable()
    artifacts: dict[str, list[str]] = {}
    hashes: dict[str, str] = {}
    for module in MODULES:
        relative = Path(*module.split(".")).with_suffix(".lean")
        source = (LEAN_PROJECT / relative).read_bytes()
        assert not FORBIDDEN_SOURCE_TOKENS.search(source.decode()), module
        captured = directory / relative
        captured.parent.mkdir(parents=True, exist_ok=True)
        captured.write_bytes(source)
        output = captured.with_suffix(".olean")
        setup = _setup(directory / f"{relative.stem}.json", module, artifacts)
        result = _run(executable, ["-DwarningAsError=true", "-R", str(directory),
            "--setup", str(setup), "-o", str(output), str(captured)], cwd=directory)
        assert not result.stdout and not result.stderr, module
        artifacts[module] = [str(output)]
        hashes[module] = hashlib.sha256(source).hexdigest()
    return Compiled(executable, directory, artifacts, hashes)


def _probe(compiled: Compiled, name: str, source: str) -> list[str]:
    path = compiled.directory / f"{name}.lean"
    path.write_text(PRELUDE + source, encoding="utf-8")
    setup = _setup(path.with_suffix(".json"), name, compiled.artifacts)
    result = _run(compiled.executable, ["-DwarningAsError=true", "-R", str(compiled.directory),
        "--setup", str(setup), str(path)], cwd=compiled.directory)
    assert not result.stderr, result.stderr
    return result.stdout.splitlines()


def test_connected_theorems_have_independent_types_and_standard_axioms(compiled):
    source = "\n".join(
        f"example : {ref.type_expression} := @{ref.qualified_name}\n"
        f"#print axioms {ref.qualified_name}" for ref in REFERENCES
    )
    output = _probe(compiled, "TheoremConsumer", source)
    _check_axioms("\n".join(output), REFERENCES)


# --- Lean literal encoders -------------------------------------------------


def _text(value: str) -> str:
    return json.dumps(value)


def _amount(row: EconomicAmountV2) -> str:
    return f"⟨{_text(row.owner)}, {_text(row.asset)}, {_text(row.custody_domain)}, {row.amount_atoms}⟩"


def _amounts(rows) -> str:
    return "[" + ", ".join(_amount(row) for row in rows) + "]"


def _supplies(rows) -> str:
    return "[" + ", ".join(f"⟨{_text(row.asset)}, {row.amount_atoms}⟩" for row in rows) + "]"


def _terminal(row: TerminalObligationV2) -> str:
    return (f"⟨{_text(row.obligation_id)}, .{LANES[row.lane_id.value]}, {_text(row.claimant)}, "
            f"{_text(row.asset)}, {_text(row.liability_domain)}, {row.amount_atoms}, "
            f".{row.status.value.lower()}⟩")


def _terminals(rows) -> str:
    return "[" + ", ".join(_terminal(row) for row in rows) + "]"


def _assets_literal(assets: AssetLaneCustodyStateV2) -> str:
    leaf = assets.transfer_state
    policies = ", ".join(
        f"⟨{_text(p.asset)}, {str(p.enabled).lower()}, "
        f"{str(p.asset_class is AssetClassV2.TAU_NATIVE_COIN).lower()}, {p.atom_decimals}⟩"
        for p in leaf.policies
    )
    return (f"(⟨{_text(leaf.module_release_id)}, [{policies}], {_amounts(leaf.balances)}, "
            f"{_supplies(leaf.supplies)}, {_amounts(assets.custody)}⟩ : Assets)")


def _account(a) -> str:
    closed = str(a.status is PerpsMarginAccountStatusV1.CLOSED).lower()
    return (f"⟨{_text(a.account_id)}, {_text(a.owner)}, ({a.position_base}), {a.entry_price_e8}, "
            f"{a.collateral_atoms}, {a.nonce}, {closed}⟩")


def _market_literal(m: PerpsMarginStateV1) -> str:
    status = {"ACTIVE": "active", "DRAIN_ONLY": "drainOnly", "HALTED": "halted"}[m.market_status.value]
    accounts = ", ".join(f"({_account(a)} : Account)" for a in m.accounts)
    return (f"(⟨{_text(m.module_release_id)}, {_text(m.market_id)}, {_text(m.collateral_asset)}, "
            f"{m.index_price_e8}, {m.maintenance_margin_bps}, {m.depeg_buffer_bps}, "
            f"{m.max_position_abs}, .{status}, ([{accounts}] : List Account)⟩ : MarketState)")


def _margin_literal(margin: PerpsMarginStateV2) -> str:
    bindings = ", ".join(f"⟨{_text(b.account_id)}, {_text(b.obligation_id)}⟩" for b in margin.active_claims)
    return f"(⟨{_market_literal(margin.economic_state)}, [{bindings}]⟩ : Margin)"


def _frame_literal(state: GlobalEconomicStateV2) -> str:
    lanes = ", ".join(
        f"⟨.{LANES[row.lane_id.value]}, {_text(row.module_release_id)}, {str(row.enabled).lower()}, "
        f"{_text(row.state_root)}⟩" for row in state.lane_roots
    )
    oracles = ", ".join(
        f"⟨{_text(o.oracle_id)}, {_text(o.occurrence_root)}, {o.observed_height}, "
        f"{'.finalized' if o.finalized else '.pending'}⟩" for o in state.oracle_occurrences
    )
    replay = ", ".join(f"⟨{_text(r.replay_id)}, {_text(r.occurrence_id)}⟩" for r in state.replay_state)
    outbox = ", ".join(_text(row.effect_id) for row in state.outbox)
    return (f"(⟨{_text(state.chain_id)}, {_text(state.deployment_root)}, {state.writer_epoch}, "
            f"{state.height}, {_text(state.profile_root)}, [{lanes}], {_amounts(state.balances)}, "
            f"{_supplies(state.supplies)}, {_amounts(state.custody)}, {_amounts(state.liabilities)}, "
            f"{_amounts(state.reserves)}, [{oracles}], [{replay}], {_terminals(state.terminal_obligations)}, "
            f"{_text(state.history_root)}, [{outbox}]⟩ : Frame)")


def _joint_literal(assets, margin, state) -> str:
    return f"(⟨{_assets_literal(assets)}, {_margin_literal(margin)}, {_frame_literal(state)}⟩ : Joint)"


def _command_literal(c: PerpsMarginCommandV1) -> str:
    kind = KINDS.get(c.command_kind, "unknown")
    return (f"(⟨.{kind}, {_text(c.account_id)}, {_text(c.market_id)}, {_text(c.owner)}, "
            f"{_text(c.asset)}, {c.amount_atoms}, {c.nonce}⟩ : Command)")


def _occurrence_literal(o: EconomicCommandOccurrenceV2, command: PerpsMarginCommandV1) -> str:
    kind = KINDS.get(o.command_kind, "unknown")
    consumed = ", ".join(_text(item) for item in o.consumed_object_ids)
    return (f"(⟨{_text(o.occurrence_id)}, {_text(o.replay_id)}, {_text(o.chain_id)}, "
            f"{_text(o.deployment_root)}, {_text(o.profile_root)}, {_text(o.pre_state_root)}, {o.height}, "
            f"{_text(o.subject_id)}, .{kind}, {_text(o.command_body_hash)}, [{consumed}]⟩ : Occurrence)")


def _request_literal(command, occurrence, oracle) -> str:
    oracle_literal = "none" if oracle is None else f"some ⟨{oracle.price_e8}⟩"
    return f"(⟨{_command_literal(command)}, {_occurrence_literal(occurrence, command)}, {oracle_literal}⟩ : Request)"


def _effects_literal(effects) -> str:
    kinds = {
        "ACCOUNT_MOVEMENT": "accountMovement", "ISSUE": "issue", "BURN": "burn", "CUSTODY": "custody",
        "LIABILITY": "liability", "RESERVE": "reserve", "FEE_ALLOCATION": "feeAllocation",
        "REWARD": "reward", "SLASH": "slash",
    }
    rows = ", ".join(
        f"⟨.{kinds[r.kind.value]}, {_text(r.principal)}, {_text(r.asset)}, {_text(r.custody_domain)}, "
        f"({r.delta_atoms})⟩" for r in effects.rows
    )
    conservation = ", ".join(
        f"⟨{_text(r.asset)}, {r.owned_and_custodied_pre_atoms}, {r.owned_and_custodied_post_atoms}, "
        f"{r.supply_pre_atoms}, {r.supply_post_atoms}, {r.authorized_issue_atoms}, {r.authorized_burn_atoms}⟩"
        for r in effects.asset_conservation
    )
    assert effects.fee_conservation == () and effects.external_outbox_enqueue == ()
    writes = ", ".join(
        f"⟨.{LANES[w.lane_id.value]}, {_text(w.pre_root)}, {_text(w.post_root)}⟩" for w in effects.lane_writes
    )
    consumptions = ", ".join(_text(item) for item in effects.occurrence_consumptions)
    return f"(⟨[{rows}], [{conservation}], [], [{writes}], [{consumptions}], []⟩ : EffectPlan)"


def _terminal_plan_literal(plan) -> str:
    deltas = ", ".join(
        f"⟨{_text(d.obligation_id)}, "
        + ("none" if d.pre_obligation is None else f"some {_terminal(d.pre_obligation)}")
        + f", {_terminal(d.post_obligation)}⟩" for d in plan.deltas
    )
    return f"(⟨[{deltas}]⟩ : TerminalPlan)"


# --- The scenario family ----------------------------------------------------


Inputs: TypeAlias = tuple[AssetLaneCustodyStateV2, PerpsMarginStateV2, GlobalEconomicStateV2]
Outcome: TypeAlias = PerpsMarginGlobalAcceptedV2 | PerpsMarginGlobalRejectedV2


@dataclass(frozen=True)
class MarginCase:
    name: str
    inputs: Inputs
    command: PerpsMarginCommandV1
    occurrence: EconomicCommandOccurrenceV2
    oracle: PerpsMarginOracleV2 | None
    result: Outcome


@dataclass(frozen=True)
class FrameCase:
    name: str
    inputs: Inputs
    accepted: AssetLaneCustodyAcceptedV2
    occurrence: EconomicCommandOccurrenceV2
    post_state: GlobalEconomicStateV2


def _digest_rows(name: str, entries) -> str:
    """An abstract input must identify one digest, independent of table order."""

    known: dict[str, str] = {}
    for literal, root in entries:
        assert literal not in known or known[literal] == root, f"ambiguous {name} digest"
        known[literal] = root
    return ", ".join(f"({literal}, {_text(root)})" for literal, root in known.items())


def _check_runtime_bindings(case: MarginCase) -> None:
    """Complement the Lean abstraction with exact retained runtime bindings."""

    assets, _, state = case.inputs
    result = case.result
    if isinstance(result, PerpsMarginGlobalRejectedV2):
        assert result.pre_state_root == result.post_state_root == state.state_root
        assert result.effects.is_empty and not result.terminal_plan.deltas
        assert not result.oracle_plan.deltas
        return
    post_assets, post = result.post_assets, result.post_state
    assert post_assets.origin_registry == assets.origin_registry
    assert post_assets.managed_policies == assets.managed_policies
    assert post_assets.transfer_state.policies == assets.transfer_state.policies
    assert post.outbox == state.outbox
    assert result.refinement.pre_state_root == state.state_root
    assert result.statement_root == hash_global_v2("perps-margin-global-statement-v2", {
        "schema": "zenodex/perps-margin-global-input/v2",
        "pre_state_root": state.state_root,
        "command": case.command,
        "occurrence": case.occurrence,
        "oracle": case.oracle,
    })


class Family:
    """Derive every case once from the actual producers; retain digests."""

    def __init__(self) -> None:
        self.cases: list[MarginCase | FrameCase] = []
        self.asset_roots: dict[str, AssetLaneCustodyStateV2] = {}
        self.margin_roots: dict[str, PerpsMarginStateV2] = {}
        self.frame_roots: dict[str, GlobalEconomicStateV2] = {}
        self.body_hashes: dict[str, PerpsMarginCommandV1] = {}
        self.claim_ids: dict[str, tuple[PerpsMarginStateV1, str, str]] = {}

    def _remember(self, assets, margin, state) -> None:
        self.asset_roots[assets.state_root] = assets
        self.margin_roots[margin.state_root] = margin
        self.frame_roots[state.state_root] = state

    def margin(self, name: str, inputs: Inputs, command: PerpsMarginCommandV1, outer_nonce: int,
               expected: str, *, occurrence: EconomicCommandOccurrenceV2 | None = None,
               oracle: PerpsMarginOracleV2 | None = None) -> Inputs:
        assets, margin, state = inputs
        occurrence = _occurrence(state, command, outer_nonce) if occurrence is None else occurrence
        before = (assets.state_root, margin.state_root, state.state_root)
        result = transition_perps_margin_global_v2(assets, margin, state, command, occurrence, oracle)
        assert (assets.state_root, margin.state_root, state.state_root) == before, name
        self._remember(assets, margin, state)
        self.body_hashes[hash_economic_command_body_v2(command.command_kind, command)] = command
        self.claim_ids[margin_claim_id_v2(margin.economic_state, command.account_id, occurrence.occurrence_id)] = (
            margin.economic_state, command.account_id, occurrence.occurrence_id,
        )
        successor: Inputs
        if expected == "ACCEPTED":
            assert isinstance(result, PerpsMarginGlobalAcceptedV2), (name, result)
            self._remember(result.post_assets, result.post_margin, result.post_state)
            successor = (result.post_assets, result.post_margin, result.post_state)
        else:
            assert isinstance(result, PerpsMarginGlobalRejectedV2), (name, result)
            assert result.code.value == expected, (name, result.code.value)
            assert result.pre_state_root == result.post_state_root == state.state_root, name
            assert result.effects.is_empty and not result.terminal_plan.deltas, name
            successor = inputs
        case = MarginCase(name, inputs, command, occurrence, oracle, result)
        _check_runtime_bindings(case)
        self.cases.append(case)
        return successor

    def transfer(self, name: str, inputs: Inputs, amount: int, outer_nonce: int) -> Inputs:
        assets, margin, state = inputs
        command = _transfer_command(amount_atoms=amount)
        occurrence = EconomicCommandOccurrenceV2(
            state.chain_id, state.deployment_root, state.height + 1, 0, 0, command.command_kind,
            command.command_body_hash, _root("asset-route"), "alice", _root("grant"), outer_nonce,
            state.profile_root, state.state_root, (),
        )
        context = AssetLaneContextV2(state.writer_epoch, assets.transfer_state.module_release_id,
                                     state.state_root, occurrence)
        accepted = transition_asset_lane_custody_v2(context, assets, command)
        assert type(accepted) is AssetLaneCustodyAcceptedV2, name
        post = derive_asset_lane_custody_global_post_v2(assets, accepted, state, occurrence)
        assert post.terminal_obligations == state.terminal_obligations
        self._remember(assets, margin, state)
        self._remember(accepted.post_state, margin, post)
        self.cases.append(FrameCase(name, inputs, accepted, occurrence, post))
        return accepted.post_state, margin, post

    def digests_literal(self) -> str:
        assets = _digest_rows("asset", ((_assets_literal(a), root) for root, a in self.asset_roots.items()))
        margins = _digest_rows("margin", ((_margin_literal(m), root) for root, m in self.margin_roots.items()))
        frames = _digest_rows("frame", ((_frame_literal(f), root) for root, f in self.frame_roots.items()))
        bodies = _digest_rows("body", ((_command_literal(c), h) for h, c in self.body_hashes.items()))
        claims = _digest_rows("claim", (
            (f"({_market_literal(m)}, {_text(account)}, {_text(occurrence)})", claim)
            for claim, (m, account, occurrence) in self.claim_ids.items()
        ))
        return f"""
def lookupTable {{α : Type}} [DecidableEq α] (table : List (α × String)) (x : α) : String :=
  ((table.find? (fun pair => decide (pair.1 = x))).map (·.2)).getD "unknown-root"
def assetTable : List (Assets × String) := [{assets}]
def marginTable : List (Margin × String) := [{margins}]
def frameTable : List (Frame × String) := [{frames}]
def bodyTable : List (Command × String) := [{bodies}]
def claimTable : List ((MarketState × String × String) × String) := [{claims}]
def d : Digests := ⟨lookupTable assetTable, lookupTable marginTable, lookupTable frameTable,
  lookupTable bodyTable, fun m a o => lookupTable claimTable (m, a, o)⟩
"""


def _expected_literal(case: MarginCase) -> str:
    result = case.result
    if isinstance(result, PerpsMarginGlobalRejectedV2):
        code = result.code.value
        return f".error ({GLOBAL_CODES[code]})" if code in GLOBAL_CODES else f".error ({MARGIN_CODES[code]})"
    assert isinstance(result, PerpsMarginGlobalAcceptedV2)
    post = _joint_literal(result.post_assets, result.post_margin, result.post_state)
    return f".ok (⟨{post}, {_effects_literal(result.effects)}, {_terminal_plan_literal(result.terminal_plan)}⟩ : Accepted)"


def _case_check(case: MarginCase | FrameCase) -> str:
    if isinstance(case, FrameCase):
        assets, margin, state = case.inputs
        leaf = case.accepted.post_state.transfer_state
        update = (f"(⟨{_amounts(leaf.balances)}, {_supplies(leaf.supplies)}, "
                  f"{_occurrence_literal(case.occurrence, _command(DEPOSIT, 0, 0))}⟩ : FrameUpdate)")
        expected = _joint_literal(case.accepted.post_state, margin, case.post_state)
        return f"#eval decide (frameStep d {_joint_literal(assets, margin, state)} {update} = some {expected})"
    assets, margin, state = case.inputs
    return (f"#eval decide (step d {_joint_literal(assets, margin, state)} "
            f"{_request_literal(case.command, case.occurrence, case.oracle)} = {_expected_literal(case)})")


def _large_balance_initial():
    assets = custody_state(accounts=MAX_ATOMS_V2, custody=0)
    margin = PerpsMarginStateV2(replace(_state(), collateral_asset="USD"), ())
    roots = {
        LaneIdV2.ASSET_TRANSFER: (assets.transfer_state.module_release_id, assets.state_root),
        LaneIdV2.PERPS_MARKET: (margin.economic_state.module_release_id, margin.state_root),
    }
    state = GlobalEconomicStateV2(
        "margin-test", _root("deployment"), 7, 0, _root("profile"),
        tuple(LaneStateRootV2(
            lane, roots.get(lane, (_root(lane.value), ZERO_ROOT_V2))[0],
            lane in roots, roots.get(lane, (None, ZERO_ROOT_V2))[1],
        ) for lane in ALL_LANE_IDS_V2),
        balances=assets.transfer_state.balances,
        supplies=assets.transfer_state.supplies,
    )
    return assets, margin, state


def _policy_variant_initial(*, enabled: bool):
    transfer, managed = _transfer_policy(), _managed_policy()
    if not enabled:
        transfer = replace(transfer, enabled=False)
    leaf = AssetTransferStateV2(
        _root("module-release"), (transfer,),
        (EconomicAmountV2("alice", "USD", "accounts", 100),), (AssetSupplyV2("USD", 100),),
    )
    assets = AssetLaneCustodyStateV2(leaf, _registry((transfer,), (managed,)), (managed,), ())
    _, margin, base = _initial()
    roots = tuple(
        replace(row, module_release_id=leaf.module_release_id, state_root=assets.state_root)
        if row.lane_id is LaneIdV2.ASSET_TRANSFER else row for row in base.lane_roots
    )
    return assets, margin, replace(base, lane_roots=roots)


def build_family() -> Family:
    family = Family()
    # A. the connected history: deposit, partial, drain, transfer, refill, drain, close, reopen
    inputs = _initial()
    for name, kind, amount, nonce in (("deposit", DEPOSIT, 40, 1), ("partial", WITHDRAW, 10, 2),
                                      ("drain", WITHDRAW, 30, 3)):
        inputs = family.margin(f"history/{name}", inputs, _command(kind, amount, nonce), nonce, "ACCEPTED")
    inputs = family.transfer("history/transfer", inputs, 5, 4)
    for name, kind, amount, nonce, outer in (("refill", DEPOSIT, 20, 4, 5), ("drain-again", WITHDRAW, 20, 5, 6),
                                             ("close", CLOSE, 0, 6, 7)):
        inputs = family.margin(f"history/{name}", inputs, _command(kind, amount, nonce), outer, "ACCEPTED")
    family.margin("history/reopen", inputs, _command(DEPOSIT, 1, 7), 8, "ACCOUNT_CLOSED")
    # B. same-owner accounts, replay reuse, exact rejection repeat
    inputs = family.margin("owner/deposit-a", _initial(), _command(DEPOSIT, 25, 1), 1, "ACCEPTED")
    inputs = family.margin("owner/deposit-b-nonce-one", inputs, _command(DEPOSIT, 25, 1, "margin-b"), 2, "ACCEPTED")
    withdraw = _command(WITHDRAW, 25, 2)
    family.margin("owner/replay-reuse", inputs, withdraw, 2, "REPLAY_ALREADY_CONSUMED")
    family.margin("owner/replay-reuse-repeat", inputs, withdraw, 2, "REPLAY_ALREADY_CONSUMED")
    inputs = family.margin("owner/drain-a", inputs, withdraw, 3, "ACCEPTED")
    inputs = family.margin("owner/refill-a", inputs, _command(DEPOSIT, 7, 3), 4, "ACCEPTED")
    family.margin("owner/drain-b", inputs, _command(WITHDRAW, 25, 2, "margin-b"), 5, "ACCEPTED")
    # C. ordered rejections and stale frames
    base = _initial()
    command = _command(DEPOSIT, 1, 1)
    occurrence = _occurrence(base[2], command, 1)
    for field, value, code in (
        ("pre_state_root", _root("stale"), "OCCURRENCE_CONTEXT_MISMATCH"),
        ("chain_id", "foreign-chain", "OCCURRENCE_CONTEXT_MISMATCH"),
        ("profile_root", _root("wrong-profile"), "OCCURRENCE_CONTEXT_MISMATCH"),
        ("height", 2, "OCCURRENCE_CONTEXT_MISMATCH"),
        ("command_body_hash", _root("wrong-body"), "OCCURRENCE_COMMAND_MISMATCH"),
        ("consumed_object_ids", ("foreign-object",), "OCCURRENCE_COMMAND_MISMATCH"),
        ("subject_id", "mallory", "UNAUTHORIZED_SUBJECT"),
    ):
        family.margin(f"reject/{field}", base, command, 1, code, occurrence=replace(occurrence, **{field: value}))
    wrong_kind = replace(occurrence, command_kind="perps_margin_withdraw")
    family.margin("reject/kind", base, command, 1, "OCCURRENCE_COMMAND_MISMATCH", occurrence=wrong_kind)
    for amount, code in ((0, "ZERO_AMOUNT"), (101, "INSUFFICIENT_BALANCE"),
                         (MAX_DELTA_ATOMS_V2 + 1, "EFFECT_DELTA_OVERFLOW")):
        family.margin(f"reject/deposit-{amount}", base, _command(DEPOSIT, amount, 1), 1, code)
    family.margin("reject/nonce", base, _command(DEPOSIT, 1, 2), 1, "NONCE_MISMATCH")
    family.margin("reject/missing-withdraw", base, _command(WITHDRAW, 1, 1), 1, "ACCOUNT_MISSING")
    family.margin("reject/close-missing", base, _command(CLOSE, 0, 1), 1, "ACCOUNT_MISSING")
    top = replace(base[2], height=MAX_U64_V2)
    top_occurrence = replace(occurrence, height=MAX_U64_V2, pre_state_root=top.state_root)
    family.margin("reject/max-height", (base[0], base[1], top), command, 1, "OCCURRENCE_CONTEXT_MISMATCH",
                  occurrence=top_occurrence)
    deposited = family.margin("stale/deposit", base, _command(DEPOSIT, 25, 1), 1, "ACCEPTED")
    stale_command = _command(WITHDRAW, 5, 2)
    family.margin("stale/asset-frame", (base[0], deposited[1], deposited[2]), stale_command, 2,
                  "PROJECTION_MISMATCH")
    family.margin("stale/margin-frame", (deposited[0], base[1], deposited[2]), stale_command, 2,
                  "PROJECTION_MISMATCH")
    unknown = (base[0], PerpsMarginStateV2(replace(base[1].economic_state, collateral_asset="EUR"), ()), base[2])
    unknown_roots = tuple(replace(row, state_root=unknown[1].state_root) if row.lane_id is LaneIdV2.PERPS_MARKET
                          else row for row in base[2].lane_roots)
    unknown = (unknown[0], unknown[1], replace(base[2], lane_roots=unknown_roots))
    family.margin("reject/unknown-collateral", unknown, replace(command, asset="EUR"), 1, "UNKNOWN_COLLATERAL")
    disabled = _policy_variant_initial(enabled=False)
    family.margin("reject/disabled-collateral", disabled, command, 1, "DISABLED_COLLATERAL")
    # D. finite-width neighbours from a maximal balance row
    big = _large_balance_initial()
    big_deposit = family.margin("width/max-delta-accepted", big, _command(DEPOSIT, MAX_DELTA_ATOMS_V2, 1), 1, "ACCEPTED")
    family.margin("width/max-delta-plus-one", big, _command(DEPOSIT, MAX_DELTA_ATOMS_V2 + 1, 1), 1,
                  "EFFECT_DELTA_OVERFLOW")
    family.margin("width/withdraw-back-to-u128-max", big_deposit, _command(WITHDRAW, MAX_DELTA_ATOMS_V2, 2), 2,
                  "ACCEPTED")
    return family


def _accepted_cases(family: Family) -> list[MarginCase]:
    return [case for case in family.cases
            if isinstance(case, MarginCase) and isinstance(case.result, PerpsMarginGlobalAcceptedV2)]


def _rejected_codes(family: Family) -> set[str]:
    return {case.result.code.value for case in family.cases
            if isinstance(case, MarginCase) and isinstance(case.result, PerpsMarginGlobalRejectedV2)}


def test_finite_actual_python_producer_correspondence(compiled):
    family = build_family()
    assert sum(isinstance(case, FrameCase) for case in family.cases) == 1
    assert len(_accepted_cases(family)) >= 12
    assert _rejected_codes(family) >= {
        "OCCURRENCE_CONTEXT_MISMATCH", "REPLAY_ALREADY_CONSUMED", "OCCURRENCE_COMMAND_MISMATCH",
        "PROJECTION_MISMATCH", "UNKNOWN_COLLATERAL", "DISABLED_COLLATERAL", "INSUFFICIENT_BALANCE",
        "UNAUTHORIZED_SUBJECT", "ACCOUNT_CLOSED", "ACCOUNT_MISSING", "NONCE_MISMATCH", "ZERO_AMOUNT",
        "EFFECT_DELTA_OVERFLOW",
    }
    checks = [_case_check(case) for case in family.cases]
    output = _probe(compiled, "RuntimeCorrespondence", family.digests_literal() + "\n".join(checks))
    assert len(output) == len(family.cases)
    assert not [case.name for case, line in zip(family.cases, output, strict=True) if line != "true"]


def _mutate(case: MarginCase, **changes: object) -> str:
    """Encode a corrupted accepted observation for a Lean inequality check."""

    result = case.result
    assert isinstance(result, PerpsMarginGlobalAcceptedV2)
    assets, margin, state = result.post_assets, result.post_margin, result.post_state
    if "liabilities" in changes:
        state = replace(state, liabilities=changes["liabilities"])
    if "terminals" in changes:
        state = replace(state, terminal_obligations=changes["terminals"])
    if "lane_roots" in changes:
        state = replace(state, lane_roots=changes["lane_roots"])
    post = _joint_literal(assets, margin, state)
    return f".ok (⟨{post}, {_effects_literal(result.effects)}, {_terminal_plan_literal(result.terminal_plan)}⟩ : Accepted)"


def test_reference_rejects_corrupted_accepted_observations(compiled):
    family = build_family()
    by_name = {case.name: case for case in family.cases if isinstance(case, MarginCase)}
    second = by_name["owner/deposit-b-nonce-one"]
    second_result = second.result
    assert isinstance(second_result, PerpsMarginGlobalAcceptedV2)
    per_account = tuple(sorted((
        EconomicAmountV2("margin-a", "USD", "perps_margin", 25),
        EconomicAmountV2("margin-b", "USD", "perps_margin", 25),
    ), key=lambda row: row.key))
    half = (EconomicAmountV2("alice", "USD", "perps_margin", 25),)
    refill = by_name["history/refill"]
    refill_result = refill.result
    assert isinstance(refill_result, PerpsMarginGlobalAcceptedV2)
    drained_id = refill.inputs[2].terminal_obligations[0].obligation_id
    reopened = tuple(
        replace(row, status=TerminalObligationStatusV2.OPEN) if row.obligation_id == drained_id else row
        for row in refill_result.post_state.terminal_obligations
    )
    stale_roots = tuple(
        replace(row, state_root=next(r.state_root for r in second.inputs[2].lane_roots
                                     if r.lane_id is LaneIdV2.ASSET_TRANSFER))
        if row.lane_id is LaneIdV2.ASSET_TRANSFER else row for row in second_result.post_state.lane_roots
    )
    corruptions: tuple[tuple[str, MarginCase, dict[str, object]], ...] = (
        ("omitted-owner-aggregation", second, {"liabilities": per_account}),
        ("halved-owner-liability", second, {"liabilities": half}),
        ("reopened-drained-terminal", refill, {"terminals": reopened}),
        ("old-asset-root-with-changed-tables", second, {"lane_roots": stale_roots}),
    )
    checks = [
        f"#eval decide (step d {_joint_literal(*case.inputs)} "
        f"{_request_literal(case.command, case.occurrence, case.oracle)} ≠ {_mutate(case, **changes)})"
        for _, case, changes in corruptions
    ]
    output = _probe(compiled, "CorruptedObservations", family.digests_literal() + "\n".join(checks))
    assert output == ["true"] * len(corruptions)


GLOBAL_SOURCE = ROOT / "src/core/perps_margin_global_v2.py"
CLAIMS_SOURCE = ROOT / "src/core/perps_margin_claims_v2.py"
MUTANTS = (
    (
        "unauthorized_conserving_movement",
        "reject/subject_id",
        GLOBAL_SOURCE,
        "        _economic_context(state, margin, occurrence, oracle), margin.economic_state, command,",
        "        _economic_context(state, margin, replace(occurrence, subject_id=command.owner), oracle),"
        " margin.economic_state, command,",
    ),
    (
        "omitted_owner_aggregation",
        "owner/deposit-b-nonce-one",
        GLOBAL_SOURCE,
        "EconomicEffectRowV2(EconomicEffectKindV2.LIABILITY, command.owner,",
        "EconomicEffectRowV2(EconomicEffectKindV2.LIABILITY, command.account_id,",
    ),
    (
        "reused_drained_terminal",
        "history/refill",
        CLAIMS_SOURCE,
        "        claim_id = margin_claim_id_v2(margin.economic_state, account_id, occurrence_id)\n"
        "        if claim_id in rows:\n            raise ValueError(\"margin opening claim id already exists\")",
        "        claim_id = next(iter(sorted(rows)))",
    ),
    (
        "stale_asset_root",
        "history/deposit",
        GLOBAL_SOURCE,
        "    lane_roots = tuple(replace(row, state_root=roots[row.lane_id])\n"
        "                       if row.lane_id in roots else row for row in state.lane_roots)",
        "    lane_roots = tuple(replace(row, state_root=roots[row.lane_id])\n"
        "                       if row.lane_id is LaneIdV2.PERPS_MARKET else row for row in state.lane_roots)",
    ),
    (
        "state_change_on_rejection",
        "history/reopen",
        GLOBAL_SOURCE,
        "    root = state.state_root\n    return PerpsMarginGlobalRejectedV2(code, root, root)",
        "    root = state.state_root\n"
        "    return PerpsMarginGlobalRejectedV2(code, root, replace(state, height=state.height + 1).state_root)",
    ),
    (
        "foreign_equal_rejection_roots",
        "history/reopen",
        GLOBAL_SOURCE,
        "    root = state.state_root\n    return PerpsMarginGlobalRejectedV2(code, root, root)",
        '    root = "0x" + "ab" * 32\n    return PerpsMarginGlobalRejectedV2(code, root, root)',
    ),
    (
        "foreign_input_statement",
        "history/deposit",
        GLOBAL_SOURCE,
        "    return PerpsMarginGlobalAcceptedV2(*projected, statement_root)",
        '    return PerpsMarginGlobalAcceptedV2(*projected, "0x" + "ab" * 32)',
    ),
    (
        "balance_guard_removed",
        "reject/deposit-101",
        GLOBAL_SOURCE,
        "        if balance < command.amount_atoms:",
        "        if False and balance < command.amount_atoms:",
    ),
    (
        "u128_boundary_off_by_one",
        "width/withdraw-back-to-u128-max",
        GLOBAL_SOURCE,
        "            if not 0 <= value <= MAX_ATOMS_V2:",
        "            if not 0 <= value < MAX_ATOMS_V2:",
    ),
)


def _load_mutant(name: str, source_path: Path, old: str, new: str, tmp_path: Path):
    source = source_path.read_text()
    assert source.count(old) == 1, name
    mutated = source.replace(old, new, 1)
    if source_path == CLAIMS_SOURCE:
        claims_name = f"src.core._margin_claims_mutant_{name}"
        claims_file = tmp_path / f"claims_{name}.py"
        claims_file.write_text(mutated)
        claims_spec = importlib.util.spec_from_file_location(claims_name, claims_file)
        assert claims_spec is not None and claims_spec.loader is not None
        claims_module = importlib.util.module_from_spec(claims_spec)
        sys.modules[claims_name] = claims_module
        claims_spec.loader.exec_module(claims_module)
        mutated = GLOBAL_SOURCE.read_text().replace(
            "from .perps_margin_claims_v2 import", f"from ._margin_claims_mutant_{name} import", 1,
        )
    module_name = f"src.core._margin_global_mutant_{name}"
    path = tmp_path / f"global_{name}.py"
    path.write_text(mutated)
    spec = importlib.util.spec_from_file_location(module_name, path)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    assert isinstance(module, types.ModuleType)
    spec.loader.exec_module(module)
    return module.transition_perps_margin_global_v2


def _observe(result: object) -> dict[str, object]:
    """Observe by shape: mutant modules re-declare the outcome classes."""

    shaped: Any = result
    name = type(result).__name__
    if name == "PerpsMarginGlobalRejectedV2":
        return {"code": shaped.code.value,
                "pre_state_root": shaped.pre_state_root, "post_state_root": shaped.post_state_root,
                "effects": shaped.effects.effect_plan_root,
                "terminal": shaped.terminal_plan.plan_root, "oracle": shaped.oracle_plan.plan_root}
    assert name == "PerpsMarginGlobalAcceptedV2", name
    return {"post_state": shaped.post_state.state_root, "post_margin": shaped.post_margin.state_root,
            "post_assets": shaped.post_assets.state_root, "effects": shaped.effects.effect_plan_root,
            "terminal": shaped.terminal_plan.plan_root, "statement": shaped.statement_root,
            "refinement": shaped.refinement.refinement_root}


@pytest.mark.parametrize("name,case_name,source_path,old,new", MUTANTS)
def test_python_source_mutants_violate_checked_contract(name, case_name, source_path, old, new, tmp_path):
    family = build_family()
    case = next(c for c in family.cases if c.name == case_name)
    assert isinstance(case, MarginCase)
    transition = _load_mutant(name, source_path, old, new, tmp_path)
    assets, margin, state = case.inputs
    candidate = transition(assets, margin, state, case.command, case.occurrence, case.oracle)
    baseline = _observe(case.result)
    observed = _observe(candidate)
    # The finite Lean gate checks the economic abstraction; the Python frame
    # checks retain the omitted bindings. Neither proves universal refinement.
    assert observed != baseline, (name, observed)


def test_compiled_sources_match_current_checkout(compiled):
    """Fail if a concurrent edit changes the proof subject during the gate."""

    for module, digest in compiled.source_hashes.items():
        path = LEAN_PROJECT / Path(*module.split(".")).with_suffix(".lean")
        assert hashlib.sha256(path.read_bytes()).hexdigest() == digest, module
    assert set(compiled.source_hashes) == set(MODULES)


def test_digest_table_rejects_distinct_roots_for_one_abstract_state():
    """Omitted policy metadata must not silently select a pack-order digest."""

    assets, margin, state = _initial()
    transfer = assets.transfer_state
    changed = AssetLaneCustodyStateV2(
        replace(transfer, policies=tuple(replace(p, fee_owner="mallory") for p in transfer.policies)),
        assets.origin_registry, assets.managed_policies, assets.custody,
    )
    assert assets.state_root != changed.state_root
    assert _assets_literal(assets) == _assets_literal(changed)
    family = Family()
    family._remember(assets, margin, state)
    family._remember(changed, margin, state)
    with pytest.raises(AssertionError, match="ambiguous asset digest"):
        family.digests_literal()
