"""Complete Spot/asset projection, independent accounting and mixed histories."""

import sys
import types
from dataclasses import replace
from pathlib import Path

import pytest
from hypothesis import given, settings
from hypothesis import strategies as st

from src.core.asset_lane_custody_coordinator_v2 import (
    AssetLaneCustodyAcceptedV2,
    transition_asset_lane_custody_v2,
)
from src.core.asset_lane_custody_global_v2 import derive_asset_lane_custody_global_post_v2
from src.core.asset_lane_custody_state_v2 import AssetLaneCustodyStateV2
from src.core.asset_lane_state_v2 import AssetLaneContextV2
from src.core.asset_transfer_types_v2 import AssetTransferStateV2
from src.core.global_economic_proof_v2 import EconomicCommandOccurrenceV2
from src.core.global_economic_state_v2 import GlobalEconomicStateV2, LaneStateRootV2
from src.core.global_settlement_resource_limits_v2 import StateResourceLimitExceededV2
from src.core.global_settlement_types_v2 import (
    ALL_LANE_IDS_V2,
    ZERO_ROOT_V2,
    AssetSupplyV2,
    EconomicAmountV2,
    EconomicEffectKindV2,
    LaneIdV2,
    TerminalObligationStatusV2,
    TerminalObligationV2,
    hash_economic_command_body_v2,
)
from src.core.spot_swap_global_v2 import (
    SPOT_POOL_CUSTODY_DOMAIN_V2,
    SpotSwapGlobalAcceptedV2,
    SpotSwapGlobalRejectCodeV2,
    SpotSwapGlobalRejectedV2,
    spot_swap_command_body_v2,
    transition_spot_swap_global_v2,
)
from src.core.spot_swap_plan_v2 import SpotSwapRejectCodeV2
from src.core.spot_swap_state_v2 import SpotIntentNonceV2, SpotSwapStateV2
from tests.core.test_asset_lane_coordinator_v2 import (
    _registry,
    _root,
    _transfer_command,
    _transfer_policy,
)
from tests.core.test_spot_swap_plan_v2 import intent
from tests.core.test_spot_swap_state_v2 import ALICE, BOB, CAROL, MALLORY, spot_state


def initial(*, fee_bps=30):
    spot = spot_state(fee_bps=fee_bps)
    policies = tuple(_transfer_policy(asset=asset, fee_atoms=0) for asset in ("A", "B"))
    balances = tuple(EconomicAmountV2(ALICE, asset, "accounts", 1000) for asset in ("A", "B"))
    reserves = (spot.pool.reserve0, spot.pool.reserve1)
    # An unrelated funded custody row must survive swaps and ordinary transfers.
    custody = tuple(sorted((EconomicAmountV2("other", "A", "escrow", 20), *(
        EconomicAmountV2(spot.pool.pool_id, asset, SPOT_POOL_CUSTODY_DOMAIN_V2, amount)
        for asset, amount in zip(("A", "B"), reserves, strict=True)
    )), key=lambda row: row.key))
    supplies = tuple(AssetSupplyV2(asset, reserve + 1000 + (20 if asset == "A" else 0))
                     for asset, reserve in zip(("A", "B"), reserves, strict=True))
    assets = AssetLaneCustodyStateV2(
        AssetTransferStateV2(_root("module-release"), policies, balances, supplies),
        _registry(policies, ()), (), custody,
    )
    roots = {LaneIdV2.ASSET_TRANSFER: (assets.transfer_state.module_release_id, assets.state_root),
             LaneIdV2.SPOT_LIQUIDITY: (spot.module_release_id, spot.state_root)}
    state = GlobalEconomicStateV2("spot-test", _root("deployment"), 1, 0, _root("profile"),
        tuple(LaneStateRootV2(lane, roots.get(lane, (_root(lane.value), ZERO_ROOT_V2))[0], lane in roots,
              roots.get(lane, (None, ZERO_ROOT_V2))[1]) for lane in ALL_LANE_IDS_V2),
        balances=balances, custody=custody, supplies=supplies)
    return assets, spot, state


def command(spot, **kwargs):
    return replace(intent(pool_id=spot.pool.pool_id, **kwargs), sender_pubkey=ALICE)


def occurrence(state, cmd, outer_nonce):
    return EconomicCommandOccurrenceV2(state.chain_id, state.deployment_root, state.height + 1, 0, 0,
        cmd.kind.value, hash_economic_command_body_v2(cmd.kind.value, spot_swap_command_body_v2(cmd)),
        _root("spot-route"), cmd.sender_pubkey, _root("grant"), outer_nonce,
        state.profile_root, state.state_root, ())


def step(inputs, cmd, outer_nonce):
    assets, spot, state = inputs
    before = (assets.state_root, spot.state_root, state.state_root)
    result = transition_spot_swap_global_v2(*inputs, cmd, occurrence(state, cmd, outer_nonce), 100)
    assert before == (assets.state_root, spot.state_root, state.state_root)
    assert type(result) is SpotSwapGlobalAcceptedV2
    assert result.refinement.production_authority == "NONE"
    assert result.post_state.supplies == state.supplies
    assert result.post_spot.lp_positions == spot.lp_positions
    assert result.post_state.liabilities == state.liabilities
    assert result.post_state.terminal_obligations == state.terminal_obligations
    assert result.post_state.outbox == state.outbox
    assert tuple(r for r in result.post_state.custody if r.custody_domain == "escrow") == (
        EconomicAmountV2("other", "A", "escrow", 20),)
    return result, (result.post_assets, result.post_spot, result.post_state)


@pytest.mark.parametrize("reverse", [False, True])
@pytest.mark.parametrize("exact_out", [False, True])
@pytest.mark.parametrize("fee_bps", [0, 30])
def test_given_actual_intent_when_swapped_then_wallet_pool_shares_and_global_state_reconcile(reverse, exact_out, fee_bps):
    inputs = initial(fee_bps=fee_bps)
    _, spot, state = inputs
    cmd = command(spot, reverse=reverse, exact_out=exact_out, recipient=BOB,
                  **({"max_amount_in": 20} if exact_out else {"min_amount_out": 1}))
    result, _ = step(inputs, cmd, 1)
    post = result.post_state
    rows = [r for r in result.effects.rows if r.kind is EconomicEffectKindV2.ACCOUNT_MOVEMENT]
    debit = -next(r.delta_atoms for r in rows if r.delta_atoms < 0)
    credit = next(r.delta_atoms for r in rows if r.delta_atoms > 0)
    asset_in, asset_out = cmd.get_field("asset_in"), cmd.get_field("asset_out")
    assert {r.key: r.amount_atoms for r in post.balances} == {
        (asset_in, ALICE, "accounts"): 1000 - debit,
        (asset_out, ALICE, "accounts"): 1000,
        (asset_out, BOB, "accounts"): credit,
    }
    before_pool = dict(zip(("A", "B"), (spot.pool.reserve0, spot.pool.reserve1), strict=True))
    after_pool = {r.asset: r.amount_atoms for r in post.custody if r.custody_domain == SPOT_POOL_CUSTODY_DOMAIN_V2}
    assert after_pool == {asset_in: before_pool[asset_in] + debit, asset_out: before_pool[asset_out] - credit}
    for supply in state.supplies:
        assert sum(r.amount_atoms for r in (*post.balances, *post.custody) if r.asset == supply.asset) == supply.amount_atoms
    assert result.post_spot.intent_nonce(ALICE) == 1
    assert {r.lane_id for r in result.effects.lane_writes} == {LaneIdV2.ASSET_TRANSFER, LaneIdV2.SPOT_LIQUIDITY}
    fee = (debit * fee_bps + 9999) // 10000
    assert sum(r.delta_atoms for r in result.effects.rows if r.kind is EconomicEffectKindV2.FEE_ALLOCATION) == fee
    assert sum(r.current_allocations_atoms for r in result.effects.fee_conservation) == fee


def assert_reject(inputs, cmd, occ, code, *, timestamp=100):
    assets, spot, state = inputs
    before = (assets.state_root, spot.state_root, state.state_root)
    for _ in range(2):
        result = transition_spot_swap_global_v2(*inputs, cmd, occ, timestamp)
        assert type(result) is SpotSwapGlobalRejectedV2
        assert result.code is code
        assert result.pre_state_root == result.post_state_root == state.state_root
        assert result.effects.is_empty
        assert before == (assets.state_root, spot.state_root, state.state_root)


@pytest.mark.parametrize("field,value", [
    ("chain_id", "wrong"), ("deployment_root", _root("wrong")), ("profile_root", _root("wrong")),
    ("pre_state_root", _root("wrong")), ("height", 2),
])
def test_correct_economics_wrong_context_rejects_without_nonce_or_effects(field, value):
    inputs = initial()
    cmd = command(inputs[1])
    occ = replace(occurrence(inputs[2], cmd, 1), **{field: value})
    assert_reject(inputs, cmd, occ, SpotSwapGlobalRejectCodeV2.OCCURRENCE_CONTEXT_MISMATCH)


@pytest.mark.parametrize("defect", ["body", "kind", "objects", "subject", "funds", "slippage", "deadline", "gap"])
def test_independent_guards_reject_conserving_unauthorized_or_unacceptable_commands(defect):
    inputs = initial()
    fields = {"max_amount_in": 1} if defect == "slippage" else {}
    if defect == "funds":
        fields = {"exact_out": False, "amount_in": 1001, "min_amount_out": 1}
    if defect == "gap":
        fields = {"nonce": 2}
    cmd = command(inputs[1], **fields)
    occ = occurrence(inputs[2], cmd, 1)
    changes = {"body": {"command_body_hash": _root("bad")}, "kind": {"command_kind": "wrong"},
               "objects": {"consumed_object_ids": (_root("object"),)}, "subject": {"subject_id": MALLORY}}
    occ = replace(occ, **changes.get(defect, {}))
    code = {"subject": SpotSwapRejectCodeV2.SUBJECT_MISMATCH,
            "funds": SpotSwapRejectCodeV2.INSUFFICIENT_BALANCE, "slippage": SpotSwapRejectCodeV2.SLIPPAGE_LIMIT,
            "deadline": SpotSwapRejectCodeV2.EXPIRED, "gap": SpotSwapRejectCodeV2.INVALID_NONCE}.get(
                defect, SpotSwapGlobalRejectCodeV2.OCCURRENCE_COMMAND_MISMATCH)
    assert_reject(inputs, cmd, occ, code, timestamp=101 if defect == "deadline" else 100)


@pytest.mark.parametrize("field", ["module", "version", "intent_id", "salt", "deadline", "fields"])
def test_every_original_intent_field_is_bound_to_the_occurrence(field):
    inputs = initial()
    cmd = command(inputs[1])
    occ = occurrence(inputs[2], cmd, 1)
    values = {"module": "Other", "version": "0.2", "intent_id": _root("other-intent"),
              "salt": "different", "deadline": 101, "fields": {**dict(cmd.fields), "recipient": MALLORY}}
    # The legacy constructor may forbid a foreign module/version before hashing.
    if field in ("module", "version"):
        object.__setattr__(cmd, field, values[field])
        with pytest.raises(ValueError):
            transition_spot_swap_global_v2(*inputs, cmd, occ, 100)
    else:
        cmd = replace(cmd, **{field: values[field]})
        assert_reject(inputs, cmd, occ, SpotSwapGlobalRejectCodeV2.OCCURRENCE_COMMAND_MISMATCH)


def transfer(inputs, outer_nonce):
    assets, spot, state = inputs
    cmd = replace(_transfer_command(amount_atoms=3, max_fee_atoms=0), asset="A", asset_origin_root=_root("origin:A"), sender=ALICE, recipient=BOB)
    occ = EconomicCommandOccurrenceV2(state.chain_id, state.deployment_root, state.height + 1, 0, 0,
        cmd.command_kind, cmd.command_body_hash, _root("asset-route"), ALICE, _root("grant"),
        outer_nonce, state.profile_root, state.state_root, ())
    result = transition_asset_lane_custody_v2(AssetLaneContextV2(state.writer_epoch,
        assets.transfer_state.module_release_id, state.state_root, occ), assets, cmd)
    assert type(result) is AssetLaneCustodyAcceptedV2
    post = derive_asset_lane_custody_global_post_v2(assets, result, state, occ)
    return result.post_state, spot, post


def test_asset_swap_asset_swap_history_keeps_independent_inner_and_outer_nonces():
    inputs = transfer(initial(), 1)
    _, inputs = step(inputs, command(inputs[1], nonce=1), 2)
    inputs = transfer(inputs, 3)
    stale = command(inputs[1], nonce=1)
    assert_reject(inputs, stale, occurrence(inputs[2], stale, 4), SpotSwapRejectCodeV2.INVALID_NONCE)
    cmd = command(inputs[1], nonce=2)
    assert_reject(inputs, cmd, occurrence(inputs[2], cmd, 3), SpotSwapGlobalRejectCodeV2.REPLAY_ALREADY_CONSUMED)
    _, inputs = step(inputs, cmd, 4)
    assert inputs[1].intent_nonce(ALICE) == 2
    assert len(inputs[2].replay_state) == 4


@pytest.mark.parametrize("defect", ["missing-custody", "extra-custody", "reserve-mismatch", "lp-owner",
                                    "lp-metadata", "module", "disabled", "asset-root", "nominal-claims"])
def test_incomplete_or_misattributed_projection_cannot_admit_a_swap(defect):
    assets, spot, state = initial()
    if defect in ("missing-custody", "extra-custody"):
        # The complete asset frame itself differs; the global projection must
        # reject before producing a superficially conserving successor.
        rows = tuple(row for row in state.custody if row.custody_domain != SPOT_POOL_CUSTODY_DOMAIN_V2)
        if defect == "extra-custody":
            rows = tuple(sorted((*state.custody, EconomicAmountV2("fake", "A", "spot_pool", 1)), key=lambda row: row.key))
        state = replace(state, custody=rows)
    elif defect == "reserve-mismatch":
        spot = SpotSwapStateV2(spot.module_release_id, replace(spot.pool, reserve0=spot.pool.reserve0 + 1), spot.lp_positions)
        state = with_spot_root(state, spot)
    elif defect in ("lp-owner", "lp-metadata"):
        rows = spot.lp_positions
        changes = {"owner": MALLORY} if defect == "lp-owner" else {"last_remove_timestamp": 99}
        rows = tuple(sorted((rows[0], replace(rows[1], **changes), rows[2]), key=lambda row: row.owner))
        spot = SpotSwapStateV2(spot.module_release_id, spot.pool, rows)
    elif defect == "nominal-claims":
        state = replace(state, liabilities=(EconomicAmountV2(BOB, "A", "spot_pool", 1),))
    else:
        lane = LaneIdV2.ASSET_TRANSFER if defect == "asset-root" else LaneIdV2.SPOT_LIQUIDITY
        change = {"enabled": False} if defect == "disabled" else (
            {"module_release_id": _root("other-release")} if defect == "module" else {"state_root": _root("other-state")})
        state = replace(state, lane_roots=tuple(replace(row, **change) if row.lane_id is lane else row for row in state.lane_roots))
    inputs = (assets, spot, state)
    cmd = command(spot)
    assert_reject(inputs, cmd, occurrence(state, cmd, 1), SpotSwapGlobalRejectCodeV2.PROJECTION_MISMATCH)


def with_spot_root(state, spot):
    return replace(state, lane_roots=tuple(replace(row, state_root=spot.state_root)
        if row.lane_id is LaneIdV2.SPOT_LIQUIDITY else row for row in state.lane_roots))


def test_swap_preserves_unrelated_open_claim_and_its_exact_backing():
    assets, spot, state = initial()
    state = replace(state, liabilities=(EconomicAmountV2(CAROL, "A", "escrow", 20),),
        terminal_obligations=(TerminalObligationV2("carol-claim", LaneIdV2.STRATEGY_ESCROW,
            CAROL, "A", "escrow", 20, TerminalObligationStatusV2.OPEN),))
    _, inputs = step((assets, spot, state), command(spot), 1)
    assert inputs[2].terminal_obligations == state.terminal_obligations
    assert inputs[2].liabilities == state.liabilities


def test_nonce_exhaustion_and_full_new_subject_table_are_logical_noops():
    assets, spot, state = initial()
    positions = spot.lp_positions
    exhausted = SpotSwapStateV2(spot.module_release_id, spot.pool, positions, (SpotIntentNonceV2(ALICE, (1 << 32) - 1),))
    exhausted_state = with_spot_root(state, exhausted)
    cmd = command(spot, nonce=(1 << 32) - 1)
    assert_reject((assets, exhausted, exhausted_state), cmd, occurrence(exhausted_state, cmd, 1), SpotSwapRejectCodeV2.INVALID_NONCE)
    nonces = tuple(SpotIntentNonceV2("0x" + f"{i:096x}", 1) for i in range(4096))
    full = SpotSwapStateV2(spot.module_release_id, spot.pool, positions, nonces)
    full_state = with_spot_root(state, full)
    cmd = command(spot)
    assert_reject((assets, full, full_state), cmd, occurrence(full_state, cmd, 1), SpotSwapGlobalRejectCodeV2.SUCCESSOR_REJECTED)
    # At capacity an already represented owner can still act; do not turn a
    # table limit into a ban on all required successor states.
    full = SpotSwapStateV2(spot.module_release_id, spot.pool, positions,
                          (*nonces[1:], SpotIntentNonceV2(ALICE, 1)))
    _, inputs = step((assets, full, with_spot_root(state, full)), command(full, nonce=2), 1)
    assert len(inputs[1].intent_nonces) == 4096


@pytest.mark.parametrize("defect", ["disabled", "transfer-fee", "origin"])
def test_asset_policy_must_be_known_and_admitted_without_inventing_token_fee_semantics(defect):
    assets, spot, state = initial()
    leaf = assets.transfer_state
    changes = {"enabled": False} if defect == "disabled" else {"transfer_fee_atoms": 1}
    policies = leaf.policies if defect == "origin" else (replace(leaf.policies[0], **changes), leaf.policies[1])
    registry = _registry(policies, (), drift_transfer_asset="A" if defect == "origin" else None)
    assets = AssetLaneCustodyStateV2(AssetTransferStateV2(leaf.module_release_id, policies, leaf.balances, leaf.supplies),
                                   registry, (), assets.custody)
    state = replace(state, lane_roots=tuple(replace(row, state_root=assets.state_root)
        if row.lane_id is LaneIdV2.ASSET_TRANSFER else row for row in state.lane_roots))
    cmd = command(spot)
    code = SpotSwapGlobalRejectCodeV2.ASSET_ORIGIN_MISMATCH if defect == "origin" else SpotSwapGlobalRejectCodeV2.UNSUPPORTED_ASSET_POLICY
    assert_reject((assets, spot, state), cmd, occurrence(state, cmd, 1), code)


def test_accepted_getters_do_not_expose_retained_pool_asset_or_effect_graphs():
    inputs = initial()
    result, _ = step(inputs, command(inputs[1]), 1)
    before = (result.post_assets.state_root, result.post_spot.state_root, result.post_state.state_root, result.effects.effect_plan_root)
    object.__setattr__(result.post_assets, "_custody", ())
    object.__setattr__(result.post_spot, "_lp_positions", ())
    object.__setattr__(result.post_state, "height", 99)
    object.__setattr__(result.effects, "_rows", ())
    assert before == (result.post_assets.state_root, result.post_spot.state_root, result.post_state.state_root, result.effects.effect_plan_root)


@pytest.mark.parametrize("field", ["_lp_positions", "_intent_nonces"])
def test_transition_checks_forged_spot_capacity_before_any_row_traversal(field):
    inputs = initial()
    cmd = command(inputs[1])
    occ = occurrence(inputs[2], cmd, 1)
    object.__setattr__(inputs[1], field, (object(),) * 4097)
    with pytest.raises(StateResourceLimitExceededV2):
        transition_spot_swap_global_v2(*inputs, cmd, occ, 100)


@pytest.mark.parametrize("field", ["sender_pubkey", "recipient"])
@pytest.mark.parametrize("alias", [ALICE[2:], ALICE.upper()])
def test_fresh_outer_occurrence_cannot_admit_a_noncanonical_inner_identity(field, alias):
    inputs = initial()
    cmd = command(inputs[1], **({"recipient": alias} if field == "recipient" else {}))
    if field == "sender_pubkey":
        cmd = replace(cmd, sender_pubkey=alias)
    occ = occurrence(inputs[2], cmd, 1)
    before = tuple(value.state_root for value in inputs)
    with pytest.raises(ValueError):
        transition_spot_swap_global_v2(*inputs, cmd, occ, 100)
    assert tuple(value.state_root for value in inputs) == before


def test_timestamp_is_bound_even_when_both_times_admit_the_same_economics():
    inputs = initial()
    cmd = command(inputs[1])
    occ = occurrence(inputs[2], cmd, 1)
    earlier = transition_spot_swap_global_v2(*inputs, cmd, occ, 99)
    later = transition_spot_swap_global_v2(*inputs, cmd, occ, 100)
    assert type(earlier) is type(later) is SpotSwapGlobalAcceptedV2
    assert earlier.post_state == later.post_state
    assert earlier.statement_root != later.statement_root


@pytest.mark.parametrize("mutant", ["lp-root", "intent-nonce", "command-body", "recipient"])
def test_semantic_mutants_are_killed_by_exact_ownership_and_command_observations(mutant, monkeypatch):
    import src.core.spot_swap_global_v2 as production

    source = Path(production.__file__).read_text()
    replacements = {
        "lp-root": (
            "if (lane.module_release_id, lane.enabled, lane.state_root) != (spot.module_release_id, True, spot.state_root):",
            "if False:",
        ),
        "intent-nonce": ("if owned.get_field(\"nonce\") != spot.intent_nonce(sender) + 1:", "if False:"),
        "command-body": ("occurrence.command_body_hash != hash_economic_command_body_v2",
                         "False and occurrence.command_body_hash != hash_economic_command_body_v2"),
        "recipient": ("plan.recipient", repr(MALLORY)),
    }
    original, replacement = replacements[mutant]
    assert source.count(original) == (2 if mutant == "recipient" else 1)
    module = types.ModuleType("src.core._spot_global_semantic_mutant")
    module.__package__ = "src.core"
    monkeypatch.setitem(sys.modules, module.__name__, module)
    exec(compile(source.replace(original, replacement), production.__file__, "exec"), module.__dict__)
    assets, spot, state = initial()
    if mutant == "lp-root":
        rows = spot.lp_positions
        spot = SpotSwapStateV2(spot.module_release_id, spot.pool, tuple(sorted(
            (rows[0], replace(rows[1], owner=MALLORY), rows[2]), key=lambda row: row.owner)))
    cmd = command(spot, recipient=BOB, nonce=2 if mutant == "intent-nonce" else 1)
    occ = occurrence(state, cmd, 1)
    if mutant == "command-body":
        occ = replace(occ, command_body_hash=_root("foreign-body"))

    def observe(implementation):
        result = implementation.transition_spot_swap_global_v2(assets, spot, state, cmd, occ, 100)
        if type(result) is implementation.SpotSwapGlobalRejectedV2:
            return ("reject", result.code.value, result.pre_state_root, result.post_state_root, result.effects.is_empty)
        return ("accept", result.post_state.to_canonical(), result.post_spot.to_canonical())

    # Require a correct production observation and a changed runtime result,
    # never a compilation failure or unrelated exception as a mutation kill.
    expected = observe(production)
    if mutant == "recipient":
        assert expected[0] == "accept"
    else:
        expected_code = {"lp-root": "PROJECTION_MISMATCH", "intent-nonce": "INVALID_NONCE",
                         "command-body": "OCCURRENCE_COMMAND_MISMATCH"}[mutant]
        assert expected == ("reject", expected_code, state.state_root, state.state_root, True)
    assert observe(module) != expected


@given(st.lists(st.tuples(st.booleans(), st.integers(1, 1100)), min_size=1, max_size=8))
@settings(max_examples=12, deadline=None, derandomize=True)
def test_stateful_swaps_match_independent_wallet_and_reserve_accounting(actions):
    inputs = initial()
    wallet, pool, count = {"A": 1000, "B": 1000}, {"A": 10_000, "B": 20_000}, 0
    for reverse, amount in actions:
        a, b = ("B", "A") if reverse else ("A", "B")
        cmd = command(inputs[1], exact_out=False, reverse=reverse, amount_in=amount, min_amount_out=0, nonce=count + 1)
        fee = (amount * 30 + 9999) // 10000
        out = pool[b] * (amount - fee) // (pool[a] + amount - fee)
        occ = occurrence(inputs[2], cmd, count + 1)
        result = transition_spot_swap_global_v2(*inputs, cmd, occ, 100)
        if out == 0 or amount > wallet[a]:
            assert type(result) is SpotSwapGlobalRejectedV2
            continue
        assert type(result) is SpotSwapGlobalAcceptedV2
        wallet[a] -= amount
        wallet[b] += out
        pool[a] += amount
        pool[b] -= out
        count += 1
        inputs = (result.post_assets, result.post_spot, result.post_state)
        assert {r.asset: r.amount_atoms for r in inputs[2].balances if r.owner == ALICE} == {
            asset: value for asset, value in wallet.items() if value}
        assert (inputs[1].pool.reserve0, inputs[1].pool.reserve1) == (pool["A"], pool["B"])
        assert inputs[1].lp_positions == spot_state().lp_positions
