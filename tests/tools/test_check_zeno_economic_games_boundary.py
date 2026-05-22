from __future__ import annotations

import copy
import json

from tools.check_zeno_economic_games_boundary import (
    MANIFEST_SCHEMA,
    main,
    validate_economic_games_boundary_v0,
)


def _game(
    game_id: str,
    category: str,
    *,
    legal_posture: str,
    transferable_reward: bool,
    budgeted: bool,
    requires_gate: bool,
    requires_counsel: bool,
) -> dict[str, object]:
    return {
        "id": game_id,
        "category": category,
        "legal_posture": legal_posture,
        "participant_action": f"eligible action for {game_id}",
        "value_source": f"value source for {game_id}",
        "activation_allowed": False,
        "transferable_reward": transferable_reward,
        "xp_entitlement": False,
        "xp_transferable": False,
        "specific_transaction_inducement": False,
        "requires_separate_tokenomics_gate": requires_gate,
        "requires_counsel_review": requires_counsel,
        "budgeted": budgeted,
        "user_terms_disclosed": True,
        "controls": [
            "objective_rules",
            "abuse_gate",
            "covered_user_interface_boundary",
        ],
    }


def _manifest() -> dict[str, object]:
    return {
        "schema": MANIFEST_SCHEMA,
        "status": "internal_research_only",
        "public_claims_allowed": False,
        "counsel_review_required": True,
        "global_controls": [
            "covered_user_interface_boundary_gate",
            "non_transferable_xp_boundary",
            "token_distribution_separate_program",
            "counsel_review_required",
            "benefit_value_accounting",
            "anti_wash_sybil_controls",
            "no_specific_transaction_solicitation",
            "no_investment_advice",
            "no_passive_yield_marketing",
        ],
        "games": [
            _game(
                "xp_level_og_status",
                "non_economic_status",
                legal_posture="allowed_internal",
                transferable_reward=False,
                budgeted=False,
                requires_gate=False,
                requires_counsel=False,
            ),
            _game(
                "league_fee_discount",
                "counsel_gated_economic_benefit",
                legal_posture="counsel_gated",
                transferable_reward=False,
                budgeted=True,
                requires_gate=True,
                requires_counsel=True,
            ),
            _game(
                "feature_waiver",
                "counsel_gated_economic_benefit",
                legal_posture="counsel_gated",
                transferable_reward=False,
                budgeted=True,
                requires_gate=True,
                requires_counsel=True,
            ),
            _game(
                "activity_mined_token_distribution",
                "counsel_gated_token_distribution",
                legal_posture="counsel_gated",
                transferable_reward=True,
                budgeted=True,
                requires_gate=True,
                requires_counsel=True,
            ),
            _game(
                "proof_mining_rewards",
                "bonded_work_reward",
                legal_posture="counsel_gated",
                transferable_reward=True,
                budgeted=True,
                requires_gate=True,
                requires_counsel=True,
            ),
            _game(
                "oracle_reporter_rewards",
                "bonded_work_reward",
                legal_posture="counsel_gated",
                transferable_reward=True,
                budgeted=True,
                requires_gate=True,
                requires_counsel=True,
            ),
            _game(
                "lp_duration_incentives",
                "high_risk_separate_gate",
                legal_posture="counsel_gated",
                transferable_reward=True,
                budgeted=True,
                requires_gate=True,
                requires_counsel=True,
            ),
            _game(
                "retroactive_activity_airdrop",
                "counsel_gated_token_distribution",
                legal_posture="counsel_gated",
                transferable_reward=True,
                budgeted=True,
                requires_gate=True,
                requires_counsel=True,
            ),
            _game(
                "lock_weighted_governance",
                "high_risk_separate_gate",
                legal_posture="counsel_gated",
                transferable_reward=False,
                budgeted=True,
                requires_gate=True,
                requires_counsel=True,
            ),
            _game(
                "referral_rewards",
                "high_risk_separate_gate",
                legal_posture="counsel_gated",
                transferable_reward=True,
                budgeted=True,
                requires_gate=True,
                requires_counsel=True,
            ),
            _game(
                "burn_indexed_unlock_accelerator",
                "high_risk_separate_gate",
                legal_posture="counsel_gated",
                transferable_reward=False,
                budgeted=True,
                requires_gate=True,
                requires_counsel=True,
            ),
            _game(
                "route_or_token_specific_boost",
                "forbidden",
                legal_posture="forbidden",
                transferable_reward=False,
                budgeted=False,
                requires_gate=True,
                requires_counsel=True,
            ),
            _game(
                "revenue_share_or_yield_boost",
                "forbidden",
                legal_posture="forbidden",
                transferable_reward=False,
                budgeted=False,
                requires_gate=True,
                requires_counsel=True,
            ),
        ],
        "promotion_boundary": {
            "public_claim_allowed": False,
            "claim_registry_entry_allowed": False,
            "non_claims": [
                "no_legal_clearance",
                "no_public_launch_readiness",
                "no_broker_dealer_registration_clearance",
                "no_exchange_registration_clearance",
                "no_investment_return",
                "no_specific_transaction_solicitation",
            ],
        },
    }


def test_economic_games_boundary_accepts_internal_catalog() -> None:
    report = validate_economic_games_boundary_v0(_manifest())

    assert report["ok"] is True
    assert report["facts"]["game_count"] == 13
    assert report["facts"]["forbidden_game_count"] == 2
    assert report["facts"]["transferable_reward_game_count"] == 6


def test_economic_games_boundary_rejects_xp_token_entitlement() -> None:
    manifest = copy.deepcopy(_manifest())
    games = manifest["games"]
    assert isinstance(games, list)
    games[0]["xp_entitlement"] = True

    report = validate_economic_games_boundary_v0(manifest)

    assert report["ok"] is False
    assert "xp_entitlement must be false" in report["games"]["items"][0]["errors"]


def test_economic_games_boundary_rejects_transferable_xp() -> None:
    manifest = copy.deepcopy(_manifest())
    games = manifest["games"]
    assert isinstance(games, list)
    games[0]["xp_transferable"] = True

    report = validate_economic_games_boundary_v0(manifest)

    assert report["ok"] is False
    assert "xp_transferable must be false" in report["games"]["items"][0]["errors"]


def test_economic_games_boundary_rejects_specific_transaction_inducement() -> None:
    manifest = copy.deepcopy(_manifest())
    games = manifest["games"]
    assert isinstance(games, list)
    games[3]["specific_transaction_inducement"] = True

    report = validate_economic_games_boundary_v0(manifest)

    assert report["ok"] is False
    assert "specific_transaction_inducement must be false" in report["games"]["items"][3]["errors"]


def test_economic_games_boundary_rejects_unbudgeted_transferable_reward() -> None:
    manifest = copy.deepcopy(_manifest())
    games = manifest["games"]
    assert isinstance(games, list)
    games[3]["budgeted"] = False

    report = validate_economic_games_boundary_v0(manifest)

    assert report["ok"] is False
    assert "economic or token game must be budgeted" in report["games"]["items"][3]["errors"]
    assert "transferable reward requires counsel review, tokenomics gate, and budget" in report["games"]["items"][3]["errors"]


def test_economic_games_boundary_rejects_forbidden_activation() -> None:
    manifest = copy.deepcopy(_manifest())
    games = manifest["games"]
    assert isinstance(games, list)
    games[-1]["activation_allowed"] = True

    report = validate_economic_games_boundary_v0(manifest)

    assert report["ok"] is False
    assert "forbidden game must set activation_allowed=false" in report["games"]["items"][-1]["errors"]


def test_economic_games_boundary_rejects_missing_required_game() -> None:
    manifest = copy.deepcopy(_manifest())
    games = manifest["games"]
    assert isinstance(games, list)
    games[:] = [game for game in games if game["id"] != "activity_mined_token_distribution"]

    report = validate_economic_games_boundary_v0(manifest)

    assert report["ok"] is False
    assert "games rejected" in report["errors"]
    assert report["games"]["facts"]["missing_required_game_ids"] == ["activity_mined_token_distribution"]


def test_economic_games_boundary_cli_outputs_report(tmp_path, capsys) -> None:
    manifest_path = tmp_path / "games.json"
    manifest_path.write_text(json.dumps(_manifest()), encoding="utf-8")

    code = main([str(manifest_path)])
    out = capsys.readouterr().out
    report = json.loads(out)

    assert code == 0
    assert report["ok"] is True
    assert report["schema"].endswith("economic_games_boundary_report.v0")
