from __future__ import annotations

from dataclasses import replace

import pytest

from src.core.global_settlement_abi_v1 import PerpsMarginStateV1 as FacadePerpsMarginStateV1
from src.core.global_settlement_types_v1 import (
    ZERO_ROOT_V1,
    EconomicEffectKindV1,
    LaneIdV1,
    TerminalObligationStatusV1,
)
from src.core.perps_margin_module_v1 import transition_perps_margin_v1
from src.core.perps_margin_types_v1 import (
    ACCOUNT_CUSTODY_DOMAIN_V1,
    MAX_PERPS_MARGIN_ACCOUNTS_V1,
    PERPS_MARGIN_CLOSE_COMMAND_KIND_V1,
    PERPS_MARGIN_CUSTODY_DOMAIN_V1,
    PERPS_MARGIN_DEPOSIT_COMMAND_KIND_V1,
    PERPS_MARGIN_WITHDRAW_COMMAND_KIND_V1,
    PerpsMarginAcceptedV1,
    PerpsMarginAccountStatusV1,
    PerpsMarginAccountV1,
    PerpsMarginCommandV1,
    PerpsMarginContextV1,
    PerpsMarginMarketStatusV1,
    PerpsMarginRejectCodeV1,
    PerpsMarginRejectedV1,
    PerpsMarginStateV1,
)


def _root(value: int) -> str:
    return f"0x{value:064x}"


def _context(
    *,
    subject_id: str = "alice",
    with_oracle: bool = False,
    oracle_price_e8: int = 100_000_000,
) -> PerpsMarginContextV1:
    return PerpsMarginContextV1(
        chain_id="zeno-test-chain",
        deployment_root=_root(1),
        profile_root=_root(2),
        writer_epoch=7,
        module_release_id=_root(3),
        command_occurrence_id=_root(4),
        subject_id=subject_id,
        grant_root=_root(5),
        oracle_authority_root=_root(9) if with_oracle else ZERO_ROOT_V1,
        oracle_occurrence_root=_root(10) if with_oracle else ZERO_ROOT_V1,
        oracle_price_e8=oracle_price_e8 if with_oracle else 0,
    )


def _account(
    *,
    collateral_atoms: int = 100_000_000,
    position_base: int = 0,
    entry_price_e8: int | None = None,
    nonce: int = 1,
    status: PerpsMarginAccountStatusV1 = PerpsMarginAccountStatusV1.OPEN,
) -> PerpsMarginAccountV1:
    return PerpsMarginAccountV1(
        account_id="perps-account-1",
        owner="alice",
        position_base=position_base,
        entry_price_e8=(100_000_000 if position_base else 0)
        if entry_price_e8 is None
        else entry_price_e8,
        collateral_atoms=collateral_atoms,
        nonce=nonce,
        status=status,
    )


def _counterparty(
    *,
    collateral_atoms: int = 100_000_000,
    position_base: int = -10,
    entry_price_e8: int | None = None,
) -> PerpsMarginAccountV1:
    return PerpsMarginAccountV1(
        account_id="perps-account-2",
        owner="bob",
        position_base=position_base,
        entry_price_e8=(100_000_000 if position_base else 0)
        if entry_price_e8 is None
        else entry_price_e8,
        collateral_atoms=collateral_atoms,
        nonce=1,
        status=PerpsMarginAccountStatusV1.OPEN,
    )


def _state(
    *,
    accounts: tuple[PerpsMarginAccountV1, ...] = (),
    market_status: PerpsMarginMarketStatusV1 = PerpsMarginMarketStatusV1.ACTIVE,
) -> PerpsMarginStateV1:
    return PerpsMarginStateV1(
        module_release_id=_root(3),
        market_id="perp-btc-usd",
        collateral_asset="zUSD",
        index_price_e8=100_000_000,
        maintenance_margin_bps=500,
        depeg_buffer_bps=100,
        max_position_abs=1_000_000,
        market_status=market_status,
        accounts=accounts,
    )


def _command(
    command_kind: str,
    *,
    amount_atoms: int,
    nonce: int,
    owner: str = "alice",
    market_id: str = "perp-btc-usd",
    asset: str = "zUSD",
) -> PerpsMarginCommandV1:
    return PerpsMarginCommandV1(
        command_kind=command_kind,
        account_id="perps-account-1",
        market_id=market_id,
        owner=owner,
        asset=asset,
        amount_atoms=amount_atoms,
        nonce=nonce,
    )


def _assert_exact_noop(
    result: PerpsMarginRejectedV1,
    state: PerpsMarginStateV1,
    code: PerpsMarginRejectCodeV1,
) -> None:
    assert result.code is code
    assert result.pre_state_root == state.state_root
    assert result.post_state_root == state.state_root
    assert result.effects.is_empty


def test_deposit_creates_open_margin_claim_and_exact_candidate_effects() -> None:
    state = _state()
    command = _command(PERPS_MARGIN_DEPOSIT_COMMAND_KIND_V1, amount_atoms=25, nonce=1)

    result = transition_perps_margin_v1(_context(), state, command)

    assert isinstance(result, PerpsMarginAcceptedV1)
    assert result.post_state.accounts == (_account(collateral_atoms=25),)
    assert result.module_journal.lane_id is LaneIdV1.PERPS_MARKET
    assert result.module_journal.terminal_obligations_root == result.terminal_obligations_root
    assert result.module_journal.private_port_root == result.private_port.port_root
    assert result.private_port.command_body_hash == command.command_body_hash
    assert result.private_port.oracle_authority_root == ZERO_ROOT_V1
    assert result.private_port.oracle_occurrence_root == ZERO_ROOT_V1
    assert result.private_port.oracle_price_e8 == 0
    assert result.statement_root == "0x49a6c59cb5503baddd9c02d8a9c90aa2fce93f678fbaaad2ca85598dda6b39ac"
    assert result.private_port.port_root == "0x83654360225cd66ce3791aac313d0fd38beb629e93138bbae1d27df99dbdee38"
    assert result.terminal_obligations[0].status is TerminalObligationStatusV1.OPEN
    assert result.terminal_obligations[0].amount_atoms == 25
    assert result.effects.asset_conservation == ()
    assert result.effects.fee_conservation == ()
    assert result.effects.external_outbox_enqueue == ()
    assert tuple((row.kind, row.principal, row.custody_domain, row.delta_atoms) for row in result.effects.rows) == (
        (EconomicEffectKindV1.ACCOUNT_MOVEMENT, "alice", ACCOUNT_CUSTODY_DOMAIN_V1, -25),
        (EconomicEffectKindV1.CUSTODY, "perps-account-1", PERPS_MARGIN_CUSTODY_DOMAIN_V1, 25),
        (EconomicEffectKindV1.LIABILITY, "alice", PERPS_MARGIN_CUSTODY_DOMAIN_V1, 25),
    )


def test_deposit_golden_roots_are_frozen_for_rust_python_parity() -> None:
    state = _state()
    command = _command(PERPS_MARGIN_DEPOSIT_COMMAND_KIND_V1, amount_atoms=25, nonce=1)

    result = transition_perps_margin_v1(_context(), state, command)

    assert isinstance(result, PerpsMarginAcceptedV1)
    assert result.module_journal.private_port_root == result.private_port.port_root
    assert result.private_port.command_body_hash == command.command_body_hash
    assert result.private_port.oracle_authority_root == ZERO_ROOT_V1
    assert result.private_port.oracle_occurrence_root == ZERO_ROOT_V1
    assert result.private_port.oracle_price_e8 == 0
    assert state.state_root == "0xf09237a0cbec631b97db5686b7760be2f1bab3a90cfcdd17625ab6f2f3738721"
    assert command.command_body_hash == "0x83b30c591ab4f1f08ca3174fcc00aeac67a51d65e9117b50874144ba3f8da93c"
    assert result.post_state.state_root == "0x14563fa71c63897bf9f52e284f6c8c9d3fb8108809e9fa9e9b0ffa7c3fad669d"
    assert result.effects.effect_plan_root == "0xd47cdd1920427234a76e5f9ab1b20e03b671b4e812a2ad6a968da1cad775760c"
    assert result.terminal_obligations_root == "0x1c5f7c894f22685e12e58aed34d1b8c37483aba3eadcb3f5680aca1d3bd2c2ca"
    assert result.receipt_root == "0xb28cd992a77c6c4eba7ae55f22b3df7f7933f3de3502f4074489faae059340d1"


def test_facade_exports_the_exact_perps_margin_state_type() -> None:
    assert FacadePerpsMarginStateV1 is PerpsMarginStateV1


@pytest.mark.parametrize(
    ("command_kind", "pre_collateral", "amount", "nonce"),
    (
        (PERPS_MARGIN_DEPOSIT_COMMAND_KIND_V1, 0, 1, 1),
        (PERPS_MARGIN_DEPOSIT_COMMAND_KIND_V1, 0, 25, 1),
        (PERPS_MARGIN_WITHDRAW_COMMAND_KIND_V1, 25, 1, 2),
        (PERPS_MARGIN_WITHDRAW_COMMAND_KIND_V1, 25, 25, 2),
    ),
)
def test_candidate_effects_preserve_owned_atoms_and_pair_custody_with_liability(
    command_kind: str,
    pre_collateral: int,
    amount: int,
    nonce: int,
) -> None:
    accounts = () if pre_collateral == 0 else (_account(collateral_atoms=pre_collateral),)
    result = transition_perps_margin_v1(
        _context(),
        _state(accounts=accounts),
        _command(command_kind, amount_atoms=amount, nonce=nonce),
    )

    assert isinstance(result, PerpsMarginAcceptedV1)
    account_delta = sum(
        row.delta_atoms
        for row in result.effects.rows
        if row.kind is EconomicEffectKindV1.ACCOUNT_MOVEMENT
    )
    custody_delta = sum(
        row.delta_atoms
        for row in result.effects.rows
        if row.kind is EconomicEffectKindV1.CUSTODY
    )
    liability_delta = sum(
        row.delta_atoms
        for row in result.effects.rows
        if row.kind is EconomicEffectKindV1.LIABILITY
    )
    assert account_delta + custody_delta == 0
    assert liability_delta == custody_delta


def test_exhaustive_small_domain_kills_floor_and_strict_boundary_mutants() -> None:
    for position_base in range(-5, 6):
        for collateral_atoms in range(21):
            account = PerpsMarginAccountV1(
                account_id="perps-account-1",
                owner="alice",
                position_base=position_base,
                entry_price_e8=7 if position_base else 0,
                collateral_atoms=collateral_atoms,
                nonce=1,
                status=PerpsMarginAccountStatusV1.OPEN,
            )
            state = PerpsMarginStateV1(
                module_release_id=_root(3),
                market_id="perp-btc-usd",
                collateral_asset="zUSD",
                index_price_e8=7,
                maintenance_margin_bps=3_333,
                depeg_buffer_bps=1,
                max_position_abs=5,
                market_status=PerpsMarginMarketStatusV1.ACTIVE,
                accounts=(
                    account,
                    _counterparty(
                        collateral_atoms=20,
                        position_base=-position_base,
                        entry_price_e8=7 if position_base else 0,
                    ),
                ),
            )
            numerator = abs(position_base) * 7 * 3_334
            expected_requirement = -(-numerator // 10_000)
            for amount_atoms in range(1, 23):
                result = transition_perps_margin_v1(
                    _context(
                        with_oracle=position_base != 0,
                        oracle_price_e8=7,
                    ),
                    state,
                    _command(
                        PERPS_MARGIN_WITHDRAW_COMMAND_KIND_V1,
                        amount_atoms=amount_atoms,
                        nonce=2,
                    ),
                )
                should_accept = amount_atoms <= collateral_atoms and (
                    position_base == 0
                    or collateral_atoms - amount_atoms >= expected_requirement
                )
                assert isinstance(result, PerpsMarginAcceptedV1) is should_accept
                if should_accept:
                    continue
                assert isinstance(result, PerpsMarginRejectedV1)
                expected_code = (
                    PerpsMarginRejectCodeV1.INSUFFICIENT_COLLATERAL
                    if amount_atoms > collateral_atoms
                    else PerpsMarginRejectCodeV1.MAINTENANCE_BREACH
                )
                assert result.code is expected_code


@pytest.mark.parametrize(
    ("withdraw_atoms", "accepted"),
    ((39_999_999, True), (40_000_000, True), (40_000_001, False)),
)
def test_withdrawal_maintenance_boundary_bva(withdraw_atoms: int, accepted: bool) -> None:
    state = _state(accounts=(_account(position_base=10), _counterparty()))
    command = _command(
        PERPS_MARGIN_WITHDRAW_COMMAND_KIND_V1,
        amount_atoms=withdraw_atoms,
        nonce=2,
    )

    result = transition_perps_margin_v1(_context(with_oracle=True), state, command)

    if accepted:
        assert isinstance(result, PerpsMarginAcceptedV1)
        assert result.post_state.accounts[0].collateral_atoms == 100_000_000 - withdraw_atoms
        return
    assert isinstance(result, PerpsMarginRejectedV1)
    _assert_exact_noop(result, state, PerpsMarginRejectCodeV1.MAINTENANCE_BREACH)


def test_oracle_bound_withdrawal_golden_roots_match_rust_projection() -> None:
    state = _state(accounts=(_account(position_base=10), _counterparty()))
    command = _command(
        PERPS_MARGIN_WITHDRAW_COMMAND_KIND_V1,
        amount_atoms=40_000_000,
        nonce=2,
    )

    result = transition_perps_margin_v1(_context(with_oracle=True), state, command)

    assert isinstance(result, PerpsMarginAcceptedV1)
    assert result.module_journal.private_port_root == result.private_port.port_root
    assert result.private_port.command_body_hash == command.command_body_hash
    assert result.private_port.oracle_authority_root == _root(9)
    assert result.private_port.oracle_occurrence_root == _root(10)
    assert result.private_port.oracle_price_e8 == 100_000_000
    assert result.statement_root == "0xd9a591464d06a0c06f3a7f8f8fd2a80a2707f15970a3c1bb55a52cb30c7d0620"
    assert result.private_port.port_root == "0xfaf98464d17415fdc1661f7465acd81d25d542d95605e5e9b0b17aea0a45cf08"
    assert state.state_root == "0xb3cfde94ceefa7082e1a8916ff0a284e66bebf96419f7a73da5b206565163da6"
    assert command.command_body_hash == "0x2e34c888f447e69e9e59c382532498ee2ec9200a28c971e821989b707d729aed"
    assert result.post_state.state_root == "0x46266091abad6ffaca603ddc821bae5241af4a46a55ac16b22afda6314604780"
    assert result.effects.effect_plan_root == "0xf304ad8551b029c9f012dffa1e36069c4f792980880b60c147f0ec41db2338dc"
    assert result.terminal_obligations_root == "0xc3779fc3bfa32a1b1dd273e8fcf85ac4a9647e38805f2c21d1e216d01fd3d22d"
    assert result.receipt_root == "0xa4d4f717f661f87c84baed43d545eed9a4865e3ab6f6429e38b39fd933e150b6"


def test_withdrawal_requires_exact_nonzero_oracle_authority_binding() -> None:
    state = _state(
        accounts=(
            _account(collateral_atoms=25_000_000, position_base=1),
            _counterparty(position_base=-1),
        )
    )
    command = _command(
        PERPS_MARGIN_WITHDRAW_COMMAND_KIND_V1,
        amount_atoms=1,
        nonce=2,
    )

    missing = transition_perps_margin_v1(_context(), state, command)
    mismatched = transition_perps_margin_v1(
        _context(with_oracle=True, oracle_price_e8=99_999_999),
        state,
        command,
    )

    assert isinstance(missing, PerpsMarginRejectedV1)
    _assert_exact_noop(missing, state, PerpsMarginRejectCodeV1.ORACLE_AUTHORITY_MISSING)
    assert isinstance(mismatched, PerpsMarginRejectedV1)
    _assert_exact_noop(mismatched, state, PerpsMarginRejectCodeV1.ORACLE_PRICE_MISMATCH)


@pytest.mark.parametrize(
    ("command_kind", "amount_atoms"),
    (
        (PERPS_MARGIN_DEPOSIT_COMMAND_KIND_V1, 1),
        (PERPS_MARGIN_WITHDRAW_COMMAND_KIND_V1, 1),
        (PERPS_MARGIN_CLOSE_COMMAND_KIND_V1, 0),
    ),
)
def test_price_independent_commands_reject_unexpected_oracle_binding(
    command_kind: str,
    amount_atoms: int,
) -> None:
    accounts = {
        PERPS_MARGIN_DEPOSIT_COMMAND_KIND_V1: (),
        PERPS_MARGIN_WITHDRAW_COMMAND_KIND_V1: (_account(collateral_atoms=1),),
        PERPS_MARGIN_CLOSE_COMMAND_KIND_V1: (replace(_account(), collateral_atoms=0),),
    }[command_kind]
    state = _state(accounts=accounts)
    nonce = 1 if command_kind == PERPS_MARGIN_DEPOSIT_COMMAND_KIND_V1 else 2

    result = transition_perps_margin_v1(
        _context(with_oracle=True),
        state,
        _command(command_kind, amount_atoms=amount_atoms, nonce=nonce),
    )

    assert isinstance(result, PerpsMarginRejectedV1)
    _assert_exact_noop(result, state, PerpsMarginRejectCodeV1.UNEXPECTED_ORACLE_AUTHORITY)


def test_partial_oracle_binding_is_invalid_input() -> None:
    with pytest.raises(ValueError, match="wholly absent or present"):
        replace(_context(), oracle_authority_root=_root(9))


def test_accepted_output_rejects_private_port_and_statement_substitution() -> None:
    result = transition_perps_margin_v1(
        _context(with_oracle=True),
        _state(
            accounts=(
                _account(collateral_atoms=25_000_000, position_base=1),
                _counterparty(position_base=-1),
            )
        ),
        _command(PERPS_MARGIN_WITHDRAW_COMMAND_KIND_V1, amount_atoms=1, nonce=2),
    )
    assert isinstance(result, PerpsMarginAcceptedV1)

    with pytest.raises(ValueError, match="private-port root mismatch"):
        replace(
            result,
            private_port=replace(result.private_port, oracle_price_e8=99_999_999),
        )
    with pytest.raises(ValueError, match="receipt root mismatch"):
        replace(result, statement_root=_root(99))


def test_deposit_withdraw_close_is_terminal_and_cannot_reopen() -> None:
    initial = _state()
    deposited = transition_perps_margin_v1(
        _context(),
        initial,
        _command(PERPS_MARGIN_DEPOSIT_COMMAND_KIND_V1, amount_atoms=10, nonce=1),
    )
    assert isinstance(deposited, PerpsMarginAcceptedV1)
    withdrawn = transition_perps_margin_v1(
        replace(_context(), command_occurrence_id=_root(6)),
        deposited.post_state,
        _command(PERPS_MARGIN_WITHDRAW_COMMAND_KIND_V1, amount_atoms=10, nonce=2),
    )
    assert isinstance(withdrawn, PerpsMarginAcceptedV1)

    closed = transition_perps_margin_v1(
        replace(_context(), command_occurrence_id=_root(7)),
        withdrawn.post_state,
        _command(PERPS_MARGIN_CLOSE_COMMAND_KIND_V1, amount_atoms=0, nonce=3),
    )

    assert isinstance(closed, PerpsMarginAcceptedV1)
    assert closed.post_state.accounts[0].status is PerpsMarginAccountStatusV1.CLOSED
    assert closed.terminal_obligations[0].status is TerminalObligationStatusV1.DRAINED
    assert closed.terminal_obligations[0].amount_atoms == 0
    retry = transition_perps_margin_v1(
        replace(_context(), command_occurrence_id=_root(8)),
        closed.post_state,
        _command(PERPS_MARGIN_DEPOSIT_COMMAND_KIND_V1, amount_atoms=1, nonce=4),
    )
    assert isinstance(retry, PerpsMarginRejectedV1)
    _assert_exact_noop(retry, closed.post_state, PerpsMarginRejectCodeV1.ACCOUNT_CLOSED)


def test_drain_only_permits_withdraw_and_close_while_rejecting_deposit() -> None:
    state = _state(
        accounts=(_account(collateral_atoms=10),),
        market_status=PerpsMarginMarketStatusV1.DRAIN_ONLY,
    )

    deposit = transition_perps_margin_v1(
        _context(),
        state,
        _command(PERPS_MARGIN_DEPOSIT_COMMAND_KIND_V1, amount_atoms=1, nonce=2),
    )
    withdrawn = transition_perps_margin_v1(
        replace(_context(), command_occurrence_id=_root(6)),
        state,
        _command(PERPS_MARGIN_WITHDRAW_COMMAND_KIND_V1, amount_atoms=10, nonce=2),
    )

    assert isinstance(deposit, PerpsMarginRejectedV1)
    _assert_exact_noop(deposit, state, PerpsMarginRejectCodeV1.MARKET_DRAIN_ONLY)
    assert isinstance(withdrawn, PerpsMarginAcceptedV1)
    closed = transition_perps_margin_v1(
        replace(_context(), command_occurrence_id=_root(7)),
        withdrawn.post_state,
        _command(PERPS_MARGIN_CLOSE_COMMAND_KIND_V1, amount_atoms=0, nonce=3),
    )
    assert isinstance(closed, PerpsMarginAcceptedV1)
    assert closed.terminal_obligations[0].status is TerminalObligationStatusV1.DRAINED


@pytest.mark.parametrize(
    ("state", "context", "command", "code"),
    (
        (_state(), _context(), _command("unknown", amount_atoms=1, nonce=1), PerpsMarginRejectCodeV1.UNKNOWN_COMMAND),
        (_state(market_status=PerpsMarginMarketStatusV1.HALTED), _context(), _command(PERPS_MARGIN_DEPOSIT_COMMAND_KIND_V1, amount_atoms=1, nonce=1), PerpsMarginRejectCodeV1.HALTED_MARKET),
        (_state(), _context(), _command(PERPS_MARGIN_DEPOSIT_COMMAND_KIND_V1, amount_atoms=1, nonce=1, market_id="wrong"), PerpsMarginRejectCodeV1.MARKET_MISMATCH),
        (_state(), _context(), _command(PERPS_MARGIN_DEPOSIT_COMMAND_KIND_V1, amount_atoms=1, nonce=1, asset="TAU"), PerpsMarginRejectCodeV1.ASSET_MISMATCH),
        (_state(), _context(subject_id="mallory"), _command(PERPS_MARGIN_DEPOSIT_COMMAND_KIND_V1, amount_atoms=1, nonce=1), PerpsMarginRejectCodeV1.UNAUTHORIZED_SUBJECT),
        (_state(), replace(_context(), module_release_id=_root(99)), _command(PERPS_MARGIN_DEPOSIT_COMMAND_KIND_V1, amount_atoms=1, nonce=1), PerpsMarginRejectCodeV1.RELEASE_MISMATCH),
        (_state(), _context(), _command(PERPS_MARGIN_WITHDRAW_COMMAND_KIND_V1, amount_atoms=1, nonce=1), PerpsMarginRejectCodeV1.ACCOUNT_MISSING),
        (_state(accounts=(replace(_account(), owner="bob"),)), _context(), _command(PERPS_MARGIN_DEPOSIT_COMMAND_KIND_V1, amount_atoms=1, nonce=2), PerpsMarginRejectCodeV1.ACCOUNT_OWNER_MISMATCH),
        (_state(accounts=(_account(),)), _context(), _command(PERPS_MARGIN_DEPOSIT_COMMAND_KIND_V1, amount_atoms=1, nonce=3), PerpsMarginRejectCodeV1.NONCE_MISMATCH),
        (_state(), _context(), _command(PERPS_MARGIN_DEPOSIT_COMMAND_KIND_V1, amount_atoms=0, nonce=1), PerpsMarginRejectCodeV1.ZERO_AMOUNT),
        (_state(accounts=(_account(collateral_atoms=1),)), _context(), _command(PERPS_MARGIN_WITHDRAW_COMMAND_KIND_V1, amount_atoms=2, nonce=2), PerpsMarginRejectCodeV1.INSUFFICIENT_COLLATERAL),
        (_state(accounts=(_account(position_base=1, collateral_atoms=0), _counterparty(position_base=-1))), _context(), _command(PERPS_MARGIN_CLOSE_COMMAND_KIND_V1, amount_atoms=0, nonce=2), PerpsMarginRejectCodeV1.POSITION_OPEN),
        (_state(accounts=(_account(collateral_atoms=1),)), _context(), _command(PERPS_MARGIN_CLOSE_COMMAND_KIND_V1, amount_atoms=0, nonce=2), PerpsMarginRejectCodeV1.COLLATERAL_REMAINS),
        (_state(accounts=(replace(_account(), collateral_atoms=0),)), _context(), _command(PERPS_MARGIN_CLOSE_COMMAND_KIND_V1, amount_atoms=1, nonce=2), PerpsMarginRejectCodeV1.INVALID_CLOSE_AMOUNT),
    ),
)
def test_policy_rejections_are_exact_noops(
    state: PerpsMarginStateV1,
    context: PerpsMarginContextV1,
    command: PerpsMarginCommandV1,
    code: PerpsMarginRejectCodeV1,
) -> None:
    result = transition_perps_margin_v1(context, state, command)

    assert isinstance(result, PerpsMarginRejectedV1)
    _assert_exact_noop(result, state, code)


def test_effect_delta_overflow_rejects_before_any_state_change() -> None:
    state = _state()

    result = transition_perps_margin_v1(
        _context(),
        state,
        _command(PERPS_MARGIN_DEPOSIT_COMMAND_KIND_V1, amount_atoms=1 << 127, nonce=1),
    )

    assert isinstance(result, PerpsMarginRejectedV1)
    _assert_exact_noop(result, state, PerpsMarginRejectCodeV1.EFFECT_DELTA_OVERFLOW)


def test_exhausted_nonce_rejects_before_command_nonce_comparison() -> None:
    state = _state(accounts=(replace(_account(), nonce=(1 << 64) - 1),))

    result = transition_perps_margin_v1(
        _context(with_oracle=True),
        state,
        _command(
            PERPS_MARGIN_WITHDRAW_COMMAND_KIND_V1,
            amount_atoms=1,
            nonce=(1 << 64) - 1,
        ),
    )

    assert isinstance(result, PerpsMarginRejectedV1)
    _assert_exact_noop(result, state, PerpsMarginRejectCodeV1.NONCE_OVERFLOW)


def test_closed_account_shape_and_account_order_are_canonical() -> None:
    with pytest.raises(ValueError, match="closed account"):
        _account(
            collateral_atoms=1,
            nonce=2,
            status=PerpsMarginAccountStatusV1.CLOSED,
        )
    with pytest.raises(ValueError, match="canonically ordered"):
        _state(
            accounts=(
                replace(_account(), account_id="z-account"),
                replace(_account(), account_id="a-account"),
            )
        )
    with pytest.raises(ValueError, match="entry price differs"):
        _state(
            accounts=(
                _account(position_base=1, entry_price_e8=99_999_999),
                _counterparty(position_base=-1),
            )
        )


def test_terminal_obligation_id_is_namespaced_by_release_market_and_account() -> None:
    first = _state(accounts=(_account(collateral_atoms=1),))
    other_market = replace(first, market_id="perp-eth-usd")
    other_release = replace(first, module_release_id=_root(99))

    identifiers = {
        first.terminal_obligations[0].obligation_id,
        other_market.terminal_obligations[0].obligation_id,
        other_release.terminal_obligations[0].obligation_id,
    }
    assert len(identifiers) == 3
    assert "perps-account-1" not in identifiers


def test_hash_derived_terminal_obligations_are_canonically_sorted() -> None:
    state = _state(accounts=(_account(position_base=1), _counterparty(position_base=-1)))

    obligation_ids = tuple(
        obligation.obligation_id for obligation in state.terminal_obligations
    )

    assert obligation_ids == tuple(sorted(obligation_ids))


def test_peer_to_peer_market_requires_exact_zero_net_position() -> None:
    with pytest.raises(ValueError, match="net position must be zero"):
        _state(accounts=(_account(position_base=1),))

    balanced = _state(
        accounts=(_account(position_base=1), _counterparty(position_base=-1))
    )
    assert sum(account.position_base for account in balanced.accounts) == 0


def test_account_count_uses_exact_maximum_boundary() -> None:
    accounts = tuple(
        replace(_account(collateral_atoms=0), account_id=f"account-{index:03d}")
        for index in range(MAX_PERPS_MARGIN_ACCOUNTS_V1 + 1)
    )

    command = replace(
        _command(PERPS_MARGIN_DEPOSIT_COMMAND_KIND_V1, amount_atoms=1, nonce=1),
        account_id="perps-account-new",
    )
    below_max = _state(accounts=accounts[:-2])
    accepted = transition_perps_margin_v1(_context(), below_max, command)
    assert isinstance(accepted, PerpsMarginAcceptedV1)
    assert len(accepted.post_state.accounts) == MAX_PERPS_MARGIN_ACCOUNTS_V1

    exact_max = _state(accounts=accounts[:-1])
    rejected = transition_perps_margin_v1(_context(), exact_max, command)
    assert isinstance(rejected, PerpsMarginRejectedV1)
    _assert_exact_noop(rejected, exact_max, PerpsMarginRejectCodeV1.ACCOUNT_LIMIT)

    with pytest.raises(ValueError, match="account count exceeds bound"):
        _state(accounts=accounts)


@pytest.mark.parametrize("field", ("index_price_e8", "maintenance_margin_bps"))
def test_bool_is_never_accepted_as_a_consensus_integer(field: str) -> None:
    values = {
        "module_release_id": _root(3),
        "market_id": "perp-btc-usd",
        "collateral_asset": "zUSD",
        "index_price_e8": 100_000_000,
        "maintenance_margin_bps": 500,
        "depeg_buffer_bps": 100,
        "max_position_abs": 1_000_000,
        "market_status": PerpsMarginMarketStatusV1.ACTIVE,
        "accounts": (),
    }
    values[field] = True

    with pytest.raises((TypeError, ValueError)):
        PerpsMarginStateV1(**values)
    with pytest.raises(TypeError, match="status is not closed"):
        PerpsMarginStateV1(**{**values, field: 1, "market_status": True})


def test_python_boundary_rejects_hostile_scalar_and_account_subclasses() -> None:
    class HostileText(str):
        def __eq__(self, other: object) -> bool:
            return True

    class HostileAccount(PerpsMarginAccountV1):
        pass

    with pytest.raises(TypeError, match="exact text"):
        replace(
            _command(PERPS_MARGIN_DEPOSIT_COMMAND_KIND_V1, amount_atoms=1, nonce=1),
            owner=HostileText("mallory"),
        )
    with pytest.raises(TypeError, match="exact typed values"):
        base = _account()
        _state(
            accounts=(
                HostileAccount(
                    base.account_id,
                    base.owner,
                    base.position_base,
                    base.entry_price_e8,
                    base.collateral_atoms,
                    base.nonce,
                    base.status,
                ),
            )
        )
    accepted = transition_perps_margin_v1(
        _context(),
        _state(),
        _command(PERPS_MARGIN_DEPOSIT_COMMAND_KIND_V1, amount_atoms=1, nonce=1),
    )
    assert isinstance(accepted, PerpsMarginAcceptedV1)
    with pytest.raises(TypeError, match="exact text"):
        replace(accepted, statement_root=HostileText(accepted.statement_root))
