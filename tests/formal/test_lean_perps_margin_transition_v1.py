"""Current margin semantics: independent cases, Lean decisions, full Rust/Python results.

The Lean input projects the selected account and market count. Complete market
reconstruction, effects, ports and journals are checked below against both
runtimes; this is finite correspondence, not a proof of either implementation.
"""

from __future__ import annotations

import importlib.util
import json
import os
import subprocess
from dataclasses import dataclass, fields, replace
from pathlib import Path

import pytest

from src.core.global_settlement_types_v1 import (
    MAX_ATOMS_V1,
    MAX_DELTA_ATOMS_V1,
    MAX_U64_V1,
    canonical_global_bytes_v1,
)
from src.core.perps_margin_module_v1 import transition_perps_margin_v1
from src.core.perps_margin_types_v1 import (
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
from tests.core.test_perps_margin_module_v1 import (
    _account,
    _command,
    _context,
    _counterparty,
    _root,
    _state,
)
from tests.formal.lean_stdlib_gate_v1 import (
    TheoremReference,
    _pinned_lean_executable,
    _run,
    check_lean_stdlib_source,
)

ROOT = Path(__file__).resolve().parents[2]
MODULE = "Proofs.PerpsMarginTransitionV1"
NS = "ZenoDEX.PerpsMarginTransitionV1"
KINDS = {
    "perps_margin_deposit": "deposit",
    "perps_margin_withdraw": "withdraw",
    "perps_margin_close": "close",
}
REJECTS = dict(
    zip(
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
)


@dataclass(frozen=True)
class Case:
    name: str
    context: PerpsMarginContextV1
    state: PerpsMarginStateV1
    command: PerpsMarginCommandV1
    expected: str


def _cases() -> list[Case]:
    context, state = _context(), _state(accounts=(_account(collateral_atoms=25),))
    deposit = _command("perps_margin_deposit", amount_atoms=1, nonce=2)
    withdraw = replace(deposit, command_kind="perps_margin_withdraw")
    close = replace(deposit, command_kind="perps_margin_close", amount_atoms=0)
    positioned = _state(accounts=(_account(position_base=10), _counterparty()))
    result: list[Case] = []

    def add(name, expected, *, ctx=context, pre=state, command=deposit):
        result.append(Case(name, ctx, pre, command, expected))

    add("deposit", "ACCEPTED")
    add(
        "release_before_unknown",
        "RELEASE_MISMATCH",
        ctx=replace(context, module_release_id=_root(99)),
        command=replace(deposit, command_kind="unknown"),
    )
    add(
        "unknown_before_halt",
        "UNKNOWN_COMMAND",
        pre=replace(state, market_status=PerpsMarginMarketStatusV1.HALTED),
        command=replace(deposit, command_kind="unknown"),
    )
    add("halt", "HALTED_MARKET", pre=replace(state, market_status=PerpsMarginMarketStatusV1.HALTED))
    add(
        "drain_deposit",
        "MARKET_DRAIN_ONLY",
        pre=replace(state, market_status=PerpsMarginMarketStatusV1.DRAIN_ONLY),
    )
    add(
        "market_before_asset",
        "MARKET_MISMATCH",
        command=replace(deposit, market_id="wrong", asset="wrong"),
    )
    add(
        "asset_before_subject",
        "ASSET_MISMATCH",
        command=replace(deposit, asset="wrong", owner="mallory"),
    )
    add("subject", "UNAUTHORIZED_SUBJECT", ctx=replace(context, subject_id="mallory"))
    add(
        "surplus_oracle_before_nonce",
        "UNEXPECTED_ORACLE_AUTHORITY",
        ctx=_context(with_oracle=True),
        command=replace(deposit, nonce=0),
    )
    add("missing", "ACCOUNT_MISSING", pre=_state(), command=withdraw)
    for count in (63, 64):
        accounts = tuple(
            replace(_account(collateral_atoms=0), account_id=f"a-{i:02}") for i in range(count)
        )
        add(
            f"count_{count}",
            "ACCEPTED" if count == 63 else "ACCOUNT_LIMIT",
            pre=_state(accounts=accounts),
            command=replace(deposit, nonce=1),
        )
    add("missing_before_limit", "ACCOUNT_MISSING", pre=_state(accounts=accounts), command=withdraw)
    add(
        "drain_withdraw",
        "ACCEPTED",
        pre=replace(state, market_status=PerpsMarginMarketStatusV1.DRAIN_ONLY),
        command=withdraw,
    )
    empty = _state(
        accounts=(_account(collateral_atoms=0),), market_status=PerpsMarginMarketStatusV1.DRAIN_ONLY
    )
    add("drain_close", "ACCEPTED", pre=empty, command=close)
    add(
        "closed_repeat",
        "ACCOUNT_CLOSED",
        pre=replace(
            empty,
            accounts=(_account(collateral_atoms=0, status=PerpsMarginAccountStatusV1.CLOSED),),
        ),
        command=close,
    )
    add(
        "owner_before_nonce",
        "ACCOUNT_OWNER_MISMATCH",
        ctx=replace(context, subject_id="mallory"),
        command=replace(deposit, owner="mallory", nonce=0),
    )
    add(
        "closed_before_nonce",
        "ACCOUNT_CLOSED",
        pre=_state(
            accounts=(_account(collateral_atoms=0, status=PerpsMarginAccountStatusV1.CLOSED),)
        ),
        command=replace(deposit, nonce=0),
    )
    add("nonce_exhausted", "NONCE_OVERFLOW", pre=_state(accounts=(_account(nonce=MAX_U64_V1),)))
    add("nonce", "NONCE_MISMATCH", command=replace(deposit, nonce=1))
    add("oracle_missing", "ORACLE_AUTHORITY_MISSING", pre=positioned, command=withdraw)
    add(
        "oracle_wrong_price",
        "ORACLE_PRICE_MISMATCH",
        pre=positioned,
        ctx=_context(with_oracle=True, oracle_price_e8=100_000_001),
        command=withdraw,
    )
    add(
        "flat_surplus_oracle",
        "UNEXPECTED_ORACLE_AUTHORITY",
        ctx=_context(with_oracle=True),
        command=withdraw,
    )
    add(
        "close_amount_before_position",
        "INVALID_CLOSE_AMOUNT",
        pre=positioned,
        command=replace(close, amount_atoms=1),
    )
    add("close_position_before_collateral", "POSITION_OPEN", pre=positioned, command=close)
    add("close_collateral", "COLLATERAL_REMAINS", command=close)
    add("zero", "ZERO_AMOUNT", command=replace(deposit, amount_atoms=0))
    add(
        "delta_overflow",
        "EFFECT_DELTA_OVERFLOW",
        command=replace(deposit, amount_atoms=MAX_DELTA_ATOMS_V1 + 1),
    )
    add(
        "balance_overflow",
        "BALANCE_OVERFLOW",
        pre=_state(accounts=(_account(collateral_atoms=MAX_ATOMS_V1),)),
    )
    add("insufficient", "INSUFFICIENT_COLLATERAL", command=replace(withdraw, amount_atoms=26))
    for amount in (39_999_999, 40_000_000, 40_000_001):
        add(
            f"maintenance_{amount}",
            "MAINTENANCE_BREACH" if amount > 40_000_000 else "ACCEPTED",
            pre=positioned,
            ctx=_context(with_oracle=True),
            command=replace(withdraw, amount_atoms=amount),
        )
    add("delta_max", "ACCEPTED", command=replace(deposit, amount_atoms=MAX_DELTA_ATOMS_V1))
    add(
        "balance_max",
        "ACCEPTED",
        pre=_state(accounts=(_account(collateral_atoms=MAX_ATOMS_V1 - 1),)),
    )
    add(
        "nonce_max",
        "ACCEPTED",
        pre=_state(accounts=(_account(nonce=MAX_U64_V1 - 1),)),
        command=replace(deposit, nonce=MAX_U64_V1),
    )
    # Fractional requirement: ceil(1 * 10001 * 1 / 10000) is two quote atoms.
    fractional = replace(
        positioned,
        index_price_e8=10_001,
        maintenance_margin_bps=1,
        depeg_buffer_bps=0,
        accounts=tuple(
            replace(
                a,
                position_base=1 if a.position_base > 0 else -1,
                entry_price_e8=10_001,
                collateral_atoms=3,
            )
            for a in positioned.accounts
        ),
    )
    for amount in (1, 2):
        add(
            f"ceil_{amount}",
            "ACCEPTED" if amount == 1 else "MAINTENANCE_BREACH",
            pre=fractional,
            ctx=_context(with_oracle=True, oracle_price_e8=10_001),
            command=replace(withdraw, amount_atoms=amount),
        )
    return result


def _plain(value):
    return json.loads(canonical_global_bytes_v1(value))


def _output(value):
    body = {field.name: getattr(value, field.name) for field in fields(value)}
    if isinstance(value, PerpsMarginAcceptedV1):
        body["private_port"] = value.private_port.to_canonical()
    else:
        body["code"] = value.code.value
    return _plain(body)


def _account_literal(a) -> str:
    return (
        "⟨"
        + ", ".join(
            (
                json.dumps(a.account_id),
                json.dumps(a.owner),
                f"({a.position_base})",
                str(a.entry_price_e8),
                str(a.collateral_atoms),
                str(a.nonce),
                str(a.status is PerpsMarginAccountStatusV1.CLOSED).lower(),
            )
        )
        + "⟩"
    )


def _lean_case(case: Case, result) -> str:
    ctx, m, c = case.context, case.state, case.command
    context = f"⟨{json.dumps(ctx.module_release_id)}, {json.dumps(ctx.subject_id)}, {str(ctx.has_oracle_authority).lower()}, {ctx.oracle_price_e8}⟩"
    status = {"ACTIVE": "active", "DRAIN_ONLY": "drainOnly", "HALTED": "halted"}[
        m.market_status.value
    ]
    market = f"⟨{json.dumps(m.module_release_id)}, {json.dumps(m.market_id)}, {json.dumps(m.collateral_asset)}, {m.index_price_e8}, {m.maintenance_margin_bps}, {m.depeg_buffer_bps}, .{status}, {len(m.accounts)}⟩"
    command = f"⟨.{KINDS.get(c.command_kind, 'unknown')}, {json.dumps(c.account_id)}, {json.dumps(c.market_id)}, {json.dumps(c.owner)}, {json.dumps(c.asset)}, {c.amount_atoms}, {c.nonce}⟩"
    account = m.account(c.account_id)
    assert account is None or account.account_id == c.account_id
    pre = "none" if account is None else f"(some {_account_literal(account)})"
    if isinstance(result, PerpsMarginRejectedV1):
        arms = f"| .error code => decide ((code : Reject) = Reject.{REJECTS[result.code.value]})\n| .ok _ => false"
    else:
        arms = f"| .ok a => decide ((a : Account) = ({_account_literal(result.post_state.account(c.account_id))} : Account))\n| .error _ => false"
    return f"-- {case.name}\n#eval match step {context} {market} {command} {pre} with\n{arms}"


@pytest.fixture(scope="module")
def lean_closure(tmp_path_factory):
    tmp = tmp_path_factory.mktemp("perps-margin-proof")
    references = (
        TheoremReference(
            f"{NS}.accepted_subject_owns_account",
            f"∀ ctx m c pre b, {NS}.step ctx m c pre = .ok b → b.owner = c.owner ∧ c.owner = ctx.subject",
        ),
        TheoremReference(
            f"{NS}.fixed_account_closed_history_is_absorbing",
            f"∀ inputs a, a.closed = true → (∀ x ∈ inputs, x.2.2.accountId = a.id) → {NS}.run inputs (some a) = some a",
        ),
        TheoremReference(
            f"{NS}.withdraw_exact_and_covered",
            f"∀ m c a b, c.kind = .withdraw → {NS}.postAccount m c a = .ok b → b.collateral + c.amount = a.collateral ∧ 0 < c.amount ∧ c.amount ≤ {NS}.maxDelta ∧ (a.position ≠ 0 → {NS}.maintenance m a ≤ b.collateral)",
        ),
        TheoremReference(
            f"{NS}.ceilQuote_minimal",
            f"∀ n k, n ≤ 10000 * k → {NS}.ceilQuote n ≤ k",
        ),
        TheoremReference(
            f"{NS}.flat_account_can_drain_and_close",
            f"∀ ctx m a, ctx.release = m.release → ctx.subject = a.owner → m.status ≠ .halted → ctx.hasOracle = false → a.closed = false → a.position = 0 → 0 < a.collateral → a.collateral ≤ {NS}.maxDelta → a.nonce + 2 ≤ {NS}.maxNonce → {NS}.run [(ctx, m, {NS}.drainCommand m a), (ctx, m, {NS}.closeCommand m a)] (some a) = some {{ a with collateral := 0, nonce := a.nonce + 2, closed := true }}",
        ),
        TheoremReference(
            f"{NS}.accepted_close_is_exact_tombstone",
            f"∀ ctx m c a b, {NS}.Selected c (some a) → c.kind = .close → {NS}.step ctx m c (some a) = .ok b → a.closed = false ∧ a.position = 0 ∧ a.collateral = 0 ∧ c.amount = 0 ∧ c.nonce = a.nonce + 1 ∧ b = {{ a with nonce := c.nonce, closed := true }} ∧ a.id = c.accountId ∧ b.owner = ctx.subject",
        ),
    )
    check_lean_stdlib_source("Proofs/PerpsMarginTransitionV1.lean", references, tmp)
    return tmp


@pytest.fixture(scope="module")
def rust_driver(tmp_path_factory):
    target = tmp_path_factory.mktemp("perps-margin-rust")
    env = dict(os.environ, CARGO_PROFILE_DEV_DEBUG="0", CARGO_INCREMENTAL="0")
    subprocess.run(
        [
            "cargo",
            "+1.87.0",
            "build",
            "--offline",
            "--locked",
            "--manifest-path",
            str(ROOT / "zk/global_settlement_abi_v1/Cargo.toml"),
            "--example",
            "perps_margin_outcomes_v1",
            "--target-dir",
            str(target),
        ],
        cwd=ROOT,
        env=env,
        check=True,
        capture_output=True,
        timeout=180,
    )
    return target / "debug/examples/perps_margin_outcomes_v1"


def _assert_case(case: Case, result) -> None:
    if case.expected != "ACCEPTED":
        assert isinstance(result, PerpsMarginRejectedV1), case.name
        assert result.code.value == case.expected, case.name
        assert result.pre_state_root == result.post_state_root == case.state.state_root
        assert result.effects.is_empty
        return
    assert isinstance(result, PerpsMarginAcceptedV1), case.name
    c, post = case.command, result.post_state
    original = case.state.account(c.account_id)
    account = post.account(c.account_id)
    assert isinstance(account, PerpsMarginAccountV1)
    assert account.owner == c.owner == case.context.subject_id
    assert account.nonce == c.nonce == (0 if original is None else original.nonce) + 1
    assert (account.position_base, account.entry_price_e8) == (
        (0, 0) if original is None else (original.position_base, original.entry_price_e8)
    )
    # Every unrelated account and every market parameter must survive exactly.
    assert tuple(a for a in case.state.accounts if a.account_id != c.account_id) == tuple(
        a for a in post.accounts if a.account_id != c.account_id
    )
    assert replace(post, accounts=case.state.accounts) == case.state
    direction = 1 if c.command_kind == "perps_margin_deposit" else -1
    close = c.command_kind == "perps_margin_close"
    if close:
        assert original is not None
        assert (
            original.collateral_atoms
            == account.collateral_atoms
            == account.position_base
            == c.amount_atoms
            == 0
        )
        assert account.status is PerpsMarginAccountStatusV1.CLOSED
    else:
        assert (
            account.collateral_atoms
            == (0 if original is None else original.collateral_atoms) + direction * c.amount_atoms
        )
        assert account.status is PerpsMarginAccountStatusV1.OPEN
    expected_rows = (
        []
        if close
        else [
            ("ACCOUNT_MOVEMENT", c.owner, c.asset, "accounts", -direction * c.amount_atoms),
            ("CUSTODY", c.account_id, c.asset, "perps_margin", direction * c.amount_atoms),
            ("LIABILITY", c.owner, c.asset, "perps_margin", direction * c.amount_atoms),
        ]
    )
    assert [
        (r.kind.value, r.principal, r.asset, r.custody_domain, r.delta_atoms)
        for r in result.effects.rows
    ] == expected_rows
    assert result.effects.occurrence_consumptions == (case.context.command_occurrence_id,)
    assert result.effects.external_outbox_enqueue == ()
    assert result.effects.asset_conservation == result.effects.fee_conservation == ()
    assert len(result.effects.lane_writes) == 1
    write = result.effects.lane_writes[0]
    assert (write.lane_id.value, write.pre_root, write.post_root) == (
        "PERPS_MARKET",
        case.state.state_root,
        post.state_root,
    )
    assert result.terminal_obligations == post.terminal_obligations


def _compare(cases: list[Case], lean_closure: Path, rust_driver: Path, tmp_path: Path):
    results, inputs, observations = [], [], []
    for case in cases:
        before = canonical_global_bytes_v1(case.state)
        result = transition_perps_margin_v1(case.context, case.state, case.command)
        assert canonical_global_bytes_v1(case.state) == before, case.name
        _assert_case(case, result)
        results.append(result)
        inputs.append(
            canonical_global_bytes_v1(
                {"context": case.context, "state": case.state, "command": case.command}
            ).decode()
        )
        observations.append(_lean_case(case, result))
    proc = subprocess.run(
        [str(rust_driver)],
        input="\n".join(inputs) + "\n",
        text=True,
        capture_output=True,
        check=True,
        timeout=45,
    )
    assert [json.loads(line) for line in proc.stdout.splitlines()] == [_output(r) for r in results]
    probe = tmp_path / "Cases.lean"
    probe.write_text(f"import {MODULE}\nopen {NS}\n" + "\n".join(observations) + "\n")
    setup = tmp_path / "setup.json"
    setup.write_text(
        json.dumps(
            {
                "name": "Cases",
                "package?": None,
                "isModule": False,
                "imports?": None,
                "importArts": {
                    MODULE: [str(lean_closure / "library/Proofs/PerpsMarginTransitionV1.olean")]
                },
                "dynlibs": [],
                "plugins": [],
                "options": {},
            }
        )
    )
    output = _run(
        _pinned_lean_executable(), ["--setup", str(setup), str(probe)], cwd=tmp_path
    ).stdout
    assert output.splitlines() == ["true"] * len(cases), output
    return results


def test_current_margin_ordered_outcomes_match_lean_and_rust(lean_closure, rust_driver, tmp_path):
    cases = _cases()
    # Arithmetic overflow is unreachable after the constructor's market envelope;
    # the formal post-account guard is retained for views outside that premise.
    assert {c.expected for c in cases} == {
        "ACCEPTED",
        *(code.value for code in PerpsMarginRejectCodeV1 if code.value != "ARITHMETIC_OVERFLOW"),
    }
    _compare(cases, lean_closure, rust_driver, tmp_path)


def test_margin_drain_history_and_tombstone_match_all_three(lean_closure, rust_driver, tmp_path):
    pre = _state()
    cases = []
    for index, (kind, amount, nonce, subject, expected) in enumerate(
        (
            ("deposit", 25, 1, "alice", "ACCEPTED"),
            ("withdraw", 25, 2, "mallory", "UNAUTHORIZED_SUBJECT"),
            ("withdraw", 25, 2, "alice", "ACCEPTED"),
            ("close", 0, 3, "alice", "ACCEPTED"),
            ("deposit", 1, 4, "alice", "ACCOUNT_CLOSED"),
            ("withdraw", 1, 4, "alice", "ACCOUNT_CLOSED"),
            ("close", 0, 4, "alice", "ACCOUNT_CLOSED"),
        )
    ):
        case = Case(
            f"history_{index}",
            replace(_context(subject_id=subject), command_occurrence_id=_root(20 + index)),
            pre,
            _command(f"perps_margin_{kind}", amount_atoms=amount, nonce=nonce),
            expected,
        )
        cases.append(case)
        result = transition_perps_margin_v1(case.context, case.state, case.command)
        if isinstance(result, PerpsMarginAcceptedV1):
            pre = result.post_state
    results = _compare(cases, lean_closure, rust_driver, tmp_path)
    closed = results[3]
    assert isinstance(closed, PerpsMarginAcceptedV1)
    account = closed.post_state.accounts[0]
    assert (
        account.collateral_atoms,
        account.position_base,
        account.nonce,
        account.status.value,
    ) == (0, 0, 3, "CLOSED")
    assert [(o.claimant, o.amount_atoms, o.status.value) for o in closed.terminal_obligations] == [
        ("alice", 0, "DRAINED")
    ]
    assert closed.effects.rows == ()
    assert closed.effects.occurrence_consumptions == (_root(23),)
    assert len(closed.effects.lane_writes) == 1


@pytest.mark.parametrize(
    "name,old,new,case_name",
    (
        (
            "tombstone",
            "if account is not None and account.status is PerpsMarginAccountStatusV1.CLOSED:",
            "if False and account is not None and account.status is PerpsMarginAccountStatusV1.CLOSED:",
            "closed_repeat",
        ),
        (
            "sibling",
            "accounts[account.account_id] = account",
            "accounts[account.account_id] = account\n    other = next((key for key in sorted(accounts) if key != account.account_id), None)\n    if other is not None:\n        accounts[other] = replace(accounts[other], collateral_atoms=accounts[other].collateral_atoms + 1)",
            "count_63",
        ),
        (
            "subject",
            "if command.owner != context.subject_id:",
            "if False and command.owner != context.subject_id:",
            "subject",
        ),
        ("rounding", "return quotient + int(remainder != 0)", "return quotient", "ceil_2"),
        (
            "nonce",
            "return replace(account, collateral_atoms=collateral_atoms, nonce=command.nonce)",
            "return replace(account, collateral_atoms=collateral_atoms, nonce=account.nonce)",
            "deposit",
        ),
        (
            "claimant",
            "EconomicEffectKindV1.LIABILITY,\n            command.owner,",
            'EconomicEffectKindV1.LIABILITY,\n            "mallory",',
            "deposit",
        ),
    ),
)
def test_independent_cases_kill_executable_runtime_mutants(name, old, new, case_name, tmp_path):
    source = (ROOT / "src/core/perps_margin_module_v1.py").read_text()
    assert source.count(old) == 1
    mutated = tmp_path / f"{name}.py"
    mutated.write_text(source.replace(old, new, 1))
    spec = importlib.util.spec_from_file_location(f"src.core._margin_mutant_{name}", mutated)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    case = next(c for c in _cases() if c.name == case_name)
    # Both paths execute successfully; setup errors or constructor crashes are not kills.
    _assert_case(case, transition_perps_margin_v1(case.context, case.state, case.command))
    candidate = module.transition_perps_margin_v1(case.context, case.state, case.command)
    assert isinstance(candidate, PerpsMarginAcceptedV1)
    with pytest.raises(AssertionError):
        _assert_case(case, candidate)
