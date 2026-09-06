"""Sparse debit authorization: checked theorems and finite runtime correspondence.

The oracle identifies every decreased key from independently summed endpoint
amounts, checks the declared sender/context and observes full accepted/rejected
histories; each fee-owner history has a nonempty role-specific decreased set.
Conserving unauthorized and reversed-debit mutants must fail it.
Negative amount/fee controls connect the model premises to exact constructors.
Signatures, selected-policy membership, replay, complete route admission and
universal Python/Rust/compiler refinement remain external obligations.
"""

from __future__ import annotations

import hashlib
import json
import re
from dataclasses import replace

import pytest

from src.core import asset_transfer_module_v1 as transfer
from src.core.asset_transfer_types_v1 import (
    AssetTransferAcceptedV1,
    AssetTransferCommandV1,
    AssetTransferContextV1,
    AssetTransferPolicyV1,
    AssetTransferRejectedV1,
    AssetTransferStateV1,
)
from src.core.global_settlement_types_v1 import (
    EconomicAmountV1,
    canonical_global_bytes_v1,
)
from tests.formal.test_lean_asset_transfer_sparse_tables_v1 import (
    Case,
    _balances_view,
    _case,
    _term,
)
from tests.formal.test_lean_asset_transfer_sparse_trace_v1 import (
    ROOT,
)
from tests.formal.test_lean_asset_transfer_sparse_trace_v1 import (
    compiled as trace_subject,  # noqa: F401 -- pytest imports the fresh-source fixture.
)
from tests.formal.test_lean_checked_epoch_economic_tables_v1 import (
    PROJECT,
    LeanSubject,
    _compile,
)

MODULE = "AssetTransferSparseAuthorizationV1"
NAMESPACE = f"Proofs.{MODULE}"
OPENS = f"open Proofs.GlobalSettlementCoreV2 Proofs.GlobalEconomicStateRefinementV2 {NAMESPACE}\n"
SUBJECTS = {
    "src/core/asset_transfer_module_v1.py": "754d75a37ad70868bf20263fc189fc9e4f5a77cb864d8a1c7973afc253c938d7",
    "src/core/asset_transfer_types_v1.py": "5757c8b692820613e1eac30b7103e857a73b42efebbdda62d0a4469511f41277",
    "lean-mathlib/Proofs/AssetTransferSparseTablesV1.lean": "5d303c709501cfe0604c3e845a3b2814b8c5ebe4f0fcfd4090bda2d697f077c0",
    "lean-mathlib/Proofs/AssetTransferSparseTraceV1.lean": "5a77ac04b4e214ab7d0dc6cb4b77e2369e16a7914d02cffb5df1d0b88f119b83",
}
ACCEPTED = "∀ {i : S.Input}, S.CanonicalBalances i.pre.balances → 0 ≤ i.command.amountAtoms → 0 ≤ i.policy.transferFeeAtoms → (S.step i).verdict = .accepted → "
HISTORY = "∀ (c : H.Config) (rs : List H.Request) (pre : GlobalState), S.CanonicalBalances pre.balances → 0 ≤ c.policy.transferFeeAtoms → (∀ r ∈ rs, 0 ≤ r.command.amountAtoms) → ∀ {o a d : String}, amountAt (H.run c rs pre).post.balances o a d < amountAt pre.balances o a d → "
TYPES = {
    "delta_non_sender_nonnegative": "∀ {pre : T.TransferState} {cmd : T.Command}, 0 ≤ cmd.amountAtoms → 0 ≤ pre.policy.transferFeeAtoms → ∀ {owner : String}, owner ≠ cmd.sender → 0 ≤ T.delta pre cmd owner",
    "accepted_non_sender_nondecreasing": ACCEPTED + "∀ o a d : String, o ≠ i.command.sender → amountAt i.pre.balances o a d ≤ amountAt (S.step i).post.balances o a d",
    "accepted_decrease_authorized": ACCEPTED + "∀ {o a d : String}, amountAt (S.step i).post.balances o a d < amountAt i.pre.balances o a d → o = i.command.sender ∧ i.command.sender = i.context.subjectId ∧ i.command.asset = a ∧ S.accounts = d",
    "step_outside_frame": "∀ {i : S.Input}, S.CanonicalBalances i.pre.balances → ∀ o a d : String, (i.command.asset ≠ a ∨ S.accounts ≠ d ∨ (o ≠ i.command.sender ∧ o ≠ i.command.recipient ∧ o ≠ i.policy.feeOwner)) → amountAt (S.step i).post.balances o a d = amountAt i.pre.balances o a d",
    "history_decrease_has_accepted_sender": HISTORY + "∃ before request suffix, rs = before ++ request :: suffix ∧ (S.step (H.inputFor c request (H.run c before pre).post)).verdict = .accepted ∧ o = request.command.sender ∧ request.command.sender = request.context.subjectId ∧ request.command.asset = a ∧ S.accounts = d ∧ amountAt (S.step (H.inputFor c request (H.run c before pre).post)).post.balances o a d < amountAt (H.run c before pre).post.balances o a d",
    "history_decrease_has_declared_subject": HISTORY + "∃ r ∈ rs, o = r.context.subjectId",
    "demo_authorized_debit": "S.CanonicalBalances S.demo.pre.balances ∧ 0 ≤ S.demo.command.amountAtoms ∧ 0 ≤ S.demo.policy.transferFeeAtoms ∧ (S.step S.demo).verdict = .accepted ∧ amountAt (S.step S.demo).post.balances \"alice\" \"USD\" S.accounts < amountAt S.demo.pre.balances \"alice\" \"USD\" S.accounts",
    "demo_rejected_then_accepted_debit": "(S.step (H.inputFor demoConfig rejectedDemoRequest S.demo.pre)).verdict = .rejected .unauthorizedSubject ∧ (S.step (H.inputFor demoConfig acceptedDemoRequest (H.run demoConfig [rejectedDemoRequest] S.demo.pre).post)).verdict = .accepted ∧ amountAt (H.run demoConfig [rejectedDemoRequest, acceptedDemoRequest] S.demo.pre).post.balances \"alice\" \"USD\" S.accounts < amountAt S.demo.pre.balances \"alice\" \"USD\" S.accounts",
    "negative_amount_requires_constructor_premise": "S.CanonicalBalances negativeAmount.pre.balances ∧ 0 ≤ negativeAmount.policy.transferFeeAtoms ∧ (S.step negativeAmount).verdict = .accepted ∧ amountAt negativeAmount.pre.balances \"bob\" \"USD\" S.accounts = 1 ∧ amountAt (S.step negativeAmount).post.balances \"bob\" \"USD\" S.accounts = 0 ∧ \"bob\" ≠ negativeAmount.command.sender",
    "negative_fee_requires_constructor_premise": "S.CanonicalBalances negativeFee.pre.balances ∧ 0 ≤ negativeFee.command.amountAtoms ∧ (S.step negativeFee).verdict = .accepted ∧ amountAt negativeFee.pre.balances \"treasury\" \"USD\" S.accounts = 1 ∧ amountAt (S.step negativeFee).post.balances \"treasury\" \"USD\" S.accounts = 0 ∧ \"treasury\" ≠ negativeFee.command.sender",
}
OBSERVERS = """
def resultView (input : S.Input) : List (List String) :=
  let output := S.step input
  let verdict := match output.verdict with
    | .accepted => "ACCEPTED"
    | .rejected code => code.code
  [[verdict]] ++ (output.post.balances.map fun r =>
    [r.owner, r.asset, r.custodyDomain, toString r.amountAtoms]) ++ [["EFFECTS"]] ++
    (output.plan.rows.map fun r =>
      [r.kind.code, r.principal, r.asset, r.custodyDomain, toString r.deltaAtoms])
"""


@pytest.fixture(scope="module")
def lean(trace_subject: LeanSubject) -> LeanSubject:  # noqa: F811
    captured = trace_subject.source / "Proofs" / f"{MODULE}.lean"
    captured.write_bytes((PROJECT / "Proofs" / f"{MODULE}.lean").read_bytes())
    result = _compile(trace_subject, captured, trace_subject.library / "Proofs" / f"{MODULE}.olean")
    assert result.returncode == 0, result.stdout + result.stderr
    assert result.stdout == result.stderr == ""
    return trace_subject


def _probe(lean: LeanSubject, name: str, body: str) -> str:
    path = lean.source / f"{name}.lean"
    path.write_text(f"import {NAMESPACE}\n" + OPENS + OBSERVERS + body)
    result = _compile(lean, path)
    assert result.returncode == 0, result.stdout + result.stderr
    assert result.stderr == ""
    return result.stdout


def test_independent_contracts_transitive_axioms_and_source_subject(lean: LeanSubject) -> None:
    source = (lean.source / "Proofs" / f"{MODULE}.lean").read_text()
    code = re.sub(r"/-.*?-/", "", source, flags=re.DOTALL)
    assert re.search(r"\b(sorry|admit|axiom|unsafe|native_decide)\b", code) is None
    assert set(re.findall(r"^theorem (\w+)", code, flags=re.MULTILINE)) == set(TYPES)
    text = "\n".join(f"example : {signature} := {name}\n#print axioms {NAMESPACE}.{name}"
                     for name, signature in TYPES.items())
    output = " ".join(_probe(lean, "Contracts", text).split())
    for name in TYPES:
        found = re.search(re.escape(f"'{NAMESPACE}.{name}' ") +
                          r"(?:depends on axioms: \[([^]]*)\]|does not depend on any axioms)", output)
        assert found, (name, output)
        axioms = {a.strip() for a in (found.group(1) or "").split(",") if a.strip()}
        assert axioms <= {"propext", "Quot.sound", "Classical.choice"}, (name, axioms)
    assert f"import {NAMESPACE}" in (PROJECT / "Proofs.lean").read_text().splitlines()
    for path, digest in SUBJECTS.items():
        assert hashlib.sha256((PROJECT.parent / path).read_bytes()).hexdigest() == digest


def _amount(rows: tuple[EconomicAmountV1, ...], key: tuple[str, str, str]) -> int:
    return sum(r.amount_atoms for r in rows if (r.owner, r.asset, r.custody_domain) == key)


def _debits(case: Case, post: AssetTransferStateV1) -> set[tuple[str, str, str]]:
    keys = {(r.owner, r.asset, r.custody_domain) for r in (*case.pre.balances, *post.balances)}
    keys |= {("ghost", "USD", "accounts"), (case.command.sender, "USD", "vault")}
    decreased = set()
    fee_owner = next(p.fee_owner for p in case.pre.policies if p.asset == case.command.asset)
    for key in keys:
        before, after = _amount(case.pre.balances, key), _amount(post.balances, key)
        if after < before:
            assert key[0] == case.command.sender, "debit owner differs from declared sender"
            assert case.command.sender == case.context.subject_id, "debit context differs from sender"
            assert key[1:] == (case.command.asset, "accounts"), "debit denomination differs"
            decreased.add(key)
        if (key[1] != case.command.asset or key[2] != "accounts" or
                key[0] not in (case.command.sender, case.command.recipient, fee_owner)):
            assert after == before, "unrelated balance changed"
    return decreased


def _runtime(case: Case) -> tuple[AssetTransferStateV1, list[list[str]]]:
    before = canonical_global_bytes_v1(case.pre)
    result = transfer.transition_asset_transfer_v1(case.context, case.pre, case.command)
    assert canonical_global_bytes_v1(case.pre) == before
    if case.error:
        assert isinstance(result, AssetTransferRejectedV1) and result.code.value == case.error
        assert result.effects.is_empty
        assert result.pre_state_root == result.post_state_root == case.pre.state_root
        return case.pre, [[case.error], *_balances_view(case.pre.balances), ["EFFECTS"]]
    assert isinstance(result, AssetTransferAcceptedV1)
    assert _debits(case, result.post_state) == {(case.command.sender, case.command.asset, "accounts")}
    return result.post_state, [["ACCEPTED"], *_balances_view(result.post_state.balances), ["EFFECTS"],
        *[[r.kind.value, r.principal, r.asset, r.custody_domain, str(r.delta_atoms)]
          for r in result.effects.rows]]


def test_actual_sparse_debits_context_and_frame_at_alias_and_width_boundaries(lean: LeanSubject) -> None:
    upper = (1 << 127) - 1
    cases = (
        _case("distinct"), _case("sender_fee", owner="alice"),
        _case("recipient_fee", owner="bob"), _case("zero_fee", fee=0),
        _case("reverse_roles", sender="bob", recipient="alice", owner="bob", amount=1),
        _case("zero_delete", rows=(("alice", "USD", 32), ("alice", "EUR", 7))),
        _case("u128_balance", fee=0, amount=1, rows=(("alice", "USD", (1 << 128) - 1),)),
        _case("i128_min", fee=1, amount=upper, rows=(("alice", "USD", upper + 1),)),
        _case("i128_max", fee=0, amount=upper, rows=(("alice", "USD", upper),)),
        _case("i128_overflow", fee=0, amount=upper + 1,
              rows=(("alice", "USD", upper + 1),), error="EFFECT_DELTA_OVERFLOW"),
        _case("unauthorized", subject="mallory", error="UNAUTHORIZED_SUBJECT"),
        _case("zero", amount=0, error="ZERO_AMOUNT"),
        _case("insufficient", amount=999, error="INSUFFICIENT_BALANCE"),
    )
    expected = [_runtime(case)[1] for case in cases]
    # One document: the pretty printer wraps wide lists over several lines.
    views = ",\n  ".join(f"resultView {_term(case)}" for case in cases)
    actual = json.loads(_probe(lean, "BoundaryCases", f"#eval IO.println (reprStr [{views}])"))
    assert actual == expected


# Fixed fee policy; accepted senders alternate and rejected attempts are interleaved.
REQUESTS = (
    ("mallory", "alice", "bob", 2, "UNAUTHORIZED_SUBJECT"),
    ("alice", "alice", "bob", 3, None),
    ("alice", "alice", "bob", 0, "ZERO_AMOUNT"),
    ("bob", "bob", "carol", 2, None),
    ("mallory", "bob", "alice", 1, "UNAUTHORIZED_SUBJECT"),
    ("carol", "carol", "alice", 1, None),
    ("alice", "alice", "carol", 999, "INSUFFICIENT_BALANCE"),
    ("alice", "alice", "bob", 1, None),
    ("bob", "bob", "alice", 3, None),
)
# Owners ending below their initial amount, per fee owner. Alice collecting every fee
# outweighs her two debits, so only bob's key satisfies the endpoint premise there.
DECREASED = {"treasury": {"alice", "bob"}, "alice": {"bob"}, "bob": {"alice"}}


def _endpoint(initial: Case, fee_owner: str) -> dict[tuple[str, str, str], int]:
    """Signed-event summation of the declared accepted requests, independent of the runtime."""
    fee = next(p.transfer_fee_atoms for p in initial.pre.policies if p.asset == "USD")
    amounts = {(r.owner, r.asset, r.custody_domain): r.amount_atoms for r in initial.pre.balances}
    for _, sender, recipient, atoms, error in REQUESTS:
        if error is not None:
            continue
        for owner, delta in ((sender, -atoms - fee), (recipient, atoms), (fee_owner, fee)):
            key = (owner, "USD", "accounts")
            amounts[key] = amounts.get(key, 0) + delta
    return amounts


@pytest.mark.parametrize("fee_owner", ("treasury", "alice", "bob"))
def test_history_decrease_has_actual_accepted_prefix_debit(lean: LeanSubject, fee_owner: str) -> None:
    initial = _case("history", owner=fee_owner, fee=1, amount=1,
                    rows=(("alice", "USD", 12), ("bob", "USD", 4), ("carol", "USD", 3),
                          ("alice", "EUR", 7), ("zebra", "EUR", 9)))
    state, expected, requests, witnesses = initial.pre, [], [], []
    for index, (subject, sender, recipient, atoms, error) in enumerate(REQUESTS):
        case = replace(initial, pre=state, error=error,
                       context=replace(initial.context, subject_id=subject),
                       command=replace(initial.command, sender=sender, recipient=recipient, amount_atoms=atoms))
        state, view = _runtime(case)
        expected += [["STEP", str(index)], *view]
        if error is None:
            witnesses.append((index, _debits(case, state), subject))
        requests.append(f'⟨⟨{json.dumps(ROOT)}, {json.dumps(subject)}⟩, '
                        f'⟨"asset_transfer", "USD", {json.dumps(sender)}, {json.dumps(recipient)}, {atoms}, 1⟩⟩')
    endpoint = _endpoint(initial, fee_owner)
    assert {key: atoms for key, atoms in endpoint.items() if atoms} == {
        (r.owner, r.asset, r.custody_domain): r.amount_atoms for r in state.balances}
    decreases = {key for key, atoms in endpoint.items() if atoms < _amount(initial.pre.balances, key)}
    assert {owner for owner, _, _ in decreases} == DECREASED[fee_owner]
    assert len(witnesses) == 5
    assert all(any(key in debits and key[0] == subject for _, debits, subject in witnesses)
               for key in decreases)
    expected += [["COUNT", "5"], *_balances_view(state.balances)]
    body = f"""
def initialInput : S.Input := {_term(initial)}
def config : H.Config := ⟨initialInput.moduleReleaseId, initialInput.policy⟩
def requests : List H.Request := [{','.join(requests)}]
def observation : List (List String) :=
  (requests.zipIdx.flatMap fun pair =>
    [["STEP", toString pair.2]] ++ resultView
      (H.inputFor config pair.1 (H.run config (requests.take pair.2) initialInput.pre).post)) ++
  [["COUNT", toString (H.run config requests initialInput.pre).acceptedPlans.length]] ++
  ((H.run config requests initialInput.pre).post.balances.map fun r =>
    [r.owner, r.asset, r.custodyDomain, toString r.amountAtoms])
#eval IO.println (reprStr observation)
"""
    assert json.loads(_probe(lean, f"History_{fee_owner}", body)) == expected


@pytest.mark.parametrize("value", (-1, -(1 << 127), True, False, 1 << 128))
def test_runtime_constructors_reject_missing_model_lower_bounds_and_widths(value: int) -> None:
    suffix = "must fit an unsigned 128-bit integer" if type(value) is int and value >= 0 else "must be a non-negative integer"
    with pytest.raises(ValueError, match=f"^asset transfer command amount {suffix}$"):
        AssetTransferCommandV1("asset_transfer", "USD", "alice", "bob", value, 0)
    with pytest.raises(ValueError, match=f"^asset transfer policy fee atoms {suffix}$"):
        AssetTransferPolicyV1("USD", "treasury", value, True)


@pytest.mark.parametrize("mutant", ("subject_guard", "reversed_debit"))
def test_conserving_unauthorized_semantic_mutants_are_detected(
    monkeypatch: pytest.MonkeyPatch, mutant: str,
) -> None:
    case = _case(mutant, fee=0, amount=1, subject="mallory" if mutant == "subject_guard" else "alice")
    if mutant == "subject_guard":
        original_policy = transfer._transfer_policy

        def bypass(context: AssetTransferContextV1, state: AssetTransferStateV1,
                   command: AssetTransferCommandV1) -> AssetTransferPolicyV1 | transfer.AssetTransferRejectCodeV1:
            return original_policy(replace(context, subject_id=command.sender), state, command)

        monkeypatch.setattr(transfer, "_transfer_policy", bypass)
        reason = "debit context differs from sender"
    else:
        original_deltas = transfer._transfer_deltas

        def reverse(command: AssetTransferCommandV1, policy: AssetTransferPolicyV1
                    ) -> dict[str, int] | transfer.AssetTransferRejectCodeV1:
            return original_deltas(replace(command, sender=command.recipient, recipient=command.sender), policy)

        monkeypatch.setattr(transfer, "_transfer_deltas", reverse)
        reason = "debit owner differs from declared sender"
    outcome = transfer.transition_asset_transfer_v1(case.context, case.pre, case.command)
    assert isinstance(outcome, AssetTransferAcceptedV1)
    assert sum(r.amount_atoms for r in outcome.post_state.balances) == sum(r.amount_atoms for r in case.pre.balances)
    with pytest.raises(AssertionError, match=reason):
        _debits(case, outcome.post_state)
