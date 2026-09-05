"""Fresh Lean checks and bounded runtime comparisons for complete physical rows.

The model covers full keys, amounts, domain separation and per-asset accounting.
Token decoding, row ceilings, canonical order/bytes and publication remain outside
the theorem. Runtime comparisons below use exact, freshly constructed values.
"""

from __future__ import annotations

import json
import os
import re
import shutil
import subprocess
from dataclasses import replace
from pathlib import Path

import pytest

from src.core.asset_lane_projection_v1 import AssetLaneStateProjectionV1
from src.core.asset_transfer_lane_module_custody_v1 import (
    transition_asset_transfer_lane_module_custody_v1,
)
from src.core.asset_transfer_lane_module_v1 import AssetTransferLaneModuleAcceptedV1
from src.core.asset_transfer_types_v1 import AssetTransferRejectedV1
from src.core.global_economic_state_delta_v1 import (
    _amount_delta_rows_v1,
    _checked_signed_delta_v1,
)
from src.core.global_settlement_types_v1 import (
    AssetSupplyV1,
    EconomicAmountV1,
    EconomicEffectKindV1,
    canonical_global_bytes_v1,
)
from tools.render_asset_lane_custody_coordinator_v1_golden import positive_inputs

ROOT = Path(__file__).resolve().parents[2]
LEAN_ROOT = ROOT / "lean-mathlib"
MODULE = "FiniteEconomicRowProjectionV1"
NAMESPACE = f"Proofs.{MODULE}"
PROOF = LEAN_ROOT / "Proofs" / f"{MODULE}.lean"
HEADER = f"import {NAMESPACE}\nopen {NAMESPACE}\n"
ROOT_VALUE = "0x" + "1" * 64


def _check(path: Path, library: Path, output: Path | None = None):
    # Keep environment local: a failed fixture must never expose it in pytest.
    environment = dict(os.environ)
    environment["LEAN_PATH"] = str(library)
    args = ["lean", "-DwarningAsError=true"]
    if output is not None:
        args += ["-R", str(LEAN_ROOT), "-o", str(output)]
    return subprocess.run(
        [*args, str(path)],
        cwd=LEAN_ROOT,
        env=environment,
        capture_output=True,
        text=True,
        check=False,
        timeout=60,
    )


@pytest.fixture(scope="module")
def lean_library(tmp_path_factory):
    assert shutil.which("lean") is not None, "pinned Lean installation required"
    assert (LEAN_ROOT / "lean-toolchain").read_text().strip() == "leanprover/lean4:v4.27.0"
    version = subprocess.run(
        ["lean", "--version"],
        cwd=LEAN_ROOT,
        capture_output=True,
        text=True,
        check=True,
        timeout=10,
    )
    assert "version 4.27.0," in version.stdout
    library = tmp_path_factory.mktemp("finite-economic-rows")
    (library / "Proofs").mkdir()
    for name in ("CheckedSignedDeltaRefinementV1", MODULE):
        result = _check(
            LEAN_ROOT / "Proofs" / f"{name}.lean",
            library,
            library / "Proofs" / f"{name}.olean",
        )
        assert result.returncode == 0, result.stdout + result.stderr
    return library


def _eval(source, expected, library, path):
    path.write_text(HEADER + source)
    result = _check(path, library)
    assert result.returncode == 0, result.stdout + result.stderr
    assert [json.loads(line) for line in result.stdout.splitlines()] == expected


def _key(key):
    return "⟨" + ", ".join(map(json.dumps, key)) + "⟩"


def _rows(rows):
    return "[" + ", ".join(f"⟨{_key(key)}, {amount}⟩" for key, amount in rows) + "]"


def _supplies(rows):
    return "[" + ", ".join(f"({json.dumps(a)}, {n})" for a, n in rows) + "]"


def _row_values(rows):
    return [(row.key, row.amount_atoms) for row in rows]


def test_projection_theorems_compile_without_added_axioms(lean_library, tmp_path):
    declarations = re.sub(r"/-.*?-/", "", PROOF.read_text(), flags=re.DOTALL)
    assert re.search(r"\b(sorry|admit|axiom)\b", declarations) is None
    names = re.findall(r"^theorem (\w+)", declarations, re.MULTILINE)
    assert {
        "finite_lookup_assetTotal",
        "accepted_projection_derived_lookup_supply",
        "checked_keyed_delta",
        "checked_keyed_delta_rejects_iff",
        "aggregate_eq_lookup",
        "elide_preserves_assetTotal",
        "unionKeys_unique_and_covers",
        "assetDeltaSum_eq_total_difference",
        "accepted_equal_supply_delta_zero",
    } <= set(names)
    probe = tmp_path / "Axioms.lean"
    probe.write_text(HEADER + "\n".join(f"#print axioms {NAMESPACE}.{n}" for n in names))
    result = _check(probe, lean_library)
    assert result.returncode == 0, result.stdout + result.stderr
    assert all(f"'{NAMESPACE}.{n}'" in result.stdout for n in names)
    axioms = {
        item.strip()
        for group in re.findall(r"depends on axioms:\s*\[([^\]]*)\]", result.stdout)
        for item in group.split(",")
        if item.strip()
    }
    assert axioms <= {"propext", "Quot.sound", "Classical.choice"}


def _runtime_projection_accepts(balances, custody, supplies):
    def construct(rows):
        return tuple(EconomicAmountV1(k[1], k[0], k[2], n) for k, n in rows)

    try:
        AssetLaneStateProjectionV1(
            ROOT_VALUE,
            ROOT_VALUE,
            construct(balances),
            construct(custody),
            tuple(AssetSupplyV1(a, n) for a, n in supplies),
        )
    except (ValueError, TypeError):
        return False
    return True


def test_projection_admission_independent_guard_failures_and_boundaries(lean_library, tmp_path):
    accounts = [(("A", "alice", "accounts"), 10), (("B", "alice", "accounts"), 20)]
    custody = [
        (("A", "alice", "escrow"), 4),
        (("A", "alice", "vault"), 3),
        (("B", "bob", "vault"), 5),
    ]
    cases = [
        (accounts, custody, [("A", 17), ("B", 25)], True),
        ([], [], [], True),
        ([], [], [("A", 0)], True),
        # Unequal duplicate amounts: totals alone cannot certify a lookup view.
        ([(accounts[0][0], 9), accounts[0], accounts[1]], custody, [("A", 26), ("B", 25)], False),
        (accounts, [custody[0], (custody[0][0], 6), *custody[1:]], [("A", 23), ("B", 25)], False),
        (accounts, custody, [("A", 17), ("A", 17), ("B", 25)], False),
        (accounts, [(("A", "carol", "accounts"), 7)], [("A", 17), ("B", 20)], False),
        ([(("A", "alice", "vault"), 10)], [], [("A", 10)], False),
        (accounts, custody, [("A", 17)], False),
        (accounts, custody, [("A", 18), ("B", 24)], False),
        ([(accounts[0][0], 0)], [], [("A", 0)], False),
        ([(accounts[0][0], 2**128)], [], [("A", 2**128)], False),
        ([(accounts[0][0], 2**128 - 1)], [], [("A", 2**128 - 1)], True),
        ([(accounts[0][0], 2**128 - 1)], [(("A", "alice", "vault"), 1)], [("A", 2**128)], False),
    ]
    source = ""
    expected = []
    for balances, vaults, supplies, accept in cases:
        assert _runtime_projection_accepts(balances, vaults, supplies) is accept
        source += f"#eval checkProjection {_rows(balances)} {_rows(vaults)} {_supplies(supplies)}\n"
        expected.append(accept)
    _eval(source, expected, lean_library, tmp_path / "Admission.lean")


def _runtime_histories():
    cases = positive_inputs()
    original = next(value for name, value in cases if name == "custody_7")
    split = replace(
        original,
        custody=(
            EconomicAmountV1("alice", "USD", "escrow", 4),
            EconomicAmountV1("alice", "USD", "vault", 3),
        ),
    )
    cases.append(("same_owner_distinct_domains", split))
    cases.append(
        ("new_recipient_key", replace(split, command=replace(split.command, recipient="carol")))
    )
    # Drain the sender, so the post projection must elide its zero row.
    cases.append(
        ("sender_terminal_zero", replace(split, command=replace(split.command, amount_atoms=98)))
    )
    first = transition_asset_transfer_lane_module_custody_v1(original)
    assert type(first) is AssetTransferLaneModuleAcceptedV1
    next_input = replace(
        original,
        pre_state=first.post_state,
        command=replace(original.command, amount_atoms=1),
        context=replace(original.context, command_occurrence_id="0x" + "4" * 64),
    )
    rejected_input = replace(next_input, command=replace(next_input.command, amount_atoms=0))
    before = canonical_global_bytes_v1(rejected_input.to_canonical())
    rejected = transition_asset_transfer_lane_module_custody_v1(rejected_input)
    assert type(rejected) is AssetTransferRejectedV1
    assert rejected.code.value == "ZERO_AMOUNT"
    assert rejected.effects.is_empty and rejected.pre_state_root == rejected.post_state_root
    assert canonical_global_bytes_v1(rejected_input.to_canonical()) == before
    cases.append(("accepted_after_rejection", next_input))
    return cases


def test_actual_runtime_rows_effects_and_history_match_keyed_model(lean_library, tmp_path):
    source = (
        "def renderDelta : Except D.Reject Int → String\n"
        '  | .ok value => "OK:" ++ toString value\n'
        '  | .error _ => "ERR"\n'
    ).replace("D.Reject", "Proofs.CheckedSignedDeltaRefinementV1.Reject")
    expected: list[bool | int | str] = []
    for index, (name, value) in enumerate(_runtime_histories()):
        before_bytes = canonical_global_bytes_v1(value.to_canonical())
        result = transition_asset_transfer_lane_module_custody_v1(value)
        assert type(result) is AssetTransferLaneModuleAcceptedV1, name
        assert canonical_global_bytes_v1(value.to_canonical()) == before_bytes
        pre, post = result.private_port.pre_state, result.private_port.post_state
        assert pre.custody == post.custody == value.custody
        expected_balances = dict(_row_values(value.pre_state.balances))
        policy = next(p for p in value.pre_state.policies if p.asset == value.command.asset)
        for owner, delta in (
            (value.command.sender, -value.command.amount_atoms - policy.transfer_fee_atoms),
            (value.command.recipient, value.command.amount_atoms),
            (policy.fee_owner, policy.transfer_fee_atoms),
        ):
            key = (value.command.asset, owner, "accounts")
            expected_balances[key] = expected_balances.get(key, 0) + delta
        assert {k: n for k, n in expected_balances.items() if n} == dict(_row_values(post.balances))
        if name == "sender_terminal_zero":
            assert (value.command.asset, value.command.sender, "accounts") not in dict(
                _row_values(post.balances)
            )
        maps = []
        for phase, state in (("pre", pre), ("post", post)):
            balances, custody = _row_values(state.balances), _row_values(state.custody)
            supplies = [(r.asset, r.amount_atoms) for r in state.supplies]
            label = f"{phase}{index}"
            source += f"def {label} : List Row := {_rows(balances + custody)}\n"
            source += (
                f"#eval checkProjection {_rows(balances)} {_rows(custody)} {_supplies(supplies)}\n"
            )
            expected.append(True)
            maps.append(dict(balances + custody))
            for asset, supply in supplies:
                assert sum(n for key, n in balances + custody if key[0] == asset) == supply
                source += (
                    f"#eval sumOver (fun key => if key.asset = {json.dumps(asset)} "
                    f"then lookupAtoms key {label} else 0) (projectionKeys {_rows(balances)} {_rows(custody)})\n"
                )
                expected.append(supply)
        union = list(maps[1]) + [key for key in maps[0] if key not in maps[1]]
        source += (
            f"#eval decide (unionKeys post{index} pre{index} = "
            "[" + ", ".join(_key(key) for key in union) + "])\n"
        )
        expected.append(True)
        for supply in pre.supplies:
            source += f"#eval assetDeltaSum {json.dumps(supply.asset)} post{index} pre{index}\n"
            expected.append(0)
        effects = {
            (r.asset, r.principal, r.custody_domain): r.delta_atoms
            for r in result.effects.rows
            if r.kind is EconomicEffectKindV1.ACCOUNT_MOVEMENT
        }
        deltas = _amount_delta_rows_v1("balances", pre.balances, post.balances)
        assert {(r.asset, r.owner, r.custody_domain): r.delta_atoms for r in deltas} == effects
        keys = sorted(set(maps[0]) | set(maps[1]) | {("USD", "absent", "vault")})
        for key in keys:
            pre_atoms, post_atoms = (m.get(key, 0) for m in maps)
            delta = post_atoms - pre_atoms
            assert _checked_signed_delta_v1(post_atoms, pre_atoms) == delta
            assert effects.get(key, 0) == delta
            source += f"#eval lookupAtoms {_key(key)} pre{index}\n#eval lookupAtoms {_key(key)} post{index}\n"
            expected += [pre_atoms, post_atoms]
            source += (
                f"#eval renderDelta (D.checkedSignedDelta "
                f"(holdingAt {_key(key)} post{index} (by decide)) "
                f"(holdingAt {_key(key)} pre{index} (by decide)))\n"
            )
            expected.append(f"OK:{delta}")
    _eval(source, expected, lean_library, tmp_path / "RuntimeRows.lean")


def test_keyed_delta_rejects_signed_overflow_without_losing_unsigned_holdings(
    lean_library, tmp_path
):
    limit = 2**127
    maximum = 2**128 - 1
    pairs = [
        (0, 0),
        (0, limit - 1),
        (0, limit),
        (0, maximum),
        (limit, 0),
        (limit + 1, 0),
        (maximum, 0),
        (maximum, maximum),
        (maximum - 1, maximum),
        (maximum, maximum - 1),
    ]
    key = ("A", "alice", "accounts")
    source = (
        "def renderDelta : Except Proofs.CheckedSignedDeltaRefinementV1.Reject Int → String\n"
        '  | .ok value => "OK:" ++ toString value\n'
        '  | .error _ => "ERR"\n'
    )
    expected = []
    for i, (before, after) in enumerate(pairs):
        pre_rows = [] if before == 0 else [(key, before)]
        post_rows = [] if after == 0 else [(key, after)]
        source += f"def before{i} : List Row := {_rows(pre_rows)}\n"
        source += f"def after{i} : List Row := {_rows(post_rows)}\n"
        source += (
            f"#eval renderDelta (D.checkedSignedDelta "
            f"(holdingAt {_key(key)} after{i} (by decide)) "
            f"(holdingAt {_key(key)} before{i} (by decide)))\n"
        )
        difference = after - before
        if -limit <= difference < limit:
            assert _checked_signed_delta_v1(after, before) == difference
            expected.append(f"OK:{difference}")
        else:
            with pytest.raises(ValueError, match="exceeds signed 128-bit bounds"):
                _checked_signed_delta_v1(after, before)
            expected.append("ERR")
    _eval(source, expected, lean_library, tmp_path / "DeltaBounds.lean")


def test_zero_elision_preserves_aggregation_but_does_not_repair_duplicate_lookup(
    lean_library, tmp_path
):
    key = ("A", "alice", "vault")
    rows = [(key, 0), (key, 5)]
    source = f"def rows : List Row := {_rows(rows)}\n"
    source += (
        "#eval checkRows rows\n"
        f"#eval lookupAtoms {_key(key)} rows\n"
        f"#eval lookupAtoms {_key(key)} (elideZeroRows rows)\n"
        f"#eval aggregateAtoms {_key(key)} rows\n"
        f"#eval aggregateAtoms {_key(key)} (elideZeroRows rows)\n"
    )
    _eval(source, [False, 0, 5, 5, 5], lean_library, tmp_path / "ZeroElision.lean")


def test_unmodelled_order_and_unsafe_enumerations_are_explicit(lean_library, tmp_path):
    # Model totals are permutation invariant; canonical runtime admission is stricter.
    rows = [(("B", "bob", "accounts"), 5), (("A", "alice", "accounts"), 10)]
    supplies = [("A", 10), ("B", 5)]
    assert not _runtime_projection_accepts(rows, [], supplies)
    source = f"#eval checkProjection {_rows(rows)} [] {_supplies(supplies)}\n"
    source += f"def rows : List Row := {_rows(rows)}\n"
    key = _key(rows[1][0])
    source += (
        f"#eval sumOver (fun key => lookupAtoms key rows) [{key}]\n"
        f"#eval sumOver (fun key => lookupAtoms key rows) [{key}, {key}]\n"
        f'#eval sumOver (fun key => lookupAtoms key rows) (projectionKeys rows [] ++ [⟨"C", "absent", "vault"⟩])\n'
    )
    # Omitting support loses 5; duplicating a present key double counts 10.
    _eval(source, [True, 10, 20, 15], lean_library, tmp_path / "Premises.lean")


@pytest.mark.parametrize(
    "mutant", ["owner_only_lookup", "duplicates_admitted", "pre_only_keys_omitted"]
)
def test_compilable_semantic_mutants_fail_fixed_theorems(mutant, lean_library, tmp_path):
    source = PROOF.read_text()
    if mutant == "owner_only_lookup":
        changed = source.replace(
            "if row.key = key then row.atoms else lookupAtoms key rows",
            "if row.key.owner = key.owner then row.atoms else lookupAtoms key rows",
            1,
        )
        witness = '#eval lookupAtoms ⟨"B", "alice", "vault"⟩ [⟨⟨"A", "alice", "accounts"⟩, 10⟩]\n'
        observed = "10"
    elif mutant == "duplicates_admitted":
        changed = source.replace(
            "def checkRows (rows : List Row) : Bool := decide (ValidRows rows)",
            "def checkRows (rows : List Row) : Bool :=\n  decide (∀ row ∈ rows, 0 < row.atoms ∧ row.atoms < 2 ^ 128)",
            1,
        )
        witness = (
            '#eval checkRows [⟨⟨"A", "alice", "accounts"⟩, 9⟩, ⟨⟨"A", "alice", "accounts"⟩, 10⟩]\n'
        )
        observed = "true"
    else:
        changed = source.replace(
            "post.map Row.key ++ (pre.map Row.key).filter (fun key => decide (key ∉ post.map Row.key))",
            "post.map Row.key ++ (pre.map Row.key).filter (fun _ => false)",
            1,
        )
        witness = '#eval (unionKeys [] [⟨⟨"A", "alice", "accounts"⟩, 10⟩]).length\n'
        observed = "0"
    assert changed != source
    probe = tmp_path / f"{mutant}.lean"
    first_fixed_claim = (
        "theorem unionKeys_unique_and_covers"
        if mutant == "pre_only_keys_omitted"
        else "theorem checkRows_accepts_iff"
    )
    prefix = changed[: changed.index(first_fixed_claim)]
    probe.write_text(prefix + witness + f"end {NAMESPACE}\n")
    result = _check(probe, lean_library)
    assert result.returncode == 0, result.stdout + result.stderr
    assert result.stdout.strip() == observed
    probe.write_text(changed)
    result = _check(probe, lean_library)
    assert result.returncode != 0
    assert "error:" in result.stdout
