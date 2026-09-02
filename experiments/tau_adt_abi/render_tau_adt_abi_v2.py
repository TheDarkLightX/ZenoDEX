#!/usr/bin/env python3
"""Tau ADT logical ABI V1 - vector-bound tier over PR #534's ADT declarations.

PR #534 declares the Command/Context/Result ADTs and a closed result algebra
(`asset_transfer_result_ok`) whose replayed theorems are definitional. This
renderer binds those declarations to the REAL Python transition:

RECOMPUTE tier (nine reject classes + accept, bounded bv[16] domain):
  per vector, one UNIVERSAL program
      ex k:Context ex c:Command ex s:State ( bindings && all r:Result ( chain -> expected ) )
  where `chain` recomputes the transition's guard precedence in Tau over the
  literal members and `expected` is built from the OBSERVED Python result
  (code, pre/post root equality, effects emptiness); plus one NON-VACUITY
  program `ex r:Result ( chain )` so the universal cannot pass vacuously.
CONTRACT tier (classes outside the bounded domain, host-produced results):
  the observed result record is pinned member-for-member and checked against
  PR #534's own `asset_transfer_result_ok` (read verbatim from the spec), plus
  the expected code. Weaker than recompute and labelled so.

The ADT `type` declarations and the `asset_transfer_result_ok` definition are
read verbatim from the PR spec file, so member order and flattened arity have
ONE source of truth. The reject-code map is derived from
AssetTransferRejectCodeV1 declaration order (index + 1), never hand-typed.
Every program needs exactly one T/F verdict (F8 discipline); anything else is
FAIL_CLOSED. Research-only; authority NONE. Logs to stderr, JSON to stdout.
"""

from __future__ import annotations

import hashlib
import json
import os
import re
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path

REPO = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO))

from src.core.asset_transfer_module_v1 import transition_asset_transfer_v1  # noqa: E402
from src.core.asset_transfer_types_v1 import (  # noqa: E402
    ASSET_TRANSFER_COMMAND_KIND_V1,
    AssetTransferCommandV1,
    AssetTransferContextV1,
    AssetTransferPolicyV1,
    AssetTransferRejectCodeV1,
    AssetTransferStateV1,
)
from src.core.global_settlement_types_v1 import (  # noqa: E402
    MAX_ASSET_BALANCE_ROWS_V1,
    MAX_ATOMS_V1,
    AssetSupplyV1,
    EconomicAmountV1,
)

SPEC_PATH = REPO / "src" / "tau_specs" / "recommended" / "asset_transfer_adt_contract_v1.tau"
JOURNAL_SPEC_PATH = REPO / "src" / "tau_specs" / "recommended" / "lane_transition_journal_adt_contract_v1.tau"
LOCK_PATH = REPO / "config" / "tau_lang_adt_research.lock"
DEFAULT_TAU_BIN = REPO / "external" / "tau-lang-adt-logical-abi-v1" / "build-Release" / "tau"
TAU_BIN = Path(os.environ.get("ZENO_TAU_ADT_BIN", str(DEFAULT_TAU_BIN)))
WIDTH = 16
IN_BAND = (1 << WIDTH) - 1

# Reject-code map: declaration order, index + 1; 0 = accepted. Pinned by
# construction against the enum, and checked against the spec's ceiling literal.
CODE_TOKENS: dict[str | None, int] = {None: 0}
CODE_TOKENS.update({member.name: index + 1 for index, member in enumerate(AssetTransferRejectCodeV1)})

# Bounded shadow-domain dictionaries (vector-local, frozen).
IDENTITY = {"sender": 1, "recv": 2, "treasury": 3, "other": 4}
ASSET = {"USD": 1, "EUR": 2}
KIND = {ASSET_TRANSFER_COMMAND_KIND_V1: 1, "bogus": 2}
ROOT = "0x" + "11" * 32
OTHER_ROOT = "0x" + "22" * 32
ROOT_TAG = {ROOT: 1, OTHER_ROOT: 2}
STATE_ROOT_TAG = 1  # pre-state root tag; an accepted post root is any other tag
CHAIN_TAG = 1

STATE_ADT = (
    "type AssetTransferStateADT1 = {module_release_id: bv[16], policy_asset: bv[8], "
    "transfer_fee_atoms: bv[16], enabled: sbf, sender_balance_atoms: bv[16], state_root: bv[16]}."
)
RECOMPUTE_CODES = (
    "RELEASE_MISMATCH", "UNKNOWN_COMMAND", "UNKNOWN_ASSET", "DISABLED_ASSET",
    "UNAUTHORIZED_SUBJECT", "SELF_TRANSFER", "ZERO_AMOUNT", "FEE_LIMIT_EXCEEDED",
    "INSUFFICIENT_BALANCE",
)
CONTRACT_CODES = ("EFFECT_DELTA_OVERFLOW", "POST_STATE_RESOURCE_BOUND_EXCEEDED")
UNREACHABLE_CODES = {
    "BALANCE_OVERFLOW": "the type enforces balances <= supply <= MAX_ATOMS_V1, so a "
    "transfer between well-formed balances cannot exceed the ceiling; only a forged state reaches it",
}


def log(msg: str) -> None:
    print(msg, file=sys.stderr)


def sha256_text(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


# --- one source of truth: the PR spec's declarations -----------------------

def spec_lines() -> list[str]:
    return [line.strip() for line in SPEC_PATH.read_text(encoding="utf-8").splitlines()
            if line.strip() and not line.strip().startswith("#")]


def spec_types() -> dict[str, str]:
    types = {}
    for line in spec_lines():
        match = re.fullmatch(r"type (\w+) = \{(.*)\}\.", line)
        if match:
            types[match.group(1)] = line
    for name in ("AssetTransferCommandADT1", "AssetTransferContextADT1", "AssetTransferResultADT1"):
        assert name in types, f"spec lacks {name}"
    return types


def spec_members(type_line: str) -> tuple[str, ...]:
    body = type_line[type_line.index("{") + 1 : type_line.rindex("}")]
    return tuple(part.split(":")[0].strip() for part in body.split(",") if ":" in part)


def spec_result_ok_definition() -> str:
    for line in spec_lines():
        if line.startswith("asset_transfer_result_ok("):
            return line
    raise AssertionError("spec lacks asset_transfer_result_ok")


def spec_code_ceiling() -> int:
    match = re.search(r"\(code <= \{(\d+)\}:bv\[8\]\)", spec_result_ok_definition())
    assert match, "spec result algebra has no closed code ceiling"
    return int(match.group(1))


# --- Python oracle ----------------------------------------------------------

@dataclass(frozen=True)
class VectorV2:
    vector_id: str
    tier: str            # "recompute" | "contract"
    intent: str | None   # the reject class the vector is designed to hit (None = accept)
    release: str         # context module_release_id
    subject: str
    kind: str
    asset: str
    sender: str
    recipient: str
    amount: int
    max_fee: int
    state_release: str
    policy_asset: str
    fee: int
    enabled: bool
    s_bal: int
    r_bal: int
    t_bal: int
    extra_rows: int = 0  # contract tier: additional distinct balance rows


def _state(v: VectorV2) -> AssetTransferStateV1:
    rows = {("sender", v.s_bal), ("recv", v.r_bal), ("treasury", v.t_bal)}
    rows |= {(f"acct-{i:04d}", 1) for i in range(v.extra_rows)}
    balances = tuple(sorted(
        (EconomicAmountV1(owner, v.policy_asset, "accounts", atoms) for owner, atoms in rows if atoms > 0),
        key=lambda row: row.key,
    ))
    supply = sum(row.amount_atoms for row in balances)
    return AssetTransferStateV1(
        module_release_id=v.state_release,
        policies=(AssetTransferPolicyV1(v.policy_asset, "treasury", v.fee, v.enabled),),
        balances=balances,
        supplies=(AssetSupplyV1(v.policy_asset, supply),),
    )


@dataclass(frozen=True)
class Observed:
    accepted: bool
    code: str | None
    noop: bool
    effects_empty: bool


def python_outcome(v: VectorV2) -> Observed:
    state = _state(v)
    context = AssetTransferContextV1("zenodex", ROOT, ROOT, 1, v.release, ROOT, v.subject, ROOT)
    command = AssetTransferCommandV1(v.kind, v.asset, v.sender, v.recipient, v.amount, v.max_fee)
    result = transition_asset_transfer_v1(context, state, command)
    if type(result).__name__ == "AssetTransferAcceptedV1":
        return Observed(True, None, result.post_state.state_root == state.state_root,
                        result.effects.is_empty)
    return Observed(False, result.code.name, result.pre_state_root == result.post_state_root,
                    result.effects.is_empty)


def build_vectors() -> list[VectorV2]:
    def rec(vid: str, intent: str | None, **kw) -> VectorV2:
        base = dict(release=ROOT, subject="sender", kind=ASSET_TRANSFER_COMMAND_KIND_V1, asset="USD",
                    sender="sender", recipient="recv", amount=30, max_fee=2, state_release=ROOT,
                    policy_asset="USD", fee=2, enabled=True, s_bal=100, r_bal=10, t_bal=5)
        base.update(kw)
        return VectorV2(vid, "recompute", intent, **base)

    vectors = [
        rec("accept_plain", None),
        rec("accept_balance_exact", None, s_bal=32),
        rec("reject_release_mismatch", "RELEASE_MISMATCH", release=OTHER_ROOT),
        rec("reject_unknown_command", "UNKNOWN_COMMAND", kind="bogus"),
        rec("reject_unknown_asset", "UNKNOWN_ASSET", asset="EUR"),
        rec("reject_disabled_asset", "DISABLED_ASSET", enabled=False),
        rec("reject_unauthorized_subject", "UNAUTHORIZED_SUBJECT", subject="other"),
        rec("reject_self_transfer", "SELF_TRANSFER", recipient="sender"),
        rec("reject_zero_amount", "ZERO_AMOUNT", amount=0),
        rec("reject_fee_limit", "FEE_LIMIT_EXCEEDED", fee=9),
        rec("reject_insufficient", "INSUFFICIENT_BALANCE", s_bal=10),
        # guard-edge boundaries
        rec("accept_fee_at_limit", None, fee=7, max_fee=7),
        rec("reject_fee_one_over", "FEE_LIMIT_EXCEEDED", fee=8, max_fee=7),
        rec("accept_balance_exact_fee", None, fee=7, max_fee=7, s_bal=37),
        rec("reject_balance_one_short", "INSUFFICIENT_BALANCE", fee=7, max_fee=7, s_bal=36),
        rec("accept_in_band_max_sum", None, s_bal=IN_BAND, amount=IN_BAND - 2, fee=2),
        # precedence discriminators: two adjacent guards both want to fire; the
        # oracle (not the fixture) decides which code wins.
        rec("prec_release_beats_command", "RELEASE_MISMATCH", release=OTHER_ROOT, kind="bogus"),
        rec("prec_command_beats_asset", "UNKNOWN_COMMAND", kind="bogus", asset="EUR"),
        rec("prec_asset_beats_disabled", "UNKNOWN_ASSET", asset="EUR", enabled=False),
        rec("prec_disabled_beats_subject", "DISABLED_ASSET", enabled=False, subject="other"),
        rec("prec_subject_beats_self", "UNAUTHORIZED_SUBJECT", subject="other", recipient="sender"),
        rec("prec_self_beats_zero", "SELF_TRANSFER", recipient="sender", amount=0),
        rec("prec_zero_beats_fee", "ZERO_AMOUNT", amount=0, fee=9),
        rec("prec_fee_beats_insufficient", "FEE_LIMIT_EXCEEDED", fee=9, s_bal=1),
        # contract tier: outside the bounded domain, host-produced results
        VectorV2("contract_effect_delta_overflow", "contract", "EFFECT_DELTA_OVERFLOW",
                 ROOT, "sender", ASSET_TRANSFER_COMMAND_KIND_V1, "USD", "sender", "recv",
                 MAX_ATOMS_V1, 1, ROOT, "USD", 1, True, MAX_ATOMS_V1, 0, 0),
        VectorV2("contract_post_state_row_ceiling", "contract", "POST_STATE_RESOURCE_BOUND_EXCEEDED",
                 ROOT, "sender", ASSET_TRANSFER_COMMAND_KIND_V1, "USD", "sender", "recv",
                 30, 2, ROOT, "USD", 2, True, 100, 0, 5, extra_rows=MAX_ASSET_BALANCE_ROWS_V1 - 2),
    ]
    for v in vectors:
        if v.tier == "recompute":
            assert v.amount + v.fee <= IN_BAND and v.s_bal <= IN_BAND, (v.vector_id, "out of band")
    return vectors


# --- Tau rendering ----------------------------------------------------------

def bv(value: int, width: int = WIDTH) -> str:
    return f"{{{value}}}:bv[{width}]"


def _preamble(types: dict[str, str], with_state: bool) -> str:
    lines = ["set charvar off", types["AssetTransferCommandADT1"], types["AssetTransferContextADT1"],
             types["AssetTransferResultADT1"]]
    if with_state:
        lines.append(STATE_ADT)
    return "\n".join(lines) + "\n"


def _rej(code: int) -> str:
    return (f"r.accepted = 0 && r.rejected = 1 && r.reject_code = {bv(code, 8)}"
            " && r.pre_state_root = s.state_root && r.post_state_root = s.state_root && r.effects_empty = 1")


_ACC = ("r.accepted = 1 && r.rejected = 0 && r.reject_code = {0}:bv[8]"
        " && r.pre_state_root = s.state_root && r.post_state_root != s.state_root && r.effects_empty = 0")


def guard_chain() -> str:
    """Transition guard precedence recomputed over ADT members (k, c, s, r).

    Mirrors _transfer_policy / _post_balances in src/core/asset_transfer_module_v1.py
    for the nine bounded classes; the enum order is the realised precedence."""
    t = CODE_TOKENS
    g1 = "k.module_release_id = s.module_release_id"
    g2 = f"c.command_kind = {bv(KIND[ASSET_TRANSFER_COMMAND_KIND_V1], 4)}"
    g3 = "c.asset = s.policy_asset"
    g4 = "s.enabled = 1"
    g5 = "c.sender = k.subject_id"
    g6 = "c.sender != c.recipient"
    g7 = f"c.amount_atoms != {bv(0)}"
    g8 = "s.transfer_fee_atoms <= c.max_fee_atoms"
    g9 = "s.sender_balance_atoms >= c.amount_atoms + s.transfer_fee_atoms"
    passed: list[str] = []
    clauses = []
    for guard, code in ((g1, "RELEASE_MISMATCH"), (g2, "UNKNOWN_COMMAND"), (g3, "UNKNOWN_ASSET"),
                        (g4, "DISABLED_ASSET"), (g5, "UNAUTHORIZED_SUBJECT"), (g6, "SELF_TRANSFER"),
                        (g7, "ZERO_AMOUNT"), (g8, "FEE_LIMIT_EXCEEDED"), (g9, "INSUFFICIENT_BALANCE")):
        neg = {
            g1: "k.module_release_id != s.module_release_id",
            g2: f"c.command_kind != {bv(KIND[ASSET_TRANSFER_COMMAND_KIND_V1], 4)}",
            g3: "c.asset != s.policy_asset",
            g4: "s.enabled = 0",
            g5: "c.sender != k.subject_id",
            g6: "c.sender = c.recipient",
            g7: f"c.amount_atoms = {bv(0)}",
            g8: "s.transfer_fee_atoms > c.max_fee_atoms",
            g9: "s.sender_balance_atoms < c.amount_atoms + s.transfer_fee_atoms",
        }[guard]
        clauses.append("( " + " && ".join([*passed, neg, _rej(t[code])]) + " )")
        passed.append(guard)
    clauses.append("( " + " && ".join([*passed, _ACC]) + " )")
    return "(\n  " + " ||\n  ".join(clauses) + "\n)"


def bindings(v: VectorV2) -> str:
    return " && ".join([
        f"k.chain_id = {bv(CHAIN_TAG, 8)}", f"k.deployment_root = {bv(1)}", f"k.profile_root = {bv(1)}",
        f"k.writer_epoch = {bv(1)}", f"k.module_release_id = {bv(ROOT_TAG[v.release])}",
        f"k.command_occurrence_id = {bv(1)}", f"k.subject_id = {bv(IDENTITY[v.subject], 8)}",
        f"k.grant_root = {bv(1)}",
        f"c.command_kind = {bv(KIND[v.kind], 4)}", f"c.asset = {bv(ASSET[v.asset], 8)}",
        f"c.sender = {bv(IDENTITY[v.sender], 8)}", f"c.recipient = {bv(IDENTITY[v.recipient], 8)}",
        f"c.amount_atoms = {bv(v.amount)}", f"c.max_fee_atoms = {bv(v.max_fee)}",
        f"s.module_release_id = {bv(ROOT_TAG[v.state_release])}", f"s.policy_asset = {bv(ASSET[v.policy_asset], 8)}",
        f"s.transfer_fee_atoms = {bv(v.fee)}", f"s.enabled = {1 if v.enabled else 0}",
        f"s.sender_balance_atoms = {bv(v.s_bal)}", f"s.state_root = {bv(STATE_ROOT_TAG)}",
    ])


def expected_clause(o: Observed) -> str:
    code = CODE_TOKENS[o.code]
    post = f"r.post_state_root = {bv(STATE_ROOT_TAG)}" if o.noop else f"r.post_state_root != {bv(STATE_ROOT_TAG)}"
    return (f"(r.accepted = {1 if o.accepted else 0} && r.rejected = {0 if o.accepted else 1}"
            f" && r.reject_code = {bv(code, 8)} && r.pre_state_root = {bv(STATE_ROOT_TAG)} && {post}"
            f" && r.effects_empty = {1 if o.effects_empty else 0})")


def render_recompute(types: dict[str, str], v: VectorV2, o: Observed) -> tuple[str, str]:
    head = _preamble(types, True) + "n ex k:AssetTransferContextADT1 ex c:AssetTransferCommandADT1 ex s:AssetTransferStateADT1 ( "
    universal = head + bindings(v) + " && all r:AssetTransferResultADT1 ( " + guard_chain() + " -> " + expected_clause(o) + " ) )\nquit\n"
    nonvacuity = head + bindings(v) + " && ex r:AssetTransferResultADT1 ( " + guard_chain() + " ) )\nquit\n"
    return universal, nonvacuity


def render_contract(types: dict[str, str], v: VectorV2, o: Observed, code_override: int | None = None) -> str:
    """Host-produced result pinned member-for-member, checked by the PR's algebra."""
    code = CODE_TOKENS[o.code] if code_override is None else code_override
    post = STATE_ROOT_TAG if o.noop else STATE_ROOT_TAG + 1
    pins = (f"r.accepted = {1 if o.accepted else 0} && r.rejected = {0 if o.accepted else 1}"
            f" && r.reject_code = {bv(code, 8)} && r.pre_state_root = {bv(STATE_ROOT_TAG)}"
            f" && r.post_state_root = {bv(post)} && r.effects_empty = {1 if o.effects_empty else 0}")
    expected_code = f"r.reject_code = {bv(CODE_TOKENS[v.intent], 8)}"
    return (_preamble(types, False) + spec_result_ok_definition() + "\n"
            f"n ex r:AssetTransferResultADT1 ( {pins} && asset_transfer_result_ok(r) && {expected_code} )\nquit\n")


# --- Tau execution (F8: exact single verdict or FAIL_CLOSED) -----------------

_ANSI = re.compile(r"\x1b\[[0-9;]*m")


def run_tau(program: str) -> tuple[str, str]:
    proc = subprocess.run([str(TAU_BIN)], input=program, capture_output=True, text=True, timeout=180)
    clean = _ANSI.sub("", proc.stdout + proc.stderr)
    verdicts = re.findall(r"%\d+: (T|F)\b", clean)
    errors = len(re.findall(r"\(Error\)", clean))
    if errors or proc.returncode != 0 or len(verdicts) != 1:
        return f"FAIL_CLOSED(verdicts={verdicts},errors={errors},rc={proc.returncode})", clean
    return verdicts[0], clean


def tau_available() -> str | None:
    if not TAU_BIN.is_file():
        return f"TAU_PIN_UNAVAILABLE: no binary at {TAU_BIN}"
    return None



# --- capability probes: PR #534's own queries, labelled honestly ---------------
# Every query below is either a definitional projection of the predicate it
# quantifies over or a property of a Tau builtin/recurrence; they evidence ADT
# flattening, mixed sbf/bv members, min() and recurrences - not ZenoDEX
# transition semantics (those are the vector-bound tier). Verdicts are still
# earned: exact single T/F, (Error) fails closed, and the false statement first.

def _definition_preamble(path: Path) -> list[str]:
    preamble = []
    for line in [ln.strip() for ln in path.read_text(encoding="utf-8").splitlines()]:
        if not line or line.startswith("#"):
            continue
        if line.startswith("always "):
            break
        if line == "set charvar off":
            continue
        assert line.endswith("."), line
        preamble.append(line)
    return preamble


def _always_query(path: Path) -> str:
    always = [ln.strip() for ln in path.read_text(encoding="utf-8").splitlines() if ln.strip().startswith("always ")]
    assert len(always) == 1
    return "valid " + always[0][len("always "):-1]


def capability_probes() -> dict[str, dict[str, str]]:
    asset, journal = SPEC_PATH, JOURNAL_SPEC_PATH
    table: list[tuple[str, Path, str, str]] = [
        ("false_whole_adt_statement", asset,
         "valid all r:AssetTransferResultADT1 (asset_transfer_result_ok(r) -> (r.accepted = 1:sbf))", "F"),
        ("asset_always_theorem", asset, _always_query(asset), "T"),
        ("journal_always_theorem", journal, _always_query(journal), "T"),
        ("fee_cap_min_equivalence", asset,
         "valid all required:bv[16] all cap:bv[16] (fee_within_cap(required, cap) <-> (required <= cap))", "T"),
        ("fee_cap_min_strict_falsification", asset,
         "valid all required:bv[16] all cap:bv[16] (fee_within_cap(required, cap) <-> (required < cap))", "F"),
        ("pr534_asset_reject_noop_projection", asset,
         "valid all r:AssetTransferResultADT1 (asset_transfer_result_ok(r) -> ((r.rejected = 1:sbf) -> ((r.pre_state_root = r.post_state_root) && (r.effects_empty = 1:sbf))))", "T"),
        ("pr534_asset_accepted_code_zero_projection", asset,
         "unsat ex r:AssetTransferResultADT1 (asset_transfer_result_ok(r) && (r.accepted = 1:sbf) && (r.reject_code != {0}:bv[8]))", "T"),
        ("pr534_asset_rejected_root_fixed_projection", asset,
         "unsat ex r:AssetTransferResultADT1 (asset_transfer_result_ok(r) && (r.rejected = 1:sbf) && (r.pre_state_root != r.post_state_root))", "T"),
        ("pr534_asset_code_12_closed_projection", asset,
         "valid all r:AssetTransferResultADT1 ((asset_transfer_result_ok(r) && (r.reject_code = {12}:bv[8])) -> ((r.rejected = 1:sbf) && (r.pre_state_root = r.post_state_root) && (r.effects_empty = 1:sbf)))", "T"),
        ("pr534_asset_command_flattening", asset,
         "valid all c:AssetTransferCommandADT1 (asset_transfer_command_shape_ok(c) -> ((c.sender != c.recipient) && (c.amount_atoms != {0}:bv[16])))", "T"),
        ("pr534_asset_context_nested_flattening", asset,
         "valid all e:AssetTransferEnvelopeADT1 (asset_transfer_context_binding_ok(e.context, e.state_module_release, e.command.sender) -> ((e.context.module_release_id = e.state_module_release) && (e.context.subject_id = e.command.sender)))", "T"),
        ("pr534_journal_nested_flattening", journal,
         "valid all j:LaneModuleTransitionJournalADT1 (lane_module_journal_ok(j) -> (journal_header_ok(j.header) && journal_binding_ok(j.binding)))", "T"),
        ("pr534_journal_effect_root_nonzero_projection", journal,
         "unsat ex j:LaneModuleTransitionJournalADT1 (lane_module_journal_ok(j) && (j.binding.effect_plan_root = {0}:bv[16]))", "T"),
        ("pr534_journal_edge_header_projection", journal,
         "valid all e:LaneJournalEdgeADT1 (same_journal_header(e.previous.header, e.next.header) -> ((e.previous.header.writer_epoch = e.next.header.writer_epoch) && (e.previous.header.module_release_id = e.next.header.module_release_id)))", "T"),
        ("pr534_cursor_monotone", journal, "valid all x:bv[16] (replay_cursor[1](x) >= x)", "T"),
        ("pr534_cursor_saturates_at_max", journal, "valid replay_cursor[1](1:bv[16]) = 1:bv[16]", "T"),
        ("pr534_cursor_advances_below_max", journal,
         "valid all x:bv[16] ((x != 1:bv[16]) -> (replay_cursor[1](x) = x + {1}:bv[16]))", "T"),
        ("pr534_cursor_boundary_fffe", journal, "valid replay_cursor[3]({#xfffe}:bv[16]) = 1:bv[16]", "T"),
    ]
    out: dict[str, dict[str, str]] = {}
    for name, spec, query, expected in table:
        program = "\n".join(["set charvar off", *_definition_preamble(spec), query, "quit", ""])
        verdict, _ = run_tau(program)
        out[name] = {"query": query, "expected": expected, "verdict": verdict}
        log(f"probe {name}: expected={expected} got={verdict}")
    return out

def selftest(types: dict[str, str]) -> dict[str, str]:
    """Falsification probes: the harness must be able to answer F and FAIL_CLOSED."""
    v = build_vectors()[0]
    o = python_outcome(v)
    assert o.accepted
    probes: dict[str, str] = {}
    wrong = Observed(False, "SELF_TRANSFER", True, True)
    probes["wrong_expectation_universal"] = run_tau(render_recompute(types, v, wrong)[0])[0]
    good_u, _ = render_recompute(types, v, o)
    weakened = re.sub(r"all r:AssetTransferResultADT1 \( \(.*?\n\) ->",
                      "all r:AssetTransferResultADT1 ( ( {1}:bv[4] = {1}:bv[4] ) ->", good_u, flags=re.S)
    assert weakened != good_u
    probes["weakened_chain_universal"] = run_tau(weakened)[0]
    cv = next(x for x in build_vectors() if x.tier == "contract")
    co = python_outcome(cv)
    probes["contract_wrong_code"] = run_tau(render_contract(types, cv, co, code_override=CODE_TOKENS[co.code] + 1))[0]
    probes["contract_mutated_effects"] = run_tau(render_contract(types, cv, Observed(False, co.code, co.noop, False)))[0]
    probes["broken_program"] = run_tau("type Broken = {a: sbf. n nonsense(\nquit\n")[0]
    expected = {"wrong_expectation_universal": "F", "weakened_chain_universal": "F",
                "contract_wrong_code": "F", "contract_mutated_effects": "F"}
    for name, want in expected.items():
        assert probes[name] == want, (name, probes[name])
    assert probes["broken_program"].startswith("FAIL_CLOSED"), probes["broken_program"]
    return probes


def main() -> int:
    types = spec_types()
    assert spec_members(types["AssetTransferResultADT1"]) == (
        "accepted", "rejected", "reject_code", "pre_state_root", "post_state_root", "effects_empty")
    assert spec_code_ceiling() == len(AssetTransferRejectCodeV1), (spec_code_ceiling(), len(AssetTransferRejectCodeV1))
    unavailable = tau_available()
    if unavailable:
        print(json.dumps({"ok": False, "schema": "zenodex/tau-adt-abi-parity/v3", "reason": unavailable}))
        return 2
    rows = []
    transcripts: list[str] = []
    ok = True
    capability = capability_probes()
    ok = ok and all(entry["verdict"] == entry["expected"] for entry in capability.values())
    probes = selftest(types)
    for v in build_vectors():
        o = python_outcome(v)
        assert o.code == v.intent, (v.vector_id, "vector does not hit its intended class", o.code)
        if v.tier == "recompute":
            u, n = render_recompute(types, v, o)
            vu, tu = run_tau(u)
            vn, tn = run_tau(n)
            transcripts += [tu, tn]
            agree = vu == "T" and vn == "T"
            programs = {"universal": {"sha256": sha256_text(u), "verdict": vu},
                        "nonvacuity": {"sha256": sha256_text(n), "verdict": vn}}
        else:
            p = render_contract(types, v, o)
            vp, tp = run_tau(p)
            transcripts.append(tp)
            agree = vp == "T"
            programs = {"contract": {"sha256": sha256_text(p), "verdict": vp}}
        ok = ok and agree
        rows.append({"vector": v.vector_id, "tier": v.tier, "python_code": o.code or "ACCEPT",
                     "python_noop": o.noop, "python_effects_empty": o.effects_empty,
                     "programs": programs, "parity": agree})
        log(f"{v.vector_id}: python={o.code or 'ACCEPT'} " + " ".join(f"{k}={p['verdict']}" for k, p in programs.items()))
    lock = dict(line.split("=", 1) for line in LOCK_PATH.read_text().splitlines() if "=" in line)
    version = subprocess.run([str(TAU_BIN), "--version"], capture_output=True, text=True, timeout=30).stdout.strip()
    report = {
        "ok": ok, "schema": "zenodex/tau-adt-abi-parity/v3", "width": WIDTH,
        "tau_commit": lock.get("commit"), "tau_binary_sha256": hashlib.sha256(TAU_BIN.read_bytes()).hexdigest(),
        "tau_version": version,
        "spec_path": str(SPEC_PATH.relative_to(REPO)), "spec_sha256": sha256_text(SPEC_PATH.read_text()),
        "journal_spec_sha256": sha256_text(JOURNAL_SPEC_PATH.read_text()),
        "lock_sha256": sha256_text(LOCK_PATH.read_text()),
        "renderer_sha256": sha256_text(Path(__file__).read_text()),
        "capability_probes": capability,
        "code_map": {k or "ACCEPT": val for k, val in CODE_TOKENS.items()},
        "recompute_codes": list(RECOMPUTE_CODES), "contract_codes": list(CONTRACT_CODES),
        "unreachable_codes": UNREACHABLE_CODES,
        "selftest": probes, "vectors": rows,
        "transcript_sha256": sha256_text("\n".join(transcripts)),
    }
    if "--receipt" in sys.argv:
        out = Path(sys.argv[sys.argv.index("--receipt") + 1])
        out.write_text(json.dumps(report, indent=1, sort_keys=True) + "\n")
        log(f"receipt written: {out}")
    print(json.dumps(report, sort_keys=True))
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
