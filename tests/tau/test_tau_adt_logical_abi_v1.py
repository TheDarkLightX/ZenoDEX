from __future__ import annotations

import re
import subprocess
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
LOCK = ROOT / "config" / "tau_lang_adt_research.lock"
ASSET_SPEC = ROOT / "src" / "tau_specs" / "recommended" / "asset_transfer_adt_contract_v1.tau"
JOURNAL_SPEC = ROOT / "src" / "tau_specs" / "recommended" / "lane_transition_journal_adt_contract_v1.tau"
TAU_DIR_REL = "external/tau-lang-adt-logical-abi-v1"
TAU_DIR = ROOT / TAU_DIR_REL
TAU_BIN = TAU_DIR / "build-Release" / "tau"
_ANSI_RE = re.compile(r"\x1b\[[0-9;]*m")
_VERDICT_RE = re.compile(r"%\d+:\s*(T|F)\b")


def _read_lock() -> dict[str, str]:
    rows: dict[str, str] = {}
    for raw in LOCK.read_text(encoding="utf-8").splitlines():
        line = raw.strip()
        if not line or line.startswith("#"):
            continue
        key, sep, value = line.partition("=")
        assert sep, f"malformed lock row: {raw!r}"
        assert key and key not in rows, f"duplicate/empty lock key: {key!r}"
        rows[key] = value
    return rows


def _git_head(path: Path) -> str | None:
    if not (path / ".git").exists():
        return None
    proc = subprocess.run(
        ["git", "-C", str(path), "rev-parse", "HEAD"],
        cwd=ROOT,
        capture_output=True,
        text=True,
        timeout=15,
    )
    if proc.returncode != 0:
        return None
    return proc.stdout.strip()


def _ensure_pinned_tau() -> tuple[Path, str]:
    lock = _read_lock()
    assert lock == {
        "schema": "zenodex.tau_lang_adt_research_lock.v1",
        "repo": "https://github.com/IDNI/tau-lang.git",
        "commit": "3c24bad9ee4c00c5d677fa465797189671823c01",
        "profile": "research",
        "purpose": "ZenoDEX ADT logical ABI V1 replay; ADTs/functions/recurrences/whole-value arguments/min-max",
        "nonclaim": "This pin does not imply Tau Tables availability or production Tau Net compatibility.",
    }
    commit = lock["commit"]
    if TAU_BIN.is_file() and _git_head(TAU_DIR) == commit:
        return TAU_BIN, commit

    # Do not capture this long-running build. The repository hygiene gate runs
    # pytest with capture enabled, and a completely silent nested build can be
    # terminated by the hosted runner before pytest has a chance to report.
    # The caller disables pytest capture around this function so upstream clone,
    # configure, and compile progress remains visible in the Actions log.
    proc = subprocess.run(
        [
            "bash",
            "tools/update_tau_lang.sh",
            "--ref",
            commit,
            "--tau-dir",
            TAU_DIR_REL,
            "--build-dir",
            "build-Release",
        ],
        cwd=ROOT,
        text=True,
        timeout=1200,
    )
    assert proc.returncode == 0, "pinned Tau build failed; see streamed build output above"
    assert TAU_BIN.is_file(), "pinned Tau build produced no executable"
    assert _git_head(TAU_DIR) == commit
    return TAU_BIN, commit


def _noncomment_lines(path: Path) -> list[str]:
    lines: list[str] = []
    for raw in path.read_text(encoding="utf-8").splitlines():
        stripped = raw.strip()
        if not stripped or stripped.startswith("#"):
            continue
        lines.append(stripped)
    return lines


def _definition_preamble(path: Path) -> list[str]:
    preamble: list[str] = []
    for line in _noncomment_lines(path):
        if line.startswith("always "):
            break
        if line == "set charvar off":
            continue
        assert line.endswith("."), f"definition must be one complete Tau command: {line!r}"
        preamble.append(line)
    assert preamble, f"missing Tau definitions: {path}"
    return preamble


def _always_query(path: Path) -> str:
    lines = _noncomment_lines(path)
    always = [line for line in lines if line.startswith("always ")]
    assert len(always) == 1
    line = always[0]
    assert line.endswith(".")
    return "valid " + line[len("always ") : -1]


def _run_query(tau_bin: Path, spec: Path, query: str, *, expected: str) -> str:
    assert expected in {"T", "F"}
    script = "\n".join(
        [
            "set charvar off",
            *_definition_preamble(spec),
            query,
            "quit",
            "",
        ]
    )
    proc = subprocess.run(
        [str(tau_bin), "-X"],
        cwd=ROOT,
        input=script,
        capture_output=True,
        text=True,
        timeout=120,
    )
    transcript = proc.stdout + proc.stderr
    clean_stdout = _ANSI_RE.sub("", proc.stdout)
    verdicts = _VERDICT_RE.findall(clean_stdout)
    assert proc.returncode == 0, transcript
    assert "(Error)" not in transcript, transcript
    assert verdicts == [expected], (
        f"expected exactly one Tau verdict {expected}, got {verdicts!r}\n{transcript}"
    )
    return transcript


def _run_truth_query(tau_bin: Path, spec: Path, query: str) -> str:
    return _run_query(tau_bin, spec, query, expected="T")


def test_tau_adt_logical_abi_source_contract() -> None:
    asset = ASSET_SPEC.read_text(encoding="utf-8")
    journal = JOURNAL_SPEC.read_text(encoding="utf-8")
    assert "type AssetTransferEnvelopeADT1" in asset
    assert "asset_transfer_result_ok(e.result)" in asset
    assert "POST_STATE_RESOURCE_BOUND_EXCEEDED" in asset
    assert "min(required, cap)" in asset
    assert "type LaneJournalEdgeADT1" in journal
    assert "lane_module_journal_ok(edge.previous)" in journal
    assert "replay_cursor[n](x):bv[16]" in journal
    assert "min({1}:bv[16], replay_cursor[n-1](x)')" in journal

    executable_asset = "\n".join(
        line for line in asset.splitlines() if not line.lstrip().startswith("#")
    ).lower()
    executable_journal = "\n".join(
        line for line in journal.splitlines() if not line.lstrip().startswith("#")
    ).lower()
    assert "table" not in executable_asset
    assert "table" not in executable_journal


def test_tau_adt_logical_abi_pinned_replay(capsys) -> None:
    # Keep the long source-resolved Tau build visible in CI rather than hiding
    # it behind pytest's fd capture.
    with capsys.disabled():
        print(
            "tau-adt-logical-abi-v1: building exact IDNI/tau-lang pin 3c24bad9...",
            flush=True,
        )
        tau_bin, commit = _ensure_pinned_tau()
        print(f"tau-adt-logical-abi-v1: pinned Tau ready at {commit}", flush=True)

    assert commit == "3c24bad9ee4c00c5d677fa465797189671823c01"

    # Harness falsification: a deliberately over-strong ADT statement must
    # return F. Requiring an exact single verdict prevents an unexpanded
    # predicate or earlier REPL output from masquerading as success.
    _run_query(
        tau_bin,
        ASSET_SPEC,
        "valid all r:AssetTransferResultADT1 (asset_transfer_result_ok(r) -> (r.accepted = 1:sbf))",
        expected="F",
    )

    # First replay each file's full declared invariant. These are deliberately
    # closed formulas so Tau must decide them as valid, not merely parse them.
    _run_truth_query(tau_bin, ASSET_SPEC, _always_query(ASSET_SPEC))
    _run_truth_query(tau_bin, JOURNAL_SPEC, _always_query(JOURNAL_SPEC))

    asset_queries = (
        # Whole-ADT result call: every typed rejection is an exact no-op.
        "valid all r:AssetTransferResultADT1 (asset_transfer_result_ok(r) -> ((r.rejected = 1:sbf) -> ((r.pre_state_root = r.post_state_root) && (r.effects_empty = 1:sbf))))",
        # Negative regression: no accepted result can carry a non-NONE code.
        "unsat ex r:AssetTransferResultADT1 (asset_transfer_result_ok(r) && (r.accepted = 1:sbf) && (r.reject_code != {0}:bv[8]))",
        # Negative regression: a rejected result cannot change the state root.
        "unsat ex r:AssetTransferResultADT1 (asset_transfer_result_ok(r) && (r.rejected = 1:sbf) && (r.pre_state_root != r.post_state_root))",
        # Boundary repaired in NEW-6: abstract code 12 is closed and no-op.
        "valid all r:AssetTransferResultADT1 ((asset_transfer_result_ok(r) && (r.reject_code = {12}:bv[8])) -> ((r.rejected = 1:sbf) && (r.pre_state_root = r.post_state_root) && (r.effects_empty = 1:sbf)))",
        # New min builtin: cap check is equivalent to unsigned <= over bv[16].
        "valid all required:bv[16] all cap:bv[16] (fee_within_cap(required, cap) <-> (required <= cap))",
        # Whole command ADT flattening reaches the predicate arity exactly.
        "valid all c:AssetTransferCommandADT1 (asset_transfer_command_shape_ok(c) -> ((c.sender != c.recipient) && (c.amount_atoms != {0}:bv[16])))",
        # Nested sub-ADT flattening: Context is passed whole, followed by two
        # scalar members drawn from the enclosing envelope.
        "valid all e:AssetTransferEnvelopeADT1 (asset_transfer_context_binding_ok(e.context, e.state_module_release, e.command.sender) -> ((e.context.module_release_id = e.state_module_release) && (e.context.subject_id = e.command.sender)))",
    )
    for query in asset_queries:
        _run_truth_query(tau_bin, ASSET_SPEC, query)

    journal_queries = (
        # Whole nested journal ADT call expands to the frozen thirteen fields.
        "valid all j:LaneModuleTransitionJournalADT1 (lane_module_journal_ok(j) -> (journal_header_ok(j.header) && journal_binding_ok(j.binding)))",
        # Negative regression: Python requires effect_plan_root to be nonzero.
        "unsat ex j:LaneModuleTransitionJournalADT1 (lane_module_journal_ok(j) && (j.binding.effect_plan_root = {0}:bv[16]))",
        # Nested edge/subtuple calls preserve same-module header bindings.
        "valid all e:LaneJournalEdgeADT1 (same_journal_header(e.previous.header, e.next.header) -> ((e.previous.header.writer_epoch = e.next.header.writer_epoch) && (e.previous.header.module_release_id = e.next.header.module_release_id)))",
        # Saturating recurrence never decreases and never wraps max to zero.
        "valid all x:bv[16] (replay_cursor[1](x) >= x)",
        "valid replay_cursor[1](1:bv[16]) = 1:bv[16]",
        "valid all x:bv[16] ((x != 1:bv[16]) -> (replay_cursor[1](x) = x + {1}:bv[16]))",
        # Boundary: 0xfffe advances once to max and then remains at max.
        "valid replay_cursor[3]({#xfffe}:bv[16]) = 1:bv[16]",
    )
    for query in journal_queries:
        _run_truth_query(tau_bin, JOURNAL_SPEC, query)
