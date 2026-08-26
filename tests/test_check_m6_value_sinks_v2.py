"""Evidence for the static-source M6 value-sink inventory.

Obligation: every durable-write operation in the statically reachable closure of
the decoded launcher set carries exactly one manifest classification bound to a
source-derived fingerprint, and every edge the decoder cannot resolve is a typed
closure gap rather than silence.

The counterexample block replays the nine minimized cases from the independent
coordinator review of candidate 2085533f. Each is a permanent mutation killer.
"""

from __future__ import annotations

import ast
import hashlib
import inspect
import json
import os
import shutil
import sqlite3
import subprocess
import sys
from collections.abc import Iterator, Mapping, Sequence
from dataclasses import replace
from pathlib import Path

import pytest

from tools import check_m6_value_sinks_v2 as checker_module
from tools.check_m6_value_sinks_v2 import (
    RenderedClosureGapV2,
    RenderedManifestV2,
    RenderedSinkEntryV2,
    check_m6_value_sinks_v2,
    main,
    render_manifest_v2,
)
from tools.m6_value_sinks import (
    UNADJUDICATED,
    ClosureGapV2,
    DeploymentClosureV2,
    RepositorySnapshotV2,
    ValueSinkObservationV2,
    canonical_relative_path,
    combine_fingerprints,
    compare_inventory,
    derive_deployed_entrypoints,
    derive_python_deployment_closure,
    dynamic_destination_gaps,
    gate_blockers,
    identity_sink_id_v2,
    load_closure_gaps,
    load_value_sink_document,
    load_value_sink_manifest,
    resolve_module,
    resolve_module_candidate,
    scan_closure,
    scan_module,
)
from tools.m6_value_sinks import launchers as launcher_module
from tools.m6_value_sinks import report as report_module
from tools.m6_value_sinks.launchers import (
    bounded_materialize_v2,
    classify_launcher_line,
    read_bounded_text,
)
from tools.m6_value_sinks.operations import (
    MAX_SQL_SCRIPT_CHARACTERS,
    MAX_SQL_STATEMENTS,
    classify_sql_script,
    classify_sql_statement,
    operation_fingerprint,
)

ROOT = Path(__file__).resolve().parents[1]

_INSTALL = 'install_wrapper "zenodex-node" python3 "${repo_dir}/tools/node.py"\n'


def _deployment(root: Path, body: str, *, install: str = _INSTALL, extra: dict[str, str] | None = None) -> None:
    (root / "scripts").mkdir(parents=True, exist_ok=True)
    (root / "scripts" / "install_zenodex.sh").write_text(install, encoding="utf-8")
    (root / "tools").mkdir(parents=True, exist_ok=True)
    (root / "tools" / "node.py").write_text(body, encoding="utf-8")
    for relative, content in (extra or {}).items():
        target = root / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text(content, encoding="utf-8")


def _observe(root: Path) -> list[tuple[str, str, str]]:
    closure = derive_python_deployment_closure(root)
    return [item.identity() for item in scan_closure(root, closure)]


def _observations(root: Path) -> tuple[ValueSinkObservationV2, ...]:
    closure = derive_python_deployment_closure(root)
    return scan_closure(root, closure)


def _entry(**overrides: object) -> dict[str, object]:
    base: dict[str, object] = {
        "classification": "DURABLE_VALUE_STATE",
        "consumers": [],
        "deployed_reachable": True,
        "identity_fingerprint": "0" * 64,
        "mediation_status": "UNMEDIATED_DEPLOYED_WRITER",
        "occurrence_count": 1,
        "path": "tools/node.py",
        "rationale": "test rationale",
        "release_binding": None,
        "sink_id": "node__publish__atomic_replace",
        "sink_kind": "ATOMIC_REPLACE",
        "symbol": "publish",
    }
    base.update(overrides)
    if "sink_id" not in overrides:
        base["sink_id"] = identity_sink_id_v2(
            (str(base["path"]), str(base["symbol"]), str(base["sink_kind"]))
        )
    return base


def _consumer(**overrides: str) -> dict[str, str]:
    base = {
        "artifact": "authority.json",
        "kind": "REPO_PATH",
        "reader_fingerprint": "1" * 64,
        "reference": "tools/reader.py",
        "source_path": "tools/reader.py",
        "source_sha256": "2" * 64,
    }
    base.update(overrides)
    return base


def _reader_fingerprint(source_path: str, artifact: str, source: str) -> str:
    tree = ast.parse(source)
    call = next(
        node
        for node in ast.walk(tree)
        if isinstance(node, ast.Call)
        and isinstance(node.func, ast.Attribute)
        and node.func.attr in {"read_bytes", "read_text"}
    )
    rendered = ast.dump(call, annotate_fields=True, include_attributes=False)
    payload = (
        b"zenodex-m6-reader-v2\0"
        + source_path.encode("utf-8")
        + b"\0"
        + artifact.encode("utf-8")
        + b"\0"
        + rendered.encode("utf-8")
    )
    return hashlib.sha256(payload).hexdigest()


def _manifest(
    root: Path,
    entries: Sequence[Mapping[str, object] | RenderedSinkEntryV2],
    gaps: Sequence[Mapping[str, str] | RenderedClosureGapV2] | None = None,
) -> Path:
    (root / "tools").mkdir(parents=True, exist_ok=True)
    path = root / "tools" / "m6_value_sink_manifest_v2.json"
    path.write_text(
        json.dumps(
            {"closure_gaps": gaps or [], "entries": entries, "schema": "zenodex/m6-value-sink-inventory/v2", "scope": "test"},
            indent=2,
            sort_keys=True,
        ),
        encoding="utf-8",
    )
    return path


# ---------------------------------------------------------------------------
# Review counterexamples, replayed as permanent mutation killers
# ---------------------------------------------------------------------------


def test_relative_import_writer_is_observed(tmp_path: Path) -> None:
    """Review R1: package-relative ImportFrom edges must join the closure."""

    _deployment(
        tmp_path,
        "import os\nfrom .worker import hidden_publish\n\n\ndef publish(a, b):\n    os.replace(a, b)\n",
        extra={
            "tools/__init__.py": "",
            "tools/worker.py": "import os\n\n\ndef hidden_publish(a, b):\n    os.replace(a, b)\n",
        },
    )

    closure = derive_python_deployment_closure(tmp_path)

    assert "tools/worker.py" in closure.modules
    assert ("tools/worker.py", "hidden_publish", "ATOMIC_REPLACE") in _observe(tmp_path)


def test_relative_import_writer_fails_the_full_gate(tmp_path: Path) -> None:
    """Review R1: the bypass must reach the gate verdict, not only the closure."""

    _deployment(
        tmp_path,
        "import os\nfrom .worker import hidden_publish\n\n\ndef publish(a, b):\n    os.replace(a, b)\n",
        extra={
            "tools/__init__.py": "",
            "tools/worker.py": "import os\n\n\ndef hidden_publish(a, b):\n    os.replace(a, b)\n",
        },
    )
    _manifest(tmp_path, [_entry()])

    report = check_m6_value_sinks_v2(tmp_path)

    assert report["scanner_relative_manifest_agreement"] is False
    assert report["closure_complete"] is False
    assert any(
        finding["rule_id"] == "unclassified_value_sink" and finding["path"] == "tools/worker.py"
        for finding in report["findings"]
    )


@pytest.mark.parametrize("level", ["from . import worker", "from .worker import hidden_publish"])
def test_relative_import_forms_resolve(tmp_path: Path, level: str) -> None:
    _deployment(
        tmp_path,
        f"{level}\n",
        extra={
            "tools/__init__.py": "",
            "tools/worker.py": "import os\n\n\ndef hidden_publish(a, b):\n    os.replace(a, b)\n",
        },
    )

    assert "tools/worker.py" in derive_python_deployment_closure(tmp_path).modules


def test_direct_imported_operation_alias_is_observed(tmp_path: Path) -> None:
    """Review R2: `from os import replace as move` must stay visible."""

    _deployment(tmp_path, "from os import replace as move\n\n\ndef publish(a, b):\n    move(a, b)\n")

    assert _observe(tmp_path) == [("tools/node.py", "publish", "ATOMIC_REPLACE")]


def test_module_alias_is_observed(tmp_path: Path) -> None:
    _deployment(tmp_path, "import os as _o\n\n\ndef publish(a, b):\n    _o.replace(a, b)\n")

    assert _observe(tmp_path) == [("tools/node.py", "publish", "ATOMIC_REPLACE")]


def test_path_open_write_mode_is_observed(tmp_path: Path) -> None:
    """Review R3: attribute-form open in a mutating mode is a durable write."""

    _deployment(tmp_path, "from pathlib import Path\n\n\ndef publish(path):\n    Path(path).open('w')\n")

    assert _observe(tmp_path) == [("tools/node.py", "publish", "OPEN_WRITE")]


def test_low_level_descriptor_write_is_observed(tmp_path: Path) -> None:
    """Review R3: descriptor writes bypass every path-level operation."""

    _deployment(
        tmp_path,
        "import os\n\n\ndef publish(path):\n"
        "    descriptor = os.open(path, os.O_WRONLY | os.O_CREAT)\n"
        "    os.write(descriptor, b'value')\n",
    )

    # os.open takes integer flags, so it never enters the mode-string vocabulary;
    # the writable open and the descriptor write are both observed.
    assert [kind for _, _, kind in _observe(tmp_path)] == [
        "DESCRIPTOR_OPEN_WRITE",
        "DESCRIPTOR_WRITE",
    ]


@pytest.mark.parametrize(
    ("statement", "expected"),
    [
        ("CREATE TABLE value_state (v INTEGER)", "SQL_WRITE"),
        ("DROP TABLE value_state", "SQL_WRITE"),
        ("ALTER TABLE value_state ADD COLUMN w INTEGER", "SQL_WRITE"),
        ("INSERT INTO balances VALUES (1)", "SQL_WRITE"),
        ("WITH moved AS (SELECT 1) INSERT INTO balances SELECT * FROM moved", "SQL_WRITE"),
        ("PRAGMA journal_mode = WAL", "SQL_PRAGMA_WRITE"),
        ("VACUUM", "SQL_WRITE"),
        ("SELECT atoms FROM balances", None),
        ("PRAGMA journal_mode", None),
    ],
)
def test_sql_statement_classification(tmp_path: Path, statement: str, expected: str | None) -> None:
    """Review R4: DDL, CTE writes and writable PRAGMA are durable writes."""

    _deployment(tmp_path, f"def publish(connection):\n    connection.execute({statement!r})\n")

    observed = [kind for _, _, kind in _observe(tmp_path)]
    assert observed == ([expected] if expected else [])


@pytest.mark.parametrize(
    "statement",
    [
        "-- retained audit comment\nDELETE FROM balances",
        "/* retained audit comment */ DELETE FROM balances",
    ],
)
def test_leading_sql_comments_cannot_hide_a_write(tmp_path: Path, statement: str) -> None:
    """A literal comment prefix must not turn a durable SQL write into silence."""

    _deployment(tmp_path, f"def publish(connection):\n    connection.execute({statement!r})\n")

    assert _observe(tmp_path) == [("tools/node.py", "publish", "SQL_WRITE")]


def test_dynamic_sql_is_typed_rather_than_silent(tmp_path: Path) -> None:
    _deployment(tmp_path, "def publish(connection, statement):\n    connection.execute(statement)\n")

    assert _observe(tmp_path) == [("tools/node.py", "publish", "SQL_DYNAMIC")]


def test_module_form_subprocess_dispatch_joins_the_closure(tmp_path: Path) -> None:
    """Review R5: `python -m pkg.mod` is the container entrypoint dispatch shape."""

    _deployment(
        tmp_path,
        "import subprocess\n\n\ndef run():\n    subprocess.run(['python3', '-m', 'tools.worker'])\n",
        extra={
            "tools/__init__.py": "",
            "tools/worker.py": "import os\n\n\ndef publish(a, b):\n    os.replace(a, b)\n",
        },
    )

    closure = derive_python_deployment_closure(tmp_path)

    assert "tools/worker.py" in closure.modules
    assert ("tools/worker.py", "publish", "ATOMIC_REPLACE") in _observe(tmp_path)


def test_undecodable_subprocess_dispatch_is_a_typed_gap(tmp_path: Path) -> None:
    _deployment(
        tmp_path,
        "import subprocess\n\n\ndef run(command):\n    subprocess.run(command)\n",
    )

    closure = derive_python_deployment_closure(tmp_path)

    assert ("tools/node.py", "unresolved_subprocess_dispatch") in closure.observed_gaps


def test_escaped_subprocess_callable_is_a_typed_gap(tmp_path: Path) -> None:
    """A subprocess runner selected through getattr leaves the closed dispatch grammar."""

    _deployment(
        tmp_path,
        "import subprocess\n\n\ndef run(argv):\n"
        "    runner = getattr(subprocess, 'run')\n"
        "    runner(argv)\n",
    )

    closure = derive_python_deployment_closure(tmp_path)

    assert ("tools/node.py", "unresolved_subprocess_dispatch") in closure.observed_gaps


def test_semantic_relocation_changes_the_identity_fingerprint(tmp_path: Path, tmp_path_factory: pytest.TempPathFactory) -> None:
    """Review R6: equal counts must not hide a relocated destination."""

    first_root = tmp_path
    second_root = tmp_path_factory.mktemp("second")
    _deployment(first_root, "import os\n\n\ndef publish(rt, rl, bt, bl):\n    os.replace(rt, rl)\n")
    _deployment(second_root, "import os\n\n\ndef publish(rt, rl, bt, bl):\n    os.replace(bt, bl)\n")

    first = scan_closure(first_root, derive_python_deployment_closure(first_root))
    second = scan_closure(second_root, derive_python_deployment_closure(second_root))

    assert [item.identity() for item in first] == [item.identity() for item in second]
    assert combine_fingerprints(tuple(i.fingerprint for i in first)) != combine_fingerprints(
        tuple(i.fingerprint for i in second)
    )


def test_relocated_operation_fails_the_full_gate(tmp_path: Path) -> None:
    """A relocated operand must break the gate on its fingerprint.

    Fixed literal operands keep destination provenance adjudicable, so the
    post-change failure is attributable to the fingerprint alone.
    """

    _deployment(
        tmp_path,
        "import os\n\n\ndef publish():\n    os.replace('reserve.tmp', 'reserve.live')\n",
    )
    _manifest(tmp_path, [_entry()])
    emitted = render_manifest_v2(tmp_path)
    assert {item["mechanism"] for item in emitted["closure_gaps"]} == {
        "unmodelled_installer_shell",
        next(
            item["mechanism"]
            for item in emitted["closure_gaps"]
            if item["mechanism"].startswith("installer_source_sha256_")
        ),
    }

    entry = _entry(identity_fingerprint=emitted["entries"][0]["identity_fingerprint"])
    manifest_path = _manifest(tmp_path, [entry], emitted["closure_gaps"])
    assert check_m6_value_sinks_v2(tmp_path)["scanner_relative_manifest_agreement"] is True

    (tmp_path / "tools" / "node.py").write_text(
        "import os\n\n\ndef publish():\n    os.replace('balance.tmp', 'balance.live')\n",
        encoding="utf-8",
    )
    report = check_m6_value_sinks_v2(tmp_path)

    assert manifest_path.exists()
    assert report["scanner_relative_manifest_agreement"] is False
    assert [finding["rule_id"] for finding in report["findings"]] == ["operation_fingerprint_mismatch"]


def test_authority_control_state_cannot_be_excused_as_non_value(tmp_path: Path) -> None:
    """Review R7: a value-bearing classification may not claim NON_VALUE_EFFECT."""

    path = _manifest(
        tmp_path,
        [
            _entry(
                classification="AUTHORITY_CONTROL_STATE",
                mediation_status="NON_VALUE_EFFECT",
                consumers=[_consumer()],
            )
        ],
    )

    with pytest.raises(ValueError, match="excuses a value-bearing classification"):
        load_value_sink_manifest(path)


def test_authority_control_state_requires_named_consumers(tmp_path: Path) -> None:
    path = _manifest(tmp_path, [_entry(classification="AUTHORITY_CONTROL_STATE", consumers=[])])

    with pytest.raises(ValueError, match="must name the consumers"):
        load_value_sink_manifest(path)


def test_generated_artifact_requires_named_consumers(tmp_path: Path) -> None:
    path = _manifest(tmp_path, [_entry(classification="GENERATED_ARTIFACT_STATE", consumers=[])])

    with pytest.raises(ValueError, match="must name the consumers"):
        load_value_sink_manifest(path)


def test_consumers_are_rejected_for_untraced_classifications(tmp_path: Path) -> None:
    path = _manifest(
        tmp_path, [_entry(consumers=[_consumer()])]
    )

    with pytest.raises(ValueError, match="does not trace them"):
        load_value_sink_manifest(path)


def test_consumer_must_bind_source_bytes_and_a_concrete_read(tmp_path: Path) -> None:
    """D11: a named file alone is not evidence that it reads the written artifact."""

    path = _manifest(
        tmp_path,
        [
            _entry(
                classification="AUTHORITY_CONTROL_STATE",
                consumers=[{"kind": "REPO_PATH", "reference": "tools/reader.py"}],
            )
        ],
    )

    with pytest.raises(ValueError, match="keys mismatch"):
        load_value_sink_manifest(path)


def test_source_bound_reader_remains_runtime_unproved_and_mutation_is_detected(
    tmp_path: Path,
) -> None:
    artifact = "authority.json"
    reader_path = "tools/node.py"
    source = (
        "from pathlib import Path\n\n"
        "Path('authority.json').write_text('value')\n"
        "Path('authority.json').read_text()\n"
    )
    _deployment(tmp_path, source)
    emitted = render_manifest_v2(tmp_path)
    entry = next(
        dict(item) for item in emitted["entries"] if item["path"] == "tools/node.py"
    )
    entry.update(
        {
            "classification": "AUTHORITY_CONTROL_STATE",
            "mediation_status": "UNMEDIATED_DEPLOYED_WRITER",
            "rationale": "source-bound test judgement",
            "consumers": [
                _consumer(
                    artifact=artifact,
                    reader_fingerprint=_reader_fingerprint(reader_path, artifact, source),
                    reference=reader_path,
                    source_path=reader_path,
                    source_sha256=hashlib.sha256(source.encode("utf-8")).hexdigest(),
                )
            ],
        }
    )
    gaps = list(emitted["closure_gaps"])
    _manifest(tmp_path, [entry], gaps=gaps)

    before = check_m6_value_sinks_v2(tmp_path)
    before_render = render_manifest_v2(tmp_path)
    assert any(item["rule_id"] == "runtime_read_unproved" for item in before["findings"])
    assert before_render["entries"][0]["classification"] == UNADJUDICATED

    (tmp_path / reader_path).write_text(
        "from pathlib import Path\n\n"
        "Path('authority.json').write_text('value')\n"
        "Path('other.json').read_text()\n",
        encoding="utf-8",
    )
    after = check_m6_value_sinks_v2(tmp_path)
    regenerated = render_manifest_v2(tmp_path)

    assert any(item["rule_id"] == "consumer_source_digest_mismatch" for item in after["findings"])
    refreshed = next(
        item for item in regenerated["entries"] if item["path"] == "tools/node.py"
    )
    assert refreshed["classification"] == UNADJUDICATED
    assert refreshed["consumers"] == []


def test_launcher_only_consumer_evidence_cannot_remain_adjudicated(tmp_path: Path) -> None:
    _deployment(
        tmp_path,
        "from pathlib import Path\n\n\ndef publish():\n    Path('authority.json').write_text('v')\n",
    )
    emitted = render_manifest_v2(tmp_path)
    entry = dict(emitted["entries"][0])
    install_bytes = _INSTALL.encode("utf-8")
    entry.update(
        {
            "classification": "AUTHORITY_CONTROL_STATE",
            "mediation_status": "UNMEDIATED_DEPLOYED_WRITER",
            "rationale": "launcher is dispatch evidence, not reader evidence",
            "consumers": [
                _consumer(
                    artifact="authority.json",
                    kind="LAUNCHER_ID",
                    reader_fingerprint="3" * 64,
                    reference="zenodex-node",
                    source_path="scripts/install_zenodex.sh",
                    source_sha256=hashlib.sha256(install_bytes).hexdigest(),
                )
            ],
        }
    )
    _manifest(tmp_path, [entry], gaps=list(emitted["closure_gaps"]))

    report = check_m6_value_sinks_v2(tmp_path)
    regenerated = render_manifest_v2(tmp_path)

    assert any(item["rule_id"] == "consumer_read_unverifiable" for item in report["findings"])
    assert regenerated["entries"][0]["classification"] == UNADJUDICATED


def test_prior_raise_keeps_a_direct_static_reader_runtime_unproved(tmp_path: Path) -> None:
    artifact = "authority.json"
    source_path = "tools/node.py"
    source = (
        "from pathlib import Path\n\nPath('authority.json').write_text('value')\n"
        "raise RuntimeError('stop')\nPath('authority.json').read_text()\n"
    )
    _deployment(tmp_path, source)
    emitted = render_manifest_v2(tmp_path)
    entry = dict(emitted["entries"][0])
    entry.update(
        {
            "classification": "AUTHORITY_CONTROL_STATE",
            "mediation_status": "UNMEDIATED_DEPLOYED_WRITER",
            "rationale": "hostile prior-raise reader claim",
            "consumers": [
                _consumer(
                    artifact=artifact,
                    reader_fingerprint=_reader_fingerprint(source_path, artifact, source),
                    reference=source_path,
                    source_path=source_path,
                    source_sha256=hashlib.sha256(source.encode("utf-8")).hexdigest(),
                )
            ],
        }
    )
    _manifest(tmp_path, [entry], gaps=list(emitted["closure_gaps"]))

    report = check_m6_value_sinks_v2(tmp_path)
    regenerated = render_manifest_v2(tmp_path)

    assert any(item["rule_id"] == "runtime_read_unproved" for item in report["findings"])
    assert regenerated["entries"][0]["classification"] == UNADJUDICATED


@pytest.mark.parametrize(
    "read_body",
    [
        pytest.param("'authority.json'.read_text()\n", id="constant-string-receiver"),
        pytest.param(
            "artifact = 'authority.json'\nartifact.read_text()\n",
            id="string-alias-receiver",
        ),
    ],
)
def test_consumer_reader_requires_a_proven_pathlib_receiver(
    tmp_path: Path, read_body: str
) -> None:
    artifact = "authority.json"
    source_path = "tools/node.py"
    source = (
        "from pathlib import Path\n\nPath('authority.json').write_text('value')\n"
        + read_body
    )
    _deployment(tmp_path, source)
    emitted = render_manifest_v2(tmp_path)
    entry = dict(emitted["entries"][0])
    entry.update(
        {
            "classification": "AUTHORITY_CONTROL_STATE",
            "mediation_status": "UNMEDIATED_DEPLOYED_WRITER",
            "rationale": "hostile untyped reader claim",
            "consumers": [
                _consumer(
                    artifact=artifact,
                    reader_fingerprint=_reader_fingerprint(source_path, artifact, source),
                    reference=source_path,
                    source_path=source_path,
                    source_sha256=hashlib.sha256(source.encode("utf-8")).hexdigest(),
                )
            ],
        }
    )
    _manifest(tmp_path, [entry], gaps=list(emitted["closure_gaps"]))

    report = check_m6_value_sinks_v2(tmp_path)
    regenerated = render_manifest_v2(tmp_path)

    assert any(
        item["rule_id"] == "consumer_reader_fingerprint_mismatch"
        for item in report["findings"]
    )
    assert regenerated["entries"][0]["classification"] == UNADJUDICATED


@pytest.mark.parametrize(
    "read_body",
    [
        pytest.param(
            "if False:\n    Path('authority.json').read_text()\n",
            id="dead-branch",
        ),
        pytest.param(
            "def never_called():\n    return Path('authority.json').read_text()\n",
            id="uncalled-function",
        ),
    ],
)
def test_consumer_reader_requires_a_direct_module_instruction(
    tmp_path: Path, read_body: str
) -> None:
    artifact = "authority.json"
    source_path = "tools/node.py"
    source = (
        "from pathlib import Path\n\nPath('authority.json').write_text('value')\n"
        + read_body
    )
    _deployment(tmp_path, source)
    emitted = render_manifest_v2(tmp_path)
    entry = dict(emitted["entries"][0])
    entry.update(
        {
            "classification": "AUTHORITY_CONTROL_STATE",
            "mediation_status": "UNMEDIATED_DEPLOYED_WRITER",
            "rationale": "hostile unreachable reader claim",
            "consumers": [
                _consumer(
                    artifact=artifact,
                    reader_fingerprint=_reader_fingerprint(source_path, artifact, source),
                    reference=source_path,
                    source_path=source_path,
                    source_sha256=hashlib.sha256(source.encode("utf-8")).hexdigest(),
                )
            ],
        }
    )
    _manifest(tmp_path, [entry], gaps=list(emitted["closure_gaps"]))

    report = check_m6_value_sinks_v2(tmp_path)
    regenerated = render_manifest_v2(tmp_path)

    assert any(
        item["rule_id"] == "consumer_read_unreachable"
        for item in report["findings"]
    )
    assert regenerated["entries"][0]["classification"] == UNADJUDICATED


# ---------------------------------------------------------------------------
# Unknown open modes must never collapse into the safe read case
# ---------------------------------------------------------------------------


@pytest.mark.parametrize(
    ("body", "expected"),
    [
        ("def publish(p):\n    open(p)\n", []),
        ("def publish(p):\n    open(p, 'r')\n", []),
        ("def publish(p):\n    open(p, 'w')\n", ["OPEN_WRITE"]),
        ("def publish(p, m):\n    open(p, m)\n", ["OPEN_MODE_UNKNOWN"]),
        ("def publish(p, m):\n    open(p, mode=m)\n", ["OPEN_MODE_UNKNOWN"]),
        ("def publish(p, o):\n    open(p, **o)\n", ["OPEN_MODE_UNKNOWN"]),
        ("def publish(p):\n    open(p, mode='a')\n", ["OPEN_WRITE"]),
        ("def publish(p):\n    open(p, mode='r')\n", []),
    ],
)
def test_builtin_open_mode_tristate(tmp_path: Path, body: str, expected: list[str]) -> None:
    """An absent mode is a safe read; a present unresolved mode stays observable."""

    _deployment(tmp_path, body)

    assert [kind for _, _, kind in _observe(tmp_path)] == expected


@pytest.mark.parametrize(
    ("body", "expected"),
    [
        ("def publish(p):\n    p.open()\n", []),
        ("def publish(p):\n    p.open('r')\n", []),
        ("def publish(p):\n    p.open('w')\n", ["OPEN_WRITE"]),
        ("def publish(p, m):\n    p.open(m)\n", ["OPEN_MODE_UNKNOWN"]),
        ("def publish(p, m):\n    p.open(mode=m)\n", ["OPEN_MODE_UNKNOWN"]),
        ("def publish(p, o):\n    p.open(**o)\n", ["OPEN_MODE_UNKNOWN"]),
    ],
)
def test_receiver_open_mode_tristate(tmp_path: Path, body: str, expected: list[str]) -> None:
    _deployment(tmp_path, body)

    assert [kind for _, _, kind in _observe(tmp_path)] == expected


# ---------------------------------------------------------------------------
# Subprocess dispatch: literal decoding is not modelled dispatch
# ---------------------------------------------------------------------------


def _worker_tree() -> dict[str, str]:
    return {
        "tools/__init__.py": "",
        "tools/worker.py": "import os\n\n\ndef publish(a, b):\n    os.replace(a, b)\n",
    }


@pytest.mark.parametrize(
    "argv",
    [
        '["bash", "writer.sh"]',
        '["python3", "-c", "import os; os.replace(1, 2)"]',
        '["sh", "-c", "mv a b"]',
        '["/usr/bin/custom-writer"]',
    ],
)
def test_all_literal_unsupported_dispatch_is_a_typed_gap(tmp_path: Path, argv: str) -> None:
    """Full literal decoding is not equivalent to modelled dispatch."""

    _deployment(tmp_path, f"import subprocess\n\n\ndef run():\n    subprocess.run({argv})\n")

    closure = derive_python_deployment_closure(tmp_path)

    assert ("tools/node.py", "unsupported_subprocess_dispatch") in closure.observed_gaps


def test_recognized_module_dispatch_creates_no_gap(tmp_path: Path) -> None:
    """Control: a recognized, fully resolved Python module dispatch resolves."""

    _deployment(
        tmp_path,
        "import subprocess\n\n\ndef run():\n    subprocess.run(['python3', '-m', 'tools.worker'])\n",
        extra=_worker_tree(),
    )

    closure = derive_python_deployment_closure(tmp_path)

    assert "tools/worker.py" in closure.modules
    assert not [gap for gap in closure.observed_gaps if "subprocess" in gap[1]]


def test_recognized_script_dispatch_creates_no_gap(tmp_path: Path) -> None:
    _deployment(
        tmp_path,
        "import subprocess\n\n\ndef run():\n    subprocess.run(['python3', 'tools/worker.py'])\n",
        extra=_worker_tree(),
    )

    closure = derive_python_deployment_closure(tmp_path)

    assert "tools/worker.py" in closure.modules
    assert not [gap for gap in closure.observed_gaps if "subprocess" in gap[1]]


def test_unresolvable_module_dispatch_is_typed_as_absent(tmp_path: Path) -> None:
    _deployment(
        tmp_path,
        "import subprocess\n\n\ndef run():\n    subprocess.run(['python3', '-m', 'not.a.module'])\n",
    )

    closure = derive_python_deployment_closure(tmp_path)

    assert ("tools/node.py", "dispatch_module_absent") in closure.observed_gaps


@pytest.mark.parametrize(
    "call",
    [
        "r(['python3', '-m', 'tools.worker', extra])",
        "subprocess.run(['python3', '-m', 'tools.worker', extra])",
    ],
)
def test_partially_dynamic_argv_still_reports_a_gap(tmp_path: Path, call: str) -> None:
    """A decodable constant must not suppress the unresolved-dispatch gap."""

    _deployment(
        tmp_path,
        "import subprocess\nfrom subprocess import run as r\n\n\n"
        f"def run_it(extra):\n    {call}\n",
        extra=_worker_tree(),
    )

    closure = derive_python_deployment_closure(tmp_path)

    assert ("tools/node.py", "unresolved_subprocess_dispatch") in closure.observed_gaps


def test_direct_subprocess_alias_is_recognized(tmp_path: Path) -> None:
    """Review family: `from subprocess import run as r` must not evade detection."""

    _deployment(tmp_path, "from subprocess import run as r\n\n\ndef go(command):\n    r(command)\n")

    closure = derive_python_deployment_closure(tmp_path)

    assert ("tools/node.py", "unresolved_subprocess_dispatch") in closure.observed_gaps


def test_unrelated_py_constant_does_not_suppress_the_gap(tmp_path: Path) -> None:
    _deployment(
        tmp_path,
        "import subprocess\n\nDOC = 'notes.py'\n\n\ndef go(command):\n    subprocess.run(command)\n",
    )

    closure = derive_python_deployment_closure(tmp_path)

    assert ("tools/node.py", "unresolved_subprocess_dispatch") in closure.observed_gaps


def test_sys_executable_head_is_recognized(tmp_path: Path) -> None:
    _deployment(
        tmp_path,
        "import subprocess\nimport sys\n\n\ndef run():\n"
        "    subprocess.run([sys.executable, '-m', 'tools.worker'])\n",
        extra=_worker_tree(),
    )

    closure = derive_python_deployment_closure(tmp_path)

    assert "tools/worker.py" in closure.modules


# ---------------------------------------------------------------------------
# Direct aliases for every supported write module
# ---------------------------------------------------------------------------


@pytest.mark.parametrize(
    ("module", "attribute", "expected"),
    [
        ("os", "replace", "ATOMIC_REPLACE"),
        ("os", "rename", "RENAME"),
        ("os", "remove", "UNLINK"),
        ("os", "unlink", "UNLINK"),
        ("os", "rmdir", "UNLINK"),
        ("os", "truncate", "TRUNCATE"),
        ("os", "ftruncate", "TRUNCATE"),
        ("os", "write", "DESCRIPTOR_WRITE"),
        ("os", "pwrite", "DESCRIPTOR_WRITE"),
        ("os", "writev", "DESCRIPTOR_WRITE"),
        ("os", "chmod", "PERMISSION_MUTATE"),
        ("os", "chown", "PERMISSION_MUTATE"),
        ("os", "link", "NAMESPACE_LINK"),
        ("os", "symlink", "NAMESPACE_LINK"),
        ("shutil", "move", "TREE_MUTATE"),
        ("shutil", "copy", "TREE_MUTATE"),
        ("shutil", "copy2", "TREE_MUTATE"),
        ("shutil", "copyfile", "TREE_MUTATE"),
        ("shutil", "copytree", "TREE_MUTATE"),
        ("shutil", "rmtree", "TREE_MUTATE"),
    ],
)
def test_direct_alias_for_every_supported_operation(
    tmp_path: Path, module: str, attribute: str, expected: str
) -> None:
    _deployment(
        tmp_path,
        f"from {module} import {attribute} as _op\n\n\ndef publish(a, b):\n    _op(a, b)\n",
    )

    assert [kind for _, _, kind in _observe(tmp_path)] == [expected]


@pytest.mark.parametrize(("module", "attribute"), [("os", "replace"), ("shutil", "move")])
def test_module_alias_for_supported_operations(tmp_path: Path, module: str, attribute: str) -> None:
    _deployment(
        tmp_path,
        f"import {module} as _m\n\n\ndef publish(a, b):\n    _m.{attribute}(a, b)\n",
    )

    assert len(_observe(tmp_path)) == 1


# ---------------------------------------------------------------------------
# Symlink and containment safety
# ---------------------------------------------------------------------------


def test_launcher_symlink_escaping_root_fails_closed(tmp_path: Path, tmp_path_factory: pytest.TempPathFactory) -> None:
    outside = tmp_path_factory.mktemp("outside")
    (outside / "evil.py").write_text("import os\n\n\ndef publish(a, b):\n    os.replace(a, b)\n", encoding="utf-8")
    _deployment(tmp_path, "def run():\n    return None\n")
    (tmp_path / "bin").mkdir()
    (tmp_path / "bin" / "escape").symlink_to(outside / "evil.py")

    entrypoints, findings, _ = derive_deployed_entrypoints(tmp_path)

    assert any(item.rule_id == "launcher_escapes_repository_root" for item in findings)
    assert all("evil.py" not in item.target for item in entrypoints)


def test_launcher_directory_symlink_is_a_typed_finding(
    tmp_path: Path, tmp_path_factory: pytest.TempPathFactory
) -> None:
    """An unopenable launcher directory cannot collapse into an empty launcher set."""

    _deployment(tmp_path, "value = 1\n")
    outside = tmp_path_factory.mktemp("launcher_directory")
    (tmp_path / "bin").symlink_to(outside, target_is_directory=True)

    _, findings, _ = derive_deployed_entrypoints(tmp_path)

    assert any(item.rule_id == "launcher_directory_unreadable" for item in findings)


def test_dangling_launcher_symlink_fails_closed(tmp_path: Path) -> None:
    _deployment(tmp_path, "def run():\n    return None\n")
    (tmp_path / "bin").mkdir()
    (tmp_path / "bin" / "dangling").symlink_to(tmp_path / "bin" / "absent-target")

    _, findings, _ = derive_deployed_entrypoints(tmp_path)

    assert any(
        item.rule_id in {"launcher_is_not_a_regular_file", "undecodable_launcher"} for item in findings
    )


def test_install_target_symlink_escaping_root_is_unresolvable(
    tmp_path: Path, tmp_path_factory: pytest.TempPathFactory
) -> None:
    outside = tmp_path_factory.mktemp("outside2")
    (outside / "evil.py").write_text("import os\n", encoding="utf-8")
    (tmp_path / "scripts").mkdir(parents=True)
    (tmp_path / "scripts" / "install_zenodex.sh").write_text(_INSTALL, encoding="utf-8")
    (tmp_path / "tools").mkdir()
    (tmp_path / "tools" / "node.py").symlink_to(outside / "evil.py")

    _, findings, _ = derive_deployed_entrypoints(tmp_path)

    assert [item.rule_id for item in findings] == ["launcher_target_unresolvable"]


@pytest.mark.parametrize(
    ("shape", "mechanism"),
    [("escapes_root", "import_target_escapes_root"), ("dangling", "import_target_dangling"), ("loop", "import_target_unresolvable")],
)
def test_unscannable_local_import_candidate_is_a_typed_gap(
    tmp_path: Path, tmp_path_factory: pytest.TempPathFactory, shape: str, mechanism: str
) -> None:
    """A reachable local edge must never be dropped silently."""

    _deployment(tmp_path, "import tools.worker\n", extra={"tools/__init__.py": ""})
    target = tmp_path / "tools" / "worker.py"
    if shape == "escapes_root":
        outside = tmp_path_factory.mktemp("outside_import")
        (outside / "worker.py").write_text("import os\n", encoding="utf-8")
        target.symlink_to(outside / "worker.py")
    elif shape == "dangling":
        target.symlink_to(tmp_path / "tools" / "absent.py")
    else:
        (tmp_path / "tools" / "other.py").symlink_to(target)
        target.symlink_to(tmp_path / "tools" / "other.py")

    closure = derive_python_deployment_closure(tmp_path)

    assert ("tools/node.py", mechanism) in closure.observed_gaps
    assert "tools/worker.py" not in closure.modules


@pytest.mark.parametrize(
    ("shape", "mechanism"),
    [("escapes_root", "dispatch_target_escapes_root"), ("dangling", "dispatch_target_dangling")],
)
def test_unscannable_dispatch_candidate_is_a_typed_gap(
    tmp_path: Path, tmp_path_factory: pytest.TempPathFactory, shape: str, mechanism: str
) -> None:
    _deployment(tmp_path, 'SURFACES = {"a": "surface.py"}\n')
    target = tmp_path / "tools" / "surface.py"
    if shape == "escapes_root":
        outside = tmp_path_factory.mktemp("outside_dispatch")
        (outside / "surface.py").write_text("import os\n", encoding="utf-8")
        target.symlink_to(outside / "surface.py")
    else:
        target.symlink_to(tmp_path / "tools" / "absent.py")

    closure = derive_python_deployment_closure(tmp_path)

    assert ("tools/node.py", mechanism) in closure.observed_gaps
    assert "tools/surface.py" not in closure.modules


def test_ordinary_external_import_stays_out_of_scope(tmp_path: Path) -> None:
    """An import with no local candidate is a library, not a dropped edge."""

    _deployment(tmp_path, "import json\nimport collections.abc\n")

    closure = derive_python_deployment_closure(tmp_path)

    assert not [gap for gap in closure.observed_gaps if gap[1].startswith("import_target_")]


def test_symlink_loop_does_not_crash_the_closure(tmp_path: Path) -> None:
    _deployment(tmp_path, "def run():\n    return None\n")
    (tmp_path / "tools" / "loop_a.py").symlink_to(tmp_path / "tools" / "loop_b.py")
    (tmp_path / "tools" / "loop_b.py").symlink_to(tmp_path / "tools" / "loop_a.py")

    closure = derive_python_deployment_closure(tmp_path)

    assert "tools/node.py" in closure.modules


def test_contained_python_subprocess_target_maps_to_unsupported(tmp_path: Path) -> None:
    """A recognized shape whose target does not resolve stays unsupported."""

    _deployment(
        tmp_path,
        "import subprocess\n\n\ndef run():\n    subprocess.run(['python3', 'tools/absent.py'])\n",
    )

    closure = derive_python_deployment_closure(tmp_path)

    assert ("tools/node.py", "unsupported_subprocess_dispatch") in closure.observed_gaps


def test_scan_opens_descendants_only_through_componentwise_directory_fds(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """Only the filesystem root is opened without an already confined dir fd."""

    _deployment(tmp_path, "import os\n\n\ndef publish(a, b):\n    os.replace(a, b)\n")
    opened: list[tuple[str, int | None]] = []
    original = os.open

    def _record(
        path: str | bytes | Path,
        flags: int,
        mode: int = 0o777,
        *,
        dir_fd: int | None = None,
    ) -> int:
        opened.append((os.fsdecode(path), dir_fd))
        return original(path, flags, mode, dir_fd=dir_fd)

    monkeypatch.setattr(os, "open", _record)
    derive_python_deployment_closure(tmp_path)

    assert opened
    assert {path for path, directory_fd in opened if directory_fd is None} == {"/"}
    assert all(Path(path).is_absolute() or directory_fd is not None for path, directory_fd in opened)


# ---------------------------------------------------------------------------
# Resource ceilings and canonical paths
# ---------------------------------------------------------------------------


@pytest.mark.parametrize(
    "value",
    ["/etc/passwd", "tools/../node.py", "tools\\node.py", "C:/node.py", "", "tools/./node.py"],
)
def test_noncanonical_paths_are_rejected(value: str) -> None:
    assert canonical_relative_path(value) is None


def test_canonical_path_is_accepted() -> None:
    assert canonical_relative_path("tools/node.py") == "tools/node.py"


def test_oversized_reachable_source_becomes_a_typed_gap(tmp_path: Path) -> None:
    _deployment(tmp_path, "import tools.big\n", extra={"tools/__init__.py": ""})
    (tmp_path / "tools" / "big.py").write_text("x = '" + "a" * (4 * 1024 * 1024 + 8) + "'\n", encoding="utf-8")

    closure = derive_python_deployment_closure(tmp_path)

    assert ("tools/big.py", "source_unscannable") in closure.observed_gaps
    assert "tools/big.py" in closure.unscanned_modules
    assert "tools/big.py" not in closure.modules


def test_unparsable_reachable_source_becomes_a_typed_gap(tmp_path: Path) -> None:
    _deployment(tmp_path, "import tools.broken\n", extra={"tools/__init__.py": "", "tools/broken.py": "def (\n"})

    closure = derive_python_deployment_closure(tmp_path)

    assert ("tools/broken.py", "source_unparsable") in closure.observed_gaps


def test_manifest_entry_ceiling_is_enforced(tmp_path: Path) -> None:
    entries = [
        _entry(path=f"tools/m{index:05d}.py", sink_id=f"s{index}", identity_fingerprint="0" * 64)
        for index in range(4097)
    ]
    path = _manifest(tmp_path, entries)

    with pytest.raises(ValueError, match="exceeds 4096 entries"):
        load_value_sink_manifest(path)


# ---------------------------------------------------------------------------
# Launcher decoding fails closed
# ---------------------------------------------------------------------------


def test_container_entrypoint_module_dispatch_is_decoded(tmp_path: Path) -> None:
    """The deployed API surface is reached only through the container entrypoint."""

    _deployment(tmp_path, "def run():\n    return None\n")
    (tmp_path / ".docker").mkdir()
    (tmp_path / ".docker" / "entrypoint.sh").write_text(
        "#!/bin/sh\npython -m src.integration.api_server &\n", encoding="utf-8"
    )
    (tmp_path / "Dockerfile").write_text(
        'COPY .docker/entrypoint.sh /entrypoint.sh\nENTRYPOINT ["/entrypoint.sh"]\n',
        encoding="utf-8",
    )
    (tmp_path / "src" / "integration").mkdir(parents=True)
    (tmp_path / "src" / "__init__.py").write_text("", encoding="utf-8")
    (tmp_path / "src" / "integration" / "__init__.py").write_text("", encoding="utf-8")
    (tmp_path / "src" / "integration" / "api_server.py").write_text(
        "import os\n\n\ndef publish(a, b):\n    os.replace(a, b)\n", encoding="utf-8"
    )

    closure = derive_python_deployment_closure(tmp_path)

    assert "src/integration/api_server.py" in closure.modules
    assert any(item.discovery == "CONTAINER_ENTRYPOINT" for item in closure.entrypoints)


def test_undecodable_launcher_is_a_finding(tmp_path: Path) -> None:
    _deployment(tmp_path, "def run():\n    return None\n")
    (tmp_path / "bin").mkdir()
    (tmp_path / "bin" / "zenodex-mystery").write_text("#!/bin/sh\nexec ./something-else\n", encoding="utf-8")

    _, findings, _ = derive_deployed_entrypoints(tmp_path)

    assert sorted({item.rule_id for item in findings}) == [
        "unconsumed_launcher_directive",
        "undecodable_launcher",
    ]


# ---------------------------------------------------------------------------
# Launcher grammar: an unmodelled directive is never silently ignored
# ---------------------------------------------------------------------------


def test_mixed_launcher_reports_the_unmodelled_directive(tmp_path: Path) -> None:
    """A decoded dispatch must not excuse a second command on another line."""

    _deployment(tmp_path, "x = 1\n")
    (tmp_path / "bin").mkdir()
    (tmp_path / "bin" / "mixed").write_text(
        '#!/bin/sh\nexec python3 "${repo_dir}/tools/node.py"\nsh evil-writer.sh\n', encoding="utf-8"
    )

    entrypoints, findings, _ = derive_deployed_entrypoints(tmp_path)

    assert any(item.target == "tools/node.py" for item in entrypoints)
    assert [item.rule_id for item in findings if item.path == "bin/mixed"] == [
        "unconsumed_launcher_directive"
    ]


@pytest.mark.parametrize(
    "line",
    [
        "set -eu; sh evil.sh",
        "set -eu && sh evil.sh",
        "set -eu | sh evil.sh",
        "x=benign; sh evil.sh",
        'script_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd); sh evil.sh',
        "repo_dir=$(sh evil.sh && pwd)",
        'exec python3 "${repo_dir}/tools/x.py"; sh evil.sh',
        'exec python3 "${repo_dir}/tools/x.py" && sh evil.sh',
        'exec python3 "${repo_dir}/tools/x.py" | tee /etc/passwd',
        'exec python3 "${repo_dir}/tools/x.py" < <(sh evil.sh)',
        'exec python3 "${repo_dir}/tools/x.py" $(sh evil.sh)',
        'env FOO=1 python3 "${repo_dir}/tools/x.py"',
        "if [ -f marker ]; then sh evil.sh; fi",
        "sh evil-writer.sh",
        "for f in *; do rm $f; done",
    ],
)
def test_trailing_shell_syntax_is_unmodelled(line: str) -> None:
    """Prefix acceptance would let appended syntax ride on a recognized form."""

    assert classify_launcher_line(line) == "UNMODELLED"


@pytest.mark.parametrize(
    ("line", "expected"),
    [
        ("#!/usr/bin/env sh", "INERT"),
        ("# a comment", "INERT"),
        ("", "INERT"),
        ("set -eu", "INERT"),
        ('script_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)', "INERT"),
        ('repo_dir=$(CDPATH= cd -- "${script_dir}/.." && pwd)', "INERT"),
        ('exec python3 "${repo_dir}/tools/zenoctl.py" "$@"', "DISPATCH"),
        ('exec python3 "${repo_dir}/tools/zenoctl.py" testnet local public "$@"', "DISPATCH"),
    ],
)
def test_generated_launcher_forms_are_recognized(line: str, expected: str) -> None:
    assert classify_launcher_line(line) == expected


def test_repository_launchers_decode_without_findings() -> None:
    """The closed grammar must still accept every checked-in wrapper."""

    entrypoints, findings, _ = derive_deployed_entrypoints(ROOT)

    assert [item for item in findings if item.path.startswith("bin/")] == []
    assert any(item.discovery == "LAUNCHER_WRAPPER" for item in entrypoints)


def test_install_wrapper_with_trailing_command_is_a_finding(tmp_path: Path) -> None:
    _deployment(
        tmp_path,
        "x = 1\n",
        install='install_wrapper "n" python3 "${repo_dir}/tools/node.py"; sh evil.sh\n',
    )

    _, findings, _ = derive_deployed_entrypoints(tmp_path)

    assert [item.rule_id for item in findings] == ["undecodable_install_wrapper"]


def test_multi_command_installer_decodes_every_target_and_refuses_the_shape(tmp_path: Path) -> None:
    """D5: a second installed command remains in scope despite shell composition."""

    install = (
        'install_wrapper "one" python3 "${repo_dir}/tools/one.py"; '
        'install_wrapper "two" python3 "${repo_dir}/tools/two.py"\n'
    )
    _deployment(
        tmp_path,
        "value = 1\n",
        install=install,
        extra={
            "tools/one.py": "from pathlib import Path\nPath('one').touch()\n",
            "tools/two.py": "from pathlib import Path\nPath('two').touch()\n",
        },
    )

    entrypoints, findings, _ = derive_deployed_entrypoints(tmp_path)

    assert {item.target for item in entrypoints} == {"tools/one.py", "tools/two.py"}
    assert any(item.rule_id == "multi_command_install_line" for item in findings)


def test_installer_function_declaration_is_not_misread_as_an_install_call(tmp_path: Path) -> None:
    install = (
        "install_wrapper() {\n    return 0\n}\n"
        'install_wrapper "node" python3 "${repo_dir}/tools/node.py"\n'
    )
    _deployment(tmp_path, "value = 1\n", install=install)

    entrypoints, findings, _ = derive_deployed_entrypoints(tmp_path)

    assert [item.target for item in entrypoints if item.discovery == "INSTALL_SCRIPT"] == [
        "tools/node.py"
    ]
    assert not [item for item in findings if item.rule_id == "undecodable_install_wrapper"]


# ---------------------------------------------------------------------------
# Count ceilings report before omission
# ---------------------------------------------------------------------------


@pytest.mark.parametrize(("count", "expected"), [(64, False), (65, True)])
def test_dockerfile_count_ceiling_bva(tmp_path: Path, count: int, expected: bool) -> None:
    _deployment(tmp_path, "x = 1\n")
    for index in range(count):
        (tmp_path / f"Dockerfile.{index:03d}").write_text('ENTRYPOINT ["/entrypoint.sh"]\n', encoding="utf-8")

    _, findings, _ = derive_deployed_entrypoints(tmp_path)

    rules = {item.rule_id for item in findings}
    assert ("dockerfile_count_ceiling_exceeded" in rules) is expected


def test_case_insensitive_docker_copy_binds_the_exact_entrypoint_source(tmp_path: Path) -> None:
    """D6: Docker instruction case and basename decoys cannot redirect the scan."""

    _deployment(tmp_path, "value = 1\n")
    (tmp_path / ".docker").mkdir()
    (tmp_path / ".docker" / "actual.sh").write_text(
        "python tools/node.py\n", encoding="utf-8"
    )
    (tmp_path / "scripts" / "entrypoint.sh").write_text(
        "python tools/decoy.py\n", encoding="utf-8"
    )
    (tmp_path / "tools" / "decoy.py").write_text("value = 2\n", encoding="utf-8")
    (tmp_path / "Dockerfile.lower").write_text(
        'cOpY .docker/actual.sh /entrypoint.sh\neNtRyPoInT ["/entrypoint.sh"]\n',
        encoding="utf-8",
    )

    entrypoints, findings, _ = derive_deployed_entrypoints(tmp_path)

    container = [item for item in entrypoints if item.discovery == "CONTAINER_ENTRYPOINT"]
    assert [(item.entrypoint_id, item.target) for item in container] == [
        (".docker/actual.sh", "tools/node.py")
    ]
    assert not [item for item in findings if "container" in item.rule_id]


def test_unrelated_directory_and_wildcard_copies_do_not_forge_dispatch_findings(
    tmp_path: Path,
) -> None:
    _deployment(tmp_path, "value = 1\n")
    (tmp_path / ".docker").mkdir()
    (tmp_path / ".docker" / "entrypoint.sh").write_text(
        "python tools/node.py\n", encoding="utf-8"
    )
    (tmp_path / "Dockerfile").write_text(
        "COPY src/ /app/src/\n"
        "COPY tools/dex-ui/package*.json /app/ui/\n"
        "COPY .docker/entrypoint.sh /entrypoint.sh\n"
        'ENTRYPOINT ["/entrypoint.sh"]\n',
        encoding="utf-8",
    )

    entrypoints, findings, _ = derive_deployed_entrypoints(tmp_path)

    assert any(item.discovery == "CONTAINER_ENTRYPOINT" for item in entrypoints)
    assert not [item for item in findings if item.rule_id == "container_copy_source_unresolvable"]


def test_docker_entrypoint_without_copy_binding_is_refused(tmp_path: Path) -> None:
    _deployment(tmp_path, "value = 1\n")
    (tmp_path / ".docker").mkdir()
    (tmp_path / ".docker" / "entrypoint.sh").write_text(
        "python tools/node.py\n", encoding="utf-8"
    )
    (tmp_path / "Dockerfile").write_text('ENTRYPOINT ["/entrypoint.sh"]\n', encoding="utf-8")

    entrypoints, findings, _ = derive_deployed_entrypoints(tmp_path)

    assert not [item for item in entrypoints if item.discovery == "CONTAINER_ENTRYPOINT"]
    assert any(item.rule_id == "container_entrypoint_copy_unbound" for item in findings)


def test_docker_copy_source_with_escaping_symlink_is_refused(
    tmp_path: Path, tmp_path_factory: pytest.TempPathFactory
) -> None:
    outside = tmp_path_factory.mktemp("docker_copy_outside")
    (outside / "entrypoint.sh").write_text("python tools/node.py\n", encoding="utf-8")
    _deployment(tmp_path, "value = 1\n")
    (tmp_path / ".docker").mkdir()
    (tmp_path / ".docker" / "entrypoint.sh").symlink_to(outside / "entrypoint.sh")
    (tmp_path / "Dockerfile").write_text(
        'COPY .docker/entrypoint.sh /entrypoint.sh\nENTRYPOINT ["/entrypoint.sh"]\n',
        encoding="utf-8",
    )

    entrypoints, findings, _ = derive_deployed_entrypoints(tmp_path)

    assert not [item for item in entrypoints if item.discovery == "CONTAINER_ENTRYPOINT"]
    assert any(item.rule_id == "container_copy_source_unresolvable" for item in findings)


@pytest.mark.parametrize(("count", "expected"), [(64, False), (65, True)])
def test_launcher_count_ceiling_bva(tmp_path: Path, count: int, expected: bool) -> None:
    _deployment(tmp_path, "x = 1\n")
    (tmp_path / "bin").mkdir()
    for index in range(count):
        (tmp_path / "bin" / f"launcher{index:03d}").write_text(
            '#!/bin/sh\nexec python3 "${repo_dir}/tools/node.py"\n', encoding="utf-8"
        )

    _, findings, _ = derive_deployed_entrypoints(tmp_path)

    rules = {item.rule_id for item in findings}
    assert ("launcher_count_ceiling_exceeded" in rules) is expected


def test_componentwise_read_refuses_an_ancestor_symlink(
    tmp_path: Path, tmp_path_factory: pytest.TempPathFactory
) -> None:
    """D7: O_NOFOLLOW applies to every path component, not only the leaf."""

    outside = tmp_path_factory.mktemp("ancestor_outside")
    (outside / "secret.py").write_text("raise RuntimeError('must not read')\n", encoding="utf-8")
    (tmp_path / "linked").symlink_to(outside, target_is_directory=True)

    text, error = read_bounded_text(
        tmp_path / "linked" / "secret.py", 4096, root=tmp_path
    )

    assert text is None
    assert error is not None


def test_bounded_materialization_stops_after_limit_plus_one() -> None:
    """D8: an unbounded producer is sampled only through the first overflow item."""

    observed: list[int] = []

    def values() -> Iterator[int]:
        value = 0
        while True:
            observed.append(value)
            yield value
            value += 1

    items, exceeded = bounded_materialize_v2(values(), 3)

    assert items == ()
    assert exceeded is True
    assert observed == [0, 1, 2, 3]


def test_launcher_enumeration_has_no_materialize_before_bound_calls() -> None:
    """D8 architecture killer: sorted(Path.glob/rglob/iterdir) is forbidden here."""

    tree = ast.parse(inspect.getsource(launcher_module))
    forbidden: list[str] = []
    for node in ast.walk(tree):
        if not isinstance(node, ast.Call) or not isinstance(node.func, ast.Name):
            continue
        if node.func.id != "sorted" or not node.args or not isinstance(node.args[0], ast.Call):
            continue
        producer = node.args[0].func
        if isinstance(producer, ast.Attribute) and producer.attr in {"glob", "iterdir", "rglob"}:
            forbidden.append(producer.attr)

    assert forbidden == []


def test_launcher_line_ceiling_is_enforced(tmp_path: Path) -> None:
    _deployment(tmp_path, "x = 1\n")
    (tmp_path / "bin").mkdir()
    (tmp_path / "bin" / "long").write_text("#!/bin/sh\n" + "# filler\n" * 600, encoding="utf-8")

    _, findings, _ = derive_deployed_entrypoints(tmp_path)

    assert any(item.rule_id == "launcher_line_ceiling_exceeded" for item in findings)


# ---------------------------------------------------------------------------
# Subprocess dispatch environment is not fixed by the source
# ---------------------------------------------------------------------------


def test_bare_interpreter_dispatch_records_an_unbound_gap(tmp_path: Path) -> None:
    """PATH and the working directory decide what actually runs."""

    _deployment(
        tmp_path,
        "import subprocess\n\n\ndef run():\n    subprocess.run(['python3', '-m', 'tools.worker'])\n",
        extra=_worker_tree(),
    )

    closure = derive_python_deployment_closure(tmp_path)

    assert ("tools/node.py", "unbound_dispatch_environment") in closure.observed_gaps
    # Discovery is preserved: the local candidate is still scanned.
    assert "tools/worker.py" in closure.modules


def test_relative_script_dispatch_records_an_unbound_gap(tmp_path: Path) -> None:
    _deployment(
        tmp_path,
        "import subprocess\n\n\ndef run():\n    subprocess.run(['python3', 'tools/worker.py'])\n",
        extra=_worker_tree(),
    )

    closure = derive_python_deployment_closure(tmp_path)

    assert ("tools/node.py", "unbound_dispatch_environment") in closure.observed_gaps
    assert "tools/worker.py" in closure.modules


def test_sys_executable_dispatch_is_still_unbound(tmp_path: Path) -> None:
    _deployment(
        tmp_path,
        "import subprocess\nimport sys\n\n\ndef run():\n"
        "    subprocess.run([sys.executable, '-m', 'tools.worker'])\n",
        extra=_worker_tree(),
    )

    closure = derive_python_deployment_closure(tmp_path)

    assert ("tools/node.py", "unbound_dispatch_environment") in closure.observed_gaps


def test_undecodable_install_wrapper_is_a_finding(tmp_path: Path) -> None:
    _deployment(tmp_path, "def run():\n    return None\n", install='install_wrapper "n" bash "${repo_dir}/tools/n.sh"\n')

    _, findings, _ = derive_deployed_entrypoints(tmp_path)

    assert [item.rule_id for item in findings] == ["undecodable_install_wrapper"]


def test_missing_launcher_target_is_a_finding(tmp_path: Path) -> None:
    (tmp_path / "scripts").mkdir(parents=True)
    (tmp_path / "scripts" / "install_zenodex.sh").write_text(_INSTALL, encoding="utf-8")

    _, findings, _ = derive_deployed_entrypoints(tmp_path)

    assert [item.rule_id for item in findings] == ["launcher_target_unresolvable"]


def test_absent_install_script_is_a_finding(tmp_path: Path) -> None:
    _, findings, _ = derive_deployed_entrypoints(tmp_path)

    assert [item.rule_id for item in findings] == ["install_script_missing"]


def test_install_script_without_launchers_is_a_finding(tmp_path: Path) -> None:
    (tmp_path / "scripts").mkdir(parents=True)
    (tmp_path / "scripts" / "install_zenodex.sh").write_text("#!/bin/sh\nset -eu\n", encoding="utf-8")

    _, findings, _ = derive_deployed_entrypoints(tmp_path)

    assert [item.rule_id for item in findings] == ["install_script_declares_no_launcher"]


# ---------------------------------------------------------------------------
# Closure-gap ratchet
# ---------------------------------------------------------------------------


def test_new_dynamic_import_breaks_the_gate(tmp_path: Path) -> None:
    _deployment(tmp_path, "import importlib\n\n\ndef run(name):\n    return importlib.import_module(name)\n")
    _manifest(tmp_path, [_entry()], gaps=[])

    report = check_m6_value_sinks_v2(tmp_path)

    assert report["scanner_relative_manifest_agreement"] is False
    assert any(item["rule_id"] == "undeclared_closure_gap" for item in report["findings"])


def test_stale_declared_gap_breaks_the_gate(tmp_path: Path) -> None:
    _deployment(tmp_path, "import os\n\n\ndef publish(a, b):\n    os.replace(a, b)\n")
    _manifest(tmp_path, [_entry()], gaps=[{"mechanism": "import_module", "path": "tools/node.py", "rationale": "stale"}])

    report = check_m6_value_sinks_v2(tmp_path)

    assert any(item["rule_id"] == "stale_closure_gap" for item in report["findings"])


def test_closure_gap_ordering_is_enforced(tmp_path: Path) -> None:
    _deployment(tmp_path, "def run():\n    return None\n")
    path = _manifest(
        tmp_path,
        [_entry()],
        gaps=[
            {"mechanism": "z", "path": "tools/zzz.py", "rationale": "r"},
            {"mechanism": "a", "path": "tools/aaa.py", "rationale": "r"},
        ],
    )

    with pytest.raises(ValueError, match="canonical order"):
        load_closure_gaps(path)


def test_closure_gap_value_object_is_ordered() -> None:
    first = ClosureGapV2("tools/a.py", "exec_module", "r")
    second = ClosureGapV2("tools/b.py", "exec_module", "r")

    assert sorted((second, first)) == [first, second]


# ---------------------------------------------------------------------------
# Manifest typed rejection
# ---------------------------------------------------------------------------


@pytest.mark.parametrize(
    ("overrides", "reason"),
    [
        ({"sink_kind": "NOVEL"}, "sink_kind is unknown"),
        ({"classification": "NOVEL"}, "classification is unknown"),
        ({"mediation_status": "NOVEL"}, "mediation_status is unknown"),
        ({"identity_fingerprint": "abc"}, "must be lowercase SHA-256"),
        ({"deployed_reachable": 1}, "must be an exact boolean"),
        ({"occurrence_count": 0}, "positive exact integer"),
        ({"occurrence_count": True}, "positive exact integer"),
        ({"release_binding": "release-1"}, "must remain null"),
        ({"path": "/etc/passwd.py"}, "canonical repository-relative Python path"),
        ({"path": "tools/../node.py"}, "canonical repository-relative Python path"),
        ({"path": "tools/node.rs"}, "canonical repository-relative Python path"),
        ({"deployed_reachable": True, "mediation_status": "RESEARCH_UNMOUNTED"}, "deployed sink as research-only"),
        ({"deployed_reachable": False, "mediation_status": "UNMEDIATED_DEPLOYED_WRITER"}, "undeployed sink as a deployed writer"),
        (
            {
                "classification": "AUTHORITY_CONTROL_STATE",
                "consumers": [
                    _consumer(reference="tools/z.py", source_path="tools/z.py"),
                    _consumer(reference="tools/a.py", source_path="tools/a.py"),
                ],
            },
            "canonically sorted",
        ),
        (
            {
                "classification": "AUTHORITY_CONTROL_STATE",
                "consumers": [_consumer(kind="NOVEL", reference="x", source_path="x")],
            },
            "kind is unknown",
        ),
        (
            {
                "classification": "AUTHORITY_CONTROL_STATE",
                "consumers": [
                    _consumer(reference="../escape.py", source_path="../escape.py")
                ],
            },
            "canonical repository-relative path",
        ),
        ({"classification": UNADJUDICATED}, "classification and mediation both unadjudicated"),
        (
            {
                "classification": UNADJUDICATED,
                "mediation_status": UNADJUDICATED,
                "consumers": [
                    _consumer(
                        kind="LAUNCHER_ID",
                        reference="zenodex-node",
                        source_path="scripts/install_zenodex.sh",
                    )
                ],
            },
            "names consumers for an unadjudicated sink",
        ),
    ],
)
def test_manifest_entry_rejection(tmp_path: Path, overrides: dict[str, object], reason: str) -> None:
    path = _manifest(tmp_path, [_entry(**overrides)])

    with pytest.raises(ValueError, match=reason):
        load_value_sink_manifest(path)


# ---------------------------------------------------------------------------
# Bounded manifest decoding: hostile input is typed, never a crash
# ---------------------------------------------------------------------------


def _write_raw(tmp_path: Path, body: str) -> Path:
    (tmp_path / "tools").mkdir(parents=True, exist_ok=True)
    path = tmp_path / "tools" / "m6_value_sink_manifest_v2.json"
    path.write_text(body, encoding="utf-8")
    return path


def test_deeply_nested_manifest_raises_typed_error_not_recursion(tmp_path: Path) -> None:
    """A ~40 KB document of 20,000 nested arrays must not exhaust the stack."""

    deep = "[" * 20_000 + "]" * 20_000
    path = _write_raw(
        tmp_path,
        '{"schema":"zenodex/m6-value-sink-inventory/v2","scope":' + deep + ',"entries":[],"closure_gaps":[]}',
    )

    with pytest.raises(ValueError, match="exceeds depth"):
        load_value_sink_manifest(path)


@pytest.mark.parametrize(("depth", "rejected"), [(64, False), (65, True)])
def test_manifest_depth_bva(tmp_path: Path, depth: int, rejected: bool) -> None:
    nested = "[" * (depth - 1) + '"s"' + "]" * (depth - 1)
    path = _write_raw(
        tmp_path,
        '{"schema":"zenodex/m6-value-sink-inventory/v2","scope":' + nested + ',"entries":[],"closure_gaps":[]}',
    )

    with pytest.raises(ValueError) as caught:
        load_value_sink_document(path)

    assert ("exceeds depth" in str(caught.value)) is rejected


def test_manifest_byte_ceiling_is_enforced(tmp_path: Path) -> None:
    path = _write_raw(
        tmp_path,
        '{"schema":"zenodex/m6-value-sink-inventory/v2","scope":"'
        + "a" * (4 * 1024 * 1024 + 16)
        + '","entries":[],"closure_gaps":[]}',
    )

    with pytest.raises(ValueError, match="exceeds .* bytes"):
        load_value_sink_document(path)


@pytest.mark.parametrize(
    ("body", "reason"),
    [
        ('"x":1.5', "non-integer number"),
        ('"x":NaN', "nonfinite constant"),
        ('"x":Infinity', "nonfinite constant"),
        ('"x":' + "9" * 21, "exceeds .* digits"),
    ],
)
def test_manifest_number_rejection(tmp_path: Path, body: str, reason: str) -> None:
    path = _write_raw(
        tmp_path,
        '{"schema":"zenodex/m6-value-sink-inventory/v2","scope":"s","entries":[],"closure_gaps":[],' + body + "}",
    )

    with pytest.raises(ValueError, match=reason):
        load_value_sink_document(path)


def test_manifest_node_ceiling_is_enforced(tmp_path: Path) -> None:
    path = _write_raw(
        tmp_path,
        '{"schema":"zenodex/m6-value-sink-inventory/v2","scope":"s","closure_gaps":[],"entries":['
        + ",".join("0" for _ in range(200_001))
        + "]}",
    )

    with pytest.raises(ValueError, match="exceeds .* nodes"):
        load_value_sink_document(path)


def test_duplicate_closure_gap_identity_is_rejected(tmp_path: Path) -> None:
    """Reconciliation compares identities, so a differing rationale must not hide one."""

    path = _manifest(
        tmp_path,
        [_entry()],
        gaps=[
            {"mechanism": "m", "path": "tools/a.py", "rationale": "first"},
            {"mechanism": "m", "path": "tools/a.py", "rationale": "second"},
        ],
    )

    with pytest.raises(ValueError, match="closure_gaps identities must be unique"):
        load_closure_gaps(path)


def test_entries_and_gaps_come_from_one_read(tmp_path: Path) -> None:
    path = _manifest(
        tmp_path,
        [_entry()],
        gaps=[{"mechanism": "import_module", "path": "tools/a.py", "rationale": "declared"}],
    )

    document = load_value_sink_document(path)

    assert len(document.entries) == 1
    assert [gap.identity() for gap in document.closure_gaps] == [("tools/a.py", "import_module")]


# ---------------------------------------------------------------------------
# Regeneration must not silently re-adjudicate a changed writer
# ---------------------------------------------------------------------------


def test_changed_fingerprint_resets_the_prior_judgement(tmp_path: Path) -> None:
    _deployment(
        tmp_path,
        "import os\n\n\ndef publish():\n    os.replace('reserve.tmp', 'reserve.live')\n",
    )
    emitted = render_manifest_v2(tmp_path)
    entry = dict(emitted["entries"][0])
    entry.update(
        {
            "classification": "ADVISORY_CONTROL_STATE",
            "mediation_status": "NON_VALUE_EFFECT",
            "rationale": "reviewed as an evidence write",
        }
    )
    _manifest(tmp_path, [entry])
    assert render_manifest_v2(tmp_path)["entries"][0]["classification"] == "ADVISORY_CONTROL_STATE"

    (tmp_path / "tools" / "node.py").write_text(
        "import os\n\n\ndef publish():\n    os.replace('balance.tmp', 'balance.live')\n",
        encoding="utf-8",
    )
    regenerated = render_manifest_v2(tmp_path)["entries"][0]

    assert regenerated["classification"] == "UNADJUDICATED"
    assert regenerated["mediation_status"] == "UNADJUDICATED"
    assert regenerated["rationale"] == "UNADJUDICATED"
    assert regenerated["consumers"] == []
    assert regenerated["release_binding"] is None


def test_changed_occurrence_count_resets_the_prior_judgement(tmp_path: Path) -> None:
    _deployment(
        tmp_path,
        "import os\n\n\ndef publish():\n    os.replace('a.tmp', 'a.live')\n",
    )
    emitted = render_manifest_v2(tmp_path)
    entry = dict(emitted["entries"][0])
    entry.update(
        {
            "classification": "ADVISORY_CONTROL_STATE",
            "mediation_status": "NON_VALUE_EFFECT",
            "rationale": "reviewed",
        }
    )
    _manifest(tmp_path, [entry])

    (tmp_path / "tools" / "node.py").write_text(
        "import os\n\n\ndef publish():\n    os.replace('a.tmp', 'a.live')\n"
        "    os.replace('b.tmp', 'b.live')\n",
        encoding="utf-8",
    )
    regenerated = render_manifest_v2(tmp_path)["entries"][0]

    assert regenerated["occurrence_count"] == 2
    assert regenerated["classification"] == "UNADJUDICATED"


def test_unchanged_identity_keeps_its_judgement(tmp_path: Path) -> None:
    """Control: a stable writer must not be re-adjudicated on every regeneration."""

    _deployment(
        tmp_path,
        "import os\n\n\ndef publish():\n    os.replace('a.tmp', 'a.live')\n",
    )
    emitted = render_manifest_v2(tmp_path)
    entry = dict(emitted["entries"][0])
    entry.update(
        {
            "classification": "ADVISORY_CONTROL_STATE",
            "mediation_status": "NON_VALUE_EFFECT",
            "rationale": "reviewed",
        }
    )
    _manifest(tmp_path, [entry])

    regenerated = render_manifest_v2(tmp_path)["entries"][0]

    assert regenerated["classification"] == "ADVISORY_CONTROL_STATE"
    assert regenerated["sink_id"] == emitted["entries"][0]["sink_id"]


def test_manifest_rejects_duplicate_json_keys(tmp_path: Path) -> None:
    (tmp_path / "tools").mkdir(parents=True)
    path = tmp_path / "tools" / "m6_value_sink_manifest_v2.json"
    path.write_text(
        '{"schema": "zenodex/m6-value-sink-inventory/v2", "schema": "x", "scope": "s",'
        ' "entries": [], "closure_gaps": []}',
        encoding="utf-8",
    )

    with pytest.raises(ValueError, match="duplicate JSON key"):
        load_value_sink_manifest(path)


def test_manifest_rejects_noncanonical_entry_order(tmp_path: Path) -> None:
    path = _manifest(tmp_path, [_entry(path="tools/zzz.py"), _entry(path="tools/aaa.py")])

    with pytest.raises(ValueError, match="canonical identity order"):
        load_value_sink_manifest(path)


def test_manifest_rejects_a_sink_id_that_does_not_bind_the_full_identity(tmp_path: Path) -> None:
    path = _manifest(tmp_path, [_entry(sink_id="legacy-caller-selected-id")])

    with pytest.raises(ValueError, match="must equal its full-identity ID"):
        load_value_sink_manifest(path)


# ---------------------------------------------------------------------------
# Parent package initializers execute before the leaf
# ---------------------------------------------------------------------------


def _package_with_writer_initializer(root: Path) -> None:
    package = root / "pkg" / "sub"
    package.mkdir(parents=True)
    (root / "pkg" / "__init__.py").write_text(
        "import os\n\n\ndef seed(a, b):\n    os.replace(a, b)\n", encoding="utf-8"
    )
    (package / "__init__.py").write_text("", encoding="utf-8")
    (package / "leaf.py").write_text("value = 1\n", encoding="utf-8")


def test_import_reaches_parent_package_initializer(tmp_path: Path) -> None:
    _deployment(tmp_path, "import pkg.sub.leaf\n")
    _package_with_writer_initializer(tmp_path)

    closure = derive_python_deployment_closure(tmp_path)

    assert "pkg/__init__.py" in closure.modules
    assert ("pkg/__init__.py", "seed", "ATOMIC_REPLACE") in _observe(tmp_path)


def test_container_module_launcher_reaches_parent_initializer(tmp_path: Path) -> None:
    """``python -m a.b`` runs ``a/__init__.py`` before the leaf."""

    _deployment(tmp_path, "value = 1\n")
    _package_with_writer_initializer(tmp_path)
    (tmp_path / ".docker").mkdir()
    (tmp_path / ".docker" / "entrypoint.sh").write_text("python -m pkg.sub.leaf\n", encoding="utf-8")
    (tmp_path / "Dockerfile").write_text(
        'COPY .docker/entrypoint.sh /entrypoint.sh\nENTRYPOINT ["/entrypoint.sh"]\n',
        encoding="utf-8",
    )

    closure = derive_python_deployment_closure(tmp_path)

    assert "pkg/__init__.py" in closure.modules
    assert ("pkg/__init__.py", "seed", "ATOMIC_REPLACE") in _observe(tmp_path)


def test_subprocess_module_dispatch_reaches_parent_initializer(tmp_path: Path) -> None:
    _deployment(
        tmp_path,
        "import subprocess\n\n\ndef run():\n    subprocess.run(['python3', '-m', 'pkg.sub.leaf'])\n",
    )
    _package_with_writer_initializer(tmp_path)

    closure = derive_python_deployment_closure(tmp_path)

    assert "pkg/__init__.py" in closure.modules
    assert ("pkg/__init__.py", "seed", "ATOMIC_REPLACE") in _observe(tmp_path)


def test_absent_leaf_is_not_satisfied_by_a_parent_initializer(tmp_path: Path) -> None:
    """A present parent chain with no leaf is not a resolved module."""

    _deployment(tmp_path, "import pkg.sub.absent\n")
    _package_with_writer_initializer(tmp_path)

    resolution = resolve_module_candidate(tmp_path.resolve(), "pkg.sub.absent")

    assert resolution.leaf is None
    assert resolution.parents
    assert resolve_module(tmp_path.resolve(), "pkg.sub.absent") is None


def test_unsafe_parent_initializer_is_reported(tmp_path: Path, tmp_path_factory: pytest.TempPathFactory) -> None:
    outside = tmp_path_factory.mktemp("outside_parent")
    (outside / "__init__.py").write_text("import os\n", encoding="utf-8")
    _deployment(tmp_path, "import pkg.leaf\n")
    (tmp_path / "pkg").mkdir()
    (tmp_path / "pkg" / "__init__.py").symlink_to(outside / "__init__.py")
    (tmp_path / "pkg" / "leaf.py").write_text("value = 1\n", encoding="utf-8")

    closure = derive_python_deployment_closure(tmp_path)

    assert ("tools/node.py", "package_initializer_escapes_root") in closure.observed_gaps


def test_python_resolves_a_package_before_a_same_named_module(tmp_path: Path) -> None:
    """D2: FileFinder executes the package when both package and module exist."""

    _deployment(tmp_path, "import competing\n")
    (tmp_path / "competing.py").write_text(
        "import os\n\n\ndef wrong(a, b):\n    os.replace(a, b)\n", encoding="utf-8"
    )
    package = tmp_path / "competing"
    package.mkdir()
    (package / "__init__.py").write_text(
        "from pathlib import Path\n\n\ndef selected():\n    Path('selected').touch()\n",
        encoding="utf-8",
    )

    closure = derive_python_deployment_closure(tmp_path)

    assert "competing/__init__.py" in closure.modules
    assert "competing.py" not in closure.modules
    assert ("competing/__init__.py", "selected", "NAMESPACE_CREATE") in _observe(tmp_path)


def test_package_module_execution_reaches_init_then_main(tmp_path: Path) -> None:
    """D2: ``python -m package`` executes both __init__ and __main__."""

    _deployment(
        tmp_path,
        "import subprocess\n\n\ndef run():\n    subprocess.run(['python3', '-m', 'pkg'])\n",
    )
    package = tmp_path / "pkg"
    package.mkdir()
    (package / "__init__.py").write_text(
        "from pathlib import Path\nPath('init.marker').touch()\n", encoding="utf-8"
    )
    (package / "__main__.py").write_text(
        "from pathlib import Path\nPath('main.marker').touch()\n", encoding="utf-8"
    )

    closure = derive_python_deployment_closure(tmp_path)
    observed = _observe(tmp_path)

    assert "pkg/__init__.py" in closure.modules
    assert "pkg/__main__.py" in closure.modules
    assert ("pkg/__init__.py", "<module>", "NAMESPACE_CREATE") in observed
    assert ("pkg/__main__.py", "<module>", "NAMESPACE_CREATE") in observed


# ---------------------------------------------------------------------------
# Descriptor and namespace operations
# ---------------------------------------------------------------------------


def test_writable_descriptor_open_and_handle_write_are_observed(tmp_path: Path) -> None:
    """The mounted wallet export uses exactly this shape."""

    _deployment(
        tmp_path,
        "import os\n\n\ndef export(path, payload):\n"
        "    fd = os.open(path, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600)\n"
        "    with os.fdopen(fd, 'wb') as handle:\n"
        "        handle.write(payload)\n",
    )

    kinds = [kind for _, _, kind in _observe(tmp_path)]

    assert "DESCRIPTOR_OPEN_WRITE" in kinds
    assert "HANDLE_WRITE" in kinds


@pytest.mark.parametrize(
    ("flags", "expected"),
    [
        ("os.O_RDONLY", None),
        ("os.O_RDONLY | os.O_CLOEXEC", None),
        ("0", None),
        ("os.O_WRONLY", "DESCRIPTOR_OPEN_WRITE"),
        ("os.O_WRONLY | os.O_CREAT | os.O_EXCL", "DESCRIPTOR_OPEN_WRITE"),
        ("os.O_RDONLY | os.O_WRONLY", "DESCRIPTOR_OPEN_WRITE"),
        # A flag expression the closed grammar cannot parse may request write.
        ("os.O_RDONLY | dynamic_flags", "DESCRIPTOR_OPEN_UNKNOWN"),
        ("dynamic_flags", "DESCRIPTOR_OPEN_UNKNOWN"),
        ("1", "DESCRIPTOR_OPEN_UNKNOWN"),
        ("compute()", "DESCRIPTOR_OPEN_UNKNOWN"),
        ("os.O_RDONLY & os.O_CLOEXEC", "DESCRIPTOR_OPEN_UNKNOWN"),
        ("os.O_RDONLY | 1", "DESCRIPTOR_OPEN_UNKNOWN"),
    ],
)
def test_descriptor_open_flag_grammar(tmp_path: Path, flags: str, expected: str | None) -> None:
    """Only a closed OR of known flags or exact zero may read as non-writing."""

    _deployment(
        tmp_path,
        "import os\n\n\ndef compute():\n    return 0\n\n\n"
        f"def go(path, dynamic_flags):\n    return os.open(path, {flags})\n",
    )

    assert [kind for _, _, kind in _observe(tmp_path)] == ([expected] if expected else [])


@pytest.mark.parametrize(
    ("body", "expected"),
    [
        # A flag name must be proved to come from os, never merely spelled O_*.
        ("import os\n\n\ndef go(p, fake):\n    os.open(p, fake.O_RDONLY)\n", "DESCRIPTOR_OPEN_UNKNOWN"),
        ("import os\n\n\ndef go(p):\n    os.open(p, os.O_RDONLY)\n", None),
        (
            "import os\nfrom os import O_RDONLY\n\n\ndef go(p):\n    os.open(p, O_RDONLY)\n",
            None,
        ),
        # A rebound flag name no longer proves anything about its value.
        (
            "import os\nfrom os import O_RDONLY\n\nO_RDONLY = 1\n\n\ndef go(p):\n    os.open(p, O_RDONLY)\n",
            "DESCRIPTOR_OPEN_UNKNOWN",
        ),
    ],
)
def test_descriptor_open_flag_provenance(tmp_path: Path, body: str, expected: str | None) -> None:
    _deployment(tmp_path, body)

    assert [kind for _, _, kind in _observe(tmp_path)] == ([expected] if expected else [])


@pytest.mark.parametrize(
    ("body", "expected"),
    [
        ("import os\n\nop = os.replace\nop2 = op\n\n\ndef go(a, b):\n    op2(a, b)\n", "ATOMIC_REPLACE"),
        (
            "import os\n\nop = os.replace\nop2 = op\nop3 = op2\n\n\ndef go(a, b):\n    op3(a, b)\n",
            "ATOMIC_REPLACE",
        ),
        ("from os import replace as r\n\nr2 = r\n\n\ndef go(a, b):\n    r2(a, b)\n", "ATOMIC_REPLACE"),
        # Two different operations behind one name is unresolved, not a guess.
        (
            "import os\n\nop = os.replace\nop = os.remove\n\n\ndef go(a, b):\n    op(a, b)\n",
            "ALIAS_TARGET_UNKNOWN",
        ),
    ],
)
def test_transitive_alias_chains_are_resolved(tmp_path: Path, body: str, expected: str) -> None:
    _deployment(tmp_path, body)

    assert [kind for _, _, kind in _observe(tmp_path)] == [expected]


@pytest.mark.parametrize("hops", [1, 2, 8, 9, 20])
def test_reverse_ordered_alias_chain_resolves_at_any_length(tmp_path: Path, hops: int) -> None:
    """Source order must not bound how far a tracked operation propagates."""

    lines = ["import os"]
    lines.extend(f"op{index} = op{index - 1}" for index in range(hops, 1, -1))
    lines.append("op1 = os.replace")
    body = "\n".join(lines) + f"\n\n\ndef go(a, b):\n    op{hops}(a, b)\n"
    _deployment(tmp_path, body)

    assert [kind for _, _, kind in _observe(tmp_path)] == ["ATOMIC_REPLACE"]


@pytest.mark.parametrize(
    ("body", "expected"),
    [
        # A parameter is a lexical binder: the name is not the imported module.
        ("import os\n\n\ndef go(os, p):\n    os.open(p, os.O_RDONLY)\n", "ALIAS_TARGET_UNKNOWN"),
        (
            "from os import replace\n\n\ndef go(replace, a, b):\n    replace(a, b)\n",
            "ALIAS_TARGET_UNKNOWN",
        ),
        (
            "import os\nfrom os import O_RDONLY\n\n\ndef go(O_RDONLY, p):\n    os.open(p, O_RDONLY)\n",
            "DESCRIPTOR_OPEN_UNKNOWN",
        ),
        (
            "import os\n\n\ndef go(items, p):\n    for os in items:\n        os.replace(p, p)\n",
            "ALIAS_TARGET_UNKNOWN",
        ),
        (
            "import os\n\n\ndef go(p):\n    with make(p) as os:\n        os.replace(p, p)\n",
            "ALIAS_TARGET_UNKNOWN",
        ),
        (
            "import os\n\n\ndef go(p):\n    try:\n        run()\n    except Error as os:\n        os.replace(p, p)\n",
            "ALIAS_TARGET_UNKNOWN",
        ),
        ("import os\n\nshim = lambda os: os.replace(1, 2)\n", "ALIAS_TARGET_UNKNOWN"),
        (
            "import os\n\n\ndef go(rows, p):\n    return [os.replace(p, p) for os in rows]\n",
            "ALIAS_TARGET_UNKNOWN",
        ),
        # Two imports binding one name leave the origin unproved.
        (
            "import os\nimport shutil as os\n\n\ndef go(a, b):\n    os.replace(a, b)\n",
            "ALIAS_TARGET_UNKNOWN",
        ),
    ],
)
def test_lexical_shadowing_keeps_calls_observable(tmp_path: Path, body: str, expected: str) -> None:
    """Coarse uncertainty is acceptable; silence is not."""

    _deployment(tmp_path, body)

    assert [kind for _, _, kind in _observe(tmp_path)] == [expected]


@pytest.mark.parametrize(
    ("body", "expected"),
    [
        (
            "import os\n\n\ndef go(v, a, b):\n    match v:\n        case os:\n            os.replace(a, b)\n",
            "ALIAS_TARGET_UNKNOWN",
        ),
        (
            "import os\n\n\ndef go(v, a, b):\n    match v:\n        case [*os]:\n            os.replace(a, b)\n",
            "ALIAS_TARGET_UNKNOWN",
        ),
        (
            'import os\n\n\ndef go(v, a, b):\n    match v:\n        case {"k": 1, **os}:\n            os.replace(a, b)\n',
            "ALIAS_TARGET_UNKNOWN",
        ),
        (
            "import os\nfrom os import O_RDONLY\n\n\ndef go(v, p):\n    match v:\n"
            "        case O_RDONLY:\n            os.open(p, O_RDONLY)\n",
            "DESCRIPTOR_OPEN_UNKNOWN",
        ),
    ],
)
def test_structural_pattern_captures_shadow_imports(tmp_path: Path, body: str, expected: str) -> None:
    """A match capture binds its name and may shadow a proved import."""

    _deployment(tmp_path, body)

    assert [kind for _, _, kind in _observe(tmp_path)] == [expected]


@pytest.mark.parametrize(
    ("body", "expected"),
    [
        ("import os\nfrom shim import *\n\n\ndef go(a, b):\n    os.replace(a, b)\n", "ALIAS_TARGET_UNKNOWN"),
        (
            "import os\nfrom shim import *\nfrom os import O_RDONLY\n\n\ndef go(p):\n    os.open(p, O_RDONLY)\n",
            "ALIAS_TARGET_UNKNOWN",
        ),
        (
            "from os import replace\nfrom shim import *\n\n\ndef go(a, b):\n    replace(a, b)\n",
            "ALIAS_TARGET_UNKNOWN",
        ),
        (
            "import os\nfrom shim import *\n\nop = os.replace\n\n\ndef go(a, b):\n    op(a, b)\n",
            "ALIAS_TARGET_UNKNOWN",
        ),
        (
            "import os\nfrom shim import *\n\nop = os.replace\nop2 = op\n\n\ndef go(a, b):\n    op2(a, b)\n",
            "ALIAS_TARGET_UNKNOWN",
        ),
        (
            "import os\nfrom shim import *\n\nop = os.replace\nop2 = op\nop3 = op2\n\n\ndef go(a, b):\n    op3(a, b)\n",
            "ALIAS_TARGET_UNKNOWN",
        ),
        (
            "import os\n\nos = shim\nop = os.replace\nop2 = op\n\n\ndef go(a, b):\n    op2(a, b)\n",
            "ALIAS_TARGET_UNKNOWN",
        ),
        (
            "import os\nfrom shim import *\n\nop = os.replace\na = op\nb = a\na = b\n\n\ndef go(x, y):\n    b(x, y)\n",
            "ALIAS_TARGET_UNKNOWN",
        ),
    ],
)
def test_wildcard_import_makes_tracked_aliases_unproved(tmp_path: Path, body: str, expected: str) -> None:
    """``from module import *`` may rebind any tracked module, operation, or flag."""

    _deployment(tmp_path, body)

    assert [kind for _, _, kind in _observe(tmp_path)] == [expected]


def test_unshadowed_module_alias_still_resolves_precisely(tmp_path: Path) -> None:
    """Control: conservative shadowing must not blunt the ordinary case."""

    _deployment(tmp_path, "import os\n\n\ndef go(a, b):\n    os.replace(a, b)\n")

    assert [kind for _, _, kind in _observe(tmp_path)] == ["ATOMIC_REPLACE"]


def test_unshadowed_transitive_alias_still_resolves_precisely(tmp_path: Path) -> None:
    """Control: unknown propagation must not swallow a proved alias chain."""

    _deployment(tmp_path, "import os\n\nop = os.replace\nop2 = op\n\n\ndef go(a, b):\n    op2(a, b)\n")

    assert [kind for _, _, kind in _observe(tmp_path)] == ["ATOMIC_REPLACE"]


def test_rebound_tracked_module_call_stays_observable(tmp_path: Path) -> None:
    """A reassigned ``os`` cannot make ``os.replace`` disappear."""

    _deployment(tmp_path, "import os\n\nos = shim\n\n\ndef go(a, b):\n    os.replace(a, b)\n")

    assert [kind for _, _, kind in _observe(tmp_path)] == ["ALIAS_TARGET_UNKNOWN"]


def test_rebound_module_with_untracked_attribute_is_not_invented(tmp_path: Path) -> None:
    """Generic unknown dispatch stays an explicit nonclaim, not a false sink."""

    _deployment(tmp_path, "import os\n\nos = shim\n\n\ndef go(a, b):\n    os.nonsense(a, b)\n")

    assert _observe(tmp_path) == []


def test_alias_cycle_terminates_without_binding(tmp_path: Path) -> None:
    """A cycle with no operation seed must terminate and bind nothing."""

    _deployment(tmp_path, "a = b\nb = a\n\n\ndef go(x, y):\n    a(x, y)\n")

    assert _observe(tmp_path) == []


def test_seeded_alias_cycle_still_resolves(tmp_path: Path) -> None:
    _deployment(
        tmp_path,
        "import os\n\nop = os.replace\na = op\nb = a\na = b\n\n\ndef go(x, y):\n    b(x, y)\n",
    )

    assert "ATOMIC_REPLACE" in [kind for _, _, kind in _observe(tmp_path)]


def test_nonconsumer_adjudicated_row_survives_regeneration_round_trip(tmp_path: Path) -> None:
    """An unchanged source-bound nonconsumer judgement survives regeneration."""

    source = "from pathlib import Path\n\nPath('profile.json').write_text('profile')\n"
    _deployment(tmp_path, source)
    emitted = render_manifest_v2(tmp_path)
    entry = dict(emitted["entries"][0])
    entry.update(
        {
            "classification": "DURABLE_VALUE_STATE",
            "mediation_status": "UNMEDIATED_DEPLOYED_WRITER",
            "rationale": "reviewed",
        }
    )
    _manifest(tmp_path, [entry], gaps=list(emitted["closure_gaps"]))

    regenerated = render_manifest_v2(tmp_path)
    regenerated_entry = regenerated["entries"][0]

    assert json.loads(json.dumps(regenerated_entry))["consumers"] == []
    assert regenerated_entry["classification"] == "DURABLE_VALUE_STATE"


@pytest.mark.parametrize(
    ("body", "expected"),
    [
        (
            "from os import open as fd_open\nimport os\n\n\ndef go(p):\n    fd_open(p, os.O_WRONLY)\n",
            "DESCRIPTOR_OPEN_WRITE",
        ),
        (
            "from os import open as fd_open\n\n\ndef go(p):\n    fd_open(p, 577)\n",
            "DESCRIPTOR_OPEN_UNKNOWN",
        ),
        (
            "from os import fdopen as wrap\n\n\ndef go(fd):\n    wrap(fd, 'wb')\n",
            "DESCRIPTOR_OPEN_WRITE",
        ),
        (
            "from os import fdopen as wrap\n\n\ndef go(fd, mode):\n    wrap(fd, mode)\n",
            "OPEN_MODE_UNKNOWN",
        ),
        (
            "import os\n\nop = os.replace\n\n\ndef go(a, b):\n    op(a, b)\n",
            "ATOMIC_REPLACE",
        ),
        (
            "import os\n\nop = os.open\n\n\ndef go(p):\n    op(p, os.O_WRONLY)\n",
            "DESCRIPTOR_OPEN_WRITE",
        ),
        (
            "import os\n\nop = os.rmdir\n\n\ndef go(p):\n    op(p)\n",
            "UNLINK",
        ),
    ],
)
def test_direct_and_reassignment_aliases_keep_their_classification(
    tmp_path: Path, body: str, expected: str
) -> None:
    """A rebound operation must not lose its argument-dependent classification."""

    _deployment(tmp_path, body)

    assert [kind for _, _, kind in _observe(tmp_path)] == [expected]


@pytest.mark.parametrize(
    ("call", "expected"),
    [
        ("p.unlink()", "UNLINK"),
        ("p.mkdir()", "NAMESPACE_CREATE"),
        ("p.touch()", "NAMESPACE_CREATE"),
        ("p.rmdir()", "UNLINK"),
        ("p.symlink_to(q)", "NAMESPACE_LINK"),
        ("p.hardlink_to(q)", "NAMESPACE_LINK"),
    ],
)
def test_path_namespace_mutations_are_observed(tmp_path: Path, call: str, expected: str) -> None:
    _deployment(tmp_path, f"def go(p, q):\n    {call}\n")

    assert [kind for _, _, kind in _observe(tmp_path)] == [expected]


@pytest.mark.parametrize(
    ("method", "expected"),
    [("rename", "RENAME"), ("replace", "PATH_REPLACE"), ("hardlink_to", "NAMESPACE_LINK")],
)
def test_two_role_path_mutations_accept_keyword_target(
    tmp_path: Path, method: str, expected: str
) -> None:
    """Valid pathlib keyword calls retain both source and destination roles."""

    _deployment(
        tmp_path,
        "from pathlib import Path\n\n\ndef publish():\n"
        f"    Path('source').{method}(target='destination')\n",
    )

    observations = _observations(tmp_path)

    assert [item.sink_kind for item in observations] == [expected]
    assert observations[0].destination == "LITERAL:source+LITERAL:destination"
    assert observations[0].destination_resolved is True


@pytest.mark.parametrize(
    ("body", "expected"),
    [
        ("import os\n\n\ndef go():\n    os.makedirs('state')\n", "NAMESPACE_CREATE"),
        ("from os import mkdir as create\n\n\ndef go():\n    create(path='state')\n", "NAMESPACE_CREATE"),
        (
            "from pathlib import Path\n\n\ndef go():\n    Path('state').chmod(0o700)\n",
            "PERMISSION_MUTATE",
        ),
        (
            "from pathlib import Path\n\n\ndef go():\n    destination = Path('state')\n"
            "    destination.chmod(0o700)\n",
            "PERMISSION_MUTATE",
        ),
    ],
)
def test_mounted_namespace_and_permission_writers_are_observed(
    tmp_path: Path, body: str, expected: str
) -> None:
    """D1: mounted namespace and permission writers cannot disappear by spelling."""

    _deployment(tmp_path, body)

    assert [kind for _, _, kind in _observe(tmp_path)] == [expected]


@pytest.mark.parametrize(
    "body",
    [
        (
            "import os\n\nHANDLERS = {'commit': os.replace}\n\n\ndef go(a, b):\n"
            "    HANDLERS['commit'](a, b)\n"
        ),
        "import os\n\n\ndef go(name, a, b):\n    getattr(os, name)(a, b)\n",
        (
            "import os\n\n\ndef register(callback):\n    return callback\n\n"
            "WRITER = register(os.replace)\n"
        ),
    ],
)
def test_unresolved_writer_provenance_is_a_typed_gap(tmp_path: Path, body: str) -> None:
    """D1: a tracked writer escaping precise alias analysis widens the gap set."""

    _deployment(tmp_path, body)

    closure = derive_python_deployment_closure(tmp_path)

    assert ("tools/node.py", "unresolved_writer_provenance") in closure.observed_gaps


def test_precise_transitive_writer_alias_does_not_invent_a_provenance_gap(tmp_path: Path) -> None:
    _deployment(
        tmp_path,
        "import os\n\nwriter = os.replace\ncommit = writer\n\n\ndef go(a, b):\n    commit(a, b)\n",
    )

    closure = derive_python_deployment_closure(tmp_path)

    assert ("tools/node.py", "unresolved_writer_provenance") not in closure.observed_gaps
    assert ("tools/node.py", "go", "ATOMIC_REPLACE") in _observe(tmp_path)


@pytest.mark.parametrize(
    ("body", "destination"),
    [
        (
            "import os\n\n\ndef go():\n    os.replace(src='staging.tmp', dst='state.json')\n",
            "LITERAL:staging.tmp+LITERAL:state.json",
        ),
        (
            "import os\n\n\ndef go():\n    os.replace('staging.tmp', dst='state.json')\n",
            "LITERAL:staging.tmp+LITERAL:state.json",
        ),
        (
            "from os import replace as commit\n\n\ndef go():\n"
            "    commit(src='staging.tmp', dst='state.json')\n",
            "LITERAL:staging.tmp+LITERAL:state.json",
        ),
        (
            "from pathlib import Path\n\n\ndef go():\n    destination = Path('state.json')\n"
            "    destination.write_text('value')\n",
            "LITERAL:state.json",
        ),
    ],
)
def test_destination_provenance_binds_positional_keyword_and_simple_aliases(
    tmp_path: Path, body: str, destination: str
) -> None:
    """D4: equivalent call spellings bind the same complete destination."""

    _deployment(tmp_path, body)

    observations = _observations(tmp_path)

    assert len(observations) == 1
    assert observations[0].destination == destination
    assert observations[0].destination_resolved is True


@pytest.mark.parametrize(
    "body",
    [
        pytest.param(
            "from pathlib import Path\n\n\ndef seed():\n    destination = Path('state.json')\n"
            "\n\ndef go(destination):\n    destination.write_text('value')\n",
            id="cross-function-same-name",
        ),
        pytest.param(
            "from pathlib import Path\n\ndestination = Path('state.json')\n\n"
            "def go(destination):\n    destination.write_text('value')\n",
            id="parameter-shadowing",
        ),
        pytest.param(
            "from pathlib import Path\n\n\nclass Seed:\n    destination = Path('state.json')\n"
            "\n\ndef go():\n    destination.write_text('value')\n",
            id="cross-class-same-name",
        ),
        pytest.param(
            "from pathlib import Path\n\n\ndef go(enabled):\n    if enabled:\n"
            "        destination = Path('state.json')\n    destination.write_text('value')\n",
            id="conditional-assignment",
        ),
        pytest.param(
            "from pathlib import Path\n\n\ndef go():\n    for _ in range(1):\n"
            "        destination = Path('state.json')\n    destination.write_text('value')\n",
            id="loop-assignment",
        ),
        pytest.param(
            "from pathlib import Path\n\n\ndef go():\n    destination.write_text('value')\n"
            "    destination = Path('state.json')\n",
            id="read-before-assignment",
        ),
    ],
)
def test_path_alias_requires_same_scope_prior_definite_single_assignment(
    tmp_path: Path, body: str
) -> None:
    """Use-site provenance cannot borrow a same-named assignment elsewhere."""

    _deployment(tmp_path, body)

    observation = _observations(tmp_path)[0]

    assert observation.destination_resolved is False
    assert observation.destination != "LITERAL:state.json"


def test_path_alias_accepts_prior_straight_line_same_scope_assignment(tmp_path: Path) -> None:
    _deployment(
        tmp_path,
        "from pathlib import Path\n\n\ndef go():\n    destination = Path('state.json')\n"
        "    destination.write_text('value')\n",
    )

    observation = _observations(tmp_path)[0]

    assert observation.destination == "LITERAL:state.json"
    assert observation.destination_resolved is True


@pytest.mark.parametrize(
    "body",
    [
        pytest.param(
            "def Path(value):\n    return runtime_path\n\np = Path('state.json')\n"
            "p.write_text('value')\n",
            id="custom-Path-function",
        ),
        pytest.param(
            "import attacker as a\n\np = a.Path('state.json')\np.write_text('value')\n",
            id="attacker-module-Path-attribute",
        ),
    ],
)
def test_path_constructor_name_requires_exact_pathlib_provenance(
    tmp_path: Path, body: str
) -> None:
    _deployment(tmp_path, body, extra={"attacker.py": "class Path:\n    pass\n"})

    observation = _observations(tmp_path)[0]

    assert observation.destination_resolved is False
    assert observation.destination != "LITERAL:state.json"


def test_pathlib_module_constructor_is_positive_provenance(tmp_path: Path) -> None:
    _deployment(
        tmp_path,
        "import pathlib\n\np = pathlib.Path('state.json')\np.write_text('value')\n",
    )

    observation = _observations(tmp_path)[0]

    assert observation.destination == "LITERAL:state.json"
    assert observation.destination_resolved is True


def test_consumer_reader_uses_the_same_use_site_alias_provenance(tmp_path: Path) -> None:
    artifact = "authority.json"
    reader_path = "tools/node.py"
    source = (
        "from pathlib import Path\n\nPath('authority.json').write_text('value')\n"
        "\n\ndef seed():\n    artifact = Path('authority.json')\n"
        "\n\ndef load(artifact):\n    return artifact.read_text()\n"
    )
    _deployment(tmp_path, source)
    emitted = render_manifest_v2(tmp_path)
    entry = dict(
        next(item for item in emitted["entries"] if item["path"] == "tools/node.py")
    )
    entry.update(
        {
            "classification": "AUTHORITY_CONTROL_STATE",
            "mediation_status": "UNMEDIATED_DEPLOYED_WRITER",
            "rationale": "hostile cross-scope reader claim",
            "consumers": [
                _consumer(
                    artifact=artifact,
                    reader_fingerprint=_reader_fingerprint(reader_path, artifact, source),
                    reference=reader_path,
                    source_path=reader_path,
                    source_sha256=hashlib.sha256(source.encode("utf-8")).hexdigest(),
                )
            ],
        }
    )
    _manifest(tmp_path, [entry], gaps=list(emitted["closure_gaps"]))

    report = check_m6_value_sinks_v2(tmp_path)
    regenerated = render_manifest_v2(tmp_path)
    refreshed = next(
        item for item in regenerated["entries"] if item["path"] == "tools/node.py"
    )

    assert any(
        item["rule_id"] == "consumer_reader_fingerprint_mismatch"
        for item in report["findings"]
    )
    assert refreshed["classification"] == UNADJUDICATED


def test_reassigned_path_alias_is_unresolved_and_non_adjudicable(tmp_path: Path) -> None:
    _deployment(
        tmp_path,
        "from pathlib import Path\n\n\ndef go(runtime_path):\n    destination = Path('state.json')\n"
        "    destination = runtime_path\n    destination.write_text('value')\n",
    )
    first = render_manifest_v2(tmp_path)
    entry = dict(first["entries"][0])
    entry.update(
        {
            "classification": "DURABLE_VALUE_STATE",
            "mediation_status": "UNMEDIATED_DEPLOYED_WRITER",
            "rationale": "hostile prior adjudication",
        }
    )
    gaps = list(first["closure_gaps"])
    _manifest(tmp_path, [entry], gaps=gaps)

    report = check_m6_value_sinks_v2(tmp_path)
    regenerated = render_manifest_v2(tmp_path)

    assert any(item["rule_id"] == "unresolved_destination_adjudication" for item in report["findings"])
    assert regenerated["entries"][0]["classification"] == UNADJUDICATED
    assert regenerated["entries"][0]["mediation_status"] == UNADJUDICATED


# ---------------------------------------------------------------------------
# Provenance binds both path roles and never trusts a local call graph
# ---------------------------------------------------------------------------


def _single_observation(root: Path) -> ValueSinkObservationV2:
    closure = derive_python_deployment_closure(root)
    observations = scan_closure(root, closure)
    return observations[0]


def test_source_operand_change_changes_the_fingerprint(
    tmp_path: Path, tmp_path_factory: pytest.TempPathFactory
) -> None:
    """A rename moves two path roles, so the source is bound as well."""

    second = tmp_path_factory.mktemp("second_source")
    _deployment(tmp_path, "import os\n\n\ndef go():\n    os.replace('report.tmp', 'live.json')\n")
    _deployment(second, "import os\n\n\ndef go():\n    os.replace('balances.tmp', 'live.json')\n")

    first_observation = _single_observation(tmp_path)
    second_observation = _single_observation(second)

    assert first_observation.identity() == second_observation.identity()
    assert first_observation.fingerprint != second_observation.fingerprint


def test_caller_literal_change_changes_the_fingerprint(
    tmp_path: Path, tmp_path_factory: pytest.TempPathFactory
) -> None:
    """The helper body is identical; only the caller's destination differs."""

    second = tmp_path_factory.mktemp("second_caller")
    body = (
        "import os\n\n\n"
        "def persist(destination):\n    os.replace('staging.tmp', destination)\n\n\n"
        "def emit():\n    persist({!r})\n"
    )
    _deployment(tmp_path, body.format("report.json"))
    _deployment(second, body.format("balances.json"))

    first_observation = _single_observation(tmp_path)
    second_observation = _single_observation(second)

    assert first_observation.identity() == second_observation.identity()
    assert first_observation.fingerprint != second_observation.fingerprint


def test_local_literal_callers_do_not_resolve_the_caller_set(tmp_path: Path) -> None:
    """External, attribute, alias, and dynamic callers stay outside this scan."""

    _deployment(
        tmp_path,
        "import os\n\n\n"
        "def persist(destination):\n    os.replace('staging.tmp', destination)\n\n\n"
        "def emit():\n    persist('report.json')\n",
    )

    closure = derive_python_deployment_closure(tmp_path)
    observation = scan_closure(tmp_path, closure)[0]

    assert observation.caller_determined is True
    assert "CALLER_SET:UNRESOLVED" in observation.destination
    assert ("tools/node.py", "dynamic_destination") in dynamic_destination_gaps((observation,))


def test_ambiguous_function_name_does_not_bind_callers(tmp_path: Path) -> None:
    """A method sharing a helper's bare name must not supply its literals."""

    _deployment(
        tmp_path,
        "import os\n\n\n"
        "def persist(destination):\n    os.replace('staging.tmp', destination)\n\n\n"
        "class Other:\n    def persist(self, destination):\n        return destination\n\n\n"
        "def emit():\n    persist('report.json')\n",
    )

    closure = derive_python_deployment_closure(tmp_path)
    observation = next(item for item in scan_closure(tmp_path, closure) if item.symbol == "persist")

    assert "LOCAL_CALLERS:NONE" in observation.destination
    assert observation.caller_determined is True


# ---------------------------------------------------------------------------
# Observation phase must read the exact bytes the closure recorded
# ---------------------------------------------------------------------------


def test_source_mutation_between_phases_is_rejected(tmp_path: Path) -> None:
    _deployment(tmp_path, "import os\n\n\ndef go(a, b):\n    os.replace(a, b)\n")
    closure = derive_python_deployment_closure(tmp_path)

    (tmp_path / "tools" / "node.py").write_text(
        "import os\n\n\ndef go(a, b):\n    os.replace(b, a)\n", encoding="utf-8"
    )

    with pytest.raises(ValueError, match="source changed between closure and scan"):
        scan_closure(tmp_path, closure)


def test_symlink_swap_between_phases_is_rejected(
    tmp_path: Path, tmp_path_factory: pytest.TempPathFactory
) -> None:
    outside = tmp_path_factory.mktemp("swap_target")
    (outside / "evil.py").write_text("import os\n\n\ndef go(a, b):\n    os.replace(b, a)\n", encoding="utf-8")
    _deployment(tmp_path, "import os\n\n\ndef go(a, b):\n    os.replace(a, b)\n")
    closure = derive_python_deployment_closure(tmp_path)

    target = tmp_path / "tools" / "node.py"
    target.unlink()
    target.symlink_to(outside / "evil.py")

    with pytest.raises(ValueError, match="cannot scan tools/node.py"):
        scan_closure(tmp_path, closure)


def test_oversize_growth_between_phases_is_rejected(tmp_path: Path) -> None:
    _deployment(tmp_path, "import os\n\n\ndef go(a, b):\n    os.replace(a, b)\n")
    closure = derive_python_deployment_closure(tmp_path)

    (tmp_path / "tools" / "node.py").write_text("x = '" + "a" * (4 * 1024 * 1024 + 8) + "'\n", encoding="utf-8")

    with pytest.raises(ValueError, match="exceeds .* bytes"):
        scan_closure(tmp_path, closure)


# ---------------------------------------------------------------------------
# Unadjudicated rows are explicit, blocking, and never auto-promoted
# ---------------------------------------------------------------------------


def test_unadjudicated_row_loads_and_blocks(tmp_path: Path) -> None:
    _deployment(tmp_path, "import os\n\n\ndef publish(a, b):\n    os.replace(a, b)\n")
    emitted = render_manifest_v2(tmp_path)
    _manifest(tmp_path, list(emitted["entries"]))

    report = check_m6_value_sinks_v2(tmp_path)

    assert report["manifest_identity_count"] == 1
    assert report["adjudicated_identity_count"] == 0
    assert report["unadjudicated_sinks"]
    assert "unadjudicated_sinks" in gate_blockers(report)


def test_unadjudicated_row_requires_null_release_binding(tmp_path: Path) -> None:
    path = _manifest(
        tmp_path,
        [_entry(classification=UNADJUDICATED, mediation_status=UNADJUDICATED, release_binding="release-1")],
    )

    with pytest.raises(ValueError, match="must remain null"):
        load_value_sink_manifest(path)


def test_regeneration_never_promotes_an_unadjudicated_row(tmp_path: Path) -> None:
    """Repeated regeneration must not turn an unknown row into a judgement."""

    _deployment(tmp_path, "import os\n\n\ndef publish(a, b):\n    os.replace(a, b)\n")
    first = render_manifest_v2(tmp_path)
    _manifest(tmp_path, list(first["entries"]))

    second = render_manifest_v2(tmp_path)

    assert second["entries"][0]["classification"] == UNADJUDICATED
    assert second["entries"][0]["mediation_status"] == UNADJUDICATED
    assert second["entries"][0]["release_binding"] is None


def test_classifying_every_sink_advisory_cannot_reach_ready_or_exit_zero(
    tmp_path: Path, capsys: pytest.CaptureFixture[str]
) -> None:
    """No manifest content may promote a research inventory."""

    _deployment(tmp_path, "import os\n\n\ndef publish(a, b):\n    os.replace(a, b)\n")
    emitted = render_manifest_v2(tmp_path)
    entry = dict(emitted["entries"][0])
    entry.update(
        {
            "classification": "ADVISORY_CONTROL_STATE",
            "mediation_status": "NON_VALUE_EFFECT",
            "rationale": "reviewed",
        }
    )
    _manifest(tmp_path, [entry])

    report = check_m6_value_sinks_v2(tmp_path)
    exit_code = main(["--root", str(tmp_path)])
    capsys.readouterr()

    assert report["release_ready"] is False
    assert report["production_authority"] is False
    assert report["vm01_status"] == "OPEN"
    assert exit_code == 1
    assert "release_gaps" in gate_blockers(report)


def test_declared_gap_alone_causes_default_nonzero(tmp_path: Path, capsys: pytest.CaptureFixture[str]) -> None:
    _deployment(
        tmp_path,
        "import importlib\nfrom pathlib import Path\n\n\ndef run(name):\n"
        "    Path('state').touch()\n    return importlib.import_module(name)\n",
    )
    _manifest(
        tmp_path,
        [_entry(classification=UNADJUDICATED, mediation_status=UNADJUDICATED)],
        gaps=[
            {
                "mechanism": "import_module",
                "path": "tools/node.py",
                "rationale": "declared dynamic import",
            }
        ],
    )

    exit_code = main(["--root", str(tmp_path)])
    capsys.readouterr()

    assert exit_code == 1


def test_emit_manifest_refuses_while_gaps_exist(tmp_path: Path, capsys: pytest.CaptureFixture[str]) -> None:
    _deployment(
        tmp_path,
        "import importlib\nfrom pathlib import Path\n\n\ndef run(name):\n"
        "    Path('state').touch()\n    return importlib.import_module(name)\n",
    )

    exit_code = main(["--root", str(tmp_path), "--emit-manifest"])

    assert exit_code == 1
    assert "research-emission" in capsys.readouterr().out


def test_research_emission_still_exits_nonzero(tmp_path: Path, capsys: pytest.CaptureFixture[str]) -> None:
    _deployment(
        tmp_path,
        "import importlib\nfrom pathlib import Path\n\n\ndef run(name):\n"
        "    Path('state').touch()\n    return importlib.import_module(name)\n",
    )

    exit_code = main(["--root", str(tmp_path), "--emit-manifest", "--research-emission"])

    assert exit_code == 1
    assert json.loads(capsys.readouterr().out)["schema"] == "zenodex/m6-value-sink-inventory/v2"


def test_dynamic_destination_in_rendered_manifest_forces_emit_nonzero(
    tmp_path: Path, capsys: pytest.CaptureFixture[str]
) -> None:
    """D9: a gap discovered during rendering cannot inherit a pre-render green exit."""

    _deployment(
        tmp_path,
        "from pathlib import Path\n\n\ndef publish(destination):\n"
        "    Path(destination).write_text('value')\n",
    )

    exit_code = main(
        ["--root", str(tmp_path), "--emit-manifest", "--research-emission"]
    )
    emitted = json.loads(capsys.readouterr().out)

    assert exit_code == 1
    assert "dynamic_destination" in {
        item["mechanism"] for item in emitted["closure_gaps"]
    }


def test_emit_renders_once_then_rejects_invalid_production_decode(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[str]
) -> None:
    """D9: emitted bytes pass the same strict decoder used by the report."""

    calls = 0

    def invalid_render(root: Path) -> RenderedManifestV2:
        nonlocal calls
        calls += 1
        return {
            "closure_gaps": [],
            "entries": [],
            "schema": "zenodex/m6-value-sink-inventory/v2",
            "scope": "invalid empty inventory",
        }

    monkeypatch.setattr(checker_module, "render_manifest_v2", invalid_render)

    exit_code = checker_module.main(
        ["--root", str(tmp_path), "--emit-manifest", "--research-emission"]
    )
    output = json.loads(capsys.readouterr().out)

    assert calls == 1
    assert exit_code == 1
    assert output["error"] == "rendered manifest failed production decoding"


def test_emit_derives_the_subject_only_once(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[str]
) -> None:
    _deployment(tmp_path, "from pathlib import Path\nPath('state').touch()\n")
    original = checker_module.derive_python_deployment_closure
    calls = 0

    def counted(root: Path) -> DeploymentClosureV2:
        nonlocal calls
        calls += 1
        return original(root)

    monkeypatch.setattr(checker_module, "derive_python_deployment_closure", counted)

    exit_code = checker_module.main(
        ["--root", str(tmp_path), "--emit-manifest", "--research-emission"]
    )
    capsys.readouterr()

    assert exit_code == 1
    assert calls == 1


# ---------------------------------------------------------------------------
# Container shell body needs a whole-line grammar
# ---------------------------------------------------------------------------


def test_trailing_command_in_container_body_is_a_gap(tmp_path: Path) -> None:
    """``python good.py; sh evil.sh`` contains a modelled target and a second command."""

    _deployment(tmp_path, "value = 1\n")
    (tmp_path / ".docker").mkdir()
    (tmp_path / ".docker" / "entrypoint.sh").write_text(
        "python tools/node.py; sh evil-writer.sh\n", encoding="utf-8"
    )
    (tmp_path / "Dockerfile").write_text(
        'COPY .docker/entrypoint.sh /entrypoint.sh\nENTRYPOINT ["/entrypoint.sh"]\n',
        encoding="utf-8",
    )

    closure = derive_python_deployment_closure(tmp_path)

    assert (".docker/entrypoint.sh", "unmodelled_container_shell_body") in closure.observed_gaps


def test_clean_container_body_creates_no_body_gap(tmp_path: Path) -> None:
    _deployment(tmp_path, "value = 1\n")
    (tmp_path / ".docker").mkdir()
    (tmp_path / ".docker" / "entrypoint.sh").write_text("python tools/node.py &\n", encoding="utf-8")
    (tmp_path / "Dockerfile").write_text(
        'COPY .docker/entrypoint.sh /entrypoint.sh\nENTRYPOINT ["/entrypoint.sh"]\n',
        encoding="utf-8",
    )

    closure = derive_python_deployment_closure(tmp_path)

    assert not [gap for gap in closure.observed_gaps if gap[1] == "unmodelled_container_shell_body"]


def test_generic_interpreter_entrypoint_is_a_gap(tmp_path: Path) -> None:
    _deployment(tmp_path, "value = 1\n")
    (tmp_path / "Dockerfile").write_text('ENTRYPOINT ["python"]\n', encoding="utf-8")

    closure = derive_python_deployment_closure(tmp_path)

    assert ("Dockerfile", "unmodelled_container_dispatch") in closure.observed_gaps


def test_copy_binding_ignores_a_duplicate_shell_basename_decoy(tmp_path: Path) -> None:
    _deployment(tmp_path, "value = 1\n")
    (tmp_path / ".docker").mkdir()
    (tmp_path / ".docker" / "entrypoint.sh").write_text("python tools/node.py\n", encoding="utf-8")
    (tmp_path / "scripts" / "entrypoint.sh").write_text("python tools/node.py\n", encoding="utf-8")
    (tmp_path / "Dockerfile").write_text(
        'COPY .docker/entrypoint.sh /entrypoint.sh\nENTRYPOINT ["/entrypoint.sh"]\n',
        encoding="utf-8",
    )

    entrypoints, findings, _ = derive_deployed_entrypoints(tmp_path)

    assert not [item for item in findings if "container" in item.rule_id]
    assert any(
        item.discovery == "CONTAINER_ENTRYPOINT" and item.entrypoint_id == ".docker/entrypoint.sh"
        for item in entrypoints
    )


# ---------------------------------------------------------------------------
# Alias dispatch
# ---------------------------------------------------------------------------


@pytest.mark.parametrize(
    ("body", "mechanism"),
    [
        (
            "from importlib import import_module as load\n\n\ndef run(n):\n    return load(n)\n",
            "dynamic_import_alias",
        ),
        (
            "import importlib\n\nload = importlib.import_module\n\n\ndef run(n):\n    return load(n)\n",
            "dynamic_import_alias",
        ),
    ],
)
def test_dynamic_import_aliases_are_reported(tmp_path: Path, body: str, mechanism: str) -> None:
    _deployment(tmp_path, body)

    closure = derive_python_deployment_closure(tmp_path)

    assert ("tools/node.py", mechanism) in closure.observed_gaps


def test_subprocess_assignment_alias_is_recognized(tmp_path: Path) -> None:
    _deployment(
        tmp_path,
        "import subprocess\n\nrunner = subprocess.run\n\n\ndef go(command):\n    runner(command)\n",
    )

    closure = derive_python_deployment_closure(tmp_path)

    assert ("tools/node.py", "unresolved_subprocess_dispatch") in closure.observed_gaps


@pytest.mark.parametrize(
    "body",
    [
        (
            "import subprocess as sp\n\nrunner = sp.run\nrunner2 = runner\n\n\ndef go():\n"
            "    runner2(['python3', '-m', 'pkg.leaf'])\n"
        ),
        (
            "import subprocess as sp\n\nsp2 = sp\nrunner = sp2.run\nrunner2 = runner\n\n"
            "def go():\n    runner2(['python3', '-m', 'pkg.leaf'])\n"
        ),
    ],
)
def test_transitive_subprocess_aliases_reach_the_dispatched_module(tmp_path: Path, body: str) -> None:
    """D3: runner and module aliases propagate to a fixpoint."""

    _deployment(
        tmp_path,
        body,
        extra={
            "pkg/__init__.py": "",
            "pkg/leaf.py": "from pathlib import Path\nPath('leaf.marker').touch()\n",
        },
    )

    closure = derive_python_deployment_closure(tmp_path)

    assert "pkg/leaf.py" in closure.modules
    assert ("pkg/leaf.py", "<module>", "NAMESPACE_CREATE") in _observe(tmp_path)


@pytest.mark.parametrize(
    "body",
    [
        (
            "from importlib import import_module as load\nload2 = load\nload3 = load2\n\n"
            "def go(name):\n    return load3(name)\n"
        ),
        (
            "import importlib as il\nil2 = il\nload = il2.import_module\nload2 = load\n\n"
            "def go(name):\n    return load2(name)\n"
        ),
    ],
)
def test_transitive_dynamic_import_aliases_remain_typed_gaps(tmp_path: Path, body: str) -> None:
    """D3: alias depth cannot turn unresolved imported code into silence."""

    _deployment(tmp_path, body)

    closure = derive_python_deployment_closure(tmp_path)

    assert ("tools/node.py", "dynamic_import_alias") in closure.observed_gaps


# ---------------------------------------------------------------------------
# Repository census
# ---------------------------------------------------------------------------


def test_repository_inventory_is_exact() -> None:
    report = check_m6_value_sinks_v2(ROOT)

    assert report["findings"] == []
    assert report["scanner_relative_manifest_agreement"] is True
    assert report["manifest_identity_count"] == 316
    assert report["observed_occurrence_count"] == 390
    assert report["static_scanned_module_count"] == 496


def test_repository_inventory_withholds_authority() -> None:
    report = check_m6_value_sinks_v2(ROOT)

    assert report["closure_complete"] is False
    assert report["release_ready"] is False
    assert report["production_authority"] is False
    assert report["vm01_status"] == "OPEN"
    assert report["p2_t01_status"] == "OPEN"
    assert report["p2_t02_status"] == "OPEN"
    assert len(report["declared_closure_gaps"]) == 170
    assert report["adjudicated_identity_count"] == 0
    assert len(report["unadjudicated_sinks"]) == 316


def test_repository_reaches_the_container_api_surface() -> None:
    closure = derive_python_deployment_closure(ROOT)

    assert "src/integration/api_server.py" in closure.modules
    assert any(item.target == "-m src.integration.api_server" for item in closure.entrypoints)


def test_repository_records_its_unscanned_reachable_module() -> None:
    report = check_m6_value_sinks_v2(ROOT)

    snapshot_failures = [
        finding
        for finding in report["findings"]
        if finding["rule_id"] == "repository_snapshot_changed"
    ]
    assert snapshot_failures == [], f"typed repository snapshot failure: {snapshot_failures}"
    assert report["scanner_relative_manifest_agreement"] is True
    assert report["static_reachable_unscanned_modules"] == [
        "generated/perp_python/perp_epoch_clearinghouse_3p_transfer_v0_1_ref.py"
    ]


def test_repository_manifest_decodes_and_binds_fingerprints() -> None:
    specs = load_value_sink_manifest(ROOT / "tools" / "m6_value_sink_manifest_v2.json")

    assert len(specs) == 316
    assert all(spec.release_binding is None for spec in specs)
    assert all(len(spec.identity_fingerprint) == 64 for spec in specs)


def test_repository_nonclaims_state_the_inventory_ceiling() -> None:
    report = check_m6_value_sinks_v2(ROOT)

    joined = " ".join(str(item) for item in report["nonclaims"])
    assert "never proof of sole-publisher closure" in joined
    assert "runtime execution and artifact consumption remain unproved" in joined
    assert "VM-01 remains open" in joined


# ---------------------------------------------------------------------------
# Comparison and command surface
# ---------------------------------------------------------------------------


def test_unclassified_observation_reports_its_count() -> None:
    from tools.m6_value_sinks.scanner import ValueSinkObservationV2

    observation = ValueSinkObservationV2("tools/node.py", "publish", "ATOMIC_REPLACE", "f" * 64)

    findings = compare_inventory((), (observation, observation), frozenset({"tools/node.py"}))

    assert [item.rule_id for item in findings] == ["unclassified_value_sink"]
    assert findings[0].evidence == "publish:ATOMIC_REPLACE:2"


def test_classified_sink_that_disappears_is_reported(tmp_path: Path) -> None:
    _deployment(tmp_path, "def run():\n    return None\n")
    _manifest(tmp_path, [_entry()])

    report = check_m6_value_sinks_v2(tmp_path)

    assert any(item["rule_id"] == "classified_value_sink_missing" for item in report["findings"])


def test_main_fails_closed_on_the_repository(capsys: pytest.CaptureFixture[str]) -> None:
    """The default gate is red while any blocker remains."""

    exit_code = main(["--root", str(ROOT)])

    output = capsys.readouterr().out
    assert exit_code == 1
    assert "VM-01 remains OPEN" in output
    assert "unadjudicated_sinks" in output


def test_repository_gate_blockers_are_named() -> None:
    report = check_m6_value_sinks_v2(ROOT)

    assert set(gate_blockers(report)) == {
        "closure_incomplete",
        "declared_closure_gaps",
        "p2_t01_open",
        "p2_t02_open",
        "production_authority_none",
        "release_not_ready",
        "static_reachable_unscanned_modules",
        "unadjudicated_sinks",
        "release_gaps",
        "vm01_open",
    }


def test_emitted_manifest_marks_a_new_sink_unadjudicated(tmp_path: Path, capsys: pytest.CaptureFixture[str]) -> None:
    _deployment(
        tmp_path,
        "import os\n\n\ndef publish():\n    os.replace('state.tmp', 'state.live')\n",
    )

    assert main(
        ["--root", str(tmp_path), "--emit-manifest", "--research-emission"]
    ) == 1

    emitted = json.loads(capsys.readouterr().out)
    assert emitted["entries"][0]["classification"] == "UNADJUDICATED"
    assert emitted["entries"][0]["mediation_status"] == "UNADJUDICATED"

    # The row loads as an explicit unknown and is reported as a blocker.
    path = _manifest(tmp_path, emitted["entries"])
    specs = load_value_sink_manifest(path)
    assert [spec.classification for spec in specs] == ["UNADJUDICATED"]
    assert check_m6_value_sinks_v2(tmp_path)["unadjudicated_sinks"] == [specs[0].sink_id]


def test_generated_sink_ids_bind_the_full_identity_without_stem_collisions(tmp_path: Path) -> None:
    """D10: equal stems and symbols in different packages receive distinct IDs."""

    _deployment(
        tmp_path,
        "import alpha.node\nimport beta.node\n",
        extra={
            "alpha/__init__.py": "",
            "alpha/node.py": "from pathlib import Path\n\n\ndef publish():\n    Path('a').touch()\n",
            "beta/__init__.py": "",
            "beta/node.py": "from pathlib import Path\n\n\ndef publish():\n    Path('b').touch()\n",
        },
    )

    entries = render_manifest_v2(tmp_path)["entries"]
    selected = [entry for entry in entries if entry["path"] in {"alpha/node.py", "beta/node.py"}]

    assert len(selected) == 2
    assert len({entry["sink_id"] for entry in selected}) == 2
    for entry in selected:
        payload = "\0".join(
            (str(entry["path"]), str(entry["symbol"]), str(entry["sink_kind"]))
        ).encode("utf-8")
        expected = hashlib.sha256(b"zenodex-m6-sink-id-v2\0" + payload).hexdigest()
        assert entry["sink_id"].endswith(expected)


# ---------------------------------------------------------------------------
# Independent Max review 98546573: seven release-blocking counterexamples
# ---------------------------------------------------------------------------


def _root_path(subject: Path | RepositorySnapshotV2) -> Path:
    return subject.root_path if isinstance(subject, RepositorySnapshotV2) else subject


def test_report_rejects_root_path_substitution_even_when_bytes_match(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """NO-GO 1: every phase must consume one persistent root capability."""

    subject = tmp_path / "subject"
    replacement = tmp_path / "replacement"
    retired = tmp_path / "retired"
    _deployment(subject, "from pathlib import Path\nPath('state').touch()\n")
    emitted = render_manifest_v2(subject)
    _manifest(subject, list(emitted["entries"]), list(emitted["closure_gaps"]))
    shutil.copytree(subject, replacement)
    original_scan = report_module.scan_closure

    def substitute_before_scan(
        root: Path | RepositorySnapshotV2, closure: DeploymentClosureV2
    ) -> tuple[ValueSinkObservationV2, ...]:
        root_path = _root_path(root)
        root_path.rename(retired)
        replacement.rename(root_path)
        return original_scan(root, closure)

    monkeypatch.setattr(report_module, "scan_closure", substitute_before_scan)

    report = check_m6_value_sinks_v2(subject)

    assert report["scanner_relative_manifest_agreement"] is False
    assert any(item["rule_id"] == "repository_snapshot_changed" for item in report["findings"])


def test_report_rejects_launcher_change_between_closure_and_scan(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """NO-GO 1: a launcher byte change cannot leave a mixed-phase report."""

    _deployment(tmp_path, "from pathlib import Path\nPath('state').touch()\n")
    emitted = render_manifest_v2(tmp_path)
    _manifest(tmp_path, list(emitted["entries"]), list(emitted["closure_gaps"]))
    original_scan = report_module.scan_closure

    def mutate_launcher_before_scan(
        root: Path | RepositorySnapshotV2, closure: DeploymentClosureV2
    ) -> tuple[ValueSinkObservationV2, ...]:
        root_path = _root_path(root)
        (root_path / "scripts" / "install_zenodex.sh").write_text(
            _INSTALL + "# concurrent mutation\n", encoding="utf-8"
        )
        return original_scan(root, closure)

    monkeypatch.setattr(report_module, "scan_closure", mutate_launcher_before_scan)

    report = check_m6_value_sinks_v2(tmp_path)

    assert report["scanner_relative_manifest_agreement"] is False
    assert any(item["rule_id"] == "repository_snapshot_changed" for item in report["findings"])


def test_report_refuses_symlink_in_repository_root_components(tmp_path: Path) -> None:
    real_parent = tmp_path / "real"
    subject = real_parent / "subject"
    _deployment(subject, "value = 1\n")
    alias = tmp_path / "alias"
    alias.symlink_to(real_parent, target_is_directory=True)

    report = check_m6_value_sinks_v2(alias / "subject")

    assert report["scanner_relative_manifest_agreement"] is False
    assert report["findings"][0]["rule_id"] == "repository_snapshot_changed"
    assert "symlink-free" in report["findings"][0]["evidence"]


def test_negated_authorization_guard_resets_mediation_judgement(tmp_path: Path) -> None:
    """NO-GO 2: mediation binds the containing module, including its guard."""

    authorized = (
        "import os\n\n\ndef publish(authorized):\n"
        "    if authorized:\n        os.replace('state.tmp', 'state.live')\n"
    )
    _deployment(tmp_path, authorized)
    first = render_manifest_v2(tmp_path)
    entry = dict(first["entries"][0])
    entry.update(
        {
            "classification": "DURABLE_VALUE_STATE",
            "mediation_status": "MEDIATED_BY_VERIFIED_PUBLISHER",
            "rationale": "reviewed authorization guard",
        }
    )
    _manifest(tmp_path, [entry], list(first["closure_gaps"]))
    (tmp_path / "tools" / "node.py").write_text(
        authorized.replace("if authorized:", "if not authorized:"), encoding="utf-8"
    )

    regenerated = render_manifest_v2(tmp_path)["entries"][0]

    assert regenerated["classification"] == UNADJUDICATED
    assert regenerated["mediation_status"] == UNADJUDICATED
    assert regenerated["consumers"] == []


@pytest.mark.parametrize(
    ("body", "mechanism"),
    [
        ("def run(code):\n    exec(code)\n", "dynamic_exec"),
        ("def run(code):\n    return eval(code)\n", "dynamic_eval"),
        ("import runpy\n\ndef run(path):\n    runpy.run_path(path)\n", "runpy_run_path"),
        ("import runpy\n\ndef run(name):\n    runpy.run_module(name)\n", "runpy_run_module"),
        ("import os\n\ndef run(command):\n    os.system(command)\n", "os_process_dispatch"),
        ("import os\n\ndef run(command):\n    os.popen(command)\n", "os_process_dispatch"),
        ("import os\n\ndef run(path, argv):\n    os.spawnv(os.P_NOWAIT, path, argv)\n", "os_process_dispatch"),
        (
            "import asyncio\n\nasync def run(*argv):\n"
            "    await asyncio.create_subprocess_exec(*argv)\n",
            "asyncio_subprocess_dispatch",
        ),
        (
            "import asyncio\n\nasync def run(command):\n"
            "    await asyncio.create_subprocess_shell(command)\n",
            "asyncio_subprocess_dispatch",
        ),
    ],
)
def test_executable_python_edges_are_typed_closure_gaps(
    tmp_path: Path, body: str, mechanism: str
) -> None:
    """NO-GO 3: bounded executable edges may never disappear silently."""

    _deployment(tmp_path, body)

    closure = derive_python_deployment_closure(tmp_path)

    assert ("tools/node.py", mechanism) in closure.observed_gaps


@pytest.mark.parametrize(
    ("body", "mechanism"),
    [
        (
            "from runpy import run_path as run\n\ndef go(path):\n    run(path)\n",
            "runpy_run_path",
        ),
        (
            "import os\n\nlaunch = os.system\n\ndef go(command):\n    launch(command)\n",
            "os_process_dispatch",
        ),
        (
            "from asyncio import create_subprocess_shell as start\n\n"
            "async def go(command):\n    await start(command)\n",
            "asyncio_subprocess_dispatch",
        ),
    ],
)
def test_executable_alias_edges_remain_typed(
    tmp_path: Path, body: str, mechanism: str
) -> None:
    _deployment(tmp_path, body)

    assert ("tools/node.py", mechanism) in derive_python_deployment_closure(
        tmp_path
    ).observed_gaps


def test_escaped_executable_callable_is_a_typed_provenance_gap(tmp_path: Path) -> None:
    _deployment(tmp_path, "import os\n\nRUNNERS = [os.system]\n")

    closure = derive_python_deployment_closure(tmp_path)

    assert (
        "tools/node.py",
        "unresolved_executable_provenance",
    ) in closure.observed_gaps


def test_star_import_is_an_explicit_unresolved_executable_edge(tmp_path: Path) -> None:
    _deployment(
        tmp_path,
        "from tools.hidden import *\n\ndef run():\n    publish()\n",
        extra={
            "tools/__init__.py": "",
            "tools/hidden.py": "__all__ = ['publish']\n\ndef publish():\n    return None\n",
        },
    )

    closure = derive_python_deployment_closure(tmp_path)

    assert ("tools/node.py", "unresolved_star_import") in closure.observed_gaps


def test_absent_module_named_by_container_entrypoint_is_a_typed_gap(tmp_path: Path) -> None:
    _deployment(tmp_path, "value = 1\n")
    (tmp_path / ".docker").mkdir()
    (tmp_path / ".docker" / "entrypoint.sh").write_text(
        "python -m absent.local_writer\n", encoding="utf-8"
    )
    (tmp_path / "Dockerfile").write_text(
        'COPY .docker/entrypoint.sh /entrypoint.sh\nENTRYPOINT ["/entrypoint.sh"]\n',
        encoding="utf-8",
    )

    closure = derive_python_deployment_closure(tmp_path)

    assert (".docker/entrypoint.sh", "dispatch_module_absent") in closure.observed_gaps


def test_direct_install_command_cannot_hide_outside_install_wrapper(tmp_path: Path) -> None:
    """NO-GO 4: the entire installer stays a declared, content-bound gap."""

    _deployment(
        tmp_path,
        "value = 1\n",
        install=(
            _INSTALL
            + "install -m 0755 tools/evil.py /usr/local/bin/evil-writer\n"
        ),
        extra={"tools/evil.py": "from pathlib import Path\nPath('hidden').touch()\n"},
    )

    _, findings, gaps = derive_deployed_entrypoints(tmp_path)

    assert any(item.rule_id == "unmodelled_installer_directive" for item in findings) or any(
        mechanism == "unmodelled_installer_shell" for _, mechanism in gaps
    )


def test_install_wrapper_semantics_are_content_bound(tmp_path: Path) -> None:
    first_body = (
        "install_wrapper() {\n    printf '%s' \"$1\"\n}\n" + _INSTALL
    )
    second_body = first_body.replace("printf '%s'", "printf '%s\\n'")
    _deployment(tmp_path, "value = 1\n", install=first_body)

    first_gaps = derive_deployed_entrypoints(tmp_path)[2]
    (tmp_path / "scripts" / "install_zenodex.sh").write_text(second_body, encoding="utf-8")
    second_gaps = derive_deployed_entrypoints(tmp_path)[2]

    first_bindings = {mechanism for _, mechanism in first_gaps if mechanism.startswith("installer_source_sha256_")}
    second_bindings = {mechanism for _, mechanism in second_gaps if mechanism.startswith("installer_source_sha256_")}
    assert len(first_bindings) == 1
    assert len(second_bindings) == 1
    assert first_bindings != second_bindings


def test_sql_comment_semicolon_cannot_hide_real_delete(tmp_path: Path) -> None:
    """NO-GO 5: lexical splitting agrees with a real SQLite side effect."""

    script = "SELECT 1; /* comment; */ DELETE FROM balances;"
    connection = sqlite3.connect(":memory:")
    connection.executescript("CREATE TABLE balances (atoms INTEGER); INSERT INTO balances VALUES (7);")
    before = connection.execute("SELECT COUNT(*) FROM balances").fetchone()
    connection.executescript(script)
    after = connection.execute("SELECT COUNT(*) FROM balances").fetchone()
    _deployment(tmp_path, f"def publish(connection):\n    connection.executescript({script!r})\n")

    assert before == (1,)
    assert after == (0,)
    assert classify_sql_script(script) == "SQL_WRITE"
    assert _observe(tmp_path) == [("tools/node.py", "publish", "SQL_WRITE")]


def test_sql_pragma_call_form_matches_real_sqlite_effect() -> None:
    statement = "PRAGMA user_version(7)"
    connection = sqlite3.connect(":memory:")
    before = connection.execute("PRAGMA user_version").fetchone()
    connection.execute(statement)
    after = connection.execute("PRAGMA user_version").fetchone()

    assert before == (0,)
    assert after == (7,)
    assert classify_sql_statement(statement) == "SQL_PRAGMA_WRITE"


def test_sql_lexical_machine_respects_quoted_semicolons_and_fails_unknown_closed() -> None:
    assert classify_sql_script("SELECT 'not;a;statement';") is None
    assert classify_sql_script("SELECT 1; /* unterminated") == "SQL_DYNAMIC"
    assert classify_sql_script("SELECT 'unterminated") == "SQL_DYNAMIC"


@pytest.mark.parametrize(
    ("script", "expected"),
    [
        (";" * (MAX_SQL_STATEMENTS - 1), None),
        (";" * MAX_SQL_STATEMENTS, "SQL_DYNAMIC"),
        (" " * MAX_SQL_SCRIPT_CHARACTERS, None),
        (" " * (MAX_SQL_SCRIPT_CHARACTERS + 1), "SQL_DYNAMIC"),
    ],
)
def test_sql_lexical_machine_resource_bounds_bva(
    script: str, expected: str | None
) -> None:
    assert classify_sql_script(script) == expected


@pytest.mark.parametrize(
    ("body", "kind"),
    [
        (
            "from pathlib import Path\n\ndef go():\n    Path('a').replace(*['b'])\n",
            "PATH_REPLACE",
        ),
        (
            "from pathlib import Path\n\ndef go():\n"
            "    Path('a').rename(**{'target': 'b'})\n",
            "RENAME",
        ),
    ],
)
def test_starred_path_receiver_writes_are_observed(tmp_path: Path, body: str, kind: str) -> None:
    """NO-GO 6: unresolved argument spelling cannot erase a proved Path writer."""

    _deployment(tmp_path, body)

    observations = _observations(tmp_path)

    assert [item.sink_kind for item in observations] == [kind]
    assert observations[0].destination_resolved is False


def test_escaped_bound_path_writer_is_a_typed_provenance_gap(tmp_path: Path) -> None:
    _deployment(
        tmp_path,
        "from pathlib import Path\n\nmove = Path('a').replace\n\ndef go():\n    move('b')\n",
    )

    closure = derive_python_deployment_closure(tmp_path)

    assert ("tools/node.py", "unresolved_receiver_writer_provenance") in closure.observed_gaps


def test_import_os_path_preserves_os_writer_provenance(tmp_path: Path) -> None:
    _deployment(tmp_path, "import os.path\n\ndef go():\n    os.replace('a', 'b')\n")

    assert _observe(tmp_path) == [("tools/node.py", "go", "ATOMIC_REPLACE")]


def test_starred_str_replace_is_not_a_path_writer(tmp_path: Path) -> None:
    _deployment(tmp_path, "def go():\n    return 'abc'.replace(*['a', 'b'])\n")

    closure = derive_python_deployment_closure(tmp_path)

    assert scan_closure(tmp_path, closure) == ()
    assert not [gap for gap in closure.observed_gaps if "receiver_writer" in gap[1]]


@pytest.mark.parametrize(("extra", "exceeded"), [(0, False), (1, True)])
def test_total_root_enumeration_ceiling_bva(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, extra: int, exceeded: bool
) -> None:
    """NO-GO 7: the bound applies before Dockerfile filtering."""

    maximum = launcher_module.MAX_ROOT_ENTRIES
    consumed: list[int] = []

    def names(_root: object, relative: str) -> Iterator[str]:
        assert relative == ""
        for index in range(maximum + extra):
            consumed.append(index)
            yield f"ordinary-{index:05d}"

    monkeypatch.setattr(launcher_module, "_directory_names", names)

    _, findings, _ = launcher_module._container_shell_scripts(tmp_path)

    assert ("repository_root_entry_ceiling_exceeded" in {item.rule_id for item in findings}) is exceeded
    assert len(consumed) == maximum + extra


def test_total_root_enumeration_stops_before_late_dockerfile(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    maximum = launcher_module.MAX_ROOT_ENTRIES
    consumed: list[int] = []

    def names(_root: object, relative: str) -> Iterator[str]:
        assert relative == ""
        for index in range(100_000):
            consumed.append(index)
            yield f"ordinary-{index:06d}"
        raise AssertionError("the bounded iterator reached a late Dockerfile")

    monkeypatch.setattr(launcher_module, "_directory_names", names)

    _, findings, _ = launcher_module._container_shell_scripts(tmp_path)

    assert {item.rule_id for item in findings} == {"repository_root_entry_ceiling_exceeded"}
    assert len(consumed) == maximum + 1


def test_nonclaim_limits_dynamic_edge_reporting_to_recognized_mechanisms() -> None:
    joined = " ".join(report_module.NONCLAIMS)

    assert "recognized unresolved executable mechanisms" in joined
    assert "unresolved dynamic import, subprocess, shell, plugin, native, and generated dispatch are reported" not in joined


# ---------------------------------------------------------------------------
# NO-GO successor: exact built-in open provenance
# ---------------------------------------------------------------------------


@pytest.mark.parametrize(
    "body",
    [
        "writer = open\n\ndef publish():\n    writer('state.db', 'w').close()\n",
        "first = open\nsecond = first\n\ndef publish():\n    second('state.db', 'a').close()\n",
        "import builtins\n\ndef publish():\n    builtins.open('state.db', 'x').close()\n",
        "import builtins as exact_builtins\n\ndef publish():\n    exact_builtins.open('state.db', 'w').close()\n",
        "from builtins import open as writer\n\ndef publish():\n    writer('state.db', 'w').close()\n",
        "from builtins import open as first\nsecond = first\n\ndef publish():\n    second('state.db', 'w').close()\n",
    ],
)
def test_builtin_open_exact_aliases_are_observed(tmp_path: Path, body: str) -> None:
    """RIPR: every exact mutating alias reaches the OPEN_WRITE observable."""

    _deployment(tmp_path, body)

    assert _observe(tmp_path) == [("tools/node.py", "publish", "OPEN_WRITE")]


@pytest.mark.parametrize(
    "body",
    [
        "writer = open\n\ndef publish():\n    writer('state.db').close()\n",
        "writer = open\n\ndef publish():\n    writer('state.db', 'r').close()\n",
        "import builtins\n\ndef publish():\n    builtins.open('state.db', 'rb').close()\n",
        "from builtins import open as writer\n\ndef publish():\n    writer('state.db', 'rt').close()\n",
    ],
)
def test_builtin_open_exact_read_aliases_remain_nonmutating(tmp_path: Path, body: str) -> None:
    _deployment(tmp_path, body)

    assert _observe(tmp_path) == []


@pytest.mark.parametrize(
    "body",
    [
        "writer = open\n\ndef publish(mode):\n    writer('state.db', mode).close()\n",
        "import builtins\n\ndef publish(mode):\n    builtins.open('state.db', mode=mode).close()\n",
        "from builtins import open as writer\n\ndef publish(options):\n    writer('state.db', **options).close()\n",
    ],
)
def test_builtin_open_dynamic_alias_modes_are_blocking_unknowns(
    tmp_path: Path, body: str
) -> None:
    _deployment(tmp_path, body)

    assert _observe(tmp_path) == [
        ("tools/node.py", "publish", "OPEN_MODE_UNKNOWN")
    ]


@pytest.mark.parametrize(
    "body",
    [
        "def publish(open):\n    open('state.db', 'w')\n",
        "def open(*args):\n    return None\n\ndef publish():\n    open('state.db', 'w')\n",
        "from tools.shim import open\n\ndef publish():\n    open('state.db', 'w')\n",
        "writer = open\nwriter = lambda *args: None\n\ndef publish():\n    writer('state.db', 'w')\n",
        "from tools.shim import *\n\ndef publish():\n    open('state.db', 'w')\n",
    ],
)
def test_builtin_open_shadow_and_wildcard_cases_are_blocking_unknowns(
    tmp_path: Path, body: str
) -> None:
    _deployment(
        tmp_path,
        body,
        extra={"tools/__init__.py": "", "tools/shim.py": "def open(*args):\n    return None\n"},
    )

    assert _observe(tmp_path) == [
        ("tools/node.py", "publish", "ALIAS_TARGET_UNKNOWN")
    ]


@pytest.mark.parametrize(
    "body",
    [
        "CALLBACKS = [open]\n",
        "import builtins\nCALLBACKS = [builtins.open]\n",
        "writer = open\n\ndef escape():\n    return writer\n",
        "import builtins\nCALLBACKS = [getattr(builtins, 'open')]\n",
    ],
)
def test_builtin_open_escape_is_a_typed_provenance_gap(tmp_path: Path, body: str) -> None:
    _deployment(tmp_path, body)

    closure = derive_python_deployment_closure(tmp_path)

    assert ("tools/node.py", "unresolved_writer_provenance") in closure.observed_gaps


def test_builtin_open_alias_is_visible_to_the_full_inventory_gate(tmp_path: Path) -> None:
    """A stale manifest that omits the aliased writer must fail consistency."""

    _deployment(
        tmp_path,
        "from pathlib import Path\nwriter = open\n\ndef publish():\n"
        "    Path('control').touch()\n    writer('state.db', 'w').close()\n",
    )
    rendered = render_manifest_v2(tmp_path)
    without_open = [
        entry for entry in rendered["entries"] if entry["sink_kind"] != "OPEN_WRITE"
    ]
    _manifest(tmp_path, without_open, rendered["closure_gaps"])

    report = check_m6_value_sinks_v2(tmp_path)

    assert report["scanner_relative_manifest_agreement"] is False
    assert any(
        finding["rule_id"] == "unclassified_value_sink"
        and finding["evidence"].startswith("publish:OPEN_WRITE:")
        for finding in report["findings"]
    )


# ---------------------------------------------------------------------------
# NO-GO successor: cross-module authorization/control drift
# ---------------------------------------------------------------------------


_GUARDED_CALLER = (
    "from tools.writer import publish as move\n\n"
    "def run(authorized):\n"
    "    if authorized:\n"
    "        move()\n\n"
    "if __name__ == '__main__':\n"
    "    run(False)\n"
)

_WRITER_MODULE = (
    "from pathlib import Path\n\n"
    "def publish():\n"
    "    Path('unauthorized.marker').write_text('moved', encoding='utf-8')\n"
)


def _install_reviewed_mediated_writer(root: Path) -> None:
    first = render_manifest_v2(root)
    entries: list[dict[str, object]] = []
    for raw_entry in first["entries"]:
        entry = dict(raw_entry)
        if entry["path"] == "tools/writer.py":
            entry.update(
                {
                    "classification": "DURABLE_VALUE_STATE",
                    "mediation_status": "MEDIATED_BY_VERIFIED_PUBLISHER",
                    "rationale": "reviewed caller authorization",
                }
            )
        entries.append(entry)
    _manifest(root, entries, first["closure_gaps"])


def _writer_entry(root: Path) -> RenderedSinkEntryV2:
    return next(
        entry
        for entry in render_manifest_v2(root)["entries"]
        if entry["path"] == "tools/writer.py"
    )


def test_mediated_judgement_without_control_certificate_resets_fail_closed(
    tmp_path: Path,
) -> None:
    """V2 has no reviewed control certificate, so mediation cannot persist."""

    _deployment(
        tmp_path,
        _GUARDED_CALLER,
        extra={"tools/__init__.py": "", "tools/writer.py": _WRITER_MODULE},
    )
    _install_reviewed_mediated_writer(tmp_path)

    report = check_m6_value_sinks_v2(tmp_path)
    regenerated = _writer_entry(tmp_path)

    assert report["scanner_relative_manifest_agreement"] is True, report["findings"]
    assert report["closure_complete"] is False
    assert any(
        finding["rule_id"] == "mediation_control_dependency_unbound"
        and finding["path"] == "tools/writer.py"
        for finding in report["findings"]
    )
    assert regenerated["classification"] == UNADJUDICATED
    assert regenerated["mediation_status"] == UNADJUDICATED
    assert regenerated["rationale"] == UNADJUDICATED
    assert regenerated["consumers"] == []


@pytest.mark.parametrize(
    "unauthorized_body",
    [
        "    if not authorized:\n        move()\n",
        "    move()\n",
        "    move()\n    if not authorized:\n        return\n",
        "    if True:\n        move()\n",
        "    selected = move\n    if not authorized:\n        selected()\n",
    ],
    ids=["negated", "removed", "reordered", "replaced", "dynamic-dispatch"],
)
def test_cross_module_authorization_drift_resets_and_runtime_oracle_detects_move(
    tmp_path: Path, unauthorized_body: str
) -> None:
    """RIPR: caller-only drift reaches both reset fields and a real durable move."""

    _deployment(
        tmp_path,
        _GUARDED_CALLER,
        extra={"tools/__init__.py": "", "tools/writer.py": _WRITER_MODULE},
    )
    _install_reviewed_mediated_writer(tmp_path)
    environment = dict(os.environ)
    environment["PYTHONDONTWRITEBYTECODE"] = "1"
    environment["PYTHONPATH"] = str(tmp_path)
    subprocess.run(
        [sys.executable, "-B", "-m", "tools.node"],
        cwd=tmp_path,
        env=environment,
        check=True,
    )
    marker = tmp_path / "unauthorized.marker"
    assert marker.exists() is False

    (tmp_path / "tools" / "node.py").write_text(
        "from tools.writer import publish as move\n\n"
        "def run(authorized):\n"
        + unauthorized_body
        + "\nif __name__ == '__main__':\n    run(False)\n",
        encoding="utf-8",
    )
    subprocess.run(
        [sys.executable, "-B", "-m", "tools.node"],
        cwd=tmp_path,
        env=environment,
        check=True,
    )
    regenerated = _writer_entry(tmp_path)

    assert marker.read_text(encoding="utf-8") == "moved"
    assert regenerated["classification"] == UNADJUDICATED
    assert regenerated["mediation_status"] == UNADJUDICATED
    assert regenerated["rationale"] == UNADJUDICATED
    assert regenerated["consumers"] == []


# ---------------------------------------------------------------------------
# NO-GO successor: bare SQLite PRAGMA classification
# ---------------------------------------------------------------------------


@pytest.mark.parametrize(
    ("statement", "expected"),
    [
        ("PRAGMA page_count", None),
        ("  pRaGmA main.page_count  ", None),
        ("PRAGMA page_count -- trailing read comment", None),
        ("PRAGMA incremental_vacuum", "SQL_PRAGMA_WRITE"),
        ("PRAGMA main.incremental_vacuum", "SQL_PRAGMA_WRITE"),
        ("PRAGMA optimize", "SQL_PRAGMA_WRITE"),
        ("PRAGMA wal_checkpoint", "SQL_PRAGMA_WRITE"),
        ("PRAGMA page_counts", "SQL_DYNAMIC"),
        ("PRAGMA unknown_extension_setting", "SQL_DYNAMIC"),
        ("PRAGMA", "SQL_DYNAMIC"),
    ],
)
def test_bare_pragma_allowlist_and_neighbors(
    statement: str, expected: str | None
) -> None:
    assert classify_sql_statement(statement) == expected


def test_bare_incremental_vacuum_matches_real_sqlite_durable_effect(
    tmp_path: Path,
) -> None:
    database = tmp_path / "pragma.sqlite3"
    connection = sqlite3.connect(database)
    try:
        connection.execute("PRAGMA page_size = 512")
        connection.execute("PRAGMA auto_vacuum = INCREMENTAL")
        connection.execute("VACUUM")
        connection.execute("CREATE TABLE payloads (body BLOB NOT NULL)")
        connection.executemany(
            "INSERT INTO payloads(body) VALUES (?)",
            [(b"x" * 1024,) for _ in range(256)],
        )
        connection.commit()
        connection.execute("DELETE FROM payloads")
        connection.commit()
        before_freelist = connection.execute("PRAGMA freelist_count").fetchone()
        before_size = database.stat().st_size

        connection.execute("PRAGMA incremental_vacuum")
        connection.commit()

        after_freelist = connection.execute("PRAGMA freelist_count").fetchone()
        after_size = database.stat().st_size
    finally:
        connection.close()

    assert before_freelist is not None and after_freelist is not None
    assert before_freelist[0] > 0
    assert after_freelist[0] < before_freelist[0]
    assert after_size < before_size
    assert classify_sql_statement("PRAGMA incremental_vacuum") == "SQL_PRAGMA_WRITE"


@pytest.mark.parametrize(
    ("statement", "expected"),
    [
        ("PRAGMA page_count", []),
        ("PRAGMA incremental_vacuum", ["SQL_PRAGMA_WRITE"]),
        ("PRAGMA unknown_extension_setting", ["SQL_DYNAMIC"]),
    ],
)
def test_bare_pragma_classification_reaches_scanner_observations(
    tmp_path: Path, statement: str, expected: list[str]
) -> None:
    _deployment(
        tmp_path,
        f"def publish(connection):\n    connection.execute({statement!r})\n",
    )

    assert [kind for _, _, kind in _observe(tmp_path)] == expected


@pytest.mark.parametrize(
    "statement",
    [
        "PRAGMA page_count",
        "PRAGMA main.page_count",
        "PRAGMA page_count -- trailing read comment",
    ],
)
def test_allowlisted_bare_pragma_matches_real_sqlite_read_only_effect(
    tmp_path: Path, statement: str
) -> None:
    database = tmp_path / "pragma-read.sqlite3"
    connection = sqlite3.connect(database)
    try:
        connection.execute("CREATE TABLE values_table (atoms INTEGER NOT NULL)")
        connection.execute("INSERT INTO values_table(atoms) VALUES (7)")
        connection.commit()
        before = database.read_bytes()

        rows = connection.execute(statement).fetchall()
        after = database.read_bytes()
    finally:
        connection.close()

    assert rows
    assert after == before
    assert classify_sql_statement(statement) is None


def test_pragma_statement_list_uses_the_strongest_effect() -> None:
    assert (
        classify_sql_script("PRAGMA page_count; PRAGMA incremental_vacuum;")
        == "SQL_PRAGMA_WRITE"
    )
    assert (
        classify_sql_script("PRAGMA page_count; PRAGMA unknown_extension_setting;")
        == "SQL_DYNAMIC"
    )


# ---------------------------------------------------------------------------
# Daybreak/Sol Max successor: closed callable provenance and runtime oracles
# ---------------------------------------------------------------------------


def _run_deployed_module(root: Path) -> None:
    environment = dict(os.environ)
    environment["PYTHONDONTWRITEBYTECODE"] = "1"
    environment["PYTHONPATH"] = str(root)
    subprocess.run(
        [sys.executable, "-B", "-m", "tools.node"],
        cwd=root,
        env=environment,
        check=True,
    )


def test_builtins_dict_open_is_observed_and_runtime_truncates(tmp_path: Path) -> None:
    """RIPR: exact __dict__ provenance and a byte-effect oracle agree."""

    target = tmp_path / "state.bin"
    target.write_bytes(b"valuable-state")
    _deployment(
        tmp_path,
        "import builtins\n\n"
        "def publish():\n"
        "    builtins.__dict__['open']('state.bin', 'w').close()\n\n"
        "if __name__ == '__main__':\n"
        "    publish()\n",
    )

    observed = _observe(tmp_path)
    _run_deployed_module(tmp_path)

    assert observed == [("tools/node.py", "publish", "OPEN_WRITE")]
    assert target.read_bytes() == b""


@pytest.mark.parametrize(
    "expression",
    [
        "builtins.exec",
        "builtins.__dict__['exec']",
        "getattr(builtins, 'exec')",
        "vars(builtins)['exec']",
    ],
)
def test_exact_builtins_exec_is_a_typed_gap_and_runtime_executes(
    tmp_path: Path, expression: str
) -> None:
    """RIPR: executable-code edges stay visible beside a filesystem oracle."""

    _deployment(
        tmp_path,
        "import builtins\n\n"
        "def publish():\n"
        f"    {expression}(\"open('exec.marker', 'w').write('executed')\")\n\n"
        "if __name__ == '__main__':\n"
        "    publish()\n",
    )

    closure = derive_python_deployment_closure(tmp_path)
    _run_deployed_module(tmp_path)

    assert ("tools/node.py", "dynamic_exec") in closure.observed_gaps
    assert (tmp_path / "exec.marker").read_text(encoding="utf-8") == "executed"


@pytest.mark.parametrize(
    "body",
    [
        "import builtins\nbuiltins = object()\n\ndef publish():\n"
        "    builtins.exec('value = 1')\n",
        "import builtins\nfrom tools.shim import *\n\ndef publish():\n"
        "    builtins.exec('value = 1')\n",
        "import builtins\nrunner = builtins.exec\nrunner = lambda code: None\n\n"
        "def publish():\n    runner('value = 1')\n",
        "import builtins\n\ndef publish(name):\n"
        "    builtins.__dict__[name]('value = 1')\n",
        "import builtins\ngetattr = lambda *args: builtins.exec\n\n"
        "def publish():\n    getattr(builtins, 'exec')('value = 1')\n",
        "import builtins\nvars = lambda value: value.__dict__\n\n"
        "def publish():\n    vars(builtins)['exec']('value = 1')\n",
        "import builtins\nfrom tools.shim import *\n\n"
        "def publish():\n    getattr(builtins, 'exec')('value = 1')\n",
    ],
)
def test_ambiguous_builtin_executable_provenance_is_a_typed_gap(
    tmp_path: Path, body: str
) -> None:
    _deployment(
        tmp_path,
        body,
        extra={"tools/__init__.py": "", "tools/shim.py": "value = 1\n"},
    )

    closure = derive_python_deployment_closure(tmp_path)

    assert (
        "tools/node.py",
        "unresolved_executable_provenance",
    ) in closure.observed_gaps


def test_handle_truncate_is_observed_and_runtime_shortens_file(tmp_path: Path) -> None:
    """RIPR: caller-handle truncation cannot disappear behind receiver typing."""

    target = tmp_path / "state.bin"
    target.write_bytes(b"valuable-state")
    _deployment(
        tmp_path,
        "def publish():\n"
        "    handle = open('state.bin', 'r+b')\n"
        "    handle.truncate(1)\n"
        "    handle.close()\n\n"
        "if __name__ == '__main__':\n"
        "    publish()\n",
    )

    kinds = [kind for _, _, kind in _observe(tmp_path)]
    _run_deployed_module(tmp_path)

    assert kinds == ["OPEN_WRITE", "TRUNCATE"]
    assert target.read_bytes() == b"v"


def test_aliased_connection_execute_is_observed_and_runtime_deletes(
    tmp_path: Path,
) -> None:
    """RIPR: an exact bound SQL method alias retains its write semantics."""

    database = tmp_path / "state.sqlite3"
    connection = sqlite3.connect(database)
    try:
        connection.execute("CREATE TABLE balances (atoms INTEGER NOT NULL)")
        connection.execute("INSERT INTO balances(atoms) VALUES (7)")
        connection.commit()
    finally:
        connection.close()
    _deployment(
        tmp_path,
        "import sqlite3\n\n"
        "def publish():\n"
        "    connection = sqlite3.connect('state.sqlite3')\n"
        "    execute = connection.execute\n"
        "    execute('DELETE FROM balances')\n"
        "    connection.commit()\n"
        "    connection.close()\n\n"
        "if __name__ == '__main__':\n"
        "    publish()\n",
    )

    observed = _observe(tmp_path)
    _run_deployed_module(tmp_path)
    connection = sqlite3.connect(database)
    try:
        remaining = connection.execute("SELECT COUNT(*) FROM balances").fetchone()
    finally:
        connection.close()

    assert observed == [
        ("tools/node.py", "publish", "DATABASE_OPEN_WRITE"),
        ("tools/node.py", "publish", "SQL_WRITE"),
    ]
    assert remaining == (0,)


@pytest.mark.parametrize(
    ("call", "prefix"),
    [
        ("fd, path = tempfile.mkstemp(prefix='mkstemp-', dir='.')\nos.close(fd)", "mkstemp-"),
        (
            "handle = tempfile.NamedTemporaryFile(prefix='named-', dir='.', delete=False)\n"
            "handle.close()",
            "named-",
        ),
    ],
)
def test_persistent_tempfile_creation_is_observed_and_runtime_creates(
    tmp_path: Path, call: str, prefix: str
) -> None:
    """RIPR: direct persistent tempfile APIs have static and filesystem oracles."""

    _deployment(
        tmp_path,
        "import os\nimport tempfile\n\n"
        "def publish():\n"
        + "\n".join(f"    {line}" for line in call.splitlines())
        + "\n\nif __name__ == '__main__':\n    publish()\n",
    )

    observed = _observe(tmp_path)
    before = {path.name for path in tmp_path.iterdir()}
    _run_deployed_module(tmp_path)
    created = sorted(
        path.name for path in tmp_path.iterdir() if path.name not in before and path.name.startswith(prefix)
    )

    assert observed == [("tools/node.py", "publish", "TEMPFILE_CREATE")]
    assert len(created) == 1


def test_positional_named_tempfile_dir_binds_destination_and_fingerprint_exactly(
    tmp_path: Path,
) -> None:
    """RIPR: positional encoding cannot masquerade as the positional directory."""

    (tmp_path / "value-tmp").mkdir()
    (tmp_path / "other-tmp").mkdir()

    def source(directory: str) -> str:
        return (
            "import tempfile\n\n"
            "def publish():\n"
            "    handle = tempfile.NamedTemporaryFile(\n"
            f"        'w+', -1, 'utf-8', None, '.tmp', 'named-', '{directory}',\n"
            "        delete=False\n"
            "    )\n"
            "    handle.close()\n\n"
            "if __name__ == '__main__':\n"
            "    publish()\n"
        )

    first_source = source("value-tmp")
    _deployment(tmp_path, first_source)
    first = _observations(tmp_path)
    _run_deployed_module(tmp_path)
    created = list((tmp_path / "value-tmp").glob("named-*.tmp"))

    _deployment(tmp_path, source("other-tmp"))
    second = _observations(tmp_path)
    tree = ast.parse(first_source)
    call = next(
        node
        for node in ast.walk(tree)
        if isinstance(node, ast.Call)
        and isinstance(node.func, ast.Attribute)
        and node.func.attr == "NamedTemporaryFile"
    )

    assert len(first) == len(second) == 1
    assert first[0].sink_kind == second[0].sink_kind == "TEMPFILE_CREATE"
    assert first[0].destination == "LITERAL:value-tmp"
    assert second[0].destination == "LITERAL:other-tmp"
    assert first[0].destination_resolved is second[0].destination_resolved is True
    operation_digest = operation_fingerprint(
        "TEMPFILE_CREATE", call, "LITERAL:value-tmp"
    )
    expected_fingerprint = hashlib.sha256(
        b"zenodex-m6-operation-module-source-v2\0"
        + hashlib.sha256(first_source.encode("utf-8")).hexdigest().encode("ascii")
        + b"\0"
        + operation_digest.encode("ascii")
    ).hexdigest()
    assert first[0].fingerprint == expected_fingerprint
    assert first[0].fingerprint != second[0].fingerprint
    assert len(created) == 1


@pytest.mark.parametrize(
    ("delete", "expected"),
    [
        ("True", "TEMPFILE_CREATE_EPHEMERAL"),
        ("delete", "TEMPFILE_CREATE_UNKNOWN"),
        ("False", "TEMPFILE_CREATE"),
    ],
)
def test_keyword_named_tempfile_delete_policy_bva(
    tmp_path: Path, delete: str, expected: str
) -> None:
    _deployment(
        tmp_path,
        "import tempfile\n\n"
        "def publish(delete=True):\n"
        "    tempfile.NamedTemporaryFile(\n"
        f"        'w+', -1, 'utf-8', None, '.tmp', 'named-', 'value-tmp',\n"
        f"        delete={delete}\n"
        "    ).close()\n",
    )

    observation = _observations(tmp_path)

    assert len(observation) == 1
    assert observation[0].sink_kind == expected
    assert observation[0].destination == "LITERAL:value-tmp"
    assert observation[0].destination_resolved is True


def test_starred_named_tempfile_arguments_are_unknown_and_unresolved(
    tmp_path: Path,
) -> None:
    _deployment(
        tmp_path,
        "import tempfile\n\n"
        "def publish(arguments):\n"
        "    tempfile.NamedTemporaryFile(*arguments).close()\n",
    )

    observation = _observations(tmp_path)

    assert len(observation) == 1
    assert observation[0].sink_kind == "TEMPFILE_CREATE_UNKNOWN"
    assert observation[0].destination_resolved is False


def test_mkstemp_positional_dir_remains_index_two(tmp_path: Path) -> None:
    _deployment(
        tmp_path,
        "import tempfile\n\n"
        "def publish():\n"
        "    tempfile.mkstemp('.tmp', 'mk-', 'value-tmp')\n",
    )

    observation = _observations(tmp_path)

    assert len(observation) == 1
    assert observation[0].sink_kind == "TEMPFILE_CREATE"
    assert observation[0].destination == "LITERAL:value-tmp"
    assert observation[0].destination_resolved is True


def test_mkdtemp_positional_dir_is_observed_and_runtime_creates_directory(
    tmp_path: Path,
) -> None:
    parent = tmp_path / "value-tmp"
    parent.mkdir()
    _deployment(
        tmp_path,
        "import tempfile\n\n"
        "def publish():\n"
        "    tempfile.mkdtemp('.tmp', 'dir-', 'value-tmp')\n\n"
        "if __name__ == '__main__':\n"
        "    publish()\n",
    )

    observation = _observations(tmp_path)
    _run_deployed_module(tmp_path)
    created = list(parent.glob("dir-*.tmp"))

    assert len(observation) == 1
    assert observation[0].sink_kind == "TEMPDIR_CREATE"
    assert observation[0].destination == "LITERAL:value-tmp"
    assert observation[0].destination_resolved is True
    assert len(created) == 1
    assert created[0].is_dir()


def test_repository_m6_durable_store_has_two_mkdtemp_occurrences() -> None:
    relative = "src/integration/m6_durable_store_v1.py"
    source = (ROOT / relative).read_text(encoding="utf-8")

    observations = tuple(
        observation
        for observation in scan_module(relative, ast.parse(source))
        if observation.sink_kind == "TEMPDIR_CREATE"
    )

    assert len(observations) == 2
    assert {observation.symbol for observation in observations} == {
        "_write_bundle_directory"
    }
    assert len({observation.fingerprint for observation in observations}) == 2


@pytest.mark.parametrize(
    "body",
    [
        "import tempfile\n\ndef publish():\n    tempfile.mkdtemp(dir='.')\n",
        "from tempfile import mkdtemp as create\n\ndef publish():\n    create(dir='.')\n",
        "import tempfile\ncreate = tempfile.mkdtemp\n\ndef publish():\n    create(dir='.')\n",
        "import tempfile\ncreate = tempfile.__dict__['mkdtemp']\n\n"
        "def publish():\n    create(dir='.')\n",
        "import tempfile\ncreate = getattr(tempfile, 'mkdtemp')\n\n"
        "def publish():\n    create(dir='.')\n",
    ],
)
def test_mkdtemp_exact_callable_forms_are_observed(
    tmp_path: Path, body: str
) -> None:
    _deployment(tmp_path, body)

    observation = _observations(tmp_path)

    assert len(observation) == 1
    assert observation[0].sink_kind == "TEMPDIR_CREATE"


@pytest.mark.parametrize(
    "body",
    [
        "import tempfile\ntempfile = object()\n\ndef publish():\n"
        "    tempfile.mkdtemp(dir='.')\n",
        "from tempfile import mkdtemp as create\ncreate = lambda **kwargs: None\n\n"
        "def publish():\n    create(dir='.')\n",
        "import tempfile\nfrom tools.shim import *\n\ndef publish():\n"
        "    tempfile.mkdtemp(dir='.')\n",
    ],
)
def test_mkdtemp_shadow_and_wildcard_are_blocking_unknown(
    tmp_path: Path, body: str
) -> None:
    _deployment(
        tmp_path,
        body,
        extra={"tools/__init__.py": "", "tools/shim.py": "value = 1\n"},
    )

    assert _observe(tmp_path) == [
        ("tools/node.py", "publish", "ALIAS_TARGET_UNKNOWN")
    ]


@pytest.mark.parametrize(
    "body",
    [
        "import tempfile\nCALLBACKS = [tempfile.mkdtemp]\n",
        "import tempfile\ndef register(value):\n    return value\n\n"
        "CREATE = register(tempfile.mkdtemp)\n",
        "import tempfile\ndef publish(name):\n    tempfile.__dict__[name](dir='.')\n",
    ],
)
def test_mkdtemp_escaped_or_dynamic_callable_is_a_typed_gap(
    tmp_path: Path, body: str
) -> None:
    _deployment(tmp_path, body)

    closure = derive_python_deployment_closure(tmp_path)

    assert ("tools/node.py", "unresolved_writer_provenance") in closure.observed_gaps


@pytest.mark.parametrize(
    ("delete", "expected"),
    [
        ("True", "TEMPDIR_CREATE_EPHEMERAL"),
        ("delete", "TEMPDIR_CREATE_UNKNOWN"),
        ("False", "TEMPDIR_CREATE"),
    ],
)
def test_temporary_directory_delete_policy_bva(
    tmp_path: Path, delete: str, expected: str
) -> None:
    _deployment(
        tmp_path,
        "import tempfile\n\n"
        "def publish(delete=True):\n"
        "    tempfile.TemporaryDirectory(\n"
        "        '.tmp', 'dir-', 'value-tmp', delete="
        f"{delete}\n"
        "    )\n",
    )

    observation = _observations(tmp_path)

    assert len(observation) == 1
    assert observation[0].sink_kind == expected
    assert observation[0].destination == "LITERAL:value-tmp"
    assert observation[0].destination_resolved is True


@pytest.mark.parametrize(
    "body",
    [
        "from tempfile import TemporaryDirectory as create\n\n"
        "def publish():\n    create(dir='.', delete=False)\n",
        "import tempfile\ncreate = tempfile.TemporaryDirectory\n\n"
        "def publish():\n    create(dir='.', delete=False)\n",
        "import tempfile\ncreate = tempfile.__dict__['TemporaryDirectory']\n\n"
        "def publish():\n    create(dir='.', delete=False)\n",
        "import tempfile\ncreate = getattr(tempfile, 'TemporaryDirectory')\n\n"
        "def publish():\n    create(dir='.', delete=False)\n",
    ],
)
def test_temporary_directory_exact_callable_forms_are_observed(
    tmp_path: Path, body: str
) -> None:
    _deployment(tmp_path, body)

    observation = _observations(tmp_path)

    assert len(observation) == 1
    assert observation[0].sink_kind == "TEMPDIR_CREATE"


@pytest.mark.parametrize(
    "body",
    [
        "import tempfile\ntempfile = object()\n\ndef publish():\n"
        "    tempfile.TemporaryDirectory(dir='.', delete=False)\n",
        "from tempfile import TemporaryDirectory as create\n"
        "create = lambda **kwargs: None\n\ndef publish():\n"
        "    create(dir='.', delete=False)\n",
    ],
)
def test_temporary_directory_shadow_is_blocking_unknown(
    tmp_path: Path, body: str
) -> None:
    _deployment(tmp_path, body)

    assert _observe(tmp_path) == [
        ("tools/node.py", "publish", "ALIAS_TARGET_UNKNOWN")
    ]


def test_escaped_temporary_directory_callable_is_a_typed_gap(tmp_path: Path) -> None:
    _deployment(
        tmp_path,
        "import tempfile\nCALLBACKS = [tempfile.TemporaryDirectory]\n",
    )

    closure = derive_python_deployment_closure(tmp_path)

    assert ("tools/node.py", "unresolved_writer_provenance") in closure.observed_gaps


def test_persistent_temporary_directory_runtime_oracle(tmp_path: Path) -> None:
    parent = tmp_path / "value-tmp"
    parent.mkdir()
    _deployment(
        tmp_path,
        "import tempfile\n\n"
        "def publish():\n"
        "    tempfile.TemporaryDirectory(\n"
        "        '.tmp', 'dir-', 'value-tmp', delete=False\n"
        "    )\n\n"
        "if __name__ == '__main__':\n"
        "    publish()\n",
    )

    observation = _observations(tmp_path)
    _run_deployed_module(tmp_path)
    created = list(parent.glob("dir-*.tmp"))

    assert len(observation) == 1
    assert observation[0].sink_kind == "TEMPDIR_CREATE"
    assert len(created) == 1
    assert created[0].is_dir()


def test_default_temporary_directory_cleanup_runtime_oracle(tmp_path: Path) -> None:
    parent = tmp_path / "value-tmp"
    parent.mkdir()
    _deployment(
        tmp_path,
        "import tempfile\n\n"
        "def publish():\n"
        "    with tempfile.TemporaryDirectory(\n"
        "        '.tmp', 'dir-', 'value-tmp'\n"
        "    ):\n"
        "        pass\n\n"
        "if __name__ == '__main__':\n"
        "    publish()\n",
    )

    observation = _observations(tmp_path)
    _run_deployed_module(tmp_path)

    assert len(observation) == 1
    assert observation[0].sink_kind == "TEMPDIR_CREATE_EPHEMERAL"
    assert list(parent.glob("dir-*.tmp")) == []


def test_temporary_directory_starred_arguments_are_unknown_and_unresolved(
    tmp_path: Path,
) -> None:
    _deployment(
        tmp_path,
        "import tempfile\n\ndef publish(arguments):\n"
        "    tempfile.TemporaryDirectory(*arguments)\n",
    )

    observation = _observations(tmp_path)

    assert len(observation) == 1
    assert observation[0].sink_kind == "TEMPDIR_CREATE_UNKNOWN"
    assert observation[0].destination_resolved is False


@pytest.mark.parametrize("factory", ["TemporaryFile", "SpooledTemporaryFile"])
def test_unnamed_tempfile_factories_are_not_namespace_sinks(
    tmp_path: Path, factory: str
) -> None:
    _deployment(
        tmp_path,
        f"import tempfile\n\ndef publish():\n    tempfile.{factory}()\n",
    )

    assert _observations(tmp_path) == ()


@pytest.mark.parametrize(
    "expression",
    [
        "builtins.__dict__['open']",
        "getattr(builtins, 'open')",
        "vars(builtins)['open']",
    ],
)
def test_exact_reflective_open_aliases_retain_callable_provenance(
    tmp_path: Path, expression: str
) -> None:
    _deployment(
        tmp_path,
        "import builtins\n\n"
        f"writer = {expression}\n\n"
        "def publish():\n"
        "    writer('state.bin', 'w').close()\n",
    )

    closure = derive_python_deployment_closure(tmp_path)

    assert [item.identity() for item in scan_closure(tmp_path, closure)] == [
        ("tools/node.py", "publish", "OPEN_WRITE")
    ]
    assert ("tools/node.py", "unresolved_writer_provenance") not in closure.observed_gaps
    assert (
        "tools/node.py",
        "unresolved_executable_provenance",
    ) not in closure.observed_gaps


def test_dynamic_reflective_writer_lookup_is_a_typed_gap(tmp_path: Path) -> None:
    _deployment(
        tmp_path,
        "import builtins\n\n"
        "def publish(name):\n"
        "    builtins.__dict__[name]('state.bin', 'w').close()\n",
    )

    closure = derive_python_deployment_closure(tmp_path)

    assert ("tools/node.py", "unresolved_writer_provenance") in closure.observed_gaps


@pytest.mark.parametrize(
    "body",
    [
        "import builtins\ngetattr = lambda *args: builtins.open\n\n"
        "def publish():\n    getattr(builtins, 'open')('state.bin', 'w').close()\n",
        "import builtins\nvars = lambda value: value.__dict__\n\n"
        "def publish():\n    vars(builtins)['open']('state.bin', 'w').close()\n",
        "import builtins\nfrom tools.shim import *\n\n"
        "def publish():\n    getattr(builtins, 'open')('state.bin', 'w').close()\n",
    ],
)
def test_shadowed_reflection_helper_is_a_typed_writer_gap(
    tmp_path: Path, body: str
) -> None:
    _deployment(
        tmp_path,
        body,
        extra={"tools/__init__.py": "", "tools/shim.py": "value = 1\n"},
    )

    closure = derive_python_deployment_closure(tmp_path)

    assert ("tools/node.py", "unresolved_writer_provenance") in closure.observed_gaps


def test_bound_truncate_alias_retains_operation_family(tmp_path: Path) -> None:
    _deployment(
        tmp_path,
        "def publish(handle):\n"
        "    shorten = handle.truncate\n"
        "    shorten(1)\n",
    )

    assert _observe(tmp_path) == [("tools/node.py", "publish", "TRUNCATE")]


def test_reassigned_bound_writer_alias_is_blocking_unknown(tmp_path: Path) -> None:
    _deployment(
        tmp_path,
        "def publish(connection):\n"
        "    execute = connection.execute\n"
        "    execute = lambda statement: None\n"
        "    execute('DELETE FROM balances')\n",
    )

    assert _observe(tmp_path) == [
        ("tools/node.py", "publish", "ALIAS_TARGET_UNKNOWN")
    ]


@pytest.mark.parametrize(
    "body",
    [
        "import tempfile\n\ncreate = tempfile.mkstemp\n\ndef publish():\n    create(dir='.')\n",
        "from tempfile import mkstemp as create\n\ndef publish():\n    create(dir='.')\n",
        "import tempfile\n\ncreate = tempfile.NamedTemporaryFile\n\ndef publish():\n"
        "    create(dir='.', delete=False).close()\n",
    ],
)
def test_persistent_tempfile_exact_aliases_are_observed(
    tmp_path: Path, body: str
) -> None:
    _deployment(tmp_path, body)

    assert _observe(tmp_path) == [
        ("tools/node.py", "publish", "TEMPFILE_CREATE")
    ]


def test_dynamic_named_tempfile_delete_policy_is_blocking_unknown(
    tmp_path: Path,
) -> None:
    _deployment(
        tmp_path,
        "import tempfile\n\n"
        "def publish(delete):\n"
        "    tempfile.NamedTemporaryFile(dir='.', delete=delete).close()\n",
    )

    assert _observe(tmp_path) == [
        ("tools/node.py", "publish", "TEMPFILE_CREATE_UNKNOWN")
    ]


def test_default_named_tempfile_policy_is_explicitly_ephemeral(
    tmp_path: Path,
) -> None:
    _deployment(
        tmp_path,
        "import tempfile\n\n"
        "def publish():\n"
        "    tempfile.NamedTemporaryFile(dir='.').close()\n",
    )

    assert _observe(tmp_path) == [
        ("tools/node.py", "publish", "TEMPFILE_CREATE_EPHEMERAL")
    ]


@pytest.mark.parametrize(
    "body",
    [
        "import tempfile\ntempfile = object()\n\ndef publish():\n    tempfile.mkstemp(dir='.')\n",
        "from tempfile import mkstemp as create\ncreate = lambda **kwargs: None\n\n"
        "def publish():\n    create(dir='.')\n",
        "import tempfile\nfrom tools.shim import *\n\ndef publish():\n"
        "    tempfile.mkstemp(dir='.')\n",
    ],
)
def test_tempfile_shadow_and_wildcard_provenance_is_blocking_unknown(
    tmp_path: Path, body: str
) -> None:
    _deployment(
        tmp_path,
        body,
        extra={"tools/__init__.py": "", "tools/shim.py": "value = 1\n"},
    )

    assert _observe(tmp_path) == [
        ("tools/node.py", "publish", "ALIAS_TARGET_UNKNOWN")
    ]


def test_escaped_tempfile_creator_is_a_typed_provenance_gap(tmp_path: Path) -> None:
    _deployment(tmp_path, "import tempfile\n\nCALLBACKS = [tempfile.mkstemp]\n")

    closure = derive_python_deployment_closure(tmp_path)

    assert ("tools/node.py", "unresolved_writer_provenance") in closure.observed_gaps


def test_reflective_builtin_open_read_control_has_no_write_observation(
    tmp_path: Path,
) -> None:
    _deployment(
        tmp_path,
        "import builtins\n\n"
        "def read():\n"
        "    builtins.__dict__['open']('state.bin', 'rb').close()\n",
    )

    closure = derive_python_deployment_closure(tmp_path)

    assert scan_closure(tmp_path, closure) == ()
    assert ("tools/node.py", "unresolved_writer_provenance") not in closure.observed_gaps


@pytest.mark.parametrize(
    ("counter", "claim"),
    [
        ("source_bytes", "claim_source_bytes"),
        ("ast_nodes", "claim_ast_nodes"),
        ("closure_edges", "claim_closure_edges"),
        ("observations", "claim_observations"),
    ],
)
def test_aggregate_resource_budgets_reject_maximum_plus_one_before_accumulation(
    counter: str, claim: str
) -> None:
    limits = launcher_module.ScanResourceLimitsV2(
        max_source_bytes=3,
        max_ast_nodes=3,
        max_closure_edges=3,
        max_observations=3,
        max_retained_descriptors=3,
        max_retained_cache_bytes=3,
    )
    meter = launcher_module.ScanResourceMeterV2(limits)
    claim_method = getattr(meter, claim)

    claim_method(3)
    with pytest.raises(launcher_module.ResourceBudgetExceeded):
        claim_method(1)

    assert getattr(meter, counter) == 3


def test_retained_descriptor_and_cache_budgets_are_atomic_at_maximum_neighbor() -> None:
    limits = launcher_module.ScanResourceLimitsV2(
        max_source_bytes=1,
        max_ast_nodes=1,
        max_closure_edges=1,
        max_observations=1,
        max_retained_descriptors=2,
        max_retained_cache_bytes=3,
    )
    meter = launcher_module.ScanResourceMeterV2(limits)

    meter.claim_retained(3)
    with pytest.raises(launcher_module.ResourceBudgetExceeded):
        meter.claim_retained(1)

    assert meter.retained_descriptors == 2
    assert meter.retained_cache_bytes == 3

    cache_limited = launcher_module.ScanResourceMeterV2(
        replace(limits, max_retained_descriptors=3)
    )
    cache_limited.claim_retained(3)
    with pytest.raises(launcher_module.ResourceBudgetExceeded):
        cache_limited.claim_retained(1)

    assert cache_limited.retained_descriptors == 2
    assert cache_limited.retained_cache_bytes == 3


@pytest.mark.parametrize(
    ("limit_name", "expected_budget", "body", "extra"),
    [
        ("max_source_bytes", "source_bytes", "value = 1\n", None),
        ("max_ast_nodes", "ast_nodes", "value = 1\n", None),
        (
            "max_closure_edges",
            "closure_edges",
            "from tools import worker\n",
            {"tools/__init__.py": "", "tools/worker.py": "value = 1\n"},
        ),
        (
            "max_observations",
            "observations",
            "from pathlib import Path\nPath('a').touch()\nPath('b').touch()\n",
            None,
        ),
    ],
)
def test_public_report_wires_each_aggregate_budget_fail_closed(
    tmp_path: Path,
    limit_name: str,
    expected_budget: str,
    body: str,
    extra: dict[str, str] | None,
) -> None:
    _deployment(tmp_path, body, extra=extra)
    limits = replace(
        launcher_module.DEFAULT_SCAN_RESOURCE_LIMITS_V2,
        **{limit_name: 1},
    )

    report = report_module.build_report(tmp_path, resource_limits=limits)

    assert report["findings"] == [
        {
            "evidence": f"{expected_budget} exceeds 1",
            "path": ".",
            "rule_id": "resource_budget_exceeded",
        }
    ]


def test_build_report_maps_resource_budget_failure_to_deterministic_red_report(
    tmp_path: Path,
) -> None:
    _deployment(tmp_path, "value = 'x' * 128\n")
    limits = replace(
        launcher_module.DEFAULT_SCAN_RESOURCE_LIMITS_V2,
        max_retained_cache_bytes=1,
    )

    report = report_module.build_report(tmp_path, resource_limits=limits)

    assert report["findings"] == [
        {
            "evidence": "retained_cache_bytes exceeds 1",
            "path": ".",
            "rule_id": "resource_budget_exceeded",
        }
    ]
    assert report["scanner_relative_manifest_agreement"] is False
    assert report["closure_complete"] is False


@pytest.mark.parametrize(
    ("failure", "rule_id"),
    [
        (OSError("denied"), "scanner_resource_failure"),
        (MemoryError(), "scanner_resource_failure"),
        (SystemError("internal"), "scanner_internal_failure"),
    ],
)
def test_build_report_normalizes_expected_scanner_failures(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    failure: BaseException,
    rule_id: str,
) -> None:
    _deployment(tmp_path, "value = 1\n")

    def fail(_root: RepositorySnapshotV2) -> object:
        raise failure

    monkeypatch.setattr(report_module, "_build_report_from_snapshot", fail)

    report = report_module.build_report(tmp_path)

    assert report["findings"] == [
        {
            "evidence": type(failure).__name__,
            "path": ".",
            "rule_id": rule_id,
        }
    ]


def test_constrained_address_space_replay_fails_red_before_large_allocation(
    tmp_path: Path,
) -> None:
    _deployment(tmp_path, "PAYLOAD = " + repr("x" * (512 * 1024)) + "\n")
    script = "\n".join(
        [
            "import json",
            "import resource",
            "import sys",
            "from pathlib import Path",
            "from tools.m6_value_sinks.launchers import DEFAULT_SCAN_RESOURCE_LIMITS_V2",
            "from tools.m6_value_sinks.report import build_report",
            "from dataclasses import replace",
            "limit = 128 * 1024 * 1024",
            "resource.setrlimit(resource.RLIMIT_AS, (limit, limit))",
            "limits = replace(DEFAULT_SCAN_RESOURCE_LIMITS_V2, max_retained_cache_bytes=256 * 1024)",
            "report = build_report(Path(sys.argv[1]), resource_limits=limits)",
            "print(json.dumps(report['findings'], sort_keys=True))",
        ]
    )
    environment = dict(os.environ)
    environment["PYTHONDONTWRITEBYTECODE"] = "1"
    environment["PYTHONPATH"] = str(ROOT)

    completed = subprocess.run(
        [sys.executable, "-B", "-c", script, str(tmp_path)],
        cwd=ROOT,
        env=environment,
        check=True,
        capture_output=True,
        text=True,
    )

    findings = json.loads(completed.stdout)
    assert findings == [
        {
            "evidence": "retained_cache_bytes exceeds 262144",
            "path": ".",
            "rule_id": "resource_budget_exceeded",
        }
    ]


def test_report_separates_scanner_agreement_from_closure_completeness(
    tmp_path: Path,
) -> None:
    _deployment(tmp_path, "from pathlib import Path\nPath('state').touch()\n")
    rendered = render_manifest_v2(tmp_path)
    _manifest(tmp_path, rendered["entries"], rendered["closure_gaps"])

    report = check_m6_value_sinks_v2(tmp_path)

    assert report["scanner_relative_manifest_agreement"] is True, report["findings"]
    assert report["closure_complete"] is False
    assert report["production_authority"] is False
    assert report["release_ready"] is False
    assert report["vm01_status"] == "OPEN"
    assert report["p2_t01_status"] == "OPEN"
    assert report["p2_t02_status"] == "OPEN"


@pytest.mark.parametrize(
    ("expression", "expected_kind"),
    [
        ("getattr(connection, 'execute')('DELETE FROM balances')", "SQL_WRITE"),
        ("vars(connection)['execute']('DELETE FROM balances')", "SQL_WRITE"),
        ("connection.__dict__['execute']('DELETE FROM balances')", "SQL_WRITE"),
        ("getattr(handle, 'truncate')(0)", "TRUNCATE"),
    ],
)
def test_exact_reflective_receiver_writers_are_observed(
    tmp_path: Path, expression: str, expected_kind: str
) -> None:
    _deployment(tmp_path, f"def publish(connection, handle):\n    {expression}\n")

    closure = derive_python_deployment_closure(tmp_path)

    assert [kind for _, _, kind in _observe(tmp_path)] == [expected_kind]
    assert ("tools/node.py", "unresolved_writer_provenance") not in closure.observed_gaps


@pytest.mark.parametrize(
    ("expression", "expected_kind"),
    [
        ("tempfile.__dict__.get('mkdtemp')(dir='.')", "TEMPDIR_CREATE"),
        ("vars(tempfile).get('mkstemp')(dir='.')", "TEMPFILE_CREATE"),
    ],
)
def test_exact_module_dictionary_get_writers_are_observed(
    tmp_path: Path, expression: str, expected_kind: str
) -> None:
    _deployment(
        tmp_path,
        f"import tempfile\n\ndef publish():\n    {expression}\n",
    )

    assert [kind for _, _, kind in _observe(tmp_path)] == [expected_kind]


def test_exact_module_dictionary_get_exec_is_a_typed_executable_gap(
    tmp_path: Path,
) -> None:
    _deployment(
        tmp_path,
        "import builtins\n\ndef publish(payload):\n"
        "    builtins.__dict__.get('exec')(payload)\n",
    )

    closure = derive_python_deployment_closure(tmp_path)

    assert ("tools/node.py", "dynamic_exec") in closure.observed_gaps


@pytest.mark.parametrize(
    ("expression", "expected_kind"),
    [
        (
            "getattr(connection, 'execute', lambda statement: None)"
            "('DELETE FROM balances')",
            "SQL_WRITE",
        ),
        (
            "vars(connection).get('execute', lambda statement: None)"
            "('DELETE FROM balances')",
            "SQL_WRITE",
        ),
    ],
)
def test_reflective_receiver_default_cannot_hide_a_possible_writer(
    tmp_path: Path, expression: str, expected_kind: str
) -> None:
    """D1: an optional reflection fallback never erases the selected writer."""

    _deployment(tmp_path, f"def publish(connection):\n    {expression}\n")

    assert [kind for _, _, kind in _observe(tmp_path)] == [expected_kind]


def test_reflective_builtin_default_keeps_dynamic_exec_gap(tmp_path: Path) -> None:
    """D1: an optional dict.get fallback cannot erase executable provenance."""

    _deployment(
        tmp_path,
        "import builtins\n\ndef publish(payload):\n"
        "    builtins.__dict__.get('exec', lambda value: None)(payload)\n",
    )

    closure = derive_python_deployment_closure(tmp_path)

    assert ("tools/node.py", "dynamic_exec") in closure.observed_gaps


@pytest.mark.parametrize(
    ("call", "expected"),
    [
        ("sqlite3.connect('state.sqlite3')", ["DATABASE_OPEN_WRITE"]),
        ("sqlite3.connect(':memory:')", []),
        ("sqlite3.connect('file:state?mode=memory', uri=True)", []),
        ("sqlite3.connect('file:state?mode=ro', uri=True)", []),
        ("sqlite3.connect('file:state?mode=rw', uri=True)", ["DATABASE_OPEN_WRITE"]),
        ("sqlite3.connect(path)", ["DATABASE_OPEN_UNKNOWN"]),
        ("sqlite3.connect('file:state', uri=dynamic)", ["DATABASE_OPEN_UNKNOWN"]),
    ],
)
def test_sqlite_connect_file_creation_and_uri_boundaries_are_explicit(
    tmp_path: Path, call: str, expected: list[str]
) -> None:
    _deployment(
        tmp_path,
        f"import sqlite3\n\ndef publish(path, dynamic):\n    {call}\n",
    )

    assert [kind for _, _, kind in _observe(tmp_path)] == expected


def test_sqlite_connect_static_writer_has_runtime_file_creation_oracle(
    tmp_path: Path,
) -> None:
    database = tmp_path / "created.sqlite3"
    _deployment(
        tmp_path,
        "import sqlite3\n\ndef publish():\n"
        "    connection = sqlite3.connect('created.sqlite3')\n"
        "    connection.close()\n",
    )

    observed = [kind for _, _, kind in _observe(tmp_path)]
    connection = sqlite3.connect(database)
    connection.close()

    assert observed == ["DATABASE_OPEN_WRITE"]
    assert database.is_file()


@pytest.mark.parametrize("parameter", ["MODE=RO", "IMMUTABLE=1"])
def test_sqlite_uri_parameter_names_are_case_sensitive_at_runtime(
    tmp_path: Path, parameter: str
) -> None:
    """D1: ignored uppercase URI keys retain SQLite's write-capable default."""

    database = tmp_path / f"{parameter.split('=', 1)[0].lower()}.sqlite3"
    uri = f"file:{database}?{parameter}"
    _deployment(
        tmp_path,
        "import sqlite3\n\ndef publish():\n"
        f"    sqlite3.connect({uri!r}, uri=True).close()\n",
    )

    observed = [kind for _, _, kind in _observe(tmp_path)]
    connection = sqlite3.connect(uri, uri=True)
    connection.close()

    assert observed == ["DATABASE_OPEN_WRITE"]
    assert database.is_file()


def test_transaction_commit_is_a_publication_sink_with_runtime_oracle(
    tmp_path: Path,
) -> None:
    """D1: committing caller-supplied work is observable as durable publication."""

    _deployment(tmp_path, "def publish(connection):\n    connection.commit()\n")
    database = tmp_path / "commit.sqlite3"
    writer = sqlite3.connect(database)
    observer = sqlite3.connect(database)
    try:
        writer.execute("CREATE TABLE values_v2 (value INTEGER NOT NULL)")
        writer.commit()
        writer.execute("INSERT INTO values_v2 VALUES (7)")
        before = observer.execute("SELECT COUNT(*) FROM values_v2").fetchone()
        writer.commit()
        after = observer.execute("SELECT COUNT(*) FROM values_v2").fetchone()
    finally:
        observer.close()
        writer.close()

    assert [kind for _, _, kind in _observe(tmp_path)] == ["TRANSACTION_COMMIT"]
    assert before == (0,)
    assert after == (1,)


def test_public_gate_blockers_refuse_forged_or_hostile_reports() -> None:
    class BlindList(list[object]):
        def __iter__(self) -> Iterator[object]:
            return iter(())

    red = report_module._red_failure_report("resource_budget_exceeded", "x")
    apparently_empty = dict(red)
    apparently_empty["findings"] = []
    hostile = dict(red)
    hostile["findings"] = BlindList(red["findings"])
    contradictory = dict(red)
    contradictory["manifest_identity_count"] = 1

    assert gate_blockers(red)
    assert gate_blockers(apparently_empty)
    assert gate_blockers(hostile) == ("report_invalid",)
    assert gate_blockers(contradictory) == ("report_invalid",)
    assert gate_blockers({**red, "unexpected": []}) == ("report_invalid",)


def test_public_report_admission_owns_nested_data_before_use() -> None:
    """D2: caller mutation after admission cannot rewrite the checked report."""

    report = report_module._red_failure_report("resource_budget_exceeded", "x")
    owned = report_module._exact_owned_report_v2(report)

    assert owned is not None
    report["findings"].clear()
    assert owned["findings"] == [
        {
            "evidence": "x",
            "path": ".",
            "rule_id": "resource_budget_exceeded",
        }
    ]


def test_public_report_admission_rejects_shared_container_aliases() -> None:
    """D2: one caller-owned container cannot occupy two semantic report roles."""

    report = report_module._red_failure_report("resource_budget_exceeded", "x")
    shared: list[dict[str, str]] = []
    report["findings"] = shared
    report["declared_closure_gaps"] = shared

    assert gate_blockers(report) == ("report_invalid",)


def test_public_gate_blockers_reject_cyclic_exact_builtin_reports_in_bounded_memory() -> None:
    """D2: exact builtins do not make cyclic or alias-amplified input owned data."""

    script = "\n".join(
        [
            "import resource",
            "from tools.m6_value_sinks.report import _red_failure_report, gate_blockers",
            "limit = 128 * 1024 * 1024",
            "resource.setrlimit(resource.RLIMIT_AS, (limit, limit))",
            "report = _red_failure_report('scanner_resource_failure', 'x')",
            "cycle = []",
            "cycle.extend([cycle] * 1024)",
            "report['findings'] = cycle",
            "print(gate_blockers(report))",
        ]
    )
    environment = dict(os.environ)
    environment["PYTHONDONTWRITEBYTECODE"] = "1"
    environment["PYTHONPATH"] = str(ROOT)

    completed = subprocess.run(
        [sys.executable, "-B", "-c", script],
        cwd=ROOT,
        env=environment,
        check=True,
        capture_output=True,
        text=True,
    )

    assert completed.stdout.strip() == "('report_invalid',)"


def _open_descriptor_set() -> set[int]:
    return {int(name) for name in os.listdir("/proc/self/fd")}


def test_directory_capability_failures_close_every_acquired_descriptor(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    (tmp_path / "child").mkdir()
    snapshot = RepositorySnapshotV2(tmp_path)
    before = _open_descriptor_set()

    def fail_claim(_cache_bytes: int) -> None:
        raise MemoryError

    monkeypatch.setattr(snapshot.resource_meter, "claim_retained", fail_claim)
    try:
        with pytest.raises(MemoryError):
            snapshot._open_directory("child")
        assert _open_descriptor_set() == before
    finally:
        snapshot.close()


def test_directory_capability_dup_failure_closes_opened_descriptor(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    (tmp_path / "child").mkdir()
    snapshot = RepositorySnapshotV2(tmp_path)
    before = _open_descriptor_set()
    real_dup = launcher_module.os.dup
    calls = 0

    def fail_second_dup(descriptor: int) -> int:
        nonlocal calls
        calls += 1
        if calls == 2:
            raise OSError("induced dup failure")
        return real_dup(descriptor)

    monkeypatch.setattr(launcher_module.os, "dup", fail_second_dup)
    try:
        with pytest.raises(OSError, match="induced dup failure"):
            snapshot._open_directory("child")
        assert _open_descriptor_set() == before
    finally:
        snapshot.close()


def test_directory_capability_fstat_failure_closes_opened_descriptor(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    (tmp_path / "child").mkdir()
    snapshot = RepositorySnapshotV2(tmp_path)
    before = _open_descriptor_set()

    def fail_fstat(_descriptor: int) -> os.stat_result:
        raise SystemError("induced fstat failure")

    monkeypatch.setattr(launcher_module.os, "fstat", fail_fstat)
    try:
        with pytest.raises(SystemError, match="induced fstat failure"):
            snapshot._open_directory("child")
        assert _open_descriptor_set() == before
    finally:
        snapshot.close()


def test_directory_capability_budget_refusal_closes_opened_descriptors(
    tmp_path: Path,
) -> None:
    (tmp_path / "child").mkdir()
    limits = launcher_module.ScanResourceLimitsV2(max_retained_descriptors=1)
    snapshot = RepositorySnapshotV2(tmp_path, resource_limits=limits)
    before = _open_descriptor_set()
    try:
        with pytest.raises(launcher_module.ResourceBudgetExceeded):
            snapshot._open_directory("child")
        assert _open_descriptor_set() == before
    finally:
        snapshot.close()


def test_public_resource_failure_report_leaks_no_descriptors(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    (tmp_path / "tools").mkdir()
    before = _open_descriptor_set()

    def fail_claim(
        _meter: launcher_module.ScanResourceMeterV2, _cache_bytes: int
    ) -> None:
        raise MemoryError

    monkeypatch.setattr(
        launcher_module.ScanResourceMeterV2, "claim_retained", fail_claim
    )
    report = report_module.build_report(tmp_path)

    assert report["findings"] == [
        {
            "evidence": "MemoryError",
            "path": ".",
            "rule_id": "scanner_resource_failure",
        }
    ]
    assert _open_descriptor_set() == before


def test_public_constructor_memory_failure_closes_bound_root_descriptor(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """D2: constructor failure transfers no live repository capability."""

    before = _open_descriptor_set()

    def fail_meter(
        _meter: launcher_module.ScanResourceMeterV2,
        _limits: launcher_module.ScanResourceLimitsV2,
    ) -> None:
        raise MemoryError

    monkeypatch.setattr(launcher_module.ScanResourceMeterV2, "__init__", fail_meter)

    report = report_module.build_report(tmp_path)

    assert report["findings"] == [
        {
            "evidence": "MemoryError",
            "path": ".",
            "rule_id": "scanner_resource_failure",
        }
    ]
    assert _open_descriptor_set() == before


def test_regular_file_fstat_failure_closes_opened_descriptor(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """D2: a failed file identity check leaves no unowned descriptor."""

    target = tmp_path / "payload.txt"
    target.write_text("payload", encoding="utf-8")
    snapshot = RepositorySnapshotV2(tmp_path)
    before = _open_descriptor_set()
    real_fstat = launcher_module.os.fstat

    def fail_target_fstat(descriptor: int) -> os.stat_result:
        try:
            if os.readlink(f"/proc/self/fd/{descriptor}") == str(target):
                raise OSError("induced regular-file fstat failure")
        except FileNotFoundError:
            pass
        return real_fstat(descriptor)

    monkeypatch.setattr(launcher_module.os, "fstat", fail_target_fstat)
    try:
        text, error = snapshot.read_bounded_text("payload.txt", 1024)

        assert text is None
        assert error == "induced regular-file fstat failure"
        assert _open_descriptor_set() == before
    finally:
        snapshot.close()
