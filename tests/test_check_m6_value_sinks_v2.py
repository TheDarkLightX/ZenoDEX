"""Evidence for the static-source M6 value-sink inventory.

Obligation: every durable-write operation in the statically reachable closure of
the decoded launcher set carries exactly one manifest classification bound to a
source-derived fingerprint, and every edge the decoder cannot resolve is a typed
closure gap rather than silence.

The counterexample block replays the minimized cases from the independent
coordinator review and the current-head audit. Each is a permanent mutation
killer.
"""

from __future__ import annotations

import hashlib
import json
from pathlib import Path
from typing import cast

import pytest

from tools.check_m6_value_sinks_v2 import (
    check_m6_value_sinks_v2,
    main,
    render_manifest_v2,
    write_manifest_v2,
)
from tools.m6_value_sinks import (
    ClosureGapV2,
    canonical_relative_path,
    combine_fingerprints,
    compare_inventory,
    derive_deployed_entrypoints,
    derive_python_deployment_closure,
    load_closure_gaps,
    load_value_sink_manifest,
    scan_closure,
)

ROOT = Path(__file__).resolve().parents[1]

_INSTALL = 'install_wrapper "zenodex-node" python3 "${repo_dir}/tools/node.py"\n'


def _deployment(
    root: Path, body: str, *, install: str = _INSTALL, extra: dict[str, str] | None = None
) -> None:
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
    return base


def _object_list(value: object) -> list[object]:
    assert isinstance(value, list)
    return value


def _object_rows(value: object) -> list[dict[str, object]]:
    items = _object_list(value)
    assert all(isinstance(item, dict) for item in items)
    return cast(list[dict[str, object]], items)


def _manifest(
    root: Path, entries: list[dict[str, object]], gaps: list[dict[str, str]] | None = None
) -> Path:
    (root / "tools").mkdir(parents=True, exist_ok=True)
    path = root / "tools" / "m6_value_sink_manifest_v2.json"
    path.write_text(
        json.dumps(
            {
                "closure_gaps": gaps or [],
                "entries": entries,
                "schema": "zenodex/m6-value-sink-inventory/v2",
                "scope": "test",
            },
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

    assert report["ok"] is False
    assert any(
        finding["rule_id"] == "unclassified_value_sink" and finding["path"] == "tools/worker.py"
        for finding in _object_rows(report["findings"])
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

    _deployment(
        tmp_path, "from os import replace as move\n\n\ndef publish(a, b):\n    move(a, b)\n"
    )

    assert _observe(tmp_path) == [("tools/node.py", "publish", "ATOMIC_REPLACE")]


def test_module_alias_is_observed(tmp_path: Path) -> None:
    _deployment(tmp_path, "import os as _o\n\n\ndef publish(a, b):\n    _o.replace(a, b)\n")

    assert _observe(tmp_path) == [("tools/node.py", "publish", "ATOMIC_REPLACE")]


def test_path_open_write_mode_is_observed(tmp_path: Path) -> None:
    """Review R3: attribute-form open in a mutating mode is a durable write."""

    _deployment(
        tmp_path, "from pathlib import Path\n\n\ndef publish(path):\n    Path(path).open('w')\n"
    )

    assert _observe(tmp_path) == [("tools/node.py", "publish", "OPEN_WRITE")]


def test_low_level_descriptor_write_is_observed(tmp_path: Path) -> None:
    """Review R3: descriptor writes bypass every path-level operation."""

    _deployment(
        tmp_path,
        "import os\n\n\ndef publish(path):\n"
        "    descriptor = os.open(path, os.O_WRONLY | os.O_CREAT)\n"
        "    os.write(descriptor, b'value')\n",
    )

    assert _observe(tmp_path) == [
        ("tools/node.py", "publish", "DESCRIPTOR_OPEN_WRITE"),
        ("tools/node.py", "publish", "DESCRIPTOR_WRITE"),
    ]


@pytest.mark.parametrize(
    ("body", "expected"),
    [
        ("path.unlink()", "UNLINK"),
        ("path.chmod(0o600)", "PERMISSION_MUTATE"),
        ("path.lchmod(0o600)", "PERMISSION_MUTATE"),
        ("path.rename(other)", "RENAME"),
        ("path.touch()", "PATH_TOUCH"),
    ],
)
def test_receiver_durable_operations_are_observed(tmp_path: Path, body: str, expected: str) -> None:
    """Review R7: receiver syntax must not hide namespace or permission writes."""

    _deployment(tmp_path, f"def publish(path, other):\n    {body}\n")

    assert _observe(tmp_path) == [("tools/node.py", "publish", expected)]


def test_path_lchmod_deployed_writer_mutant_fails_closed(tmp_path: Path) -> None:
    """O-007A mutant: a receiver-form permission writer must reach the gate."""

    _deployment(
        tmp_path,
        "from pathlib import Path\n\n\ndef publish(path):\n    Path(path).lchmod(0o600)\n",
    )
    _manifest(tmp_path, [])

    report = check_m6_value_sinks_v2(tmp_path)

    assert report["ok"] is False
    assert any(
        finding["rule_id"] == "unclassified_value_sink"
        and finding["path"] == "tools/node.py"
        and finding["evidence"] == "publish:PERMISSION_MUTATE:1"
        for finding in _object_rows(report["findings"])
    )


@pytest.mark.parametrize(
    ("flags", "expected"),
    [
        ("os.O_RDONLY", []),
        ("os.O_RDONLY | os.O_DIRECTORY", []),
        ("os.O_WRONLY | os.O_CREAT", ["DESCRIPTOR_OPEN_WRITE"]),
        ("flags", ["DESCRIPTOR_OPEN_UNKNOWN"]),
    ],
)
def test_os_open_flag_authority_is_observed(
    tmp_path: Path, flags: str, expected: list[str]
) -> None:
    """Review R8: descriptor acquisition must distinguish read, write, and unknown flags."""

    _deployment(tmp_path, f"import os\n\n\ndef publish(path, flags):\n    os.open(path, {flags})\n")

    assert [kind for _, _, kind in _observe(tmp_path)] == expected


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


def test_dynamic_sql_is_typed_rather_than_silent(tmp_path: Path) -> None:
    _deployment(
        tmp_path, "def publish(connection, statement):\n    connection.execute(statement)\n"
    )

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


def test_semantic_relocation_changes_the_identity_fingerprint(
    tmp_path: Path, tmp_path_factory: pytest.TempPathFactory
) -> None:
    """Review R6: equal counts must not hide a relocated destination."""

    first_root = tmp_path
    second_root = tmp_path_factory.mktemp("second")
    _deployment(first_root, "import os\n\n\ndef publish(rt, rl, bt, bl):\n    os.replace(rt, rl)\n")
    _deployment(
        second_root, "import os\n\n\ndef publish(rt, rl, bt, bl):\n    os.replace(bt, bl)\n"
    )

    first = scan_closure(first_root, derive_python_deployment_closure(first_root))
    second = scan_closure(second_root, derive_python_deployment_closure(second_root))

    assert [item.identity() for item in first] == [item.identity() for item in second]
    assert combine_fingerprints(tuple(i.fingerprint for i in first)) != combine_fingerprints(
        tuple(i.fingerprint for i in second)
    )


def test_relocated_operation_fails_the_full_gate(tmp_path: Path) -> None:
    _deployment(tmp_path, "import os\n\n\ndef publish(rt, rl, bt, bl):\n    os.replace(rt, rl)\n")
    manifest_path = _manifest(tmp_path, [_entry()])
    emitted = render_manifest_v2(tmp_path)
    entry = _entry(identity_fingerprint=_object_rows(emitted["entries"])[0]["identity_fingerprint"])
    _manifest(tmp_path, [entry])
    assert check_m6_value_sinks_v2(tmp_path)["ok"] is True

    (tmp_path / "tools" / "node.py").write_text(
        "import os\n\n\ndef publish(rt, rl, bt, bl):\n    os.replace(bt, bl)\n", encoding="utf-8"
    )
    report = check_m6_value_sinks_v2(tmp_path)

    assert manifest_path.exists()
    assert report["ok"] is False
    assert any(
        finding["rule_id"] == "operation_fingerprint_mismatch"
        for finding in _object_rows(report["findings"])
    )


def test_authority_control_state_cannot_be_excused_as_non_value(tmp_path: Path) -> None:
    """Review R7: a value-bearing classification may not claim NON_VALUE_EFFECT."""

    path = _manifest(
        tmp_path,
        [
            _entry(
                classification="AUTHORITY_CONTROL_STATE",
                mediation_status="NON_VALUE_EFFECT",
                consumers=["a reader"],
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
    path = _manifest(tmp_path, [_entry(consumers=["a reader"])])

    with pytest.raises(ValueError, match="does not trace them"):
        load_value_sink_manifest(path)


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


def test_unresolvable_module_dispatch_is_unsupported(tmp_path: Path) -> None:
    _deployment(
        tmp_path,
        "import subprocess\n\n\ndef run():\n    subprocess.run(['python3', '-m', 'not.a.module'])\n",
    )

    closure = derive_python_deployment_closure(tmp_path)

    assert ("tools/node.py", "unsupported_subprocess_dispatch") in closure.observed_gaps


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
        f"import subprocess\nfrom subprocess import run as r\n\n\ndef run_it(extra):\n    {call}\n",
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
        ("os", "mkdir", "DIRECTORY_CREATE"),
        ("os", "makedirs", "DIRECTORY_CREATE"),
        ("os", "open", "DESCRIPTOR_OPEN_UNKNOWN"),
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


def test_launcher_symlink_escaping_root_fails_closed(
    tmp_path: Path, tmp_path_factory: pytest.TempPathFactory
) -> None:
    outside = tmp_path_factory.mktemp("outside")
    (outside / "evil.py").write_text(
        "import os\n\n\ndef publish(a, b):\n    os.replace(a, b)\n", encoding="utf-8"
    )
    _deployment(tmp_path, "def run():\n    return None\n")
    (tmp_path / "bin").mkdir()
    (tmp_path / "bin" / "escape").symlink_to(outside / "evil.py")

    entrypoints, findings = derive_deployed_entrypoints(tmp_path)

    assert any(item.rule_id == "launcher_escapes_repository_root" for item in findings)
    assert all("evil.py" not in item.target for item in entrypoints)


def test_dangling_launcher_symlink_fails_closed(tmp_path: Path) -> None:
    _deployment(tmp_path, "def run():\n    return None\n")
    (tmp_path / "bin").mkdir()
    (tmp_path / "bin" / "dangling").symlink_to(tmp_path / "bin" / "absent-target")

    _, findings = derive_deployed_entrypoints(tmp_path)

    assert any(
        item.rule_id in {"launcher_is_not_a_regular_file", "undecodable_launcher"}
        for item in findings
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

    _, findings = derive_deployed_entrypoints(tmp_path)

    assert [item.rule_id for item in findings] == ["launcher_target_unresolvable"]


@pytest.mark.parametrize(
    ("shape", "mechanism"),
    [
        ("escapes_root", "import_target_escapes_root"),
        ("dangling", "import_target_dangling"),
        ("loop", "import_target_unresolvable"),
    ],
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


def test_scan_reads_no_file_outside_the_subject_root(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """Every path the closure opens must resolve inside the supplied root."""

    _deployment(tmp_path, "import os\n\n\ndef publish(a, b):\n    os.replace(a, b)\n")
    opened: list[str] = []
    original = Path.read_bytes

    def _record(self: Path) -> bytes:
        opened.append(str(self.resolve()))
        return original(self)

    monkeypatch.setattr(Path, "read_bytes", _record)
    derive_python_deployment_closure(tmp_path)

    root = str(tmp_path.resolve())
    assert opened
    assert all(item.startswith(root) for item in opened)


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
    (tmp_path / "tools" / "big.py").write_text(
        "x = '" + "a" * (4 * 1024 * 1024 + 8) + "'\n", encoding="utf-8"
    )

    closure = derive_python_deployment_closure(tmp_path)

    assert ("tools/big.py", "source_unscannable") in closure.observed_gaps
    assert "tools/big.py" in closure.unscanned_modules
    assert "tools/big.py" not in closure.modules


def test_unparsable_reachable_source_becomes_a_typed_gap(tmp_path: Path) -> None:
    _deployment(
        tmp_path,
        "import tools.broken\n",
        extra={"tools/__init__.py": "", "tools/broken.py": "def (\n"},
    )

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
    (tmp_path / "Dockerfile").write_text('ENTRYPOINT ["/entrypoint.sh"]\n', encoding="utf-8")
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
    (tmp_path / "bin" / "zenodex-mystery").write_text(
        "#!/bin/sh\nexec ./something-else\n", encoding="utf-8"
    )

    _, findings = derive_deployed_entrypoints(tmp_path)

    assert [(item.rule_id, item.path) for item in findings] == [
        ("undecodable_launcher", "bin/zenodex-mystery")
    ]


def test_undecodable_install_wrapper_is_a_finding(tmp_path: Path) -> None:
    _deployment(
        tmp_path,
        "def run():\n    return None\n",
        install='install_wrapper "n" bash "${repo_dir}/tools/n.sh"\n',
    )

    _, findings = derive_deployed_entrypoints(tmp_path)

    assert [item.rule_id for item in findings] == ["undecodable_install_wrapper"]


def test_missing_launcher_target_is_a_finding(tmp_path: Path) -> None:
    (tmp_path / "scripts").mkdir(parents=True)
    (tmp_path / "scripts" / "install_zenodex.sh").write_text(_INSTALL, encoding="utf-8")

    _, findings = derive_deployed_entrypoints(tmp_path)

    assert [item.rule_id for item in findings] == ["launcher_target_unresolvable"]


def test_absent_install_script_is_a_finding(tmp_path: Path) -> None:
    _, findings = derive_deployed_entrypoints(tmp_path)

    assert [item.rule_id for item in findings] == ["install_script_missing"]


def test_install_script_without_launchers_is_a_finding(tmp_path: Path) -> None:
    (tmp_path / "scripts").mkdir(parents=True)
    (tmp_path / "scripts" / "install_zenodex.sh").write_text(
        "#!/bin/sh\nset -eu\n", encoding="utf-8"
    )

    _, findings = derive_deployed_entrypoints(tmp_path)

    assert [item.rule_id for item in findings] == ["install_script_declares_no_launcher"]


# ---------------------------------------------------------------------------
# Closure-gap ratchet
# ---------------------------------------------------------------------------


def test_new_dynamic_import_breaks_the_gate(tmp_path: Path) -> None:
    _deployment(
        tmp_path, "import importlib\n\n\ndef run(name):\n    return importlib.import_module(name)\n"
    )
    _manifest(tmp_path, [_entry()], gaps=[])

    report = check_m6_value_sinks_v2(tmp_path)

    assert report["ok"] is False
    assert any(
        item["rule_id"] == "undeclared_closure_gap" for item in _object_rows(report["findings"])
    )


def test_stale_declared_gap_breaks_the_gate(tmp_path: Path) -> None:
    _deployment(tmp_path, "import os\n\n\ndef publish(a, b):\n    os.replace(a, b)\n")
    _manifest(
        tmp_path,
        [_entry()],
        gaps=[{"mechanism": "import_module", "path": "tools/node.py", "rationale": "stale"}],
    )

    report = check_m6_value_sinks_v2(tmp_path)

    assert any(item["rule_id"] == "stale_closure_gap" for item in _object_rows(report["findings"]))


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
        (
            {"deployed_reachable": True, "mediation_status": "RESEARCH_UNMOUNTED"},
            "deployed sink as research-only",
        ),
        (
            {"deployed_reachable": False, "mediation_status": "UNMEDIATED_DEPLOYED_WRITER"},
            "undeployed sink as a deployed writer",
        ),
        ({"consumers": ["b", "a"]}, "unique and canonically sorted"),
    ],
)
def test_manifest_entry_rejection(
    tmp_path: Path, overrides: dict[str, object], reason: str
) -> None:
    path = _manifest(tmp_path, [_entry(**overrides)])

    with pytest.raises(ValueError, match=reason):
        load_value_sink_manifest(path)


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
    path = _manifest(
        tmp_path,
        [_entry(path="tools/zzz.py", sink_id="z"), _entry(path="tools/aaa.py", sink_id="a")],
    )

    with pytest.raises(ValueError, match="canonical identity order"):
        load_value_sink_manifest(path)


def test_manifest_rejects_duplicate_sink_ids(tmp_path: Path) -> None:
    path = _manifest(tmp_path, [_entry(symbol="a"), _entry(symbol="b")])

    with pytest.raises(ValueError, match="value sink IDs must be unique"):
        load_value_sink_manifest(path)


# ---------------------------------------------------------------------------
# Repository census
# ---------------------------------------------------------------------------


def test_repository_inventory_is_exact() -> None:
    report = check_m6_value_sinks_v2(ROOT)

    assert report["findings"] == []
    assert report["ok"] is True
    assert report["classified_identity_count"] == 162
    assert report["observed_occurrence_count"] == 181
    assert report["static_scanned_module_count"] == 463


def test_repository_inventory_withholds_authority() -> None:
    report = check_m6_value_sinks_v2(ROOT)

    assert report["release_ready"] is False
    assert report["production_authority"] is False
    assert report["vm01_status"] == "OPEN"
    assert len(_object_list(report["unmediated_static_writers"])) == 54
    assert len(_object_list(report["declared_closure_gaps"])) == 26


def test_repository_reaches_the_container_api_surface() -> None:
    closure = derive_python_deployment_closure(ROOT)

    assert "src/integration/api_server.py" in closure.modules
    assert any(item.target == "-m src.integration.api_server" for item in closure.entrypoints)


def test_repository_records_its_unscanned_reachable_module() -> None:
    report = check_m6_value_sinks_v2(ROOT)

    assert report["static_reachable_unscanned_modules"] == [
        "generated/perp_python/perp_epoch_clearinghouse_3p_transfer_v0_1_ref.py"
    ]


def test_repository_manifest_decodes_and_binds_fingerprints() -> None:
    specs = load_value_sink_manifest(ROOT / "tools" / "m6_value_sink_manifest_v2.json")

    assert len(specs) == 162
    assert all(spec.release_binding is None for spec in specs)
    assert all(len(spec.identity_fingerprint) == 64 for spec in specs)


def test_repository_nonclaims_state_the_inventory_ceiling() -> None:
    report = check_m6_value_sinks_v2(ROOT)

    joined = " ".join(str(item) for item in _object_list(report["nonclaims"]))
    assert "never proof of sole-publisher closure" in joined
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

    assert any(
        item["rule_id"] == "classified_value_sink_missing"
        for item in _object_rows(report["findings"])
    )


def test_main_reports_zero_for_the_repository(capsys: pytest.CaptureFixture[str]) -> None:
    exit_code = main(["--root", str(ROOT)])

    assert exit_code == 0
    assert "VM-01 remains OPEN" in capsys.readouterr().out


def test_main_require_release_ready_fails_closed(capsys: pytest.CaptureFixture[str]) -> None:
    exit_code = main(["--root", str(ROOT), "--require-release-ready"])

    assert exit_code == 1
    assert json.loads(capsys.readouterr().out)["release_ready"] is False


def test_emitted_manifest_marks_a_new_sink_unadjudicated(
    tmp_path: Path, capsys: pytest.CaptureFixture[str]
) -> None:
    _deployment(tmp_path, "import os\n\n\ndef publish(a, b):\n    os.replace(a, b)\n")

    assert main(["--root", str(tmp_path), "--emit-manifest"]) == 0

    emitted = json.loads(capsys.readouterr().out)
    assert emitted["entries"][0]["classification"] == "UNADJUDICATED"
    path = _manifest(tmp_path, emitted["entries"])
    with pytest.raises(ValueError, match=r"entries\[0\]\.classification is unknown"):
        load_value_sink_manifest(path)


def test_atomic_manifest_regeneration_preserves_prior_adjudication(tmp_path: Path) -> None:
    _deployment(tmp_path, "import os\n\n\ndef publish(a, b):\n    os.replace(a, b)\n")
    fingerprint = _object_rows(render_manifest_v2(tmp_path)["entries"])[0]["identity_fingerprint"]
    _manifest(
        tmp_path,
        [
            _entry(
                identity_fingerprint=fingerprint,
                rationale="reviewed exact operation",
                sink_id="reviewed_publish",
            )
        ],
    )

    write_manifest_v2(tmp_path)

    [spec] = load_value_sink_manifest(tmp_path / "tools" / "m6_value_sink_manifest_v2.json")
    assert spec.classification == "DURABLE_VALUE_STATE"
    assert spec.mediation_status == "UNMEDIATED_DEPLOYED_WRITER"
    assert spec.rationale == "reviewed exact operation"
    assert spec.sink_id == "reviewed_publish"


def test_atomic_manifest_regeneration_preserves_malformed_prior_bytes(tmp_path: Path) -> None:
    _deployment(tmp_path, "import os\n\n\ndef publish(a, b):\n    os.replace(a, b)\n")
    manifest_path = tmp_path / "tools" / "m6_value_sink_manifest_v2.json"
    malformed = b'{"schema":"zenodex/m6-value-sink-inventory/v2"}\n'
    manifest_path.write_bytes(malformed)

    with pytest.raises(ValueError):
        write_manifest_v2(tmp_path)

    assert manifest_path.read_bytes() == malformed
    assert not manifest_path.with_name(f".{manifest_path.name}.candidate").exists()


def test_atomic_manifest_regeneration_requires_exact_external_prior_digest(tmp_path: Path) -> None:
    _deployment(tmp_path, "import os\n\n\ndef publish(a, b):\n    os.replace(a, b)\n")
    fingerprint = _object_rows(render_manifest_v2(tmp_path)["entries"])[0]["identity_fingerprint"]
    prior_path = tmp_path / "reviewed-prior.json"
    current_path = _manifest(tmp_path, [_entry(rationale="current reviewed manifest")])
    prior_path.write_text(
        current_path.read_text(encoding="utf-8")
        .replace("current reviewed manifest", "digest-pinned reviewed prior")
        .replace("f" * 64, str(fingerprint)),
        encoding="utf-8",
    )
    current_bytes = current_path.read_bytes()

    with pytest.raises(ValueError, match="SHA-256 mismatch"):
        write_manifest_v2(
            tmp_path,
            prior_manifest=prior_path,
            prior_manifest_sha256="0" * 64,
        )

    assert current_path.read_bytes() == current_bytes

    write_manifest_v2(
        tmp_path,
        prior_manifest=prior_path,
        prior_manifest_sha256=hashlib.sha256(prior_path.read_bytes()).hexdigest(),
    )
    [spec] = load_value_sink_manifest(current_path)
    assert spec.rationale == "digest-pinned reviewed prior"
