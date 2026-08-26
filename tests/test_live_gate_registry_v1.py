from __future__ import annotations

import os
import sys
import time
from collections.abc import Iterator
from pathlib import Path

import pytest

import tools.live_gate_registry_v1 as registry_module
from tools.live_gate_registry_v1 import (
    LIVE_GATE_REGISTRY,
    MAX_LIVE_GATE_TIMEOUT_SECONDS,
    ChildScanV1,
    GitObjectPresenceV1,
    LiveGateSpecV1,
    ProcessBoundsV1,
    ProcessRunV1,
    enable_child_subreaper_v1,
    gate_environment_v1,
    git_commit_object_probe_v1,
    git_v1,
    live_gate_preflight_v1,
    observe_live_gate_v1,
    project_observed_value_v1,
    reap_escaped_descendants_v1,
    run_bounded_process_v1,
)

ROOT = Path(__file__).resolve().parents[1]


def test_registry_is_closed_sorted_python_only_and_points_at_real_tools() -> None:
    # Arrange / Act / Assert
    assert list(LIVE_GATE_REGISTRY) == sorted(LIVE_GATE_REGISTRY)
    for spec in LIVE_GATE_REGISTRY.values():
        assert spec.argv[0] == "python3"
        assert spec.checker_path == spec.argv[1]
        assert spec.checker_path.startswith("tools/") and spec.checker_path.endswith(".py")
        assert (ROOT / spec.checker_path).is_file()
        assert 1 <= spec.timeout_seconds <= MAX_LIVE_GATE_TIMEOUT_SECONDS
        assert (spec.output_format == "json") or spec.observed_projection == ()


def test_registry_mapping_rejects_runtime_mutation() -> None:
    """Same-process callers cannot insert, remove, replace, or clear gates."""

    gate_id = next(iter(LIVE_GATE_REGISTRY))
    spec = LIVE_GATE_REGISTRY[gate_id]
    operations = (
        lambda: LIVE_GATE_REGISTRY.__setitem__("forged", spec),  # type: ignore[attr-defined]
        lambda: LIVE_GATE_REGISTRY.__delitem__(gate_id),  # type: ignore[attr-defined]
        lambda: LIVE_GATE_REGISTRY.clear(),  # type: ignore[attr-defined]
        lambda: LIVE_GATE_REGISTRY.update({"forged": spec}),  # type: ignore[attr-defined]
    )

    for operation in operations:
        with pytest.raises((AttributeError, TypeError)):
            operation()
    assert LIVE_GATE_REGISTRY[gate_id] is spec
    assert "forged" not in LIVE_GATE_REGISTRY


def test_foreign_or_lookalike_spec_cannot_be_observed(tmp_path: Path) -> None:
    # Arrange: a look-alike copy of a real entry that would drop a marker if executed.
    marker = tmp_path / "marker"
    real = LIVE_GATE_REGISTRY["m6_asset_precision_policy"]
    lookalike = LiveGateSpecV1(
        real.gate_id,
        ("python3", "-c", f"open({str(marker)!r}, 'w').write('x')"),
        real.checker_path,
        real.output_format,
        real.observed_projection,
        real.timeout_seconds,
    )

    # Act / Assert
    with pytest.raises(ValueError, match="registry entry"):
        observe_live_gate_v1(lookalike, ROOT)
    with pytest.raises(ValueError, match="registry entry"):
        observe_live_gate_v1(LiveGateSpecV1("zz_fake", ("python3", "tools/fake.py"), "tools/fake.py", "json", (), 1), ROOT)
    assert not marker.exists()


def test_environment_is_explicit_and_carries_no_ambient_secrets() -> None:
    # Act
    env = gate_environment_v1(ROOT)

    # Assert
    assert env["PATH"] == "/usr/bin:/bin"
    assert env["HOME"] == "/nonexistent"
    assert env["PYTHONNOUSERSITE"] == "1"
    assert env["GIT_CONFIG_GLOBAL"] == "/dev/null"
    assert env["GIT_NO_REPLACE_OBJECTS"] == "1"
    assert env["PYTHONPATH"] == str(ROOT.resolve())
    assert set(env) == {
        "PATH", "HOME", "XDG_CONFIG_HOME", "LANG", "LC_ALL", "GIT_CONFIG_NOSYSTEM",
        "GIT_CONFIG_GLOBAL", "GIT_NO_REPLACE_OBJECTS", "GIT_TERMINAL_PROMPT", "PYTHONPATH", "PYTHONNOUSERSITE",
        "PYTHONHASHSEED", "PYTHONDONTWRITEBYTECODE", "PYTHONIOENCODING",
    }


def test_hostile_parent_python_path_never_reaches_the_child(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path
) -> None:
    # Arrange: Mallory controls the parent's PYTHONPATH and sys.path.
    hostile = tmp_path / "hostile_site"
    hostile.mkdir()
    monkeypatch.setenv("PYTHONPATH", str(hostile))
    monkeypatch.syspath_prepend(str(hostile))
    monkeypatch.setenv("PYTHONUSERBASE", str(tmp_path / "hostile_user"))

    # Act
    env = gate_environment_v1(ROOT)
    child = run_bounded_process_v1(
        [sys.executable, "-c", "import sys; print('\\n'.join(sys.path))"],
        cwd=tmp_path,
        env=env,
        bounds=ProcessBoundsV1(30, 65536),
    )

    # Assert: the explicit environment and the child's actual search path exclude the hostile entries.
    assert env["PYTHONPATH"] == str(ROOT.resolve())
    assert str(hostile) not in " ".join(env.values())
    assert child.error == ""
    child_path = child.stdout.decode("utf-8").splitlines()
    assert str(ROOT.resolve()) in child_path
    assert str(hostile) not in child_path
    assert not any("hostile_user" in entry for entry in child_path)


def test_tracked_path_hook_trigger_is_refused_before_any_gate_runs(tmp_path: Path) -> None:
    # Arrange: a temporary root carrying the tracked sitecustomize.py and the ignored trigger directory.
    root = tmp_path / "root"
    root.mkdir()
    (root / "sitecustomize.py").write_text(
        (ROOT / "sitecustomize.py").read_text(encoding="utf-8"), encoding="utf-8"
    )
    trigger = root / "external" / "ESSO"
    trigger.mkdir(parents=True)
    spec = LIVE_GATE_REGISTRY["m6_asset_precision_policy"]

    # Act: reproduce the hazard with the raw bounded runner, then probe the gate boundary.
    hazard = run_bounded_process_v1(
        [sys.executable, "-c", "import sys; print('\\n'.join(sys.path))"],
        cwd=root,
        env=gate_environment_v1(root),
        bounds=ProcessBoundsV1(30, 65536),
    )
    refused = observe_live_gate_v1(spec, root)
    errors_present = live_gate_preflight_v1(root)
    trigger.rmdir()
    errors_absent = live_gate_preflight_v1(root)

    # Assert: PYTHONPATH=root alone lets the hook widen the child path; the preflight refuses to run.
    assert hazard.error == ""
    assert str(trigger.resolve()) in hazard.stdout.decode("utf-8").splitlines()
    assert errors_present == [
        "live gate preflight: external/ESSO is present under the root and the tracked "
        "sitecustomize.py would insert it into child sys.path"
    ]
    assert refused.error == errors_present[0]
    assert refused.exit_code == -1 and refused.observed == {}
    assert errors_absent == []
    assert live_gate_preflight_v1(ROOT) == []


def test_path_hook_preflight_refuses_the_exact_exdev_anchor_branch(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    # Arrange: inject the exact typed result produced when openat2 translates
    # kernel EXDEV at an ignored ancestor mount boundary.
    root = tmp_path / "root"
    root.mkdir()
    anchored = registry_module.AnchoredDirectoryV1.open(root)
    marker = tmp_path / "child.marker"
    spec = LIVE_GATE_REGISTRY["m6_asset_precision_policy"]

    def exdev_probe(
        _self: object, relative: str
    ) -> registry_module.AnchoredPathProbeV1:
        assert relative == "external/ESSO"
        return registry_module.AnchoredPathProbeV1(
            registry_module.AnchoredPathStateV1.REFUSED,
            "mount boundary crossed at 'external'",
        )

    monkeypatch.setattr(registry_module.AnchoredDirectoryV1, "probe", exdev_probe)

    # Act
    try:
        errors = live_gate_preflight_v1(anchored)
        observed = observe_live_gate_v1(spec, anchored)
    finally:
        anchored.close()

    # Assert: EXDEV/AnchorRefused is a typed refusal and no child side effect can run.
    assert errors == [
        "live gate preflight: external/ESSO could not be proved absent under the anchored root: "
        "mount boundary crossed at 'external'"
    ]
    assert observed.exit_code == -1 and observed.error == errors[0]
    assert not marker.exists()


def test_supervisor_code_cannot_be_substituted_by_a_root_pathname_twin(
    tmp_path: Path,
) -> None:
    # Arrange: run this attack in a fresh interpreter so the old lazy supervisor
    # root has not already been opened. The held working root remains the real
    # inode while its pathname temporarily names a malicious twin.
    import json
    import subprocess
    import textwrap

    root = tmp_path / "root"
    parked = tmp_path / "root.anchored"
    twin = tmp_path / "twin"
    for directory in (root / "tools", twin / "tools"):
        directory.mkdir(parents=True)
        (directory / "__init__.py").write_text("", encoding="utf-8")
    for relative in (
        Path("tools/bounded_json_v1.py"),
        Path("tools/live_gate_registry_v1.py"),
    ):
        (root / relative).write_bytes((ROOT / relative).read_bytes())
    spec = LIVE_GATE_REGISTRY["m6_asset_precision_policy"]
    real_marker = tmp_path / "real.marker"
    forged_marker = tmp_path / "forged.marker"
    real_output = {
        "ok": True,
        "decimal_places": 18,
        "atoms_per_display_unit": 10**18,
        "policy_root": "root-twin-regression",
    }
    checker = root / spec.checker_path
    checker.parent.mkdir(parents=True, exist_ok=True)
    checker.write_text(
        "if __package__ is not None:\n"
        "    raise RuntimeError('sealed execution changed direct-script package semantics')\n"
        "import json\n"
        "from pathlib import Path\n"
        f"Path({str(real_marker)!r}).write_text('real', encoding='utf-8')\n"
        f"print(json.dumps({real_output!r}, sort_keys=True))\n",
        encoding="utf-8",
    )
    forged_stdout = json.dumps(real_output, sort_keys=True).encode("utf-8")
    (twin / "tools/live_gate_registry_v1.py").write_text(
        "import base64, json, os, sys\n"
        "from pathlib import Path\n"
        "def supervise_main():\n"
        "    json.loads(sys.stdin.buffer.read())\n"
        f"    Path({str(forged_marker)!r}).write_text('forged', encoding='utf-8')\n"
        "    response = {'error': '', 'escaped_descendants': 0, 'exit_code': 0, "
        f"'stdout_b64': base64.b64encode({forged_stdout!r}).decode('ascii')"
        "}\n"
        "    sys.stdout.write(json.dumps(response, sort_keys=True))\n"
        "    sys.stdout.flush()\n"
        "    os._exit(0)\n",
        encoding="utf-8",
    )
    runner = textwrap.dedent(
        """
        import json
        import os
        from pathlib import Path
        import sys

        root, parked, twin, real_marker, forged_marker = map(Path, sys.argv[1:])
        sys.path.insert(0, str(root))
        from tools.live_gate_registry_v1 import AnchoredDirectoryV1, LIVE_GATE_REGISTRY, observe_live_gate_v1

        anchored = AnchoredDirectoryV1.open(root)
        original_identity = (anchored.device, anchored.inode)
        os.rename(root, parked)
        os.rename(twin, root)
        try:
            replacement = root.stat()
            observed = observe_live_gate_v1(
                LIVE_GATE_REGISTRY["m6_asset_precision_policy"], anchored
            )
            print(json.dumps({
                "different_identity": original_identity != (replacement.st_dev, replacement.st_ino),
                "error": observed.error,
                "exit_code": observed.exit_code,
                "real_marker": real_marker.exists(),
                "forged_marker": forged_marker.exists(),
            }, sort_keys=True))
        finally:
            anchored.close()
            os.rename(root, twin)
            os.rename(parked, root)
        """
    )

    # Act
    run = subprocess.run(
        [
            sys.executable,
            "-I",
            "-c",
            runner,
            str(root),
            str(parked),
            str(twin),
            str(real_marker),
            str(forged_marker),
        ],
        check=False,
        capture_output=True,
        text=True,
        timeout=60,
    )

    # Assert: only the supervisor held from the original root may run.
    assert run.returncode == 0, run.stderr
    result = json.loads(run.stdout)
    assert result == {
        "different_identity": True,
        "error": "",
        "exit_code": 0,
        "forged_marker": False,
        "real_marker": True,
    }


def test_sealed_execution_never_adds_tools_directory_to_import_path(
    tmp_path: Path,
) -> None:
    # Arrange: adding root/tools ahead of the standard library would let this
    # sibling json.py execute in either the supervisor or checker interpreter.
    root = tmp_path / "root"
    (root / "tools").mkdir(parents=True)
    for relative in (
        Path("tools/__init__.py"),
        Path("tools/bounded_json_v1.py"),
        Path("tools/live_gate_registry_v1.py"),
    ):
        (root / relative).write_bytes((ROOT / relative).read_bytes())
    marker = tmp_path / "hostile-tools-json.marker"
    (root / "tools/json.py").write_text(
        "from pathlib import Path\n"
        f"Path({str(marker)!r}).write_text('executed', encoding='utf-8')\n"
        "raise RuntimeError('hostile tools/json.py executed')\n",
        encoding="utf-8",
    )
    spec = LIVE_GATE_REGISTRY["m6_asset_precision_policy"]
    checker = root / spec.checker_path
    checker.parent.mkdir(parents=True, exist_ok=True)
    checker.write_text(
        "import json\n"
        "print(json.dumps({"
        "'ok': True, 'decimal_places': 18, "
        "'atoms_per_display_unit': 10**18, "
        "'policy_root': 'no-sibling-shadowing'"
        "}, sort_keys=True))\n",
        encoding="utf-8",
    )

    # Act
    with registry_module.AnchoredDirectoryV1.open(root) as anchored:
        observed = observe_live_gate_v1(spec, anchored)

    # Assert: only the descriptor-rooted repository root is added. Bare json
    # therefore resolves to the standard library, never root/tools/json.py.
    assert observed.error == "" and observed.exit_code == 0
    assert observed.observed["policy_root"] == "no-sibling-shadowing"
    assert not marker.exists()


@pytest.mark.parametrize(
    "gate_id",
    (
        "m6_asset_precision_policy",
        "m6_value_sinks",
        "value_movement_closure_status",
    ),
)
def test_root_only_sealed_execution_matches_direct_script_import_semantics(
    gate_id: str,
) -> None:
    # Arrange: these three live gates historically branched on __package__.
    # Direct execution has no repository PYTHONPATH and therefore exercises
    # each package-first import's narrow sibling fallback.
    import json
    import subprocess

    spec = LIVE_GATE_REGISTRY[gate_id]
    direct_env = {
        **registry_module.PROCESS_ENVIRONMENT_BASE,
        "PYTHONNOUSERSITE": "1",
        "PYTHONHASHSEED": "0",
        "PYTHONDONTWRITEBYTECODE": "1",
        "PYTHONIOENCODING": "utf-8",
    }
    direct = subprocess.run(
        [sys.executable, *spec.argv[1:]],
        cwd=ROOT,
        env=direct_env,
        check=False,
        capture_output=True,
        timeout=spec.timeout_seconds,
    )

    # Act: sealed execution keeps __package__=None and adds only the anchored
    # repository root, so the canonical tools.* import succeeds first.
    with registry_module.AnchoredDirectoryV1.open(ROOT) as anchored:
        sealed = observe_live_gate_v1(spec, anchored)
    direct_payload = json.loads(direct.stdout)
    direct_observed = {
        key: project_observed_value_v1(direct_payload, key)
        for key in spec.observed_projection
    }

    # Assert: neither model hits an import failure and their registry-visible
    # exit code and projection are identical.
    assert b"ModuleNotFoundError" not in direct.stderr
    assert sealed.error == ""
    assert direct.returncode == sealed.exit_code
    assert direct_observed == sealed.observed


def test_transient_supervisor_inode_rewrite_executes_only_the_sealed_snapshot(
    tmp_path: Path,
) -> None:
    # Arrange: a fresh interpreter binds the real registry, then an exact hook
    # rewrites that same source inode immediately before the supervisor child
    # reads it. The hostile source restores the original before returning a
    # forged response, defeating mutable-fd pre/post hashing.
    import json
    import subprocess
    import textwrap

    root = tmp_path / "root"
    (root / "tools").mkdir(parents=True)
    for relative in (
        Path("tools/__init__.py"),
        Path("tools/bounded_json_v1.py"),
        Path("tools/live_gate_registry_v1.py"),
    ):
        (root / relative).write_bytes((ROOT / relative).read_bytes())
    registry_path = root / "tools/live_gate_registry_v1.py"
    original_registry = registry_path.read_text(encoding="utf-8")
    spec = LIVE_GATE_REGISTRY["m6_asset_precision_policy"]
    real_marker = tmp_path / "real-supervisor.marker"
    forged_marker = tmp_path / "forged-supervisor.marker"
    real_output = {
        "ok": True,
        "decimal_places": 18,
        "atoms_per_display_unit": 10**18,
        "policy_root": "sealed-supervisor-regression",
    }
    checker = root / spec.checker_path
    checker.parent.mkdir(parents=True, exist_ok=True)
    checker.write_text(
        "import json\n"
        "from pathlib import Path\n"
        f"Path({str(real_marker)!r}).write_text('real', encoding='utf-8')\n"
        f"print(json.dumps({real_output!r}, sort_keys=True))\n",
        encoding="utf-8",
    )
    forged_stdout = json.dumps(real_output, sort_keys=True).encode("utf-8")
    transient_source = (
        "import base64, json, os, sys\n"
        "from pathlib import Path\n"
        f"_ORIGINAL = {original_registry!r}\n"
        "def supervise_main():\n"
        "    json.loads(sys.stdin.buffer.read())\n"
        f"    Path({str(registry_path)!r}).write_text(_ORIGINAL, encoding='utf-8')\n"
        f"    Path({str(forged_marker)!r}).write_text('forged', encoding='utf-8')\n"
        "    response = {'error': '', 'escaped_descendants': 0, 'exit_code': 0, "
        f"'stdout_b64': base64.b64encode({forged_stdout!r}).decode('ascii')"
        "}\n"
        "    sys.stdout.write(json.dumps(response, sort_keys=True))\n"
        "    sys.stdout.flush()\n"
        "    os._exit(0)\n"
    )
    runner = textwrap.dedent(
        """
        import json
        from pathlib import Path
        import sys

        root, registry_path, real_marker, forged_marker, transient_path = map(Path, sys.argv[1:])
        sys.path.insert(0, str(root))
        import tools.live_gate_registry_v1 as registry

        original = registry_path.read_text(encoding="utf-8")
        transient = transient_path.read_text(encoding="utf-8")
        anchored = registry.AnchoredDirectoryV1.open(root)
        real_run = registry._run_plain_process
        rewritten = False

        def rewrite_then_run(argv, **kwargs):
            global rewritten
            if not rewritten:
                registry_path.write_text(transient, encoding="utf-8")
                rewritten = True
            return real_run(argv, **kwargs)

        registry._run_plain_process = rewrite_then_run
        try:
            observed = registry.observe_live_gate_v1(
                registry.LIVE_GATE_REGISTRY["m6_asset_precision_policy"], anchored
            )
            print(json.dumps({
                "error": observed.error,
                "exit_code": observed.exit_code,
                "forged_marker": forged_marker.exists(),
                "real_marker": real_marker.exists(),
                "rewritten": rewritten,
            }, sort_keys=True))
        finally:
            registry_path.write_text(original, encoding="utf-8")
            anchored.close()
        """
    )
    transient_path = tmp_path / "transient_registry.py"
    transient_path.write_text(transient_source, encoding="utf-8")

    # Act
    run = subprocess.run(
        [
            sys.executable,
            "-I",
            "-c",
            runner,
            str(root),
            str(registry_path),
            str(real_marker),
            str(forged_marker),
            str(transient_path),
        ],
        check=False,
        capture_output=True,
        text=True,
        timeout=60,
    )

    # Assert: the real supervisor snapshot may run; transient source never does.
    assert run.returncode == 0, run.stderr
    result = json.loads(run.stdout)
    assert result["rewritten"] is True
    assert result["forged_marker"] is False
    assert result["real_marker"] is True
    assert "supervisor source changed in place" in result["error"]


def _process_alive(pid: int) -> bool:
    try:
        stat_line = Path(f"/proc/{pid}/stat").read_text(encoding="utf-8")
    except OSError:
        return False
    state = stat_line.rsplit(")", 1)[1].split()[0]
    return state not in {"Z", "X"}


def _pidfd_for(pid: int, cmdline_marker: str) -> int | None:
    """A pidfd for ``pid`` only if its command line still carries ``cmdline_marker``; ``None`` if it is gone or reused."""

    try:
        fd = os.pidfd_open(pid)
    except OSError:
        return None
    try:
        cmdline = Path(f"/proc/{pid}/cmdline").read_bytes()
    except OSError:
        os.close(fd)
        return None
    if cmdline_marker.encode("utf-8") not in cmdline:
        os.close(fd)
        return None
    return fd


def _pidfd_exited(fd: int) -> bool:
    import select

    poller = select.poll()
    poller.register(fd, select.POLLIN)
    return bool(poller.poll(0))


def _pidfd_kill_and_release(fd: int) -> None:
    """SIGKILL through the pidfd (exact process, never a reused pid), wait for exit, reap if ours, close."""

    import signal

    try:
        try:
            signal.pidfd_send_signal(fd, signal.SIGKILL)
        except ProcessLookupError:
            pass
        deadline = time.monotonic() + 5
        while not _pidfd_exited(fd) and time.monotonic() < deadline:
            time.sleep(0.02)
        try:
            os.waitid(os.P_PIDFD, fd, os.WEXITED | os.WNOHANG)
        except ChildProcessError:
            pass
    finally:
        os.close(fd)


def test_timeout_kills_the_whole_process_group_including_descendants(tmp_path: Path) -> None:
    # Arrange: a child that spawns a grandchild holding the pipes, then both sleep.
    pid_file = tmp_path / "grandchild.pid"
    grandchild = (
        "import os, time; open(%r, 'w').write(str(os.getpid())); time.sleep(60)" % str(pid_file)
    )
    child_program = (
        "import os, subprocess, sys, time\n"
        f"subprocess.Popen([sys.executable, '-c', {grandchild!r}])\n"
        f"while not os.path.exists({str(pid_file)!r}):\n"
        "    time.sleep(0.01)\n"
        "time.sleep(60)\n"
    )

    # Act
    run = run_bounded_process_v1(
        [sys.executable, "-c", child_program],
        cwd=tmp_path,
        env=gate_environment_v1(ROOT),
        bounds=ProcessBoundsV1(2, 65536),
    )
    grandchild_pid = int(pid_file.read_text(encoding="utf-8"))
    deadline = time.monotonic() + 5
    while _process_alive(grandchild_pid) and time.monotonic() < deadline:
        time.sleep(0.02)

    # Assert: the bounded run reports the timeout and the descendant is dead, not orphaned.
    assert run.error == "process exceeded the timeout"
    assert not _process_alive(grandchild_pid)


@pytest.mark.parametrize("daemon_closes_pipes", [True, False], ids=["daemon_closes_pipes", "daemon_holds_pipes"])
def test_setsid_daemon_grandchild_is_reparented_killed_and_its_observation_refused(
    daemon_closes_pipes: bool, tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    # Arrange: the child double-forks a daemon that calls setsid (outside the child's process group) and exits 0.
    pid_file = tmp_path / "daemon.pid"
    release_pipes = "    os.closerange(0, 3)\n" if daemon_closes_pipes else ""
    program = (
        "import os, sys, time\n"
        "if os.fork() == 0:\n"
        "    os.setsid()\n"
        f"{release_pipes}"
        f"    open({str(pid_file)!r}, 'w').write(str(os.getpid()))\n"
        "    time.sleep(60)\n"
        f"while not os.path.exists({str(pid_file)!r}):\n"
        "    time.sleep(0.01)\n"
        "sys.exit(0)\n"
    )

    # Act
    assert enable_child_subreaper_v1() == ""
    run = run_bounded_process_v1(
        [sys.executable, "-c", program], cwd=tmp_path, env=gate_environment_v1(ROOT), bounds=ProcessBoundsV1(2, 65536)
    )
    daemon_pid = int(pid_file.read_text(encoding="utf-8"))
    monkeypatch.setattr(registry_module, "run_bounded_process_v1", lambda *_args, **_kwargs: ProcessRunV1(0, b"{}", "", 1))
    refused = observe_live_gate_v1(LIVE_GATE_REGISTRY["m6_asset_precision_policy"], ROOT)

    # Assert: the daemon outlived its process group, was reparented here, killed, and counted, whether it released
    # the pipes (clean exit) or held them (bounded timeout); the gate result is refused either way.
    assert not _process_alive(daemon_pid)
    assert run.escaped_descendants == 1
    if daemon_closes_pipes:
        assert run.error == "" and run.exit_code == 0
    else:
        assert run.error == "process exceeded the timeout" and run.exit_code == -1
    assert reap_escaped_descendants_v1(frozenset(registry_module._scan_children(os.getpid()).children)) == (0, "")
    assert "leaked 1 descendant" in refused.error and refused.observed == {}


def test_child_enumeration_failure_is_typed_and_never_a_silent_containment_claim(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    # Arrange: a program that would drop a marker if it ran; enumeration fails before the run, then after it.
    marker = tmp_path / "marker"
    argv = [sys.executable, "-c", f"open({str(marker)!r}, 'w').write('x')"]
    env, bounds = gate_environment_v1(ROOT), ProcessBoundsV1(10, 1024)
    real_scan = registry_module._scan_children
    monkeypatch.setattr(registry_module, "_scan_children", lambda _pid: ChildScanV1({}, "/proc enumeration failed: PermissionError"))
    contained = registry_module._run_contained_process  # the containment core exactly as the supervisor process runs it

    # Act: refused before any spawn.
    refused_before = contained(argv, cwd=str(tmp_path), env=env, bounds=bounds, pass_fds=())
    marker_after_refusal = marker.exists()
    calls: list[int] = []

    def failing_after_run(pid: int) -> ChildScanV1:
        calls.append(pid)
        return real_scan(pid) if len(calls) == 1 else ChildScanV1({}, "/proc record for pid is unreadable or malformed")

    monkeypatch.setattr(registry_module, "_scan_children", failing_after_run)
    unverifiable_after = contained(argv, cwd=str(tmp_path), env=env, bounds=bounds, pass_fds=())
    monkeypatch.setattr(registry_module, "_scan_children", real_scan)
    healthy = real_scan(os.getpid())

    # Assert: both failures are typed, the second run's completed output is discarded, and the real scan works.
    assert refused_before.exit_code == -1 and refused_before.error.startswith("descendant containment unavailable")
    assert not marker_after_refusal
    assert unverifiable_after.exit_code == -1 and unverifiable_after.error.startswith("descendant containment unverifiable")
    assert unverifiable_after.stdout == b"" and marker.exists()
    assert healthy.error == "" and os.getpid() not in healthy.children


@pytest.mark.parametrize("children_file", ["kernel_list", "forced_fallback"])
def test_live_child_with_unreadable_proc_record_is_still_contained(children_file: str, monkeypatch: pytest.MonkeyPatch) -> None:
    # Arrange: a real sleeping child whose /proc stat record is made unreadable; pid 1 is made unreadable too.
    # The second variant forces the /proc enumeration fallback regardless of kernel children-file support.
    import subprocess

    child = subprocess.Popen([sys.executable, "-c", "import time; time.sleep(60)"], stdin=subprocess.DEVNULL)
    real_stat_fields = registry_module._stat_fields
    monkeypatch.setattr(registry_module, "_stat_fields", lambda pid: None if pid in {child.pid, 1} else real_stat_fields(pid))
    if children_file == "forced_fallback":
        monkeypatch.setattr(registry_module, "_listed_children", lambda _pid: None)
    try:
        # Act
        scan = registry_module._scan_children(os.getpid())
        killed, error = reap_escaped_descendants_v1(frozenset(scan.children) - {child.pid}, deadline_seconds=5.0)
        deadline = time.monotonic() + 5
        while _process_alive(child.pid) and time.monotonic() < deadline:
            time.sleep(0.02)
    finally:
        child.kill()
        child.wait(timeout=5)

    # Assert: the unreadable live child is reported by parentage and killed; the unrelated unreadable pid is not claimed.
    assert scan.error == "" and scan.children.get(child.pid) == "?" and 1 not in scan.children
    assert (killed, error) == (1, "")
    assert not _process_alive(child.pid)


def test_anchored_directory_pins_child_cwd_search_path_preflight_and_git_to_the_inode(tmp_path: Path) -> None:
    # Arrange: a real directory anchored, then its pathname swapped to a twin that carries the path-hook trigger.
    original, twin = tmp_path / "root", tmp_path / "twin"
    for base in (original, twin):
        base.mkdir()
        (base / "marker.py").write_text(f"NAME = {base.name!r}\n", encoding="utf-8")
    (twin / "external" / "ESSO").mkdir(parents=True)
    original_inode = os.stat(original).st_ino
    anchored = registry_module.AnchoredDirectoryV1.open(original)
    moved = tmp_path / "moved"
    original.rename(moved)
    twin.rename(original)
    try:
        # Act
        env = gate_environment_v1(anchored)
        expected_child_path = anchored.child_path
        preflight_anchored = live_gate_preflight_v1(anchored)
        preflight_pathname = live_gate_preflight_v1(original)
        probe = run_bounded_process_v1(
            [sys.executable, "-c", "import os, marker; print(os.stat('.').st_ino, marker.NAME, os.readlink('/proc/self/cwd'))"],
            cwd=anchored,
            env=env,
            bounds=ProcessBoundsV1(30, 4096),
        )
        swapped_pathname = registry_module.AnchoredDirectoryV1.open(original)
        swapped_identity = (swapped_pathname.device, swapped_pathname.inode)
        swapped_pathname.close()
    finally:
        original.rename(twin)
        moved.rename(original)
        anchored.close()

    # Assert: the child ran in the anchored inode with the anchored search path; the pathname view saw the twin.
    inode, name, cwd = probe.stdout.decode("utf-8").split()
    assert probe.error == "" and int(inode) == original_inode and name == "root" and cwd == str(moved)
    assert env["PYTHONPATH"] == expected_child_path == f"/proc/self/fd/{expected_child_path.rsplit('/', 1)[1]}"
    assert preflight_anchored == []
    assert preflight_pathname and "external/ESSO" in preflight_pathname[0]
    assert swapped_identity != (anchored.device, anchored.inode)
    assert not anchored.is_open
    with pytest.raises(registry_module.AnchorRefused):
        anchored.stat("marker.py")
    closed_run = run_bounded_process_v1([sys.executable, "-c", "pass"], cwd=anchored, env=gate_environment_v1(ROOT), bounds=ProcessBoundsV1(5, 64))
    assert closed_run.error == "process could not start: anchored directory or file is closed"
    link = tmp_path / "link"
    os.symlink(original, link)
    with pytest.raises(registry_module.AnchorRefused, match="symlink"):
        registry_module.AnchoredDirectoryV1.open(link)
    nested = tmp_path / "nested"
    nested.mkdir()
    with pytest.raises(registry_module.AnchorRefused, match="symlink"):
        registry_module.AnchoredDirectoryV1.open(link / "nested-through-link")


def test_openat2_policy_is_kernel_enforced_and_support_is_probed_exactly_once(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    # Arrange
    assert registry_module.openat2_support_v1() == ""
    assert registry_module.SUBTREE_RESOLVE == 0x0F and registry_module.ROOT_PATH_RESOLVE == 0x06
    slash = registry_module.AnchoredDirectoryV1.open(Path("/"))
    repo = registry_module.AnchoredDirectoryV1.open(tmp_path)
    (tmp_path / "real").mkdir()
    (tmp_path / "real" / "file.txt").write_text("x\n", encoding="utf-8")
    os.symlink(tmp_path / "real", tmp_path / "link")

    # Act / Assert: a mount crossing below the root, a symlink component, and a parent escape are kernel refusals.
    try:
        with pytest.raises(registry_module.AnchorRefused, match="mount boundary crossed at 'proc'"):
            slash.stat("proc/self/stat")
        exdev_probe = slash.probe("proc/self/stat")
        assert exdev_probe.state is registry_module.AnchoredPathStateV1.REFUSED
        assert "mount boundary crossed at 'proc'" in exdev_probe.reason
        with pytest.raises(registry_module.AnchorRefused, match="mount boundary crossed at 'proc'"):
            slash.exists("proc/self/stat")
        with pytest.raises(registry_module.AnchorRefused, match="symlink refused at 'link'"):
            repo.stat("link/file.txt")
        with pytest.raises(registry_module.AnchorRefused, match="not a canonical"):
            repo.stat("../escape")
        assert repo.exists("real/file.txt") and not repo.exists("real/missing")
        with repo.open_file("real/file.txt") as held:
            assert held.size == 2 and held.rehash() == held.sha256
    finally:
        slash.close()
        repo.close()
    monkeypatch.setattr(registry_module, "_OPENAT2_SUPPORT", ["openat2 with the required resolve flags is unavailable on this kernel (probe)"])
    with pytest.raises(registry_module.AnchorRefused, match="unavailable"):
        registry_module.AnchoredDirectoryV1.open(tmp_path)


def test_open_file_post_seal_failure_closes_both_new_descriptors(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    # Arrange: force the verification read which occurs after the sealed memfd
    # was created to fail. The root descriptor itself remains owned by the test.
    source = tmp_path / "checker.py"
    source.write_text("print('bounded')\n", encoding="utf-8")
    anchored = registry_module.AnchoredDirectoryV1.open(tmp_path)
    before = set(os.listdir("/proc/self/fd"))

    def fail_post_seal_hash(_descriptor: int) -> str:
        raise OSError("injected post-seal verification failure")

    monkeypatch.setattr(registry_module, "_hash_descriptor", fail_post_seal_hash)

    # Act / Assert: neither the source fd nor sealed memfd remains open.
    try:
        with pytest.raises(OSError, match="post-seal verification failure"):
            anchored.open_file(source.name)
        assert set(os.listdir("/proc/self/fd")) == before
    finally:
        anchored.close()


def test_open_file_sealed_copy_failure_closes_source_and_memfd(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    # Arrange: fail inside the copy after memfd_create but before ownership can
    # be returned to AnchoredFileV1.
    source = tmp_path / "checker.py"
    source.write_text("print('bounded')\n", encoding="utf-8")
    anchored = registry_module.AnchoredDirectoryV1.open(tmp_path)
    before = set(os.listdir("/proc/self/fd"))

    def fail_sealed_write(_descriptor: int, _data: object) -> int:
        raise OSError("injected sealed copy failure")

    monkeypatch.setattr(registry_module.os, "write", fail_sealed_write)

    # Act / Assert: the inner memfd and outer source descriptor both unwind.
    try:
        with pytest.raises(OSError, match="sealed copy failure"):
            anchored.open_file(source.name)
        assert set(os.listdir("/proc/self/fd")) == before
    finally:
        anchored.close()


def test_anchored_file_close_attempts_sealed_fd_when_source_close_raises(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    # Arrange: inject an error after the mutable source fd has actually closed.
    # The sealed executable fd must still be closed by the finally branch.
    source = tmp_path / "checker.py"
    source.write_text("print('bounded')\n", encoding="utf-8")
    anchored = registry_module.AnchoredDirectoryV1.open(tmp_path)
    held = anchored.open_file(source.name)
    source_fd = held._descriptor
    sealed_fd = held._sealed_descriptor
    real_close = os.close
    closed: list[int] = []

    def close_with_source_failure(descriptor: int) -> None:
        closed.append(descriptor)
        real_close(descriptor)
        if descriptor == source_fd:
            raise OSError("injected source close failure")

    monkeypatch.setattr(registry_module.os, "close", close_with_source_failure)

    # Act / Assert: ownership is cleared and both real descriptors are closed.
    try:
        with pytest.raises(OSError, match="source close failure"):
            held.close()
        assert closed[:2] == [source_fd, sealed_fd]
        assert not held.is_open
        with pytest.raises(OSError):
            os.fstat(source_fd)
        with pytest.raises(OSError):
            os.fstat(sealed_fd)
    finally:
        anchored.close()


def test_parent_death_guard_is_installed_fail_closed(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    # Arrange: the containment core in-process (as the supervisor runs it); prctl for PR_SET_PDEATHSIG is made to fail.
    real_prctl = registry_module._LIBC.prctl
    env, bounds = gate_environment_v1(ROOT), ProcessBoundsV1(10, 4096)
    marker = tmp_path / "marker"
    argv = [sys.executable, "-c", f"open({str(marker)!r}, 'w').write('x')"]

    def failing_pdeathsig(option: int, *args: object) -> int:
        return -1 if option == registry_module._PR_SET_PDEATHSIG else int(real_prctl(option, *args))

    monkeypatch.setattr(registry_module._LIBC, "prctl", failing_pdeathsig)

    # Act: the refused run is observed before the accepted control (which writes the same marker); the prctl
    # monkeypatch is restored and PDEATHSIG reset in a finally so no failed assertion can leave pytest configured.
    try:
        refused = registry_module._run_contained_process(argv, cwd=str(tmp_path), env=env, bounds=bounds, pass_fds=())
        refused_marker_exists = marker.exists()
        monkeypatch.setattr(registry_module._LIBC, "prctl", real_prctl)
        with pytest.raises(RuntimeError, match="supervisor died before"):
            registry_module._die_with_parent(expected_parent=1 if os.getppid() != 1 else 2)
        real_prctl(registry_module._PR_SET_PDEATHSIG, 0, 0, 0, 0)
        accepted = registry_module._run_contained_process(argv, cwd=str(tmp_path), env=env, bounds=bounds, pass_fds=())
    finally:
        monkeypatch.setattr(registry_module._LIBC, "prctl", real_prctl)
        real_prctl(registry_module._PR_SET_PDEATHSIG, 0, 0, 0, 0)

    # Assert: a guard that cannot be installed or a parent already replaced aborts before exec (no marker), typed;
    # with the guard installed the child runs normally and only then does the marker exist.
    assert refused.exit_code == -1 and "parent-death guard aborted the child before exec" in refused.error
    assert not refused_marker_exists
    assert accepted.error == "" and accepted.exit_code == 0 and marker.exists()


def test_gate_that_kills_its_supervisor_is_a_typed_failure_and_its_escaped_descendant_is_the_stated_residual(tmp_path: Path) -> None:
    # Arrange: the gate starts a new-session descendant, then kills its own supervisor and lingers.
    import subprocess

    gate_pid_file, escapee_pid_file = tmp_path / "gate.pid", tmp_path / "escapee.pid"
    escapee = f"import os, time; open({str(escapee_pid_file)!r}, 'w').write(str(os.getpid())); time.sleep(60)"
    program = (
        "import os, signal, subprocess, sys, time\n"
        f"open({str(gate_pid_file)!r}, 'w').write(str(os.getpid()))\n"
        f"subprocess.Popen([sys.executable, '-c', {escapee!r}], stdin=subprocess.DEVNULL, start_new_session=True)\n"
        f"while not os.path.exists({str(escapee_pid_file)!r}):\n"
        "    time.sleep(0.01)\n"
        "os.kill(os.getppid(), signal.SIGKILL)\n"
        "time.sleep(30)\n"
    )

    # Act: each process is captured as a pidfd (identity-checked against its own command line) the moment its pid
    # is known; liveness, the kill, and the wait all go through the pidfd, never through a reusable integer pid,
    # and one enclosing finally releases every process this test caused.
    cleanup: list[int] = []
    gate_fd = escapee_fd = None
    escapee_alive = None
    try:
        run = run_bounded_process_v1([sys.executable, "-c", program], cwd=tmp_path, env=gate_environment_v1(ROOT), bounds=ProcessBoundsV1(10, 65536))
        for pid_file in (gate_pid_file, escapee_pid_file):
            deadline = time.monotonic() + 5
            while not pid_file.exists() and time.monotonic() < deadline:
                time.sleep(0.02)
        if gate_pid_file.exists():
            gate_fd = _pidfd_for(int(gate_pid_file.read_text(encoding="utf-8")), str(gate_pid_file))
            if gate_fd is not None:
                cleanup.append(gate_fd)
        if escapee_pid_file.exists():
            escapee_fd = _pidfd_for(int(escapee_pid_file.read_text(encoding="utf-8")), str(escapee_pid_file))
            if escapee_fd is not None:
                cleanup.append(escapee_fd)
        deadline = time.monotonic() + 5
        while gate_fd is not None and not _pidfd_exited(gate_fd) and time.monotonic() < deadline:
            time.sleep(0.02)
        gate_exited = gate_fd is None or _pidfd_exited(gate_fd)
        escapee_alive = escapee_fd is not None and not _pidfd_exited(escapee_fd)
    finally:
        for fd in cleanup:
            _pidfd_kill_and_release(fd)

    # Assert: typed parent-side failure stating the orphan residual and that nothing is killed by pid; the direct
    # gate child died only through best-effort PDEATHSIG; the new-session descendant survived, exactly as the
    # nonclaim states (no cgroup, PID namespace, or external sandbox here).
    assert run.exit_code == -1 and run.error.startswith("supervisor lost")
    assert "may be orphaned" in run.error and "nothing is killed by pid" in run.error
    assert gate_exited
    assert escapee_alive is True
    assert subprocess.run([sys.executable, "-c", "print('checker process still spawns normally')"], capture_output=True, check=False).returncode == 0


def test_witness_unrelated_child_of_the_checker_process_survives_gate_containment(tmp_path: Path) -> None:
    # Max ae889ac4 counterexample 4: a subprocess created concurrently by another thread was classified as an
    # escaped descendant, killed, and reaped.
    import subprocess
    import threading

    results: dict[str, ProcessRunV1] = {}
    pid_file = tmp_path / "daemon.pid"
    env = gate_environment_v1(ROOT)

    def leaking_run() -> None:
        results["run"] = run_bounded_process_v1(
            [sys.executable, "-c", _leaking_program(pid_file, linger_seconds=0.8)], cwd=tmp_path, env=env, bounds=ProcessBoundsV1(10, 65536)
        )

    thread = threading.Thread(target=leaking_run)

    # Act: the leaking run starts first and lingers; an unrelated child of this process is created while it is
    # in flight, so it exists when the run's containment reaps.
    thread.start()
    time.sleep(0.2)
    unrelated = subprocess.Popen([sys.executable, "-c", "import time; time.sleep(30)"], stdin=subprocess.DEVNULL)
    try:
        thread.join(timeout=60)
        unrelated_state = unrelated.poll()
        daemon_pid = int(pid_file.read_text(encoding="utf-8"))
    finally:
        unrelated.kill()
        unrelated.wait(timeout=5)

    # Assert: the gate's own daemon was contained and counted; the unrelated child was never touched.
    assert not thread.is_alive()
    assert results["run"].error == "" and results["run"].escaped_descendants == 1
    assert not _process_alive(daemon_pid)
    assert unrelated_state is None


def _leaking_program(pid_file: Path, linger_seconds: float = 0.0) -> str:
    """A child that double-forks a setsid daemon (pipes released), lingers, and exits 0 once the daemon is up."""

    return (
        "import os, sys, time\n"
        "if os.fork() == 0:\n"
        "    os.setsid()\n"
        "    os.closerange(0, 3)\n"
        f"    open({str(pid_file)!r}, 'w').write(str(os.getpid()))\n"
        "    time.sleep(60)\n"
        f"while not os.path.exists({str(pid_file)!r}):\n"
        "    time.sleep(0.01)\n"
        f"time.sleep({linger_seconds!r})\n"
        "sys.exit(0)\n"
    )


def test_two_concurrent_leaking_runs_each_account_for_their_own_daemon(tmp_path: Path) -> None:
    # Arrange: two threads start leaking runs at the same time; without exclusive supervisor ownership one run
    # could collect the other's reparented daemon and report zero leakage.
    import threading

    results: dict[str, ProcessRunV1] = {}
    pid_files = {name: tmp_path / f"{name}.pid" for name in ("a", "b")}
    env = gate_environment_v1(ROOT)

    def run(name: str) -> None:
        results[name] = run_bounded_process_v1(
            [sys.executable, "-c", _leaking_program(pid_files[name])], cwd=tmp_path, env=env, bounds=ProcessBoundsV1(5, 65536)
        )

    threads = [threading.Thread(target=run, args=(name,)) for name in pid_files]

    # Act
    for thread in threads:
        thread.start()
    for thread in threads:
        thread.join(timeout=60)
    daemons = {name: int(path.read_text(encoding="utf-8")) for name, path in pid_files.items()}

    # Assert: both runs completed, each accounts for exactly its own daemon, and both daemons are dead.
    assert not any(thread.is_alive() for thread in threads)
    assert {name: (run.error, run.exit_code, run.escaped_descendants) for name, run in results.items()} == {
        "a": ("", 0, 1),
        "b": ("", 0, 1),
    }
    assert not any(_process_alive(pid) for pid in daemons.values())


def test_delayed_empty_scan_past_the_deadline_is_a_typed_error(monkeypatch: pytest.MonkeyPatch) -> None:
    # Arrange: enumeration returns no children but only after the deadline has passed.
    def delayed_empty_scan(_pid: int) -> ChildScanV1:
        time.sleep(0.06)
        return ChildScanV1({}, "")

    monkeypatch.setattr(registry_module, "_scan_children", delayed_empty_scan)

    # Act
    killed, error = reap_escaped_descendants_v1(frozenset(), deadline_seconds=0.05)

    # Assert: never a success once the deadline is exceeded, even with nothing found.
    assert killed == 0 and error == "descendant containment unverifiable: enumeration exceeded the 0.05 s deadline"


def _fake_proc_record(pid: int, total_bytes: int) -> bytes:
    head = f"{pid} (fixture) S 1 {pid} {pid} 0 -1 4194560".encode("ascii")
    assert len(head) <= total_bytes
    return head + b" 0" * ((total_bytes - len(head)) // 2) + b" " * ((total_bytes - len(head)) % 2)


def test_proc_enumeration_entry_and_record_byte_ceilings_are_exact(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    # Arrange: a fake /proc without a children file (forcing the scan) whose own record sits at the byte ceiling.
    own = os.getpid()
    fake_proc = tmp_path / "proc"
    (fake_proc / str(own)).mkdir(parents=True)
    limit = registry_module._MAX_PROC_RECORD_BYTES
    (fake_proc / str(own) / "stat").write_bytes(_fake_proc_record(own, limit))
    fixture_pids = [2**22 + offset for offset in (1, 2, 3)]  # beyond pid_max, so never equal to own or any live pid
    assert own not in fixture_pids
    for pid in fixture_pids[:2]:
        (fake_proc / str(pid)).mkdir()
    monkeypatch.setattr(registry_module, "_PROC_ROOT", fake_proc)
    monkeypatch.setattr(registry_module, "_MAX_PROC_ENTRIES", 3)

    # Act
    at_entry_ceiling = registry_module._scan_children(own)
    (fake_proc / str(fixture_pids[2])).mkdir()
    over_entry_ceiling = registry_module._scan_children(own)
    (fake_proc / str(fixture_pids[2])).rmdir()
    (fake_proc / str(own) / "stat").write_bytes(_fake_proc_record(own, limit + 1))
    over_record_ceiling = registry_module._scan_children(own)

    # Assert: exactly at the ceilings the scan succeeds with no children; one beyond is a typed enumeration error.
    assert at_entry_ceiling == ChildScanV1({}, "")
    assert over_entry_ceiling.children == {} and "exceeded the 3 entry ceiling" in over_entry_ceiling.error
    assert over_record_ceiling.children == {} and "unreadable or malformed" in over_record_ceiling.error


def test_proc_enumeration_stops_pulling_entries_at_the_ceiling_plus_one(monkeypatch: pytest.MonkeyPatch) -> None:
    # Arrange: an unbounded stream of numeric entries that records how many were pulled.
    pulled: list[int] = []

    def endless_entries() -> Iterator[str]:
        number = 1
        while True:
            pulled.append(number)
            yield str(number)
            number += 1

    monkeypatch.setattr(registry_module, "_numeric_proc_entries", endless_entries)
    monkeypatch.setattr(registry_module, "_MAX_PROC_ENTRIES", 5)

    # Act
    candidates, error = registry_module._scanned_candidates(os.getpid())

    # Assert: the consumer refused on item MAX+1 and never retained more than MAX entries.
    assert candidates == [] and error == "/proc enumeration exceeded the 5 entry ceiling"
    assert pulled == [1, 2, 3, 4, 5, 6]


def test_child_that_never_reaps_is_a_typed_bounded_containment_error(monkeypatch: pytest.MonkeyPatch) -> None:
    # Arrange: enumeration keeps reporting a live child at a pid beyond pid_max, so kill and reap never resolve it.
    phantom = 2**22 + 7
    monkeypatch.setattr(registry_module, "_scan_children", lambda _pid: ChildScanV1({phantom: "D"}, ""))

    # Act
    started = time.monotonic()
    killed, error = reap_escaped_descendants_v1(frozenset(), deadline_seconds=0.3)
    elapsed = time.monotonic() - started

    # Assert: bounded by the deadline, never blocking, and a typed incomplete-containment error.
    assert killed == 1 and error.startswith("descendant containment incomplete: 1 child process(es) unresolved")
    assert 0.3 <= elapsed < 2.0
    assert not _process_alive(phantom)


def test_child_that_closes_its_pipes_and_completes_after_the_bound_is_a_timeout_with_no_grace(tmp_path: Path) -> None:
    # Arrange: the child releases stdout/stderr immediately (so the drain sees EOF) and then outlives the bound.
    late = [sys.executable, "-c", "import os, time; os.closerange(1, 3); time.sleep(1.4)"]
    prompt = [sys.executable, "-c", "import os, time; os.closerange(1, 3); time.sleep(0.2)"]
    env = gate_environment_v1(ROOT)

    # Act
    started = time.monotonic()
    late_run = run_bounded_process_v1(late, cwd=tmp_path, env=env, bounds=ProcessBoundsV1(1, 1024))
    late_elapsed = time.monotonic() - started
    prompt_run = run_bounded_process_v1(prompt, cwd=tmp_path, env=env, bounds=ProcessBoundsV1(1, 1024))

    # Assert: completion after the deadline is a typed timeout returned at the deadline, not a success after a grace second.
    assert late_run.error == "process exceeded the timeout" and late_run.exit_code == -1
    assert late_elapsed < 1.35
    assert prompt_run.error == "" and prompt_run.exit_code == 0


def test_bounded_process_capture_rejects_oversized_output_timeout_and_missing_binary(tmp_path: Path) -> None:
    # Arrange
    env = gate_environment_v1(ROOT)
    flood = [sys.executable, "-c", "import sys; sys.stdout.write('x' * 2048)"]
    stall = [sys.executable, "-c", "import time; time.sleep(30)"]
    good = [sys.executable, "-c", "import sys; sys.stdout.write('ok'); sys.stderr.write('e'); sys.exit(3)"]

    # Act
    flooded = run_bounded_process_v1(flood, cwd=tmp_path, env=env, bounds=ProcessBoundsV1(30, 2047))
    exact = run_bounded_process_v1(flood, cwd=tmp_path, env=env, bounds=ProcessBoundsV1(30, 2048))
    stalled = run_bounded_process_v1(stall, cwd=tmp_path, env=env, bounds=ProcessBoundsV1(1, 1024))
    finished = run_bounded_process_v1(good, cwd=tmp_path, env=env, bounds=ProcessBoundsV1(30, 1024))
    missing = run_bounded_process_v1(["/nonexistent/binary"], cwd=tmp_path, env=env, bounds=ProcessBoundsV1(1, 1))

    # Assert
    assert flooded.error == "process output exceeds the bound" and flooded.stdout == b""
    assert exact.error == "" and exact.stdout == b"x" * 2048
    assert stalled.error == "process exceeded the timeout"
    assert finished.error == "" and finished.exit_code == 3 and finished.stdout == b"ok"
    assert missing.error.startswith("process could not start")


def test_git_runs_from_trusted_binary_with_minimal_environment() -> None:
    # Act
    code, head = git_v1(ROOT, ["rev-parse", "HEAD"])
    bad_code, bad_out = git_v1(ROOT, ["cat-file", "-e", "0" * 40 + "^{commit}"])

    # Assert
    assert code == 0 and len(head) == 40
    assert bad_code != 0 and bad_out == ""


def test_git_commit_object_probe_distinguishes_presence_and_absence() -> None:
    # Arrange
    code, head = git_v1(ROOT, ["rev-parse", "HEAD"])
    assert code == 0

    # Act
    present = git_commit_object_probe_v1(ROOT, head)
    absent = git_commit_object_probe_v1(ROOT, "0" * 40)

    # Assert
    assert present.state is GitObjectPresenceV1.PRESENT and present.reason == ""
    assert absent.state is GitObjectPresenceV1.ABSENT and absent.reason == ""


@pytest.mark.parametrize("exit_code", (1, 128))
def test_git_commit_object_probe_never_downgrades_fatal_exit_to_absence(
    exit_code: int, monkeypatch: pytest.MonkeyPatch
) -> None:
    # Arrange
    monkeypatch.setattr(
        registry_module,
        "_run_plain_process",
        lambda *_args, **_kwargs: ProcessRunV1(
            exit_code,
            b"",
            "",
            0,
            b"fatal: injected object database failure\n",
        ),
    )

    # Act
    result = git_commit_object_probe_v1(ROOT, "0" * 40)

    # Assert
    assert result.state is GitObjectPresenceV1.QUERY_FAILED
    assert result.reason != ""


def test_git_commit_object_probe_rejects_malformed_or_wrong_type_response(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    # Arrange
    oid = "0" * 40
    monkeypatch.setattr(
        registry_module,
        "_run_plain_process",
        lambda *_args, **_kwargs: ProcessRunV1(0, f"{oid} blob\n".encode(), ""),
    )

    # Act
    malformed = git_commit_object_probe_v1(ROOT, oid)
    invalid_oid = git_commit_object_probe_v1(ROOT, "0" * 39)

    # Assert
    assert malformed.state is GitObjectPresenceV1.QUERY_FAILED
    assert invalid_oid.state is GitObjectPresenceV1.QUERY_FAILED


def test_anchored_file_hash_and_read_do_not_mutate_shared_offsets() -> None:
    with registry_module.AnchoredDirectoryV1.open(ROOT) as anchored:
        with anchored.open_file("tools/live_gate_registry_v1.py") as source:
            os.lseek(source._descriptor, 7, os.SEEK_SET)
            os.lseek(source._sealed_descriptor, 11, os.SEEK_SET)

            assert source.rehash() == source.sha256
            assert source.read(source.size) is not None
            assert os.lseek(source._descriptor, 0, os.SEEK_CUR) == 7
            assert os.lseek(source._sealed_descriptor, 0, os.SEEK_CUR) == 11


@pytest.mark.parametrize(
    "args",
    (
        ["-C", "/tmp", "rev-parse", "HEAD"],
        ["--git-dir=/tmp/other", "rev-parse", "HEAD"],
        ["-c", "alias.escape=!true", "escape"],
        ["status", "--porcelain=v2", "--work-tree=/tmp"],
    ),
)
def test_git_refuses_root_redirection_and_unregistered_commands(
    args: list[str],
) -> None:
    code, output = git_v1(ROOT, args)

    assert code == -1
    assert output == ""


def test_registry_gate_observation_is_bounded_json_projection() -> None:
    # Arrange
    spec = LIVE_GATE_REGISTRY["m6_asset_precision_policy"]

    # Act
    observation = observe_live_gate_v1(spec, ROOT)

    # Assert
    assert observation.error == ""
    assert observation.exit_code == 0
    assert set(observation.observed) == set(spec.observed_projection)
    assert observation.observed["decimal_places"] == 8


def test_projection_grammar_handles_length_mapping_and_missing_fields() -> None:
    # Arrange
    value = {"findings": [{"rule_id": "a"}, {"rule_id": "b"}], "ok": False}

    # Act / Assert
    assert project_observed_value_v1(value, "ok") is False
    assert project_observed_value_v1(value, "findings#len") == 2
    assert project_observed_value_v1(value, "findings[].rule_id") == ["a", "b"]
    with pytest.raises(ValueError, match="missing field"):
        project_observed_value_v1(value, "absent")
    with pytest.raises(ValueError, match="#len"):
        project_observed_value_v1(value, "ok#len")
    with pytest.raises(ValueError, match="is not a list"):
        project_observed_value_v1(value, "ok[].x")
