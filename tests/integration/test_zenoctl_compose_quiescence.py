from __future__ import annotations

import subprocess
import json
from dataclasses import dataclass
from pathlib import Path

import pytest

from tools.zenoctl_testnet_local import compose as cm

PROJECT = "zenodex-local-quarantine"
COMPOSE_FILE = Path("docker-compose.local.yml")
CONTAINER_ID = "a" * 64
PROFILE_ID = "local-testnet-retired-bridge-quarantine-v1"
PROFILE_DIGEST = "sha256:" + "b" * 64


@dataclass(frozen=True)
class _Outcome:
    returncode: int
    stdout: str | None = None
    stderr: str | None = None


@dataclass(frozen=True)
class _RunCall:
    command: tuple[str, ...]
    capture_output: bool


def _install_subprocess_script(
    monkeypatch: pytest.MonkeyPatch,
    outcomes: list[_Outcome],
) -> list[_RunCall]:
    scripted = list(outcomes)
    calls: list[_RunCall] = []

    def fake_run(
        command: list[str],
        *,
        env: dict[str, str] | None,
        check: bool,
        capture_output: bool,
        text: bool,
    ) -> subprocess.CompletedProcess[str]:
        if check:
            raise AssertionError("compose._run must apply its own strict return-code check")
        if not text:
            raise AssertionError("compose._run must request text output")
        if not scripted:
            raise AssertionError(f"unexpected subprocess call: {command!r}")
        calls.append(_RunCall(tuple(command), capture_output))
        outcome = scripted.pop(0)
        return subprocess.CompletedProcess(
            args=command,
            returncode=outcome.returncode,
            stdout=outcome.stdout,
            stderr=outcome.stderr,
        )

    monkeypatch.setattr(cm.subprocess, "run", fake_run)
    return calls


def _compose_down(*, remove_volumes: bool = False) -> None:
    cm.compose_down(
        engine=cm.ComposeEngine(binary="docker"),
        project_name=PROJECT,
        compose_files=[COMPOSE_FILE],
        remove_volumes=remove_volumes,
    )


def _inspect_record(*, environment: list[str] | None = None) -> dict[str, object]:
    return {
        "Id": CONTAINER_ID,
        "Config": {
            "Image": "zenodex/operator-tools:local",
            "Labels": {
                "com.docker.compose.project": PROJECT,
                "com.docker.compose.service": "zenodex-api",
                "io.zenodex.local-operator-profile-id": PROFILE_ID,
                "io.zenodex.local-operator-profile-digest": PROFILE_DIGEST,
            },
            "Env": environment
            or [
                "PERPS_WALLET_API_ENABLED=false",
                "ZUSD_TAU_WALLET_API_ENABLED=false",
                "ZUSD_MONETARY_WALLET_API_ENABLED=false",
            ],
        },
    }


def test_compose_down_rejects_nonzero_shutdown_before_query(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    calls = _install_subprocess_script(
        monkeypatch,
        [_Outcome(returncode=17, stderr="down failed")],
    )

    with pytest.raises(RuntimeError, match=r"command failed \(exit 17\)"):
        _compose_down()

    if len(calls) != 1:
        raise AssertionError(f"expected only the failed down call, got {calls!r}")


def test_compose_down_rejects_surviving_project_container_ids(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    calls = _install_subprocess_script(
        monkeypatch,
        [
            _Outcome(returncode=0),
            _Outcome(returncode=0, stdout=f"{CONTAINER_ID}\n"),
        ],
    )

    with pytest.raises(RuntimeError, match="still has 1 container") as caught:
        _compose_down()

    if CONTAINER_ID not in str(caught.value):
        raise AssertionError("survivor error omitted the canonical container ID")
    if len(calls) != 2:
        raise AssertionError(f"expected down and survivor query, got {calls!r}")


def test_compose_down_rejects_container_query_failure(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    _install_subprocess_script(
        monkeypatch,
        [
            _Outcome(returncode=0),
            _Outcome(returncode=125, stdout="", stderr="daemon unavailable"),
        ],
    )

    with pytest.raises(RuntimeError, match=r"command failed \(exit 125\)") as caught:
        _compose_down()
    if "daemon unavailable" not in str(caught.value):
        raise AssertionError("query failure omitted the subprocess diagnostic")


@pytest.mark.parametrize(
    "malformed_output",
    [
        None,
        "short-id\n",
        f"{'A' * 64}\n",
        f" {CONTAINER_ID}\n",
        CONTAINER_ID,
        f"{CONTAINER_ID}\n\n",
        f"{CONTAINER_ID}\n{CONTAINER_ID}\n",
    ],
)
def test_compose_down_rejects_malformed_container_query_output(
    monkeypatch: pytest.MonkeyPatch,
    malformed_output: str | None,
) -> None:
    _install_subprocess_script(
        monkeypatch,
        [
            _Outcome(returncode=0),
            _Outcome(returncode=0, stdout=malformed_output),
        ],
    )

    with pytest.raises(RuntimeError, match="container query returned"):
        _compose_down()


def test_compose_down_accepts_canonical_zero_survivor_result(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    calls = _install_subprocess_script(
        monkeypatch,
        [
            _Outcome(returncode=0),
            _Outcome(returncode=0, stdout=""),
        ],
    )

    _compose_down(remove_volumes=True)

    expected = [
        _RunCall(
            (
                "docker",
                "compose",
                "-p",
                PROJECT,
                "-f",
                str(COMPOSE_FILE),
                "down",
                "--remove-orphans",
                "-v",
            ),
            False,
        ),
        _RunCall(
            (
                "docker",
                "ps",
                "--all",
                "--quiet",
                "--no-trunc",
                "--filter",
                f"label=com.docker.compose.project={PROJECT}",
            ),
            True,
        ),
    ]
    if calls != expected:
        raise AssertionError(f"unexpected compose quiescence commands: {calls!r}")


def test_inspect_project_containers_decodes_owned_typed_snapshot(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    _install_subprocess_script(
        monkeypatch,
        [
            _Outcome(returncode=0, stdout=f"{CONTAINER_ID}\n"),
            _Outcome(returncode=0, stdout=json.dumps([_inspect_record()])),
        ],
    )

    snapshots = cm.inspect_project_containers(
        engine=cm.ComposeEngine(binary="docker"),
        project_name=PROJECT,
    )

    assert len(snapshots) == 1
    snapshot = snapshots[0]
    assert snapshot.container_id == CONTAINER_ID
    assert snapshot.compose_service == "zenodex-api"
    assert snapshot.profile_id == PROFILE_ID
    assert snapshot.profile_digest == PROFILE_DIGEST
    assert snapshot.environment_value("PERPS_WALLET_API_ENABLED") == "false"


def test_inspect_project_containers_rejects_duplicate_environment_names(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    _install_subprocess_script(
        monkeypatch,
        [
            _Outcome(returncode=0, stdout=f"{CONTAINER_ID}\n"),
            _Outcome(
                returncode=0,
                stdout=json.dumps(
                    [
                        _inspect_record(
                            environment=[
                                "PERPS_WALLET_API_ENABLED=false",
                                "PERPS_WALLET_API_ENABLED=true",
                            ]
                        )
                    ]
                ),
            ),
        ],
    )

    with pytest.raises(RuntimeError, match="duplicate name"):
        cm.inspect_project_containers(
            engine=cm.ComposeEngine(binary="docker"),
            project_name=PROJECT,
        )


def test_inspect_project_containers_rejects_query_inspect_set_mismatch(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    record = _inspect_record()
    record["Id"] = "c" * 64
    _install_subprocess_script(
        monkeypatch,
        [
            _Outcome(returncode=0, stdout=f"{CONTAINER_ID}\n"),
            _Outcome(returncode=0, stdout=json.dumps([record])),
        ],
    )

    with pytest.raises(RuntimeError, match="does not match"):
        cm.inspect_project_containers(
            engine=cm.ComposeEngine(binary="docker"),
            project_name=PROJECT,
        )
