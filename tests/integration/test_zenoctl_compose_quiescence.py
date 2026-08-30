from __future__ import annotations

import json
import subprocess
from dataclasses import dataclass
from pathlib import Path
from typing import cast

import pytest

from tools.zenoctl_testnet_local import compose as cm

PROJECT = "zenodex-local-quarantine"
COMPOSE_FILE = Path("docker-compose.local.yml")
CONTAINER_ID = "a" * 64
SECOND_CONTAINER_ID = "c" * 64
PROFILE_ID = "local-testnet-retired-bridge-quarantine-v2"
PROFILE_DIGEST = "sha256:" + "b" * 64
IMAGE_ID = "sha256:" + "d" * 64
IMAGE_REFERENCE = "zenodex/operator-tools:local"


@dataclass(frozen=True)
class _Outcome:
    returncode: int
    stdout: str | None = None
    stderr: str | None = None


@dataclass(frozen=True)
class _RunCall:
    command: tuple[str, ...]
    capture_output: bool
    input_text: str | None = None


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
        input: str | None,
        text: bool,
    ) -> subprocess.CompletedProcess[str]:
        if check:
            raise AssertionError("compose._run must apply its own strict return-code check")
        if not text:
            raise AssertionError("compose._run must request text output")
        if not scripted:
            raise AssertionError(f"unexpected subprocess call: {command!r}")
        calls.append(_RunCall(tuple(command), capture_output, input))
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


def test_compose_run_forwards_exact_stdin_payload(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    calls = _install_subprocess_script(
        monkeypatch,
        [_Outcome(returncode=0, stdout="accepted")],
    )

    result = cm.compose_run(
        engine=cm.ComposeEngine(binary="docker"),
        project_name=PROJECT,
        compose_files=[COMPOSE_FILE],
        service="zenodex-api",
        command=["-c", "print('ok')"],
        extra_args=["-T"],
        capture=True,
        input_text='{"payload":"bound"}',
    )

    if result.stdout != "accepted":
        raise AssertionError("compose run result was not returned")
    expected = _RunCall(
        (
            "docker",
            "compose",
            "-p",
            PROJECT,
            "-f",
            str(COMPOSE_FILE),
            "run",
            "--rm",
            "--no-deps",
            "-T",
            "zenodex-api",
            "-c",
            "print('ok')",
        ),
        True,
        '{"payload":"bound"}',
    )
    if calls != [expected]:
        raise AssertionError(f"compose run did not preserve stdin: {calls!r}")


def _inspect_record(*, environment: list[str] | None = None) -> dict[str, object]:
    return {
        "Id": CONTAINER_ID,
        "Image": IMAGE_ID,
        "Path": "/usr/local/bin/python3",
        "Args": ["-m", "src.integration.api_server"],
        "State": {
            "Status": "running",
            "Running": True,
            "Paused": False,
            "Restarting": False,
            "OOMKilled": False,
            "Dead": False,
            "Pid": 4242,
            "ExitCode": 0,
            "Error": "",
            "Health": {"Status": "healthy"},
        },
        "Config": {
            "Image": IMAGE_REFERENCE,
            "Cmd": ["-m", "src.integration.api_server"],
            "Entrypoint": None,
            "WorkingDir": "/app",
            "User": "1000:1000",
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
        "HostConfig": {
            "Binds": ["/srv/zenodex/config.json:/app/config.json:ro"],
            "ExtraHosts": None,
            "Devices": [],
            "PortBindings": {
                "8000/tcp": [
                    {"HostIp": "127.0.0.1", "HostPort": "18080"},
                ]
            },
            "RestartPolicy": {
                "Name": "on-failure",
                "MaximumRetryCount": 3,
            },
            "ReadonlyRootfs": True,
            "NetworkMode": f"{PROJECT}_zenodex-local-testnet",
            "Privileged": False,
            "CapAdd": None,
            "CapDrop": ["ALL"],
            "SecurityOpt": ["no-new-privileges:true"],
            "PidMode": "",
        },
        "Mounts": [
            {
                "Type": "bind",
                "Source": "/srv/zenodex/config.json",
                "Destination": "/app/config.json",
                "Mode": "ro",
                "RW": False,
                "Propagation": "rprivate",
            }
        ],
        "NetworkSettings": {
            "Ports": {
                "8000/tcp": [
                    {"HostIp": "127.0.0.1", "HostPort": "18080"},
                ]
            },
            "Networks": {f"{PROJECT}_zenodex-local-testnet": {}},
        },
    }


def _replace_nested(
    record: dict[str, object],
    path: tuple[str, ...],
    value: object,
) -> None:
    current = record
    for component in path[:-1]:
        child = current[component]
        if type(child) is not dict:
            raise AssertionError(f"test fixture path is not an object: {path!r}")
        current = cast(dict[str, object], child)
    current[path[-1]] = value


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
    calls = _install_subprocess_script(
        monkeypatch,
        [
            _Outcome(returncode=0, stdout=f"{CONTAINER_ID}\n"),
            _Outcome(returncode=0, stdout=json.dumps([_inspect_record()])),
            _Outcome(returncode=0, stdout=f"{CONTAINER_ID}\n"),
        ],
    )

    snapshots = cm.inspect_project_containers(
        engine=cm.ComposeEngine(binary="docker"),
        project_name=PROJECT,
    )

    if len(snapshots) != 1:
        raise AssertionError(f"expected one snapshot, got {snapshots!r}")
    snapshot = snapshots[0]
    if snapshot.container_id != CONTAINER_ID:
        raise AssertionError("snapshot lost the canonical container ID")
    if snapshot.compose_service != "zenodex-api":
        raise AssertionError("snapshot lost the compose service")
    if snapshot.profile_id != PROFILE_ID or snapshot.profile_digest != PROFILE_DIGEST:
        raise AssertionError("snapshot lost the quarantine profile binding")
    if snapshot.environment_value("PERPS_WALLET_API_ENABLED") != "false":
        raise AssertionError("snapshot lost the exact route environment")

    facts = snapshot.engine_facts
    if facts is None:
        raise AssertionError("engine-decoded snapshots must carry complete engine facts")
    if facts.immutable_image_id != IMAGE_ID or facts.config_image != IMAGE_REFERENCE:
        raise AssertionError("snapshot did not retain both image identities")
    if facts.path != "/usr/local/bin/python3":
        raise AssertionError("snapshot lost the actual executable path")
    if facts.args != ("-m", "src.integration.api_server"):
        raise AssertionError("snapshot lost the actual executable arguments")
    if facts.command.is_null or facts.command.values != facts.args:
        raise AssertionError("snapshot lost Config.Cmd list identity")
    if not facts.entrypoint.is_null or facts.entrypoint.values:
        raise AssertionError("snapshot collapsed a null Config.Entrypoint")
    if facts.working_dir != "/app" or facts.user != "1000:1000":
        raise AssertionError("snapshot lost working-directory or user facts")
    if len(facts.mounts) != 1:
        raise AssertionError("snapshot lost the effective mount")
    mount = facts.mounts[0]
    if (
        mount.mount_type != "bind"
        or mount.destination != "/app/config.json"
        or mount.read_write
    ):
        raise AssertionError("snapshot altered effective mount semantics")
    if facts.binds.is_null or len(facts.binds.values) != 1:
        raise AssertionError("snapshot lost HostConfig.Binds")
    configured = facts.configured_ports.bindings
    published = facts.published_ports.bindings
    if configured != published or len(published) != 1:
        raise AssertionError("snapshot lost configured or published port bindings")
    if published[0].host_port != 18_080:
        raise AssertionError("snapshot altered the published host port")
    if facts.restart_policy.name != "on-failure":
        raise AssertionError("snapshot lost restart policy")
    if not facts.readonly_rootfs:
        raise AssertionError("snapshot lost readonly-rootfs state")
    if not facts.cap_add.is_null or facts.cap_add.values:
        raise AssertionError("snapshot altered the empty added-capability set")
    if facts.cap_drop.is_null or facts.cap_drop.values != ("ALL",):
        raise AssertionError("snapshot lost the dropped-capability set")
    if facts.security_opt.is_null or facts.security_opt.values != (
        "no-new-privileges:true",
    ):
        raise AssertionError("snapshot lost security options")
    if facts.pid_mode:
        raise AssertionError("snapshot altered the private PID namespace")
    if not facts.extra_hosts.is_null or facts.extra_hosts.values:
        raise AssertionError("snapshot altered the empty host-override set")
    if facts.devices.is_null or facts.devices.values:
        raise AssertionError("snapshot altered the empty device set")
    if facts.attached_networks != (f"{PROJECT}_zenodex-local-testnet",):
        raise AssertionError("snapshot lost the attached-network identity")
    if not facts.state.running or facts.state.status != "running":
        raise AssertionError("snapshot lost running state")
    if facts.state.health_status != "healthy":
        raise AssertionError("snapshot lost health state")
    query = (
        "docker",
        "ps",
        "--all",
        "--quiet",
        "--no-trunc",
        "--filter",
        f"label=com.docker.compose.project={PROJECT}",
    )
    expected_calls = [
        _RunCall(query, True),
        _RunCall(
            ("docker", "inspect", "--type", "container", CONTAINER_ID),
            True,
        ),
        _RunCall(query, True),
    ]
    if calls != expected_calls:
        raise AssertionError(f"inspection was not query-inspect-query: {calls!r}")


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


def test_inspect_project_containers_rejects_membership_change_after_inspect(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    _install_subprocess_script(
        monkeypatch,
        [
            _Outcome(returncode=0, stdout=f"{CONTAINER_ID}\n"),
            _Outcome(returncode=0, stdout=json.dumps([_inspect_record()])),
            _Outcome(
                returncode=0,
                stdout=f"{CONTAINER_ID}\n{SECOND_CONTAINER_ID}\n",
            ),
        ],
    )

    with pytest.raises(RuntimeError, match="membership changed"):
        cm.inspect_project_containers(
            engine=cm.ComposeEngine(binary="docker"),
            project_name=PROJECT,
        )


def test_inspect_project_containers_rejects_empty_project_membership_race(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    calls = _install_subprocess_script(
        monkeypatch,
        [
            _Outcome(returncode=0, stdout=""),
            _Outcome(returncode=0, stdout=f"{CONTAINER_ID}\n"),
        ],
    )

    with pytest.raises(RuntimeError, match="membership changed"):
        cm.inspect_project_containers(
            engine=cm.ComposeEngine(binary="docker"),
            project_name=PROJECT,
        )
    if len(calls) != 2:
        raise AssertionError("empty membership must be re-queried before acceptance")


def test_inspect_project_containers_accepts_stably_empty_project(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    calls = _install_subprocess_script(
        monkeypatch,
        [
            _Outcome(returncode=0, stdout=""),
            _Outcome(returncode=0, stdout=""),
        ],
    )

    observed = cm.inspect_project_containers(
        engine=cm.ComposeEngine(binary="docker"),
        project_name=PROJECT,
    )
    if observed:
        raise AssertionError(f"stably empty project returned snapshots: {observed!r}")
    if len(calls) != 2 or calls[0] != calls[1]:
        raise AssertionError("empty project acceptance requires two identical queries")


def test_inspect_project_containers_rejects_second_query_failure(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    _install_subprocess_script(
        monkeypatch,
        [
            _Outcome(returncode=0, stdout=f"{CONTAINER_ID}\n"),
            _Outcome(returncode=0, stdout=json.dumps([_inspect_record()])),
            _Outcome(returncode=125, stdout="", stderr="daemon changed state"),
        ],
    )

    with pytest.raises(RuntimeError, match=r"command failed \(exit 125\)"):
        cm.inspect_project_containers(
            engine=cm.ComposeEngine(binary="docker"),
            project_name=PROJECT,
        )


@pytest.mark.parametrize(
    ("path", "malformed"),
    [
        (("Image",), "sha256:" + "D" * 64),
        (("Path",), None),
        (("Args",), None),
        (("Config", "Image"), 7),
        (("Config", "Cmd"), "python3"),
        (("Config", "Entrypoint"), False),
        (("Config", "WorkingDir"), None),
        (("Config", "User"), []),
        (("HostConfig", "Binds"), {}),
        (("HostConfig", "PortBindings"), []),
        (("HostConfig", "ReadonlyRootfs"), 1),
        (("Mounts",), None),
        (("NetworkSettings", "Ports"), []),
        (("State", "Running"), 1),
    ],
)
def test_project_container_snapshot_rejects_malformed_authority_shapes(
    path: tuple[str, ...],
    malformed: object,
) -> None:
    record = _inspect_record()
    _replace_nested(record, path, malformed)

    with pytest.raises(RuntimeError):
        cm._project_container_snapshot(record, expected_project=PROJECT)


def test_project_container_snapshot_observes_canonical_host_overrides_devices_and_networks() -> None:
    baseline = cm._project_container_snapshot(
        _inspect_record(), expected_project=PROJECT
    )
    changed_record = _inspect_record()
    host_config = cast(dict[str, object], changed_record["HostConfig"])
    host_config["ExtraHosts"] = [
        "zeta.internal:203.0.113.9",
        "alpha.internal:2001:db8::1",
    ]
    host_config["Devices"] = [
        {
            "PathOnHost": "/dev/zenodex-z",
            "PathInContainer": "/dev/zenodex-z",
            "CgroupPermissions": "rwm",
        },
        {
            "PathOnHost": "/dev/zenodex-a",
            "PathInContainer": "/dev/zenodex-a",
            "CgroupPermissions": "rw",
        },
    ]
    network_settings = cast(dict[str, object], changed_record["NetworkSettings"])
    network_settings["Networks"] = {
        "zeta-network": {},
        f"{PROJECT}_zenodex-local-testnet": {},
        "alpha-network": {},
    }

    changed = cm._project_container_snapshot(changed_record, expected_project=PROJECT)

    baseline_facts = baseline.engine_facts
    changed_facts = changed.engine_facts
    if baseline_facts is None or changed_facts is None:
        raise AssertionError("strict decoder returned incomplete engine facts")
    if changed_facts == baseline_facts:
        raise AssertionError("authority-relevant engine changes were decoded away")
    if tuple(item.host for item in changed_facts.extra_hosts.values) != (
        "alpha.internal",
        "zeta.internal",
    ):
        raise AssertionError("host overrides are not canonically ordered")
    if tuple(item.path_in_container for item in changed_facts.devices.values) != (
        "/dev/zenodex-a",
        "/dev/zenodex-z",
    ):
        raise AssertionError("devices are not canonically ordered")
    if changed_facts.attached_networks != (
        "alpha-network",
        f"{PROJECT}_zenodex-local-testnet",
        "zeta-network",
    ):
        raise AssertionError("attached networks are not canonically ordered")


@pytest.mark.parametrize(
    ("parent", "field"),
    (
        ("HostConfig", "ExtraHosts"),
        ("HostConfig", "Devices"),
        ("NetworkSettings", "Networks"),
    ),
)
def test_project_container_snapshot_rejects_omitted_authority_relevant_engine_fact(
    parent: str,
    field: str,
) -> None:
    record = _inspect_record()
    container = cast(dict[str, object], record[parent])
    del container[field]

    with pytest.raises(RuntimeError, match="lacks required runtime facts"):
        cm._project_container_snapshot(record, expected_project=PROJECT)


@pytest.mark.parametrize(
    ("path", "malformed"),
    (
        (("HostConfig", "ExtraHosts"), {"tau-local": "203.0.113.9"}),
        (("HostConfig", "ExtraHosts"), ["missing-address"]),
        (
            ("HostConfig", "Devices"),
            [
                {
                    "PathOnHost": "/dev/kvm",
                    "PathInContainer": "/dev/kvm",
                    "CgroupPermissions": ["r", "w"],
                }
            ],
        ),
        (("NetworkSettings", "Networks"), []),
        (("NetworkSettings", "Networks"), {"attacker-network": []}),
    ),
)
def test_project_container_snapshot_rejects_malformed_authority_relevant_engine_fact(
    path: tuple[str, ...],
    malformed: object,
) -> None:
    record = _inspect_record()
    _replace_nested(record, path, malformed)

    with pytest.raises(RuntimeError):
        cm._project_container_snapshot(record, expected_project=PROJECT)


def test_project_container_snapshot_rejects_duplicate_mount_destinations() -> None:
    record = _inspect_record()
    mounts = cast(list[object], record["Mounts"])
    duplicate = cast(dict[str, object], mounts[0]).copy()
    duplicate["Source"] = "/srv/zenodex/other.json"
    mounts.append(duplicate)

    with pytest.raises(RuntimeError, match="duplicate mount destination"):
        cm._project_container_snapshot(record, expected_project=PROJECT)


def test_project_container_snapshot_rejects_duplicate_bind_destinations() -> None:
    record = _inspect_record()
    host_config = cast(dict[str, object], record["HostConfig"])
    host_config["Binds"] = [
        "/srv/zenodex/config.json:/app/config.json:ro",
        "/srv/zenodex/other.json:/app/config.json:rw",
    ]

    with pytest.raises(RuntimeError, match="duplicate bind destination"):
        cm._project_container_snapshot(record, expected_project=PROJECT)


def test_project_container_snapshot_rejects_duplicate_port_bindings() -> None:
    record = _inspect_record()
    host_config = cast(dict[str, object], record["HostConfig"])
    port_bindings = cast(dict[str, object], host_config["PortBindings"])
    binding = {"HostIp": "127.0.0.1", "HostPort": "18080"}
    port_bindings["8000/tcp"] = [binding, binding.copy()]

    with pytest.raises(RuntimeError, match="duplicate port binding"):
        cm._project_container_snapshot(record, expected_project=PROJECT)


def test_project_container_snapshot_rejects_ambiguous_empty_binding_list() -> None:
    record = _inspect_record()
    host_config = cast(dict[str, object], record["HostConfig"])
    port_bindings = cast(dict[str, object], host_config["PortBindings"])
    port_bindings["8000/tcp"] = []

    with pytest.raises(RuntimeError, match="empty binding list"):
        cm._project_container_snapshot(record, expected_project=PROJECT)


def test_project_container_snapshot_retains_null_and_empty_variants() -> None:
    null_record = _inspect_record()
    null_host_config = cast(dict[str, object], null_record["HostConfig"])
    null_host_config["Binds"] = None
    null_host_config["PortBindings"] = {"8000/tcp": None}
    null_network = cast(dict[str, object], null_record["NetworkSettings"])
    null_network["Ports"] = {"8000/tcp": None}

    empty_record = _inspect_record()
    empty_host_config = cast(dict[str, object], empty_record["HostConfig"])
    empty_host_config["Binds"] = []
    empty_host_config["PortBindings"] = {}
    empty_network = cast(dict[str, object], empty_record["NetworkSettings"])
    empty_network["Ports"] = {}

    null_snapshot = cm._project_container_snapshot(
        null_record, expected_project=PROJECT
    )
    empty_snapshot = cm._project_container_snapshot(
        empty_record, expected_project=PROJECT
    )
    null_facts = null_snapshot.engine_facts
    empty_facts = empty_snapshot.engine_facts
    if null_facts is None or empty_facts is None:
        raise AssertionError("strict decoder returned incomplete engine facts")
    if not null_facts.binds.is_null or empty_facts.binds.is_null:
        raise AssertionError("null and empty bind variants were collapsed")
    expected_unbound = (cm.ContainerPort(number=8000, protocol="tcp"),)
    if null_facts.configured_ports.unbound_ports != expected_unbound:
        raise AssertionError("null port binding was not retained as unbound")
    if empty_facts.configured_ports.unbound_ports:
        raise AssertionError("empty port map was conflated with a null port binding")


def test_project_container_snapshot_rejects_hostile_mount_extra_shape() -> None:
    record = _inspect_record()
    mounts = cast(list[object], record["Mounts"])
    mount = cast(dict[str, object], mounts[0])
    mount["AccessOverride"] = "rw"

    with pytest.raises(RuntimeError, match="unsupported keys"):
        cm._project_container_snapshot(record, expected_project=PROJECT)


def test_project_container_snapshot_rejects_hostile_port_extra_shape() -> None:
    record = _inspect_record()
    host_config = cast(dict[str, object], record["HostConfig"])
    ports = cast(dict[str, object], host_config["PortBindings"])
    bindings = cast(list[object], ports["8000/tcp"])
    binding = cast(dict[str, object], bindings[0])
    binding["HostPath"] = "/run/authority.sock"

    with pytest.raises(RuntimeError, match="unsupported keys"):
        cm._project_container_snapshot(record, expected_project=PROJECT)


def test_inspect_project_containers_rejects_duplicate_json_keys(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    encoded = json.dumps([_inspect_record()])
    needle = f'"Image": "{IMAGE_ID}"'
    duplicate = f'{needle}, "Image": "{IMAGE_ID}"'
    hostile = encoded.replace(needle, duplicate, 1)
    _install_subprocess_script(
        monkeypatch,
        [
            _Outcome(returncode=0, stdout=f"{CONTAINER_ID}\n"),
            _Outcome(returncode=0, stdout=hostile),
        ],
    )

    with pytest.raises(RuntimeError, match="duplicate"):
        cm.inspect_project_containers(
            engine=cm.ComposeEngine(binary="docker"),
            project_name=PROJECT,
        )


def test_inspect_image_reference_accepts_immutable_id_and_exact_environment(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    calls = _install_subprocess_script(
        monkeypatch,
        [
            _Outcome(
                returncode=0,
                stdout=json.dumps(
                    [
                        {
                            "Id": IMAGE_ID,
                            "Config": {
                                "Env": [
                                    "PYTHON_VERSION=3.11",
                                    "PATH=/usr/local/bin:/usr/bin",
                                ],
                                "ExposedPorts": {"8000/tcp": None},
                            },
                        }
                    ]
                ),
            )
        ],
    )

    observed = cm.inspect_image_reference(
        engine=cm.ComposeEngine(binary="docker"),
        image_reference=IMAGE_REFERENCE,
    )

    expected_facts = cm.ImageReferenceEngineFacts(
        immutable_image_id=IMAGE_ID,
        environment=(
            ("PATH", "/usr/local/bin:/usr/bin"),
            ("PYTHON_VERSION", "3.11"),
        ),
        exposed_ports=(cm.ContainerPort(number=8000, protocol="tcp"),),
    )
    if observed != expected_facts:
        raise AssertionError("image reference facts were not decoded canonically")
    expected = _RunCall(
        ("docker", "image", "inspect", IMAGE_REFERENCE),
        True,
    )
    if calls != [expected]:
        raise AssertionError(f"unexpected image inspection command: {calls!r}")


@pytest.mark.parametrize(
    "malformed_output",
    [
        None,
        "{}",
        "[]",
        json.dumps([{"Id": "sha256:" + "D" * 64}]),
        json.dumps([{"Id": IMAGE_ID, "Config": {"Env": ["PATH=/bin"]}}] * 2),
        json.dumps([{"Id": IMAGE_ID, "Config": {"Env": None}}]),
        json.dumps(
            [
                {
                    "Id": IMAGE_ID,
                    "Config": {"Env": ["PATH=/bin", "PATH=/hostile"]},
                }
            ]
        ),
    ],
)
def test_inspect_image_reference_rejects_malformed_results(
    monkeypatch: pytest.MonkeyPatch,
    malformed_output: str | None,
) -> None:
    _install_subprocess_script(
        monkeypatch,
        [_Outcome(returncode=0, stdout=malformed_output)],
    )

    with pytest.raises(RuntimeError):
        cm.inspect_image_reference(
            engine=cm.ComposeEngine(binary="docker"),
            image_reference=IMAGE_REFERENCE,
        )


def test_inspect_image_reference_rejects_query_failure(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    _install_subprocess_script(
        monkeypatch,
        [_Outcome(returncode=125, stdout="", stderr="image store unavailable")],
    )

    with pytest.raises(RuntimeError, match=r"command failed \(exit 125\)") as caught:
        cm.inspect_image_reference(
            engine=cm.ComposeEngine(binary="docker"),
            image_reference=IMAGE_REFERENCE,
        )
    if "image store unavailable" not in str(caught.value):
        raise AssertionError("image inspection failure omitted engine diagnostic")
