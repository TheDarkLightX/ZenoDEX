"""CBC tests for the exact authority-false Linux supervisor entrypoint."""

from __future__ import annotations

import inspect
from pathlib import Path
from typing import cast

import pytest

from tools import zrpf_spot_v7_firecracker_linux_runner as linux_runner
from tools._zrpf_spot_v7_firecracker_descriptor_handoff import (
    _PreparedDescriptorBoundSpotV7LaunchV1,
)
from tools.zrpf_spot_v7_firecracker_linux_netns_adapter import (
    PinnedLinuxSpotV7NetworkNamespaceKernelV1,
)
from tools.zrpf_spot_v7_firecracker_root_supervisor import (
    SpotV7RootSupervisorPlanV1,
    SpotV7RootSupervisorRejectV1,
)


def _exact_prepared_launch_token() -> _PreparedDescriptorBoundSpotV7LaunchV1:
    """Return an unspent exact-type token without exercising privileged effects."""

    return object.__new__(_PreparedDescriptorBoundSpotV7LaunchV1)


def _exact_plan_token() -> SpotV7RootSupervisorPlanV1:
    """Return an exact-type token for the forwarding-only composition test."""

    return object.__new__(SpotV7RootSupervisorPlanV1)


def _pinned_kernel() -> PinnedLinuxSpotV7NetworkNamespaceKernelV1:
    return PinnedLinuxSpotV7NetworkNamespaceKernelV1(
        executable=Path("/governed/zrpf-firecracker-netns-helper"),
        expected_sha256="11" * 32,
    )


def test_exact_runner_has_no_injected_os_port_parameter() -> None:
    parameters = inspect.signature(
        linux_runner.run_exact_linux_spot_v7_root_supervisor_candidate_v1
    ).parameters

    assert tuple(parameters) == (
        "prepared_launch",
        "plan",
        "network_namespace_kernel",
    )
    assert "os_port" not in parameters


def test_exact_runner_constructs_the_exact_linux_port(monkeypatch: pytest.MonkeyPatch) -> None:
    prepared_launch = _exact_prepared_launch_token()
    plan = _exact_plan_token()
    kernel = _pinned_kernel()
    sentinel = object()
    observed: dict[str, object] = {}

    def capture(**kwargs: object) -> object:
        observed.update(kwargs)
        return sentinel

    monkeypatch.setattr(
        linux_runner,
        "run_spot_v7_root_supervisor_contract_v1",
        capture,
    )

    result = linux_runner.run_exact_linux_spot_v7_root_supervisor_candidate_v1(
        prepared_launch=prepared_launch,
        plan=plan,
        network_namespace_kernel=kernel,
    )

    assert result is sentinel
    assert observed["prepared_launch"] is prepared_launch
    assert observed["plan"] is plan
    port = cast(
        linux_runner.LinuxSpotV7RootSupervisorOsPortV1,
        observed["os_port"],
    )
    assert type(port) is linux_runner.LinuxSpotV7RootSupervisorOsPortV1
    assert port.live_execution_verified is False
    assert port.live_ownership_verified is False
    assert port.runtime_authority is False
    assert port.settlement_authority is False
    assert port.release_authority is False
    assert port.production_authority is False


class _ProtocolCompatibleKernel:
    """A structural test double that must not reach the exact candidate route."""


@pytest.mark.parametrize(
    ("field", "value", "expected_code"),
    (
        (
            "prepared_launch",
            object(),
            "linux_runner_prepared_launch_invalid",
        ),
        ("plan", object(), "linux_runner_plan_invalid"),
        (
            "network_namespace_kernel",
            _ProtocolCompatibleKernel(),
            "linux_runner_namespace_kernel_invalid",
        ),
    ),
)
def test_exact_runner_rejects_substituted_boundary_objects_before_execution(
    monkeypatch: pytest.MonkeyPatch,
    field: str,
    value: object,
    expected_code: str,
) -> None:
    kwargs: dict[str, object] = {
        "prepared_launch": _exact_prepared_launch_token(),
        "plan": _exact_plan_token(),
        "network_namespace_kernel": _pinned_kernel(),
    }
    kwargs[field] = value

    def unexpected(**_kwargs: object) -> object:
        raise AssertionError("substituted boundary object reached execution")

    monkeypatch.setattr(
        linux_runner,
        "run_spot_v7_root_supervisor_contract_v1",
        unexpected,
    )

    with pytest.raises(SpotV7RootSupervisorRejectV1) as captured:
        linux_runner.run_exact_linux_spot_v7_root_supervisor_candidate_v1(**kwargs)

    assert captured.value.code == expected_code


def test_exact_runner_rejects_pinned_kernel_subclass(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    class _PinnedKernelSubclass(PinnedLinuxSpotV7NetworkNamespaceKernelV1):
        pass

    kernel = _PinnedKernelSubclass(
        executable=Path("/governed/zrpf-firecracker-netns-helper"),
        expected_sha256="22" * 32,
    )
    monkeypatch.setattr(
        linux_runner,
        "run_spot_v7_root_supervisor_contract_v1",
        lambda **_kwargs: pytest.fail("subclass reached execution"),
    )

    with pytest.raises(SpotV7RootSupervisorRejectV1) as captured:
        linux_runner.run_exact_linux_spot_v7_root_supervisor_candidate_v1(
            prepared_launch=_exact_prepared_launch_token(),
            plan=_exact_plan_token(),
            network_namespace_kernel=kernel,
        )

    assert captured.value.code == "linux_runner_namespace_kernel_invalid"


def test_exact_runner_claims_remain_false() -> None:
    assert linux_runner.LINUX_RUNNER_LIVE_EXECUTION_VERIFIED_V1 is False
    assert linux_runner.LINUX_RUNNER_LIVE_OWNERSHIP_VERIFIED_V1 is False
    assert linux_runner.LINUX_RUNNER_RUNTIME_AUTHORITY_V1 is False
    assert linux_runner.LINUX_RUNNER_SETTLEMENT_AUTHORITY_V1 is False
    assert linux_runner.LINUX_RUNNER_RELEASE_AUTHORITY_V1 is False
    assert linux_runner.LINUX_RUNNER_PRODUCTION_AUTHORITY_V1 is False
