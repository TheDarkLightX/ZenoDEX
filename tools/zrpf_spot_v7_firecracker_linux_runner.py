"""Exact authority-false Linux entrypoint for one staged Spot V7 launch.

The lower-level root-supervisor contract intentionally accepts a structural
OS-port protocol so its ordering and teardown laws can be tested without root
privileges.  This module is the narrower candidate execution route: it accepts
only the exact pinned Linux namespace helper, constructs the exact Linux port
internally, and forwards the already descriptor-staged launch once.

Successful return is still an authority-false observation.  This module does
not establish that a privileged host executed the path, that the selected
artifacts are release-governed, or that the payload may authorize settlement.
The caller still selects the exact helper instance.  Its executable identity
and per-run freshness require a later governed release boundary.
"""

from __future__ import annotations

from tools._zrpf_spot_v7_firecracker_descriptor_handoff import (
    _PreparedDescriptorBoundSpotV7LaunchV1,
)
from tools.zrpf_spot_v7_firecracker_linux_netns_adapter import (
    PinnedLinuxSpotV7NetworkNamespaceKernelV1,
)
from tools.zrpf_spot_v7_firecracker_linux_port import (
    LinuxSpotV7RootSupervisorOsPortV1,
)
from tools.zrpf_spot_v7_firecracker_root_supervisor import (
    CompletedSpotV7RootSupervisorRunV1,
    SpotV7RootSupervisorPlanV1,
    SpotV7RootSupervisorRejectV1,
    run_spot_v7_root_supervisor_contract_v1,
)

LINUX_RUNNER_LIVE_EXECUTION_VERIFIED_V1 = False
LINUX_RUNNER_LIVE_OWNERSHIP_VERIFIED_V1 = False
LINUX_RUNNER_RUNTIME_AUTHORITY_V1 = False
LINUX_RUNNER_SETTLEMENT_AUTHORITY_V1 = False
LINUX_RUNNER_RELEASE_AUTHORITY_V1 = False
LINUX_RUNNER_PRODUCTION_AUTHORITY_V1 = False


def run_exact_linux_spot_v7_root_supervisor_candidate_v1(
    *,
    prepared_launch: _PreparedDescriptorBoundSpotV7LaunchV1,
    plan: SpotV7RootSupervisorPlanV1,
    network_namespace_kernel: PinnedLinuxSpotV7NetworkNamespaceKernelV1,
) -> CompletedSpotV7RootSupervisorRunV1:
    """Run the candidate route with no caller-supplied OS-port implementation.

    Exact-type checks happen before constructing the effectful Linux port and
    before the staged launch is spent.  The delegated supervisor retains sole
    ownership of execution ordering, output validation, and teardown.  Callers
    should supply a fresh helper instance for each run; this candidate boundary
    does not promote that operational expectation to authority.
    """

    if type(prepared_launch) is not _PreparedDescriptorBoundSpotV7LaunchV1:
        raise SpotV7RootSupervisorRejectV1("linux_runner_prepared_launch_invalid")
    if type(plan) is not SpotV7RootSupervisorPlanV1:
        raise SpotV7RootSupervisorRejectV1("linux_runner_plan_invalid")
    if type(network_namespace_kernel) is not PinnedLinuxSpotV7NetworkNamespaceKernelV1:
        raise SpotV7RootSupervisorRejectV1("linux_runner_namespace_kernel_invalid")
    os_port = LinuxSpotV7RootSupervisorOsPortV1(network_namespace_kernel)
    return run_spot_v7_root_supervisor_contract_v1(
        prepared_launch=prepared_launch,
        plan=plan,
        os_port=os_port,
    )


__all__ = [
    "LINUX_RUNNER_LIVE_EXECUTION_VERIFIED_V1",
    "LINUX_RUNNER_LIVE_OWNERSHIP_VERIFIED_V1",
    "LINUX_RUNNER_PRODUCTION_AUTHORITY_V1",
    "LINUX_RUNNER_RELEASE_AUTHORITY_V1",
    "LINUX_RUNNER_RUNTIME_AUTHORITY_V1",
    "LINUX_RUNNER_SETTLEMENT_AUTHORITY_V1",
    "run_exact_linux_spot_v7_root_supervisor_candidate_v1",
]
