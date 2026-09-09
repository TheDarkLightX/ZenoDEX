"""Conditionally execute the exact V2 custody/global statement on one verifier.

The selected verifier configuration, guest ELF, SDK, and operating system are
trusted external premises.  Matching bytes do not establish guest honesty, and
this adapter grants no profile, intent, store, publication, or other authority.
"""

from __future__ import annotations

from ..core.asset_lane_coordinator_values_v2 import AssetLaneCommandV2, AssetLaneRejectedV2
from ..core.asset_lane_custody_state_v2 import AssetLaneCustodyStateV2
from ..core.asset_lane_custody_statement_v2 import prepare_asset_lane_custody_global_statement_v2
from ..core.asset_lane_state_v2 import AssetLaneContextV2
from ..core.global_economic_state_v2 import GlobalEconomicStateV2
from .global_receipt_verifier_v1 import GlobalReceiptVerifierV1


def verify_asset_lane_custody_global_receipt_v2(
    context: AssetLaneContextV2,
    pre_state: AssetLaneCustodyStateV2,
    command: AssetLaneCommandV2,
    global_pre: GlobalEconomicStateV2,
    global_post: GlobalEconomicStateV2,
    *,
    receipt_bytes: bytes,
    verifier: GlobalReceiptVerifierV1,
) -> bytes | AssetLaneRejectedV2:
    """Prepare and conditionally verify one detached custody/global statement.

    Rejected custody leaves return unchanged and never launch the verifier.  A
    successful return is the prepared statement bytes with authority ``NONE``.
    """
    if type(verifier) is not GlobalReceiptVerifierV1:
        raise TypeError("custody receipt verification requires an exact V1 verifier")
    snapshot = GlobalReceiptVerifierV1(
        verifier.executable_path,
        verifier.executable_sha256,
        verifier.expected_image_id,
        verifier.timeout_ms,
    )
    prepared = prepare_asset_lane_custody_global_statement_v2(
        context,
        pre_state,
        command,
        global_pre,
        global_post,
    )
    if type(prepared) is AssetLaneRejectedV2:
        return prepared
    if type(prepared) is not bytes:
        raise TypeError("custody statement producer returned an unsupported value")
    snapshot.verify_succinct_receipt(
        receipt_bytes,
        expected_image_id=snapshot.expected_image_id,
        expected_journal_bytes=prepared,
    )
    return prepared


__all__ = ["verify_asset_lane_custody_global_receipt_v2"]
