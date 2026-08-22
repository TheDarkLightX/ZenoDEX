"""Pure phase predicate for clearinghouse position admission."""

from __future__ import annotations

from collections.abc import Mapping

from .domain_limits import require_int_range


def clearinghouse_position_update_allowed(state: Mapping[str, object]) -> bool:
    """Return whether a position update is outside the published-price window.

    The clearinghouse kernels keep ``clearing_price_seen`` sticky after the
    first settlement. The epoch markers are therefore the authoritative phase
    encoding. A current clearing price is pending exactly when its epoch is the
    current epoch and the oracle/index update for that epoch has not settled.

    A settled epoch remains position-admissible until the next epoch advance;
    this preserves the established v1 clearinghouse workflow.
    """
    now_epoch = require_int_range("now_epoch", state.get("now_epoch"), minimum=0)
    clearing_price_epoch = require_int_range(
        "clearing_price_epoch",
        state.get("clearing_price_epoch"),
        minimum=0,
        maximum=now_epoch,
    )
    oracle_last_update_epoch = require_int_range(
        "oracle_last_update_epoch",
        state.get("oracle_last_update_epoch"),
        minimum=0,
        maximum=now_epoch,
    )
    if oracle_last_update_epoch > clearing_price_epoch:
        raise ValueError(
            "oracle_last_update_epoch cannot exceed clearing_price_epoch: "
            f"{oracle_last_update_epoch} > {clearing_price_epoch}"
        )
    return not (
        clearing_price_epoch == now_epoch
        and oracle_last_update_epoch < now_epoch
    )
