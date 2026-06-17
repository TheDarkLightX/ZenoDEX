"""Compatibility exports for legacy imports of the old monolithic dispatch module.

Endpoint registrations now live in route-family modules imported by
``api_server_dex_dispatch``. This module intentionally performs no endpoint
registration, so direct imports from disaster-discovery tools cannot freeze the
registry during a circular import. Keep only compatibility aliases here.
"""

from __future__ import annotations

from src.integration.dex_dispatch_proof_mining_snapshots import (
    _load_latest_writer_snapshot_for_template,
    _load_latest_writer_snapshot_from_file_for_template,
    _load_latest_writer_snapshot_from_url_for_template,
)

__all__ = [
    "_load_latest_writer_snapshot_for_template",
    "_load_latest_writer_snapshot_from_file_for_template",
    "_load_latest_writer_snapshot_from_url_for_template",
]
