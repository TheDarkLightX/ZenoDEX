"""Compatibility marker for legacy imports of the old monolithic dispatch module.

Endpoint registrations now live in route-family modules imported by
``api_server_dex_dispatch``. This module intentionally performs no endpoint
registration or helper export, so direct imports cannot freeze the registry
during a circular import or recover retired local-only surfaces.
"""

from __future__ import annotations

__all__: list[str] = []
