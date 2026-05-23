from __future__ import annotations

from typing import Any, Literal, get_args

from .cantor_bdd_region import build_cantor_bdd_region_ba
from .region_ba import RegionBA, build_cantor_region_ba


RegionBABackendName = Literal["prefix", "bdd"]
DEFAULT_REGION_BA_BACKEND: RegionBABackendName = "prefix"


def supported_region_ba_backends() -> tuple[RegionBABackendName, ...]:
    return tuple(get_args(RegionBABackendName))


def resolve_region_ba_backend(name: str) -> RegionBA[Any]:
    backend = str(name).strip().lower()
    if backend == "prefix":
        return build_cantor_region_ba()
    if backend == "bdd":
        return build_cantor_bdd_region_ba()
    supported = ", ".join(supported_region_ba_backends())
    raise ValueError(f"unsupported RegionBA backend: {name!r}; expected one of: {supported}")
