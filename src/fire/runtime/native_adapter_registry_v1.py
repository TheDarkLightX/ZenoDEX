from __future__ import annotations

from typing import Any, Callable

from src.fire.runtime.burn_boost_call_v1_native_adapter import make_adapter as make_burn_boost_call_adapter
from src.fire.runtime.fee_note_v1_native_adapter import make_adapter as make_fee_note_adapter
from src.fire.runtime.lp_loss_cover_v1_native_adapter import make_adapter as make_lp_loss_cover_adapter


FIRE_NATIVE_ADAPTERS: dict[str, Callable[[Any], Any]] = {
    "burn_boost_call_v1": make_burn_boost_call_adapter,
    "fee_note_v1": make_fee_note_adapter,
    "lp_loss_cover_v1": make_lp_loss_cover_adapter,
}


def list_fire_native_adapter_entries() -> tuple[tuple[str, Callable[[Any], Any]], ...]:
    return tuple(FIRE_NATIVE_ADAPTERS.items())


def get_fire_native_adapter_maker(object_id: str) -> Callable[[Any], Any]:
    if object_id not in FIRE_NATIVE_ADAPTERS:
        raise KeyError(f"unsupported FIRE native adapter object_id: {object_id}")
    return FIRE_NATIVE_ADAPTERS[object_id]


__all__ = [
    "FIRE_NATIVE_ADAPTERS",
    "get_fire_native_adapter_maker",
    "list_fire_native_adapter_entries",
    "make_burn_boost_call_adapter",
    "make_fee_note_adapter",
    "make_lp_loss_cover_adapter",
]
