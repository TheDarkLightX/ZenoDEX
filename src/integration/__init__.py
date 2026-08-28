"""Tau integration package with side-effect-free lazy compatibility exports."""

from __future__ import annotations

from importlib import import_module
from typing import Any, Final

_LAZY_EXPORTS_V1: Final = {
    "create_intent_operation": ("src.integration.operations", "create_intent_operation"),
    "create_settlement_operation": ("src.integration.operations", "create_settlement_operation"),
    "parse_intents": ("src.integration.operations", "parse_intents"),
    "parse_settlement": ("src.integration.operations", "parse_settlement"),
    "validate_operations": ("src.integration.validation", "validate_operations"),
}

__all__ = [
    "parse_intents",
    "parse_settlement",
    "create_intent_operation",
    "create_settlement_operation",
    "validate_operations",
]


def __getattr__(name: str) -> Any:
    """Load legacy package exports only when a caller explicitly requests one."""

    if type(name) is not str or name not in _LAZY_EXPORTS_V1:
        raise AttributeError(name)
    module_name, attribute_name = _LAZY_EXPORTS_V1[name]
    return getattr(import_module(module_name), attribute_name)
