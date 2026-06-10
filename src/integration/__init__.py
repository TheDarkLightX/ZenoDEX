"""Tau Testnet Alpha integration layer.

Submodule imports should stay cheap and side-effect-light. Keep the historical
package-level exports lazy so importing a focused integration module does not
pull in the full DEX/perps stack during test collection.
"""

from __future__ import annotations

from importlib import import_module
from typing import Any


_LAZY_EXPORTS = {
    "parse_intents": ("operations", "parse_intents"),
    "parse_settlement": ("operations", "parse_settlement"),
    "create_intent_operation": ("operations", "create_intent_operation"),
    "create_settlement_operation": ("operations", "create_settlement_operation"),
    "validate_operations": ("validation", "validate_operations"),
}

__all__ = [
    "parse_intents",
    "parse_settlement",
    "create_intent_operation",
    "create_settlement_operation",
    "validate_operations",
]


def __getattr__(name: str) -> Any:
    if name not in _LAZY_EXPORTS:
        raise AttributeError(name)
    module_name, attr_name = _LAZY_EXPORTS[name]
    value = getattr(import_module(f".{module_name}", __name__), attr_name)
    globals()[name] = value
    return value
