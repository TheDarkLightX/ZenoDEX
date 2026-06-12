"""Total canonical-encodability guards for the autonomous-governance lane.

Every governance surface in this lane returns a hash-chained receipt, and the
receipt body is committed with `canonical_json_bytes` (which rejects unpaired
surrogate code points with `TypeError`, rejects non-`str` dict keys, and runs
the standard-library JSON encoder, which recurses on nesting). That creates a
class of input that is hostile to *encoding* rather than to the governance
math:

- a lone surrogate (`"\\ud800"`, reachable through a JSON string escape) in a
  field name or value,
- a deeply nested blob that exhausts the recursion limit inside the encoder,
- a Python-level object whose `__str__`/`__repr__` raises.

Fed to a boundary that quotes the raw input in an error label or carries it
verbatim into the receipt body, any of these crashes the very receipt that
should have *refused* the input. A fail-closed boundary must instead refuse
with a deterministic, itself-encodable receipt.

These helpers make that refusal possible:

- `is_canonically_encodable` decides, without ever raising, whether a value can
  be canonically hashed. It is built on the bounded size probe, which bails at
  `MAX_CANONICAL_DEPTH_V1` *before* deep recursion (so a 50k-deep blob raises a
  shallow `ValueError`, never a `RecursionError`) and rejects surrogates and
  non-`str` keys. A boundary calls it on its untrusted plain-JSON inputs and
  refuses any that fail.
- `safe_field_label` renders a (possibly hostile) field name as a label that is
  always canonical-JSON encodable and never triggers the field's own code.
  Benign `str` names pass through byte-identically, so pinned error strings and
  factory negative-control expectations are unchanged.

Scope: these guard *plain-JSON* inputs (mappings/sequences of str/int/bool/None
nested shallowly). They are deliberately NOT applied to typed descriptor
objects (e.g. `KeyBackendDescriptor`), which the bounded probe would reject as
"unsupported type" — those travel to validators that understand their type.
"""

from __future__ import annotations

from src.state.canonical import bounded_json_utf8_size

# Generous enough that any realistic governance receipt/input passes (a sample
# policy is ~1.3 KB; a max 4096-step trajectory input is well under this), while
# still refusing a pathological multi-megabyte blob fail-closed.
MAX_CANONICAL_BYTES_V1 = 64 * 1024 * 1024
# The standard-library JSON encoder recurses per nesting level; the bounded
# probe bails here *before* deep recursion. Legitimate governance structures
# nest only a handful of levels deep, so this is a safe ceiling.
MAX_CANONICAL_DEPTH_V1 = 64
# A fixed, ASCII placeholder for a field name whose own __str__/__repr__ raises.
UNRENDERABLE_FIELD_LABEL = "<unrenderable>"


def is_canonically_encodable(value: object) -> bool:
    """Return True iff `value` can be canonically hashed without raising.

    Total: never raises. The bounded probe rejects surrogates and non-`str`
    keys with `TypeError`, over-deep nesting with a shallow `ValueError` (so the
    real JSON encoder's `RecursionError` is never reached), and over-large or
    over-numerous structures with `ValueError`. Any other exception — including
    one from a hostile container's own `__iter__`/`items`, or a `RecursionError`
    backstop — also means the value cannot be cleanly hashed, so it is treated
    as non-encodable rather than allowed to escape. `BaseException`
    (KeyboardInterrupt, SystemExit) is intentionally NOT caught.
    """

    try:
        bounded_json_utf8_size(
            value,
            max_bytes=MAX_CANONICAL_BYTES_V1,
            max_depth=MAX_CANONICAL_DEPTH_V1,
        )
    except Exception:  # noqa: BLE001 - a safety predicate must be total, not lucky
        return False
    return True


def is_canonically_encodable_without_size_limit(value: object) -> bool:
    """Return True iff `value` can hash safely, ignoring only byte/item caps.

    This is for verifier surfaces that must accept any receipt emitted by their
    own runner. It preserves the crash-vector guards (surrogates, unsupported
    types, floats, non-string keys, and over-depth nesting) without imposing a
    size ceiling lower than the runner's maximum valid output.
    """

    def string_has_surrogate(text: str) -> bool:
        try:
            for ch in text:
                codepoint = ord(ch)
                if 0xD800 <= codepoint <= 0xDFFF:
                    return True
        except Exception:  # noqa: BLE001 - hostile str subclasses must refuse
            return True
        return False

    try:
        stack: list[tuple[object, int]] = [(value, MAX_CANONICAL_DEPTH_V1)]
        while stack:
            current, depth = stack.pop()
            if depth <= 0:
                return False
            if current is None or current is True or current is False:
                continue
            if isinstance(current, float):
                return False
            if isinstance(current, int) and not isinstance(current, bool):
                continue
            if isinstance(current, str):
                if string_has_surrogate(current):
                    return False
                continue
            if isinstance(current, (list, tuple)):
                for item in current:
                    stack.append((item, depth - 1))
                continue
            if isinstance(current, dict):
                for key, item in current.items():
                    if not isinstance(key, str) or string_has_surrogate(key):
                        return False
                    stack.append((item, depth - 1))
                continue
            return False
    except Exception:  # noqa: BLE001 - this probe is a total safety predicate
        return False
    return True


def safe_field_label(key: object) -> str:
    """Render `key` as a canonical-safe, never-raising field label.

    Benign `str` names pass through byte-identically. A name carrying surrogate
    code points is ASCII-escaped (so it is canonically encodable). An object
    whose `__str__`/`__repr__` raises becomes a fixed placeholder rather than
    letting the hostile code run inside error formatting. The result is always
    canonical-JSON encodable.
    """

    if type(key) is str:
        text = key
    else:
        try:
            text = str(key)
        except Exception:  # noqa: BLE001 - hostile __str__/__repr__ must not escape
            return UNRENDERABLE_FIELD_LABEL
    try:
        text.encode("utf-8")
    except UnicodeEncodeError:
        return ascii(text)
    except Exception:  # noqa: BLE001 - a hostile __str__/__repr__ must not escape
        return UNRENDERABLE_FIELD_LABEL
    return text
