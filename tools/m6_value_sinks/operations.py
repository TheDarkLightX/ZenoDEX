"""Durable-write operation vocabulary for the M6 value-sink inventory.

Discovery keys on the operation performed rather than on the identifier that
performs it, so a renamed writer symbol cannot change an observation.  The
vocabulary is a table so that adding a family is a data edit instead of another
branch in a conditional chain.

Nothing here reads the filesystem.  Callers supply parsed source.
"""

from __future__ import annotations

import ast
import hashlib
import re
from dataclasses import dataclass
from typing import Mapping

# Operations reached through a module attribute, keyed by (module, attribute).
MODULE_OPERATIONS: Mapping[tuple[str, str], str] = {
    ("os", "chmod"): "PERMISSION_MUTATE",
    ("os", "chown"): "PERMISSION_MUTATE",
    ("os", "fchmod"): "PERMISSION_MUTATE",
    ("os", "ftruncate"): "TRUNCATE",
    ("os", "lchown"): "PERMISSION_MUTATE",
    ("os", "link"): "NAMESPACE_LINK",
    ("os", "makedirs"): "DIRECTORY_CREATE",
    ("os", "mkdir"): "DIRECTORY_CREATE",
    ("os", "open"): "DESCRIPTOR_OPEN_UNKNOWN",
    ("os", "pwrite"): "DESCRIPTOR_WRITE",
    ("os", "remove"): "UNLINK",
    ("os", "removedirs"): "UNLINK",
    ("os", "rename"): "RENAME",
    ("os", "renames"): "RENAME",
    ("os", "replace"): "ATOMIC_REPLACE",
    ("os", "rmdir"): "UNLINK",
    ("os", "symlink"): "NAMESPACE_LINK",
    ("os", "truncate"): "TRUNCATE",
    ("os", "unlink"): "UNLINK",
    ("os", "write"): "DESCRIPTOR_WRITE",
    ("os", "writev"): "DESCRIPTOR_WRITE",
    ("shutil", "copy"): "TREE_MUTATE",
    ("shutil", "copy2"): "TREE_MUTATE",
    ("shutil", "copyfile"): "TREE_MUTATE",
    ("shutil", "copytree"): "TREE_MUTATE",
    ("shutil", "move"): "TREE_MUTATE",
    ("shutil", "rmtree"): "TREE_MUTATE",
}

TRACKED_MODULES = frozenset(module for module, _ in MODULE_OPERATIONS)

# Operations reached through an attribute on any receiver.  The receiver type is
# unknown at scan time, so over-detection is preferred: an extra classification
# costs one manifest row, an omission hides a durable writer.
RECEIVER_OPERATIONS: Mapping[str, str] = {
    "chmod": "PERMISSION_MUTATE",
    "hardlink_to": "NAMESPACE_LINK",
    "lchmod": "PERMISSION_MUTATE",
    "rename": "RENAME",
    "rmdir": "UNLINK",
    "symlink_to": "NAMESPACE_LINK",
    "touch": "PATH_TOUCH",
    "unlink": "UNLINK",
    "write_bytes": "PATH_WRITE",
    "write_text": "PATH_WRITE",
}

SQL_EXECUTE_ATTRIBUTES = frozenset({"execute", "executemany", "executescript"})

SINK_KINDS = frozenset(
    set(MODULE_OPERATIONS.values())
    | set(RECEIVER_OPERATIONS.values())
    | {
        "ATOMIC_REPLACE",
        "DESCRIPTOR_OPEN_WRITE",
        "OPEN_MODE_UNKNOWN",
        "OPEN_WRITE",
        "PATH_REPLACE",
        "SQL_DYNAMIC",
        "SQL_PRAGMA_WRITE",
        "SQL_WRITE",
        "STATE_ATTRIBUTE_ASSIGN",
    }
)

_MUTATING_OPEN_MODE_RE = re.compile(r"[wax+]")

_OS_OPEN_WRITE_FLAGS = frozenset(
    {
        "O_APPEND",
        "O_CREAT",
        "O_EXCL",
        "O_RDWR",
        "O_TMPFILE",
        "O_TRUNC",
        "O_WRONLY",
    }
)
_OS_OPEN_READ_FLAGS = frozenset(
    {
        "O_BINARY",
        "O_CLOEXEC",
        "O_DIRECTORY",
        "O_DSYNC",
        "O_NOINHERIT",
        "O_NOCTTY",
        "O_NOFOLLOW",
        "O_NONBLOCK",
        "O_PATH",
        "O_RANDOM",
        "O_RDONLY",
        "O_RSYNC",
        "O_SEQUENTIAL",
        "O_SYNC",
        "O_TEXT",
    }
)

# Statement verbs that create, destroy, or alter durable rows or schema.
_SQL_WRITE_VERBS = (
    "ALTER",
    "ATTACH",
    "CREATE",
    "DELETE",
    "DETACH",
    "DROP",
    "GRANT",
    "INSERT",
    "MERGE",
    "REINDEX",
    "RENAME",
    "REPLACE",
    "REVOKE",
    "TRUNCATE",
    "UPDATE",
    "UPSERT",
    "VACUUM",
)
_SQL_WRITE_RE = re.compile(rf"\s*(?:{'|'.join(_SQL_WRITE_VERBS)})\b", re.IGNORECASE)
# A common table expression may hide a write behind a leading WITH clause.
_SQL_CTE_RE = re.compile(
    rf"\s*WITH\b.*?\b(?:{'|'.join(_SQL_WRITE_VERBS)})\b", re.IGNORECASE | re.DOTALL
)
# ``PRAGMA name = value`` mutates durable database configuration; a bare read does not.
_SQL_PRAGMA_WRITE_RE = re.compile(r"\s*PRAGMA\b[^;]*=", re.IGNORECASE)


@dataclass(frozen=True, slots=True)
class ImportBindingsV2:
    """Names bound to tracked modules and to directly imported operations."""

    module_aliases: Mapping[str, str]
    direct_aliases: Mapping[str, tuple[str, str]]


def resolve_import_bindings(tree: ast.Module) -> ImportBindingsV2:
    """Bind local names to tracked modules and directly imported operations.

    ``import os as _o`` and ``from os import replace as move`` both keep the
    operation observable, so alias tracking is part of the operation identity
    rather than an optional convenience.
    """

    return ImportBindingsV2(
        module_aliases=_module_alias_bindings(tree),
        direct_aliases=_direct_alias_bindings(tree),
    )


def _module_alias_bindings(tree: ast.Module) -> dict[str, str]:
    return {
        alias.asname or alias.name: alias.name
        for node in ast.walk(tree)
        if isinstance(node, ast.Import)
        for alias in node.names
        if alias.name in TRACKED_MODULES
    }


def _direct_alias_bindings(tree: ast.Module) -> dict[str, tuple[str, str]]:
    return {
        alias.asname or alias.name: (str(node.module), alias.name)
        for node in ast.walk(tree)
        if isinstance(node, ast.ImportFrom) and node.level == 0 and node.module in TRACKED_MODULES
        for alias in node.names
        if (node.module, alias.name) in MODULE_OPERATIONS
    }


def classify_sql_statement(statement: str | None) -> str | None:
    """Classify one SQL statement, treating an unresolved statement as a write."""

    if statement is None:
        # A statement built at runtime cannot be shown to leave value state intact.
        return "SQL_DYNAMIC"
    if _SQL_PRAGMA_WRITE_RE.match(statement) is not None:
        return "SQL_PRAGMA_WRITE"
    if _SQL_WRITE_RE.match(statement) is not None:
        return "SQL_WRITE"
    if _SQL_CTE_RE.match(statement) is not None:
        return "SQL_WRITE"
    return None


def literal_string_argument(call: ast.Call, index: int = 0) -> str | None:
    if len(call.args) <= index:
        return None
    value = call.args[index]
    return value.value if isinstance(value, ast.Constant) and isinstance(value.value, str) else None


@dataclass(frozen=True, slots=True)
class OpenModeV2:
    """Tri-state mode of an ``open`` call.

    An absent mode is the documented read default and is safe.  A present but
    unresolved mode is unknown, and an unknown mode may be a write, so it must
    never collapse into the safe case.
    """

    present: bool
    literal: str | None


def open_mode(call: ast.Call, *, mode_index: int) -> OpenModeV2:
    """Read the mode argument in positional, keyword, or unpacked form."""

    if len(call.args) > mode_index:
        value = call.args[mode_index]
        if isinstance(value, ast.Constant) and isinstance(value.value, str):
            return OpenModeV2(present=True, literal=value.value)
        return OpenModeV2(present=True, literal=None)
    for keyword in call.keywords:
        if keyword.arg == "mode":
            value = keyword.value
            if isinstance(value, ast.Constant) and isinstance(value.value, str):
                return OpenModeV2(present=True, literal=value.value)
            return OpenModeV2(present=True, literal=None)
        if keyword.arg is None:
            # ``**options`` may carry a mode that cannot be read here.
            return OpenModeV2(present=True, literal=None)
    return OpenModeV2(present=False, literal=None)


def classify_open_call(call: ast.Call, *, mode_index: int) -> str | None:
    """Classify an ``open`` call, keeping an unresolved mode observable."""

    mode = open_mode(call, mode_index=mode_index)
    if not mode.present:
        return None
    if mode.literal is None:
        return "OPEN_MODE_UNKNOWN"
    return "OPEN_WRITE" if _MUTATING_OPEN_MODE_RE.search(mode.literal) is not None else None


def _os_open_flag_class(expression: ast.expr) -> str:
    """Classify one statically visible ``os.open`` flag expression."""

    if isinstance(expression, ast.BinOp) and isinstance(expression.op, ast.BitOr):
        classes = {_os_open_flag_class(expression.left), _os_open_flag_class(expression.right)}
        if "WRITE" in classes:
            return "WRITE"
        return "UNKNOWN" if "UNKNOWN" in classes else "READ"
    if isinstance(expression, ast.Attribute):
        name = expression.attr
    elif isinstance(expression, ast.Name):
        name = expression.id
    elif isinstance(expression, ast.Constant) and type(expression.value) is int:
        return "READ" if expression.value == 0 else "UNKNOWN"
    else:
        return "UNKNOWN"
    if name in _OS_OPEN_WRITE_FLAGS:
        return "WRITE"
    return "READ" if name in _OS_OPEN_READ_FLAGS else "UNKNOWN"


def classify_os_open_call(call: ast.Call) -> str | None:
    """Distinguish read-only, write-capable, and unresolved descriptor opens."""

    flags: ast.expr | None = call.args[1] if len(call.args) > 1 else None
    if flags is None:
        for keyword in call.keywords:
            if keyword.arg == "flags":
                flags = keyword.value
                break
            if keyword.arg is None:
                return "DESCRIPTOR_OPEN_UNKNOWN"
    if flags is None:
        return "DESCRIPTOR_OPEN_UNKNOWN"
    classification = _os_open_flag_class(flags)
    if classification == "READ":
        return None
    return "DESCRIPTOR_OPEN_WRITE" if classification == "WRITE" else "DESCRIPTOR_OPEN_UNKNOWN"


def is_unary_call(call: ast.Call) -> bool:
    """Separate ``Path.replace(target)`` from ``str.replace(old, new)`` by arity."""

    return len(call.args) == 1 and not call.keywords and not isinstance(call.args[0], ast.Starred)


def operation_fingerprint(kind: str, node: ast.AST) -> str:
    """Derive a source-shape fingerprint for one observed operation.

    The dump keeps argument expressions and drops source positions, so moving an
    operation from an evidence destination to a value-state destination changes
    the fingerprint while reformatting does not.
    """

    rendered = ast.dump(node, annotate_fields=True, include_attributes=False)
    payload = b"zenodex-m6-operation-v2\0" + kind.encode("ascii") + b"\0" + rendered.encode("utf-8")
    return hashlib.sha256(payload).hexdigest()


def combine_fingerprints(fingerprints: tuple[str, ...]) -> str:
    """Bind every occurrence of one identity into a single canonical digest."""

    payload = b"zenodex-m6-identity-v2\0" + b"\0".join(
        value.encode("ascii") for value in sorted(fingerprints)
    )
    return hashlib.sha256(payload).hexdigest()
