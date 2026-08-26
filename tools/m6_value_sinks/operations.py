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
import urllib.parse
from collections import Counter, deque
from dataclasses import dataclass
from types import MappingProxyType
from typing import Mapping, Sequence

# Operations reached through a module attribute, keyed by (module, attribute).
MODULE_OPERATIONS: Mapping[tuple[str, str], str] = {
    ("os", "chmod"): "PERMISSION_MUTATE",
    ("os", "chown"): "PERMISSION_MUTATE",
    ("os", "fchmod"): "PERMISSION_MUTATE",
    ("os", "ftruncate"): "TRUNCATE",
    ("os", "lchown"): "PERMISSION_MUTATE",
    ("os", "link"): "NAMESPACE_LINK",
    ("os", "makedirs"): "NAMESPACE_CREATE",
    ("os", "mkdir"): "NAMESPACE_CREATE",
    ("os", "mknod"): "NAMESPACE_CREATE",
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
    ("tempfile", "mkdtemp"): "TEMPDIR_CREATE",
    ("tempfile", "mkstemp"): "TEMPFILE_CREATE",
}

# Which positional arguments name economically relevant path operands.  A
# rename, replace, link, or copy moves value between two roles, so binding only
# the destination would leave the source unbound.
MODULE_OPERAND_INDICES: Mapping[tuple[str, str], tuple[int, ...]] = {
    ("os", "chmod"): (0,),
    ("os", "chown"): (0,),
    ("os", "fchmod"): (0,),
    ("os", "ftruncate"): (0,),
    ("os", "lchown"): (0,),
    ("os", "link"): (0, 1),
    ("os", "makedirs"): (0,),
    ("os", "mkdir"): (0,),
    ("os", "mknod"): (0,),
    ("os", "pwrite"): (0,),
    ("os", "remove"): (0,),
    ("os", "removedirs"): (0,),
    ("os", "rename"): (0, 1),
    ("os", "renames"): (0, 1),
    ("os", "replace"): (0, 1),
    ("os", "rmdir"): (0,),
    ("os", "symlink"): (0, 1),
    ("os", "truncate"): (0,),
    ("os", "unlink"): (0,),
    ("os", "write"): (0,),
    ("os", "writev"): (0,),
    ("shutil", "copy"): (0, 1),
    ("shutil", "copy2"): (0, 1),
    ("shutil", "copyfile"): (0, 1),
    ("shutil", "copytree"): (0, 1),
    ("shutil", "move"): (0, 1),
    ("shutil", "rmtree"): (0,),
    ("tempfile", "mkdtemp"): (2,),
    ("tempfile", "mkstemp"): (2,),
}

# Operations reached through an attribute on any receiver.  The receiver type is
# unknown at scan time, so over-detection is preferred: an extra classification
# costs one manifest row, an omission hides a durable writer.
# Keyword spellings for the same operands, so ``os.replace(src=a, dst=b)`` binds
# exactly what ``os.replace(a, b)`` binds.
MODULE_OPERAND_KEYWORDS: Mapping[tuple[str, str], tuple[str, ...]] = {
    ("os", "chmod"): ("path",),
    ("os", "chown"): ("path",),
    ("os", "fchmod"): ("fd",),
    ("os", "ftruncate"): ("fd",),
    ("os", "lchown"): ("path",),
    ("os", "link"): ("src", "dst"),
    ("os", "makedirs"): ("name",),
    ("os", "mkdir"): ("path",),
    ("os", "mknod"): ("path",),
    ("os", "pwrite"): ("fd",),
    ("os", "remove"): ("path",),
    ("os", "removedirs"): ("name",),
    ("os", "rename"): ("src", "dst"),
    ("os", "renames"): ("old", "new"),
    ("os", "replace"): ("src", "dst"),
    ("os", "rmdir"): ("path",),
    ("os", "symlink"): ("src", "dst"),
    ("os", "truncate"): ("path",),
    ("os", "unlink"): ("path",),
    ("os", "write"): ("fd",),
    ("os", "writev"): ("fd",),
    ("shutil", "copy"): ("src", "dst"),
    ("shutil", "copy2"): ("src", "dst"),
    ("shutil", "copyfile"): ("src", "dst"),
    ("shutil", "copytree"): ("src", "dst"),
    ("shutil", "move"): ("src", "dst"),
    ("shutil", "rmtree"): ("path",),
    ("tempfile", "mkdtemp"): ("dir",),
    ("tempfile", "mkstemp"): ("dir",),
}

RECEIVER_OPERATIONS: Mapping[str, str] = {
    "chmod": "PERMISSION_MUTATE",
    "hardlink_to": "NAMESPACE_LINK",
    "lchmod": "PERMISSION_MUTATE",
    "makedirs": "NAMESPACE_CREATE",
    "mkdir": "NAMESPACE_CREATE",
    "rmdir": "UNLINK",
    "symlink_to": "NAMESPACE_LINK",
    "touch": "NAMESPACE_CREATE",
    "commit": "TRANSACTION_COMMIT",
    "truncate": "TRUNCATE",
    "unlink": "UNLINK",
    "write": "HANDLE_WRITE",
    "write_bytes": "PATH_WRITE",
    "write_text": "PATH_WRITE",
    "writelines": "HANDLE_WRITE",
}

# ``os.open`` takes integer flags rather than a mode string.
_WRITABLE_OPEN_FLAGS = frozenset({"O_WRONLY", "O_RDWR", "O_CREAT", "O_APPEND", "O_TRUNC", "O_EXCL"})
_READONLY_OPEN_FLAGS = frozenset({"O_RDONLY", "O_CLOEXEC", "O_NOFOLLOW", "O_PATH", "O_DIRECTORY", "O_NONBLOCK"})
_KNOWN_OPEN_FLAGS = _WRITABLE_OPEN_FLAGS | _READONLY_OPEN_FLAGS

# These functions need argument inspection rather than a fixed kind. Built-in
# ``open`` is modelled through its actual ``builtins`` provenance so an alias or
# a shadowed spelling cannot disappear into, or masquerade as, the direct form.
SPECIAL_MODULE_FUNCTIONS: frozenset[tuple[str, str]] = frozenset(
    {
        ("builtins", "open"),
        ("os", "fdopen"),
        ("os", "open"),
        ("sqlite3", "connect"),
        ("tempfile", "NamedTemporaryFile"),
        ("tempfile", "TemporaryDirectory"),
    }
)
EXECUTABLE_MODULE_FUNCTIONS: Mapping[tuple[str, str], str] = {
    ("builtins", "eval"): "dynamic_eval",
    ("builtins", "exec"): "dynamic_exec",
}
TRACKED_MODULES = frozenset(
    {module for module, _ in MODULE_OPERATIONS}
    | {module for module, _ in SPECIAL_MODULE_FUNCTIONS}
    | {module for module, _ in EXECUTABLE_MODULE_FUNCTIONS}
)
_IMPLICIT_BUILTIN_OPERATIONS: Mapping[str, tuple[str, str]] = {
    "eval": ("builtins", "eval"),
    "exec": ("builtins", "exec"),
    "open": ("builtins", "open"),
}

_RECEIVER_TARGET_MODULE = "<receiver>"

# ``ast.TypeAlias`` exists from Python 3.12; its name is a binder when present.
_TYPE_ALIAS = getattr(ast, "TypeAlias", None)

SQL_EXECUTE_ATTRIBUTES = frozenset({"execute", "executemany", "executescript"})
_ALIASABLE_RECEIVER_ATTRIBUTES = frozenset(RECEIVER_OPERATIONS) | SQL_EXECUTE_ATTRIBUTES

SINK_KINDS = frozenset(
    set(MODULE_OPERATIONS.values())
    | set(RECEIVER_OPERATIONS.values())
    | {
        "ALIAS_TARGET_UNKNOWN",
        "ATOMIC_REPLACE",
        "DESCRIPTOR_OPEN_UNKNOWN",
        "DESCRIPTOR_OPEN_WRITE",
        "DATABASE_OPEN_EPHEMERAL",
        "DATABASE_OPEN_UNKNOWN",
        "DATABASE_OPEN_WRITE",
        "HANDLE_WRITE",
        "NAMESPACE_CREATE",
        "NAMESPACE_LINK",
        "OPEN_MODE_UNKNOWN",
        "OPEN_WRITE",
        "PATH_REPLACE",
        "UNLINK",
        "SQL_DYNAMIC",
        "SQL_PRAGMA_WRITE",
        "SQL_WRITE",
        "STATE_ATTRIBUTE_ASSIGN",
        "TEMPDIR_CREATE",
        "TEMPDIR_CREATE_EPHEMERAL",
        "TEMPDIR_CREATE_UNKNOWN",
        "TEMPFILE_CREATE",
        "TEMPFILE_CREATE_EPHEMERAL",
        "TEMPFILE_CREATE_UNKNOWN",
        "UNMODELLED_WRITER_REFERENCE",
    }
)

_MUTATING_OPEN_MODE_RE = re.compile(r"[wax+]")
_READ_ONLY_OPEN_MODES = frozenset({"r", "rb", "br", "rt", "tr"})
_OPEN_MODE_CHARACTERS = frozenset("rwaxtb+")

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
_SQL_CTE_RE = re.compile(rf"\s*WITH\b.*?\b(?:{'|'.join(_SQL_WRITE_VERBS)})\b", re.IGNORECASE | re.DOTALL)
# ``PRAGMA name = value`` mutates database configuration. Bare forms require an
# explicit SQLite allowlist because some no-argument pragmas mutate durable
# state (for example ``incremental_vacuum`` and ``optimize``).
_SQL_PRAGMA_WRITE_RE = re.compile(r"\s*PRAGMA\b[^;]*=", re.IGNORECASE)
_SQL_PROVED_READ_RE = re.compile(r"\s*(?:SELECT|EXPLAIN|VALUES)\b", re.IGNORECASE)
_SQL_BARE_PRAGMA_RE = re.compile(
    r"\s*PRAGMA\s+(?:(?:[A-Za-z_][A-Za-z0-9_]*)\.)?"
    r"(?P<name>[A-Za-z_][A-Za-z0-9_]*)\s*\Z",
    re.IGNORECASE,
)
_SQL_BARE_PRAGMA_READ_ONLY = frozenset(
    {
        "application_id",
        "auto_vacuum",
        "busy_timeout",
        "cache_size",
        "cache_spill",
        "cell_size_check",
        "checkpoint_fullfsync",
        "collation_list",
        "compile_options",
        "data_version",
        "database_list",
        "defer_foreign_keys",
        "encoding",
        "foreign_key_check",
        "foreign_keys",
        "freelist_count",
        "fullfsync",
        "function_list",
        "hard_heap_limit",
        "ignore_check_constraints",
        "integrity_check",
        "journal_mode",
        "journal_size_limit",
        "legacy_alter_table",
        "locking_mode",
        "max_page_count",
        "mmap_size",
        "module_list",
        "page_count",
        "page_size",
        "pragma_list",
        "query_only",
        "quick_check",
        "read_uncommitted",
        "recursive_triggers",
        "reverse_unordered_selects",
        "schema_version",
        "secure_delete",
        "soft_heap_limit",
        "synchronous",
        "table_list",
        "temp_store",
        "threads",
        "trusted_schema",
        "user_version",
        "wal_autocheckpoint",
    }
)
_SQL_BARE_PRAGMA_WRITES = frozenset(
    {"incremental_vacuum", "optimize", "wal_checkpoint"}
)
_SQL_PRAGMA_CALL_WRITE_RE = re.compile(
    r"\s*PRAGMA\s+(?:[A-Za-z_][A-Za-z0-9_]*\.)?"
    r"(?:application_id|auto_vacuum|cache_size|foreign_keys|journal_mode|"
    r"incremental_vacuum|journal_size_limit|locking_mode|max_page_count|mmap_size|optimize|page_size|"
    r"secure_delete|synchronous|temp_store|trusted_schema|user_version|"
    r"wal_autocheckpoint|wal_checkpoint)\s*\(",
    re.IGNORECASE,
)
MAX_SQL_SCRIPT_CHARACTERS = 1_048_576
MAX_SQL_STATEMENTS = 4096


def _strip_leading_sql_comments(statement: str) -> str | None:
    """Remove only complete leading SQL comments before verb classification."""

    cursor = 0
    length = len(statement)
    while True:
        while cursor < length and statement[cursor].isspace():
            cursor += 1
        if statement.startswith("--", cursor):
            newline = statement.find("\n", cursor + 2)
            if newline < 0:
                return ""
            cursor = newline + 1
            continue
        if statement.startswith("/*", cursor):
            close = statement.find("*/", cursor + 2)
            if close < 0:
                return None
            cursor = close + 2
            continue
        return statement[cursor:]


@dataclass(frozen=True, slots=True)
class ImportBindingsV2:
    """Names bound to tracked modules and to directly bound operations.

    ``special_aliases`` holds operations whose kind depends on their arguments,
    so a direct import or a reassignment of ``os.open`` stays classified by the
    same flag and mode rules as the attribute form.
    """

    module_aliases: Mapping[str, str]
    direct_aliases: Mapping[str, tuple[str, str]]
    special_aliases: Mapping[str, tuple[str, str]]
    receiver_aliases: Mapping[str, tuple[str, str]]
    executable_aliases: Mapping[str, tuple[str, str]]
    flag_aliases: Mapping[str, str]
    ambiguous_aliases: frozenset[str]
    ambiguous_writer_aliases: frozenset[str]
    ambiguous_executable_aliases: frozenset[str]
    rebound_module_aliases: Mapping[str, frozenset[str]]
    reflection_helpers: frozenset[str]


@dataclass(frozen=True, slots=True)
class CallableResolutionV2:
    """One exact callable target, or an explicitly unresolved provenance edge."""

    target: tuple[str, str] | None
    unresolved: bool = False


def _known_callable_target(target: tuple[str, str]) -> bool:
    return (
        target in MODULE_OPERATIONS
        or target in SPECIAL_MODULE_FUNCTIONS
        or target in EXECUTABLE_MODULE_FUNCTIONS
        or (target[0] == _RECEIVER_TARGET_MODULE and target[1] in _ALIASABLE_RECEIVER_ATTRIBUTES)
    )


def callable_target_is_writer(target: tuple[str, str]) -> bool:
    """Return whether an exact target belongs to the durable-writer vocabulary."""

    return target not in EXECUTABLE_MODULE_FUNCTIONS and _known_callable_target(target)


def _module_name(
    expression: ast.expr,
    module_aliases: Mapping[str, str],
    rebound_modules: Mapping[str, frozenset[str]],
) -> tuple[str | None, bool]:
    if not isinstance(expression, ast.Name):
        return None, False
    module = module_aliases.get(expression.id)
    if module is not None:
        return module, False
    return None, expression.id in rebound_modules


def _module_dictionary(
    expression: ast.expr,
    module_aliases: Mapping[str, str],
    rebound_modules: Mapping[str, frozenset[str]],
    reflection_helpers: frozenset[str],
) -> tuple[str | None, bool]:
    if isinstance(expression, ast.Attribute) and expression.attr == "__dict__":
        return _module_name(expression.value, module_aliases, rebound_modules)
    if (
        isinstance(expression, ast.Call)
        and isinstance(expression.func, ast.Name)
        and expression.func.id == "vars"
        and len(expression.args) == 1
        and not expression.keywords
    ):
        module, rebound = _module_name(
            expression.args[0], module_aliases, rebound_modules
        )
        if "vars" not in reflection_helpers:
            return None, module is not None or rebound
        return module, rebound
    return None, False


def _constant_string(expression: ast.expr) -> str | None:
    value = expression.value if isinstance(expression, ast.Constant) else None
    return value if isinstance(value, str) else None


def _receiver_dictionary(
    expression: ast.expr,
    module_aliases: Mapping[str, str],
    rebound_modules: Mapping[str, frozenset[str]],
    reflection_helpers: frozenset[str],
) -> bool:
    """Recognize an exact receiver ``__dict__`` or unshadowed ``vars(receiver)``."""

    if isinstance(expression, ast.Attribute) and expression.attr == "__dict__":
        module, rebound = _module_name(
            expression.value, module_aliases, rebound_modules
        )
        return module is None and not rebound
    if (
        isinstance(expression, ast.Call)
        and isinstance(expression.func, ast.Name)
        and expression.func.id == "vars"
        and "vars" in reflection_helpers
        and len(expression.args) == 1
        and not expression.keywords
    ):
        module, rebound = _module_name(
            expression.args[0], module_aliases, rebound_modules
        )
        return module is None and not rebound
    return False


def _dictionary_get_call(expression: ast.expr) -> tuple[ast.expr, ast.expr] | None:
    if (
        isinstance(expression, ast.Call)
        and isinstance(expression.func, ast.Attribute)
        and expression.func.attr == "get"
        and len(expression.args) in {1, 2}
        and not any(isinstance(argument, ast.Starred) for argument in expression.args)
        and not expression.keywords
    ):
        return expression.func.value, expression.args[0]
    return None


def _static_callable_resolution(
    expression: ast.expr,
    module_aliases: Mapping[str, str],
    rebound_modules: Mapping[str, frozenset[str]],
    reflection_helpers: frozenset[str],
) -> CallableResolutionV2:
    """Resolve closed Attribute, Subscript, getattr, vars, and __dict__ forms."""

    if isinstance(expression, ast.Attribute):
        module, rebound = _module_name(expression.value, module_aliases, rebound_modules)
        if module is not None:
            target = (module, expression.attr)
            return CallableResolutionV2(target if _known_callable_target(target) else None)
        if rebound:
            return CallableResolutionV2(None, True)
        if expression.attr in _ALIASABLE_RECEIVER_ATTRIBUTES:
            return CallableResolutionV2((_RECEIVER_TARGET_MODULE, expression.attr))
        return CallableResolutionV2(None)
    if isinstance(expression, ast.Subscript):
        module, rebound = _module_dictionary(
            expression.value, module_aliases, rebound_modules, reflection_helpers
        )
        attribute = _constant_string(expression.slice)
        if module is None:
            if rebound:
                return CallableResolutionV2(None, True)
            if _receiver_dictionary(
                expression.value,
                module_aliases,
                rebound_modules,
                reflection_helpers,
            ):
                if attribute is None:
                    return CallableResolutionV2(None, True)
                target = (_RECEIVER_TARGET_MODULE, attribute)
                return CallableResolutionV2(
                    target if _known_callable_target(target) else None
                )
            return CallableResolutionV2(None)
        if attribute is None:
            return CallableResolutionV2(None, True)
        target = (module, attribute)
        return CallableResolutionV2(
            target if _known_callable_target(target) else None,
            not _known_callable_target(target),
        )
    dictionary_get = _dictionary_get_call(expression)
    if dictionary_get is not None:
        dictionary, key = dictionary_get
        module, rebound = _module_dictionary(
            dictionary,
            module_aliases,
            rebound_modules,
            reflection_helpers,
        )
        attribute = _constant_string(key)
        if module is not None:
            if attribute is None:
                return CallableResolutionV2(None, True)
            target = (module, attribute)
            return CallableResolutionV2(
                target if _known_callable_target(target) else None,
                not _known_callable_target(target),
            )
        if rebound:
            return CallableResolutionV2(None, True)
        if _receiver_dictionary(
            dictionary,
            module_aliases,
            rebound_modules,
            reflection_helpers,
        ):
            if attribute is None:
                return CallableResolutionV2(None, True)
            target = (_RECEIVER_TARGET_MODULE, attribute)
            return CallableResolutionV2(
                target if _known_callable_target(target) else None
            )
        return CallableResolutionV2(None)
    if (
        isinstance(expression, ast.Call)
        and isinstance(expression.func, ast.Name)
        and expression.func.id == "getattr"
        and len(expression.args) in {2, 3}
        and not any(isinstance(argument, ast.Starred) for argument in expression.args)
        and not expression.keywords
    ):
        module, rebound = _module_name(
            expression.args[0], module_aliases, rebound_modules
        )
        if "getattr" not in reflection_helpers:
            return CallableResolutionV2(None, module is not None or rebound)
        attribute = _constant_string(expression.args[1])
        if module is None:
            if rebound:
                return CallableResolutionV2(None, True)
            if attribute in _ALIASABLE_RECEIVER_ATTRIBUTES:
                return CallableResolutionV2(
                    (_RECEIVER_TARGET_MODULE, attribute)
                )
            return CallableResolutionV2(None, attribute is None)
        if attribute is None:
            return CallableResolutionV2(None, True)
        target = (module, attribute)
        return CallableResolutionV2(
            target if _known_callable_target(target) else None,
            not _known_callable_target(target),
        )
    return CallableResolutionV2(None)


def resolve_callable_expression(
    expression: ast.expr, bindings: ImportBindingsV2
) -> CallableResolutionV2:
    """Resolve one call expression without guessing through ambiguity."""

    if isinstance(expression, ast.Name):
        if expression.id in bindings.ambiguous_aliases:
            return CallableResolutionV2(None, True)
        for aliases in (
            bindings.direct_aliases,
            bindings.special_aliases,
            bindings.receiver_aliases,
            bindings.executable_aliases,
        ):
            target = aliases.get(expression.id)
            if target is not None:
                return CallableResolutionV2(target)
        return CallableResolutionV2(None)
    return _static_callable_resolution(
        expression,
        bindings.module_aliases,
        bindings.rebound_module_aliases,
        bindings.reflection_helpers,
    )


def _possible_modules(
    expression: ast.expr, bindings: ImportBindingsV2
) -> frozenset[str]:
    """Return only source-derived module candidates for an ambiguous expression."""

    if not isinstance(expression, ast.Name):
        return frozenset()
    exact = bindings.module_aliases.get(expression.id)
    if exact is not None:
        return frozenset((exact,))
    return bindings.rebound_module_aliases.get(expression.id, frozenset())


def _possible_dictionary_modules(
    expression: ast.expr, bindings: ImportBindingsV2
) -> frozenset[str]:
    if isinstance(expression, ast.Attribute) and expression.attr == "__dict__":
        return _possible_modules(expression.value, bindings)
    if (
        isinstance(expression, ast.Call)
        and isinstance(expression.func, ast.Name)
        and expression.func.id == "vars"
        and len(expression.args) == 1
        and not expression.keywords
    ):
        return _possible_modules(expression.args[0], bindings)
    return frozenset()


def callable_expression_may_target_executable(
    expression: ast.expr, bindings: ImportBindingsV2
) -> bool:
    """Fail closed when an unresolved callable may denote tracked code execution.

    This predicate does not invent a precise target. It recognizes the closed
    Attribute/Subscript/getattr/vars/__dict__ grammar and reports only whether
    source provenance leaves a tracked executable target possible.
    """

    resolution = resolve_callable_expression(expression, bindings)
    if resolution.target in EXECUTABLE_MODULE_FUNCTIONS:
        return True
    if not resolution.unresolved:
        return False
    if isinstance(expression, ast.Name):
        return expression.id in bindings.ambiguous_executable_aliases

    modules: frozenset[str]
    attribute: str | None
    if isinstance(expression, ast.Attribute):
        modules = _possible_modules(expression.value, bindings)
        attribute = expression.attr
    elif isinstance(expression, ast.Subscript):
        modules = _possible_dictionary_modules(expression.value, bindings)
        attribute = _constant_string(expression.slice)
    elif (
        isinstance(expression, ast.Call)
        and isinstance(expression.func, ast.Name)
        and expression.func.id == "getattr"
        and len(expression.args) in {2, 3}
        and not any(isinstance(argument, ast.Starred) for argument in expression.args)
        and not expression.keywords
    ):
        modules = _possible_modules(expression.args[0], bindings)
        attribute = _constant_string(expression.args[1])
    elif (dictionary_get := _dictionary_get_call(expression)) is not None:
        modules = _possible_dictionary_modules(dictionary_get[0], bindings)
        attribute = _constant_string(dictionary_get[1])
    else:
        return False

    if attribute is None:
        return any(
            module == executable_module
            for module in modules
            for executable_module, _ in EXECUTABLE_MODULE_FUNCTIONS
        )
    return any(
        (module, attribute) in EXECUTABLE_MODULE_FUNCTIONS for module in modules
    )


def unresolved_writer_provenance(tree: ast.Module) -> bool:
    """Report a tracked writer that leaves the closed alias/call grammar.

    A direct call and a simple name-to-name alias chain are modelled precisely.
    Passing a writer as data, putting it in a container, selecting it with
    ``getattr``, or using a rebound/ambiguous alias leaves that grammar.  Such a
    reference is a closure gap because the operation and destination reached by
    the escaped callable are no longer source-proved by this scanner.
    """

    bindings = resolve_import_bindings(tree)
    parents = {
        id(child): parent
        for parent in ast.walk(tree)
        for child in ast.iter_child_nodes(parent)
    }
    precise_aliases = (
        set(bindings.direct_aliases)
        | set(bindings.special_aliases)
        | set(bindings.receiver_aliases)
    )

    for node in ast.walk(tree):
        if isinstance(node, ast.Call) and _is_dynamic_writer_lookup(node, bindings):
            return True
        if isinstance(node, (ast.Attribute, ast.Subscript, ast.Call)):
            resolution = resolve_callable_expression(node, bindings)
            if resolution.unresolved and isinstance(node, (ast.Subscript, ast.Call)):
                return True
            if resolution.target is None or not callable_target_is_writer(resolution.target):
                continue
            if not _is_precisely_consumed_writer_reference(
                node, parents.get(id(node)), precise_aliases
            ):
                return True
        elif isinstance(node, ast.Name) and isinstance(node.ctx, ast.Load):
            if node.id in bindings.ambiguous_writer_aliases:
                return True
            if node.id not in precise_aliases:
                continue
            if not _is_precisely_consumed_writer_reference(
                node, parents.get(id(node)), precise_aliases
            ):
                return True
    return False


def _is_dynamic_writer_lookup(call: ast.Call, bindings: ImportBindingsV2) -> bool:
    function = call.func
    if (
        not isinstance(function, ast.Name)
        or function.id != "getattr"
        or "getattr" not in bindings.reflection_helpers
        or not call.args
    ):
        return False
    base = call.args[0]
    if not isinstance(base, ast.Name) or (
        base.id not in bindings.module_aliases
        and base.id not in bindings.rebound_module_aliases
    ):
        return False
    return resolve_callable_expression(call, bindings).target is None


def _is_precisely_consumed_writer_reference(
    node: ast.expr,
    parent: ast.AST | None,
    precise_aliases: set[str],
) -> bool:
    if isinstance(parent, ast.Call) and parent.func is node:
        return True
    if isinstance(parent, ast.Assign) and parent.value is node:
        targets = [target for target in parent.targets if isinstance(target, ast.Name)]
        return bool(targets) and len(targets) == len(parent.targets) and all(
            target.id in precise_aliases for target in targets
        )
    if isinstance(parent, ast.AnnAssign) and parent.value is node:
        return isinstance(parent.target, ast.Name) and parent.target.id in precise_aliases
    return False


def resolve_import_bindings(tree: ast.Module) -> ImportBindingsV2:
    """Bind local names to tracked modules and directly imported operations.

    ``import os as _o`` and ``from os import replace as move`` both keep the
    operation observable, so alias tracking is part of the operation identity
    rather than an optional convenience.
    """

    assigned = set(_bound_names(tree))
    binding_counts = _binding_counts(tree)
    alias_targets = _alias_assignment_targets(tree)
    alias_assignment_counts = Counter(name for name, _ in _alias_assignments(tree))
    imported_modules = _module_alias_bindings(tree)
    wildcard = has_wildcard_import(tree)
    if wildcard:
        # A star import may rebind any tracked module, operation, or flag name,
        # so every tracked alias in this module becomes unproved.
        assigned |= set(imported_modules) | set(_flag_alias_bindings(tree))
        assigned |= (
            set(_direct_alias_bindings(tree))
            | set(_special_alias_bindings(tree))
            | set(_executable_alias_bindings(tree))
        )
        assigned |= alias_targets
    # A rebound import no longer proves anything about what the name holds, but
    # the name did originate from a tracked module, so calls through it stay
    # observable as unresolved rather than disappearing.
    module_aliases = {
        name: module for name, module in imported_modules.items() if name not in assigned
    }
    rebound_module_aliases = {
        name: modules
        for name, modules in _module_alias_candidates(tree).items()
        if name in assigned
    }
    flag_aliases = {
        name: flag for name, flag in _flag_alias_bindings(tree).items() if name not in assigned
    }
    direct_imports = _direct_alias_bindings(tree)
    special_imports = _special_alias_bindings(tree)
    executable_imports = _executable_alias_bindings(tree)
    explicit_seed_names = set(direct_imports) | set(special_imports) | set(executable_imports)
    reflection_helpers = frozenset(
        helper
        for helper in ("getattr", "vars")
        if binding_counts.get(helper, 0) == 0 and not wildcard
    )
    seeds: dict[str, set[tuple[str, str]]] = {}
    for name, target in direct_imports.items():
        seeds.setdefault(name, set()).add(target)
    for name, target in special_imports.items():
        seeds.setdefault(name, set()).add(target)
    for name, target in executable_imports.items():
        seeds.setdefault(name, set()).add(target)
    for name, target in _IMPLICIT_BUILTIN_OPERATIONS.items():
        # The implicit built-in exists only when no lexical binder can shadow
        # its spelling. Exact ``from builtins import`` and assignment aliases
        # enter through the ordinary seed/graph rules instead.
        if binding_counts.get(name, 0) == 0 and not wildcard:
            seeds.setdefault(name, set()).add(target)
    resolved, unknown = _resolve_alias_chains(
        tree,
        module_aliases,
        rebound_module_aliases,
        reflection_helpers,
        seeds,
    )
    ambiguous: set[str] = set(unknown)
    for name in _IMPLICIT_BUILTIN_OPERATIONS:
        if name not in resolved:
            ambiguous.add(name)
    for name, targets in resolved.items():
        # A shadowed operation alias may hold anything at the call site, so the
        # call stays observable as unresolved instead of keeping its old target.
        expected_bindings = alias_assignment_counts.get(name, 0) + (
            1 if name in explicit_seed_names else 0
        )
        shadowed = (
            wildcard
            or (name in assigned and name not in alias_targets)
            or binding_counts.get(name, 0) > expected_bindings
        )
        if len(targets) != 1 or shadowed:
            ambiguous.add(name)
    for name, value in _alias_assignments(tree):
        if name not in resolved:
            continue
        if isinstance(value, ast.Name):
            source_is_proved = value.id in resolved
        else:
            source_is_proved = _static_callable_resolution(
                value,
                module_aliases,
                rebound_module_aliases,
                reflection_helpers,
            ).target is not None
        if not source_is_proved:
            ambiguous.add(name)
    ambiguous = _propagate_alias_taint(tree, ambiguous)
    direct_aliases: dict[str, tuple[str, str]] = {}
    special_aliases: dict[str, tuple[str, str]] = {}
    receiver_aliases: dict[str, tuple[str, str]] = {}
    executable_aliases: dict[str, tuple[str, str]] = {}
    for name, targets in resolved.items():
        if name in ambiguous or len(targets) != 1:
            continue
        target = next(iter(targets))
        if target in EXECUTABLE_MODULE_FUNCTIONS:
            executable_aliases[name] = target
        elif target[0] == _RECEIVER_TARGET_MODULE:
            receiver_aliases[name] = target
        elif target in SPECIAL_MODULE_FUNCTIONS:
            special_aliases[name] = target
        else:
            direct_aliases[name] = target
    ambiguous_writer_aliases = {
        name
        for name in ambiguous
        if any(callable_target_is_writer(target) for target in resolved.get(name, ()))
        or callable_target_is_writer(_IMPLICIT_BUILTIN_OPERATIONS.get(name, ("", "")))
        or name in unknown
    }
    ambiguous_executable_aliases = {
        name
        for name in ambiguous
        if any(target in EXECUTABLE_MODULE_FUNCTIONS for target in resolved.get(name, ()))
        or _IMPLICIT_BUILTIN_OPERATIONS.get(name) in EXECUTABLE_MODULE_FUNCTIONS
    }
    return ImportBindingsV2(
        module_aliases=module_aliases,
        direct_aliases=direct_aliases,
        special_aliases=special_aliases,
        receiver_aliases=receiver_aliases,
        executable_aliases=executable_aliases,
        flag_aliases=flag_aliases,
        ambiguous_aliases=frozenset(ambiguous),
        ambiguous_writer_aliases=frozenset(ambiguous_writer_aliases),
        ambiguous_executable_aliases=frozenset(ambiguous_executable_aliases),
        rebound_module_aliases=rebound_module_aliases,
        reflection_helpers=reflection_helpers,
    )


def _target_names(node: ast.expr | None) -> set[str]:
    """Collect names bound by an assignment target, including unpacking."""

    if node is None:
        return set()
    return {child.id for child in ast.walk(node) if isinstance(child, ast.Name)}


def _argument_names(arguments: ast.arguments) -> set[str]:
    names = {
        argument.arg
        for group in (arguments.posonlyargs, arguments.args, arguments.kwonlyargs)
        for argument in group
    }
    names.update(optional.arg for optional in (arguments.vararg, arguments.kwarg) if optional is not None)
    return names


def _bound_names(tree: ast.Module) -> frozenset[str]:
    """Collect every name any lexical binder in the module may rebind.

    The scan is module-wide and deliberately coarse. Over-reporting a shadowed
    import costs an unresolved observation, while missing one lets a writer
    disappear: ``def go(os, p): os.open(p, os.O_RDONLY)`` reads as a proved
    read-only call unless the parameter counts as a binder.
    """

    names: set[str] = set()
    for node in ast.walk(tree):
        if isinstance(node, ast.Assign):
            for target in node.targets:
                names |= _target_names(target)
        elif isinstance(node, (ast.AnnAssign, ast.AugAssign)):
            names |= _target_names(node.target)
        elif isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            names.add(node.name)
            names |= _argument_names(node.args)
        elif isinstance(node, ast.Lambda):
            names |= _argument_names(node.args)
        elif isinstance(node, ast.ClassDef):
            names.add(node.name)
        elif isinstance(node, (ast.For, ast.AsyncFor)):
            names |= _target_names(node.target)
        elif isinstance(node, ast.comprehension):
            names |= _target_names(node.target)
        elif isinstance(node, ast.withitem):
            names |= _target_names(node.optional_vars)
        elif isinstance(node, ast.ExceptHandler) and node.name is not None:
            names.add(node.name)
        elif isinstance(node, ast.NamedExpr):
            names |= _target_names(node.target)
        elif isinstance(node, ast.Global | ast.Nonlocal):
            names.update(node.names)
        elif isinstance(node, ast.MatchAs | ast.MatchStar) and node.name is not None:
            # A structural-pattern capture binds its name in the enclosing scope.
            names.add(node.name)
        elif isinstance(node, ast.MatchMapping) and node.rest is not None:
            names.add(node.rest)
        elif _TYPE_ALIAS is not None and isinstance(node, _TYPE_ALIAS):
            names |= _target_names(node.name)
    names |= _conflicting_import_names(tree)
    return frozenset(names)


def _binding_counts(tree: ast.Module) -> Counter[str]:
    """Count lexical bindings so one exact alias cannot hide a later rebind."""

    counts: Counter[str] = Counter()

    def add(names: set[str]) -> None:
        counts.update(names)

    for node in ast.walk(tree):
        if isinstance(node, ast.Assign):
            for target in node.targets:
                add(_target_names(target))
        elif isinstance(node, (ast.AnnAssign, ast.AugAssign)):
            add(_target_names(node.target))
        elif isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            counts[node.name] += 1
            counts.update(_argument_names(node.args))
        elif isinstance(node, ast.Lambda):
            counts.update(_argument_names(node.args))
        elif isinstance(node, ast.ClassDef):
            counts[node.name] += 1
        elif isinstance(node, (ast.For, ast.AsyncFor)):
            add(_target_names(node.target))
        elif isinstance(node, ast.comprehension):
            add(_target_names(node.target))
        elif isinstance(node, ast.withitem):
            add(_target_names(node.optional_vars))
        elif isinstance(node, ast.ExceptHandler) and node.name is not None:
            counts[node.name] += 1
        elif isinstance(node, ast.NamedExpr):
            add(_target_names(node.target))
        elif isinstance(node, ast.Import):
            counts.update(alias.asname or alias.name.split(".", maxsplit=1)[0] for alias in node.names)
        elif isinstance(node, ast.ImportFrom):
            counts.update(
                alias.asname or alias.name for alias in node.names if alias.name != "*"
            )
        elif isinstance(node, ast.Global | ast.Nonlocal):
            counts.update(node.names)
        elif isinstance(node, ast.MatchAs | ast.MatchStar) and node.name is not None:
            counts[node.name] += 1
        elif isinstance(node, ast.MatchMapping) and node.rest is not None:
            counts[node.rest] += 1
        elif _TYPE_ALIAS is not None and isinstance(node, _TYPE_ALIAS):
            add(_target_names(node.name))
    return counts


def has_wildcard_import(tree: ast.Module) -> bool:
    """Report ``from module import *``, which may bind any tracked name."""

    return any(
        isinstance(node, ast.ImportFrom) and any(alias.name == "*" for alias in node.names)
        for node in ast.walk(tree)
    )


def _conflicting_import_names(tree: ast.Module) -> set[str]:
    """Report names bound by more than one import."""

    seen: dict[str, str] = {}
    conflicting: set[str] = set()
    for node in ast.walk(tree):
        if isinstance(node, ast.Import):
            pairs = [(alias.asname or alias.name, alias.name) for alias in node.names]
        elif isinstance(node, ast.ImportFrom):
            pairs = [(alias.asname or alias.name, f"{node.module}.{alias.name}") for alias in node.names]
        else:
            continue
        for local, origin in pairs:
            if seen.setdefault(local, origin) != origin:
                conflicting.add(local)
    return conflicting


def _flag_alias_bindings(tree: ast.Module) -> dict[str, str]:
    return {
        alias.asname or alias.name: alias.name
        for node in ast.walk(tree)
        if isinstance(node, ast.ImportFrom) and node.level == 0 and node.module == "os"
        for alias in node.names
        if alias.name in _KNOWN_OPEN_FLAGS
    }


def _alias_assignment_targets(tree: ast.Module) -> frozenset[str]:
    """Names bound by the simple alias assignments this resolver models."""

    return frozenset(name for name, _ in _alias_assignments(tree))


def _alias_assignments(tree: ast.Module) -> tuple[tuple[str, ast.expr], ...]:
    pairs: list[tuple[str, ast.expr]] = []
    for node in ast.walk(tree):
        if isinstance(node, ast.Assign):
            targets = [target for target in node.targets if isinstance(target, ast.Name)]
            value = node.value
        elif isinstance(node, ast.AnnAssign) and isinstance(node.target, ast.Name) and node.value is not None:
            targets = [node.target]
            value = node.value
        else:
            continue
        if isinstance(value, (ast.Name, ast.Attribute, ast.Subscript, ast.Call)):
            pairs.extend((target.id, value) for target in targets)
    return tuple(pairs)


def _resolve_alias_chains(
    tree: ast.Module,
    module_aliases: Mapping[str, str],
    rebound_modules: Mapping[str, frozenset[str]],
    reflection_helpers: frozenset[str],
    seeds: Mapping[str, set[tuple[str, str]]],
) -> tuple[dict[str, set[tuple[str, str]]], set[str]]:
    """Resolve ``op = os.replace; op2 = op`` chains to a fixpoint.

    A name that resolves to more than one operation is reported as ambiguous.
    A name assigned from a tracked attribute on a rebound module carries an
    unknown target through the same graph, so a wildcard import or a reassigned
    module cannot make the alias disappear.
    """

    assignments = _alias_assignments(tree)
    resolved: dict[str, set[tuple[str, str]]] = {name: set(targets) for name, targets in seeds.items()}
    unknown: set[str] = set()
    for name, value in assignments:
        if isinstance(value, ast.Name):
            continue
        resolution = _static_callable_resolution(
            value, module_aliases, rebound_modules, reflection_helpers
        )
        if resolution.target is not None:
            resolved.setdefault(name, set()).add(resolution.target)
        if resolution.unresolved:
            unknown.add(name)
    # Propagate along a dependency graph rather than a fixed number of passes.
    # A pass-bounded loop drops a reverse-ordered chain longer than the bound.
    readers: dict[str, set[str]] = {}
    for name, value in assignments:
        if isinstance(value, ast.Name):
            readers.setdefault(value.id, set()).add(name)
    # Propagation terminates because each enqueue adds at least one target to a
    # finite, monotonically growing set, so no chain length or cycle escapes it.
    worklist = deque(resolved)
    while worklist:
        source = worklist.popleft()
        for reader in readers.get(source, ()):
            current = resolved.setdefault(reader, set())
            before = len(current)
            current.update(resolved[source])
            if len(current) != before:
                worklist.append(reader)
    unknown_worklist = deque(unknown)
    while unknown_worklist:
        source = unknown_worklist.popleft()
        for reader in readers.get(source, ()):
            if reader not in unknown:
                unknown.add(reader)
                unknown_worklist.append(reader)
    return resolved, unknown


def _propagate_alias_taint(tree: ast.Module, initial: set[str]) -> set[str]:
    """Propagate ambiguous provenance through the same simple alias graph."""

    readers: dict[str, set[str]] = {}
    for name, value in _alias_assignments(tree):
        if isinstance(value, ast.Name):
            readers.setdefault(value.id, set()).add(name)
    tainted = set(initial)
    worklist = deque(tainted)
    while worklist:
        source = worklist.popleft()
        for reader in readers.get(source, ()):
            if reader not in tainted:
                tainted.add(reader)
                worklist.append(reader)
    return tainted


def _is_tracked_attribute(modules: frozenset[str], attribute: str) -> bool:
    return any(
        (module, attribute) in MODULE_OPERATIONS
        or (module, attribute) in SPECIAL_MODULE_FUNCTIONS
        or (module, attribute) in EXECUTABLE_MODULE_FUNCTIONS
        for module in modules
    )


def _special_alias_bindings(tree: ast.Module) -> dict[str, tuple[str, str]]:
    return {
        alias.asname or alias.name: (str(node.module), alias.name)
        for node in ast.walk(tree)
        if isinstance(node, ast.ImportFrom) and node.level == 0 and node.module in TRACKED_MODULES
        for alias in node.names
        if (node.module, alias.name) in SPECIAL_MODULE_FUNCTIONS
    }


def _executable_alias_bindings(tree: ast.Module) -> dict[str, tuple[str, str]]:
    return {
        alias.asname or alias.name: (str(node.module), alias.name)
        for node in ast.walk(tree)
        if isinstance(node, ast.ImportFrom)
        and node.level == 0
        and node.module in TRACKED_MODULES
        for alias in node.names
        if (node.module, alias.name) in EXECUTABLE_MODULE_FUNCTIONS
    }


def _module_alias_bindings(tree: ast.Module) -> dict[str, str]:
    bindings: dict[str, str] = {}
    for node in ast.walk(tree):
        if not isinstance(node, ast.Import):
            continue
        for alias in node.names:
            if alias.name in TRACKED_MODULES:
                bindings[alias.asname or alias.name] = alias.name
            elif alias.name.startswith("os.") and alias.asname is None:
                # ``import os.path`` binds the top-level name ``os``. Losing
                # that CPython import rule makes a later ``os.replace`` vanish.
                bindings["os"] = "os"
    return bindings


def _module_alias_candidates(tree: ast.Module) -> dict[str, frozenset[str]]:
    """Every tracked module a local name may have been bound to.

    Conflicting imports leave the origin ambiguous, so a rebound name must be
    checked against all of its candidates rather than the last one seen.
    """

    candidates: dict[str, set[str]] = {}
    for node in ast.walk(tree):
        if not isinstance(node, ast.Import):
            continue
        for alias in node.names:
            if alias.name in TRACKED_MODULES:
                candidates.setdefault(alias.asname or alias.name, set()).add(alias.name)
            elif alias.name.startswith("os.") and alias.asname is None:
                candidates.setdefault("os", set()).add("os")
    return {name: frozenset(modules) for name, modules in candidates.items()}


def _direct_alias_bindings(tree: ast.Module) -> dict[str, tuple[str, str]]:
    return {
        alias.asname or alias.name: (str(node.module), alias.name)
        for node in ast.walk(tree)
        if isinstance(node, ast.ImportFrom) and node.level == 0 and node.module in TRACKED_MODULES
        for alias in node.names
        if (node.module, alias.name) in MODULE_OPERATIONS
    }


def _split_sql_script(statement: str) -> tuple[tuple[str, ...], bool]:
    """Split SQL with a bounded lexical machine; ``False`` means unknown syntax.

    This is intentionally a lexer rather than a SQL parser. It recognizes
    statement boundaries while preserving semicolons inside quoted strings and
    comments. Unterminated lexical states and resource overflow fail closed.
    """

    if len(statement) > MAX_SQL_SCRIPT_CHARACTERS:
        return (), False
    parts: list[str] = []
    current: list[str] = []
    state = "NORMAL"
    index = 0
    while index < len(statement):
        character = statement[index]
        following = statement[index + 1] if index + 1 < len(statement) else ""
        if state == "NORMAL":
            if character == "-" and following == "-":
                current.append(" ")
                state = "LINE_COMMENT"
                index += 2
                continue
            if character == "/" and following == "*":
                current.append(" ")
                state = "BLOCK_COMMENT"
                index += 2
                continue
            if character in {"'", '"', "`"}:
                current.append(character)
                state = {"'": "SINGLE", '"': "DOUBLE", "`": "BACKTICK"}[character]
            elif character == "[":
                current.append(character)
                state = "BRACKET"
            elif character == ";":
                parts.append("".join(current))
                if len(parts) > MAX_SQL_STATEMENTS:
                    return (), False
                current = []
            else:
                current.append(character)
        elif state == "LINE_COMMENT":
            if character in {"\n", "\r"}:
                current.append(character)
                state = "NORMAL"
        elif state == "BLOCK_COMMENT":
            if character == "*" and following == "/":
                current.append(" ")
                state = "NORMAL"
                index += 2
                continue
        elif state in {"SINGLE", "DOUBLE", "BACKTICK"}:
            delimiter = {"SINGLE": "'", "DOUBLE": '"', "BACKTICK": "`"}[state]
            current.append(character)
            if character == delimiter:
                if following == delimiter:
                    current.append(following)
                    index += 2
                    continue
                state = "NORMAL"
        elif state == "BRACKET":
            current.append(character)
            if character == "]":
                state = "NORMAL"
        index += 1
    if state == "LINE_COMMENT":
        state = "NORMAL"
    if state != "NORMAL":
        return (), False
    parts.append("".join(current))
    if len(parts) > MAX_SQL_STATEMENTS:
        return (), False
    return tuple(parts), True


def classify_sql_script(statement: str | None) -> str | None:
    """Classify a multi-statement script by its strongest statement.

    ``executescript`` runs every statement, so a benign leading ``SELECT``
    cannot make a trailing ``DROP TABLE`` invisible.
    """

    if statement is None:
        return "SQL_DYNAMIC"
    parts, complete = _split_sql_script(statement)
    if not complete:
        return "SQL_DYNAMIC"
    kinds = [_classify_sql_fragment(part) for part in parts]
    return _strongest_sql_kind(kinds)


def _strongest_sql_kind(kinds: Sequence[str | None]) -> str | None:
    """Join statement effects under the scanner's fail-closed ordering."""

    if "SQL_DYNAMIC" in kinds:
        return "SQL_DYNAMIC"
    if "SQL_WRITE" in kinds:
        return "SQL_WRITE"
    if "SQL_PRAGMA_WRITE" in kinds:
        return "SQL_PRAGMA_WRITE"
    return None


def classify_sql_statement(statement: str | None) -> str | None:
    """Classify SQL passed to one execute call under the bounded lexer."""

    if statement is None:
        # A statement built at runtime cannot be shown to leave value state intact.
        return "SQL_DYNAMIC"
    parts, complete = _split_sql_script(statement)
    if not complete:
        return "SQL_DYNAMIC"
    return _strongest_sql_kind([_classify_sql_fragment(part) for part in parts])


def _classify_sql_fragment(statement: str) -> str | None:
    """Classify one comment-free fragment produced by the bounded lexer."""

    stripped = _strip_leading_sql_comments(statement)
    if stripped is None:
        return "SQL_DYNAMIC"
    statement = stripped
    if (
        _SQL_PRAGMA_WRITE_RE.match(statement) is not None
        or _SQL_PRAGMA_CALL_WRITE_RE.match(statement) is not None
    ):
        return "SQL_PRAGMA_WRITE"
    if _SQL_WRITE_RE.match(statement) is not None:
        return "SQL_WRITE"
    if _SQL_CTE_RE.match(statement) is not None:
        return "SQL_WRITE"
    if not statement.strip():
        return None
    if _SQL_PROVED_READ_RE.match(statement) is not None:
        return None
    bare_pragma = _SQL_BARE_PRAGMA_RE.match(statement)
    if bare_pragma is not None:
        name = bare_pragma.group("name").lower()
        if name in _SQL_BARE_PRAGMA_WRITES:
            return "SQL_PRAGMA_WRITE"
        if name in _SQL_BARE_PRAGMA_READ_ONLY:
            return None
        return "SQL_DYNAMIC"
    # This bounded lexer cannot prove arbitrary SQL read-only. Unknown syntax is
    # observable rather than silently treated as harmless.
    return "SQL_DYNAMIC"


def literal_string_argument(call: ast.Call, index: int = 0) -> str | None:
    if len(call.args) <= index:
        return None
    value = call.args[index]
    return value.value if isinstance(value, ast.Constant) and isinstance(value.value, str) else None


def _closed_call_argument(
    call: ast.Call, index: int, keyword: str
) -> tuple[bool, ast.expr | None]:
    """Return ``(closed, value)`` for one positional-or-keyword argument."""

    if any(isinstance(argument, ast.Starred) for argument in call.args):
        return False, None
    matches = [item.value for item in call.keywords if item.arg == keyword]
    if any(item.arg is None for item in call.keywords) or len(matches) > 1:
        return False, None
    positional = call.args[index] if len(call.args) > index else None
    if positional is not None and matches:
        return False, None
    return True, positional if positional is not None else (matches[0] if matches else None)


def classify_sqlite_connect(call: ast.Call) -> str | None:
    """Classify SQLite connection creation and write capability from closed literals."""

    if len(call.args) > 8:
        return "DATABASE_OPEN_UNKNOWN"
    database_closed, database_node = _closed_call_argument(call, 0, "database")
    uri_closed, uri_node = _closed_call_argument(call, 7, "uri")
    if not database_closed or not uri_closed or database_node is None:
        return "DATABASE_OPEN_UNKNOWN"
    database = _constant_string(database_node)
    if database is None:
        return "DATABASE_OPEN_UNKNOWN"
    if uri_node is None:
        uri = False
    elif isinstance(uri_node, ast.Constant) and type(uri_node.value) is bool:
        uri = uri_node.value
    else:
        return "DATABASE_OPEN_UNKNOWN"
    if database == ":memory:":
        return None
    if database == "":
        return "DATABASE_OPEN_EPHEMERAL"
    if not uri or not database.startswith("file:"):
        return "DATABASE_OPEN_WRITE"
    try:
        query = urllib.parse.urlsplit(database).query
        pairs = urllib.parse.parse_qsl(
            query, keep_blank_values=True, strict_parsing=False
        )
    except ValueError:
        return "DATABASE_OPEN_UNKNOWN"
    parameters: dict[str, list[str]] = {}
    for key, value in pairs:
        # SQLite URI parameter names and values are case-sensitive. Folding
        # either one can turn an ignored option (for example ``MODE=RO``) into
        # a fictitious read-only guarantee while SQLite opens the default
        # write-capable database instead.
        parameters.setdefault(key, []).append(value)
    if any(len(values) != 1 for values in parameters.values()):
        return "DATABASE_OPEN_UNKNOWN"
    mode = parameters.get("mode", [""])[0]
    immutable = parameters.get("immutable", [""])[0]
    if mode == "memory" or database.startswith("file::memory:"):
        return None
    if mode == "ro" or immutable == "1":
        return None
    if mode not in {"", "rw", "rwc"} or immutable not in {"", "0", "1"}:
        return "DATABASE_OPEN_UNKNOWN"
    return "DATABASE_OPEN_WRITE"


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


def _closed_flag_set(expression: ast.expr, bindings: ImportBindingsV2) -> frozenset[str] | None:
    """Parse a closed ``os.open`` flag expression with proved provenance.

    The grammar admits bitwise-OR combinations of ``O_`` flags whose origin is
    proved (an attribute on a bound ``os`` alias, or an exact imported flag
    name) plus the literal ``0``.  A call, an unproved name, an attribute on
    some other object such as ``fake.O_RDONLY``, another operator, or a nonzero
    literal leaves the grammar and reads as unresolved.
    """

    if isinstance(expression, ast.BinOp) and isinstance(expression.op, ast.BitOr):
        left = _closed_flag_set(expression.left, bindings)
        right = _closed_flag_set(expression.right, bindings)
        return None if left is None or right is None else left | right
    if isinstance(expression, ast.Constant):
        return frozenset() if type(expression.value) is int and expression.value == 0 else None
    if isinstance(expression, ast.Attribute):
        base = expression.value
        proved = isinstance(base, ast.Name) and bindings.module_aliases.get(base.id) == "os"
        if proved and expression.attr in _KNOWN_OPEN_FLAGS:
            return frozenset({expression.attr})
        return None
    if isinstance(expression, ast.Name):
        canonical = bindings.flag_aliases.get(expression.id)
        return frozenset({canonical}) if canonical is not None else None
    return None


def classify_descriptor_open(
    call: ast.Call, bindings: ImportBindingsV2, *, flag_index: int = 1
) -> str | None:
    """Classify ``os.open`` by its integer flag expression.

    An unresolved flag expression may request write access, so it reports an
    unknown descriptor open rather than disappearing.
    """

    if len(call.args) <= flag_index:
        return "DESCRIPTOR_OPEN_UNKNOWN"
    names = _closed_flag_set(call.args[flag_index], bindings)
    if names is None:
        # A flag expression this grammar cannot close may request write access.
        return "DESCRIPTOR_OPEN_UNKNOWN"
    if names & _WRITABLE_OPEN_FLAGS:
        return "DESCRIPTOR_OPEN_WRITE"
    return None


def classify_open_call(call: ast.Call, *, mode_index: int) -> str | None:
    """Classify an ``open`` call, keeping an unresolved mode observable."""

    mode = open_mode(call, mode_index=mode_index)
    if not mode.present:
        return None
    if mode.literal is None:
        return "OPEN_MODE_UNKNOWN"
    if mode.literal in _READ_ONLY_OPEN_MODES:
        return None
    if not mode.literal or not set(mode.literal).issubset(_OPEN_MODE_CHARACTERS):
        return "OPEN_MODE_UNKNOWN"
    if _MUTATING_OPEN_MODE_RE.search(mode.literal) is not None:
        return "OPEN_WRITE"
    # A literal composed of known characters may still be an invalid or
    # version-dependent spelling (for example ``rr``). It cannot inherit the
    # proved read-only status of the exact allowlist.
    return "OPEN_MODE_UNKNOWN"


def classify_named_temporary_file(call: ast.Call) -> str:
    """Classify the deletion policy of ``NamedTemporaryFile`` exactly.

    The documented default is cleanup-enabled. A literal ``delete=False`` is a
    persistent creation. Dynamic or unpacked policy remains blocking because it
    may select the persistent branch at runtime.
    """

    if any(isinstance(argument, ast.Starred) for argument in call.args):
        return "TEMPFILE_CREATE_UNKNOWN"
    if len(call.args) > 7:
        return "TEMPFILE_CREATE_UNKNOWN"
    delete_value: ast.expr | None = None
    for keyword in call.keywords:
        if keyword.arg is None:
            return "TEMPFILE_CREATE_UNKNOWN"
        if keyword.arg == "delete":
            if delete_value is not None:
                return "TEMPFILE_CREATE_UNKNOWN"
            delete_value = keyword.value
    if delete_value is None:
        return "TEMPFILE_CREATE_EPHEMERAL"
    if isinstance(delete_value, ast.Constant) and type(delete_value.value) is bool:
        return (
            "TEMPFILE_CREATE_EPHEMERAL"
            if delete_value.value
            else "TEMPFILE_CREATE"
        )
    return "TEMPFILE_CREATE_UNKNOWN"


def classify_temporary_directory(call: ast.Call) -> str:
    """Classify ``TemporaryDirectory`` by its keyword-only cleanup policy."""

    if any(isinstance(argument, ast.Starred) for argument in call.args):
        return "TEMPDIR_CREATE_UNKNOWN"
    if len(call.args) > 4:
        return "TEMPDIR_CREATE_UNKNOWN"
    delete_value: ast.expr | None = None
    for keyword in call.keywords:
        if keyword.arg is None:
            return "TEMPDIR_CREATE_UNKNOWN"
        if keyword.arg == "delete":
            if delete_value is not None:
                return "TEMPDIR_CREATE_UNKNOWN"
            delete_value = keyword.value
    if delete_value is None:
        return "TEMPDIR_CREATE_EPHEMERAL"
    if isinstance(delete_value, ast.Constant) and type(delete_value.value) is bool:
        return "TEMPDIR_CREATE_EPHEMERAL" if delete_value.value else "TEMPDIR_CREATE"
    return "TEMPDIR_CREATE_UNKNOWN"


def is_unary_call(call: ast.Call) -> bool:
    """Separate ``Path.replace(target)`` from ``str.replace(old, new)`` by arity."""

    return (
        len(call.args) == 1
        and not call.keywords
        and not isinstance(call.args[0], ast.Starred)
    )


@dataclass(frozen=True, slots=True)
class DestinationV2:
    """Where one operation writes, and whether the caller decides it."""

    descriptor: str
    parameter: str | None
    resolved: bool

    @property
    def caller_determined(self) -> bool:
        return self.parameter is not None


_PATHLIB_CONSTRUCTORS = frozenset({"Path", "PurePath", "PurePosixPath"})


@dataclass(frozen=True, slots=True)
class _LiteralAliasV2:
    literal: str
    pathlib_object: bool


class _SameScopeBindingCollector(ast.NodeVisitor):
    """Collect bindings without entering a nested lexical scope."""

    def __init__(self) -> None:
        self.bindings: dict[str, int] = {}

    def _bind(self, name: str) -> None:
        self.bindings[name] = self.bindings.get(name, 0) + 1

    def visit_Name(self, node: ast.Name) -> None:
        if isinstance(node.ctx, (ast.Store, ast.Del)):
            self._bind(node.id)

    def visit_FunctionDef(self, node: ast.FunctionDef) -> None:
        self._bind(node.name)

    def visit_AsyncFunctionDef(self, node: ast.AsyncFunctionDef) -> None:
        self._bind(node.name)

    def visit_ClassDef(self, node: ast.ClassDef) -> None:
        self._bind(node.name)

    def visit_Lambda(self, node: ast.Lambda) -> None:
        return

    def visit_Import(self, node: ast.Import) -> None:
        for alias in node.names:
            self._bind(alias.asname or alias.name.split(".", maxsplit=1)[0])

    def visit_ImportFrom(self, node: ast.ImportFrom) -> None:
        for alias in node.names:
            self._bind(alias.asname or alias.name)

    def visit_Global(self, node: ast.Global) -> None:
        for name in node.names:
            self._bind(name)

    def visit_Nonlocal(self, node: ast.Nonlocal) -> None:
        for name in node.names:
            self._bind(name)

    def visit_ExceptHandler(self, node: ast.ExceptHandler) -> None:
        if node.name is not None:
            self._bind(node.name)
        self.generic_visit(node)

    def visit_MatchAs(self, node: ast.MatchAs) -> None:
        if node.name is not None:
            self._bind(node.name)
        self.generic_visit(node)

    def visit_MatchStar(self, node: ast.MatchStar) -> None:
        if node.name is not None:
            self._bind(node.name)

    def visit_MatchMapping(self, node: ast.MatchMapping) -> None:
        if node.rest is not None:
            self._bind(node.rest)
        self.generic_visit(node)


_LEXICAL_SCOPES = (ast.Module, ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef, ast.Lambda)


class LiteralPathResolverV2:
    """Resolve only definite, prior, single-assignment aliases at one use site.

    The accepted shape is deliberately small: one direct assignment in the
    nearest statement scope, before the statement containing the use, with no
    other binding of that name in the scope.  Nested scopes, branch-local
    assignments, read-before-assignment, parameter shadowing, and rebindings
    therefore remain unresolved.
    """

    def __init__(self, tree: ast.Module) -> None:
        self._tree = tree
        self._parents = {
            child: parent for parent in ast.walk(tree) for child in ast.iter_child_nodes(parent)
        }
        self._cache: dict[ast.AST, Mapping[str, _LiteralAliasV2]] = {}
        self._scope_bindings_cache: dict[ast.AST, Mapping[str, int]] = {}

    def literal_at(self, expression: ast.expr, use: ast.AST) -> str | None:
        """Resolve a path operand; raw strings are valid for os-style APIs."""

        if isinstance(expression, ast.Constant) and isinstance(expression.value, str):
            return expression.value
        if isinstance(expression, ast.Name):
            alias = self._aliases_at(use).get(expression.id)
            return alias.literal if alias is not None else None
        return self._proven_pathlib_constructor_literal(expression, use)

    def pathlib_receiver_literal_at(self, expression: ast.expr, use: ast.AST) -> str | None:
        """Resolve only a receiver proved to be a constructed pathlib object."""

        if isinstance(expression, ast.Name):
            alias = self._aliases_at(use).get(expression.id)
            return alias.literal if alias is not None and alias.pathlib_object else None
        return self._proven_pathlib_constructor_literal(expression, use)

    def _aliases_at(self, use: ast.AST) -> Mapping[str, _LiteralAliasV2]:
        cached = self._cache.get(use)
        if cached is not None:
            return cached
        result = self._aliases_at_uncached(use)
        self._cache[use] = result
        return result

    def _aliases_at_uncached(self, use: ast.AST) -> Mapping[str, _LiteralAliasV2]:
        scope = self._nearest_scope(use)
        if not isinstance(scope, (ast.Module, ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
            return MappingProxyType({})
        body = scope.body
        statement = self._containing_statement(use, scope)
        if statement is None or statement not in body:
            return MappingProxyType({})
        use_index = body.index(statement)
        bindings = self._scope_bindings(scope)
        aliases: dict[str, _LiteralAliasV2] = {}
        for item in body[:use_index]:
            candidate = self._direct_literal_assignment(item)
            if candidate is None:
                continue
            name, alias = candidate
            if bindings.get(name) == 1:
                aliases[name] = alias
        return MappingProxyType(aliases)

    def _scope_bindings(self, scope: ast.AST) -> Mapping[str, int]:
        cached = self._scope_bindings_cache.get(scope)
        if cached is not None:
            return cached
        collector = _SameScopeBindingCollector()
        if isinstance(scope, (ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda)):
            for name in _argument_names(scope.args):
                collector._bind(name)
        if isinstance(scope, ast.Lambda):
            collector.visit(scope.body)
        elif isinstance(scope, (ast.Module, ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
            for item in scope.body:
                collector.visit(item)
        result = MappingProxyType(dict(collector.bindings))
        self._scope_bindings_cache[scope] = result
        return result

    def _nearest_scope(self, use: ast.AST) -> ast.AST | None:
        current = use
        while current is not self._tree:
            parent = self._parents.get(current)
            if parent is None:
                return None
            if isinstance(parent, _LEXICAL_SCOPES):
                return parent
            current = parent
        return self._tree

    def _containing_statement(self, use: ast.AST, scope: ast.AST) -> ast.stmt | None:
        current = use
        while self._parents.get(current) is not scope:
            parent = self._parents.get(current)
            if parent is None:
                return None
            current = parent
        return current if isinstance(current, ast.stmt) else None

    def _direct_literal_assignment(
        self, statement: ast.stmt
    ) -> tuple[str, _LiteralAliasV2] | None:
        if (
            isinstance(statement, ast.Assign)
            and len(statement.targets) == 1
            and isinstance(statement.targets[0], ast.Name)
        ):
            name = statement.targets[0].id
            value = statement.value
        elif (
            isinstance(statement, ast.AnnAssign)
            and isinstance(statement.target, ast.Name)
            and statement.value is not None
        ):
            name = statement.target.id
            value = statement.value
        else:
            return None
        if isinstance(value, ast.Constant) and isinstance(value.value, str):
            return name, _LiteralAliasV2(value.value, False)
        literal = self._proven_pathlib_constructor_literal(value, statement)
        return (name, _LiteralAliasV2(literal, True)) if literal is not None else None

    def _proven_pathlib_constructor_literal(
        self, expression: ast.expr, use: ast.AST
    ) -> str | None:
        if (
            not isinstance(expression, ast.Call)
            or len(expression.args) != 1
            or expression.keywords
            or not isinstance(expression.args[0], ast.Constant)
            or not isinstance(expression.args[0].value, str)
        ):
            return None
        constructors, modules = self._pathlib_bindings_at(use)
        function = expression.func
        if isinstance(function, ast.Name) and function.id in constructors:
            return expression.args[0].value
        if (
            isinstance(function, ast.Attribute)
            and function.attr in _PATHLIB_CONSTRUCTORS
            and isinstance(function.value, ast.Name)
            and function.value.id in modules
        ):
            return expression.args[0].value
        return None

    def _pathlib_bindings_at(self, use: ast.AST) -> tuple[frozenset[str], frozenset[str]]:
        boundary = self._containing_statement(use, self._tree)
        if boundary is None or boundary not in self._tree.body:
            return frozenset(), frozenset()
        boundary_index = self._tree.body.index(boundary)
        module_bindings = self._scope_bindings(self._tree)
        constructors: set[str] = set()
        modules: set[str] = set()
        for statement in self._tree.body[:boundary_index]:
            if isinstance(statement, ast.Import):
                for alias in statement.names:
                    local = alias.asname or alias.name.split(".", maxsplit=1)[0]
                    if alias.name == "pathlib" and module_bindings.get(local) == 1:
                        modules.add(local)
            elif (
                isinstance(statement, ast.ImportFrom)
                and statement.level == 0
                and statement.module == "pathlib"
            ):
                for alias in statement.names:
                    local = alias.asname or alias.name
                    if alias.name in _PATHLIB_CONSTRUCTORS and module_bindings.get(local) == 1:
                        constructors.add(local)
        for scope in self._inner_scopes(use):
            bindings = self._scope_bindings(scope)
            constructors.difference_update(name for name in constructors if bindings.get(name, 0))
            modules.difference_update(name for name in modules if bindings.get(name, 0))
        return frozenset(constructors), frozenset(modules)

    def _inner_scopes(self, use: ast.AST) -> tuple[ast.AST, ...]:
        scopes: list[ast.AST] = []
        current = use
        while current is not self._tree:
            parent = self._parents.get(current)
            if parent is None:
                break
            if isinstance(parent, _LEXICAL_SCOPES) and parent is not self._tree:
                scopes.append(parent)
            current = parent
        return tuple(scopes)


_PATH_RECEIVER_WRITER_ATTRIBUTES = frozenset(RECEIVER_OPERATIONS) | frozenset(
    {"hardlink_to", "rename", "replace", "symlink_to"}
)


def unresolved_receiver_writer_provenance(tree: ast.Module) -> bool:
    """Detect a proved pathlib writer method that escapes direct-call analysis."""

    resolver = LiteralPathResolverV2(tree)
    parents = {
        id(child): parent
        for parent in ast.walk(tree)
        for child in ast.iter_child_nodes(parent)
    }
    for node in ast.walk(tree):
        if not isinstance(node, ast.Attribute) or node.attr not in _PATH_RECEIVER_WRITER_ATTRIBUTES:
            continue
        if resolver.pathlib_receiver_literal_at(node.value, node) is None:
            continue
        parent = parents.get(id(node))
        if isinstance(parent, ast.Call) and parent.func is node:
            continue
        return True
    return False


def _describe_operand(
    expression: ast.expr | None,
    parameters: frozenset[str],
    resolver: LiteralPathResolverV2 | None,
    use: ast.AST | None,
) -> tuple[str, str | None, bool]:
    if expression is None:
        return "NONE", None, False
    literal = (
        resolver.literal_at(expression, use)
        if resolver is not None and use is not None
        else expression.value
        if isinstance(expression, ast.Constant) and isinstance(expression.value, str)
        else None
    )
    if literal is not None:
        return f"LITERAL:{literal}", None, True
    referenced = {node.id for node in ast.walk(expression) if isinstance(node, ast.Name)}
    bound = sorted(referenced & parameters)
    if bound:
        return f"PARAMETER:{','.join(bound)}", bound[0], False
    rendered = ast.dump(expression, annotate_fields=True, include_attributes=False)
    return f"EXPR:{hashlib.sha256(rendered.encode('utf-8')).hexdigest()[:16]}", None, False


def describe_destination(
    expressions: Sequence[ast.expr | None],
    parameters: frozenset[str],
    resolver: LiteralPathResolverV2 | None = None,
    use: ast.AST | None = None,
) -> DestinationV2:
    """Describe every economically relevant operand of one operation.

    An operand that traces to a parameter of the enclosing function is chosen by
    the caller, so the same helper body can write an evidence file or a balance
    file.  That case is reported rather than treated as a fixed destination.
    """

    if not expressions:
        return DestinationV2("NONE", None, False)
    descriptors: list[str] = []
    parameter: str | None = None
    resolved = True
    for expression in expressions:
        descriptor, bound, operand_resolved = _describe_operand(
            expression, parameters, resolver, use
        )
        descriptors.append(descriptor)
        parameter = parameter or bound
        resolved = resolved and operand_resolved
    return DestinationV2("+".join(descriptors), parameter, resolved)


def operation_fingerprint(kind: str, node: ast.AST, provenance: str = "NONE") -> str:
    """Derive a source-shape fingerprint for one observed operation.

    The dump keeps argument expressions and drops source positions, so moving an
    operation from an evidence destination to a value-state destination changes
    the fingerprint while reformatting does not.  ``provenance`` binds the
    destination and, for a caller-determined helper, the caller-supplied
    literals, so a shared helper cannot keep one judgement across callers that
    write different artifacts.
    """

    rendered = ast.dump(node, annotate_fields=True, include_attributes=False)
    payload = (
        b"zenodex-m6-operation-v2\0"
        + kind.encode("ascii")
        + b"\0"
        + provenance.encode("utf-8")
        + b"\0"
        + rendered.encode("utf-8")
    )
    return hashlib.sha256(payload).hexdigest()


def combine_fingerprints(fingerprints: tuple[str, ...]) -> str:
    """Bind every occurrence of one identity into a single canonical digest."""

    payload = b"zenodex-m6-identity-v2\0" + b"\0".join(
        value.encode("ascii") for value in sorted(fingerprints)
    )
    return hashlib.sha256(payload).hexdigest()
