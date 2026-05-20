from __future__ import annotations

import sqlite3
from pathlib import Path

_U32_MAX = 0xFFFFFFFF


def _require_u32(name: str, value: object) -> int:
    if not isinstance(value, int) or isinstance(value, bool):
        raise TypeError(f"{name} must be an int")
    out = int(value)
    if out < 0 or out > _U32_MAX:
        raise ValueError(f"{name} out of u32 range: {out}")
    return out


def build_tau_testnet_wallet_outbound_o5_rule(
    *,
    scoped_sender_id: int,
    max_outbound_amount: int,
) -> str:
    sender_id = _require_u32("scoped_sender_id", scoped_sender_id)
    max_amount = _require_u32("max_outbound_amount", max_outbound_amount)
    return (
        "always "
        "("
        f"(o5[t] = {{ 1 }}:bv <-> ((!(i3[t]:bv = {{ {sender_id} }}:bv)) || (i1[t]:bv <= {{ {max_amount} }}:bv)))"
        ")."
    )


def get_or_create_tau_string_numeric_id(*, db_path: str | Path, text: str) -> int:
    path = Path(db_path)
    if not isinstance(text, str) or not text.strip():
        raise ValueError("text must be a non-empty string")
    path.parent.mkdir(parents=True, exist_ok=True)
    with sqlite3.connect(path) as conn:
        conn.execute(
            """
            CREATE TABLE IF NOT EXISTS tau_strings (
                id   INTEGER PRIMARY KEY AUTOINCREMENT,
                text TEXT    NOT NULL UNIQUE
            )
            """
        )
        cur = conn.execute("SELECT id FROM tau_strings WHERE text = ?", (text,))
        row = cur.fetchone()
        if row is not None:
            return int(row[0])
        cur = conn.execute("INSERT INTO tau_strings(text) VALUES (?)", (text,))
        conn.commit()
        lastrowid = cur.lastrowid
        if lastrowid is None:
            raise RuntimeError("sqlite did not return a row id for tau_strings insert")
        return int(lastrowid)
