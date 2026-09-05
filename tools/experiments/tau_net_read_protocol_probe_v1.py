"""Replay hash-pinned upstream read handlers with offline fixture containers.

Run as a module with --upstream pointing to an existing Tau Testnet Git repository.
This executes only the five reviewed source files after checking their bytes.
It never starts a node, contacts a peer, changes a checkout, or grants authority.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
import sys
from pathlib import Path
from types import ModuleType, SimpleNamespace
from unittest.mock import patch

from src.core import tau_net_observation_v1 as core

UPSTREAM_COMMIT = "0b038824c8583a1a902ef54369d3d0ecf3384cf5"
SOURCE_SHA256 = {
    "api_response.py": "1dad7240f3116e6d309856753ff8e4bcce327772c87206d8e2b0c48bc5912b4a",
    "commands/gettaustate.py": "cf775185efacff647925ba54570aaa5af8dfc333ad0cda9763a806f7016ed7e3",
    "commands/getaccountstate.py": "288e5019f27f31abc37191ed18ce01c4d0cc54693ac0db4abd33445eb7b9ab60",
    "commands/gettxstatus.py": "f293977bc334540228cf7f27f9af49902a96436beee58e97661086ba501ae844",
    "commands/getblocks.py": "012e273c704e79c8e309759550ac0f692cbf46c6fbcc3171ab2313c4c29502d1",
}
TX = "a" * 64
BLOCK = "b" * 64


def require(condition: bool, label: str) -> None:
    if not condition:
        raise RuntimeError(label)


def pinned_sources(upstream: Path) -> dict[str, bytes]:
    sources = {}
    for name, expected in SOURCE_SHA256.items():
        result = subprocess.run(
            ["git", "-C", str(upstream), "show", f"{UPSTREAM_COMMIT}:{name}"],
            check=True,
            capture_output=True,
            timeout=15,
        )
        require(hashlib.sha256(result.stdout).hexdigest() == expected, f"SOURCE_DRIFT:{name}")
        sources[name] = result.stdout
    return sources


def load_handlers(sources: dict[str, bytes]) -> dict[str, ModuleType]:
    api = ModuleType("api_response")
    exec(compile(sources["api_response.py"], "api_response.py", "exec"), api.__dict__)
    handlers = {}
    with patch.dict(sys.modules, {"api_response": api}):
        for name in ("gettaustate", "getaccountstate", "gettxstatus", "getblocks"):
            filename = f"commands/{name}.py"
            module = ModuleType(name)
            exec(compile(sources[filename], filename, "exec"), module.__dict__)
            handlers[name] = module
    handlers["gettxstatus"].__dict__["time"] = SimpleNamespace(time=lambda: 10)
    return handlers


def observed(
    handlers: dict[str, ModuleType],
    request: core.TauReadRequestV1,
    container: object,
) -> core.TauObservationBodyV1:
    encoded = core.encode_tau_read_request_v1(request)
    if not isinstance(encoded, bytes):
        raise RuntimeError("INVALID_PROBE_REQUEST")
    raw = handlers[request.command.value].execute(encoded.decode("ascii"), container)
    require(type(raw) is str, "UPSTREAM_RESPONSE_TYPE")
    decoded = core.decode_tau_read_response_v1(request, raw.encode("utf-8"))
    if not isinstance(decoded, core.TauReadObservationV1):
        raise RuntimeError(f"UPSTREAM_RESPONSE_REJECTED:{decoded.code.value}")
    return decoded.body


def check_rules_and_accounts(handlers: dict[str, ModuleType]) -> list[str]:
    checks = []
    rules = core.TauReadRequestV1(core.TauReadCommandV1.GET_TAU_STATE)
    for state in (None, "o1[t] = i1[t]."):
        container = SimpleNamespace(
            chain_state=SimpleNamespace(get_rules_state=lambda value=state: value)
        )
        require(
            observed(handlers, rules, container) == core.TauRulesObservationV1(state or ""), "RULES"
        )
        checks.append("rules_empty" if state is None else "rules_text")
    pending = [
        {"tx_hash": "1" * 64, "sender_pubkey": "alice", "amount_out": 20, "estimated_fee": 2},
        {"tx_hash": "2" * 64, "sender_pubkey": "bob", "amount_in": 90, "estimated_fee": 99},
        {
            "tx_hash": "3" * 64,
            "sender_pubkey": "alice",
            "amount_out": 30,
            "amount_in": 7,
            "estimated_fee": 3,
        },
    ]
    account = core.TauReadRequestV1(core.TauReadCommandV1.GET_ACCOUNT_STATE, "alice")
    for balance, expected in ((100, 45), (54, 0)):
        container = SimpleNamespace(
            chain_state=SimpleNamespace(get_balance=lambda _address, value=balance: value),
            db=SimpleNamespace(get_mempool_txs_for_address=lambda _address: pending),
        )
        body = observed(handlers, account, container)
        if not isinstance(body, core.TauAccountObservationV1):
            raise RuntimeError("ACCOUNT_TYPE")
        require(
            (
                body.pending_outgoing_atoms,
                body.pending_incoming_atoms,
                body.pending_fees_atoms,
                body.available_balance_atoms,
            )
            == (50, 97, 5, expected),
            "ACCOUNT_AGGREGATES",
        )
        require(body.pending_txs[2].amount_atoms == 30, "SELF_INFLOW_IS_OMITTED")
        checks.append("account_available" if balance == 100 else "account_overreserved")
    return checks


def check_status_history(handlers: dict[str, ModuleType]) -> list[str]:
    request = core.TauReadRequestV1(core.TauReadCommandV1.GET_TX_STATUS, TX.upper())
    db = SimpleNamespace(
        get_mempool_entry=lambda _tx: None,
        get_tx_block_locations=lambda _tx: [],
        get_dropped_tx=lambda _tx: None,
    )
    container = SimpleNamespace(db=db)
    require(observed(handlers, request, container) == core.TauTxUnknownObservationV1(TX), "UNKNOWN")
    checks = ["unknown_is_success"]
    for expiration, status in (
        (11, core.TauMempoolStatusV1.QUEUED),
        (9, core.TauMempoolStatusV1.EXPIRED),
    ):
        entry = {
            "payload": json.dumps({"expiration_time": expiration}),
            "received_at": 0,
            "fee_limit": 9,
            "estimated_fee": 2,
        }
        db.get_mempool_entry = lambda _tx, value=entry: value
        body = observed(handlers, request, container)
        require(
            isinstance(body, core.TauTxMempoolObservationV1) and body.status is status,
            "MEMPOOL_STATUS",
        )
        checks.append(f"mempool_{status.value}")
    db.get_mempool_entry = lambda _tx: None
    db.get_tx_block_locations = lambda _tx: [{"block_hash": BLOCK, "block_number": 7}]
    db.get_canonical_confirmation = lambda _block, _height: (True, 10)
    require(
        observed(handlers, request, container) == core.TauTxConfirmedObservationV1(TX, BLOCK, 7, 4),
        "CONFIRMED",
    )
    checks.append("reported_canonical_inclusion")
    db.get_mempool_entry = lambda _tx: {"payload": "{}"}
    require(
        isinstance(observed(handlers, request, container), core.TauTxMempoolObservationV1),
        "MEMPOOL_PRECEDENCE",
    )
    checks.append("mempool_precedes_inclusion")
    db.get_mempool_entry = lambda _tx: None
    db.get_canonical_confirmation = lambda _block, _height: (False, 10)
    require(
        observed(handlers, request, container) == core.TauTxUnknownObservationV1(TX),
        "FORK_ONLY_UNKNOWN",
    )
    checks.append("fork_only_is_unknown")
    for dropped_status in core.TauDroppedStatusV1:
        db.get_dropped_tx = lambda _tx, value=dropped_status.value: {
            "reason": value,
            "dropped_at": 0,
        }
        body = observed(handlers, request, container)
        require(
            isinstance(body, core.TauTxDroppedObservationV1) and body.status is dropped_status,
            "DROPPED_STATUS",
        )
        checks.append(f"dropped_{dropped_status.value}")
    return checks


def check_getblocks_limit_is_ignored(handlers: dict[str, ModuleType]) -> str:
    blocks = [{"fixture": index} for index in range(3)]
    container = SimpleNamespace(db=SimpleNamespace(get_all_blocks=lambda: blocks))
    raw = handlers["getblocks"].execute("getblocks 1", container)
    require(json.loads(raw)["data"]["blocks"] == blocks, "GETBLOCKS_CONTRACT_CHANGED")
    require(
        core.make_tau_read_request_v1("getblocks", "1")
        == core.TauObservationRejectV1(core.TauObservationRejectCodeV1.UNSUPPORTED_COMMAND),
        "GETBLOCKS_MUST_REMAIN_UNSUPPORTED",
    )
    return "getblocks_ignores_limit_and_observer_disallows_it"


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--upstream", required=True, type=Path)
    args = parser.parse_args()
    handlers = load_handlers(pinned_sources(args.upstream))
    checks = check_rules_and_accounts(handlers) + check_status_history(handlers)
    checks.append(check_getblocks_limit_is_ignored(handlers))
    print(
        json.dumps(
            {
                "status": "PASS",
                "upstream_commit": UPSTREAM_COMMIT,
                "source_sha256": SOURCE_SHA256,
                "checks": checks,
                "authority_granted": False,
                "live_node_qualified": False,
            },
            sort_keys=True,
            indent=2,
        )
    )


if __name__ == "__main__":
    main()
