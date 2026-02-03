from __future__ import annotations


def test_state_pair_to_facts_delta_and_escaping() -> None:
    from tools.trace_to_facts import state_pair_to_facts

    pre = {"a": 1, "b": True, "s": "a'b", "unchanged": 9}
    post = {"a": 3, "b": False, "s": "c", "unchanged": 9}

    facts = state_pair_to_facts(ex_id="ex1", pre=pre, post=post, include_delta=True, only_changed=True)

    assert facts == [
        "in('ex1','a',1).",
        "out('ex1','a',3).",
        "delta('ex1','a',2).",
        "in('ex1','b',true).",
        "out('ex1','b',false).",
        "in('ex1','s','a''b').",
        "out('ex1','s','c').",
    ]

