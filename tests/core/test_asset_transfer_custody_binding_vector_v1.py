"""The committed synthetic vector must follow the recorded regeneration command."""

from experiments.v3_custody_successor_v1.render_vectors import ROOT, VECTOR_PATH, vector_bytes


def test_custody_binding_vector_matches_the_actual_python_binding() -> None:
    assert (ROOT / VECTOR_PATH).read_bytes() == vector_bytes()
