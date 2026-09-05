"""Independent partition oracle and Python half of the Rust projection fixture."""

from tools import render_global_accounting_allocation_projection_v1_golden as renderer


def test_projection_fixture_is_current() -> None:
    assert renderer.FIXTURE_PATH_V1.read_bytes() == renderer.render_bytes_v1()


def test_partition_vectors_follow_integer_partition_and_witness_obligations() -> None:
    vectors = renderer.render_fixture_v1()["vectors"]
    for controlled in (0, 1, 2, renderer.MAX_ATOMS - 1, renderer.MAX_ATOMS):
        for claimed in (0, 1, 2, renderer.MAX_ATOMS - 1, renderer.MAX_ATOMS):
            expected = "PROJECTION_WITNESS_REQUIRED"
            if claimed > controlled:
                expected = "PROJECTION_NEGATIVE_RESIDUAL"
            elif claimed < controlled:
                expected = "PROJECTION_UNASSIGNED_CONTROLLED_ATOMS"
            assert vectors[f"partition_{controlled}_{claimed}"]["expected"]["code"] == expected
    assert vectors["custody_fold_overflow"]["expected"]["code"] == "PROJECTION_ROW_TOTAL_OVERFLOW"
    assert (
        vectors["liability_fold_above_u128"]["expected"]["code"] == "PROJECTION_NEGATIVE_RESIDUAL"
    )
    assert (
        vectors["zero_support_precedes_negative"]["expected"]["code"]
        == "PROJECTION_NONCANONICAL_ZERO_ECONOMIC_ROW"
    )
