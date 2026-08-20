"""Exact arithmetic checks for formulas in SIMPLIFICATION_NOTES.md.

This script performs no search.  It only evaluates the displayed parametric
identities at q=7,8,9 and checks the claimed integral bounds.
"""

from fractions import Fraction
from math import comb, floor


def target(n: int) -> int:
    return 1 + comb(n - 1, 2) - floor((n - 1) / 2)


def added_centre_numerator(q: int) -> int:
    n = q + 6
    return (
        6 * comb(q, 3)
        + 54 * comb(q, 2)
        + 198 * q
        + 174
        - 36 * (target(n) - 1)
        - 4 * n * (n - 4)
    )


def signature_upper_bound(q: int) -> int:
    return 2 * comb(q, 2) + 4 * floor(q / 2)


expected = {
    7: (276, 46, 54),
    8: (454, 76, 72),
    9: (720, 120, 88),
}

for q, (numerator, lower, upper) in expected.items():
    actual_numerator = added_centre_numerator(q)
    actual_lower = -(-actual_numerator // 6)
    actual_upper = signature_upper_bound(q)
    assert (actual_numerator, actual_lower, actual_upper) == (
        numerator,
        lower,
        upper,
    )
    print(
        f"q={q}: 6W>={actual_numerator}, W>={actual_lower}, "
        f"W<={actual_upper}, raw_lower={Fraction(actual_numerator, 6)}"
    )

print("PASS_REVIEW_SIMPLIFICATION_IDENTITIES_NO_SEARCH")


def split_row_numerator(n: int, m: int, circle_cap: int) -> int:
    """The lower numerator 6W for the common selected-circle row."""

    q = n - m
    p0 = comb(q, 3)
    p1 = m * comb(q, 2)
    p2 = comb(m, 2) * q
    p3 = comb(m, 3)
    return (
        6 * p0
        + 9 * p1
        + 12 * p2
        + 6 * p3
        + 3 * (3 * m)
        + 6 * (3 * q)
        - 36 * circle_cap
        - 4 * n * (n - 4)
    )


expected_n16 = {
    4: (540, 90, 84),
    5: (792, 132, 110),
    6: (1008, 168, 110),
}

for m, (numerator, lower, upper) in expected_n16.items():
    actual_numerator = split_row_numerator(16, m, 98)
    actual_lower = -(-actual_numerator // 6)
    if m == 4:
        q = 12
        actual_upper = comb(q, 2) + 3 * floor(q / 2)
    elif m == 5:
        q = 11
        actual_upper = 2 * comb(q, 2)
    else:
        q = 10
        actual_upper = signature_upper_bound(q)
    assert (actual_numerator, actual_lower, actual_upper) == (
        numerator,
        lower,
        upper,
    )
    assert actual_lower > actual_upper
    print(
        f"n=16,m={m}: 6W>={actual_numerator}, W>={actual_lower}, "
        f"W<={actual_upper}"
    )


def selected_slack(m: int) -> int:
    selected_coefficient = 6 * comb(m, 3) + 3 * m * (4 - m) - 36
    return 4 * m * (m - 4) - selected_coefficient


assert [selected_slack(m) for m in (4, 5, 6)] == [12, 11, 0]

# Nonselected line factors for all ranges allowed by the nine-point rich-block
# cap.  These are the only ranges needed for n=16,m=4,5,6.
for x in range(3, 10):
    assert x * (14 - x) * (x - 3) >= 0
for x in range(2, 9):
    assert (x - 2) * (-2 * x * x + 21 * x + 17) >= 0
for x in range(1, 8):
    assert (x - 1) * (-x * x + 7 * x + 12) >= 0

print("PASS_N16_M4_M5_M6_COMMON_ROW_AND_SIGNATURE_BOUNDS_NO_SEARCH")
