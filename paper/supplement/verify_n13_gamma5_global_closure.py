"""Independent exact-arithmetic audit of the n=13, Gamma=5 branch.

This file verifies a second global closure, separate from the direct
blockwise transfer printed in the article.  It is a certificate checker,
not a premise of the proof and not a configuration search.
"""

from fractions import Fraction

import sympy as sp


def choose3(s: int) -> int:
    return s * (s - 1) * (s - 2) // 6


def main() -> None:
    # Circle coefficient identity.
    beta = {3: 10, 4: 13, 5: 13}
    for s in (3, 4, 5):
        rhs = 45 * choose3(s) + 31 * s * (4 - s) - 23 * s * (s - 4) + 9 * beta[s]
        assert rhs == 297, (s, rhs)

    # Line remainder and its sign on the geometrically possible range.
    x = sp.symbols("x", integer=True)
    raw = 46 * x * (x - 2) - 45 * x * (x - 1) * (x - 2) / 6 - 31 * x * (4 - x)
    factored = x * (x - 3) * (154 - 15 * x) / 2
    assert sp.expand(raw - factored) == 0
    remainders = {}
    for s in range(3, 11):
        value = int(factored.subs(x, s))
        assert value >= 0
        remainders[s] = value
    assert [remainders[s] for s in (4, 5, 6, 7)] == [188, 395, 576, 686]

    # Global lower bound and boundary slack budgets.
    base = 45 * 286 + 31 * 39 - 23 * 117 + 9 * 663
    assert base == 17355
    assert Fraction(base, 297) == Fraction(5785, 99) > 58
    assert 297 * 59 - base == 168
    assert 297 * 60 - base == 465

    # The exceptional local count follows without a scalar scan.  The
    # divisibility equation is
    #
    #     3*t3 + sigma == 0 (mod 7),
    #
    # while 0 <= t3 <= 2 and 0 <= sigma <= 2-t3 imply
    # 0 <= 3*t3+sigma <= 2*t3+2 <= 6.  Hence the left side is zero,
    # and nonnegativity gives t3=sigma=0.
    assert 2 * 2 + 2 == 6 < 7
    t3 = sigma = 0
    t4 = (63 - 3 * t3 - sigma) // 7
    t2 = sigma + 3 + t4
    assert (t2, t3, t4, sigma) == (12, 0, 9, 0)
    assert t2 + 3 * t3 + 6 * t4 == 66

    # Symbolic elimination for the boundary cases.
    C, C3, C4, k, ell, e, f, R = sp.symbols("C C3 C4 k ell e f R", integer=True)
    defining = {
        R: 286 - 4 * C,
        ell: R + 3 * C3 - 6 * k - 4 * e - 10 * f,
        C4: (286 - C - ell - 9 * k - 4 * e - 10 * f) / 3,
    }

    # Direct expansions of D and M from their block coefficients.
    D_direct = -3 * C3 + 5 * k + 6 * ell + 16 * e + 30 * f
    M_direct = 3 * C3 - 5 * k + 3 * ell - 5 * f
    r_expr = defining[R]
    assert sp.simplify(
        D_direct.subs(C3, (ell - R + 6 * k + 4 * e + 10 * f) / 3)
        - (R + 5 * ell - k + 12 * e + 20 * f)
    ) == 0
    assert sp.simplify(
        M_direct.subs(C3, (ell - R + 6 * k + 4 * e + 10 * f) / 3)
        - (4 * ell + k + 4 * e + 5 * f - R)
    ) == 0

    # Pointwise facet equivalence.
    c4_expr = defining[C4]
    m_expr = 4 * ell + k + 4 * e + 5 * f - R
    facet_left = 4 * (c4_expr + e) + m_expr - 78
    facet_numerator = 8 * C + 8 * ell + 8 * e - 25 * f + 52 - 33 * k
    assert sp.simplify(3 * facet_left.subs(R, r_expr) - facet_numerator) == 0

    # Compare the facet upper bound with the D and M lower bounds on k.
    upper = 8 * C + 8 * ell + 8 * e - 25 * f + 52
    lower_d = R + 5 * ell + 12 * e + 20 * f - 117
    lower_m = R + 39 - 4 * ell - 4 * e - 5 * f
    assert sp.expand((upper - 33 * lower_m).subs(R, r_expr)) == (
        140 * C + 140 * ell + 140 * e + 140 * f - 10673
    )
    assert sp.expand((upper - 33 * lower_d).subs(R, r_expr)) == (
        140 * C - 157 * ell - 388 * e - 685 * f - 5525
    )

    # C=59 contradiction.
    assert (10673 - 140 * 59 + 139) // 140 == 18
    assert (140 * 59 - 5525) // 157 == 17

    # C=60: the inequalities force e=f=0 and ell in {17,18};
    # the triple identity requires ell == 1 mod 3.
    assert (10673 - 140 * 60 + 139) // 140 == 17
    assert 140 * 60 - 5525 == 2875
    assert 388 - 157 == 231
    assert 685 - 157 == 528
    assert 2875 - 157 * 17 == 206
    assert 231 > 206 and 528 > 206
    possible_ell = list(range(17, 2875 // 157 + 1))
    assert possible_ell == [17, 18]
    assert all(value % 3 != 1 for value in possible_ell)
    assert 46 % 3 == 1

    print("PASS_SYMBOLIC_N13_GAMMA5_ADDED_CENTER_GLOBAL_CLOSURE")


if __name__ == "__main__":
    main()
