from __future__ import annotations

import argparse
import json
from fractions import Fraction
from functools import lru_cache
from itertools import combinations, permutations
from pathlib import Path

import sympy as sp

from erdos506_small_n_incidence_audit import _feasible_circle_cover
from erdos506_small_n_relaxed_cover import line_patterns


N = 6
COUNTEREXAMPLE_CAP = 7
CORRECTED_EXACT_VALUE = 8

PASCH_PATTERN = ((0, 1, 2), (0, 3, 4), (1, 3, 5), (2, 4, 5))


def _canonical_pattern(pattern: tuple[tuple[int, ...], ...]) -> tuple[tuple[int, ...], ...]:
    best: tuple[tuple[int, ...], ...] | None = None
    for perm in permutations(range(N)):
        relabelled = tuple(sorted(tuple(sorted(perm[i] for i in block)) for block in pattern))
        if best is None or relabelled < best:
            best = relabelled
    assert best is not None
    return best


@lru_cache(maxsize=1)
def _survivor_orbit_counts() -> dict[tuple[tuple[int, ...], ...], int]:
    """Abstract line-pattern survivors under the corrected contradiction cap C <= 7."""

    counts: dict[tuple[tuple[int, ...], ...], int] = {}
    for pattern in line_patterns(N):
        feasible, _ = _feasible_circle_cover(N, pattern, COUNTEREXAMPLE_CAP)
        if feasible:
            canonical = _canonical_pattern(pattern)
            counts[canonical] = counts.get(canonical, 0) + 1
    return counts


def _collinear(
    points: list[tuple[Fraction, Fraction]], i: int, j: int, k: int
) -> bool:
    x1, y1 = points[i]
    x2, y2 = points[j]
    x3, y3 = points[k]
    return (x2 - x1) * (y3 - y1) == (y2 - y1) * (x3 - x1)


def _circle_key(
    points: list[tuple[Fraction, Fraction]], i: int, j: int, k: int
) -> tuple[Fraction, Fraction, Fraction]:
    """Return (D,E,F) for x^2+y^2+Dx+Ey+F=0 through a noncollinear triple."""

    rows: list[tuple[Fraction, Fraction, Fraction]] = []
    rhs: list[Fraction] = []
    for idx in (i, j, k):
        x, y = points[idx]
        rows.append((x, y, Fraction(1)))
        rhs.append(-(x * x + y * y))
    (a1, b1, c1), (a2, b2, c2), (a3, b3, c3) = rows
    det = (
        a1 * (b2 * c3 - c2 * b3)
        - b1 * (a2 * c3 - c2 * a3)
        + c1 * (a2 * b3 - b2 * a3)
    )
    assert det != 0

    def det_replace(col: int) -> Fraction:
        matrix = [list(row) for row in rows]
        for row, value in zip(matrix, rhs):
            row[col] = value
        (u1, v1, w1), (u2, v2, w2), (u3, v3, w3) = matrix
        return (
            u1 * (v2 * w3 - w2 * v3)
            - v1 * (u2 * w3 - w2 * u3)
            + w1 * (u2 * v3 - v2 * u3)
        )

    return tuple(det_replace(col) / det for col in range(3))  # type: ignore[return-value]


def _fraction_text(value: Fraction) -> str:
    return str(value.numerator) if value.denominator == 1 else f"{value.numerator}/{value.denominator}"


@lru_cache(maxsize=1)
def corrected_eight_circle_witness() -> dict[str, object]:
    """Exact rational witness that disproves the obsolete claim f(6)=9."""

    points = [
        (Fraction(0), Fraction(0)),
        (Fraction(4), Fraction(0)),
        (Fraction(1), Fraction(0)),
        (Fraction(1), Fraction(3)),
        (Fraction(2, 5), Fraction(6, 5)),
        (Fraction(2), Fraction(2)),
    ]
    collinear_triples: list[tuple[int, int, int]] = []
    circle_triples: dict[
        tuple[Fraction, Fraction, Fraction], list[tuple[int, int, int]]
    ] = {}
    for triple in combinations(range(N), 3):
        if _collinear(points, *triple):
            collinear_triples.append(triple)
        else:
            circle_triples.setdefault(_circle_key(points, *triple), []).append(triple)

    circles: list[dict[str, object]] = []
    owned_noncollinear_triples = 0
    for (D, E, F), triples in circle_triples.items():
        support = []
        for idx, (x, y) in enumerate(points):
            if x * x + y * y + D * x + E * y + F == 0:
                support.append(idx)
        radius_squared = (D * D + E * E) / 4 - F
        assert radius_squared > 0
        assert len(triples) == len(list(combinations(support, 3)))
        owned_noncollinear_triples += len(triples)
        circles.append(
            {
                "support": support,
                "coefficients_D_E_F": [_fraction_text(z) for z in (D, E, F)],
                "radius_squared": _fraction_text(radius_squared),
                "owned_triples": [list(triple) for triple in triples],
            }
        )

    circles.sort(key=lambda row: tuple(row["support"]))
    assert collinear_triples == [(0, 1, 2), (0, 3, 4), (1, 3, 5)]
    assert len(circle_triples) == CORRECTED_EXACT_VALUE
    assert owned_noncollinear_triples + len(collinear_triples) == 20
    assert max(len(row["support"]) for row in circles) == 4

    return {
        "points": [[_fraction_text(x), _fraction_text(y)] for x, y in points],
        "collinear_triples": [list(triple) for triple in collinear_triples],
        "circles": circles,
        "distinct_circle_count": len(circle_triples),
        "maximum_circle_support": max(len(row["support"]) for row in circles),
        "all_twenty_triples_accounted_for": True,
    }


@lru_cache(maxsize=1)
def pasch_similarity_certificate() -> dict[str, object]:
    """Verify the determinant identities used to reject the sole C <= 7 survivor.

    The coordinates are obtained by a Euclidean similarity, not by an arbitrary
    affine map.  Consequently the determinant test still represents circles.
    """

    a, b, u, v = sp.symbols("a b u v")
    R = u**2 + v**2
    t = a * (b - 1) / (b - a)
    points = [
        (sp.Integer(0), sp.Integer(0)),
        (sp.Integer(1), sp.Integer(0)),
        (a, sp.Integer(0)),
        (u, v),
        (b * u, b * v),
        (t + (1 - t) * u, (1 - t) * v),
    ]

    def determinant(indices: tuple[int, int, int, int]) -> sp.Expr:
        # Translate the first point to the origin and reduce the 4x4
        # concyclicity determinant to a much smaller 3x3 determinant.  The
        # leading minus sign restores the column orientation used in the
        # manuscript's definition of Delta.
        x0, y0 = points[indices[0]]
        rows = []
        for idx in indices[1:]:
            x, y = points[idx]
            X, Y = x - x0, y - y0
            rows.append([sp.expand(X * X + Y * Y), X, Y])
        return -sp.factor(sp.det(sp.Matrix(rows)))

    expected = {
        (0, 1, 4, 5): v * b**2 * (a - 1) * (b - 1) / (a - b) ** 2 * (-R * b + 2 * a * u - a),
        (0, 2, 3, 5): v * a**2 * (a - 1) * (b - 1) / (a - b) ** 2 * (-R * b - a + 2 * b * u),
        (1, 2, 3, 4): v * (a - 1) * (b - 1) * (-R * b + a),
    }
    for support, claimed in expected.items():
        assert sp.cancel(determinant(support) - claimed) == 0

    eq1 = a * (1 - 2 * u) + b * R
    eq2 = a + b * (R - 2 * u)
    eq3 = a - b * R
    assert sp.expand(eq3.subs(a, b * R)) == 0
    assert sp.expand(eq2.subs(a, b * R) - 2 * b * (R - u)) == 0
    assert sp.expand(eq1.subs(a, b * R) - 2 * b * R * (1 - u)) == 0
    assert sp.expand(R.subs(u, 1) - 1 - v**2) == 0

    return {
        "line_blocks": [list(block) for block in PASCH_PATTERN],
        "normalization": "Euclidean similarity: p0=(0,0), p1=(1,0), p3=(u,v), v!=0",
        "remaining_points": {
            "p2": "(a,0)",
            "p4": "b*(u,v)",
            "p5": "t*(1,0)+(1-t)*(u,v)",
            "t": "a*(b-1)/(b-a)",
            "R": "u^2+v^2",
        },
        "nonzero_conditions": ["a", "b", "v", "a-1", "b-1", "a-b"],
        "forced_circle_supports": [[0, 1, 4, 5], [0, 2, 3, 5], [1, 2, 3, 4]],
        "reduced_equations": [
            "a*(1-2*u)+b*R=0",
            "a+b*(R-2*u)=0",
            "a-b*R=0",
        ],
        "elimination": (
            "The third equation gives a=bR. The second then gives R=u; "
            "the first gives u=1 because b and R are nonzero. Finally "
            "R=u^2+v^2 forces v=0, contradicting the normalization."
        ),
        "determinant_identities_verified_symbolically": True,
        "uses_affine_circle_invariance": False,
    }


@lru_cache(maxsize=1)
def n6_survivor_geometry_audit() -> dict[str, object]:
    orbit_counts = _survivor_orbit_counts()
    canonical_pasch = _canonical_pattern(PASCH_PATTERN)
    assert set(orbit_counts) == {canonical_pasch}

    witness = corrected_eight_circle_witness()
    pasch = pasch_similarity_certificate()
    return {
        "packet": "corrected Erdos 506 n=6 geometry audit",
        "variant": "distinct real points, neither all collinear nor all concyclic",
        "n": N,
        "obsolete_claim": "f(6)=9",
        "corrected_exact_value": CORRECTED_EXACT_VALUE,
        "counterexample_cap_for_lower_bound": COUNTEREXAMPLE_CAP,
        "input_incidence_survivor_count_at_cap": sum(orbit_counts.values()),
        "survivor_orbit_count": len(orbit_counts),
        "sole_survivor": pasch,
        "paper_lower_bound_endpoint_replayed": True,
        "standalone_machine_certificate_of_lower_bound": False,
        "upper_bound_witness": witness,
        "upper_bound_eight_certified": witness["distinct_circle_count"] == CORRECTED_EXACT_VALUE,
        "correction": (
            "The former script normalized an arbitrary triangle affinely and then tested Euclidean "
            "concyclicity. Affine maps do not preserve circles. Under the corrected cap C<=7 only "
            "the complete-quadrilateral orbit survives, and the similarity-safe determinant "
            "certificate above rejects it. The displayed rational configuration attains C=8."
        ),
        "claim_boundary": (
            "This script exactly enumerates the abstract line-pattern survivors, verifies the "
            "displayed rational upper witness, and symbolically checks the determinant identities "
            "at the sole Pasch endpoint. The support-forcing/equality argument connecting an "
            "arbitrary C<=7 configuration to the three displayed four-circles is proved in the "
            "manuscript, not independently encoded here. Thus this is a reproducibility audit, "
            "not a standalone machine certificate of the full lower bound."
        ),
    }


def main() -> int:
    parser = argparse.ArgumentParser(description="Corrected n=6 geometry audit for Erdos 506.")
    parser.add_argument("--output-json", type=Path)
    args = parser.parse_args()
    payload = n6_survivor_geometry_audit()
    text = json.dumps(payload, indent=2, sort_keys=True)
    if args.output_json:
        args.output_json.write_text(text + "\n", encoding="utf-8")
    else:
        print(text)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
