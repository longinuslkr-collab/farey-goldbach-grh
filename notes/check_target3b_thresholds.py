"""Check the 8/17 and 7/15 exponent tables using exact fractions."""

from fractions import Fraction


def elementary_cut(x, cap):
    return (3 * x - 2 * cap) / 10


def spectral_cut(x, cap):
    return (6 * x - 4 * cap) / 17


def target(x, cap, cap_denominator):
    return (cap_denominator * cap - x) / 10


def type_i(x, j, r):
    return j - x, j + 2 * r - x / 2


def cauchy(x, j, s):
    return (j - s) / 2, j - x / 2, j + s / 2 - x / 4


def spectral_cauchy(x, j, s):
    return (j - s) / 2, j - x / 2, j + 3 * s / 8 - x / 4


def sixth_moment(x, j, s):
    return (5 * j - 2 * s) / 6, (5 * j + s - x) / 6, j - s / 2, j - x / 6


def fourth_moment(x, j, s):
    return (3 * j + s - x) / 4, (3 * j - s) / 4, j + s / 2 - x / 2, j - x / 4


def check_vertices(cap_denominator, middle_cut, first_band, tight_rows):
    # Homogeneity allows x = 1. At a fixed cap, each band's affine
    # inequalities attain their maximum over j and s at their endpoints.
    # Each such endpoint value is affine in cap, so only its two endpoints
    # need to be checked as well.
    x = Fraction(1)
    for cap in (Fraction(0), x / cap_denominator):
        r, t, u = (x - cap) / 5, middle_cut(x, cap), (2 * x - cap) / 5
        assert 0 <= cap < r < t < u <= x / 2
        limit = target(x, cap, cap_denominator)
        for j in (Fraction(0), cap):
            assert all(row <= limit for row in type_i(x, j, r))
            for low, high, rows in (
                (r, t, first_band),
                (t, u, sixth_moment),
                (u, x / 2, fourth_moment),
            ):
                for s in (low, high):
                    assert all(row <= limit for row in rows(x, j, s))
        assert tight_rows(x, cap, t, u) == (limit, limit)


def elementary_tight_rows(x, cap, t, _u):
    return cauchy(x, cap, t)[2], sixth_moment(x, cap, t)[0]


def spectral_tight_rows(x, cap, _t, u):
    return sixth_moment(x, cap, u)[1], fourth_moment(x, cap, u)[1]


def check_thresholds():
    for theta, elementary_sign, spectral_sign in (
        (Fraction(46, 100), 1, 1),
        (Fraction(7, 15), 1, 0),
        (Fraction(47, 100), 1, -1),
        (Fraction(8, 17), 0, -1),
        (Fraction(59, 125), -1, -1),
        (Fraction(9, 19), -1, -1),
        (Fraction(1, 2), -1, -1),
    ):
        x, cap = 1 - theta, 1 - 2 * theta
        for cap_denominator, expected_sign in ((9, elementary_sign), (8, spectral_sign)):
            bound = target(x, cap, cap_denominator)
            assert bound == (
                cap_denominator - 1 - (2 * cap_denominator - 1) * theta
            ) / 10
            assert (bound > 0) - (bound < 0) == expected_sign
    assert Fraction(8, 17) < Fraction(59, 125) < Fraction(9, 19)
    assert Fraction(7, 15) < Fraction(47, 100) < Fraction(8, 17)


def check_spectral_completion():
    # These expressions are affine. Normalize x to 1 and check the vertices.
    x = Fraction(1)
    for cap in (Fraction(0), x / 8):
        r = (x - cap) / 5
        assert r - cap >= x / 20
        for s in (r, x / 2):
            for k in (Fraction(0), s):
                assert k / 2 + Fraction(7, 32) * (cap - k) / 2 <= s / 2
            for j in (Fraction(0), cap):
                outer = 2 * x - s
                tuples = 2 * (j + s)
                first = (outer + tuples + x + s / 2) / 2 - 2 * x
                second = (outer + tuples + 3 * x / 2 - s / 4) / 2 - 2 * x
                assert first == j + 3 * s / 4 - x / 2
                assert first <= second == spectral_cauchy(x, j, s)[2]

    j = x / 8
    s = 3 * j
    assert spectral_cauchy(x, j, s)[2] == x / 64
    assert sixth_moment(x, j, s)[1] == fourth_moment(x, j, s)[1] == 0


if __name__ == "__main__":
    check_vertices(9, elementary_cut, cauchy, elementary_tight_rows)
    check_vertices(8, spectral_cut, spectral_cauchy, spectral_tight_rows)
    check_thresholds()
    check_spectral_completion()
    print("Verified both exponent tables, the spectral completion, and the thresholds 8/17 and 7/15.")
