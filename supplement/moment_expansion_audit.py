#!/usr/bin/env python3
"""Exact symbolic audit of the finite-horizon variance coefficients.

This script reproduces the algebraic certificate described in
"An Exponentially Weighted Endpoint Coordinate".  It performs no simulation
and contains no fitted coefficients.

For

    x = sum_j w_j Q_j R_j,
    y = sum_j w_j (R_j - 1),
    L = 2 * atanh(x / (1 + y)),

with geometric Wilder weights w_j = alpha * (1 - alpha)**j, the script:

1. derives the one-observation joint cumulants from raw moments by enumerating
   set partitions;
2. derives moments of (x, y) from their joint cumulants, again by enumerating
   set partitions;
3. derives the degree-eight Taylor polynomial P_8 for (L / 2)**2 and checks
   it against the coefficient table used by the moment calculation;
4. extracts the coefficients v_1, ..., v_4 in

       Var(L) = v_1 alpha + ... + v_4 alpha**4 + O(alpha**5);

5. checks the general formulas and the Laplace, Rademacher, Gaussian, and
   Student-t first-shift special cases using exact symbolic arithmetic.

Requirement: SymPy 1.14 or newer is recommended.
Run with:   python moment_expansion_audit.py
"""

from __future__ import annotations

from functools import lru_cache
from math import factorial
import sympy as sp


ALPHA_ORDER = 4

alpha = sp.symbols("alpha")
m2, m3, m4, m5 = sp.symbols("m2 m3 m4 m5")
x_symbol, y_symbol, degree_marker = sp.symbols("x y degree_marker")
MOMENTS = {0: sp.Integer(1), 1: sp.Integer(1), 2: m2, 3: m3, 4: m4, 5: m5}


@lru_cache(maxsize=None)
def set_partitions(n: int) -> tuple[tuple[tuple[int, ...], ...], ...]:
    """Return every set partition of range(n), each exactly once."""
    if n == 0:
        return ((),)

    newest = n - 1
    result: list[tuple[tuple[int, ...], ...]] = []
    for partition in set_partitions(n - 1):
        # Put the new element in a new final block.
        result.append(partition + ((newest,),))

        # Or insert it into each existing block.
        for block_index in range(len(partition)):
            updated = list(partition)
            updated[block_index] = updated[block_index] + (newest,)
            result.append(tuple(updated))

    return tuple(result)


def truncate_alpha(expr: sp.Expr) -> sp.Expr:
    """Keep terms through alpha**ALPHA_ORDER."""
    return sp.series(expr, alpha, 0, ALPHA_ORDER + 1).removeO().expand()


AlphaPolynomial = tuple[sp.Expr, ...]
ZERO_POLY: AlphaPolynomial = tuple(sp.Integer(0) for _ in range(ALPHA_ORDER + 1))
ONE_POLY: AlphaPolynomial = (sp.Integer(1),) + tuple(
    sp.Integer(0) for _ in range(ALPHA_ORDER)
)


def poly_add(left: AlphaPolynomial, right: AlphaPolynomial) -> AlphaPolynomial:
    """Add two alpha-series coefficient vectors."""
    return tuple(left[k] + right[k] for k in range(ALPHA_ORDER + 1))


def poly_scale(poly: AlphaPolynomial, scalar: sp.Expr) -> AlphaPolynomial:
    """Multiply an alpha-series coefficient vector by a scalar."""
    return tuple(scalar * coefficient for coefficient in poly)


def poly_multiply(left: AlphaPolynomial, right: AlphaPolynomial) -> AlphaPolynomial:
    """Multiply two alpha series, truncating above alpha**4."""
    result = [sp.Integer(0)] * (ALPHA_ORDER + 1)
    for left_order, left_coefficient in enumerate(left):
        if left_coefficient == 0:
            continue
        for right_order, right_coefficient in enumerate(right):
            total_order = left_order + right_order
            if total_order > ALPHA_ORDER:
                break
            if right_coefficient != 0:
                result[total_order] += left_coefficient * right_coefficient
    return tuple(result)


def expression_to_poly(expr: sp.Expr) -> AlphaPolynomial:
    """Convert an expression to a truncated alpha-series coefficient vector."""
    expanded = truncate_alpha(expr)
    return tuple(expanded.coeff(alpha, k) for k in range(ALPHA_ORDER + 1))


def poly_to_expression(poly: AlphaPolynomial) -> sp.Expr:
    """Convert an alpha-series coefficient vector to a SymPy expression."""
    return sp.expand(sum(poly[k] * alpha**k for k in range(ALPHA_ORDER + 1)))


def radial_moment(order: int) -> sp.Expr:
    """Return m_order = E[R**order], using m_0 = m_1 = 1."""
    if order not in MOMENTS:
        raise ValueError(f"Moment m_{order} was requested but is not needed by the audit.")
    return MOMENTS[order]


@lru_cache(maxsize=None)
def raw_joint_moment(q_count: int, r_count: int) -> sp.Expr:
    """Compute E[(Q R)^q_count (R - 1)^r_count]."""
    if q_count % 2 == 1:
        return sp.Integer(0)

    return sp.expand(
        sum(
            sp.binomial(r_count, k)
            * (-1) ** (r_count - k)
            * radial_moment(q_count + k)
            for k in range(r_count + 1)
        )
    )


@lru_cache(maxsize=None)
def one_observation_cumulant(q_count: int, r_count: int) -> sp.Expr:
    """Compute c_{q_count,r_count} from the moment-cumulant formula."""
    variables = ("q",) * q_count + ("r",) * r_count
    n = len(variables)
    if n == 0:
        raise ValueError("A cumulant must contain at least one argument.")

    total = sp.Integer(0)
    for partition in set_partitions(n):
        block_product = sp.Integer(1)
        for block in partition:
            block_q = sum(variables[index] == "q" for index in block)
            block_r = len(block) - block_q
            block_product *= raw_joint_moment(block_q, block_r)

        block_count = len(partition)
        total += (
            factorial(block_count - 1)
            * (-1) ** (block_count - 1)
            * block_product
        )

    return sp.factor(total)


@lru_cache(maxsize=None)
def weight_power_sum_series(order: int) -> sp.Expr:
    """Series of s_order = sum_j w_j**order through alpha**4."""
    if order < 2:
        raise ValueError("Only centered cumulants of order at least two are used.")
    exact = alpha**order / (1 - (1 - alpha) ** order)
    return truncate_alpha(exact)


@lru_cache(maxsize=None)
def weighted_joint_cumulant_poly(x_count: int, y_count: int) -> AlphaPolynomial:
    """Alpha-series vector for a weighted joint cumulant."""
    order = x_count + y_count
    if order == 1 or order > 5:
        return ZERO_POLY
    return poly_scale(
        expression_to_poly(weight_power_sum_series(order)),
        one_observation_cumulant(x_count, y_count),
    )


@lru_cache(maxsize=None)
def weighted_joint_moment_poly(x_count: int, y_count: int) -> AlphaPolynomial:
    """Coefficient vector for E[x**x_count y**y_count] through alpha**4."""
    variables = ("x",) * x_count + ("y",) * y_count
    total = ZERO_POLY

    for partition in set_partitions(len(variables)):
        contribution = ONE_POLY
        for block in partition:
            block_x = sum(variables[index] == "x" for index in block)
            block_y = len(block) - block_x
            cumulant = weighted_joint_cumulant_poly(block_x, block_y)
            if cumulant == ZERO_POLY:
                contribution = ZERO_POLY
                break
            contribution = poly_multiply(contribution, cumulant)
        total = poly_add(total, contribution)

    return total


def weighted_joint_moment(x_count: int, y_count: int) -> sp.Expr:
    """SymPy expression for E[x**x_count y**y_count] through alpha**4."""
    return poly_to_expression(weighted_joint_moment_poly(x_count, y_count))


# Coefficients of the total-degree-eight Taylor polynomial P_8(x, y) for
# atanh(x / (1 + y))**2.
P8_TERMS: tuple[tuple[sp.Rational, int, int], ...] = (
    (sp.Rational(1), 2, 0),
    (sp.Rational(-2), 2, 1),
    (sp.Rational(3), 2, 2),
    (sp.Rational(-4), 2, 3),
    (sp.Rational(5), 2, 4),
    (sp.Rational(-6), 2, 5),
    (sp.Rational(7), 2, 6),
    (sp.Rational(2, 3), 4, 0),
    (sp.Rational(-8, 3), 4, 1),
    (sp.Rational(20, 3), 4, 2),
    (sp.Rational(-40, 3), 4, 3),
    (sp.Rational(70, 3), 4, 4),
    (sp.Rational(23, 45), 6, 0),
    (sp.Rational(-46, 15), 6, 1),
    (sp.Rational(161, 15), 6, 2),
    (sp.Rational(44, 105), 8, 0),
)


def p8_from_table() -> sp.Expr:
    """Return the displayed P_8 coefficient table as a SymPy expression."""
    return sp.expand(
        sum(
            coefficient * x_symbol**x_power * y_symbol**y_power
            for coefficient, x_power, y_power in P8_TERMS
        )
    )


def p8_from_taylor_series() -> sp.Expr:
    """Derive the total-degree-eight Taylor polynomial independently."""
    scaled = sp.atanh(
        degree_marker * x_symbol / (1 + degree_marker * y_symbol)
    ) ** 2
    return sp.expand(
        sp.series(scaled, degree_marker, 0, 9)
        .removeO()
        .subs(degree_marker, 1)
    )


def computed_variance_series() -> sp.Expr:
    """Return 4 E[P_8(x,y)], i.e. Var(L) through alpha**4."""
    expectation = ZERO_POLY
    for coefficient, x_power, y_power in P8_TERMS:
        expectation = poly_add(
            expectation,
            poly_scale(weighted_joint_moment_poly(x_power, y_power), coefficient),
        )
    return poly_to_expression(poly_scale(expectation, sp.Integer(4)))


def coefficient_tuple(series: sp.Expr) -> tuple[sp.Expr, ...]:
    expanded = sp.expand(series)
    return tuple(sp.factor(expanded.coeff(alpha, k)) for k in range(1, 5))


def assert_symbolic_equal(label: str, actual: sp.Expr, expected: sp.Expr) -> None:
    difference = sp.factor(sp.expand(actual - expected))
    if difference != 0:
        raise AssertionError(
            f"{label} failed:\n  actual   = {actual}\n"
            f"  expected = {expected}\n  difference = {difference}"
        )


def audit_p8_generation() -> None:
    """Check that the coefficient table is the actual Taylor polynomial."""
    assert_symbolic_equal(
        "generated P_8 Taylor polynomial",
        p8_from_taylor_series(),
        p8_from_table(),
    )


def audit_student_first_shift(
    general: tuple[sp.Expr, ...],
) -> tuple[sp.Expr, tuple[sp.Expr, ...]]:
    """Check the Student-t first-shift formula and exact selected values."""
    nu, c_squared = sp.symbols("nu c_squared")
    def raw_abs_moment(order: int) -> sp.Expr:
        return (
            nu ** sp.Rational(order, 2)
            * sp.gamma(sp.Rational(order + 1, 2))
            * sp.gamma((nu - order) / 2)
            / (sp.sqrt(sp.pi) * sp.gamma(nu / 2))
        )
    c_squared_from_gamma = sp.simplify(
        sp.expand_func(2 * raw_abs_moment(2) / raw_abs_moment(1) ** 2)
    )
    radial_third_ratio = sp.simplify(
        sp.expand_func(
            raw_abs_moment(3) / (raw_abs_moment(1) * raw_abs_moment(2))
        )
    )
    assert_symbolic_equal(
        "Student radial m3/m2 ratio",
        radial_third_ratio,
        2 * (nu - 2) / (nu - 3),
    )
    student_m2 = c_squared / 2
    student_m3 = student_m2 * radial_third_ratio
    student_k = sp.factor(
        (general[1] / general[0]).subs({m2: student_m2, m3: student_m3})
    )
    expected_k = sp.Rational(5, 4) * c_squared - sp.Rational(7, 3) - sp.Rational(
        8, 3
    ) / (nu - 3)
    assert_symbolic_equal("Student K_nu formula", student_k, expected_k)

    selected_data = (
        (sp.Integer(4), sp.Integer(4), sp.Integer(0)),
        (sp.Integer(5), 3 * sp.pi**2 / 8, 15 * sp.pi**2 / 32 - sp.Rational(11, 3)),
        (sp.Integer(6), sp.Rational(32, 9), sp.Rational(11, 9)),
        (sp.Integer(8), sp.Rational(256, 75), sp.Rational(7, 5)),
    )
    selected_values: list[sp.Expr] = []
    for nu_value, c_squared_value, target in selected_data:
        observed_c_squared = sp.simplify(c_squared_from_gamma.subs(nu, nu_value))
        assert_symbolic_equal(
            f"Student C_{nu_value} squared", observed_c_squared, c_squared_value
        )
        observed = sp.factor(
            student_k.subs({nu: nu_value, c_squared: observed_c_squared})
        )
        assert_symbolic_equal(f"Student K_{nu_value}", observed, target)
        selected_values.append(observed)

    return student_k, tuple(selected_values)


def audit_one_observation_cumulants() -> None:
    expected = {
        (2, 0): m2,
        (0, 2): m2 - 1,
        (2, 1): m3 - m2,
        (0, 3): m3 - 3 * m2 + 2,
        (4, 0): m4 - 3 * m2**2,
        (2, 2): m4 - 2 * m3 + 2 * m2 - m2**2,
        (0, 4): m4 - 4 * m3 + 12 * m2 - 3 * m2**2 - 6,
        (4, 1): m5 - m4 - 6 * m2 * m3 + 6 * m2**2,
        (2, 3): m5 - 3 * m4 + 6 * m3 - 6 * m2 + 6 * m2**2 - 4 * m2 * m3,
        (0, 5): m5 - 5 * m4 + 20 * m3 - 60 * m2 + 30 * m2**2 - 10 * m2 * m3 + 24,
    }
    for counts, target in expected.items():
        assert_symbolic_equal(
            f"one-observation cumulant c_{counts}",
            one_observation_cumulant(*counts),
            target,
        )


def expected_general_coefficients() -> tuple[sp.Expr, ...]:
    return (
        2 * m2,
        (15 * m2**2 + 2 * m2 - 8 * m3) / 3,
        (64 * m2**3 + 5 * m2**2 - 64 * m2 * m3 + m2 - 2 * m3 + 11 * m4) / 3,
        (
            11700 * m2**4
            - 17040 * m2**2 * m3
            + 70 * m2**2
            + 224 * m2 * m3
            + 4020 * m2 * m4
            + 18 * m2
            + 2400 * m3**2
            - 18 * m3
            - 99 * m4
            - 480 * m5
        )
        / 90,
    )


def normalizer_coefficients(coefficients: tuple[sp.Expr, ...]) -> tuple[sp.Expr, ...]:
    """Return K, A, B in g*(n) = n - K + A/n + B/n**2 + O(n**-3)."""
    v1, v2, v3, v4 = coefficients
    a = sp.cancel(v2 / v1)
    b = sp.cancel(v3 / v1)
    c = sp.cancel(v4 / v1)
    return tuple(sp.factor(value) for value in (a, a**2 - b, -a**3 + 2 * a * b - c))


def audit_special_case(
    name: str,
    general: tuple[sp.Expr, ...],
    substitutions: dict[sp.Symbol, sp.Expr],
    expected: tuple[sp.Expr, ...],
) -> tuple[sp.Expr, ...]:
    actual = tuple(sp.factor(value.subs(substitutions)) for value in general)
    for index, (observed, target) in enumerate(zip(actual, expected), start=1):
        assert_symbolic_equal(f"{name} v_{index}", observed, target)
    return actual


def main() -> None:
    audit_p8_generation()
    audit_one_observation_cumulants()

    variance_series = computed_variance_series()
    computed = coefficient_tuple(variance_series)
    expected = expected_general_coefficients()
    for index, (observed, target) in enumerate(zip(computed, expected), start=1):
        assert_symbolic_equal(f"general v_{index}", observed, target)

    laplace = audit_special_case(
        "Laplace",
        computed,
        {m2: 2, m3: 6, m4: 24, m5: 120},
        (sp.Integer(4), sp.Rational(16, 3), sp.Integer(6), sp.Rational(52, 9)),
    )
    rademacher = audit_special_case(
        "Rademacher",
        computed,
        {m2: 1, m3: 1, m4: 1, m5: 1},
        (sp.Integer(2), sp.Integer(3), sp.Integer(5), sp.Rational(53, 6)),
    )
    gaussian_expected = (
        sp.pi,
        sp.pi * (15 * sp.pi - 28) / 12,
        sp.pi * (16 * sp.pi**2 - 45 * sp.pi - 3) / 6,
        sp.pi * (2925 * sp.pi**3 - 11010 * sp.pi**2 + 5981 * sp.pi - 36) / 360,
    )
    gaussian = audit_special_case(
        "Gaussian",
        computed,
        {m2: sp.pi / 2, m3: sp.pi, m4: 3 * sp.pi**2 / 4, m5: 2 * sp.pi**2},
        gaussian_expected,
    )
    student_formula, student_values = audit_student_first_shift(computed)

    laplace_normalizer = normalizer_coefficients(laplace)
    gaussian_normalizer = normalizer_coefficients(gaussian)
    for label, actual, target in zip(
        ("Laplace K", "Laplace A", "Laplace B"),
        laplace_normalizer,
        (sp.Rational(4, 3), sp.Rational(5, 18), sp.Rational(5, 27)),
    ):
        assert_symbolic_equal(label, actual, target)
    for label, actual, target in zip(
        ("Gaussian K", "Gaussian A", "Gaussian B"),
        gaussian_normalizer,
        (
            (15 * sp.pi - 28) / 12,
            (856 + 240 * sp.pi - 159 * sp.pi**2) / 144,
            (89220 * sp.pi**2 + 130784 - 28344 * sp.pi - 29475 * sp.pi**3) / 8640,
        ),
    ):
        assert_symbolic_equal(label, actual, target)

    print(f"SymPy {sp.__version__}")
    print("PASS: generated P_8 Taylor polynomial")
    print("PASS: one-observation cumulant table")
    print("PASS: general coefficients")
    for index, value in enumerate(computed, start=1):
        print(f"  v_{index} = {value}")
    print("PASS: Laplace coefficients      ", laplace)
    print("PASS: Rademacher coefficients   ", rademacher)
    print("PASS: Gaussian coefficients     ", gaussian)
    print("PASS: Laplace normalizer (K,A,B)", laplace_normalizer)
    print("PASS: Gaussian normalizer (K,A,B)", gaussian_normalizer)
    print("PASS: Student first-shift formula ", student_formula)
    print("PASS: Student K_(4,5,6,8)        ", student_values)
    print("ALL EXACT SYMBOLIC CHECKS PASSED")


if __name__ == "__main__":
    main()
