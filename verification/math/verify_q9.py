#!/usr/bin/env python3
"""Exact finite-dimensional checks for the closed genus-five q=9 branch.

Only the orbit algebra, polynomial identities, and divisor-degree bookkeeping
are checked here. The sheaf and relative-geometric arguments are outside the
scope of this script.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from itertools import permutations
from typing import Iterable

Scalar = Fraction
NumericMatrix = tuple[tuple[Scalar, ...], ...]
EXPONENTS = 6  # D, a, b, c, f, lambda


@dataclass(frozen=True)
class Polynomial:
    terms: tuple[tuple[tuple[int, ...], Scalar], ...]

    def __init__(self, value: int | Scalar | dict[tuple[int, ...], Scalar] = 0):
        if isinstance(value, dict):
            cleaned = tuple(
                sorted(
                    (power, Scalar(coeff)) for power, coeff in value.items() if coeff
                )
            )
        else:
            coeff = Scalar(value)
            cleaned = () if coeff == 0 else (((0,) * EXPONENTS, coeff),)
        object.__setattr__(self, "terms", cleaned)

    @staticmethod
    def variable(index: int) -> "Polynomial":
        powers = [0] * EXPONENTS
        powers[index] = 1
        return Polynomial({tuple(powers): Scalar(1)})

    @staticmethod
    def coerce(value: int | Scalar | "Polynomial") -> "Polynomial":
        return value if isinstance(value, Polynomial) else Polynomial(value)

    def as_dict(self) -> dict[tuple[int, ...], Scalar]:
        return dict(self.terms)

    def __add__(self, other: int | Scalar | "Polynomial") -> "Polynomial":
        output = self.as_dict()
        for power, coeff in Polynomial.coerce(other).terms:
            output[power] = output.get(power, Scalar(0)) + coeff
        return Polynomial(output)

    __radd__ = __add__

    def __neg__(self) -> "Polynomial":
        return Polynomial({power: -coeff for power, coeff in self.terms})

    def __sub__(self, other: int | Scalar | "Polynomial") -> "Polynomial":
        return self + (-Polynomial.coerce(other))

    def __rsub__(self, other: int | Scalar | "Polynomial") -> "Polynomial":
        return Polynomial.coerce(other) - self

    def __mul__(self, other: int | Scalar | "Polynomial") -> "Polynomial":
        rhs = Polynomial.coerce(other)
        output: dict[tuple[int, ...], Scalar] = {}
        for left_power, left_coeff in self.terms:
            for right_power, right_coeff in rhs.terms:
                power = tuple(
                    a + b for a, b in zip(left_power, right_power, strict=True)
                )
                output[power] = output.get(power, Scalar(0)) + left_coeff * right_coeff
        return Polynomial(output)

    __rmul__ = __mul__

    def __pow__(self, exponent: int) -> "Polynomial":
        assert exponent >= 0
        output = Polynomial(1)
        base = self
        remaining = exponent
        while remaining:
            if remaining & 1:
                output *= base
            base *= base
            remaining >>= 1
        return output


PolyMatrix = tuple[tuple[Polynomial, ...], ...]


def matrix_unit(row: int, column: int) -> NumericMatrix:
    return tuple(
        tuple(Scalar(1) if (i, j) == (row, column) else Scalar(0) for j in range(3))
        for i in range(3)
    )


def numeric_add(left: NumericMatrix, right: NumericMatrix) -> NumericMatrix:
    return tuple(
        tuple(a + b for a, b in zip(left_row, right_row, strict=True))
        for left_row, right_row in zip(left, right, strict=True)
    )


def numeric_scale(value: Scalar, matrix: NumericMatrix) -> NumericMatrix:
    return tuple(tuple(value * entry for entry in row) for row in matrix)


def numeric_multiply(left: NumericMatrix, right: NumericMatrix) -> NumericMatrix:
    return tuple(
        tuple(
            sum((left[i][k] * right[k][j] for k in range(3)), Scalar(0))
            for j in range(3)
        )
        for i in range(3)
    )


def commutator(left: NumericMatrix, right: NumericMatrix) -> NumericMatrix:
    return numeric_add(
        numeric_multiply(left, right),
        numeric_scale(Scalar(-1), numeric_multiply(right, left)),
    )


def trace(matrix: NumericMatrix) -> Scalar:
    return sum((matrix[i][i] for i in range(3)), Scalar(0))


def flatten(matrix: NumericMatrix) -> list[Scalar]:
    return [entry for row in matrix for entry in row]


def rank(rows: Iterable[Iterable[Scalar]]) -> int:
    matrix = [list(row) for row in rows]
    if not matrix:
        return 0
    row_count = len(matrix)
    column_count = len(matrix[0])
    pivot_row = 0
    for column in range(column_count):
        pivot = next(
            (i for i in range(pivot_row, row_count) if matrix[i][column]), None
        )
        if pivot is None:
            continue
        matrix[pivot_row], matrix[pivot] = matrix[pivot], matrix[pivot_row]
        pivot_value = matrix[pivot_row][column]
        matrix[pivot_row] = [entry / pivot_value for entry in matrix[pivot_row]]
        for i in range(row_count):
            if i == pivot_row or matrix[i][column] == 0:
                continue
            factor = matrix[i][column]
            matrix[i] = [
                a - factor * b
                for a, b in zip(matrix[i], matrix[pivot_row], strict=True)
            ]
        pivot_row += 1
        if pivot_row == row_count:
            break
    return pivot_row


def columns_rank(columns: list[list[Scalar]]) -> int:
    rows = zip(*columns, strict=True)
    return rank(rows)


def matrices_rank(matrices: Iterable[NumericMatrix]) -> int:
    return columns_rank([flatten(matrix) for matrix in matrices])


def sl3_basis() -> list[NumericMatrix]:
    h1 = (
        (Scalar(1), Scalar(0), Scalar(0)),
        (Scalar(0), Scalar(-1), Scalar(0)),
        (Scalar(0), Scalar(0), Scalar(0)),
    )
    h2 = (
        (Scalar(0), Scalar(0), Scalar(0)),
        (Scalar(0), Scalar(1), Scalar(0)),
        (Scalar(0), Scalar(0), Scalar(-1)),
    )
    return [h1, h2, *(matrix_unit(i, j) for i in range(3) for j in range(3) if i != j)]


def centralizer_dimension(element: NumericMatrix) -> int:
    columns = [flatten(commutator(basis, element)) for basis in sl3_basis()]
    return 8 - columns_rank(columns)


def normalizer_dimension(element: NumericMatrix) -> int:
    columns = [flatten(commutator(basis, element)) for basis in sl3_basis()]
    columns.append(flatten(numeric_scale(Scalar(-1), element)))
    return 9 - columns_rank(columns)


def kirillov_rank(element: NumericMatrix) -> int:
    basis = sl3_basis()
    form = [
        [trace(numeric_multiply(element, commutator(left, right))) for right in basis]
        for left in basis
    ]
    return rank(form)


def poly_matrix(values: list[list[int | Scalar | Polynomial]]) -> PolyMatrix:
    return tuple(tuple(Polynomial.coerce(value) for value in row) for row in values)


def poly_add(left: PolyMatrix, right: PolyMatrix) -> PolyMatrix:
    return tuple(
        tuple(a + b for a, b in zip(left_row, right_row, strict=True))
        for left_row, right_row in zip(left, right, strict=True)
    )


def poly_scale(value: int | Scalar | Polynomial, matrix: PolyMatrix) -> PolyMatrix:
    factor = Polynomial.coerce(value)
    return tuple(tuple(factor * entry for entry in row) for row in matrix)


def poly_multiply(left: PolyMatrix, right: PolyMatrix) -> PolyMatrix:
    size = len(left)
    return tuple(
        tuple(
            sum((left[i][k] * right[k][j] for k in range(size)), Polynomial(0))
            for j in range(size)
        )
        for i in range(size)
    )


def poly_identity(size: int) -> PolyMatrix:
    return tuple(
        tuple(Polynomial(1 if i == j else 0) for j in range(size)) for i in range(size)
    )


def poly_trace(matrix: PolyMatrix) -> Polynomial:
    return sum((matrix[i][i] for i in range(len(matrix))), Polynomial(0))


def determinant3(matrix: PolyMatrix) -> Polynomial:
    a, b, c = matrix[0]
    d, e, f = matrix[1]
    g, h, i = matrix[2]
    return a * (e * i - f * h) - b * (d * i - f * g) + c * (d * h - e * g)


def determinant(matrix: NumericMatrix | PolyMatrix) -> Scalar | Polynomial:
    size = len(matrix)
    assert all(len(row) == size for row in matrix)
    result: Scalar | Polynomial = Scalar(0)
    for permutation in permutations(range(size)):
        inversions = sum(
            permutation[i] > permutation[j]
            for i in range(size)
            for j in range(i + 1, size)
        )
        term: Scalar | Polynomial = Scalar(-1 if inversions % 2 else 1)
        for row, column in enumerate(permutation):
            term *= matrix[row][column]
        result += term
    return result


def pfaffian4(matrix: NumericMatrix | PolyMatrix) -> Scalar | Polynomial:
    assert len(matrix) == 4 and all(len(row) == 4 for row in matrix)
    return (
        matrix[0][1] * matrix[2][3]
        - matrix[0][2] * matrix[1][3]
        + matrix[0][3] * matrix[1][2]
    )


def zero_poly_matrix(size: int) -> PolyMatrix:
    return poly_matrix([[0] * size for _ in range(size)])


def kirillov_matrix(
    element: NumericMatrix, quotient_basis: list[NumericMatrix]
) -> NumericMatrix:
    return tuple(
        tuple(
            trace(numeric_multiply(element, commutator(left, right)))
            for right in quotient_basis
        )
        for left in quotient_basis
    )


def trace_gram_matrix(basis: list[NumericMatrix]) -> NumericMatrix:
    return tuple(
        tuple(trace(numeric_multiply(left, right)) for right in basis) for left in basis
    )


def verify_orbits() -> None:
    e12 = matrix_unit(0, 1)
    representatives = {
        "regular semisimple": (
            (Scalar(1), Scalar(0), Scalar(0)),
            (Scalar(0), Scalar(0), Scalar(0)),
            (Scalar(0), Scalar(0), Scalar(-1)),
        ),
        "mixed regular": (
            (Scalar(1), Scalar(1), Scalar(0)),
            (Scalar(0), Scalar(1), Scalar(0)),
            (Scalar(0), Scalar(0), Scalar(-2)),
        ),
        "regular nilpotent": numeric_add(e12, matrix_unit(1, 2)),
        "semisimple (2,1)": (
            (Scalar(1), Scalar(0), Scalar(0)),
            (Scalar(0), Scalar(1), Scalar(0)),
            (Scalar(0), Scalar(0), Scalar(-2)),
        ),
        "minimal nilpotent": e12,
    }
    expected = {
        "regular semisimple": (2, 2, 1),
        "mixed regular": (2, 2, 1),
        "regular nilpotent": (2, 3, 2),
        "semisimple (2,1)": (4, 4, 3),
        "minimal nilpotent": (4, 5, 4),
    }
    for name, element in representatives.items():
        result = (
            centralizer_dimension(element),
            normalizer_dimension(element),
            normalizer_dimension(element) - 1,
        )
        assert result == expected[name], (name, result, expected[name])
    assert kirillov_rank(representatives["semisimple (2,1)"]) == 4
    assert kirillov_rank(representatives["minimal nilpotent"]) == 4


def verify_minimal_centralizer() -> None:
    m = matrix_unit(0, 1)
    p = matrix_unit(0, 2)
    q = matrix_unit(2, 1)
    h = (
        (Scalar(1, 2), Scalar(0), Scalar(0)),
        (Scalar(0), Scalar(1, 2), Scalar(0)),
        (Scalar(0), Scalar(0), Scalar(-1)),
    )
    centralizer_basis = [m, p, q, h]
    zero = numeric_scale(Scalar(0), m)

    # These four independent elements exhaust the centralizer. Consequently,
    # X_0 + <m,p,q,h> is the full affine solution of [X,m]=m.
    assert matrices_rank(centralizer_basis) == 4
    assert centralizer_dimension(m) == 4
    assert normalizer_dimension(m) == 5
    assert all(commutator(element, m) == zero for element in centralizer_basis)
    x0 = (
        (Scalar(1, 2), Scalar(0), Scalar(0)),
        (Scalar(0), Scalar(-1, 2), Scalar(0)),
        (Scalar(0), Scalar(0), Scalar(0)),
    )
    assert commutator(x0, m) == m

    # Modulo <m>, the derived algebra is exactly <p,q>.
    assert commutator(p, q) == m
    assert commutator(h, p) == numeric_scale(Scalar(3, 2), p)
    assert commutator(h, q) == numeric_scale(Scalar(-3, 2), q)
    derived_brackets = [
        commutator(left, right) for left in (p, q, h) for right in (p, q, h)
    ]
    assert matrices_rank([m, *derived_brackets]) == 3
    assert matrices_rank([m, p, q]) == 3

    # The trace form descends through <m>; on C_0=<p,q,h> its radical is
    # precisely the derived rank-two subspace <p,q>, and the quotient value
    # tr(h^2)=3/2 is a unit.
    assert all(
        trace(numeric_multiply(m, element)) == 0 for element in centralizer_basis
    )
    gram = trace_gram_matrix([p, q, h])
    expected_gram = (
        (Scalar(0), Scalar(0), Scalar(0)),
        (Scalar(0), Scalar(0), Scalar(0)),
        (Scalar(0), Scalar(0), Scalar(3, 2)),
    )
    assert gram == expected_gram
    assert rank(gram) == 1


def verify_boundary_cocycle_normalizers() -> None:
    """Check both generic orbit algebras in the boundary-cocycle lemma."""

    zero = numeric_scale(Scalar(0), matrix_unit(0, 1))
    e12 = matrix_unit(0, 1)
    e21 = matrix_unit(1, 0)
    d = (
        (Scalar(1, 2), Scalar(0), Scalar(0)),
        (Scalar(0), Scalar(-1, 2), Scalar(0)),
        (Scalar(0), Scalar(0), Scalar(0)),
    )
    semisimple = (
        (Scalar(1), Scalar(0), Scalar(0)),
        (Scalar(0), Scalar(1), Scalar(0)),
        (Scalar(0), Scalar(0), Scalar(-2)),
    )

    # The semisimple quotient normalizer is a nonabelian sl2 and its grading
    # character is zero, contradicting the boundary law on a 3-space.
    assert commutator(e12, semisimple) == zero
    assert commutator(e21, semisimple) == zero
    assert commutator(d, semisimple) == zero
    assert commutator(e12, e21) == numeric_scale(Scalar(2), d)
    assert commutator(d, e12) == e12

    # For the minimal quotient, lambda(d)=1.  If a grading-one element is
    # d+c h+a p+b q, its eigenvalues on the unique 2-dimensional abelian
    # subalgebra <p,q> are (1+3c)/2 and (1-3c)/2.  Their sum is always one,
    # so the boundary law cannot make both eigenvalues one.
    h = (
        (Scalar(1, 2), Scalar(0), Scalar(0)),
        (Scalar(0), Scalar(1, 2), Scalar(0)),
        (Scalar(0), Scalar(0), Scalar(-1)),
    )
    p = matrix_unit(0, 2)
    q = matrix_unit(2, 1)
    minimal = e12
    assert commutator(d, minimal) == minimal
    assert commutator(h, minimal) == zero
    assert commutator(d, p) == numeric_scale(Scalar(1, 2), p)
    assert commutator(d, q) == numeric_scale(Scalar(1, 2), q)
    assert commutator(h, p) == numeric_scale(Scalar(3, 2), p)
    assert commutator(h, q) == numeric_scale(Scalar(-3, 2), q)
    assert commutator(p, q) == minimal  # Zero modulo the Hodge line.

    # In C_0=<h,p,q>, the quotient bracket of a plane has coefficients
    # (3/2)(h wedge p) along p and -(3/2)(h wedge q) along q.  Hence an
    # abelian 2-plane has both of those Pluecker coordinates zero; its only
    # nonzero coordinate is p wedge q, so the plane is uniquely <p,q>.
    assert matrices_rank([h, p, q]) == 3
    assert matrices_rank([p, q]) == 2
    c = Polynomial.variable(0)
    first = Scalar(1, 2) * (1 + 3 * c)
    second = Scalar(1, 2) * (1 - 3 * c)
    assert first + second == Polynomial(1)


def verify_pfaffian_determinant() -> None:
    # First verify the universal 4-by-4 alternating identity symbolically.
    x01, x02, x03, x12, x13, x23 = (Polynomial.variable(i) for i in range(EXPONENTS))
    generic_form = poly_matrix(
        [
            [0, x01, x02, x03],
            [-x01, 0, x12, x13],
            [-x02, -x12, 0, x23],
            [-x03, -x13, -x23, 0],
        ]
    )
    generic_pfaffian = x01 * x23 - x02 * x13 + x03 * x12
    assert pfaffian4(generic_form) == generic_pfaffian
    assert determinant(generic_form) == generic_pfaffian**2

    # Then check that the quotient Kirillov forms for both remaining orbit
    # types are nondegenerate and obey the same determinant-square identity.
    m = matrix_unit(0, 1)
    minimal_quotient_basis = [
        matrix_unit(1, 0),
        matrix_unit(1, 2),
        matrix_unit(2, 0),
        (
            (Scalar(1), Scalar(0), Scalar(0)),
            (Scalar(0), Scalar(-1), Scalar(0)),
            (Scalar(0), Scalar(0), Scalar(0)),
        ),
    ]
    semisimple = (
        (Scalar(1), Scalar(0), Scalar(0)),
        (Scalar(0), Scalar(1), Scalar(0)),
        (Scalar(0), Scalar(0), Scalar(-2)),
    )
    semisimple_quotient_basis = [
        matrix_unit(0, 2),
        matrix_unit(2, 0),
        matrix_unit(1, 2),
        matrix_unit(2, 1),
    ]
    for element, quotient_basis in (
        (m, minimal_quotient_basis),
        (semisimple, semisimple_quotient_basis),
    ):
        form = kirillov_matrix(element, quotient_basis)
        assert all(form[i][j] == -form[j][i] for i in range(4) for j in range(4))
        assert rank(form) == 4
        pfaffian = pfaffian4(form)
        assert pfaffian != 0
        assert determinant(form) == pfaffian * pfaffian


def verify_spectral_projector() -> None:
    d, a, b, c, f, variable = (Polynomial.variable(i) for i in range(EXPONENTS))
    half = Scalar(1, 2)
    identity = poly_identity(3)
    m = poly_matrix([[0, 1, 0], [0, 0, 0], [0, 0, 0]])
    x = poly_matrix(
        [
            [half * (1 + d), a, b],
            [0, half * (-1 + d), 0],
            [0, c, -d],
        ]
    )
    alpha = half * (d + 1)
    beta = half * (d - 1)
    gamma = -d

    assert poly_add(poly_multiply(x, m), poly_scale(-1, poly_multiply(m, x))) == m

    characteristic = determinant3(
        poly_add(poly_scale(variable, identity), poly_scale(-1, x))
    )
    expected_characteristic = (
        (variable - alpha) * (variable - beta) * (variable - gamma)
    )
    assert characteristic == expected_characteristic

    discriminant = (alpha - beta) ** 2 * (alpha - gamma) ** 2 * (beta - gamma) ** 2
    expected_discriminant = Scalar(1, 16) * (3 * d - 1) ** 2 * (3 * d + 1) ** 2
    assert discriminant == expected_discriminant

    numerator = poly_multiply(
        poly_add(x, poly_scale(-alpha, identity)),
        poly_add(x, poly_scale(-beta, identity)),
    )
    denominator = (gamma - alpha) * (gamma - beta)
    assert poly_multiply(numerator, numerator) == poly_scale(denominator, numerator)
    assert poly_trace(numerator) == denominator
    assert poly_multiply(numerator, m) == zero_poly_matrix(3)
    assert poly_multiply(m, numerator) == zero_poly_matrix(3)

    shifted = poly_add(x, poly_scale(f, m))
    shifted_numerator = poly_multiply(
        poly_add(shifted, poly_scale(-alpha, identity)),
        poly_add(shifted, poly_scale(-beta, identity)),
    )
    assert shifted_numerator == numerator

    # At D=0 the eigenvalues 1/2, -1/2, 0 are distinct and the first two
    # form the unique ordered pair differing by one.
    assert alpha - beta == Polynomial(1)
    eigenvalues_at_zero = (Scalar(1, 2), Scalar(-1, 2), Scalar(0))
    unit_differences = [
        (i, j)
        for i, left in enumerate(eigenvalues_at_zero)
        for j, right in enumerate(eigenvalues_at_zero)
        if left - right == 1
    ]
    assert unit_differences == [(0, 1)]

    # Derive every bad D exactly from the three affine eigenvalue functions.
    # An affine function is represented by (slope, intercept).
    affine_eigenvalues = (
        (Scalar(1, 2), Scalar(1, 2)),
        (Scalar(1, 2), Scalar(-1, 2)),
        (Scalar(-1), Scalar(0)),
    )

    def solve_difference(i: int, j: int, target: Scalar) -> Scalar | None:
        left_slope, left_intercept = affine_eigenvalues[i]
        right_slope, right_intercept = affine_eigenvalues[j]
        slope = left_slope - right_slope
        intercept = left_intercept - right_intercept
        if slope == 0:
            assert intercept != target
            return None
        return (target - intercept) / slope

    repeated_root_values = {
        value
        for i in range(3)
        for j in range(i + 1, 3)
        if (value := solve_difference(i, j, Scalar(0))) is not None
    }
    unwanted_unit_difference_values = {
        value
        for i in range(3)
        for j in range(3)
        if i != j and (i, j) != (0, 1)
        if (value := solve_difference(i, j, Scalar(1))) is not None
    }
    assert repeated_root_values == {Scalar(-1, 3), Scalar(1, 3)}
    assert unwanted_unit_difference_values == {
        Scalar(-1),
        Scalar(-1, 3),
        Scalar(1, 3),
        Scalar(1),
    }
    assert repeated_root_values | unwanted_unit_difference_values == {
        Scalar(-1),
        Scalar(-1, 3),
        Scalar(1, 3),
        Scalar(1),
    }


def effective_twist_degrees(
    base_degree: int,
    *,
    total_lower: int | None = None,
    total_upper: int,
) -> tuple[int, ...]:
    """Solve exact integer degree bounds for an effective divisor twist."""

    twist_lower = 0
    if total_lower is not None:
        twist_lower = max(twist_lower, total_lower - base_degree)
    twist_upper = total_upper - base_degree
    if twist_upper < twist_lower:
        return ()
    return tuple(range(twist_lower, twist_upper + 1))


def verify_degree_cases() -> None:
    degree_m = -1

    # In the semisimple case, det K=M(T). The full-rank O^3 inclusion gives
    # deg K>=0, while stability gives deg K<=0.
    semisimple = effective_twist_degrees(degree_m, total_lower=0, total_upper=0)
    assert semisimple == (1,)

    # If lambda vanishes on O^3, the same bounds apply to
    # det(Z/M)=M(T).
    lambda_zero = effective_twist_degrees(degree_m, total_lower=0, total_upper=0)
    assert lambda_zero == (1,)

    # If lambda is nonzero on O^3, projectivity forces Z_lambda=0. Now
    # det K=M(T-Z_lambda), and the nonzero morphism det K -> M gives
    # deg det K<=deg M. Effectivity of T therefore derives T=0.
    z_lambda_degrees = (0,)
    residual = tuple(
        (t_degree, z_degree)
        for z_degree in z_lambda_degrees
        for t_degree in effective_twist_degrees(
            degree_m - z_degree,
            total_upper=degree_m,
        )
    )
    assert residual == ((0, 0),)


def main() -> None:
    verify_orbits()
    verify_minimal_centralizer()
    verify_boundary_cocycle_normalizers()
    verify_pfaffian_determinant()
    verify_spectral_projector()
    verify_degree_cases()
    print("Q9 orbit dimensions and Kirillov ranks: PASS")
    print("Q9 full affine normalizer and centralizer quotient: PASS")
    print("Q9 boundary-cocycle normalizer obstruction: PASS")
    print("Q9 Pfaffian-square determinant identities: PASS")
    print("Q9 spectral polynomial, exact bad set, and projector: PASS")
    print("Q9 divisor-degree cases: PASS")
    print("Q9 FINITE CHECKS: PASS")


if __name__ == "__main__":
    main()
