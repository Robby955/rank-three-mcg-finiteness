#!/usr/bin/env python3
"""Exact local-algebra checks for the genus-five q=10 jet obstruction.

The calculation runs over Q[a_1,...,a_8][z]/(z^2). It reconstructs the
bracket from standard sl_3 matrices, forms the quotient by a moving line, and
only then extracts the maps on ker(B_0) and coker(B_0). The displayed matrices
are therefore checked as outputs of the quotient calculation.

This certifies finite local linear algebra only, not the global section,
saturation, or parabolic-stability reductions in the manuscript.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from itertools import permutations
from typing import Iterable, Sequence

VARIABLE_COUNT = 8
Scalar = Fraction


@dataclass(frozen=True)
class Affine:
    """An affine polynomial in the eight first-order coefficients."""

    constant: Scalar
    coefficients: tuple[Scalar, ...]

    def __init__(
        self,
        constant: int | Scalar = 0,
        coefficients: Sequence[int | Scalar] | None = None,
    ) -> None:
        values = coefficients if coefficients is not None else (0,) * VARIABLE_COUNT
        assert len(values) == VARIABLE_COUNT
        object.__setattr__(self, "constant", Scalar(constant))
        object.__setattr__(
            self, "coefficients", tuple(Scalar(value) for value in values)
        )

    @staticmethod
    def variable(index: int) -> "Affine":
        coefficients = [Scalar(0)] * VARIABLE_COUNT
        coefficients[index] = Scalar(1)
        return Affine(0, coefficients)

    @staticmethod
    def coerce(value: int | Scalar | "Affine") -> "Affine":
        return value if isinstance(value, Affine) else Affine(value)

    def __add__(self, other: int | Scalar | "Affine") -> "Affine":
        right = Affine.coerce(other)
        return Affine(
            self.constant + right.constant,
            tuple(
                left + right_value
                for left, right_value in zip(
                    self.coefficients, right.coefficients, strict=True
                )
            ),
        )

    __radd__ = __add__

    def __neg__(self) -> "Affine":
        return Affine(-self.constant, tuple(-value for value in self.coefficients))

    def __sub__(self, other: int | Scalar | "Affine") -> "Affine":
        return self + (-Affine.coerce(other))

    def __rsub__(self, other: int | Scalar | "Affine") -> "Affine":
        return Affine.coerce(other) - self

    def __mul__(self, other: int | Scalar | "Affine") -> "Affine":
        right = Affine.coerce(other)
        left_is_scalar = not any(self.coefficients)
        right_is_scalar = not any(right.coefficients)
        assert left_is_scalar or right_is_scalar, "quadratic term is not needed here"
        if left_is_scalar:
            return Affine(
                self.constant * right.constant,
                tuple(self.constant * value for value in right.coefficients),
            )
        return Affine(
            self.constant * right.constant,
            tuple(right.constant * value for value in self.coefficients),
        )

    __rmul__ = __mul__

    def scalar(self) -> Scalar:
        assert not any(self.coefficients)
        return self.constant


@dataclass(frozen=True)
class Dual:
    """An affine-valued dual number constant + z * linear."""

    constant: Scalar
    linear: Affine

    def __init__(
        self,
        constant: int | Scalar = 0,
        linear: int | Scalar | Affine = 0,
    ) -> None:
        object.__setattr__(self, "constant", Scalar(constant))
        object.__setattr__(self, "linear", Affine.coerce(linear))

    @staticmethod
    def coerce(value: int | Scalar | "Dual") -> "Dual":
        return value if isinstance(value, Dual) else Dual(value)

    def __add__(self, other: int | Scalar | "Dual") -> "Dual":
        right = Dual.coerce(other)
        return Dual(self.constant + right.constant, self.linear + right.linear)

    __radd__ = __add__

    def __neg__(self) -> "Dual":
        return Dual(-self.constant, -self.linear)

    def __sub__(self, other: int | Scalar | "Dual") -> "Dual":
        return self + (-Dual.coerce(other))

    def __rsub__(self, other: int | Scalar | "Dual") -> "Dual":
        return Dual.coerce(other) - self

    def __mul__(self, other: int | Scalar | "Dual") -> "Dual":
        right = Dual.coerce(other)
        return Dual(
            self.constant * right.constant,
            self.constant * right.linear + right.constant * self.linear,
        )

    __rmul__ = __mul__

    def inverse(self) -> "Dual":
        assert self.constant != 0
        return Dual(
            1 / self.constant,
            (-1 / (self.constant * self.constant)) * self.linear,
        )


NumericMatrix = list[list[Scalar]]
AffineMatrix = list[list[Affine]]
Matrix3 = tuple[tuple[Scalar, ...], ...]


def matrix_unit(row: int, column: int) -> Matrix3:
    return tuple(
        tuple(Scalar(1) if (i, j) == (row, column) else Scalar(0) for j in range(3))
        for i in range(3)
    )


def matrix3_add(left: Matrix3, right: Matrix3) -> Matrix3:
    return tuple(
        tuple(a + b for a, b in zip(left_row, right_row, strict=True))
        for left_row, right_row in zip(left, right, strict=True)
    )


def matrix3_scale(value: Scalar, matrix: Matrix3) -> Matrix3:
    return tuple(tuple(value * entry for entry in row) for row in matrix)


def matrix3_multiply(left: Matrix3, right: Matrix3) -> Matrix3:
    return tuple(
        tuple(
            sum((left[i][k] * right[k][j] for k in range(3)), Scalar(0))
            for j in range(3)
        )
        for i in range(3)
    )


def commutator(left: Matrix3, right: Matrix3) -> Matrix3:
    return matrix3_add(
        matrix3_multiply(left, right),
        matrix3_scale(Scalar(-1), matrix3_multiply(right, left)),
    )


H1 = matrix3_add(matrix_unit(0, 0), matrix3_scale(Scalar(-1), matrix_unit(1, 1)))
H2 = matrix3_add(matrix_unit(1, 1), matrix3_scale(Scalar(-1), matrix_unit(2, 2)))
ORDINARY_BASIS = [
    H1,
    H2,
    matrix_unit(0, 1),
    matrix_unit(1, 0),
    matrix_unit(0, 2),
    matrix_unit(1, 2),
    matrix_unit(2, 0),
    matrix_unit(2, 1),
]
BASIS_NAMES = ("H1", "H2", "E12", "E21", "zE13", "zE23", "E31", "E32")
UPPER_RADICAL = frozenset((4, 5))
LOWER_RADICAL = frozenset((6, 7))


def sl3_coordinates(matrix: Matrix3) -> tuple[Scalar, ...]:
    assert sum((matrix[i][i] for i in range(3)), Scalar(0)) == 0
    return (
        matrix[0][0],
        -matrix[2][2],
        matrix[0][1],
        matrix[1][0],
        matrix[0][2],
        matrix[1][2],
        matrix[2][0],
        matrix[2][1],
    )


def ordinary_bracket(left: int, right: int) -> tuple[Scalar, ...]:
    return sl3_coordinates(commutator(ORDINARY_BASIS[left], ORDINARY_BASIS[right]))


def lattice_bracket(left: int, right: int) -> tuple[Dual, ...]:
    """Bracket in (H1,H2,E12,E21,zE13,zE23,E31,E32)."""

    has_z = (left in UPPER_RADICAL and right in LOWER_RADICAL) or (
        left in LOWER_RADICAL and right in UPPER_RADICAL
    )
    return tuple(
        Dual(0, value) if has_z else Dual(value)
        for value in ordinary_bracket(left, right)
    )


def add_scaled_dual_vector(
    output: list[Dual], scalar: Dual, vector: Sequence[Dual]
) -> None:
    for index, value in enumerate(vector):
        output[index] = output[index] + scalar * value


def reduce_modulo_line(
    vector: Sequence[Dual], line: Sequence[Dual], drop_index: int
) -> list[Dual]:
    inverse = line[drop_index].inverse()
    dropped = vector[drop_index]
    return [
        vector[index] - dropped * line[index] * inverse
        for index in range(8)
        if index != drop_index
    ]


def quotient_series(
    constant_line: Sequence[int], drop_index: int
) -> tuple[list[int], NumericMatrix, AffineMatrix]:
    """Construct B_0 and B_1 on the seven-dimensional moving quotient."""

    variables = [Affine.variable(index) for index in range(VARIABLE_COUNT)]
    line = [
        Dual(constant, variable)
        for constant, variable in zip(constant_line, variables, strict=True)
    ]
    complement = [index for index in range(8) if index != drop_index]
    columns: list[list[Dual]] = []
    for basis_index in complement:
        bracket = [Dual() for _ in range(8)]
        for line_index, coefficient in enumerate(line):
            add_scaled_dual_vector(
                bracket, coefficient, lattice_bracket(line_index, basis_index)
            )
        columns.append(reduce_modulo_line(bracket, line, drop_index))

    constant_matrix = [
        [columns[column][row].constant for column in range(7)] for row in range(7)
    ]
    linear_matrix = [
        [columns[column][row].linear for column in range(7)] for row in range(7)
    ]
    return complement, constant_matrix, linear_matrix


def numeric_rank(rows: Iterable[Iterable[Scalar]]) -> int:
    matrix = [list(row) for row in rows]
    if not matrix:
        return 0
    row_count = len(matrix)
    column_count = len(matrix[0])
    pivot_row = 0
    for column in range(column_count):
        pivot = next(
            (row for row in range(pivot_row, row_count) if matrix[row][column]),
            None,
        )
        if pivot is None:
            continue
        matrix[pivot_row], matrix[pivot] = matrix[pivot], matrix[pivot_row]
        pivot_value = matrix[pivot_row][column]
        matrix[pivot_row] = [value / pivot_value for value in matrix[pivot_row]]
        for row in range(row_count):
            if row == pivot_row or matrix[row][column] == 0:
                continue
            factor = matrix[row][column]
            matrix[row] = [
                value - factor * pivot_value
                for value, pivot_value in zip(
                    matrix[row], matrix[pivot_row], strict=True
                )
            ]
        pivot_row += 1
        if pivot_row == row_count:
            break
    return pivot_row


def numeric_multiply(left: NumericMatrix, right: NumericMatrix) -> NumericMatrix:
    inner = len(right)
    assert len(left[0]) == inner
    return [
        [
            sum(
                (left[i][k] * right[k][j] for k in range(inner)),
                Scalar(0),
            )
            for j in range(len(right[0]))
        ]
        for i in range(len(left))
    ]


def affine_multiply(
    left: Sequence[Sequence[int | Scalar | Affine]],
    right: Sequence[Sequence[int | Scalar | Affine]],
) -> AffineMatrix:
    inner = len(right)
    assert len(left[0]) == inner
    return [
        [
            sum(
                (
                    Affine.coerce(left[i][k]) * Affine.coerce(right[k][j])
                    for k in range(inner)
                ),
                Affine(),
            )
            for j in range(len(right[0]))
        ]
        for i in range(len(left))
    ]


def affine_add(left: AffineMatrix, right: AffineMatrix) -> AffineMatrix:
    return [
        [a + b for a, b in zip(left_row, right_row, strict=True)]
        for left_row, right_row in zip(left, right, strict=True)
    ]


def affine_scale(value: Scalar, matrix: AffineMatrix) -> AffineMatrix:
    return [[value * entry for entry in row] for row in matrix]


def numeric_as_affine(matrix: NumericMatrix) -> AffineMatrix:
    return [[Affine(entry) for entry in row] for row in matrix]


def as_affine_matrix(
    matrix: Sequence[Sequence[int | Scalar | Affine]],
) -> AffineMatrix:
    return [[Affine.coerce(entry) for entry in row] for row in matrix]


def basis_columns(dimension: int, indices: Sequence[int]) -> NumericMatrix:
    return [
        [Scalar(1) if row == index else Scalar(0) for index in indices]
        for row in range(dimension)
    ]


def basis_rows(dimension: int, indices: Sequence[int]) -> NumericMatrix:
    return [
        [Scalar(1) if column == index else Scalar(0) for column in range(dimension)]
        for index in indices
    ]


def numeric_determinant(matrix: NumericMatrix) -> Scalar:
    size = len(matrix)
    assert all(len(row) == size for row in matrix)
    output = Scalar(0)
    for permutation in permutations(range(size)):
        inversions = sum(
            1
            for i in range(size)
            for j in range(i + 1, size)
            if permutation[i] > permutation[j]
        )
        term = Scalar(-1 if inversions % 2 else 1)
        for row, column in enumerate(permutation):
            term *= matrix[row][column]
        output += term
    return output


def constant_minor(
    matrix: AffineMatrix, rows: Sequence[int], columns: Sequence[int]
) -> Scalar:
    numeric = [[matrix[row][column].scalar() for column in columns] for row in rows]
    return numeric_determinant(numeric)


def zero_numeric(rows: int, columns: int) -> NumericMatrix:
    return [[Scalar(0) for _ in range(columns)] for _ in range(rows)]


def projected_map(
    cokernel: NumericMatrix,
    first_order: AffineMatrix,
    kernel: NumericMatrix,
) -> AffineMatrix:
    return affine_multiply(affine_multiply(cokernel, first_order), kernel)


def verify_frame_and_rescaling_invariance(
    constant: NumericMatrix,
    first_order: AffineMatrix,
    kernel: NumericMatrix,
    cokernel: NumericMatrix,
) -> None:
    """Check B1 -> B1+B0 U-V B0 and B1 -> B1+c B0 exactly."""

    size = len(constant)
    base = projected_map(cokernel, first_order, kernel)
    assert numeric_multiply(constant, kernel) == zero_numeric(size, len(kernel[0]))
    assert numeric_multiply(cokernel, constant) == zero_numeric(len(cokernel), size)

    # Matrix units span all moving source and target frame corrections.
    for row in range(size):
        for column in range(size):
            elementary = zero_numeric(size, size)
            elementary[row][column] = Scalar(1)

            source_change = numeric_multiply(constant, elementary)
            changed = affine_add(first_order, numeric_as_affine(source_change))
            assert projected_map(cokernel, changed, kernel) == base

            target_change = numeric_multiply(elementary, constant)
            changed = affine_add(
                first_order,
                affine_scale(Scalar(-1), numeric_as_affine(target_change)),
            )
            assert projected_map(cokernel, changed, kernel) == base

    # Line rescaling contributes a scalar multiple of B0; one generator checks
    # the identity because the correction is linear in that scalar.
    rescaled = affine_add(first_order, numeric_as_affine(constant))
    assert projected_map(cokernel, rescaled, kernel) == base


def expected_pure_map() -> AffineMatrix:
    a = [Affine.variable(index) for index in range(VARIABLE_COUNT)]
    return as_affine_matrix(
        [
            [a[0], a[0], -a[3], 0, 1, 0],
            [a[1], a[1], 0, 0, 1, 0],
            [-a[2], 2 * a[2], 2 * a[0] - a[1], 0, 0, 1],
            [3 * a[3], 0, 0, 0, 0, 0],
            [2 * a[6], 2 * a[6], 0, 0, -a[0] - a[1], -a[3]],
            [0, 3 * a[7], a[6], 0, -a[2], a[0] - 2 * a[1]],
        ]
    )


def expected_mixed_map() -> AffineMatrix:
    a = [Affine.variable(index) for index in range(VARIABLE_COUNT)]
    return as_affine_matrix(
        [
            [a[0], -a[3], 0, 1, 0],
            [a[1], 0, -1, 1, 0],
            [-a[2], 2 * a[0] - a[1], 0, 0, 1],
            [3 * a[3], 0, 0, 0, 0],
            [
                2 * a[5] + 2 * a[6],
                0,
                -a[0] + 2 * a[1],
                -a[0] - a[1],
                -a[3],
            ],
        ]
    )


def verify_integral_involution() -> None:
    """Verify X -> -D X^t D^-1 on the full parahoric bracket table."""

    # For D=diag(z,z,1), this signed permutation is integral and exchanges
    # zE13 with -E31 and zE23 with -E32.
    image = (
        (0, -1),
        (1, -1),
        (3, -1),
        (2, -1),
        (6, -1),
        (7, -1),
        (4, -1),
        (5, -1),
    )

    for index, (target, sign) in enumerate(image):
        second_target, second_sign = image[target]
        assert second_target == index
        assert sign * second_sign == 1

    def transform(vector: Sequence[Dual]) -> tuple[Dual, ...]:
        output = [Dual() for _ in range(8)]
        for source, coefficient in enumerate(vector):
            target, sign = image[source]
            output[target] = output[target] + sign * coefficient
        return tuple(output)

    for left in range(8):
        for right in range(8):
            left_target, left_sign = image[left]
            right_target, right_sign = image[right]
            transformed = transform(lattice_bracket(left, right))
            expected = tuple(
                left_sign * right_sign * value
                for value in lattice_bracket(left_target, right_target)
            )
            assert transformed == expected, (
                BASIS_NAMES[left],
                BASIS_NAMES[right],
                transformed,
                expected,
            )

    assert image[4] == (6, -1)
    assert image[5] == (7, -1)
    assert sorted(target for target, _ in image) == list(range(8))


def verify_pure_case() -> tuple[int, Scalar]:
    complement, constant, first_order = quotient_series((0, 0, 0, 0, 1, 0, 0, 0), 4)
    assert complement == [0, 1, 2, 3, 5, 6, 7]

    expected_constant = zero_numeric(7, 7)
    expected_constant[4][3] = Scalar(-1)
    assert constant == expected_constant
    assert numeric_rank(constant) == 1

    # ker(B0)=(e1,e2,e3,e6,e7,e8),
    # coker(B0)=(e1,e2,e3,e4,e7,e8).
    kernel = basis_columns(7, (0, 1, 2, 4, 5, 6))
    cokernel = basis_rows(7, (0, 1, 2, 3, 5, 6))
    assert numeric_rank(kernel) == 6
    assert numeric_rank(cokernel) == 6

    induced = projected_map(cokernel, first_order, kernel)
    assert induced == expected_pure_map()
    determinant = constant_minor(induced, (0, 2), (4, 5))
    assert determinant == 1

    verify_frame_and_rescaling_invariance(constant, first_order, kernel, cokernel)
    return numeric_rank(constant), determinant


def verify_mixed_case() -> tuple[int, Scalar]:
    complement, constant, first_order = quotient_series((0, 0, 0, 0, 1, 0, 0, 1), 4)
    assert complement == [0, 1, 2, 3, 5, 6, 7]

    expected_constant = zero_numeric(7, 7)
    expected_constant[6][1] = Scalar(3)
    expected_constant[4][3] = Scalar(-1)
    expected_constant[5][3] = Scalar(1)
    assert constant == expected_constant
    assert numeric_rank(constant) == 2

    # ker(B0)=(e1,e3,e6,e7,e8). In the cokernel e7=e6 and e8=0.
    kernel = basis_columns(7, (0, 2, 4, 5, 6))
    cokernel = basis_rows(7, (0, 1, 2, 3))
    cokernel.append(
        [
            Scalar(0),
            Scalar(0),
            Scalar(0),
            Scalar(0),
            Scalar(1),
            Scalar(1),
            Scalar(0),
        ]
    )
    assert numeric_rank(kernel) == 5
    assert numeric_rank(cokernel) == 5

    induced = projected_map(cokernel, first_order, kernel)
    assert induced == expected_mixed_map()
    determinant = constant_minor(induced, (0, 1, 2), (2, 3, 4))
    assert determinant == 1

    verify_frame_and_rescaling_invariance(constant, first_order, kernel, cokernel)
    return numeric_rank(constant), determinant


def main() -> None:
    pure_rank, pure_minor = verify_pure_case()
    mixed_rank, mixed_minor = verify_mixed_case()
    verify_integral_involution()

    print(
        "q=10 pure quotient: B0 rank",
        pure_rank,
        "; displayed constant 2-minor",
        pure_minor,
    )
    print(
        "q=10 mixed quotient: B0 rank",
        mixed_rank,
        "; displayed constant 3-minor",
        mixed_minor,
    )
    print("integral involution: 64 bracket identities and both pure lines verified")
    print("moving-frame and line-rescaling invariance: verified on matrix-unit bases")
    print("Q=10 JET FINITE CHECKS: PASS")


if __name__ == "__main__":
    main()
