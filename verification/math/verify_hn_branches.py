#!/usr/bin/env python3
"""Exact finite checks for the genus-six and genus-five HN reconstruction.

The section routine deliberately ranges over every rank/degree decomposition,
not only slope-ordered HN types. Its result is therefore a safe upper bound.
The script does not certify the geometric elimination of an equality case.
"""

from __future__ import annotations

from fractions import Fraction
from functools import lru_cache
from math import ceil, floor
from typing import Iterable

GENUS = 5
COEFFICIENT_RANK = 8


def high_t1_candidates(
    offsets: Iterable[int],
    *,
    q_min: int,
    sum_min: int,
    clifford_slack: int,
) -> dict[int, tuple[int, ...]]:
    """Enumerate the integral t=1 rows left by the displayed inequalities."""
    return {
        y: tuple(q for q in range(q_min, y + clifford_slack + 1) if q + y >= sum_min)
        for y in offsets
    }


def offset_ranges(genus: int) -> dict[int, tuple[int, ...]]:
    ranges: dict[int, tuple[int, ...]] = {}
    for high_rank in range(COEFFICIENT_RANK + 1):
        quotient_rank = COEFFICIENT_RANK - high_rank
        if quotient_rank <= 0:
            continue
        coefficient_degree = COEFFICIENT_RANK * (2 * genus - 2)
        lower = Fraction(coefficient_degree) - Fraction(
            quotient_rank * (2 * genus * quotient_rank - 2), quotient_rank + 1
        )
        upper = (2 * genus - 2) * high_rank
        values = tuple(range(ceil(lower), upper + 1))
        if values:
            ranges[high_rank] = values
    return ranges


def no_high_candidates() -> list[tuple[int, int]]:
    candidates: list[tuple[int, int]] = []
    for total_weight in (0, 2, 3, 4, 5):
        q_min = max(9, 8 + total_weight)
        q_max = 14 - total_weight
        candidates.extend((total_weight, q) for q in range(q_min, q_max + 1))
    return candidates


@lru_cache(maxsize=None)
def compositions(total: int, parts: int, positive: bool) -> tuple[tuple[int, ...], ...]:
    if parts == 1:
        allowed = total >= 1 if positive else total >= 0
        return ((total,),) if allowed else ()

    start = 1 if positive else 0
    output: list[tuple[int, ...]] = []
    for first in range(start, total + 1):
        remaining = total - first
        minimum_tail = parts - 1 if positive else 0
        if remaining < minimum_tail:
            break
        for tail in compositions(remaining, parts - 1, positive):
            output.append((first, *tail))
    return tuple(output)


def semistable_h0_bound(rank: int, degree: int, *, generic_curve: bool) -> int:
    if degree == 0:
        return rank
    if 0 < degree <= rank:
        return rank - ceil(Fraction(rank - degree, GENUS))

    bound = floor(rank + Fraction(degree, 2))
    if rank == 1 and generic_curve and degree in (2, 3):
        # The dense genus-five fibre is nonhyperelliptic and nontrigonal.
        return 1
    return bound


def hn_section_upper_bound(
    rank: int,
    degree: int,
    *,
    allow_zero_degree: bool,
    generic_curve: bool,
) -> tuple[int, tuple[tuple[tuple[int, int], ...], ...]]:
    best = -1
    witnesses: list[tuple[tuple[int, int], ...]] = []
    for parts in range(1, rank + 1):
        for ranks in compositions(rank, parts, True):
            for degrees in compositions(degree, parts, not allow_zero_degree):
                value = sum(
                    semistable_h0_bound(r, d, generic_curve=generic_curve)
                    for r, d in zip(ranks, degrees, strict=True)
                )
                witness = tuple(zip(ranks, degrees, strict=True))
                if value > best:
                    best = value
                    witnesses = [witness]
                elif value == best:
                    witnesses.append(witness)
    return best, tuple(witnesses)


def main() -> None:
    genus_six_offsets = offset_ranges(6)
    assert genus_six_offsets[1] == (9, 10)
    assert genus_six_offsets[2] == (20,)
    genus_six_t1 = high_t1_candidates(
        genus_six_offsets[1],
        q_min=11,
        sum_min=20,
        clifford_slack=2,
    )
    assert genus_six_t1 == {9: (11,), 10: (11, 12)}
    assert {y: y - 10 for y in genus_six_t1} == {9: -1, 10: 0}

    offsets = offset_ranges(5)
    genus_five_t1 = high_t1_candidates(
        offsets[1],
        q_min=9,
        sum_min=16,
        clifford_slack=4,
    )
    assert genus_five_t1 == {
        5: (),
        6: (10,),
        7: (9, 10, 11),
        8: (9, 10, 11, 12),
    }
    assert {y: y - 8 for y in genus_five_t1} == {
        5: -3,
        6: -2,
        7: -1,
        8: 0,
    }

    assert offsets[1] == (5, 6, 7, 8)
    assert offsets[2] == (15, 16)
    assert offsets[3] == (24,)

    no_high = no_high_candidates()
    assert no_high == [
        (0, 9),
        (0, 10),
        (0, 11),
        (0, 12),
        (0, 13),
        (0, 14),
        (2, 10),
        (2, 11),
        (2, 12),
        (3, 11),
    ]

    expected_closed = {1: 5, 2: 6, 3: 6, 4: 7, 5: 8, 6: 8}
    closed: dict[int, int] = {}
    for degree, expected in expected_closed.items():
        bound, _ = hn_section_upper_bound(
            7,
            degree,
            allow_zero_degree=False,
            generic_curve=True,
        )
        assert bound == expected, (degree, bound, expected)
        closed[degree] = bound

    punctured, _ = hn_section_upper_bound(
        7,
        2,
        allow_zero_degree=True,
        generic_curve=True,
    )
    assert punctured == 7

    residual: list[tuple[int, int]] = []
    for total_weight, q in no_high:
        if total_weight == 0:
            degree = q - 8
            required_sections = q - 4
            if required_sections <= closed[degree]:
                residual.append((total_weight, q))
        elif (total_weight, q) == (2, 12):
            required_sections = q - 4
            if required_sections <= punctured:
                residual.append((total_weight, q))
        else:
            residual.append((total_weight, q))
    assert residual == [(0, 9), (0, 10), (2, 10), (2, 11), (3, 11)]

    print("Genus-six t=1 table:", genus_six_t1)
    print("Genus-five t=1 table:", genus_five_t1)
    print("Genus-five HN offsets:", {key: offsets[key] for key in (1, 2, 3)})
    print("No-high candidates:", no_high)
    print("Closed rank-seven section bounds:", closed)
    print("Punctured rank-seven degree-two bound:", punctured)
    print("Residual no-high list:", residual)
    print("HN FINITE CHECKS: PASS")


if __name__ == "__main__":
    main()
