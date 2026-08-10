# Status

Snapshot: 10 August 2026.

Status vocabulary in this repository:

- `PUBLISHED`: stated in a cited published source.
- `PROVED`: proved in the manuscript or supplementary notes within the stated
  scope.
- `PROVED CONDITIONAL ON`: derived assuming an explicitly named interface.
- `CANDIDATE`: a proposed theorem whose assembled proof awaits independent
  specialist review.
- `OPEN`: neither proved nor refuted here.
- `REFUTED`: contradicted by a verified argument or counterexample.

## Claim matrix

| Statement | Status | Boundary |
|---|---|---|
| Finite image for MCG-finite rank $r$ when $r<\sqrt{g+1}$ | `PUBLISHED` | Landesman--Litt, Theorem 1.2.1 |
| Rank-three finite image for $g\ge5$, all $n\ge0$ | `CANDIDATE` | Complete unrefereed manuscript |
| Rank-three finite image for $g=3,4$ | `OPEN` | No claim and no counterexample |

## Why genus five remains the claimed endpoint

The normalizer boundary-cocycle obstruction eliminates any branch in which
the universal-extension argument produces a generically injective trivial
subbundle

```math
\mathcal{O}_C^3\subseteq\ker\beta
```

inside the quotient normalizer, provided the full boundary
$H^0(C,E/M)\to H^1(C,M)$ is injective. This directly closes both the
zero-weight $q=9$ branch and the final high-Harder--Narasimhan branch in
genus five. The genus-four analysis still lacks the required bracket
compression across its surviving branches; genus three loses an additional
rank. These are method walls, not evidence that the theorem is false in those
genera.

## Current review state

The current manuscript explicitly addresses the following proof interfaces:

- a compact load-bearing dependency roadmap that separates the main proof
  from the two independent reconstructions;
- the legitimacy of testing generic branches on the required open loci in
  moduli;
- the ordinary-degree and induced-weight bookkeeping at each punctured
  stability contradiction;
- the normalizer boundary-cocycle identity and its direct application to all
  $q=9$ cases and the final high-HN branch;
- the residue and point-pushing descent that moves the dense $S=0$ fixed part
  from a pointed family to a finite cover of the unpointed moduli space;
- the full $q=9$, $h=2$ Pfaffian, determinant, and spectral-projector
  reconstruction, retained as an independent second argument;
- the complex rank-one fixed-part route through the cited
  Landesman--Litt interfaces;
- saturation and generic effectivity on the full finite-etale cover;
- the periodic-chain determinant calculation, canonical generic determinant
  character, and local-global kernel identity, retained as an independent
  reconstruction;
- the formal propagation and characteristic-socle steps.

The boundary-cocycle, fixed-part/full-cover, and Artin-propagation interfaces,
together with the independent canonical-Deligne reconstruction, are recorded
in [LOAD_BEARING_AUDIT.md](LOAD_BEARING_AUDIT.md). The finite HN, $q=10$ jet,
and $q=9$ calculations are replayable with `make verify-math`.

These interfaces are stated in full in the current source. Independent
verification of the assembled argument remains outstanding, so the theorem
remains `CANDIDATE`.

## Promotion rule

Do not replace `CANDIDATE` with `PROVED` or describe the genus-five result as
established literature solely because:

- the TeX compiles;
- the committed PDF passes preflight;
- deterministic finite checks pass;
- multiple internal reconstructions agree; or
- no counterexample has been found.
