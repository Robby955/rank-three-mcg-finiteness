# Status

Snapshot: 15 August 2026.

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
| Finite image for MCG-finite rank `r` when `r < √(g + 1)` | `PUBLISHED` | Landesman--Litt, Theorem 1.2.1 |
| Finite image for MCG-finite rank `r` when `r² ≤ g + 1` | `CANDIDATE` | The new equality case `r² = g + 1` is a complete unrefereed standalone note |
| Proposed sharper range `g ≥ r² − 4` | `OPEN` | No proof or counterexample is claimed here |
| Rank-three finite image for `g ≥ 5`, all `n ≥ 0` | `CANDIDATE` | Complete unrefereed manuscript |
| Rank-three finite image for `g = 4`, all `n ≥ 0` | `CANDIDATE` | Separate unrefereed manuscript, conditional on its explicitly listed interfaces B1--B5 |
| Rank-three finite image for `g = 3` | `OPEN` | No theorem or counterexample is claimed; explicit residual walls remain |

## Why genus four is a separate conditional candidate

The normalizer boundary-cocycle obstruction eliminates any branch in which
the universal-extension argument produces a generically injective trivial
subbundle

> `𝒪_C³ ⊆ ker β`

inside the quotient normalizer, provided the full boundary
`H⁰(C, E/M) → H¹(C, M)` is injective. This directly closes both the
zero-weight `q = 9` branch and the final high-Harder--Narasimhan branch in
genus five. The standalone square-endpoint note reaches rank three at genus
eight; the specialized manuscript treats genera seven, six, and five.

The separate genus-four manuscript imports five interface groups from that
candidate package and proposes eliminations for the dense rank-eight,
rank-five orthogonal, and rank-six monomial coefficients, followed by the
remaining propagation equality. Its conclusion is therefore a conditional,
unrefereed `CANDIDATE`, not a consequence of the published strict theorem and
not an established result. Genus three remains `OPEN`.

## Current review state

The current manuscript explicitly addresses the following proof interfaces:

- a compact load-bearing dependency roadmap that separates the main proof
  from the two independent reconstructions;
- the legitimacy of testing generic branches on the required open loci in
  moduli;
- the ordinary-degree and induced-weight bookkeeping at each punctured
  stability contradiction;
- the normalizer boundary-cocycle identity and its direct application to all
  `q = 9` cases, the repaired `(S, q) = (2, 10)` branch, and the final
  high-HN branch;
- the explicit morphism-of-extensions square in `(S, q) = (2, 10)`, which
  bounds the effective degree-two self-block by rank one and produces four
  independent quotient-normalizer sections without identifying its divisor
  with the marked point;
- the residue and point-pushing descent that moves the dense `S = 0` fixed part
  from a pointed family to a finite cover of the unpointed moduli space;
- the full `q = 9`, `h = 2` Pfaffian, determinant, and spectral-projector
  reconstruction, retained as an independent second argument;
- the complex rank-one fixed-part route through the cited
  Landesman--Litt interfaces;
- saturation and generic effectivity on the full finite-etale cover;
- the periodic-chain determinant calculation, canonical generic determinant
  character, and local-global kernel identity, retained as an independent
  reconstruction;
- the formal propagation and characteristic-socle steps.

The boundary-cocycle, degree-two extension-naturality, fixed-part/full-cover,
and Artin-propagation interfaces,
together with the independent canonical-Deligne reconstruction, are recorded
in [LOAD_BEARING_AUDIT.md](LOAD_BEARING_AUDIT.md). The finite HN and `q = 9`
calculations are replayable with `make verify-math`; the retained `q = 10`
jet script is a non-load-bearing local diagnostic.

These interfaces are stated in full in the current source. Independent
verification of the assembled argument remains outstanding, so the theorem
remains `CANDIDATE`.

The genus-four manuscript separately states B1--B5 as hypotheses of its main
candidate theorem and identifies the new geometric steps requiring review.
Its artifact verifier checks the source/PDF correspondence and public claim
boundaries; it does not certify the proof.

## Promotion rule

Do not replace `CANDIDATE` with `PROVED` or describe either rank-three
candidate as established literature solely because:

- the TeX compiles;
- the committed PDF passes preflight;
- deterministic finite checks pass;
- multiple non-referee reconstructions agree; or
- no counterexample has been found.
