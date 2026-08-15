# Proof and review map

This map is an entry point for a specialist reader. Section names refer to the
[canonical manuscript](manuscript/rank3_genus5_reader.tex).

| Manuscript component | Role | Focused review question |
|---|---|---|
| Section 2, published inputs and conventions | Fixes Landesman--Litt, Brill--Noether, universal-curve, coparabolic, canonical-Deligne, and parabolic-stability bookkeeping | Are the published hypotheses, ordinary degrees, and induced weights imported in their exact form? |
| Section 3, projective closure alternatives | Reduces irreducible rank three to actual adjoint constituents | Does the projective classification cover every closure type used later? |
| Section 4, fixed-part interface | Converts an invariant rank-one subsystem into multiplication rank zero and explains why a general test fibre may be chosen | Is the complex rank-one case split valid on the chosen cover, and do the required open moduli conditions meet the branch locus? |
| Sections 5--6, endpoint and first super-endpoint | Strengthens the stable coefficient estimate, classifies the next equality case, and proves the normalizer boundary-cocycle obstruction | Are stability, parabolic degree, and equality cases used with the correct strictness, and does the Cech identity exclude a generically rank-three normalizer subspace? |
| Sections 7--9, genera seven, six, and genus-five HN tree | Reduces the remaining adjoint coefficient to finitely many branches | Are all numerical branches exhaustive under the stated HN inequalities? |
| Sections 4 and 10.2, zero-weight `(S, q) = (0, 9)` branch | Descends the fixed part past the pointed boundary, then uses a rank-at-least-three trivial quotient-normalizer subbundle | Does point-pushing kill every residue summand, and do stability and the full extension boundary give the exact hypotheses of the cocycle obstruction? |
| Section 10.3, independent `q = 9` reconstruction | Retains the former Pfaffian, determinant, and spectral-projector elimination as a second proof | Do the divisors `T` and `Z_λ` force either a degree-one line or the exact projector hypotheses? |
| Section 10.4, full-cover relative line | Constructs and saturates the Hodge line without shrinking the finite cover | Does reflexive extension preserve relative degree and does generic effectivity globalize? |
| Sections 11--12, punctured and final high-HN branches | Produces a trivial rank-four quotient-normalizer subbundle and applies the boundary-cocycle obstruction | Does parabolic stability make the full extension boundary injective? |
| Section 13, independent canonical-Deligne reconstruction | Retains the no-pole map `det 𝒦 → M` as a second proof | Is the periodic lattice-chain model exactly the canonical adjoint Deligne lattice for all contact orders? |
| Section 14, propagation | Returns adjoint vanishing to finite image for all rank-three representations | Do projective descent, Artin devissage, unitary endpoints, and socle induction match the cited pipeline? |

The strict-rank substitutions in the final row are expanded in
[PIPELINE_AUDIT.md](PIPELINE_AUDIT.md). The principal load-bearing interfaces,
together with the independent reconstructions in Sections 10.3 and 13, are
recorded in
[LOAD_BEARING_AUDIT.md](LOAD_BEARING_AUDIT.md).

## Separate genus-four candidate

The [genus-four manuscript](manuscript/rank3_genus4_extension.tex) is a
separate conditional candidate, not a corollary certified by the map above.

| Genus-four component | Role | Focused review question |
|---|---|---|
| Sections 1--2, statement and B1--B5 | Makes the imported dependency package part of the candidate statement | Are B1--B5 exactly the interfaces proved or proposed in the companion manuscript, with no hidden strict-genus use? |
| Sections 4--5, finite frontiers | Records the no-high and high-HN survivor tables | Are the HN types, section bounds, parabolic weights, and degree inequalities exhaustive? |
| Section 6, dense rank-eight coefficient | Proposes the fibrewise and global elimination of every remaining dense branch | Do the Cech--Petri symmetry, evaluation-lattice saturation, Killing/Spin comparison, primitive pairing bound, and BPGN equality cases hold as stated? |
| Section 7, proper projective closures | Treats the rank-five orthogonal and rank-six monomial coefficients | Do the imported first-super classification, invariant form, and determinant-sign arguments exclude all proper-closure cases? |
| Section 8, propagation | Handles the genus-four scalar equality and carries fixed-part vanishing to finite image | Is the standard rank-eight symplectic subsystem identified on every finite cover, and do the B5 descent and socle steps apply at equality? |
| Section 9, verification boundary | Separates exact finite calculations from the unrefereed geometric argument | Are all conditional dependencies and nonclaims stated accurately? |

For genus four, begin with Sections 1--2, then review Sections 6, 7, and 8 in
that order. The `verify_genus4_candidate.py` gate checks the source/PDF
identity and public claim boundary; it does not certify the proof.

## Suggested review order

1. Read Sections 2 and 4 to fix conventions and the fixed-part interface.
2. Check the boundary-cocycle proposition in Section 6 and its direct
   applications in Sections 10.2 and 12.
3. Check the finite HN branch tables in Sections 7--11.
4. Check Section 14 against the cited Landesman--Litt statements.
5. As independent second proofs, check the Pfaffian/spectral reconstruction
   in Section 10.3 and the no-pole reconstruction in Section 13.

The exact finite arithmetic under [`verification/math`](verification/math)
and the PDF verification do not certify the Hodge-theoretic, parabolic, or
mapping-class-group steps.
