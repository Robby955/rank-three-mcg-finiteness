# Landesman--Litt pipeline substitution audit

This note records where the strict rank hypothesis enters the published proof
of Landesman--Litt and what the rank-three manuscript substitutes for it.

Source inspected: Aaron Landesman and Daniel Litt, *Canonical representations
of surface groups*, arXiv:2205.15352v4 and *Annals of Mathematics* 199 (2024),
823--897.

This is an internal dependency audit, not an external referee report.

## Result of the source inspection

In the proofs of Sections 8.2--8.7, the published inequality
`r < sqrt(g+1)` is used in two substantive ways:

1. to obtain adjoint fixed-part vanishing, hence strong cohomological rigidity
   and formal constancy; and
2. to bound the dimension of a projected characteristic extension in the
   non-semisimple step.

No additional numerical use of the strict rank hypothesis was found in the
integrality, unitary-conjugate, nonabelian-Hodge, or socle-induction portions of
those proofs.

## Substitution map

| Published step | Where the strict bound enters | Rank-three replacement |
|---|---|---|
| Proposition 8.2.1, strong cohomological rigidity | Uses Theorem 6.2.1 for the adjoint coefficient of rank `r^2 - 1 < g`; Schur and Leray provide the other vanishing | Sections 4--12 establish the required finite-cover adjoint fixed-part vanishing; Section 14 supplies finite-index descent |
| Lemma 8.3.3, projective integrality | The proof invokes Proposition 8.2.1; its remaining inputs are irreducibility, `g >= 3`, MCG-finiteness, and quasi-unipotent boundary monodromy | The specialized strong-rigidity conclusion replaces Proposition 8.2.1 |
| Lemma 8.3.4, linear integrality | Uses Lemma 8.3.3 and finite determinant; there is no independent rank estimate in the lifting argument | Projective integrality plus the unchanged finite-determinant lift |
| Proposition 8.4.1, unitary finite image | Uses Lemma 8.3.4 and Proposition 8.2.1; the isomonodromy input has the larger range `r < 2 sqrt(g+1)` | Rank three satisfies the larger range for `g >= 5`; the specialized rigidity and integrality conclusions provide the other inputs |
| Lemma 8.5.1, infinitesimal constancy | Uses `r^2 - 1 < g` precisely to invoke Theorem 6.2.1 for every Artin truncation | Proposition 14.4 gives the rank-three Artin vanishing after treating irreducible, reducible, and scalar residual types |
| Lemma 8.5.2, global constancy | Uses Lemma 8.5.1; the rest is the curve reduction and closedness of the semisimple conjugacy orbit | Proposition 14.4 replaces Lemma 8.5.1; the remaining argument is unchanged |
| Lemma 8.6.1, characteristic extensions | Uses the strict rank bound to force `n_i dim(sigma_i) < (g+1)/4`, then compares with Theorem 7.2.1 | Proposition 14.7 uses total rank at most three, hence `n_i dim(sigma_i) <= 2`, and the same published lower bound |
| Section 8.7, socle induction | Uses the semisimple theorem and Lemma 8.6.1 | Propositions 14.6 and 14.7 supply those two inputs |

## What remains load-bearing

The source inspection supports the architecture of the substitution, but it
does not independently prove the new substitute statements. The remaining
specialist-review frontier is concentrated in three interfaces:

1. **Normalizer boundary cocycle.** Check the full-boundary Cech identity,
   the generic-rank hypothesis, and the semisimple and minimal-nilpotent
   quotient-normalizer calculations used in both genus-five applications.
2. **Fixed part to adjoint vanishing.** Check the complex rank-one Hodge-line
   construction, its behavior on every connected finite cover, and the passage
   from the fibre calculation to the global fixed-part statement.
   This includes the coparabolic convention used in the HN inequalities.
3. **Finite-cover geometry to dominant-etale formal propagation.** Check the
   projective finite-index descent and the reducible/scalar Artin devissage in
   Section 14.

The zero-weight genus-five `q=9`, `h=2` Pfaffian/spectral reduction and the
periodic-chain no-pole determinant calculation have complete displayed
arguments. They are retained as separate reconstructions, but
neither is a dependency of the main elimination.

## Separate open boundary

Genus four and genus three are not consequences of this audit. The cocycle
obstruction applies once a generically injective trivial rank-three
quotient-normalizer subbundle is available, but the current genus-four HN
analysis does not supply that compression across all surviving branches.
Genus three loses an additional rank. New input is required for both genera.
