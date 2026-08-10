# Supplementary notes on proof interfaces

Snapshot: 10 August 2026.

## Scope

This note expands three interfaces that merit specialist scrutiny:

1. the normalizer boundary cocycle directly excludes a generically
   rank-three trivial subbundle once the full extension boundary is injective;
2. the fixed-part argument produces a global rank-zero Hodge line on every
   connected finite-etale cover where the coefficient is defined;
3. finite-cover adjoint vanishing propagates to the dominant-etale Artin base
   after treating irreducible, reducible nonscalar, and scalar residual types
   separately.

The coparabolic convention remains part of the HN input. The canonical
adjoint Deligne lattice, no-pole determinant character, and $q=9$
spectral-projector route are included as separate reconstructions rather than
dependencies of the main elimination. These notes record the proposed
deductions and their exact published inputs; they do not constitute
independent referee acceptance. The genus-at-least-five theorem remains
`CANDIDATE`.

Primary sources checked:

- Landesman--Litt, [*Canonical representations of surface
  groups*](https://annals.math.princeton.edu/2024/199-2/p06), especially
  Proposition 4.2.2, Theorems 4.1.1 and 5.1.6, Lemma 6.1.1, Theorem 1.7.1,
  and Sections 8.2--8.7;
- Landesman--Litt, [*Geometric local systems on very general curves and
  isomonodromy*](https://doi.org/10.1090/jams/1038)
  ([arXiv:2202.00039v3](https://arxiv.org/abs/2202.00039v3)), especially the
  definitions of parabolic duality and coparabolic bundles and Proposition
  6.3.6.

## 1. Normalizer boundary cocycle

Let $M\subset E$ be a saturated line in a Lie bundle with generic fibre
$\mathfrak{sl}_3$, put $G=E/M$, and let

```math
K=N_E(M)/M=\ker(G\longrightarrow G\otimes M^{-1}).
```

For global sections $x,y\in H^0(C,K)$, choose local normalizer lifts
$X_i,Y_i$. Their differences $a_{ij}=X_j-X_i$ and
$b_{ij}=Y_j-Y_i$ are $M$-valued Cech cocycles representing the boundary
classes $\partial x$ and $\partial y$. The normalizer action on $M$ gives a
grading character $\lambda:K\to\mathcal O_C$. Projectivity makes
$\lambda(x)$ and $\lambda(y)$ constant, and direct expansion gives

```math
\partial[x,y]=\lambda(x)\partial y-\lambda(y)\partial x.
```

If the full boundary $H^0(C,G)\to H^1(C,M)$ is injective, this becomes

```math
[x,y]=\lambda(x)y-\lambda(y)x.
```

The generic quotient normalizer of a nonzero element of
$\mathfrak{sl}_3$ has dimension $1,2,3,$ or $4$. A generically
three-dimensional space of global sections therefore leaves only the
semisimple $(2,1)$ and minimal-nilpotent cases. In the semisimple case the
quotient normalizer is $\mathfrak{sl}_2$ and $\lambda=0$, while the displayed
law would make it abelian. In the minimal-nilpotent case, with $m=E_{12}$,
the quotient normalizer has basis

```math
D=\mathrm{diag}(1/2,-1/2,0),\quad
H=\mathrm{diag}(1/2,1/2,-1),\quad P=E_{13},\quad Q=E_{32}.
```

Here $\lambda(D)=1$, the other three basis vectors lie in $\ker\lambda$,
and
$[D,P]=P/2$, $[D,Q]=Q/2$, $[H,P]=3P/2$,
$[H,Q]=-3Q/2$. If the three-space lies in $\ker\lambda$, the law incorrectly
makes $\langle H,P,Q\rangle$ abelian. Otherwise its two-dimensional
intersection with $\ker\lambda$ must be $\langle P,Q\rangle$; writing its
grading-one element as $D+cH+aP+bQ$ would require both eigenvalues
$(1+3c)/2$ and $(1-3c)/2$ to equal one, which is impossible.

The two application hypotheses are explicit. The trivial subbundle must have
generic rank at least three; three abstract sections are not enough. The
boundary must be the full boundary for $0\to M\to E\to G\to0$; injectivity
only on the original universal-extension subspace is not enough. In the
closed $q=9$ branch, stability gives $H^0(C,E)=0$. In the punctured high-HN
branch, parabolic stability gives the same vanishing. Thus the full boundary
is injective in both cases, and their displayed trivial subbundles of ranks at
least three give the contradiction directly.

Audit result: the Cech identity, the two normalizer calculations, and both
application hypotheses pass. No no-pole determinant or spectral projector is
used in these eliminations.

## 2. Fixed part and the full-cover Hodge line

Let a nonzero fixed vector span the trivial irreducible rank-one local system
$\mathbb L$ inside $R^1\pi_*^\circ\mathbb U$. Proposition 4.2.2 supplies a
constant Hodge structure $Q$ and a morphism of variations

```math
Q\otimes\widetilde{\mathbb L}\longrightarrow
R^1\pi_*^\circ\widetilde{\mathbb U}.
```

The proof of Lemma 6.1.1 has two Hodge-type cases. For the real rank-one
trivial system, the case supported in both types $(1,0)$ and $(0,1)$ is
impossible. After conjugating the coefficient if necessary, a nonzero
one-dimensional Hodge component of $Q$ therefore gives a global constant line
inside $F^1$. Its second fundamental form vanishes identically. This is
stronger than choosing a favourable vector on one fibre.

Theorem 4.1.1 and Hodge--de Rham degeneration identify the Hodge filtration
with the relative logarithmic de Rham term. On the finite-etale moduli cover,
the Kodaira--Spencer map, equivalently the cotangent map $c_b^*$ in Theorem
5.1.6, is an isomorphism. The factorization in that theorem therefore turns
zero second fundamental form into zero multiplication map. The resulting
adjoint map

```math
\pi^*\mathcal H\otimes\omega_\pi(D)^{-1}\longrightarrow\mathcal E
```

is fibrewise nonzero and has multiplication rank zero on every fibre.
For the rank $8$, $6$, and $5$ coefficients used in the new cases, the
projective-closure decomposition makes the coefficient globally defined after
a finite-etale cover; finite determinant and irreducible unitary fibral
monodromy make it unitary on the total family. The argument is unchanged after
every further connected finite-etale cover.

On the regular total space, double dualizing the saturated rank-one image
produces an invertible sheaf. The double-dual correction is supported in
codimension at least two and therefore misses the generic curve. Relative
degree is constant. If the inverse line has generic degree one and is
effective generically, upper semicontinuity, cohomology and base change, and
the evaluation divisor produce a finite flat degree-one divisor over the full
base, hence a section. No shrink to a generic open is used.

For a pointed universal curve, the existence of a section is not by itself a
contradiction: the marked points give tautological sections. The use of
Chen--Salter therefore requires moving the fixed part and its Hodge line to a
closed universal family before constructing the degree-one section. The
manuscript's boundary-descent lemma verifies this only when $S=0$ and the
projective image is Zariski dense in $\mathrm{PGL}_3$; this audit does not
assert a general pointed-section exclusion for any other branch.

The exact mechanism is the relative residue sequence

```math
0\to R^1\bar\pi_*\mathbb U\to R^1\pi_*^\circ\mathbb U
\to\bigoplus_i s_i^*\mathbb U(-1)\to R^2\bar\pi_*\mathbb U.
```

For the $i$th Birman point-pushing subgroup, a direct diagonal/filling
calculation shows that the canonical projective globalization acts on
$s_i^*\mathbb U$ by
$\mathrm{Ad}(\bar\rho(\mathrm{ev}_i(\alpha)))$. After filling, the
point-push is the corresponding inner automorphism, and the proof of
Landesman--Litt Lemma 2.2.2 identifies its unique projective intertwiner.
This calculation is not attributed to the geometric existence statement in
Lemma 2.2.3. Its intersection with the finite-cover subgroup evaluates to a
finite-index subgroup of the filled surface group.
Zariski density in connected $\mathrm{PGL}_3$ is unchanged after finite
index, so the adjoint boundary term has no fixed vectors. The fixed part is
therefore in closed cohomology. The forgotten point-pushing kernel acts there
by inner automorphisms with coefficient conjugation and hence trivially on
group cohomology, so the fixed vector factors through a finite-index subgroup
of $\mathrm{Mod}_g$. No linear filling is assumed: density makes the
centralizer of the closed projective representation in $\mathrm{PGL}_3$
trivial, so the uniqueness argument constructing the canonical projective
globalization works directly in $\mathrm{PGL}_3$. After passage to a common
finite cover, the unique projective intertwiners in the proof of
Landesman--Litt Lemma 2.2.2 identify its pullback with the pointed
globalization. Lemma 2.1.5 makes the fibre group normal. The closed adjoint
has trivial determinant and irreducible unitary fibral restriction, so Lemma
2.4.1 makes it unitary on the total space. Apply Theorem 4.1.1 to
$\mathbb U\oplus\mathbb U^\vee$, which has its natural real structure, and
then take the $\mathbb U$-summand; this avoids assuming an unstated compact
real form for the total globalization. Applying the theorem once more with
empty boundary identifies the closed $F^1$ term with ordinary holomorphic
one-forms. With trivial puncture monodromy, closed cohomology is the
weight-one term, and strictness gives
$F^1_{\mathrm{open}}\cap W_1=F^1_{\mathrm{closed}}$. This comparison is what
transports the variation of mixed Hodge structure and its Hodge filtration;
flat factorization alone would not suffice.

Dependency boundary: the fixed-part and closure construction uses the cited
Landesman--Litt fixed-part and period-map theorems. Its contradiction with
Chen--Salter additionally depends on the stated $S=0$ dense-adjoint boundary
descent in pointed applications.

## 3. Coparabolic and canonical Deligne lattices

For

```math
P_*=(E_*)^\vee\otimes\omega_C(D),
```

the parabolic dual formula

```math
(E_*^\vee)_\alpha=(\widehat E_{-\alpha})^\vee(-D)
```

and the definition $\widehat P_0=P_\varepsilon$ for small positive
$\varepsilon$ give

```math
\widehat P_0=E^\vee\otimes\omega_C.
```

This is also the ordinary bundle explicitly used in the published proof of
the Landesman--Litt pairing proposition. Thus the manuscript's HN section
counts do not contain a hidden $D$ twist.

At a puncture, diagonalize the semisimple unitary residue with weights
$0\leq\alpha_i<1$. On $E_{ij}$ the adjoint residue is
$\alpha_i-\alpha_j$. Its canonical representative is obtained by multiplying
$E_{ij}$ by $z$ exactly when $\alpha_i<\alpha_j$. Hence the canonical adjoint
Deligne lattice is

```math
\left(\bigoplus_i RH_i\right)\oplus
\left(\bigoplus_{i\ne j}z^{[\alpha_i<\alpha_j]}RE_{ij}\right),
```

which is precisely the trace-zero endomorphism algebra of the periodic chain
defined by the ordered residue weights. Repeated weights merely enlarge a
block. The endomorphism algebra is closed under commutators, so the global
bracket has zeros but no poles.

For a saturated minimal-nilpotent line $M$, primitivity over the DVR gives

```math
M=\mathrm{Hom}_{\mathrm{ch}}(Q,I).
```

The line normalizer is the flag parabolic preserving
$I\subset H\subset V$. Filtering it by its action on $I$, $J=H/I$, and
$Q=V/H$ gives the two off-diagonal chain-Hom lattices. Their composition is an
integral generically perfect pairing. The diagonal factor is controlled by
the split trace sequence; the inclusion
$\mathrm{End}_{\mathrm{ch}}(J)\hookrightarrow
\mathrm{End}_R(J_0)$ has the determinant direction used in the
manuscript. These maps yield

```math
\det\mathcal K\longrightarrow M^{\otimes(r-2)}
```

without a pole. All local maps restrict to the same intrinsic generic
determinant character, so they glue. Flat completion and saturation identify
the completed global bracket kernel with the integral normalizer quotient.

More explicitly, over the function field the flag
$I\subset H\subset V$ attached to a minimal-nilpotent line canonically gives
the off-diagonal pairing
$\mathrm{Hom}(J,I)\otimes\mathrm{Hom}(Q,J)\to\mathrm{Hom}(Q,I)$.
The trace-zero diagonal factor has canonically trivial determinant. Together
these define one generic character

```math
\det(N(\ell)/\ell)\longrightarrow\ell^{\otimes(r-2)}.
```

The periodic-chain construction at every DVR restricts to this same character.
Its determinant inclusions can contribute only effective cokernel lengths, so
the character has no pole at any closed point and extends uniquely to the
global determinant morphism.

Dependency boundary: the coparabolic convention and the canonical Deligne
periodic-chain model are used for the semisimple unitary residues specified in
the manuscript. The no-pole determinant conclusion is a separate
reconstruction, not a dependency of the main proof.

## 4. Finite-cover geometry and Artin propagation

For an irreducible residual representation, pull a dominant-etale linear
globalization back to the finite-etale projective-globalization cover.
Schur's lemma identifies its adjoint with the pullback of the canonical
projective adjoint. The image of the pullback fundamental group in the
finite-cover fundamental group has finite index. A hypothetical invariant on
the dominant-etale base would therefore become an invariant on a further
connected finite-etale cover, contradicting the assumed vanishing there.

For a free Artin coefficient with irreducible residual fibre, Schur gives
$R^0\pi_*\mathrm{ad}R=0$. Induction over a small extension
$0\to I\to A\to A'\to0$ and the long exact sequence then propagates both
$R^0$ vanishing and global $R^1$ fixed-part vanishing.

For a reducible nonscalar unitary residual fibre, the Landesman--Litt
fibral-unitary decomposition gives summands $U_i\otimes\pi^*W_i$. Passing to
the first nonzero maximal-ideal graded piece of $W_i$ produces a complex map

```math
(W_i^0)^\vee\longrightarrow R^1\pi_*^\circ U_i.
```

Its image has rank at most the residual multiplicity $w_i$. The complete
rank-three residual table gives

```math
(u_i,w_i)=(1,w_i\leq4),\quad(2,w_i\leq3),\quad(3,1),
```

whereas the published fixed-part lower bounds at genus five are respectively
$8$, $6$, and $4$.

For a scalar residual fibre, the adjoint has eight copies of the trivial
fibral coefficient. Any unitary base-line twist can be removed without
changing ranks. Multiplication by a nonzero logarithmic one-form is injective
on $H^0(\omega_C)$, so Lemma 6.1.1 gives the sharper lower bound $2g$ for a
nonzero fixed sub-local system. This excludes rank at most eight when
$g\geq5$.

These three cases provide exactly the Artin vanishing substituted into Lemma
8.5.1. The source audit in [PIPELINE_AUDIT.md](PIPELINE_AUDIT.md) records the
remaining rigidity, integrality, isomonodromy, constancy, and socle steps.

Dependency boundary: this interface uses the named Landesman--Litt
decomposition, fixed-part, deformation, and socle results.

## Remaining boundary

These notes isolate the specialist-review boundary in genus five. They do not
provide independent verification of the assembled theorem. The deterministic
verifiers under [`verification/math`](verification/math) check only the finite
HN arithmetic and $q=9$ fibre algebra.

Genus three and four remain a separate method wall. The cocycle obstruction
would eliminate a genus-four branch once a generically injective trivial
rank-three quotient-normalizer subbundle is available, but the current
genus-four HN analysis does not produce that compression across all surviving
branches. Genus three loses an additional rank. Neither lower-genus theorem
is claimed here.
