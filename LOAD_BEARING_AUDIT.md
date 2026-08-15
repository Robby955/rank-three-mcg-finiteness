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
adjoint Deligne lattice, no-pole determinant character, and `q = 9`
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

Let `M ⊂ E` be a saturated line in a Lie bundle with generic fibre
`sl₃`, put `G = E/M`, and let

```text
K = N_E(M)/M = ker(G → G ⊗ M⁻¹).
```

For global sections `x, y ∈ H⁰(C,K)`, choose local normalizer lifts
`X_i, Y_i`. Their differences `a_ij = X_j − X_i` and
`b_ij = Y_j − Y_i` are `M`-valued Čech cocycles representing the boundary
classes `∂x` and `∂y`. The normalizer action on `M` gives a grading
character `λ: K → 𝒪_C`. Projectivity makes `λ(x)` and `λ(y)` constant,
and direct expansion gives

```text
∂[x,y] = λ(x)∂y − λ(y)∂x.
```

If the full boundary `H⁰(C,G) → H¹(C,M)` is injective, this becomes

```text
[x,y] = λ(x)y − λ(y)x.
```

The generic quotient normalizer of a nonzero element of
`sl₃` has dimension `1`, `2`, `3`, or `4`. A generically
three-dimensional space of global sections therefore leaves only the
semisimple `(2,1)` and minimal-nilpotent cases. In the semisimple case the
quotient normalizer is `sl₂` and `λ = 0`, while the displayed law would make
it abelian. In the minimal-nilpotent case, with `m = E₁₂`,
the quotient normalizer has basis

```text
D = diag(1/2,−1/2,0),    H = diag(1/2,1/2,−1),
P = E₁₃,              Q = E₃₂.
```

Here `λ(D) = 1`, the other three basis vectors lie in `ker λ`, and
`[D,P] = P/2`, `[D,Q] = Q/2`, `[H,P] = 3P/2`, and
`[H,Q] = −3Q/2`. If the three-space lies in `ker λ`, the law incorrectly
makes `⟨H,P,Q⟩` abelian. Otherwise its two-dimensional intersection with
`ker λ` must be `⟨P,Q⟩`; writing its grading-one element as
`D + cH + aP + bQ` would require both eigenvalues `(1 + 3c)/2` and
`(1 − 3c)/2` to equal one, which is impossible.

The two application hypotheses are explicit. The trivial subbundle must have
generic rank at least three; three abstract sections are not enough. The
boundary must be the full boundary for `0 → M → E → G → 0`; injectivity
only on the original universal-extension subspace is not enough. In the
closed `q = 9` branch, stability gives `H⁰(C,E) = 0`. In the punctured high-HN
branch, parabolic stability gives the same vanishing. Thus the full boundary
is injective in both cases, and their displayed trivial subbundles of ranks at
least three give the contradiction directly.

Audit result: the Cech identity, the two normalizer calculations, and both
application hypotheses pass. No no-pole determinant or spectral projector is
used in these eliminations.

## 2. Fixed part and the full-cover Hodge line

Let a nonzero fixed vector span the trivial irreducible rank-one local system
`𝕃` inside `R¹π_*^∘𝕌`. Proposition 4.2.2 supplies a constant Hodge
structure `Q` and a morphism of variations

```text
Q ⊗ 𝕃̃ → R¹π_*^∘𝕌̃.
```

The proof of Lemma 6.1.1 has two Hodge-type cases. For the real rank-one
trivial system, the case supported in both types `(1,0)` and `(0,1)` is
impossible. After conjugating the coefficient if necessary, a nonzero
one-dimensional Hodge component of `Q` therefore gives a global constant line
inside `F¹`. Its second fundamental form vanishes identically. This is
stronger than choosing a favourable vector on one fibre.

Theorem 4.1.1 and Hodge--de Rham degeneration identify the Hodge filtration
with the relative logarithmic de Rham term. On the finite-etale moduli cover,
the Kodaira--Spencer map, equivalently the cotangent map `c_b^*` in Theorem
5.1.6, is an isomorphism. The factorization in that theorem therefore turns
zero second fundamental form into zero multiplication map. The resulting
adjoint map

```text
π^*𝓗 ⊗ ω_π(D)⁻¹ → 𝓔
```

is fibrewise nonzero and has multiplication rank zero on every fibre.
For the rank `8`, `6`, and `5` coefficients used in the new cases, the
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
manuscript's boundary-descent lemma verifies this only when `S = 0` and the
projective image is Zariski dense in `PGL₃`; this audit does not
assert a general pointed-section exclusion for any other branch.

The exact mechanism is the relative residue sequence

```text
0 → R¹π̄_*𝕌 → R¹π_*^∘𝕌 → ⊕ᵢ s_i^*𝕌(−1) → R²π̄_*𝕌.
```

For the `i`th Birman point-pushing subgroup, a direct diagonal/filling
calculation shows that the canonical projective globalization acts on
`s_i^*𝕌` by `Ad(ρ̄(ev_i(α)))`. After filling, the
point-push is the corresponding inner automorphism, and the proof of
Landesman--Litt Lemma 2.2.2 identifies its unique projective intertwiner.
This calculation is not attributed to the geometric existence statement in
Lemma 2.2.3. Its intersection with the finite-cover subgroup evaluates to a
finite-index subgroup of the filled surface group.
Zariski density in connected `PGL₃` is unchanged after finite
index, so the adjoint boundary term has no fixed vectors. The fixed part is
therefore in closed cohomology. The forgotten point-pushing kernel acts there
by inner automorphisms with coefficient conjugation and hence trivially on
group cohomology, so the fixed vector factors through a finite-index subgroup
of `Mod_g`. No linear filling is assumed: density makes the
centralizer of the closed projective representation in `PGL₃`
trivial, so the uniqueness argument constructing the canonical projective
globalization works directly in `PGL₃`. After passage to a common
finite cover, the unique projective intertwiners in the proof of
Landesman--Litt Lemma 2.2.2 identify its pullback with the pointed
globalization. Lemma 2.1.5 makes the fibre group normal. The closed adjoint
has trivial determinant and irreducible unitary fibral restriction, so Lemma
2.4.1 makes it unitary on the total space. Apply Theorem 4.1.1 to
`𝕌 ⊕ 𝕌∨`, which has its natural real structure, and then take the
`𝕌`-summand; this avoids assuming an unstated compact
real form for the total globalization. Applying the theorem once more with
empty boundary identifies the closed `F¹` term with ordinary holomorphic
one-forms. With trivial puncture monodromy, closed cohomology is the
weight-one term, and strictness gives
`F¹_open ∩ W₁ = F¹_closed`. This comparison is what
transports the variation of mixed Hodge structure and its Hodge filtration;
flat factorization alone would not suffice.

Dependency boundary: the fixed-part and closure construction uses the cited
Landesman--Litt fixed-part and period-map theorems. Its contradiction with
Chen--Salter additionally depends on the stated `S = 0` dense-adjoint boundary
descent in pointed applications.

## 3. Coparabolic and canonical Deligne lattices

For

```text
P_* = (E_*)^∨ ⊗ ω_C(D),
```

the parabolic dual formula

```text
(E_*^∨)_α = (Ê_{−α})^∨(−D)
```

and the definition `P̂₀ = P_ε` for small positive `ε` give

```text
P̂₀ = E^∨ ⊗ ω_C.
```

This is also the ordinary bundle explicitly used in the published proof of
the Landesman--Litt pairing proposition. Thus the manuscript's HN section
counts do not contain a hidden `D` twist.

At a puncture, diagonalize the semisimple unitary residue with weights
`0 ≤ α_i < 1`. On `E_ij` the adjoint residue is `α_i − α_j`. Its
canonical representative is obtained by multiplying `E_ij` by `z` exactly
when `α_i < α_j`. Hence the canonical adjoint
Deligne lattice is

```text
(⊕ᵢ R H_i) ⊕ (⊕_{i ≠ j} z^[α_i < α_j] R E_ij),
```

which is precisely the trace-zero endomorphism algebra of the periodic chain
defined by the ordered residue weights. Repeated weights merely enlarge a
block. The endomorphism algebra is closed under commutators, so the global
bracket has zeros but no poles.

For a saturated minimal-nilpotent line `M`, primitivity over the DVR gives

```text
M = Hom_ch(Q,I).
```

The line normalizer is the flag parabolic preserving
`I ⊂ H ⊂ V`. Filtering it by its action on `I`, `J = H/I`, and
`Q = V/H` gives the two off-diagonal chain-Hom lattices. Their composition is an
integral generically perfect pairing. The diagonal factor is controlled by
the split trace sequence; the inclusion
`End_ch(J) ↪ End_R(J₀)` has the determinant direction used in the
manuscript. These maps yield

```text
det 𝒦 → M^{⊗(r−2)}
```

without a pole. All local maps restrict to the same intrinsic generic
determinant character, so they glue. Flat completion and saturation identify
the completed global bracket kernel with the integral normalizer quotient.

More explicitly, over the function field the flag
`I ⊂ H ⊂ V` attached to a minimal-nilpotent line canonically gives
the off-diagonal pairing
`Hom(J,I) ⊗ Hom(Q,J) → Hom(Q,I)`.
The trace-zero diagonal factor has canonically trivial determinant. Together
these define one generic character

```text
det(N(ℓ)/ℓ) → ℓ^{⊗(r−2)}.
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
`R⁰π_* ad R = 0`. Induction over a small extension
`0 → I → A → A′ → 0` and the long exact sequence then propagates both
`R⁰` vanishing and global `R¹` fixed-part vanishing.

For a reducible nonscalar unitary residual fibre, the Landesman--Litt
fibral-unitary decomposition gives summands `U_i ⊗ π⁎W_i`. Passing to
the first nonzero maximal-ideal graded piece of `W_i` produces a complex map

```text
(W_i⁰)∨ → R¹π_*^∘ U_i.
```

Its image has rank at most the residual multiplicity `w_i`. The complete
rank-three residual table gives

```text
(u_i,w_i) = (1,w_i ≤ 4), (2,w_i ≤ 3), (3,1),
```

whereas the published fixed-part lower bounds at genus five are respectively
`8`, `6`, and `4`.

For a scalar residual fibre, the adjoint has eight copies of the trivial
fibral coefficient. Any unitary base-line twist can be removed without
changing ranks. Multiplication by a nonzero logarithmic one-form is injective
on `H⁰(ω_C)`, so Lemma 6.1.1 gives the sharper lower bound `2g` for a
nonzero fixed sub-local system. This excludes rank at most eight when
`g ≥ 5`.

These three cases provide exactly the Artin vanishing substituted into Lemma
8.5.1. The source audit in [PIPELINE_AUDIT.md](PIPELINE_AUDIT.md) records the
remaining rigidity, integrality, isomonodromy, constancy, and socle steps.

Dependency boundary: this interface uses the named Landesman--Litt
decomposition, fixed-part, deformation, and socle results.

## Remaining boundary

These notes isolate the specialist-review boundary in genus five. They do not
provide independent verification of the assembled theorem. The deterministic
verifiers under [`verification/math`](verification/math) check only the finite
HN arithmetic and `q = 9` fibre algebra.

These genus-five notes do not establish a lower-genus theorem. The separate
genus-four candidate manuscript uses additional no-high, high-HN,
proper-projective-closure, and propagation arguments and is conditional on its
stated interface package B1--B5; this audit does not independently verify that
extension. Genus three remains open.
