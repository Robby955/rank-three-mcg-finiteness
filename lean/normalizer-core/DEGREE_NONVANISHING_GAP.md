# Exact remaining degree/nonvanishing interface

The target is the specified-section implication of
[Stacks Lemma 33.44.12(2)](https://stacks.math.columbia.edu/tag/0B40): on a
proper curve, a nonzero section of an invertible sheaf that vanishes at a
point forces positive degree. Its degree-zero contrapositive must concern
the specified determinant section.

## The concrete construction now proved

For an actual module sheaf L with genuine line charts, the core constructs
the actual dual evaluation L-dual -> O at a specified global section s.
On an integral scheme, nonzero generic germ proves this map monic and its
actual local equations regular. Here regular means a non-zero-divisor;
it does not mean invertible or nonzero in the residue field.

Finite line-chart covers with quasi-compact inclusions construct an actual
global ideal and closed zero subscheme D, with exact chart restrictions and
cover independence. The actual image module I is identified with L-dual.
Its dual Hom(I,O) is locally free and finitely presented, and a constructed
isomorphism Hom(I,O) -> L carries the inclusion I -> O, viewed as a global
dual section, to the specified s. The image module and global ideal are
explicitly linked by their actual affine-chart ideal data.

The determinant application supplies these line charts from the original
rank-n bundle charts and supplies generic nonzeroness from independence of
the actual specified generic germs. See
[DeterminantZeroDivisor.lean](Normalizer/DeterminantZeroDivisor.lean) and
[SectionIdealBundle.lean](Normalizer/SectionIdealBundle.lean).

This supplies concrete ingredients of
[Stacks Lemma 31.15.10(2)](https://stacks.math.columbia.edu/tag/01X0).
It is not a general bundled effective-Cartier-divisor/O(D) API, nor a proof
of the full two-way correspondence and uniqueness assertion on arbitrary
schemes. No global IdealSheafData-to-Modules functor is supplied; the ideal
module of this constructed D is linked by the proved chart comparisons.

## Exact next geometric lemma

Let p : X -> Spec(k) be a proper integral curve, let s have nonzero generic
germ in a line bundle, and let i : D -> X be its constructed zero subscheme.
Prove that the actual composite i followed by p is finite.

This is the finiteness step of
[Stacks Lemma 33.44.9](https://stacks.math.columbia.edu/tag/0AYY). It requires
proving that the constructed zero scheme has dimension at most zero and
using properness. Neither conclusion is currently a formal theorem for
this constructed D. The finite quasi-compact chart inputs also need to be
obtained from the actual curve and bundle data when applying this core.

## Degree and positivity remain after finiteness

One must construct actual curve degree, prove that the line bundle degree
equals the degree of this zero scheme, and show that a nonempty finite
zero scheme has positive degree. The established line degree is the
Euler-characteristic difference in
[Stacks Definition 33.44.1](https://stacks.math.columbia.edu/tag/0AYR).
Defining it as the length of the cokernel of this chosen section would
omit the required comparison with that established degree.

The pinned library has additive sheaf cohomology, module length and
exact-sequence length formulas. The current core has not assembled proper
coherent cohomology finiteness, dimension-one vanishing, coherent Euler
additivity and the zero-dimensional-support comparison for these actual
scheme module sheaves. The cited comparison uses
[coherent Euler additivity](https://stacks.math.columbia.edu/tag/08AA) and
[zero-dimensional support](https://stacks.math.columbia.edu/tag/0AYT).

These are missing formalizations of written mathematical dependencies.
No degree function tailored to the conclusion, positivity assumption,
abstract cohomology dimensions or replacement nonvanishing assumption has
been inserted into the proved core. The complete degree/nonvanishing
theorem and section bound h0(E/M) <= 4 remain unformalized.
