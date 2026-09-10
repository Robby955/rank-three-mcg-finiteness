# Exact remaining degree/nonvanishing interface

The target is the specified-section implication of
[Stacks Lemma 33.44.12(2)](https://stacks.math.columbia.edu/tag/0B40): on a
proper curve, a nonzero section of an invertible sheaf that vanishes at a
point forces positive degree. Its degree-zero contrapositive must concern
the specified determinant section.

## The concrete construction now proved

For an actual module sheaf L with genuine line charts, the core constructs
the actual dual evaluation L-dual -> O at a specified global section s.
On an integral scheme, genuine pointwise line charts prove that the global
section map into the generic stalk is injective. Thus a nonzero global
section has nonzero generic germ. That proves dual evaluation monic and its
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

## Actual finiteness and positive function dimension now proved

For a proper integral curve p : X -> Spec(k), a nonzero global section s
and genuine pointwise line charts, the core constructs a finite
quasi-compact chart cover and proves its actual zero scheme D finite over k.
The proof derives generic-point exclusion, dimension at most zero, and
finiteness of the actual morphism D -> Spec(k). It retains nilpotents and
includes the empty zero scheme. Properness is sufficient; the fixed-cover
finiteness result only needs X of finite type over k and dimension at most one.

Under the scalar action induced by that actual morphism, Gamma(D,O_D) is
finite-dimensional, its dimension is zero exactly when D is empty, and a
zero of the specified section gives strictly positive dimension. The zero
condition is noninvertibility of the actual local equation in the local
ring. Its equivalence with membership in the constructed support is proved.
The determinant specialization constructs its line charts and generic
nonzeroness from the actual rank-n charts and generic independence. See
[SectionZeroFinite.lean](Normalizer/SectionZeroFinite.lean),
[SectionZeroLocus.lean](Normalizer/SectionZeroLocus.lean) and
[LineGenericInjection.lean](Normalizer/LineGenericInjection.lean).

These are finiteness and function-dimension ingredients of
[Stacks Lemma 33.44.9](https://stacks.math.columbia.edu/tag/0AYY).
They do not yet identify a line-bundle degree with this dimension.

## Exact next geometric lemma and degree comparison

For the actual closed immersion i : D -> X, construct the restriction and
direct-image module sheaves and prove the actual short exact sequence

```text
0 -> O_X --s--> L -> i_*(L|D) -> 0.
```

The next implementation entry point is the scalar comparison
`cokernel (schemeSectionDualEvaluation L s) ≅ i_* O_D`, compatible with
the actual quotient maps. The canonical map O_X -> i_* O_D already exists
as `SheafOfModules.unitToPushforwardObjUnit i.toRingCatSheafHom`.
Mathlib's `IdealSheafData.subschemeι_app_surjective` and
`ker_subschemeι_app`, together with the proved section ideal chart
comparisons, supply the local quotient-ring data. The remaining work is
to assemble that data into the actual module-sheaf cokernel comparison.

For L, the canonical map to i_*(L|D) is already the unit of
`Scheme.Modules.pullbackPushforwardAdjunction i`. Its identification as
the cokernel of `schemeSectionHom L s` has not been proved. Genuine line
frames should transport the scalar comparison locally. Categorical
cokernel exactness alone does not establish this geometric identification.

Then prove that its Euler-characteristic comparison identifies the
established degree of L with dim_k Gamma(D,O_D). This is the missing bridge
from the proved positive function dimension to positive line-bundle degree.
The established line degree is the Euler-characteristic difference in
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
No degree function tailored to the conclusion, line-degree positivity assumption,
abstract cohomology dimensions or replacement nonvanishing assumption has
been inserted into the proved core. The complete degree/nonvanishing
theorem and section bound h0(E/M) <= 4 remain unformalized.
