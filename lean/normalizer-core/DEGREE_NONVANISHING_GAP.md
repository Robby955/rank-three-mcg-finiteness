# Exact remaining degree/nonvanishing interface

The requested theorem is the implication in
[Stacks Lemma 33.44.12(2)](https://stacks.math.columbia.edu/tag/0B40): on a
proper curve, a nonzero section of an invertible sheaf that vanishes at a
point forces its degree to be positive. Its degree-zero contrapositive
must concern the specified determinant section, not merely the existence
of some abstract trivialization of its line bundle.

## First missing construction on the cited proof route

Given an actual invertible module sheaf L and a regular specified global
section s, construct its effective Cartier zero divisor D = Z(s), the
actual invertible module O(D), and an isomorphism O(D) ≅ L carrying the
canonical section to s. This is the construction in
[Stacks Lemma 31.15.10(2)](https://stacks.math.columbia.edu/tag/01X0).

The pinned mathlib has ideal-sheaf and subscheme constructions, but this
audit found no effective-Cartier-divisor/O(D) interface connecting them to
the actual invertible module and its specified section. Local equations
alone do not supply that missing global construction and comparison.

Next one must construct actual curve degree and prove
deg L = deg D, and that a nonempty effective divisor has positive degree.
The established degree is the Euler-characteristic difference in
[Stacks Definition 33.44.1](https://stacks.math.columbia.edu/tag/0AYR), and
the line-bundle/divisor equality is
[Stacks Lemma 33.44.9](https://stacks.math.columbia.edu/tag/0AYY).
Defining degree as the total length of the cokernel of this chosen section
would omit the substantive comparison with that established degree.

## Why the Euler-characteristic route does not yet close it

The library contains additive sheaf cohomology (`Sheaf.H`), module length
and exact-sequence length formulas. A generic complex Euler-characteristic
definition also exists. The audit found no assembled proper-coherent
cohomology finiteness, dimension-one vanishing, coherent Euler additivity
and zero-dimensional-support comparison applicable to these actual scheme
module sheaves. Those are needed for the alternative proof through
0 → O → L → coker(s) → 0.

The cited steps are [coherent Euler additivity](https://stacks.math.columbia.edu/tag/08AA)
and [zero-dimensional support](https://stacks.math.columbia.edu/tag/0AYT).
These are exact mathematical dependencies, not new formal hypotheses in
the proved core. This is a missing formalization, not a refutation of the
published degree lemma or of the manuscript's written implication.

## Fail-closed boundary

The exterior comparison and generic nonzeroness are separate from this
degree argument. No degree function with a tailored definition, positivity
axiom, arbitrary cohomology dimensions or substitute nonvanishing assumption
has been added. The complete degree/nonvanishing theorem remains unformalized.
The requested sequence therefore cannot yet be described as completed or
published as a completed determinant argument.
