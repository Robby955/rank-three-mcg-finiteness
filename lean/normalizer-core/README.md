# Normalizer boundary laws in Lean

This package proves boundary-cocycle algebra, exhaustive algebraic `sl₃`
normalizer reduction, and supporting sheaf and generic-stalk results in Lean 4.
It does not formally verify the candidate rank-three finite-image theorem,
the square endpoint, or a genus-three result.

The core has 875 named theorems, 1230 audited named declarations, and 84
examples. The proofs use only `propext`, `Classical.choice`, and `Quot.sound`.
There are no proof placeholders or custom axioms in this package.
See the [verification record](VERIFICATION.md) for the scope of the checks
and the [cohomology review guide](COHOMOLOGY_REVIEW.md) for the new proof chain.

The latest slice constructs an actual finite map X -> P1_k on proper
normal integral curves of dimension at most one, and hence proves actual
H1(X,O_X) finite-dimensional over the original field. The smooth case
derives stalk normality. Curves normal away from one possibly singular
point are covered as well, and dimension zero is proved without reducedness.
No rational function, nonconstancy or cohomology dimension is supplied.
The earlier actual chart/Laurent comparison proves H1 finiteness for any
finite map, without source normality or integrality.

The unrestricted singular integral case still needs an affine neighborhood
containing its whole nonnormal locus, or normalization and cohomology
transfer. Higher vanishing and Euler/degree comparison remain separate.
See the [exact gap](DEGREE_NONVANISHING_GAP.md).

## Main results

Let `N(m)` be the normalizer of the line spanned by a nonzero matrix `m`
in `sl₃(F)`, over a characteristic-zero field `F`.

1. **Boundary law.** The overlap commutator calculation gives
   `∂[x,y] = λ(x)∂y − λ(y)∂x`. An injective linear boundary map then gives
   `[x,y] = λ(x)y − λ(y)x`. The algebraic theorem states its representative
   and linear-map hypotheses explicitly.
2. **Semisimple normalizer.** For `m = diag(1,1,−2)`, the actual quotient
   `N(m)/Fm` is identified with the three-dimensional `sl₂` model, with
   zero character. Every subspace satisfying the boundary law has
   dimension less than three.
3. **Minimal-nilpotent normalizer.** For `m = E₁₂`, the actual quotient
   `N(m)/Fm` has dimension four. Every subspace satisfying the law for
   its scalar-action character has dimension at most two.
4. **Sheaf constructions.** Local frames give a normalizer sheaf, its
   quotient bracket and character, and the canonical identification
   `N_E(M)/M ≅ ker(G → G ⊗ M∨)` for `G = E/M`, under the stated sheaf
   and trivialization hypotheses.
5. **Local freeness.** A finitely presented module sheaf with free stalks
   is locally free in mathlib's sense. On an integral scheme with regular
   local rings of dimension at most one, finite presentation and
   torsion-free stalks suffice. The open cover and local generators are
   constructed in the proof.

6. **Exhaustive algebraic reduction.** Every nonzero traceless rank-three
   matrix over a characteristic-zero field satisfies the proved obstruction
   under the precise boundary-lift hypotheses. The Jordan reductions,
   conjugacy and field-extension passage are proved.
7. **Curve support.** Actual finite-presentation, saturation and smooth-curve
   data give local freeness of the actual quotient. Global regular functions
   give constant scalar characters under the stated properness hypotheses.
   Actual generic quotient comparisons preserve bracket and character.
8. **Exterior stalks.** A genuine rank-n bundle chart gives an actual
   rank-one chart of the top exterior sheaf and an isomorphism between its
   stalk and the top exterior power of the original stalk. The isomorphism
   sends the specified exterior section germ to the wedge of its germs.
9. **Specified section.** Independence of the actual generic germs over the
   function field implies that their specified exterior section is nonzero.
   This does not infer generic independence from base-field independence or
   prove nonvanishing at every point.

10. **Zero ideal and inverse module.** Finite genuine line-chart covers with
    quasi-compact inclusions construct the actual global zero ideal and closed
    subscheme, independent of the chosen cover. On an integral scheme, generic
    nonzeroness gives regular local equations and monic dual evaluation.
    The dual of its actual image ideal module is identified with the original
    line module, carrying the canonical inclusion section to the specified
    section. The determinant specialization constructs its line charts from
    actual rank-n bundle charts.

11. **Finite zero scheme.** On a proper integral curve, a nonzero global
    line-bundle section and genuine pointwise charts construct a finite
    quasi-compact cover and a finite actual zero scheme D. A zero of the
    specified section gives positive dimension of Gamma(D,O_D), with its
    actual base-field action and full nilpotent structure retained.

12. **Actual scalar exact sequence.** The cokernel of the actual dual
    evaluation is identified with the actual pushed-forward structure module
    of D, preserving the quotient map. For a nonzero line section on an
    integral scheme, this gives `0 -> L-dual -> O_X -> i_*O_D -> 0` in
    mathlib's `ShortComplex.ShortExact`. The determinant specialization is
    included; affine exactness and stalk surjectivity are derived.

13. **Actual line exact sequence.** The original restriction map is identified
    as the cokernel of multiplication by the specified section. For nonzero s
    on an integral scheme, `0 -> O_X -> L -> i_*(L restricted to D) -> 0`
    is short exact. The determinant case is included; on a proper scheme,
    the finite chart cover is constructed from pointwise line charts.

14. **Intrinsic zero-scheme cohomology.** Every abelian sheaf on a discrete
    space has zero higher cohomology. Actual finiteness of the zero scheme
    supplies discreteness, so this applies to the constructed D, including
    its nonreduced structure.

15. **Ambient cokernel cohomology.** Closed direct image has the same actual
    abelian cohomology as its source, naturally and compatibly with global
    sections in degree zero. Thus the specified line-section cokernel on a
    proper integral curve has zero positive-degree cohomology. Its finite
    chart cover and zero-scheme finiteness are derived; the determinant
    specialization uses actual generic independence and pointwise bundle charts.

16. **Actual cohomology sequence.** Forgetting module structure preserves
    the section short exact sequence. Its extension class gives the canonical
    connecting map, and the six-object H⁰-to-H¹ segment is exact at its four
    interior terms, with the actual section and restriction maps. H⁰
    injectivity and H¹ surjectivity on the finite-type integral curve are proved.

17. **Restricted-line dimension.** Genuine line charts on a finite scheme
    construct a global trivialization, including on nonreduced and disconnected
    schemes. Its actual section dimension equals the global-function dimension,
    with the specified base-field action. The actual section cokernel and its
    H⁰ inherit this comparison; a zero gives positive dimension. All its
    cohomology groups are finite, with positive degrees zero.

18. **Cohomology scalars and line H⁰.** Actual scalar endomorphisms construct
    the base-field action on sheaf cohomology. The induced maps, H⁰-to-sections
    comparison and actual connecting map are linear. On a proper integral
    curve over an algebraically closed field, every genuine line bundle has
    finite-dimensional actual sections and H⁰, without supplying a nonzero section.

19. **Finite H¹ kernel and dimension balance.** The actual H¹ section map
    has finite kernel; finiteness of H¹(O_X) and H¹(L) is equivalent. On the
    proper integral curve over an algebraically closed field, the exact
    balance is h⁰(L) + dim ker(H¹(O_X) -> H¹(L)) = 1 + dim Gamma(D,O_D).
    Neither whole H¹ space is assumed finite.

20. **Terminal cohomology comparison.** The actual cohomology presheaf at a
    terminal object is naturally equivalent to sheaf cohomology in every
    degree, with the specified degree-zero evaluation formula.

21. **Slice cohomology comparison.** On a small Grothendieck site,
    `F.H' n U ≃+ (F.over U).H n` is constructed in every degree. The actual
    direct-sum extension, sheaf adjunction and exactness are proved. Naturality
    and degree-zero evaluation on the identity generator are proved; examples
    specialize to scheme opens and compare with the terminal result.

22. **Actual affine H¹ vanishing.** Every associated module sheaf on
    `Spec R` has zero first cohomology in the category of all abelian sheaves,
    for every commutative ring and every module. The same holds for every
    actual quasicoherent module sheaf on `Spec R`. The proof solves finite
    principal-open difference cocycles, glues corrected local lifts, and uses
    the canonical injective presentation and Ext exact sequence. No
    noetherian, finite-generation or characteristic hypothesis is needed.

23. **Actual affine opens.** Ambient-open cohomology agrees in every degree
    with cohomology of the actual restricted module, linearly over the
    structure field. Every quasicoherent module sheaf has zero H1 on each
    actual affine open. The cokernel example derives quasicoherence from
    finite presentation.
24. **Two-affine presentation.** A supplied actual cover by two affine opens
    gives a linear quotient presentation of global H1 through the original
    Mayer-Vietoris boundary. Its kernel consists of restriction differences.
    This constructs neither a curve cover nor quotient finiteness.

The degree/nonvanishing implication is still unformalized. Actual H¹(O_X)
finiteness, the remaining curve vanishing and Euler comparison with established
line-bundle degree remain to be formalized.
The proved dimension of Gamma(D,O_D) is not a definition of line degree.
These results are not a general bundled effective-Cartier-divisor
or O(D) API. See [the exact gap](DEGREE_NONVANISHING_GAP.md) and
[the current checkpoint](ZERO_DIVISOR_CHECKPOINT.md).
The required curve sections and representation-derived geometric data remain
application obligations. Overall formalization verdict: **PARTIAL**.

## Read and check

Start with [Flagship.lean](Normalizer/Flagship.lean) for the matrix quotient
obstructions and [Boundary.lean](Normalizer/Boundary.lean) for the abstract
boundary law. [ExteriorStalkComparison.lean](Normalizer/ExteriorStalkComparison.lean)
and [DeterminantGenericNonzero.lean](Normalizer/DeterminantGenericNonzero.lean)
contain the exterior interfaces. [DeterminantZeroDivisor.lean](Normalizer/DeterminantZeroDivisor.lean)
connects their specified section to the zero-ideal and inverse-module constructions.
[SectionZeroFinite.lean](Normalizer/SectionZeroFinite.lean) proves actual
finiteness and positive zero-scheme function dimension.
[SectionZeroExact.lean](Normalizer/SectionZeroExact.lean) contains the actual
scalar short exact sequence. [OVERVIEW.md](OVERVIEW.md) explains the dependency structure
and the remaining proof obligations. [CORRESPONDENCE.md](CORRESPONDENCE.md)
maps every named theorem to its mathematical role in the public manuscript.

Install [elan](https://github.com/leanprover/elan#installation), Git, and
Python 3.10 or newer. From this directory:

```sh
lake exe cache get
python3 scripts/verify.py
python3 scripts/check_correspondence.py
```

The toolchain is Lean `4.34.0-rc2`; mathlib is pinned to
`7974e751bece493b6ff508039423ca9fa2452fa8`. Keep `lean-toolchain` and
`lake-manifest.json` intact. The cache command downloads compiled mathlib
dependencies; it does not supply proofs for this package's modules.

The verifier builds both library targets, generates `AxiomAudit.lean`,
runs `#print axioms` for each named declaration, rejects unexpected axioms
and warnings, and writes logs and source hashes to `receipts/`.
The examples are compiled as part of the library.

To check the exact distributed files, use `sha256sum -c SHA256SUMS`
on Linux or `shasum -a 256 -c SHA256SUMS` on macOS. For development,
rebuild and regenerate the manifest after intentional changes.

## Scope and attribution

The source correspondence is fixed to public repository commit
`12f81e2852e0a8e71f16777d9eb9c7bc8916e6df`. The candidate manuscript
develops its arguments from the work of Aaron Landesman and Daniel Litt;
this package does not formalize their complete theorem or claim those
published results as new. General library support results are distinguished
from the manuscript's geometric assertions in the correspondence table.

The package is licensed under [Apache-2.0](LICENSE). See [NOTICE](NOTICE)
for attribution and dependency licensing. The surrounding manuscript
retains its existing license and candidate status.
