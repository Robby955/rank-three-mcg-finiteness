# Normalizer boundary laws in Lean

This package proves boundary-cocycle algebra, exhaustive algebraic `sl₃`
normalizer reduction, and supporting sheaf and generic-stalk results in Lean 4.
It does not formally verify the candidate rank-three finite-image theorem,
the square endpoint, or a genus-three result.

The core has 591 named theorems, 836 audited named declarations, and 54
examples. The proofs use only `propext`, `Classical.choice`, and `Quot.sound`.
There are no proof placeholders or custom axioms in this package.
See the [verification record](VERIFICATION.md) for the scope of the checks.

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

The degree/nonvanishing implication is still unformalized. The next geometric
construction is the actual sequence `0 -> O_X --s--> L -> i_*(L|D) -> 0`,
followed by its Euler-characteristic comparison with line-bundle degree.
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
finiteness and positive zero-scheme function dimension. [OVERVIEW.md](OVERVIEW.md) explains the dependency structure
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
