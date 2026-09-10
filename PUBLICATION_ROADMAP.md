# Formalization and publication roadmap

This continuation extends public commit
`87cb21ff4f83d56d326793433ef6569a2d6e81bd`. The previous public milestone
contained 233 theorems, 340 audited declarations and 35 examples. The current
package contains 472 theorems, 679 audited declarations and 48 examples.
These counts describe the scope of checked declarations, not completion
of the candidate representation theorem.

## Completed formal interfaces

| Interface | Checked scope |
|---|---|
| Normalizer algebra | Exhaustive characteristic-zero traceless 3×3 matrix reduction and the boundary-law obstruction. |
| Actual curve quotient support | Finite presentation, stalk exactness, saturation-to-torsion-freeness, smooth-stalk regularity and local-freeness assembly under actual bundle and curve inputs. |
| Character and generic quotient | Actual constants and scalar-character constructions; actual generic quotient comparisons preserving bracket and character under the stated ambient identification. |
| Generic dimension | Preservation from an actual free inclusion or actual trivialized subsheaf; no inference from base-field independence alone. |
| Exterior line | Genuine rank-n bundle charts construct rank-one charts of the actual top exterior sheaf. |
| Exterior stalk | The canonical actual stalk comparison is an isomorphism on genuine rank-n charts and preserves the specified wedge of section germs. |
| Specified determinant | Function-field independence of the actual generic germs proves the specified exterior section has nonzero generic germ and is globally nonzero. |

## Next mathematical construction

Formalize the effective Cartier zero divisor of a regular specified section
of an actual invertible sheaf and construct the section-preserving
identification of its associated invertible sheaf with the original one.
This is the first missing construction on the proof route for
[Stacks Lemma 33.44.12(2)](https://stacks.math.columbia.edu/tag/0B40).
Then construct actual curve degree, prove its divisor-degree comparison,
and derive that a nonzero section of a degree-zero line bundle has no zeros.
See the [precise dependency gap](lean/normalizer-core/DEGREE_NONVANISHING_GAP.md).

The construction of the actual saturated evaluation subbundle and its
degree zero, the rank-two section estimate, the global boundary application
and assembly of `h⁰(E/M) ≤ 4` remain separate. After that come the residual
representation inputs, exhaustive genus-five branch coverage and upstream
fixed-part, descent, HN, Hodge-theoretic, arithmetic and finiteness arguments.

## Verification and release boundary

The local checks and their reproducible commands are in the
[verification record](lean/normalizer-core/VERIFICATION.md). The CI workflow
regenerates the axiom audit and checks hashes and correspondence. Its hosted
results are recorded in the pull request checks and
[workflow runs](https://github.com/Robby955/rank-three-mcg-finiteness/actions/workflows/lean-normalizer.yml).
Those checks establish replay of the listed formal propositions. The missing
geometric hypotheses and external mathematical review remain separate.

The degree/nonvanishing step is not a completed formal theorem. This update
is a **PARTIAL formalization milestone**. The manuscript labels stay fixed:
Landesman–Litt's strict range is **PUBLISHED**; the equality endpoint and
rank three for genus at least five are **CANDIDATE**; genus four is
**CANDIDATE conditional on B1–B5**; genus three and the general
`g ≥ r²−4` range are **OPEN**. No manuscript, tag or release is changed.
