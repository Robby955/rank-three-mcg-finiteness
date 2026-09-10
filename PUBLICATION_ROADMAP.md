# Formalization and publication roadmap

This local continuation starts from merged public commit
`a7544c5b9136dd88d6741188a7be531d49bbace2` (PR #7), whose package contained
472 theorems, 679 audited declarations and 48 examples. The current local
package contains 591 theorems, 836 audited declarations and 54 examples.
The local zero-ideal commit `d5cc96d0dcf8af6a42a047463a7a75c924680926`
contained 547 theorems, 791 declarations and 52 examples. This finiteness
step adds 44 theorems, one construction and two examples. Counts describe
coverage, not completion of the candidate
representation theorem. The new continuation has not been pushed or tested
by hosted CI.

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
| Zero subscheme | Finite genuine line charts with quasi-compact inclusions construct the global ideal and closed subscheme, with exact restrictions and cover independence. |
| Regularity | On an integral scheme, nonzero generic germ proves regular local equations and actual monic dual evaluation. |
| Inverse ideal module | The dual of the actual image ideal module is locally free, finitely presented and canonically isomorphic to the original line, carrying the inclusion section to the specified section. |
| Global-to-generic injection | Genuine pointwise line charts on an integral scheme prove global section nonzeroness equivalent to nonzero generic germ. |
| Finite charts and zero scheme | Proper curve and genuine pointwise line charts construct a finite quasi-compact chart cover. A nonzero specified section has an actual zero scheme finite over the field. |
| Positive zero-scheme function dimension | A zero of the specified section gives nonempty D and positive finite dimension of Gamma(D,O_D), using the actual structure morphism. The determinant specialization is proved. |

## Next mathematical construction

Construct and prove the actual short exact sequence
`0 -> O_X --s--> L -> i_*(L|D) -> 0` for the constructed zero scheme D.
Then prove that its Euler-characteristic comparison identifies the
established line-bundle degree with dim_k Gamma(D,O_D). The finiteness and
positive function-dimension ingredients of
[Stacks Lemma 33.44.9](https://stacks.math.columbia.edu/tag/0AYY) are now
formalized. The remaining degree comparison is required for the desired
specified-section implication in
[Stacks Lemma 33.44.12(2)](https://stacks.math.columbia.edu/tag/0B40).

The current proofs construct the concrete zero ideal and inverse image-ideal
module. They do not expose a general bundled effective-Cartier-divisor/O(D)
API or prove the full equivalence and uniqueness statement of Stacks 31.15.10.
The finite quasi-compact charts are now constructed from genuine pointwise
line charts on the proper curve. The actual representation-derived bundle
and curve still need to be instantiated. See the [exact gap](lean/normalizer-core/DEGREE_NONVANISHING_GAP.md)
and [local checkpoint](lean/normalizer-core/ZERO_DIVISOR_CHECKPOINT.md).

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
