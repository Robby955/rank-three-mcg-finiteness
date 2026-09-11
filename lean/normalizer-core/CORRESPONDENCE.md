# Public manuscript-to-Lean correspondence

All declaration names have the prefix `Normalizer.`. This table covers all
855 named theorems and 355 named constructions;
all 1210 declarations are included in `AxiomAudit.lean`.

The source is the public repository at commit
`12f81e2852e0a8e71f16777d9eb9c7bc8916e6df`:

- **P**: [genus-five manuscript](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L915-L1036), proposition `prop:normalizer-boundary`, lines 915–1036. Line numbers elsewhere prefixed P refer to the same file.
- **A**: [normalizer boundary-cocycle discussion](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/LOAD_BEARING_AUDIT.md#L37-L95), lines 37–95.
- **E1**: [adjoint-universal proposition](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L1038-L1095), lines 1038–1095.
- **E2**: [the `(S,q)=(2,10)` branch](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L1928-L2016), lines 1928–2016.

“Support” means a general lemma used to formalize that step, rather than
an assertion that the full geometric statement is proved. Reconstructions
and alternative proof routes are labeled. The exact Lean hypotheses in
the linked declarations govern every statement; the coverage column is
an explanation, not a replacement for those hypotheses.

The two explicit matrix results hold over characteristic-zero fields.
Their coordinate quotients are identified with the actual matrix
normalizer quotients. The expanded package also proves exhaustive algebraic normalizer reduction
and actual generic comparison results with their stated geometric inputs.
The complete section-bound and representation application remain unformalized.
The [overview](OVERVIEW.md) records the current geometric gaps; no finite
arithmetic script serves as a proof in this package.

Source SHA-256 values:

```text
2cc61289a02074c4bd42cdbe337ca5dca922bc83299ccf56ca485d6b65f2d6c3  manuscript/rank3_genus5_reader.tex
b64fe79e47d5862c0bf2b77ca3f3cb06bd6e1289ad6721e9b8d23b5305aa622b  LOAD_BEARING_AUDIT.md
```


## ActualNormalizerQuotient

| Source / mathematical role | Lean declaration | Kind | Exact coverage |
|---|---|---|---|
| General support; exact hypotheses in the linked declaration | [`SlThree`](Normalizer/ActualNormalizerQuotient.lean#L14) | abbrev | Mathlib's actual special linear Lie subalgebra of three-by-three matrices. |
| General support; exact hypotheses in the linked declaration | [`SlThreeLineQuotient`](Normalizer/ActualNormalizerQuotient.lean#L17) | abbrev | Mathlib's actual Lie normalizer quotient by the frame line ideal. |
| General support; exact hypotheses in the linked declaration | [`slThreeLineCharacter`](Normalizer/ActualNormalizerQuotient.lean#L21) | def | The actual descended scalar-action character on that quotient. |
| General support; exact hypotheses in the linked declaration | [`slThree_quotient_boundary_lift_exists`](Normalizer/ActualNormalizerQuotient.lean#L28) | theorem | Splits the actual quotient map linearly, restricts to the supplied subspace, and proves all four MatrixBoundaryLift properties from its actual boundary law. |
| General support; exact hypotheses in the linked declaration | [`slThree_quotient_boundary_finrank`](Normalizer/ActualNormalizerQuotient.lean#L91) | theorem | Over any characteristic-zero field, every subspace of the actual line-normalizer quotient satisfying its actual character boundary law has dimension at most two; no chosen lifts or normal forms are inputs. |

## AffineFreeNeighborhood

| Source / mathematical role | Lean declaration | Kind | Exact coverage |
|---|---|---|---|
| General support; exact hypotheses in the linked declaration | [`affineLocalizationMap`](Normalizer/AffineFreeNeighborhood.lean#L17) | def | AffineFreeNeighborhood |
| General support; exact hypotheses in the linked declaration | [`affineLocalizationSheaf`](Normalizer/AffineFreeNeighborhood.lean#L25) | def | AffineFreeNeighborhood |
| General support; exact hypotheses in the linked declaration | [`affineLocalizationSections`](Normalizer/AffineFreeNeighborhood.lean#L36) | def | AffineFreeNeighborhood |
| General support; exact hypotheses in the linked declaration | [`affineLocalizationToSections`](Normalizer/AffineFreeNeighborhood.lean#L62) | def | AffineFreeNeighborhood |
| General support; exact hypotheses in the linked declaration | [`affineLocalizationSectionsIso`](Normalizer/AffineFreeNeighborhood.lean#L74) | def | AffineFreeNeighborhood |
| General support; exact hypotheses in the linked declaration | [`affineTildeRestrictionIso`](Normalizer/AffineFreeNeighborhood.lean#L87) | def | AffineFreeNeighborhood |
| Actual chart support for [P 936](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L936) | [`affineLocalizationMap_opensRange`](Normalizer/AffineFreeNeighborhood.lean#L96) | theorem | The image of Spec of localization away from r is the actual principal open D(r). |
| General support; exact hypotheses in the linked declaration | [`affineLocalizationFreeSheafIso`](Normalizer/AffineFreeNeighborhood.lean#L101) | def | AffineFreeNeighborhood |
| Actual affine trivialization support for [P 936](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L936) | [`affineLocalization_finiteFree_trivialization`](Normalizer/AffineFreeNeighborhood.lean#L112) | theorem | A finite module with free localization gives a finite free-sheaf isomorphism on the actual localization chart; the localization is explicitly nontrivial. |
| Associated-sheaf neighborhood step supporting [P 936](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L936) | [`affineStalk_exists_finiteFree_neighborhood`](Normalizer/AffineFreeNeighborhood.lean#L122) | theorem | A free actual stalk of tilde(M), with M finitely presented, produces a principal affine chart containing the point and an actual finite free-sheaf trivialization. |

## AffineLocallyFree

| Source / mathematical role | Lean declaration | Kind | Exact coverage |
|---|---|---|---|
| General support; exact hypotheses in the linked declaration | [`affineFreeSheafIso`](Normalizer/AffineLocallyFree.lean#L19) | def | AffineLocallyFree |
| Affine local-trivialization support for [P 936](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L936) | [`affineFreeSheaf_isLocallyFree`](Normalizer/AffineLocallyFree.lean#L26) | theorem | A free module's actual associated sheaf is locally free, via its basis and tilde of the free module. |
| Affine finite-type support for [P 936](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L936) | [`affineFreeSheaf_isFiniteType`](Normalizer/AffineLocallyFree.lean#L32) | theorem | A finite free module's actual associated sheaf has finite local generators. |
| Affine PID case of [P 936](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L936) | [`affineSaturatedQuotient_trivialization`](Normalizer/AffineLocallyFree.lean#L46) | theorem | Constructs an actual global free-sheaf isomorphism with a finite index type for the scalar-saturated quotient over Spec of a PID. |
| Affine PID case of [P 936](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L936) | [`affineSaturatedQuotient_finiteLocallyFree`](Normalizer/AffineLocallyFree.lean#L56) | theorem | The actual affine sheaf cokernel is both locally free and finite type. No PID-chart assumption for smooth curves is used. |

## AffinePresentedNeighborhood

| Source / mathematical role | Lean declaration | Kind | Exact coverage |
|---|---|---|---|
| Presented-affine neighborhood step supporting [P 936](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L936) | [`affinePresentation_exists_finiteFree_neighborhood`](Normalizer/AffinePresentedNeighborhood.lean#L18) | theorem | An actual affine sheaf with a finite global presentation and a free actual stalk has a principal affine finite free-sheaf neighborhood. |

## AffineQuotient

| Source / mathematical role | Lean declaration | Kind | Exact coverage |
|---|---|---|---|
| General support; exact hypotheses in the linked declaration | [`affineCokernelIso`](Normalizer/AffineQuotient.lean#L20) | def | AffineQuotient |
| Affine quotient support for [P 936](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L936) | [`affineCokernelIso_projection`](Normalizer/AffineQuotient.lean#L26) | theorem | The actual sheaf cokernel comparison preserves the projection induced by the module cokernel. |
| Affine saturation support for [P 936](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L936) | [`quotient_isTorsionFree_of_saturated`](Normalizer/AffineQuotient.lean#L33) | theorem | Over a domain, explicit scalar saturation of S proves torsion freeness of the actual module quotient M/S. |
| Affine PID case of [P 936](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L936) | [`quotient_free_of_saturated`](Normalizer/AffineQuotient.lean#L48) | theorem | A finite module quotient with explicit scalar saturation is free over a PID, using mathlib's standard finite torsion-free theorem. |
| General support; exact hypotheses in the linked declaration | [`affineSubmoduleQuotientIso`](Normalizer/AffineQuotient.lean#L57) | def | AffineQuotient |
| Actual affine quotient support for [P 936](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L936) | [`affineSubmoduleQuotientIso_projection`](Normalizer/AffineQuotient.lean#L66) | theorem | The actual sheaf cokernel of tilde(S -> M) is identified with tilde(M/S) by the canonical quotient projection. |

## AffineStalks

| Source / mathematical role | Lean declaration | Kind | Exact coverage |
|---|---|---|---|
| General support; exact hypotheses in the linked declaration | [`affineStalkAlgebra`](Normalizer/AffineStalks.lean#L18) | def | AffineStalks |
| Local-ring action support for [P 936](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L936) | [`affineStalk_isScalarTower`](Normalizer/AffineStalks.lean#L26) | theorem | The ordinary base-ring action on the actual associated-sheaf stalk agrees with its actual local-ring action. |
| Affine free-stalk support for [P 936](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L936) | [`affineStalk_free_iff`](Normalizer/AffineStalks.lean#L34) | theorem | The ordinary module free locus is exactly the locus of free actual sheaf stalks over their actual local rings. |
| Finite-stalk support for [P 936](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L936) | [`affineStalk_finite`](Normalizer/AffineStalks.lean#L47) | theorem | The actual stalk of an associated finite module is finite over the actual local ring. |
| Affine neighborhood support for [P 936](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L936) | [`affineStalk_freeLocus_isOpen`](Normalizer/AffineStalks.lean#L57) | theorem | For a finitely presented module, the free-actual-stalk locus of its associated sheaf is open. |
| Module localization step supporting [P 936](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L936) | [`affineStalk_exists_free_localization`](Normalizer/AffineStalks.lean#L67) | theorem | A free actual stalk gives a free localization away from an element outside the prime, with the same rank. The separate sheaf comparison constructs the actual trivialization. |

## Boundary

| Source / mathematical role | Lean declaration | Kind | Exact coverage |
|---|---|---|---|
| [P 952–961](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L952-L961), arbitrary overlap sections | [`abelian_overlap_difference`](Normalizer/Boundary.lean#L14) | theorem | Uses [a,b]=0 and the two normalizer actions, without requiring constant scalar multiples of a line generator. |
| [P 952–961](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L952-L961); [A 46–54](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/LOAD_BEARING_AUDIT.md#L46-L54) | [`cech_commutator_difference`](Normalizer/Boundary.lean#L22) | theorem | Local overlap expansion with the convention Xj − Xi; derived from Lie algebra identities. |
| [P 957–966](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L957-L966); [A 48–54](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/LOAD_BEARING_AUDIT.md#L48-L54) | [`boundary_cocycle`](Normalizer/Boundary.lean#L35) | theorem | Apply a linear class map on a cocycle submodule. The representative equalities and constant scalars are explicit hypotheses; actual sheaf cohomology is not constructed. |
| [P 968–972](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L968-L972); [A 57–60](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/LOAD_BEARING_AUDIT.md#L57-L60) | [`quotient_boundary_law`](Normalizer/Boundary.lean#L58) | theorem | Injectivity of an ambient linear boundary map yields the bracket identity. |

## BoundaryBaseChange

| Source / mathematical role | Lean declaration | Kind | Exact coverage |
|---|---|---|---|
| Field-extension support for P 977–984 | [`boundaryCharacterBaseChange`](Normalizer/BoundaryBaseChange.lean#L18) | def | Actual tensor scalar extension of the linear character. |
| Field-extension support for P 977–984 | [`boundaryCharacterBaseChange_tmul`](Normalizer/BoundaryBaseChange.lean#L22) | theorem | Character formula on pure tensors. |
| Field-extension support for P 977–984 | [`boundaryBracketBaseChange_tmul`](Normalizer/BoundaryBaseChange.lean#L28) | theorem | Bilinear bracket formula on pure tensors. |
| Field-extension support for P 977–984 | [`boundaryLaw_baseChange_span`](Normalizer/BoundaryBaseChange.lean#L36) | theorem | Proves the law on the larger-field span of tensor images. |
| Field-extension support for P 977–984 | [`boundaryLaw_baseChange_span_range`](Normalizer/BoundaryBaseChange.lean#L52) | theorem | Finite-generator form of the scalar-extended boundary law. |
| Field-extension support for P 977–984 | [`baseChange_one_tmul_linearIndependent`](Normalizer/BoundaryBaseChange.lean#L68) | theorem | Field extension preserves independence, by flatness of the actual tensor map. |
| Field-extension support for P 977–984 | [`baseChange_span_finrank`](Normalizer/BoundaryBaseChange.lean#L75) | theorem | The span of an independent finite family keeps its dimension under arbitrary field extension. |

## BoundaryScalarExtension

| Source / mathematical role | Lean declaration | Kind | Exact coverage |
|---|---|---|---|
| General support; exact hypotheses in the linked declaration | [`matrixBaseChange_trace`](Normalizer/BoundaryScalarExtension.lean#L31) | theorem | Trace-zero lift condition extends to every tensor. |
| General support; exact hypotheses in the linked declaration | [`matrixBaseChange_action`](Normalizer/BoundaryScalarExtension.lean#L40) | theorem | The canonically extended character is the actual action on the extended line for every tensor. |
| General support; exact hypotheses in the linked declaration | [`matrixBaseChange_boundary`](Normalizer/BoundaryScalarExtension.lean#L54) | theorem | Double tensor induction extends the boundary identity; on pure tensors the line coefficient becomes a*b times the original coefficient's image. |
| General support; exact hypotheses in the linked declaration | [`matrixBoundaryLift_baseChange`](Normalizer/BoundaryScalarExtension.lean#L100) | theorem | All four quotient-lift properties survive arbitrary field extension, including independence modulo the line. |
| General support; exact hypotheses in the linked declaration | [`traceless_matrix_boundary_lift_any_field`](Normalizer/BoundaryScalarExtension.lean#L112) | theorem | Extends the data to an algebraic closure, applies the exhaustive obstruction, and preserves the original dimension; algebraic closedness of the original field is unnecessary. |

## BoundarySpan

| Source / mathematical role | Lean declaration | Kind | Exact coverage |
|---|---|---|---|
| Algebra supporting P 978–979 | [`boundaryLaw_span`](Normalizer/BoundarySpan.lean#L10) | theorem | A bilinear boundary identity on a generating set holds on its full linear span. |
| Algebra supporting P 978–979 | [`boundaryLaw_span_image`](Normalizer/BoundarySpan.lean#L36) | theorem | Transports the identity to a semilinear image span with explicit bracket and character compatibility. |

## CyclicNormalizer

| Source / mathematical role | Lean declaration | Kind | Exact coverage |
|---|---|---|---|
| General support; exact hypotheses in the linked declaration | [`cyclic_matrix_boundary_lift`](Normalizer/CyclicNormalizer.lean#L15) | theorem | Full minimal-polynomial degree excludes a three-dimensional independent quotient lift; no boundary-bracket hypothesis is used in the proof. |

## CyclicVector

| Source / mathematical role | Lean declaration | Kind | Exact coverage |
|---|---|---|---|
| General support; exact hypotheses in the linked declaration | [`exists_polynomial_separating_vector`](Normalizer/CyclicVector.lean#L26) | theorem | Constructs a vector with the same polynomial annihilator as the endomorphism, using the polynomial-module structure theorem. |
| General support; exact hypotheses in the linked declaration | [`polynomial_evaluation_injective`](Normalizer/CyclicVector.lean#L40) | theorem | Evaluation at a separating vector is injective on the generated polynomial algebra. |
| General support; exact hypotheses in the linked declaration | [`separating_vector_linearIndependent_powers`](Normalizer/CyclicVector.lean#L56) | theorem | The first minimal-polynomial-degree powers of a separating vector are linearly independent. |
| General support; exact hypotheses in the linked declaration | [`exists_polynomial_cyclic_vector`](Normalizer/CyclicVector.lean#L75) | theorem | Full minimal-polynomial degree produces a cyclic vector in a finite-dimensional space. |
| General support; exact hypotheses in the linked declaration | [`centralizerEvaluation`](Normalizer/CyclicVector.lean#L100) | def | Linear evaluation map on the actual centralizer subalgebra. |
| General support; exact hypotheses in the linked declaration | [`centralizerEvaluation_injective`](Normalizer/CyclicVector.lean#L108) | theorem | A commuting endomorphism is determined by its value at a cyclic vector. |
| General support; exact hypotheses in the linked declaration | [`centralizer_finrank_le_of_natDegree_eq_finrank`](Normalizer/CyclicVector.lean#L131) | theorem | Bounds the dimension of the actual centralizer by the ambient representation dimension for full-degree minimal polynomial. |
| General support; exact hypotheses in the linked declaration | [`commuting_eq_zero_of_cyclic_vector`](Normalizer/CyclicVector.lean#L138) | theorem | A commuting endomorphism vanishing at a cyclic vector is zero. |
| General support; exact hypotheses in the linked declaration | [`cyclic_normalizer_lift_finrank`](Normalizer/CyclicVector.lean#L151) | theorem | Augmented evaluation gives dim W + 1 ≤ dim V, using a functional nonzero on the identity and vanishing on the operator and lifts. |

## DeterminantFrame

| Source / mathematical role | Lean declaration | Kind | Exact coverage |
|---|---|---|---|
| General support; exact hypotheses in the linked declaration | [`frameCoordinateMatrix`](Normalizer/DeterminantFrame.lean#L17) | def | Actual coordinate matrix with the proposed frame vectors as columns in a reference basis. |
| General support; exact hypotheses in the linked declaration | [`frameCoordinateMatrix_toMatrix`](Normalizer/DeterminantFrame.lean#L21) | theorem | The coordinate matrix represents the actual finite linear-combination map. |
| General support; exact hypotheses in the linked declaration | [`determinantFrameEquiv`](Normalizer/DeterminantFrame.lean#L28) | def | Constructed coefficient-to-vector linear equivalence from a unit coordinate determinant, including its inverse. |
| General support; exact hypotheses in the linked declaration | [`determinantFrameEquiv_apply`](Normalizer/DeterminantFrame.lean#L34) | theorem | The constructed equivalence applies coefficients by the actual finite linear combination. |
| General support; exact hypotheses in the linked declaration | [`frameCoordinateMatrix_isUnit_det_iff`](Normalizer/DeterminantFrame.lean#L40) | theorem | Unit determinant is equivalent to bijectivity of the actual finite coefficient map over a commutative ring. |
| General support; exact hypotheses in the linked declaration | [`frameCoordinateMatrix_isUnit_det_basis_iff`](Normalizer/DeterminantFrame.lean#L54) | theorem | The unit-determinant condition does not depend on the reference basis. |
| General support; exact hypotheses in the linked declaration | [`frameCoordinateMatrix_residue_det_ne_zero_iff`](Normalizer/DeterminantFrame.lean#L61) | theorem | Over a local ring, nonvanishing of the actual reduced coordinate determinant is equivalent to bijectivity of the coefficient map. |

## DeterminantGenericNonzero

| Source / mathematical role | Lean declaration | Kind | Exact coverage |
|---|---|---|---|
| Determinant/generic-stalk support | [`schemeExteriorGlobalSection_generic_ne_zero`](Normalizer/DeterminantGenericNonzero.lean#L18) | theorem | The specified exterior section has nonzero actual generic germ from function-field independence of the actual section germs; no triviality or degree assumption. |
| Determinant/generic-stalk support | [`schemeExteriorGlobalSection_ne_zero`](Normalizer/DeterminantGenericNonzero.lean#L33) | theorem | The actual specified global exterior section is nonzero under that generic independence hypothesis; for rank n this is the specified determinant section. |

## DeterminantSection

| Source / mathematical role | Lean declaration | Kind | Exact coverage |
|---|---|---|---|
| General support; exact hypotheses in the linked declaration | [`schemeExteriorPure_eq_det_smul`](Normalizer/DeterminantSection.lean#L18) | theorem | Actual local exterior product in the sheafification equals its determinant coefficient times the reference-basis exterior product. |
| General support; exact hypotheses in the linked declaration | [`schemeExteriorGlobalSection_local_det`](Normalizer/DeterminantSection.lean#L28) | theorem | The specified actual global exterior section satisfies its local determinant formula on every open with a basis of the section module; no local-freeness or degree conclusion is asserted. |

## DiagonalNormalizer

| Source / mathematical role | Lean declaration | Kind | Exact coverage |
|---|---|---|---|
| General support; exact hypotheses in the linked declaration | [`distinct_diagonal_matrix_boundary_lift`](Normalizer/DiagonalNormalizer.lean#L10) | theorem | Distinct diagonal entries force off-diagonal lift entries to vanish; two coordinates detect each trace-zero lift. |
| General support; exact hypotheses in the linked declaration | [`repeated_diagonal_sem_model`](Normalizer/DiagonalNormalizer.lean#L46) | theorem | Every nonzero trace-zero diagonal matrix with a repeated entry is explicitly a nonzero scalar multiple of a permutation of semM. |
| General support; exact hypotheses in the linked declaration | [`diagonal_matrix_boundary_lift`](Normalizer/DiagonalNormalizer.lean#L103) | theorem | Combines the distinct-entry exclusion with the checked semisimple model for every nonzero trace-zero diagonal matrix. |

## EtaleRegularity

| Source / mathematical role | Lean declaration | Kind | Exact coverage |
|---|---|---|---|
| Local algebra supporting P 936 | [`regularLocal_of_flat_unramified`](Normalizer/EtaleRegularity.lean#L14) | theorem | A flat, essentially finite type, formally unramified local map from a regular local ring has regular local target. Noetherianity is derived. |

## EvaluationFrame

| Source / mathematical role | Lean declaration | Kind | Exact coverage |
|---|---|---|---|
| General support; exact hypotheses in the linked declaration | [`evaluation_lift_eq_of_frame`](Normalizer/EvaluationFrame.lean#L21) | theorem | The canonical tensor evaluation factors through base change of the constant-coordinate map and the actual generic frame. |
| General support; exact hypotheses in the linked declaration | [`evaluation_lift_injective_of_frame`](Normalizer/EvaluationFrame.lean#L39) | theorem | Injective constant coordinates and generic frame imply injectivity of tensor evaluation by flatness and the proved factorization. |
| General support; exact hypotheses in the linked declaration | [`evaluation_range_finrank_of_frame`](Normalizer/EvaluationFrame.lean#L50) | theorem | Under the explicit frame data, the dimension of the actual evaluation range over K equals the section-space dimension over F. |
| General support; exact hypotheses in the linked declaration | [`evaluation_lift_injective_of_composite_frame`](Normalizer/EvaluationFrame.lean#L61) | theorem | Derives tensor-evaluation injectivity when the independent frame lies in a larger ambient fibre; no injectivity of the ambient map is required. |

## ExtensionDimension

| Source / mathematical role | Lean declaration | Kind | Exact coverage |
|---|---|---|---|
| E2 rank A≤1 and kernel estimate | [`extension_dimension_loss`](Normalizer/ExtensionDimension.lean#L16) | theorem | General linear bound dim V≤dim ker A+dim ker s when e is injective and s e A=0. |
| Reconstruction encompassing E1 and E2 | [`extension_kernel_lower_bound`](Normalizer/ExtensionDimension.lean#L32) | theorem | General d≥1 estimate dim ker A≥g−h under the displayed dimension hypotheses. |
| E2 dim ker A≥4 | [`degree_two_kernel_four`](Normalizer/ExtensionDimension.lean#L42) | theorem | Exact genus-five degree-two numerical specialization. |

## ExtensionNaturality

| Source / mathematical role | Lean declaration | Kind | Exact coverage |
|---|---|---|---|
| E2 zero-left extension diagram | [`connecting_zero_of_zero_left`](Normalizer/ExtensionNaturality.lean#L18) | theorem | Actual mathlib homology connecting map, for arbitrary short exact complexes. |
| E1 morphism identity; E2 s_*eA=0 | [`extension_block_annihilated`](Normalizer/ExtensionNaturality.lean#L29) | theorem | Derives the annihilation identity from two genuine morphisms of short exact complexes and their right-component factorization. |
| E1 A=0 | [`extension_block_zero`](Normalizer/ExtensionNaturality.lean#L43) | theorem | Cancels two monomorphisms; their geometric identification is not asserted. |
| E1 and E2, extension naturality plus dimension count | [`homology_extension_kernel_lower_bound`](Normalizer/ExtensionNaturality.lean#L64) | theorem | Combines actual connecting maps, injectivity from vanishing middle homology, and the dimension estimate. No sheaf cohomology construction is claimed. |

## ExteriorLineTrivialization

| Source / mathematical role | Lean declaration | Kind | Exact coverage |
|---|---|---|---|
| Support for the generic-rank hypothesis in P 924–932 | [`bundleFrameBasis`](Normalizer/ExteriorLineTrivialization.lean#L23) | def | Derives section bases on every open from an actual global bundle sheaf isomorphism. |
| Support for the generic-rank hypothesis in P 924–932 | [`bundleFrameBasis_apply`](Normalizer/ExteriorLineTrivialization.lean#L29) | theorem | Identifies basis vectors with images of the actual standard sheaf sections. |
| Support for the generic-rank hypothesis in P 924–932 | [`bundleFrameBasis_restrict`](Normalizer/ExteriorLineTrivialization.lean#L45) | theorem | Proves restriction compatibility of those bases from the sheaf isomorphism. |
| Support for the generic-rank hypothesis in P 924–932 | [`bundleTopExteriorPresheafIso`](Normalizer/ExteriorLineTrivialization.lean#L57) | def | Constructs a unit-to-top-exterior presheaf isomorphism from the actual bundle frame. |
| Support for the generic-rank hypothesis in P 924–932 | [`bundleTopExteriorSheafIso`](Normalizer/ExteriorLineTrivialization.lean#L75) | def | Sheafifies that actual presheaf isomorphism to a genuine global exterior-line trivialization. |
| Support for the generic-rank hypothesis in P 924–932 | [`bundleLocalFrameBasis`](Normalizer/ExteriorLineTrivialization.lean#L83) | def | Derives bases on all smaller opens from a genuine local bundle sheaf trivialization. |
| Support for the generic-rank hypothesis in P 924–932 | [`bundleLocalFrameBasis_apply`](Normalizer/ExteriorLineTrivialization.lean#L92) | theorem | Local basis vectors are the actual frame images. |
| Support for the generic-rank hypothesis in P 924–932 | [`bundleLocalFrameBasis_restrict`](Normalizer/ExteriorLineTrivialization.lean#L112) | theorem | Proves local basis restriction compatibility. |
| Support for the generic-rank hypothesis in P 924–932 | [`bundleTopExteriorPresheafIsoOver`](Normalizer/ExteriorLineTrivialization.lean#L132) | def | Constructs the actual restricted exterior presheaf isomorphism on a bundle chart. |
| Support for the generic-rank hypothesis in P 924–932 | [`bundleTopExteriorSheafMapOver`](Normalizer/ExteriorLineTrivialization.lean#L154) | def | Constructs the local frame-wedge sheaf morphism through the actual sheafification projection. |
| Support for the generic-rank hypothesis in P 924–932 | [`bundleTopExteriorSheafMapOver_isIso`](Normalizer/ExteriorLineTrivialization.lean#L163) | theorem | Derives invertibility from actual local bijectivity of the restricted sheafification projection. |
| Support for the generic-rank hypothesis in P 924–932 | [`bundleTopExteriorSheafIsoOver`](Normalizer/ExteriorLineTrivialization.lean#L197) | def | A genuine rank-n bundle chart gives a genuine line chart of the constructed top exterior sheaf. |
| Support for the generic-rank hypothesis in P 924–932 | [`bundleTopExteriorSheafIsoOver_hom_one`](Normalizer/ExteriorLineTrivialization.lean#L205) | theorem | On every smaller open, the local isomorphism sends 1 to the actual exterior product of the frame. |
| Support for the generic-rank hypothesis in P 924–932 | [`schemeTrivialBundleOverIsoFree`](Normalizer/ExteriorLineTrivialization.lean#L216) | def | Identifies the restricted standard biproduct bundle with the actual free sheaf over the open. |
| Support for the generic-rank hypothesis in P 924–932 | [`exteriorLineIsoOfFree`](Normalizer/ExteriorLineTrivialization.lean#L231) | def | Constructs the exterior-line chart directly from an actual finite free-sheaf chart. |
| Support for the generic-rank hypothesis in P 924–932 | [`exteriorSheaf_isLocallyFree_of_free_cover`](Normalizer/ExteriorLineTrivialization.lean#L239) | theorem | Actual fixed-rank finite free charts imply mathlib IsLocallyFree for the constructed top exterior sheaf; the proof constructs rank-one charts. |
| Support for the generic-rank hypothesis in P 924–932 | [`exteriorSheaf_isFinitePresentation_of_free_cover`](Normalizer/ExteriorLineTrivialization.lean#L257) | theorem | The derived rank-one charts imply actual finite presentation, using the local finite-bundle theorem. |

## ExteriorNonzero

| Source / mathematical role | Lean declaration | Kind | Exact coverage |
|---|---|---|---|
| Determinant/generic-stalk support | [`basis_exteriorProduct_ne_zero`](Normalizer/ExteriorNonzero.lean#L11) | theorem | A finite basis has nonzero top exterior product over any nontrivial commutative ring. |
| Determinant/generic-stalk support | [`exteriorProduct_ne_zero_of_linearIndependent`](Normalizer/ExteriorNonzero.lean#L20) | theorem | A finite independent family over a field has nonzero exterior product; the ambient vector space need not be finite dimensional. |

## ExteriorSemilinear

| Source / mathematical role | Lean declaration | Kind | Exact coverage |
|---|---|---|---|
| General support; exact hypotheses in the linked declaration | [`exteriorSemilinearMap`](Normalizer/ExteriorSemilinear.lean#L15) | def | Actual exterior-power map induced by a semilinear map with change of coefficient ring, constructed from the universal property. |
| General support; exact hypotheses in the linked declaration | [`exteriorSemilinearMap_ιMulti`](Normalizer/ExteriorSemilinear.lean#L39) | theorem | The constructed exterior map sends each pure wedge to the actual wedge of the images. |
| General support; exact hypotheses in the linked declaration | [`exteriorSemilinearMap_ext`](Normalizer/ExteriorSemilinear.lean#L48) | theorem | Pure wedges determine semilinear maps out of the actual exterior power. |
| General support; exact hypotheses in the linked declaration | [`exteriorSemilinearMap_id`](Normalizer/ExteriorSemilinear.lean#L61) | theorem | The actual induced exterior map of the identity is the identity. |
| General support; exact hypotheses in the linked declaration | [`exteriorSemilinearMap_comp`](Normalizer/ExteriorSemilinear.lean#L69) | theorem | Induced exterior maps respect composition with the actual coefficient-ring composition. |

## ExteriorSheaf

| Source / mathematical role | Lean declaration | Kind | Exact coverage |
|---|---|---|---|
| General support; exact hypotheses in the linked declaration | [`schemeExteriorPresheaf`](Normalizer/ExteriorSheaf.lean#L32) | def | Actual module presheaf of sectionwise exterior powers with coefficient-changing restrictions and proved functoriality. |
| General support; exact hypotheses in the linked declaration | [`schemeExteriorPresheaf_restrict`](Normalizer/ExteriorSheaf.lean#L64) | theorem | Actual presheaf restriction sends each wedge to the wedge of the restricted sections. |
| General support; exact hypotheses in the linked declaration | [`schemeExteriorSheaf`](Normalizer/ExteriorSheaf.lean#L72) | def | Actual associated module sheaf of the sectionwise exterior-power presheaf. |
| General support; exact hypotheses in the linked declaration | [`schemeExteriorProjection`](Normalizer/ExteriorSheaf.lean#L76) | def | Actual canonical projection from the exterior-power module presheaf to its sheafification. |
| General support; exact hypotheses in the linked declaration | [`schemeExteriorPure`](Normalizer/ExteriorSheaf.lean#L80) | def | Exterior product of local sections in the actual sheafified exterior power. |
| General support; exact hypotheses in the linked declaration | [`schemeExteriorPure_restrict`](Normalizer/ExteriorSheaf.lean#L84) | theorem | Local exterior products commute with the actual sheaf restrictions. |
| General support; exact hypotheses in the linked declaration | [`schemeExteriorGlobalSection`](Normalizer/ExteriorSheaf.lean#L94) | def | Actual exterior product of the specified global sections; the rank-n line-bundle interpretation remains separate. |

## ExteriorStalkComparison

| Source / mathematical role | Lean declaration | Kind | Exact coverage |
|---|---|---|---|
| Determinant/generic-stalk support | [`schemeModuleGermSemilinear`](Normalizer/ExteriorStalkComparison.lean#L30) | def | Constructs the actual module germ with its coefficient-changing scalar law. |
| Determinant/generic-stalk support | [`exteriorPresheafStalkComparison`](Normalizer/ExteriorStalkComparison.lean#L85) | def | Constructs the local-ring-linear comparison from the actual sectionwise-exterior presheaf stalk, using its genuine colimit. |
| Determinant/generic-stalk support | [`schemeExteriorProjectionStalk`](Normalizer/ExteriorStalkComparison.lean#L118) | def | Actual stalk map induced by the sheafification projection. |
| Determinant/generic-stalk support | [`schemeExteriorProjectionStalk_bijective`](Normalizer/ExteriorStalkComparison.lean#L135) | theorem | The genuine sheafification projection induces a bijection on actual stalks. |
| Determinant/generic-stalk support | [`schemeExteriorProjectionStalkEquiv`](Normalizer/ExteriorStalkComparison.lean#L145) | def | Constructed linear equivalence between actual presheaf and sheafification stalks. |
| Determinant/generic-stalk support | [`schemeExteriorStalkComparison`](Normalizer/ExteriorStalkComparison.lean#L154) | def | Canonical actual exterior-sheaf stalk comparison for every module sheaf and every scheme point. |
| Determinant/generic-stalk support | [`schemeExteriorStalkComparison_germ_pure`](Normalizer/ExteriorStalkComparison.lean#L162) | theorem | Sends the germ of the specified local exterior product to the exterior product of the actual germs. |
| Determinant/generic-stalk support | [`schemeExteriorStalkComparison_bijective_of_chart`](Normalizer/ExteriorStalkComparison.lean#L206) | theorem | Derives bijectivity from an actual rank-n bundle chart, using the constructed exterior-line chart and actual stalk basis. |
| Determinant/generic-stalk support | [`schemeExteriorStalkEquivOfChart`](Normalizer/ExteriorStalkComparison.lean#L231) | def | Constructs the actual top-exterior stalk identification from a genuine bundle chart; specializing to the generic point gives the function-field-linear identification. |
| Determinant/generic-stalk support | [`schemeExteriorStalkEquivOfChart_germ_pure`](Normalizer/ExteriorStalkComparison.lean#L239) | theorem | The constructed equivalence has the specified pure-germ formula on every neighborhood, including those outside the chosen chart. |

## FanInCompatibility

| Source / mathematical role | Lean declaration | Kind | Exact coverage |
|---|---|---|---|
| P 945–950: interface comparison | [`schemeConstants_eq_constantMap`](Normalizer/FanInCompatibility.lean#L15) | theorem | The two lane interfaces are the same actual constants ring map. |
| P 945–950: interface comparison | [`schemeFunctionFieldConstants_eq_constantMap`](Normalizer/FanInCompatibility.lean#L20) | theorem | The two lane interfaces are the same actual generic constants ring map. |
| P 945–950: interface comparison | [`properScalarCharacter_eq_globalCharacter`](Normalizer/FanInCompatibility.lean#L26) | theorem | The independently constructed global scalar characters agree under properness; the weaker universal-closedness interface is retained. |
| P 945–950: interface comparison | [`schemeModuleStalkCharacter_eq_stalkFunctional`](Normalizer/FanInCompatibility.lean#L37) | theorem | The unit-stalk-equivalence and direct-cocone character constructions agree on every actual stalk element. |

## FiniteBundlePresentation

| Source / mathematical role | Lean declaration | Kind | Exact coverage |
|---|---|---|---|
| Finite-rank bundle support for P 936 | [`sheaf_isFinitePresentation_of_finiteFree_cover`](Normalizer/FiniteBundlePresentation.lean#L16) | theorem | Actual finite free over-site trivializations on a genuine open cover yield finite presentation. Ranks may vary; no unrestricted local-freeness shortcut. |
| Finite-rank neighborhood support for P 936 | [`sheaf_isFinitePresentation_of_finiteFree_neighborhoods`](Normalizer/FiniteBundlePresentation.lean#L37) | theorem | Pointwise genuine open immersions with finite free trivializations yield actual sheaf finite presentation. |
| Actual bundle quotient support for P 936 | [`finiteBundle_cokernel_isFinitePresentation`](Normalizer/FiniteBundlePresentation.lean#L57) | theorem | Finite free covers for both source and target, possibly different, imply finite presentation of their actual categorical cokernel. |

## Flagship

| Source / mathematical role | Lean declaration | Kind | Exact coverage |
|---|---|---|---|
| General support; exact hypotheses in the linked declaration | [`semQuotientBracket`](Normalizer/Flagship.lean#L10) | def | Flagship |
| General support; exact hypotheses in the linked declaration | [`nilQuotientBracket`](Normalizer/Flagship.lean#L14) | def | Flagship |
| General support; exact hypotheses in the linked declaration | [`nilCharacter`](Normalizer/Flagship.lean#L17) | def | Flagship |
| [P 985–990](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L985-L990); [A 66–68](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/LOAD_BEARING_AUDIT.md#L66-L68) | [`sem_quotient_no_three`](Normalizer/Flagship.lean#L19) | theorem | Every subspace of the actual semisimple matrix quotient satisfying the law has finrank < 3. |
| [P 992–1035](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L992-L1035); [A 68–82](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/LOAD_BEARING_AUDIT.md#L68-L82) | [`nil_quotient_no_three`](Normalizer/Flagship.lean#L29) | theorem | Every subspace of the actual minimal matrix quotient satisfying the law has finrank < 3. |
| Algebraic corollary of [P 968–990](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L968-L990) | [`sem_injective_boundary_obstruction`](Normalizer/Flagship.lean#L40) | theorem | Boundary map on the whole algebraic quotient is explicitly assumed injective. This convenience corollary is not the geometric global-section instantiation. |
| Algebraic corollary of [P 968–1035](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L968-L1035) | [`nil_injective_boundary_obstruction`](Normalizer/Flagship.lean#L51) | theorem | Same algebraic corollary for the minimal quotient, with its grading character. No map on the geometric generic fibre is asserted to exist. |
| [P 1029–1035](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L1029-L1035); [A 80–82](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/LOAD_BEARING_AUDIT.md#L80-L82) | [`nil_eigenvalue_conflict`](Normalizer/Flagship.lean#L63) | theorem | The two displayed eigenvalues cannot both equal one. |
| E1/E2 followed by P normalizer obstruction | [`sem_extension_obstruction`](Normalizer/Flagship.lean#L78) | theorem | Excludes an explicit injective realization of the large kernel in the semisimple quotient satisfying its law. |
| E1/E2 followed by P normalizer obstruction | [`nil_extension_obstruction`](Normalizer/Flagship.lean#L91) | theorem | Same for the minimal-nilpotent quotient. |

## FrameCharacter

| Source / mathematical role | Lean declaration | Kind | Exact coverage |
|---|---|---|---|
| General support; exact hypotheses in the linked declaration | [`frameLine`](Normalizer/FrameCharacter.lean#L13) | def | FrameCharacter |
| [P 937–942](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L937-L942), [M,M]=0 | [`frameLine_abelian`](Normalizer/FrameCharacter.lean#L22) | theorem | The actual cyclic Lie subalgebra is abelian. |
| [P 937–947](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L937-L947), normalizer action | [`mem_frameNormalizer`](Normalizer/FrameCharacter.lean#L31) | theorem | Actual normalizer membership iff the generator has scalar action. |
| General support; exact hypotheses in the linked declaration | [`frameCharacter`](Normalizer/FrameCharacter.lean#L56) | def | FrameCharacter |
| [P 944–947](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L944-L947), [x,m]=λ(x)m | [`frameCharacter_action`](Normalizer/FrameCharacter.lean#L73) | theorem | The constructed character satisfies its action equation. |
| [P 944–947](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L944-L947), uniqueness | [`frameCharacter_eq`](Normalizer/FrameCharacter.lean#L79) | theorem | Frame injectivity makes the coefficient unique. |
| [P 944–947](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L944-L947), grading character | [`frameCharacter_bracket`](Normalizer/FrameCharacter.lean#L88) | theorem | Jacobi proves bracket vanishing. |
| General support; exact hypotheses in the linked declaration | [`frameIdeal`](Normalizer/FrameCharacter.lean#L100) | def | FrameCharacter |
| [P 942–947](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L942-L947), descent | [`frameCharacter_kills_line`](Normalizer/FrameCharacter.lean#L106) | theorem | The character kills the actual line ideal. |
| [P 942–947](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L942-L947), lift independence | [`frameCharacter_change_lift`](Normalizer/FrameCharacter.lean#L117) | theorem | Changing a lift by a line section preserves its character. |
| General support; exact hypotheses in the linked declaration | [`quotientFrameCharacter`](Normalizer/FrameCharacter.lean#L126) | def | FrameCharacter |
| [P 942–947](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L942-L947), quotient | [`quotientFrameCharacter_mk`](Normalizer/FrameCharacter.lean#L132) | theorem | The actual quotient character agrees on representatives. |
| [P 944–947](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L944-L947), quotient character | [`quotientFrameCharacter_bracket`](Normalizer/FrameCharacter.lean#L138) | theorem | It kills the actual quotient Lie bracket. |
| [P 944–947](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L944-L947), frame independence | [`frameLine_unit`](Normalizer/FrameCharacter.lean#L148) | theorem | Unit rescaling preserves the line subalgebra and normalizer. |
| [P 944–947](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L944-L947), frame independence | [`frame_action_unit_iff`](Normalizer/FrameCharacter.lean#L155) | theorem | The action coefficient survives unit rescaling. |
| [P 944–947](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L944-L947), frame property | [`frame_unit_injective`](Normalizer/FrameCharacter.lean#L166) | theorem | Rescaling preserves frame injectivity. |
| [P 944–947](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L944-L947), frame independence | [`frameCharacter_unit`](Normalizer/FrameCharacter.lean#L176) | theorem | The constructed characters agree in unit-related frames. |
| [P 944–947](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L944-L947), overlap compatibility | [`frameCharacter_unit_mod_line`](Normalizer/FrameCharacter.lean#L190) | theorem | Simultaneous frame and quotient-lift changes preserve the character. |
| General support; exact hypotheses in the linked declaration | [`frameNormalizerMap`](Normalizer/FrameCharacter.lean#L213) | def | FrameCharacter |
| [P 944–947](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L944-L947), restriction | [`frameCharacter_restrict`](Normalizer/FrameCharacter.lean#L226) | theorem | Compatibility with a bracket-preserving semilinear restriction. |
| General support; exact hypotheses in the linked declaration | [`frameQuotientMap`](Normalizer/FrameCharacter.lean#L238) | def | FrameCharacter |
| [P 942–947](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L942-L947), quotient restriction | [`quotientFrameCharacter_restrict`](Normalizer/FrameCharacter.lean#L253) | theorem | Compatibility on the actual normalizer quotients. |

## GenericBoundary

| Source / mathematical role | Lean declaration | Kind | Exact coverage |
|---|---|---|---|
| P 949–950, 974–979 | [`schemeFunctionFieldConstants`](Normalizer/GenericBoundary.lean#L16) | def | Canonical base-field map to the actual function field, through global constants and the generic germ. |
| P 949–950, 974–979 | [`generic_character_scalar`](Normalizer/GenericBoundary.lean#L23) | theorem | The actual generic character of a global section is the image of its proper-scheme scalar character. |
| P 949–950, 974–979 | [`generic_boundaryLaw_span`](Normalizer/GenericBoundary.lean#L46) | theorem | Derives the boundary law on the actual generic span from the global generator identity. |
| P 949–950, 974–979 | [`freeSheaf_mono_generic_boundaryLaw`](Normalizer/GenericBoundary.lean#L63) | theorem | Combines the generic law and exact dimension for an actual finite free-sheaf inclusion; global identity and inclusion remain explicit inputs. |
| P 949–950, 974–979 | [`freeSheaf_mono_generic_boundaryLaw_baseChange`](Normalizer/GenericBoundary.lean#L77) | theorem | The same actual generic span keeps its law and dimension after any field extension. |

## GenericSections

| Source / mathematical role | Lean declaration | Kind | Exact coverage |
|---|---|---|---|
| Support for P 930–932, 974–979 | [`schemeModuleStalkMap_injective`](Normalizer/GenericSections.lean#L17) | theorem | An actual sheaf monomorphism is injective on actual stalks. |
| Support for P 930–932, 974–979 | [`freeSheafGenerator`](Normalizer/GenericSections.lean#L28) | def | Canonical actual global generator of a free sheaf. |
| Support for P 930–932, 974–979 | [`freeSheafCoordinate`](Normalizer/GenericSections.lean#L33) | def | Actual free-sheaf coordinate projection to the unit sheaf. |
| Support for P 930–932, 974–979 | [`freeSheafCoordinate_generator`](Normalizer/GenericSections.lean#L40) | theorem | Coordinate projections satisfy the Kronecker rule on global generators. |
| Support for P 930–932, 974–979 | [`unitSheaf_germ_one_ne_zero`](Normalizer/GenericSections.lean#L57) | theorem | The unit section has nonzero actual germ. |
| Support for P 930–932, 974–979 | [`freeSheafGenericGenerators`](Normalizer/GenericSections.lean#L75) | def | Actual generic germs of canonical free-sheaf generators. |
| Support for P 930–932, 974–979 | [`freeSheafGenericGenerators_linearIndependent`](Normalizer/GenericSections.lean#L83) | theorem | Canonical finite free-sheaf generators are independent over the actual function field. |
| Support for P 930–932, 974–979 | [`freeSheaf_mono_generic_linearIndependent`](Normalizer/GenericSections.lean#L108) | theorem | An actual free-sheaf monomorphism yields independent generic image germs; it does not infer this from base-field independence alone. |
| Support for P 930–932, 974–979 | [`freeSheaf_mono_generic_span_finrank`](Normalizer/GenericSections.lean#L127) | theorem | The generic span of an actual finite free-sheaf inclusion has the expected dimension. Constructing that inclusion from the genus-five geometry remains separate. |

## GeometricNormalizerObstruction

| Source / mathematical role | Lean declaration | Kind | Exact coverage |
|---|---|---|---|
| P 941–947, 974–1035: actual generic comparison | [`actualNormalizer_generic_boundary_finrank`](Normalizer/GeometricNormalizerObstruction.lean#L49) | theorem | An intrinsic boundary-law subspace of the actual generic normalizer quotient has dimension less than three. An actual ambient sl3 identification and its germ bracket compatibility remain inputs; nonzero line generator and quotient comparisons are derived. |

## GlobalSectionFrame

| Source / mathematical role | Lean declaration | Kind | Exact coverage |
|---|---|---|---|
| General support; exact hypotheses in the linked declaration | [`schemeSectionFamily`](Normalizer/GlobalSectionFrame.lean#L17) | def | Compatible family of restrictions constructed from an actual global section. |
| General support; exact hypotheses in the linked declaration | [`schemeSectionHom`](Normalizer/GlobalSectionFrame.lean#L28) | def | Actual morphism from the unit sheaf represented by the prescribed global section. |
| General support; exact hypotheses in the linked declaration | [`schemeSectionHom_one`](Normalizer/GlobalSectionFrame.lean#L32) | theorem | The unit-sheaf morphism sends one to the actual restricted section on each open. |
| General support; exact hypotheses in the linked declaration | [`schemeSectionFrameMap`](Normalizer/GlobalSectionFrame.lean#L42) | def | Actual evaluation sheaf morphism from the finite trivial bundle defined by the prescribed global sections. |
| General support; exact hypotheses in the linked declaration | [`schemeSectionFrameMap_standard`](Normalizer/GlobalSectionFrame.lean#L47) | theorem | Actual standard sections map to the prescribed sections restricted to each open. |
| General support; exact hypotheses in the linked declaration | [`schemeSectionFrameMap_stalk`](Normalizer/GlobalSectionFrame.lean#L57) | theorem | Actual evaluation at every stalk is the finite linear combination of the germs of the prescribed global sections. |
| General support; exact hypotheses in the linked declaration | [`schemeModule_isIso_of_stalk_bijective`](Normalizer/GlobalSectionFrame.lean#L78) | theorem | An actual scheme-module morphism with bijective actual stalk maps is a global isomorphism. |

## HomologyBoundary

| Source / mathematical role | Lean declaration | Kind | Exact coverage |
|---|---|---|---|
| Exactness underlying [P 959–966](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L959-L966) | [`connecting_eq_zero_of_closed_lift`](Normalizer/HomologyBoundary.lean#L18) | theorem | Actual mathlib connecting map vanishes on a class with a closed middle cochain lift. |
| [P 959–966](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L959-L966) | [`connecting_boundary_law`](Normalizer/HomologyBoundary.lean#L41) | theorem | Proves the actual connecting-map law from a differential identity on lifts; no boundary-value identities are assumed. |
| [P 952–966](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L952-L966) | [`connecting_boundary_law_of_overlaps`](Normalizer/HomologyBoundary.lean#L68) | theorem | Derives that differential identity using arbitrary abelian-ideal overlap sections and an injective overlap map. Construction of the curve's complexes is outside scope. |

## IntegralSheafTorsion

| Source / mathematical role | Lean declaration | Kind | Exact coverage |
|---|---|---|---|
| General support; exact hypotheses in the linked declaration | [`schemeModuleStalkModule`](Normalizer/IntegralSheafTorsion.lean#L24) | def | IntegralSheafTorsion |
| Actual scheme-stalk support for [P 936](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L936) and [P 941](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L941) | [`schemeModule_germ_smul`](Normalizer/IntegralSheafTorsion.lean#L32) | theorem | The actual structure-sheaf and module-sheaf germs satisfy the scalar multiplication identity. |
| Actual integral-scheme torsion support for [P 936](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L936) and [P 941](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L941) | [`integralSheaf_sections_isTorsionFree`](Normalizer/IntegralSheafTorsion.lean#L43) | theorem | Torsion-free actual stalks imply torsion-free sections on every open; empty opens use sheaf separatedness. |
| Actual integral-scheme torsion support for [P 936](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L936) and [P 941](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L941) | [`integralSheaf_stalk_isTorsionFree`](Normalizer/IntegralSheafTorsion.lean#L62) | theorem | Torsion-free section modules on all opens imply torsion-free actual stalks by representing germs and shrinking their relations. |
| Actual integral-scheme torsion support for [P 936](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L936) and [P 941](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L941) | [`integralSheaf_torsionFree_iff`](Normalizer/IntegralSheafTorsion.lean#L96) | theorem | Proves the equivalence of the actual stalkwise and all-open sectionwise torsion-free criteria on an integral scheme. |
| Actual integral-scheme kernel saturation in [P 941](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L941) | [`integralSheaf_kernelCokernel_stalk_isTorsionFree`](Normalizer/IntegralSheafTorsion.lean#L105) | theorem | The actual quotient by a sheaf kernel has torsion-free stalks when the target has torsion-free stalks. The target hypothesis remains explicit. |

## KernelQuotient

| Source / mathematical role | Lean declaration | Kind | Exact coverage |
|---|---|---|---|
| General support; exact hypotheses in the linked declaration | [`kernelQuotientProjection`](Normalizer/KernelQuotient.lean#L21) | def | KernelQuotient |
| General categorical support for [P 937–942](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L937-L942) | [`kernelQuotientProjection_fac`](Normalizer/KernelQuotient.lean#L25) | theorem | The map between the two actual kernels composes to the original kernel inclusion followed by the cokernel projection. |
| General categorical support for [P 937–942](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L937-L942) | [`kernelQuotientProjection_epi`](Normalizer/KernelQuotient.lean#L32) | theorem | That map is an epimorphism, proved through epimorphic refinements; no sectionwise surjectivity is assumed. |
| General support; exact hypotheses in the linked declaration | [`kernelQuotientIso`](Normalizer/KernelQuotient.lean#L68) | def | KernelQuotient |
| General categorical support for [P 937–942](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L937-L942) | [`kernelQuotientIso_projection`](Normalizer/KernelQuotient.lean#L74) | theorem | The cokernel/kernel isomorphism is induced by the canonical kernel projection. |
| General categorical support for [P 937–942](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L937-L942) | [`kernelQuotientIso_fac`](Normalizer/KernelQuotient.lean#L82) | theorem | The comparison commutes with the original and quotient inclusions. |
| General categorical support for [P 937–942](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L937-L942) | [`kernelQuotientIso_hom_ι`](Normalizer/KernelQuotient.lean#L89) | theorem | The map into the ambient quotient is its actual cokernel descent. |
| General support; exact hypotheses in the linked declaration | [`kernelQuotientIsoOfKernel`](Normalizer/KernelQuotient.lean#L116) | def | KernelQuotient |
| General categorical support for [P 937–942](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L937-L942) | [`kernelQuotientIsoOfKernel_fac`](Normalizer/KernelQuotient.lean#L123) | theorem | The same compatibility holds for any supplied actual kernel satisfying its universal property. |
| General categorical support for [P 937–942](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L937-L942) | [`kernelQuotientIsoOfKernel_hom_ι`](Normalizer/KernelQuotient.lean#L132) | theorem | The supplied-kernel comparison is the descent of its original inclusion. |

## KernelSaturation

| Source / mathematical role | Lean declaration | Kind | Exact coverage |
|---|---|---|---|
| General support; exact hypotheses in the linked declaration | [`kernelCokernelToTarget`](Normalizer/KernelSaturation.lean#L31) | def | KernelSaturation |
| Categorical quotient support for [P 941](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L941) | [`kernelCokernelToTarget_projection`](Normalizer/KernelSaturation.lean#L36) | theorem | The actual quotient by a sheaf kernel maps to the target with composite equal to the original morphism. |
| Categorical quotient support for [P 941](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L941) | [`kernelCokernelToTarget_mono`](Normalizer/KernelSaturation.lean#L41) | theorem | The actual quotient by the kernel embeds in the target sheaf, by the abelian-category coimage theorem. |
| Sectionwise support for [P 941](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L941) | [`kernelCokernelToTarget_app_injective`](Normalizer/KernelSaturation.lean#L48) | theorem | Evaluation of the actual monomorphism is injective; no sectionwise quotient formula or surjectivity is asserted. |
| Sectionwise support for [P 941](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L941) | [`kernelCokernel_sections_isTorsionFree`](Normalizer/KernelSaturation.lean#L57) | theorem | At a specified open with torsion-free target sections, the actual quotient's sections are torsion free. |
| Sectionwise support for [P 941](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L941) | [`sheaf_kernel_regular_smul_iff`](Normalizer/KernelSaturation.lean#L65) | theorem | A regular scalar can be cancelled when testing vanishing under the actual sheaf morphism. |
| Sectionwise support for [P 941](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L941) | [`subsheafKernel_regular_smul_mem_iff`](Normalizer/KernelSaturation.lean#L74) | theorem | For a supplied subsheaf identified with the actual kernel, regular scalar multiplication does not change membership. |

## KernelTargetIso

| Source / mathematical role | Lean declaration | Kind | Exact coverage |
|---|---|---|---|
| General support; exact hypotheses in the linked declaration | [`kernelTargetIso`](Normalizer/KernelTargetIso.lean#L19) | def | KernelTargetIso |
| Categorical support for [P 938–939](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L938-L939) | [`kernelTargetIso_hom_ι`](Normalizer/KernelTargetIso.lean#L23) | theorem | Changing a morphism target by an actual isomorphism preserves its kernel inclusion into the source. |
| Categorical support for [P 938–939](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L938-L939) | [`kernelTargetIso_inv_ι`](Normalizer/KernelTargetIso.lean#L28) | theorem | The inverse kernel transport also preserves the canonical inclusion. |

## LieBoundarySpan

| Source / mathematical role | Lean declaration | Kind | Exact coverage |
|---|---|---|---|
| General support; exact hypotheses in the linked declaration | [`lie_boundaryLaw_span`](Normalizer/LieBoundarySpan.lean#L14) | theorem | Extends the boundary law on a generating set to its full linear span by bilinearity, with the same ambient linear character. |
| General support; exact hypotheses in the linked declaration | [`evaluated_boundaryLaw`](Normalizer/LieBoundarySpan.lean#L40) | theorem | The global scalar character, evaluation compatibility, and law on evaluated sections give the actual boundary law on the canonical tensor-evaluation range; no injectivity is assumed. |
| General support; exact hypotheses in the linked declaration | [`slThree_evaluated_span_finrank`](Normalizer/LieBoundarySpan.lean#L53) | theorem | The actual K-span of evaluated sections in the normalizer quotient has dimension at most two under character compatibility and the evaluated boundary law. |

## LieNormalizerTransport

| Source / mathematical role | Lean declaration | Kind | Exact coverage |
|---|---|---|---|
| General support; exact hypotheses in the linked declaration | [`mem_frameNormalizer_lieEquiv`](Normalizer/LieNormalizerTransport.lean#L15) | theorem | Ambient Lie equivalences preserve and reflect membership in the actual line normalizer. |
| General support; exact hypotheses in the linked declaration | [`frameNormalizerLieEquiv`](Normalizer/LieNormalizerTransport.lean#L31) | def | Constructed Lie equivalence between the actual line normalizers. |
| General support; exact hypotheses in the linked declaration | [`frameNormalizerLieEquiv_apply`](Normalizer/LieNormalizerTransport.lean#L43) | theorem | The normalizer comparison agrees with the ambient equivalence on underlying elements. |
| General support; exact hypotheses in the linked declaration | [`frameQuotientLieHom`](Normalizer/LieNormalizerTransport.lean#L49) | def | Induced map on the actual frame-ideal Lie quotients, with bracket preservation proved. |
| General support; exact hypotheses in the linked declaration | [`frameQuotientLieEquiv`](Normalizer/LieNormalizerTransport.lean#L91) | def | Constructed quotient Lie equivalence; bijectivity is proved by reflecting the line and lifting representatives. |
| General support; exact hypotheses in the linked declaration | [`frameQuotientLieEquiv_mk`](Normalizer/LieNormalizerTransport.lean#L98) | theorem | Actual quotient-representative formula for the induced Lie equivalence. |
| General support; exact hypotheses in the linked declaration | [`quotientFrameCharacter_lieEquiv`](Normalizer/LieNormalizerTransport.lean#L105) | theorem | The actual scalar-action quotient character is preserved by the constructed equivalence. |
| General support; exact hypotheses in the linked declaration | [`boundaryLaw_frameQuotientLieEquiv`](Normalizer/LieNormalizerTransport.lean#L115) | theorem | The actual character boundary law transports to the image subspace under the quotient equivalence. |
| General support; exact hypotheses in the linked declaration | [`lieEquiv_slThree_quotient_boundary_finrank`](Normalizer/LieNormalizerTransport.lean#L139) | theorem | Given an ambient Lie equivalence to sl3 over a characteristic-zero field, an actual quotient subspace satisfying its character boundary law has dimension less than three; quotient transport and dimension preservation are proved. |

## LineSheafTensor

| Source / mathematical role | Lean declaration | Kind | Exact coverage |
|---|---|---|---|
| General support; exact hypotheses in the linked declaration | [`lineSheafTensorEvalAt`](Normalizer/LineSheafTensor.lean#L103) | def | LineSheafTensor |
| [P 938](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L938), canonical tensor-Hom comparison | [`lineSheafTensorEvalAt_tmul`](Normalizer/LineSheafTensor.lean#L111) | theorem | The canonical sectionwise tensor evaluation acts by phi(m) • res(g) on every smaller open. |
| General support; exact hypotheses in the linked declaration | [`moduleHomSectionEval`](Normalizer/LineSheafTensor.lean#L122) | def | LineSheafTensor |
| General support; exact hypotheses in the linked declaration | [`moduleHomSectionEquiv`](Normalizer/LineSheafTensor.lean#L140) | def | LineSheafTensor |
| General support; exact hypotheses in the linked declaration | [`lineSheafTensorEvalPresheaf`](Normalizer/LineSheafTensor.lean#L170) | def | LineSheafTensor |
| [P 938](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L938), canonical tensor-Hom comparison | [`lineSheafTensorEvalPresheaf_pure`](Normalizer/LineSheafTensor.lean#L207) | theorem | The bundled presheaf evaluation has the same canonical pure-tensor formula. |
| [P 938](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L938), canonical tensor-Hom comparison | [`lineSheafTensorEvalAt_bijective`](Normalizer/LineSheafTensor.lean#L254) | theorem | Canonical presheaf evaluation is bijective on every subopen of an actual rank-one trivialization. |
| General support; exact hypotheses in the linked declaration | [`lineSheafTensorEval`](Normalizer/LineSheafTensor.lean#L262) | def | LineSheafTensor |
| [P 938](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L938), canonical tensor-Hom comparison | [`lineSheafTensorEval_pure`](Normalizer/LineSheafTensor.lean#L270) | theorem | Evaluation from the actual tensor sheaf retains the prescribed formula on pure tensors and all smaller opens. |
| [P 938](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L938), canonical tensor-Hom comparison | [`lineSheafTensorEval_isIso`](Normalizer/LineSheafTensor.lean#L285) | theorem | A genuine covering family of rank-one sheaf trivializations makes canonical tensor evaluation an isomorphism globally. |
| General support; exact hypotheses in the linked declaration | [`lineSheafTensorIso`](Normalizer/LineSheafTensor.lean#L296) | def | LineSheafTensor |
| [P 938](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L938), canonical tensor-Hom comparison | [`lineSheafTensorIso_hom`](Normalizer/LineSheafTensor.lean#L305) | theorem | The forward isomorphism is the canonical evaluation map, which was defined independently of the cover. |

## LineStalk

| Source / mathematical role | Lean declaration | Kind | Exact coverage |
|---|---|---|---|
| General support; exact hypotheses in the linked declaration | [`schemeLineFrameGerm`](Normalizer/LineStalk.lean#L17) | def | The actual ambient-stalk germ of the frame obtained from a genuine line-sheaf trivialization. |
| General support; exact hypotheses in the linked declaration | [`schemeLineStalk_range`](Normalizer/LineStalk.lean#L47) | theorem | The actual line-stalk image equals the span of the genuine frame germ; no rank or saturation hypothesis. |
| General support; exact hypotheses in the linked declaration | [`schemeLineFrameGerm_smul_injective`](Normalizer/LineStalk.lean#L109) | theorem | The actual frame germ has unique scalar coefficients, proved from the sheaf trivialization by shrinking. |
| General support; exact hypotheses in the linked declaration | [`schemeLineFrameGerm_ne_zero`](Normalizer/LineStalk.lean#L120) | theorem | The actual frame germ is nonzero, using proved scalar injectivity and nontriviality of the local ring. |

## LineTensor

| Source / mathematical role | Lean declaration | Kind | Exact coverage |
|---|---|---|---|
| General support; exact hypotheses in the linked declaration | [`tensorHomEval`](Normalizer/LineTensor.lean#L19) | def | LineTensor |
| Support for [P 936–940](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L936-L940), module algebra | [`tensorHomEval_tmul`](Normalizer/LineTensor.lean#L23) | theorem | Canonical module evaluation sends g tensor phi to the map m -> phi(m) • g. |
| Support for [P 936–940](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L936-L940), module algebra | [`line_coordinate`](Normalizer/LineTensor.lean#L29) | theorem | A chosen rank-one frame reconstructs every vector from its coordinate. |
| Support for [P 936–940](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L936-L940), module algebra | [`line_dual_coordinate`](Normalizer/LineTensor.lean#L35) | theorem | Every functional is its value on the frame times the coordinate functional. |
| General support; exact hypotheses in the linked declaration | [`lineTensorHomInv`](Normalizer/LineTensor.lean#L43) | def | LineTensor |
| Support for [P 936–940](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L936-L940), module algebra | [`lineTensorHomInv_apply`](Normalizer/LineTensor.lean#L50) | theorem | The explicit inverse sends f to f(frame) tensor coordinate. |
| Support for [P 936–940](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L936-L940), module algebra | [`tensorHomEval_lineTensorHomInv`](Normalizer/LineTensor.lean#L53) | theorem | Evaluation after the constructed inverse is the identity. |
| Support for [P 936–940](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L936-L940), module algebra | [`lineTensorHomInv_tensorHomEval`](Normalizer/LineTensor.lean#L59) | theorem | The constructed inverse after evaluation is the identity on all tensors. |
| General support; exact hypotheses in the linked declaration | [`lineTensorHomEquiv`](Normalizer/LineTensor.lean#L71) | def | LineTensor |
| Support for [P 936–940](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L936-L940), module algebra | [`lineTensorHomEquiv_toLinearMap`](Normalizer/LineTensor.lean#L79) | theorem | The local equivalence has exactly the canonical evaluation as its forward map. |
| Support for [P 936–940](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L936-L940), module algebra | [`lineTensorHomEquiv_symm_apply`](Normalizer/LineTensor.lean#L83) | theorem | The equivalence inverse has the prescribed frame formula. |
| Support for [P 936–940](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L936-L940), module algebra | [`lineTensorHomEquiv_eq`](Normalizer/LineTensor.lean#L87) | theorem | The canonical equivalence is independent of the chosen frame. |
| Support for [P 936–940](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L936-L940), module algebra | [`tensorHomEval_injective`](Normalizer/LineTensor.lean#L92) | theorem | Evaluation is injective for an actually trivialized rank-one source. |
| Support for [P 936–940](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L936-L940), module algebra | [`tensorHomEval_surjective`](Normalizer/LineTensor.lean#L96) | theorem | Evaluation is surjective for an actually trivialized rank-one source. |
| Support for [P 936–940](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L936-L940), module algebra | [`tensorHomEval_natural_target`](Normalizer/LineTensor.lean#L103) | theorem | Evaluation commutes with any linear map on the target module. |
| Support for [P 936–940](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L936-L940), module algebra | [`tensorHomEval_natural_source`](Normalizer/LineTensor.lean#L115) | theorem | Evaluation commutes with precomposition on the source module. |

## LocalCharacterGluing

| Source / mathematical role | Lean declaration | Kind | Exact coverage |
|---|---|---|---|
| General support; exact hypotheses in the linked declaration | [`glueLocalModuleMorphisms`](Normalizer/LocalCharacterGluing.lean#L119) | def | LocalCharacterGluing |
| Support for [P 944–947](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L944-L947), local-to-global action | [`glueLocalModuleMorphisms_local`](Normalizer/LocalCharacterGluing.lean#L132) | theorem | The constructed sheaf-of-modules morphism recovers each prescribed local linear map on every subopen of a cover member. |
| Support for [P 944–947](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L944-L947), independence of gluing choices | [`glueLocalModuleMorphisms_unique`](Normalizer/LocalCharacterGluing.lean#L143) | theorem | Any morphism with the prescribed local components equals the constructed morphism. |
| Support for [P 944–947](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L944-L947), existence of a global morphism | [`existsUnique_localModuleMorphism`](Normalizer/LocalCharacterGluing.lean#L162) | theorem | Restriction and overlap compatibility give exactly one morphism of the actual sheaves of modules. |

## LocalFrameStalk

| Source / mathematical role | Lean declaration | Kind | Exact coverage |
|---|---|---|---|
| Determinant/generic-stalk support | [`schemeLocalStalkMap`](Normalizer/LocalFrameStalk.lean#L69) | def | A genuine morphism on a neighborhood gives a map of the actual ambient stalks through a colimit of germs. |
| Determinant/generic-stalk support | [`schemeLocalStalkMap_germ`](Normalizer/LocalFrameStalk.lean#L81) | theorem | The constructed local stalk map sends local germs to germs of their actual images. |
| Determinant/generic-stalk support | [`schemeLocalStalkEquiv`](Normalizer/LocalFrameStalk.lean#L89) | def | A genuine neighborhood sheaf isomorphism gives an actual local-ring-linear stalk equivalence. |
| Determinant/generic-stalk support | [`schemeLocalStalkEquiv_germ`](Normalizer/LocalFrameStalk.lean#L112) | theorem | The actual stalk equivalence has its local-section germ formula. |
| Determinant/generic-stalk support | [`schemeLocalFrameStalkBasis`](Normalizer/LocalFrameStalk.lean#L123) | def | Constructs a basis of the actual stalk from a genuine local finite bundle trivialization. |
| Determinant/generic-stalk support | [`schemeLocalFrameStalkBasis_apply`](Normalizer/LocalFrameStalk.lean#L130) | theorem | The derived basis vectors are germs of the actual local frame. |
| Determinant/generic-stalk support | [`schemeLocalFrameStalkBasis_germ`](Normalizer/LocalFrameStalk.lean#L153) | theorem | The actual local frame germ formula holds on every smaller neighborhood. |
| Determinant/generic-stalk support | [`schemeLocalFrameStalkBasis_repr_germ`](Normalizer/LocalFrameStalk.lean#L164) | theorem | Actual stalk coordinates of a section germ are germs of the corresponding local frame coordinates. |

## LocallyFreeAssembly

| Source / mathematical role | Lean declaration | Kind | Exact coverage |
|---|---|---|---|
| General support; exact hypotheses in the linked declaration | [`openImmersionOverFreeIso`](Normalizer/LocallyFreeAssembly.lean#L16) | def | LocallyFreeAssembly |
| General support; exact hypotheses in the linked declaration | [`freeCoverLocalGeneratorsData`](Normalizer/LocallyFreeAssembly.lean#L37) | def | LocallyFreeAssembly |
| Local-generator support for [P 936](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L936) | [`freeCoverLocalGeneratorsData_isLocallyFree`](Normalizer/LocallyFreeAssembly.lean#L47) | theorem | Proves every local generator map is an isomorphism, the defining local-freeness datum. |
| General local-freeness criterion underlying [P 936](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L936) | [`sheaf_isLocallyFree_of_free_stalks`](Normalizer/LocallyFreeAssembly.lean#L60) | theorem | For any scheme, actual sheaf finite presentation and free actual stalks imply mathlib IsLocallyFree. The cover and generators are constructed. |

## LocallyFreeTransport

| Source / mathematical role | Lean declaration | Kind | Exact coverage |
|---|---|---|---|
| General support; exact hypotheses in the linked declaration | [`localGeneratorsDataOfIso`](Normalizer/LocallyFreeTransport.lean#L24) | def | LocallyFreeTransport |
| Actual local-trivialization support for [P 936](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L936) | [`isLocallyFree_of_iso`](Normalizer/LocallyFreeTransport.lean#L35) | theorem | An actual sheaf isomorphism transports local generators and their isomorphism property on the unchanged covering family. |
| Actual finite-type support for [P 936](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L936) | [`isFiniteType_of_iso`](Normalizer/LocallyFreeTransport.lean#L47) | theorem | The same transport retains the finite local generator index types. |
| Actual finite-type support for [P 936](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L936) | [`freeSheaf_isFiniteType`](Normalizer/LocallyFreeTransport.lean#L57) | theorem | A free sheaf indexed by a finite type has actual finite local generators. |

## Matrices

| Source / mathematical role | Lean declaration | Kind | Exact coverage |
|---|---|---|---|
| General support; exact hypotheses in the linked declaration | [`Mat`](Normalizer/Matrices.lean#L11) | abbrev | Matrices |
| General support; exact hypotheses in the linked declaration | [`comm`](Normalizer/Matrices.lean#L13) | def | Matrices |
| General support; exact hypotheses in the linked declaration | [`semM`](Normalizer/Matrices.lean#L14) | def | Matrices |
| General support; exact hypotheses in the linked declaration | [`nilM`](Normalizer/Matrices.lean#L15) | def | Matrices |
| General support; exact hypotheses in the linked declaration | [`semLift`](Normalizer/Matrices.lean#L18) | def | Matrices |
| General support; exact hypotheses in the linked declaration | [`nilLift`](Normalizer/Matrices.lean#L22) | def | Matrices |
| General support; exact hypotheses in the linked declaration | [`semBracket`](Normalizer/Matrices.lean#L26) | def | Matrices |
| General support; exact hypotheses in the linked declaration | [`nilBracket`](Normalizer/Matrices.lean#L30) | def | Matrices |
| [P 985–987](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L985-L987) | [`semLift_trace`](Normalizer/Matrices.lean#L41) | theorem | Semisimple coordinate lifts are trace zero. |
| [P 992–997](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L992-L997) | [`nilLift_trace`](Normalizer/Matrices.lean#L44) | theorem | Minimal coordinate lifts are trace zero. |
| [P 985–987](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L985-L987); [A 66–68](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/LOAD_BEARING_AUDIT.md#L66-L68) | [`sem_action`](Normalizer/Matrices.lean#L49) | theorem | Every parametrized semisimple normalizer element centralizes the distinguished matrix. |
| [P 999–1002](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L999-L1002); [A 76](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/LOAD_BEARING_AUDIT.md#L76) | [`nil_action`](Normalizer/Matrices.lean#L52) | theorem | Action on E12 is exactly multiplication by the D-coordinate. |
| [P 985–987](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L985-L987) | [`sem_bracket_lift`](Normalizer/Matrices.lean#L55) | theorem | All semisimple matrix commutators equal the lifted sl2 coordinate bracket; arbitrary line lifts allowed. |
| [P 1003–1006](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L1003-L1006) | [`nil_bracket_lift`](Normalizer/Matrices.lean#L61) | theorem | All minimal matrix commutators equal the lifted coordinate bracket plus an explicitly calculated multiple of E12. |
| [P 980–990](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L980-L990); [A 63–68](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/LOAD_BEARING_AUDIT.md#L63-L68) | [`sem_normalizer`](Normalizer/Matrices.lean#L68) | theorem | If and only if: trace zero and [X,m]=t m are equivalent to the explicit four-parameter normal form with t=0. |
| [P 992–1002](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L992-L1002); [A 68–76](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/LOAD_BEARING_AUDIT.md#L68-L76) | [`nil_normalizer`](Normalizer/Matrices.lean#L98) | theorem | If and only if: trace zero and [X,E12]=t E12 are equivalent to the explicit five-parameter normal form with t equal to the D-coordinate. |

## MatrixScalarExtension

| Source / mathematical role | Lean declaration | Kind | Exact coverage |
|---|---|---|---|
| General support; exact hypotheses in the linked declaration | [`matrixScalarExtension`](Normalizer/MatrixScalarExtension.lean#L16) | def | Canonical linear equivalence from K tensor_F Mat3(F) to Mat3(K). |
| General support; exact hypotheses in the linked declaration | [`matrixScalarExtension_tmul`](Normalizer/MatrixScalarExtension.lean#L25) | theorem | The canonical matrix equivalence sends a tensor X to a times the entrywise image of X. |
| General support; exact hypotheses in the linked declaration | [`matrix_map_trace`](Normalizer/MatrixScalarExtension.lean#L31) | theorem | Entrywise field extension preserves trace. |
| General support; exact hypotheses in the linked declaration | [`matrix_map_comm`](Normalizer/MatrixScalarExtension.lean#L35) | theorem | Entrywise field extension preserves commutators. |
| General support; exact hypotheses in the linked declaration | [`matrix_map_smul`](Normalizer/MatrixScalarExtension.lean#L41) | theorem | Entrywise extension carries scalar multiplication to multiplication by the scalar's image. |
| General support; exact hypotheses in the linked declaration | [`matrix_map_ne_zero`](Normalizer/MatrixScalarExtension.lean#L46) | theorem | A nonzero matrix remains nonzero after extension of fields. |
| General support; exact hypotheses in the linked declaration | [`matrixBaseChange`](Normalizer/MatrixScalarExtension.lean#L56) | def | The actual tensor extension of a matrix-valued linear map. |
| General support; exact hypotheses in the linked declaration | [`characterBaseChange`](Normalizer/MatrixScalarExtension.lean#L61) | def | The actual tensor extension of the scalar-valued character. |
| General support; exact hypotheses in the linked declaration | [`matrixBaseChange_tmul`](Normalizer/MatrixScalarExtension.lean#L65) | theorem | Pure-tensor formula for the extended matrix lift. |
| General support; exact hypotheses in the linked declaration | [`characterBaseChange_tmul`](Normalizer/MatrixScalarExtension.lean#L69) | theorem | Pure-tensor formula for the extended character. |
| General support; exact hypotheses in the linked declaration | [`boundaryLift_baseChange_finrank`](Normalizer/MatrixScalarExtension.lean#L75) | theorem | Dimension of the actual scalar-extended source equals its original dimension. |
| General support; exact hypotheses in the linked declaration | [`matrixBaseChange_independent_mod_line`](Normalizer/MatrixScalarExtension.lean#L81) | theorem | Flatness preserves injectivity of the map to the matrix quotient, proving independence modulo the extended distinguished line. |

## MatrixTransport

| Source / mathematical role | Lean declaration | Kind | Exact coverage |
|---|---|---|---|
| General support; exact hypotheses in the linked declaration | [`MatrixBoundaryLift`](Normalizer/MatrixTransport.lean#L15) | def | Four explicit hypotheses: trace-zero lifts, actual scalar action, boundary law modulo the line, and independence modulo the line. |
| General support; exact hypotheses in the linked declaration | [`sem_matrix_boundary_lift`](Normalizer/MatrixTransport.lean#L23) | theorem | Applies the checked semisimple quotient projection and obstruction to an arbitrary independent linear lift. |
| General support; exact hypotheses in the linked declaration | [`nil_matrix_boundary_lift`](Normalizer/MatrixTransport.lean#L56) | theorem | Applies the checked nilpotent quotient projection and actual character to an arbitrary independent linear lift. |
| General support; exact hypotheses in the linked declaration | [`matrixConjugation`](Normalizer/MatrixTransport.lean#L89) | def | Linear equivalence defined by an invertible matrix and its inverse. |
| General support; exact hypotheses in the linked declaration | [`matrixConjugation_trace`](Normalizer/MatrixTransport.lean#L98) | theorem | Matrix conjugation preserves trace. |
| General support; exact hypotheses in the linked declaration | [`matrixConjugation_comm`](Normalizer/MatrixTransport.lean#L103) | theorem | Matrix conjugation preserves commutators. |
| General support; exact hypotheses in the linked declaration | [`matrix_boundary_lift_transport`](Normalizer/MatrixTransport.lean#L111) | theorem | A trace- and commutator-preserving linear equivalence and a nonzero rescaling preserve all four lift hypotheses and the same character. |
| General support; exact hypotheses in the linked declaration | [`conjugate_sem_matrix_boundary_lift`](Normalizer/MatrixTransport.lean#L141) | theorem | The semisimple obstruction transported through a supplied conjugacy and nonzero scalar. |
| General support; exact hypotheses in the linked declaration | [`conjugate_nil_matrix_boundary_lift`](Normalizer/MatrixTransport.lean#L150) | theorem | The nilpotent obstruction transported through a supplied conjugacy and nonzero scalar. |
| General support; exact hypotheses in the linked declaration | [`matrix_reindex_trace`](Normalizer/MatrixTransport.lean#L160) | theorem | Simultaneous permutation of rows and columns preserves trace. |
| General support; exact hypotheses in the linked declaration | [`matrix_reindex_comm`](Normalizer/MatrixTransport.lean#L165) | theorem | Simultaneous permutation of rows and columns preserves commutators. |

## MatrixTrichotomy

| Source / mathematical role | Lean declaration | Kind | Exact coverage |
|---|---|---|---|
| General support; exact hypotheses in the linked declaration | [`monic_degree_le_two_not_squarefree`](Normalizer/MatrixTrichotomy.lean#L18) | theorem | Over an algebraically closed field, a nonsquarefree monic polynomial of degree at most two is exactly a squared monic linear factor. |
| General support; exact hypotheses in the linked declaration | [`traceless_matrix_trichotomy`](Normalizer/MatrixTrichotomy.lean#L35) | theorem | Proves exhaustive alternatives: minimal polynomial degree three, semisimple associated endomorphism, or square-zero matrix; no normal form is assumed. |

## ModuleHomLine

| Source / mathematical role | Lean declaration | Kind | Exact coverage |
|---|---|---|---|
| General support; exact hypotheses in the linked declaration | [`moduleLineFrameAt`](Normalizer/ModuleHomLine.lean#L18) | def | ModuleHomLine |
| Support for [P 938](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L938), actual local sheaf frames | [`moduleLineFrameAt_restrict`](Normalizer/ModuleHomLine.lean#L25) | theorem | The frame from a restricted-sheaf isomorphism commutes with restriction. |
| Support for [P 938](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L938), actual local sheaf frames | [`moduleLineFrameAt_symm_restrict`](Normalizer/ModuleHomLine.lean#L35) | theorem | Coordinates in that frame commute with restriction. |
| Support for [P 938](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L938), actual local sheaf frames | [`moduleHom_eval_frame`](Normalizer/ModuleHomLine.lean#L72) | theorem | Naturality on every smaller open recovers an internal-Hom section from the image of its frame. |
| General support; exact hypotheses in the linked declaration | [`moduleHomFrameEquiv`](Normalizer/ModuleHomLine.lean#L94) | def | ModuleHomLine |
| Support for [P 938](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L938), actual local sheaf frames | [`moduleHomFrameEquiv_apply`](Normalizer/ModuleHomLine.lean#L118) | theorem | The local internal-Hom equivalence is actual evaluation at the frame. |

## ModuleSheafHom

| Source / mathematical role | Lean declaration | Kind | Exact coverage |
|---|---|---|---|
| General support; exact hypotheses in the linked declaration | [`moduleHomSheaf`](Normalizer/ModuleSheafHom.lean#L171) | def | ModuleSheafHom |
| General support; exact hypotheses in the linked declaration | [`moduleHomEval`](Normalizer/ModuleSheafHom.lean#L182) | def | ModuleSheafHom |
| General support; exact hypotheses in the linked declaration | [`moduleHomMk`](Normalizer/ModuleSheafHom.lean#L190) | def | ModuleSheafHom |
| Hom-sheaf infrastructure for [P 937–942](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L937-L942) | [`moduleHomEval_mk`](Normalizer/ModuleSheafHom.lean#L210) | theorem | A constructed Hom section recovers every supplied compatible local linear map. |
| Hom-sheaf infrastructure for [P 937–942](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L937-L942) | [`moduleHom_ext`](Normalizer/ModuleSheafHom.lean#L222) | theorem | Equality is tested on all smaller opens and all source sections. |
| Hom-sheaf infrastructure for [P 937–942](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L937-L942) | [`moduleHom_restrict`](Normalizer/ModuleSheafHom.lean#L232) | theorem | Restricting a Hom section retains its original component on each smaller open. |
| Hom-sheaf infrastructure for [P 937–942](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L937-L942) | [`moduleHomEval_natural`](Normalizer/ModuleSheafHom.lean#L248) | theorem | Every Hom section acts naturally with respect to module restrictions. |
| Hom-sheaf infrastructure for [P 937–942](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L937-L942) | [`moduleHomEval_zero`](Normalizer/ModuleSheafHom.lean#L258) | theorem | Zero acts by zero. |
| Hom-sheaf infrastructure for [P 937–942](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L937-L942) | [`moduleHomEval_add`](Normalizer/ModuleSheafHom.lean#L262) | theorem | Addition acts componentwise. |
| Hom-sheaf infrastructure for [P 937–942](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L937-L942) | [`moduleHomEval_smul`](Normalizer/ModuleSheafHom.lean#L268) | theorem | Scalars are restricted before acting on a smaller open. |
| General support; exact hypotheses in the linked declaration | [`moduleHomOverEquiv`](Normalizer/ModuleSheafHom.lean#L276) | def | ModuleSheafHom |

## ModuleSheafTensor

| Source / mathematical role | Lean declaration | Kind | Exact coverage |
|---|---|---|---|
| General support; exact hypotheses in the linked declaration | [`moduleSectionCommRing`](Normalizer/ModuleSheafTensor.lean#L20) | def | ModuleSheafTensor |
| General support; exact hypotheses in the linked declaration | [`moduleTensorPresheaf`](Normalizer/ModuleSheafTensor.lean#L32) | def | ModuleSheafTensor |
| General support; exact hypotheses in the linked declaration | [`moduleTensorSheaf`](Normalizer/ModuleSheafTensor.lean#L37) | def | ModuleSheafTensor |
| General support; exact hypotheses in the linked declaration | [`moduleTensorProjection`](Normalizer/ModuleSheafTensor.lean#L42) | def | ModuleSheafTensor |
| General support; exact hypotheses in the linked declaration | [`moduleTensorHomEquiv`](Normalizer/ModuleSheafTensor.lean#L48) | def | ModuleSheafTensor |
| General support; exact hypotheses in the linked declaration | [`moduleTensorLift`](Normalizer/ModuleSheafTensor.lean#L54) | def | ModuleSheafTensor |
| Support for [P 938](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L938), actual tensor sheaf | [`moduleTensorHomEquiv_apply`](Normalizer/ModuleSheafTensor.lean#L60) | theorem | The actual sheafification adjunction restricts a sheaf morphism along its canonical projection. |
| Support for [P 938](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L938), actual tensor sheaf | [`moduleTensorProjection_lift`](Normalizer/ModuleSheafTensor.lean#L66) | theorem | The lifted sheaf morphism has the originally prescribed presheaf values. |
| Support for [P 938](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L938), actual tensor sheaf | [`moduleTensor_hom_ext`](Normalizer/ModuleSheafTensor.lean#L73) | theorem | The projection formula uniquely determines a morphism from the actual tensor sheaf. |
| General support; exact hypotheses in the linked declaration | [`moduleTensorPresheafPure`](Normalizer/ModuleSheafTensor.lean#L80) | def | ModuleSheafTensor |
| General support; exact hypotheses in the linked declaration | [`moduleTensorPure`](Normalizer/ModuleSheafTensor.lean#L87) | def | ModuleSheafTensor |
| Support for [P 938](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L938), actual tensor sheaf | [`moduleTensorPresheafPure_restrict`](Normalizer/ModuleSheafTensor.lean#L94) | theorem | Restriction of a presheaf pure tensor is the tensor of the restricted sections. |
| Support for [P 938](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L938), actual tensor sheaf | [`moduleTensorPresheaf_map_tmul`](Normalizer/ModuleSheafTensor.lean#L101) | theorem | The actual tensor-presheaf restriction has the ordinary pure-tensor formula. |
| Support for [P 938](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L938), actual tensor sheaf | [`moduleTensorPure_restrict`](Normalizer/ModuleSheafTensor.lean#L110) | theorem | The same pure-tensor restriction formula survives actual sheafification. |
| Support for [P 938](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L938), actual tensor sheaf | [`moduleTensorLift_pure`](Normalizer/ModuleSheafTensor.lean#L118) | theorem | A lifted sheaf map evaluates pure tensors by its prescribed presheaf map. |

## NormalizerBilinear

| Source / mathematical role | Lean declaration | Kind | Exact coverage |
|---|---|---|---|
| P 941–947, 977–979 | [`normalizerQuotientSectionBilinear`](Normalizer/NormalizerBilinear.lean#L31) | def | Bundles the constructed actual normalizer quotient bracket as a sectionwise bilinear map. |
| P 941–947, 977–979 | [`normalizerQuotientSectionBilinear_apply`](Normalizer/NormalizerBilinear.lean#L46) | theorem | Agrees with the previously constructed quotient bracket. |
| P 941–947, 977–979 | [`normalizerQuotientSectionBilinear_restrict`](Normalizer/NormalizerBilinear.lean#L51) | theorem | Proves restriction compatibility for that actual bracket. |
| P 941–947, 977–979 | [`normalizerQuotientStalkBilinear`](Normalizer/NormalizerBilinear.lean#L61) | def | Constructs the actual normalizer quotient stalk bracket. |
| P 941–947, 977–979 | [`normalizerQuotientStalkBilinear_germ`](Normalizer/NormalizerBilinear.lean#L70) | theorem | Actual normalizer quotient bracket commutes with germs. |
| P 941–947, 977–979 | [`normalizerQuotientStalkBilinear_alternating`](Normalizer/NormalizerBilinear.lean#L78) | theorem | Proves alternation of the actual stalk bracket from ambient alternation. |
| P 941–947, 977–979 | [`normalizerQuotientStalkBilinear_leibniz`](Normalizer/NormalizerBilinear.lean#L89) | theorem | Proves the actual stalk Jacobi identity. |
| P 941–947, 977–979 | [`normalizerQuotientStalkLieRing`](Normalizer/NormalizerBilinear.lean#L106) | def | Bundles the actual stalk Lie ring. |
| P 941–947, 977–979 | [`normalizerQuotientStalkLieAlgebra`](Normalizer/NormalizerBilinear.lean#L121) | def | Bundles the actual stalk Lie algebra over the actual local ring. |

## NormalizerGeneric

| Source / mathematical role | Lean declaration | Kind | Exact coverage |
|---|---|---|---|
| P 945–950, 974–984 | [`normalizerQuotient_generic_boundaryLaw`](Normalizer/NormalizerGeneric.lean#L54) | theorem | Specializes the passage to the actual normalizer quotient and its character from genuine line trivializations, assuming the actual inclusion and global identity. |
| P 945–950, 974–984 | [`normalizerQuotient_generic_boundaryLaw_baseChange`](Normalizer/NormalizerGeneric.lean#L77) | theorem | Specializes the tensor-extension passage to the same actual normalizer quotient. This does not classify its generic matrix normalizer. |

## NormalizerKernel

| Source / mathematical role | Lean declaration | Kind | Exact coverage |
|---|---|---|---|
| General support; exact hypotheses in the linked declaration | [`ambientQuotientSheaf`](Normalizer/NormalizerKernel.lean#L19) | def | NormalizerKernel |
| General support; exact hypotheses in the linked declaration | [`ambientQuotientProjection`](Normalizer/NormalizerKernel.lean#L22) | def | NormalizerKernel |
| [P 937–942](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L937-L942), ambient quotient exactness | [`ambientQuotient_zero_iff`](Normalizer/NormalizerKernel.lean#L26) | theorem | A section of E maps to zero in the actual sheaf quotient exactly when it lies in I on that same open. |
| General support; exact hypotheses in the linked declaration | [`normalizerBracketMap`](Normalizer/NormalizerKernel.lean#L141) | def | NormalizerKernel |
| [P 937–941](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L937-L941), actual bracket-induced map | [`normalizerBracketMap_apply`](Normalizer/NormalizerKernel.lean#L176) | theorem | Evaluating b(x) on a local I-section gives the actual projected bracket [res x,m] mod I. |
| [P 937–942](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L937-L942), normalizer kernel | [`normalizerBracketMap_zero_iff`](Normalizer/NormalizerKernel.lean#L186) | theorem | Vanishing of the constructed Hom-valued map is equivalent to the existing all-restrictions normalizer condition. |
| [P 937–942](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L937-L942), normalizer inclusion | [`normalizerBracketMap_condition`](Normalizer/NormalizerKernel.lean#L206) | theorem | The existing normalizer inclusion is killed by the actual bracket map. |
| General support; exact hypotheses in the linked declaration | [`normalizerBracketIsKernel`](Normalizer/NormalizerKernel.lean#L215) | def | NormalizerKernel |
| [P 937–941](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L937-L941), descent through E/I | [`normalizerBracketMap_kills_line`](Normalizer/NormalizerKernel.lean#L227) | theorem | Abelianness makes b kill the actual subsheaf inclusion. |
| General support; exact hypotheses in the linked declaration | [`ambientQuotientBracketMap`](Normalizer/NormalizerKernel.lean#L235) | def | NormalizerKernel |
| [P 937–941](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L937-L941), induced quotient map | [`ambientQuotientBracketMap_projection`](Normalizer/NormalizerKernel.lean#L241) | theorem | The constructed beta satisfies q composed with beta equals b. |
| [P 937–941](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L937-L941), bracket formula after descent | [`ambientQuotientBracketMap_apply`](Normalizer/NormalizerKernel.lean#L249) | theorem | On projected sections, beta evaluates to the same actual projected bracket on every smaller open. |
| General support; exact hypotheses in the linked declaration | [`normalizerQuotientKernelIso`](Normalizer/NormalizerKernel.lean#L269) | def | NormalizerKernel |
| [P 937–942](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L937-L942), kernel identification | [`normalizerQuotientKernelIso_fac`](Normalizer/NormalizerKernel.lean#L283) | theorem | The proved N/I ≅ ker beta identifies the original inclusion/projection diagram. No kernel-identification hypothesis remains. |
| General support; exact hypotheses in the linked declaration | [`normalizerQuotientToAmbient`](Normalizer/NormalizerKernel.lean#L305) | def | NormalizerKernel |
| [P 937–942](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L937-L942), canonical map into G | [`normalizerQuotientToAmbient_projection`](Normalizer/NormalizerKernel.lean#L312) | theorem | The direct cokernel descent from N/I to G recovers N -> E -> G. |
| [P 937–942](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L937-L942), intended inclusion under the isomorphism | [`normalizerQuotientKernelIso_hom_ι`](Normalizer/NormalizerKernel.lean#L320) | theorem | The kernel inclusion is exactly the canonical descended map, not an unrelated embedding. |
| [P 937–942](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L937-L942), K as a subobject of G | [`normalizerQuotientToAmbient_mono`](Normalizer/NormalizerKernel.lean#L329) | theorem | The canonical N/I -> G is monic as an actual module-sheaf morphism. Saturation on a curve remains separate. |

## NormalizerQuotientStalk

| Source / mathematical role | Lean declaration | Kind | Exact coverage |
|---|---|---|---|
| General support; exact hypotheses in the linked declaration | [`schemeNormalizerStalkEquiv_line`](Normalizer/NormalizerQuotientStalk.lean#L46) | theorem | The constructed normalizer-stalk comparison sends the image of the actual line inclusion onto the actual frame ideal. |
| General support; exact hypotheses in the linked declaration | [`schemeNormalizerQuotientStalkEquiv`](Normalizer/NormalizerQuotientStalk.lean#L77) | def | Constructed equivalence from the actual normalizer sheaf-cokernel stalk to the algebraic line-normalizer quotient; ambient identification remains an explicit input. |
| General support; exact hypotheses in the linked declaration | [`schemeNormalizerQuotientStalkEquiv_projection`](Normalizer/NormalizerQuotientStalk.lean#L89) | theorem | The actual quotient-stalk equivalence agrees with the quotient of the normalizer comparison on every projected stalk representative. |

## NormalizerSheaf

| Source / mathematical role | Lean declaration | Kind | Exact coverage |
|---|---|---|---|
| General support; exact hypotheses in the linked declaration | [`normalizerSubsheaf`](Normalizer/NormalizerSheaf.lean#L45) | def | NormalizerSheaf |
| [P 937–942](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L937-L942), normalizer subsheaf | [`mem_normalizerSubsheaf`](Normalizer/NormalizerSheaf.lean#L61) | theorem | Membership means preserving the subsheaf after every restriction; the subsheaf and its local membership proof are constructed. |
| [P 944–947](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L944-L947), action on the line | [`normalizerSubsheaf_action`](Normalizer/NormalizerSheaf.lean#L67) | theorem | A normalizer section acts on sections of the subsheaf on the same open. |
| [P 941–942](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L941-L942), inclusion of the line | [`abelian_subsheaf_le_normalizer`](Normalizer/NormalizerSheaf.lean#L73) | theorem | An actual abelian subsheaf lies in the constructed normalizer. |
| [P 941–942](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L941-L942), closure under bracket | [`normalizerSubsheaf_bracket`](Normalizer/NormalizerSheaf.lean#L82) | theorem | Restriction compatibility and Jacobi imply bracket closure of the constructed normalizer. |
| Support for [P 944–947](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L944-L947), framed description | [`normalizerSubsheaf_frame_criterion`](Normalizer/NormalizerSheaf.lean#L96) | theorem | A frame generating the line on all subopens reduces normalizer membership to the action on that frame. |
| General support; exact hypotheses in the linked declaration | [`normalizerLineInclusion`](Normalizer/NormalizerSheaf.lean#L119) | def | NormalizerSheaf |
| General support; exact hypotheses in the linked declaration | [`normalizerQuotientSheaf`](Normalizer/NormalizerSheaf.lean#L126) | def | NormalizerSheaf |
| General support; exact hypotheses in the linked declaration | [`descendNormalizerCharacter`](Normalizer/NormalizerSheaf.lean#L131) | def | NormalizerSheaf |
| [P 944–947](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L944-L947), character descent | [`descendNormalizerCharacter_fac`](Normalizer/NormalizerSheaf.lean#L139) | theorem | A character killing the inclusion factors through the actual sheaf cokernel, recovering the original map. |
| [P 944–947](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L944-L947), uniqueness of descent | [`descendNormalizerCharacter_unique`](Normalizer/NormalizerSheaf.lean#L148) | theorem | The factorization through the sheaf quotient is unique. |
| General support; exact hypotheses in the linked declaration | [`gluedNormalizerCharacter`](Normalizer/NormalizerSheaf.lean#L187) | def | NormalizerSheaf |
| Support for [P 944–947](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L944-L947), vanishing on the line | [`gluedNormalizerCharacter_kills_line`](Normalizer/NormalizerSheaf.lean#L192) | theorem | Local vanishing of the supplied compatible characters gives zero composition with the actual line inclusion. |
| General support; exact hypotheses in the linked declaration | [`gluedNormalizerQuotientCharacter`](Normalizer/NormalizerSheaf.lean#L208) | def | NormalizerSheaf |
| [P 944–947](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L944-L947), local action equation after quotienting | [`gluedNormalizerQuotientCharacter_local`](Normalizer/NormalizerSheaf.lean#L220) | theorem | The constructed quotient character recovers the prescribed coefficient on every local normalizer lift under the actual sheaf-cokernel projection. |

## NormalizerStalk

| Source / mathematical role | Lean declaration | Kind | Exact coverage |
|---|---|---|---|
| General support; exact hypotheses in the linked declaration | [`schemeSubmoduleStalk_injective`](Normalizer/NormalizerStalk.lean#L17) | theorem | An actual subsheaf inclusion is injective on the actual stalk. |
| General support; exact hypotheses in the linked declaration | [`schemeSubmoduleStalk_mem_range`](Normalizer/NormalizerStalk.lean#L24) | theorem | Membership in the subsheaf stalk image is equivalent to having a local representative in that subsheaf. |
| General support; exact hypotheses in the linked declaration | [`lineTrivializationAt_span`](Normalizer/NormalizerStalk.lean#L39) | theorem | A genuine restricted-sheaf line trivialization supplies a frame generating on every smaller open. |
| General support; exact hypotheses in the linked declaration | [`schemeNormalizerStalk_mem_iff`](Normalizer/NormalizerStalk.lean#L79) | theorem | With a uniformly generating local frame and a bracket-preserving ambient stalk identification, actual normalizer-stalk membership is equivalent to algebraic line-normalizer membership; the reverse implication is proved by shrinking. |
| General support; exact hypotheses in the linked declaration | [`schemeNormalizerStalk_mem_iff_trivialization`](Normalizer/NormalizerStalk.lean#L181) | theorem | Derives the frame-generation input from a genuine sheaf trivialization and applies the normalizer-stalk membership comparison. |
| General support; exact hypotheses in the linked declaration | [`schemeNormalizerStalkEquiv`](Normalizer/NormalizerStalk.lean#L189) | def | Constructed linear equivalence from the actual normalizer stalk to the actual algebraic line normalizer; no surjectivity assumption. |
| General support; exact hypotheses in the linked declaration | [`schemeNormalizerStalkEquiv_apply`](Normalizer/NormalizerStalk.lean#L214) | theorem | The normalizer-stalk equivalence is the ambient identification composed with the actual stalk inclusion. |

## NormalizerStalkBracket

| Source / mathematical role | Lean declaration | Kind | Exact coverage |
|---|---|---|---|
| General support; exact hypotheses in the linked declaration | [`schemeNormalizerQuotientStalkEquiv_bracket`](Normalizer/NormalizerStalkBracket.lean#L75) | theorem | The constructed quotient comparison preserves the actual sheaf bracket on germs of arbitrary quotient sections; simultaneous local lifts are derived. |

## NormalizerStalkCharacter

| Source / mathematical role | Lean declaration | Kind | Exact coverage |
|---|---|---|---|
| General support; exact hypotheses in the linked declaration | [`schemeLineFrameGerm_map_smul_injective`](Normalizer/NormalizerStalkCharacter.lean#L17) | theorem | An ambient linear equivalence preserves the proved faithfulness of the actual line frame germ. |
| General support; exact hypotheses in the linked declaration | [`schemeNormalizerQuotientStalkCharacter`](Normalizer/NormalizerStalkCharacter.lean#L61) | theorem | The actual quotientCharacterOfTrivializations becomes quotientFrameCharacter under the constructed quotient-stalk equivalence, on every stalk element; character compatibility is a conclusion. |

## NormalizerStalkIntegration

| Source / mathematical role | Lean declaration | Kind | Exact coverage |
|---|---|---|---|
| P 941–947, 974–1035: actual generic comparison | [`normalizerQuotientStalkEquiv_intrinsic_bracket`](Normalizer/NormalizerStalkIntegration.lean#L44) | theorem | Proves compatibility of the quotient-stalk comparison with the local intrinsic bracket on all elements. |
| P 941–947, 974–1035: actual generic comparison | [`normalizerQuotientStalkLieEquiv`](Normalizer/NormalizerStalkIntegration.lean#L56) | def | Bundles the actual quotient-stalk comparison as a Lie equivalence, using the intrinsic source bracket. |
| P 941–947, 974–1035: actual generic comparison | [`normalizerQuotientStalkEquiv_intrinsic_character`](Normalizer/NormalizerStalkIntegration.lean#L81) | theorem | The intrinsic stalk character is the algebraic scalar-action character under the constructed comparison. |
| P 941–947, 974–1035: actual generic comparison | [`normalizerQuotientStalkEquiv_boundary_identity`](Normalizer/NormalizerStalkIntegration.lean#L99) | theorem | Transports the intrinsic boundary identity on whole actual stalk submodules, deriving bracket and character compatibility. |

## NormalizerTensorKernel

| Source / mathematical role | Lean declaration | Kind | Exact coverage |
|---|---|---|---|
| General support; exact hypotheses in the linked declaration | [`normalizerTensorBracketMap`](Normalizer/NormalizerTensorKernel.lean#L27) | def | NormalizerTensorKernel |
| [P 938–939](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L938-L939), tensor-valued normalizer kernel | [`normalizerTensorBracketMap_evaluation`](Normalizer/NormalizerTensorKernel.lean#L36) | theorem | Contracting the tensor-valued bracket by canonical evaluation recovers the original Hom-valued bracket. |
| [P 938–939](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L938-L939), tensor-valued normalizer kernel | [`normalizerTensorBracketMap_projection`](Normalizer/NormalizerTensorKernel.lean#L45) | theorem | The tensor bracket after the ambient cokernel projection is the original bracket transported by the proved target isomorphism. |
| [P 938–939](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L938-L939), tensor-valued normalizer kernel | [`normalizerTensorBracketMap_apply`](Normalizer/NormalizerTensorKernel.lean#L55) | theorem | Contracting on a local line section gives the projected actual commutator, including the original sign. |
| General support; exact hypotheses in the linked declaration | [`normalizerTensorQuotientKernelIso`](Normalizer/NormalizerTensorKernel.lean#L79) | def | NormalizerTensorKernel |
| [P 938–939](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L938-L939), tensor-valued normalizer kernel | [`normalizerTensorQuotientKernelIso_hom_ι`](Normalizer/NormalizerTensorKernel.lean#L91) | theorem | The tensor-kernel isomorphism identifies its kernel inclusion with the actual descended N/I -> G map. |
| [P 938–939](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L938-L939), tensor-valued normalizer kernel | [`normalizerTensorQuotientKernelIso_projection`](Normalizer/NormalizerTensorKernel.lean#L108) | theorem | The tensor-kernel identification commutes with the original normalizer inclusion and ambient quotient projection. |

## Obstruction

| Source / mathematical role | Lean declaration | Kind | Exact coverage |
|---|---|---|---|
| General support; exact hypotheses in the linked declaration | [`BoundaryLaw`](Normalizer/Obstruction.lean#L9) | def | Obstruction |
| [P 985–990](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L985-L990); [A 66–68](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/LOAD_BEARING_AUDIT.md#L66-L68) | [`sem_no_three`](Normalizer/Obstruction.lean#L31) | theorem | Coordinate proof: finrank at least 3 forces the whole sl2 model, contradicted by [E12,E21] ≠ 0. |
| [P 1008–1035](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L1008-L1035); [A 78–82](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/LOAD_BEARING_AUDIT.md#L78-L82) | [`nil_dimension_le_two`](Normalizer/Obstruction.lean#L57) | theorem | Alternative proof of the same obstruction by injective coordinate projections. It proves finrank ≤ 2 without assuming the manuscript’s abelian-plane classification. |
| [P 1008–1035](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L1008-L1035) | [`nil_no_three`](Normalizer/Obstruction.lean#L103) | theorem | Immediate dimension-<3 form of nil_dimension_le_two. |

## ProperConstants

| Source / mathematical role | Lean declaration | Kind | Exact coverage |
|---|---|---|---|
| Actual constants map supporting P 949–950 | [`schemeConstants`](Normalizer/ProperConstants.lean#L17) | def | The canonical ring map k → Γ(X,O), formed from the structure morphism and the canonical Γ(Spec k,O) isomorphism. |
| Proper-curve constancy supporting P 949–950 | [`properScheme_constants_bijective`](Normalizer/ProperConstants.lean#L23) | theorem | The actual constants map is bijective on an integral proper scheme over an algebraically closed field; no smoothness or dimension assumption is needed. |
| Scalar existence and uniqueness for P 949–950 | [`properScheme_global_function_constant`](Normalizer/ProperConstants.lean#L33) | theorem | Every actual global function has a unique scalar preimage under that map. |
| Actual sheaf character constancy for P 949–950 | [`properScheme_global_character_constant`](Normalizer/ProperConstants.lean#L42) | theorem | Any actual morphism from a scheme module sheaf to the unit sheaf has a unique scalar value on each global section. Applies to the constructed quotient character once the actual scheme data is supplied. |
| General support; exact hypotheses in the linked declaration | [`schemeConstantMap`](Normalizer/ProperConstants.lean#L65) | def | Actual base-field constant-function map from the scheme structure morphism. |
| General support; exact hypotheses in the linked declaration | [`schemeConstantMap_bijective`](Normalizer/ProperConstants.lean#L70) | theorem | Universal closedness over an algebraically closed field and integrality of the actual scheme imply bijectivity of its constant map; no global-function isomorphism is assumed. |
| General support; exact hypotheses in the linked declaration | [`properConstantEquiv`](Normalizer/ProperConstants.lean#L79) | def | Constructed ring isomorphism from the base field to actual global regular functions. |
| General support; exact hypotheses in the linked declaration | [`proper_global_function_constant`](Normalizer/ProperConstants.lean#L84) | theorem | Every actual global regular function is a unique base-field constant, from the geometric hypotheses. |
| General support; exact hypotheses in the linked declaration | [`schemeConstantAt`](Normalizer/ProperConstants.lean#L93) | def | The constant-function map restricted to any actual open. |
| General support; exact hypotheses in the linked declaration | [`proper_global_function_restrict`](Normalizer/ProperConstants.lean#L97) | theorem | The unique global scalar represents the regular function on every open. |

## ProperGlobalCharacter

| Source / mathematical role | Lean declaration | Kind | Exact coverage |
|---|---|---|---|
| General support; exact hypotheses in the linked declaration | [`schemeGlobalSectionsModuleOfMorphism`](Normalizer/ProperGlobalCharacter.lean#L19) | def | Base-field module structure on actual global bundle sections induced by the scheme structure morphism. |
| General support; exact hypotheses in the linked declaration | [`properGlobalCharacter`](Normalizer/ProperGlobalCharacter.lean#L28) | def | Base-field-linear functional on actual global sections, constructed from a sheaf functional and proved geometric constancy. |
| General support; exact hypotheses in the linked declaration | [`properGlobalCharacter_spec`](Normalizer/ProperGlobalCharacter.lean#L47) | theorem | The constructed global scalar maps to the actual global functional value. |
| General support; exact hypotheses in the linked declaration | [`properGlobalCharacter_restrict`](Normalizer/ProperGlobalCharacter.lean#L54) | theorem | The same scalar describes the functional on the restricted global section on every open, derived from naturality. |
| General support; exact hypotheses in the linked declaration | [`properGlobalCharacter_germ`](Normalizer/ProperGlobalCharacter.lean#L63) | theorem | The actual stalk functional on a global germ equals the germ of its unique global scalar at every point. |

## ProperNormalizerCharacter

| Source / mathematical role | Lean declaration | Kind | Exact coverage |
|---|---|---|---|
| General support; exact hypotheses in the linked declaration | [`schemeLineNormalizerQuotient`](Normalizer/ProperNormalizerCharacter.lean#L30) | abbrev | Actual line-normalizer quotient sheaf as a scheme module; abelianness follows from alternating action and genuine line frames. |
| General support; exact hypotheses in the linked declaration | [`schemeNormalizerCharacter`](Normalizer/ProperNormalizerCharacter.lean#L40) | def | The sheaf action coefficient constructed from actual local line trivializations; commutativity comes from the scheme. |
| General support; exact hypotheses in the linked declaration | [`properNormalizerScalar`](Normalizer/ProperNormalizerCharacter.lean#L49) | def | Base-field-valued scalar on actual normalizer quotient global sections, with the sheaf functional and global constancy both constructed. |
| General support; exact hypotheses in the linked declaration | [`properNormalizerScalar_generic`](Normalizer/ProperNormalizerCharacter.lean#L57) | theorem | Constructed normalizer scalar agrees with the induced generic sheaf functional on actual evaluation; no supplied scalar compatibility or sheaf functional. |

## ProperTrivialEvaluation

| Source / mathematical role | Lean declaration | Kind | Exact coverage |
|---|---|---|---|
| General support; exact hypotheses in the linked declaration | [`schemeGenericSectionsScalarTower`](Normalizer/ProperTrivialEvaluation.lean#L20) | theorem | Actual constant-field and function-field scalar actions on the generic fibre form a scalar tower. |
| General support; exact hypotheses in the linked declaration | [`schemeGlobalSectionsMap`](Normalizer/ProperTrivialEvaluation.lean#L30) | def | Actual sheaf map induces a base-field-linear map on actual global sections. |
| General support; exact hypotheses in the linked declaration | [`schemeGlobalSectionsIso`](Normalizer/ProperTrivialEvaluation.lean#L45) | def | Actual sheaf isomorphism induces a base-field-linear equivalence on actual global sections. |
| General support; exact hypotheses in the linked declaration | [`properTrivialCoordinates`](Normalizer/ProperTrivialEvaluation.lean#L62) | def | Scalar coordinates on global sections of the actual trivial sheaf, using geometric constancy. |
| General support; exact hypotheses in the linked declaration | [`properTrivialCoordinates_injective`](Normalizer/ProperTrivialEvaluation.lean#L70) | theorem | Constructed global scalar coordinates are injective. |
| General support; exact hypotheses in the linked declaration | [`properTrivialCoordinates_generic`](Normalizer/ProperTrivialEvaluation.lean#L84) | theorem | The actual generic coordinate tuple is the scalar extension of the global scalar tuple. |
| General support; exact hypotheses in the linked declaration | [`properTrivialEvaluation_frame`](Normalizer/ProperTrivialEvaluation.lean#L92) | theorem | Actual generic evaluation satisfies the constructed frame formula; no coordinate compatibility is assumed. |
| General support; exact hypotheses in the linked declaration | [`properTrivialEvaluation_tensor_injective`](Normalizer/ProperTrivialEvaluation.lean#L101) | theorem | Canonical tensor evaluation of the actual finite trivial sheaf is injective. |
| General support; exact hypotheses in the linked declaration | [`properTrivializedCoordinates`](Normalizer/ProperTrivialEvaluation.lean#L120) | def | Scalar coordinates on global sections transported through an actual global sheaf trivialization. |
| General support; exact hypotheses in the linked declaration | [`properTrivializedGenericFrame`](Normalizer/ProperTrivialEvaluation.lean#L129) | def | Generic frame constructed by the actual stalk isomorphism of a global sheaf trivialization. |
| General support; exact hypotheses in the linked declaration | [`properTrivializedCoordinates_injective`](Normalizer/ProperTrivialEvaluation.lean#L136) | theorem | Coordinates supplied by the genuine global trivialization are injective. |
| General support; exact hypotheses in the linked declaration | [`properTrivializedGenericFrame_injective`](Normalizer/ProperTrivialEvaluation.lean#L142) | theorem | Independence of the generic frame is derived from the actual global sheaf trivialization. |
| General support; exact hypotheses in the linked declaration | [`properTrivializedEvaluation_frame`](Normalizer/ProperTrivialEvaluation.lean#L149) | theorem | Actual generic evaluation has the frame formula derived from the global sheaf trivialization. |
| General support; exact hypotheses in the linked declaration | [`properTrivializedEvaluation_tensor_injective`](Normalizer/ProperTrivialEvaluation.lean#L162) | theorem | Canonical tensor evaluation is injective for an actual globally trivialized module sheaf. |

## Quotients

| Source / mathematical role | Lean declaration | Kind | Exact coverage |
|---|---|---|---|
| General support; exact hypotheses in the linked declaration | [`rightAdjoint`](Normalizer/Quotients.lean#L8) | def | Quotients |
| General support; exact hypotheses in the linked declaration | [`lineNormalizer`](Normalizer/Quotients.lean#L20) | def | Quotients |
| [P 937–947](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L937-L947); [A 39–43](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/LOAD_BEARING_AUDIT.md#L39-L43) | [`mem_lineNormalizer`](Normalizer/Quotients.lean#L25) | theorem | Actual matrix normalizer membership: trace zero and a scalar action on the specified line. |
| General support; exact hypotheses in the linked declaration | [`semCoordinates`](Normalizer/Quotients.lean#L31) | def | Quotients |
| General support; exact hypotheses in the linked declaration | [`nilCoordinates`](Normalizer/Quotients.lean#L36) | def | Quotients |
| [P 985–987](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L985-L987); presentation infrastructure | [`sem_coordinates_lift`](Normalizer/Quotients.lean#L41) | theorem | Semisimple coordinates recover the quotient vector independently of its line lift. |
| [P 992–997](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L992-L997); presentation infrastructure | [`nil_coordinates_lift`](Normalizer/Quotients.lean#L45) | theorem | Minimal coordinates recover the quotient vector independently of its line lift. |
| General support; exact hypotheses in the linked declaration | [`semProjection`](Normalizer/Quotients.lean#L49) | def | Quotients |
| General support; exact hypotheses in the linked declaration | [`nilProjection`](Normalizer/Quotients.lean#L52) | def | Quotients |
| [P 985–987](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L985-L987); presentation infrastructure | [`sem_projection_surjective`](Normalizer/Quotients.lean#L55) | theorem | All three semisimple quotient coordinates are realized by actual normalizer matrices. |
| [P 992–997](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L992-L997); presentation infrastructure | [`nil_projection_surjective`](Normalizer/Quotients.lean#L63) | theorem | All four minimal quotient coordinates are realized by actual normalizer matrices. |
| [P 937–942](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L937-L942), 985–987 | [`sem_projection_kernel`](Normalizer/Quotients.lean#L72) | theorem | Projection kernel is exactly the distinguished scalar line; quotient is not an unrelated coordinate definition. |
| [P 937–942](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L937-L942), 992–997 | [`nil_projection_kernel`](Normalizer/Quotients.lean#L87) | theorem | Projection kernel is exactly F E12. |
| General support; exact hypotheses in the linked declaration | [`SemQuotient`](Normalizer/Quotients.lean#L102) | abbrev | Quotients |
| General support; exact hypotheses in the linked declaration | [`NilQuotient`](Normalizer/Quotients.lean#L104) | abbrev | Quotients |
| General support; exact hypotheses in the linked declaration | [`semQuotientEquiv`](Normalizer/Quotients.lean#L107) | def | Quotients |
| General support; exact hypotheses in the linked declaration | [`nilQuotientEquiv`](Normalizer/Quotients.lean#L109) | def | Quotients |
| [P 980–987](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L980-L987); [A 63–68](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/LOAD_BEARING_AUDIT.md#L63-L68) | [`sem_quotient_finrank`](Normalizer/Quotients.lean#L112) | theorem | The actual semisimple normalizer modulo its line has dimension 3. |
| [P 980–997](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L980-L997); [A 63–73](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/LOAD_BEARING_AUDIT.md#L63-L73) | [`nil_quotient_finrank`](Normalizer/Quotients.lean#L114) | theorem | The actual minimal normalizer modulo its line has dimension 4. |
| [P 937–942](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L937-L942), 985–987 | [`sem_projection_bracket`](Normalizer/Quotients.lean#L118) | theorem | Matrix commutators project to semBracket for all normalizer representatives. |
| [P 937–942](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L937-L942), 1003–1006 | [`nil_projection_bracket`](Normalizer/Quotients.lean#L129) | theorem | Matrix commutators project to nilBracket for all normalizer representatives. |
| [P 944–947](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L944-L947), 985–987 | [`sem_projection_character`](Normalizer/Quotients.lean#L140) | theorem | Any scalar action on the distinguished line is zero. |
| [P 944–947](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L944-L947), 999–1002 | [`nil_projection_character`](Normalizer/Quotients.lean#L146) | theorem | Any scalar action on E12 equals the quotient D-coordinate. |
| [P 985–987](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L985-L987); semisimple model | [`sem_frameCharacter`](Normalizer/Quotients.lean#L158) | theorem | The constructed character equals zero for the specified matrix. |
| [P 999–1002](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L999-L1002); minimal model | [`nil_frameCharacter`](Normalizer/Quotients.lean#L171) | theorem | It equals the specified D-coordinate. |

## RestrictionStalks

| Source / mathematical role | Lean declaration | Kind | Exact coverage |
|---|---|---|---|
| General support; exact hypotheses in the linked declaration | [`restrictionLocalRingEquiv`](Normalizer/RestrictionStalks.lean#L18) | def | RestrictionStalks |
| Restriction local-ring support for [P 936](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L936) | [`restrictionLocalRingEquiv_germ`](Normalizer/RestrictionStalks.lean#L23) | theorem | The actual local-ring isomorphism under an open immersion has the prescribed formula on germs using the actual section-ring isomorphism. |
| General support; exact hypotheses in the linked declaration | [`restrictionStalkAddIso`](Normalizer/RestrictionStalks.lean#L38) | def | RestrictionStalks |
| Restriction module-stalk support for [P 936](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L936) | [`restrictionStalkAddIso_germ`](Normalizer/RestrictionStalks.lean#L43) | theorem | The actual additive stalk identification under open restriction has the prescribed section-germ formula. |
| General support; exact hypotheses in the linked declaration | [`restrictionStalkEquiv`](Normalizer/RestrictionStalks.lean#L53) | def | RestrictionStalks |
| Free-stalk restriction supporting [P 936](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L936) | [`restrictionStalk_free`](Normalizer/RestrictionStalks.lean#L72) | theorem | A free actual stalk stays free under open restriction, transported semilinearly through the actual local-ring isomorphism. |

## SaturatedStalkQuotient

| Source / mathematical role | Lean declaration | Kind | Exact coverage |
|---|---|---|---|
| Actual stalk exactness support for P 936 | [`sheaf_cokernel_stalk_surjective`](Normalizer/SaturatedStalkQuotient.lean#L18) | theorem | The actual sheaf quotient projection is surjective on actual stalks, proved using local representatives. No surjectivity on fixed-open sections is asserted. |
| Actual stalk exactness support for P 936 | [`sheaf_cokernel_stalk_comp`](Normalizer/SaturatedStalkQuotient.lean#L32) | theorem | The morphism followed by its actual quotient projection is zero on stalks. |
| Actual stalk exactness support for P 936 | [`sheaf_cokernel_stalk_exact`](Normalizer/SaturatedStalkQuotient.lean#L45) | theorem | For a monomorphism, a stalk element killed by the quotient projection comes from a source stalk element. A zero germ is shrunk to a zero section before using exactness. |
| Actual stalk submodule support for P 936 | [`sheaf_cokernel_stalk_ker_eq_range`](Normalizer/SaturatedStalkQuotient.lean#L69) | theorem | The kernel of the actual stalk quotient projection equals the range of the actual stalk inclusion, as local-ring submodules. |
| Actual quotient comparison supporting P 936 | [`sheafCokernelStalkEquiv`](Normalizer/SaturatedStalkQuotient.lean#L80) | def | The quotient of actual stalk modules is linearly isomorphic over the actual local ring to the stalk of the actual sheaf cokernel. |
| Canonical projection support for P 936 | [`sheafCokernelStalkEquiv_mk`](Normalizer/SaturatedStalkQuotient.lean#L89) | theorem | The comparison sends a quotient class to its image under the actual stalk projection. |
| Scalar saturation support for P 936 | [`sheaf_cokernel_stalk_isTorsionFree_of_saturated`](Normalizer/SaturatedStalkQuotient.lean#L96) | theorem | On an integral scheme, scalar saturation of a mono's actual stalk range implies torsion-freeness of its actual cokernel stalk. |
| Exact saturation correspondence for P 936 | [`sheaf_cokernel_stalk_torsionFree_iff_saturated`](Normalizer/SaturatedStalkQuotient.lean#L117) | theorem | The converse also holds: actual quotient stalk torsion-freeness is equivalent to scalar saturation of the actual stalk inclusion. |
| Actual dimension support for P 936 | [`scheme_stalk_ringKrullDim_le`](Normalizer/SaturatedStalkQuotient.lean#L136) | theorem | Each actual local-ring dimension is bounded by scheme Krull dimension, through the point's coheight. |
| Saturated bundle quotient criterion supporting P 936 | [`saturatedFiniteBundle_cokernel_isLocallyFree`](Normalizer/SaturatedStalkQuotient.lean#L145) | theorem | An actual mono between bundles with finite free covers, on an integral scheme of dimension at most one with regular actual local rings, has locally free cokernel if its actual stalk ranges are scalar-saturated. Quotient finite presentation, free stalks and local dimension bounds are derived. |

## ScalarCharacter

| Source / mathematical role | Lean declaration | Kind | Exact coverage |
|---|---|---|---|
| P 945–950, 952–961 | [`schemeGlobalCharacter`](Normalizer/ScalarCharacter.lean#L17) | def | Actual global character as a linear map over the global function ring. |
| P 945–950, 952–961 | [`schemeGlobalSectionsModule`](Normalizer/ScalarCharacter.lean#L24) | def | Base-field module structure on global sections through the actual structure morphism. |
| P 945–950, 952–961 | [`properSchemeConstantEquiv`](Normalizer/ScalarCharacter.lean#L29) | def | Canonical constants map bundled as a ring equivalence, with bijectivity proved from properness. |
| P 945–950, 952–961 | [`properSchemeScalarCharacter`](Normalizer/ScalarCharacter.lean#L36) | def | Base-field-linear scalar character of an actual sheaf morphism on an integral proper scheme over an algebraically closed field. |
| P 945–950, 952–961 | [`properSchemeScalarCharacter_spec`](Normalizer/ScalarCharacter.lean#L58) | theorem | The scalar character maps back to the actual global function character. |
| P 945–950, 952–961 | [`properSchemeScalarCharacter_restrict`](Normalizer/ScalarCharacter.lean#L67) | theorem | The restricted global character is the restriction of its unique constant scalar. |
| P 945–950, 952–961 | [`properSchemeScalarCharacter_local_lift`](Normalizer/ScalarCharacter.lean#L81) | theorem | Every actual local lift has the same restricted constant character value. |
| P 945–950, 952–961 | [`properNormalizerScalarCharacter_action`](Normalizer/ScalarCharacter.lean#L117) | theorem | For the constructed normalizer quotient and genuine line frames, the local action coefficient agrees with the scalar character. |

## SchemeGenericEvaluation

| Source / mathematical role | Lean declaration | Kind | Exact coverage |
|---|---|---|---|
| General support; exact hypotheses in the linked declaration | [`schemeFunctionFieldConstantMap`](Normalizer/SchemeGenericEvaluation.lean#L16) | def | Actual inclusion of base-field constants into the function field via the generic germ. |
| General support; exact hypotheses in the linked declaration | [`schemeFunctionFieldAlgebra`](Normalizer/SchemeGenericEvaluation.lean#L21) | def | Base-field algebra structure on the actual function field. |
| General support; exact hypotheses in the linked declaration | [`schemeGenericSectionsModule`](Normalizer/SchemeGenericEvaluation.lean#L26) | def | Base-field module structure on the actual generic fibre by restriction of scalars. |
| General support; exact hypotheses in the linked declaration | [`schemeGenericEvaluation`](Normalizer/SchemeGenericEvaluation.lean#L32) | def | Actual base-field-linear generic evaluation, constructed as the germ map at the generic point. |
| General support; exact hypotheses in the linked declaration | [`schemeGenericEvaluation_natural`](Normalizer/SchemeGenericEvaluation.lean#L48) | theorem | Actual generic evaluation commutes with the actual stalk map of every sheaf morphism. |
| General support; exact hypotheses in the linked declaration | [`schemeGenericEvaluation_mem_kernel`](Normalizer/SchemeGenericEvaluation.lean#L56) | theorem | A section killed by a sheaf morphism evaluates in the actual kernel of its generic stalk map; no dimension assertion. |
| General support; exact hypotheses in the linked declaration | [`schemeGenericCharacter`](Normalizer/SchemeGenericEvaluation.lean#L64) | def | Actual function-field-linear generic functional induced from a supplied sheaf functional. |
| General support; exact hypotheses in the linked declaration | [`properGenericCharacter_compat`](Normalizer/SchemeGenericEvaluation.lean#L71) | theorem | Geometric constancy proves compatibility of the actual global scalar, generic functional, and generic evaluation; matrix identification is separate. |

## SectionDeterminantTrivialization

| Source / mathematical role | Lean declaration | Kind | Exact coverage |
|---|---|---|---|
| General support; exact hypotheses in the linked declaration | [`schemeSectionStalkMatrix`](Normalizer/SectionDeterminantTrivialization.lean#L20) | def | Actual stalk coordinate matrix of the given global section germs in a supplied stalk basis. |
| General support; exact hypotheses in the linked declaration | [`schemeSectionFrameMap_isIso_iff_unit_det`](Normalizer/SectionDeterminantTrivialization.lean#L41) | theorem | The actual global-section evaluation is an isomorphism iff its stalk coordinate determinant is a unit at every point; actual stalk bases are explicit inputs. |
| General support; exact hypotheses in the linked declaration | [`schemeSectionFrameIso`](Normalizer/SectionDeterminantTrivialization.lean#L56) | def | Constructed global sheaf trivialization from the prescribed sections and pointwise unit determinants. |
| General support; exact hypotheses in the linked declaration | [`schemeSectionFrameIso_standard`](Normalizer/SectionDeterminantTrivialization.lean#L65) | theorem | The constructed global trivialization sends each standard global section to the prescribed section. |
| General support; exact hypotheses in the linked declaration | [`schemeSectionFrameMap_isIso_iff_residue_det`](Normalizer/SectionDeterminantTrivialization.lean#L75) | theorem | The actual global-section evaluation is an isomorphism iff its reduced coordinate determinant is nonzero at every scheme point. |
| General support; exact hypotheses in the linked declaration | [`properSubsheaf_evaluation_finrank_of_unit_det`](Normalizer/SectionDeterminantTrivialization.lean#L100) | theorem | Actual section germs in an actual subsheaf with pointwise unit determinants imply dimension preservation for canonical generic tensor evaluation. The global trivialization and independent frame are constructed; the degree argument establishing unit determinants is separate. |

## SectionRankAssembly

| Source / mathematical role | Lean declaration | Kind | Exact coverage |
|---|---|---|---|
| General support; exact hypotheses in the linked declaration | [`slThree_section_dimension_le_of_frame`](Normalizer/SectionRankAssembly.lean#L19) | theorem | Kernel evaluation in the actual quotient, compatible constant coordinates and ambient frame, and the character boundary law imply dim W ≤ dim T + 2; curve construction of these data remains separate. |
| General support; exact hypotheses in the linked declaration | [`slThree_four_sections_of_frame`](Normalizer/SectionRankAssembly.lean#L48) | theorem | Adds dim T ≤ 2 to the explicit frame and kernel-boundary interface and concludes dim W ≤ 4; this is not the actual curve proposition. |

## SemisimpleNormalizer

| Source / mathematical role | Lean declaration | Kind | Exact coverage |
|---|---|---|---|
| General support; exact hypotheses in the linked declaration | [`eigenbasis_three`](Normalizer/SemisimpleNormalizer.lean#L11) | theorem | Spanning eigenspaces produce an eigenvector basis indexed by Fin 3. |
| General support; exact hypotheses in the linked declaration | [`matrixInBasis`](Normalizer/SemisimpleNormalizer.lean#L37) | def | Algebra equivalence expressing a matrix in the chosen basis. |
| General support; exact hypotheses in the linked declaration | [`matrixInBasis_trace`](Normalizer/SemisimpleNormalizer.lean#L40) | theorem | Change of basis preserves trace. |
| General support; exact hypotheses in the linked declaration | [`matrixInBasis_comm`](Normalizer/SemisimpleNormalizer.lean#L45) | theorem | Change of basis preserves commutators. |
| General support; exact hypotheses in the linked declaration | [`matrixInBasis_diagonal`](Normalizer/SemisimpleNormalizer.lean#L51) | theorem | The eigenvector equations give the actual diagonal transformed matrix. |
| General support; exact hypotheses in the linked declaration | [`diagonalizable_matrix_boundary_lift`](Normalizer/SemisimpleNormalizer.lean#L66) | theorem | The obstruction for every nonzero traceless matrix with spanning eigenspaces. |
| General support; exact hypotheses in the linked declaration | [`semisimple_matrix_boundary_lift`](Normalizer/SemisimpleNormalizer.lean#L83) | theorem | Over an algebraically closed characteristic-zero field, every nonzero traceless semisimple matrix satisfies the obstruction. |

## SheafBoundary

| Source / mathematical role | Lean declaration | Kind | Exact coverage |
|---|---|---|---|
| E1/E2, use of H⁰(E)=0 | [`sheaf_global_map_zero_of_vanishing`](Normalizer/SheafBoundary.lean#L21) | theorem | Vanishing of the actual global-section vector space makes the induced global morphism zero. |
| Alternative descent proof of [P 952–970](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L952-L970) | [`sheaf_boundary_law_of_overlaps`](Normalizer/SheafBoundary.lean#L30) | theorem | Actual sheaf gluing and separatedness give the global relation from local lifts and the overlap law, provided the global image of E in G is zero. This is a consequence of H⁰(E)=0; the general injective-boundary case still requires the geometric exactness input. |

## SheafCokernelFinitePresentation

| Source / mathematical role | Lean declaration | Kind | Exact coverage |
|---|---|---|---|
| Affine presentation support for P 936 | [`tilde_exists_finitePresentation`](Normalizer/SheafCokernelFinitePresentation.lean#L18) | theorem | A finitely presented module has a finite global presentation of its actual associated sheaf. |
| Affine quotient support for P 936 | [`affineCokernel_exists_finitePresentation`](Normalizer/SheafCokernelFinitePresentation.lean#L29) | theorem | Finite global presentations of source and target yield one for their actual affine sheaf cokernel, using the actual module quotient and tilde comparison. |
| Cover refinement support for P 936 | [`presentationRestrictFromOver`](Normalizer/SheafCokernelFinitePresentation.lean#L63) | def | Transports an actual over-site presentation to a smaller open subscheme. |
| Cover refinement support for P 936 | [`presentationRestrictFromOver_isFinite`](Normalizer/SheafCokernelFinitePresentation.lean#L77) | theorem | Restriction retains finite generator and relation index types. |
| Simultaneous affine presentation support for P 936 | [`exists_common_affineOpenCover_finitePresentation`](Normalizer/SheafCokernelFinitePresentation.lean#L90) | theorem | Two actual finitely presented sheaves admit finite global presentations on the same affine open cover. |
| Over-site assembly support for P 936 | [`openImmersionOverPresentation`](Normalizer/SheafCokernelFinitePresentation.lean#L138) | def | Moves a presentation along an open immersion to the over-site of its actual open image. |
| Over-site assembly support for P 936 | [`openImmersionOverPresentation_isFinite`](Normalizer/SheafCokernelFinitePresentation.lean#L159) | theorem | The actual image presentation retains finite generators and relations. |
| Finite-presentation assembly support for P 936 | [`sheaf_isFinitePresentation_of_affineCover`](Normalizer/SheafCokernelFinitePresentation.lean#L172) | theorem | Constructs mathlib finite-presentation data from finite global presentations on an actual affine open cover. |
| Quotient finite-presentation support for P 936 | [`sheaf_cokernel_isFinitePresentation`](Normalizer/SheafCokernelFinitePresentation.lean#L197) | theorem | On any scheme, the actual cokernel of any map between finitely presented module sheaves is finitely presented. No saturation or integrality hypothesis is needed. |
| Quotient local-freeness support for P 936 | [`sheaf_cokernel_isLocallyFree_of_regular_stalks`](Normalizer/SheafCokernelFinitePresentation.lean#L218) | theorem | On an integral scheme with regular local rings of dimension at most one, source and target finite presentation plus torsion-free cokernel stalks imply actual cokernel local freeness. Quotient finite presentation is derived. |

## SheafFinitePresentation

| Source / mathematical role | Lean declaration | Kind | Exact coverage |
|---|---|---|---|
| Actual finite-presentation support for [P 936](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L936) | [`sheafPresentation_isFinitePresentation`](Normalizer/SheafFinitePresentation.lean#L25) | theorem | An actual finite global sheaf presentation supplies mathlib's actual local finite-presentation property. |
| Affine finite-presentation support for [P 936](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L936) | [`presentationTilde_isFinite`](Normalizer/SheafFinitePresentation.lean#L42) | theorem | Finite module generators and relations remain finite in the actual global presentation of the associated sheaf. |
| Affine finite-presentation support for [P 936](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L936) | [`tilde_isFinitePresentation`](Normalizer/SheafFinitePresentation.lean#L58) | theorem | A finitely presented module gives an actual finitely presented associated sheaf. |
| Affine-section finite-presentation support for [P 936](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L936) | [`affinePresentation_sections_finitePresentation`](Normalizer/SheafFinitePresentation.lean#L69) | theorem | An actual finite global affine sheaf presentation yields finitely presented global sections by reconstructing a finite module cokernel and its sheaf isomorphism. No arbitrary right exactness of global sections is assumed. |
| Affine-cover refinement supporting [P 936](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L936) | [`exists_affineOpenCover_finitePresentation`](Normalizer/SheafFinitePresentation.lean#L101) | theorem | Mathlib's local finite-presentation property yields an actual affine open cover with actual finite global presentations on its restrictions. |

## SheafFreeNeighborhood

| Source / mathematical role | Lean declaration | Kind | Exact coverage |
|---|---|---|---|
| General pointwise local-freeness interface underlying [P 936](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L936) and [P 941](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L941) | [`sheafStalk_exists_finiteFree_neighborhood`](Normalizer/SheafFreeNeighborhood.lean#L23) | theorem | For any actual scheme module with mathlib finite presentation and a free actual stalk at x, constructs an affine open immersion whose image contains x and an isomorphism of the actual restricted sheaf to a finite free sheaf. |

## SheafOperationDescent

| Source / mathematical role | Lean declaration | Kind | Exact coverage |
|---|---|---|---|
| Support for [P 941–942](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L941-L942) and 952–956, checking local identities | [`sheaf_eq_of_local_lifts`](Normalizer/SheafOperationDescent.lean#L69) | theorem | Equality in any target module sheaf can be checked on a constructed cover of simultaneous lifts of three sections. Uses intersections of covering image sieves. |
| General support; exact hypotheses in the linked declaration | [`descendSheafOperation`](Normalizer/SheafOperationDescent.lean#L125) | def | SheafOperationDescent |
| Support for [P 941–942](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L941-L942), actual gluing | [`descendSheafOperation_local`](Normalizer/SheafOperationDescent.lean#L134) | theorem | A natural binary operation constant on fibres of a locally surjective map glues to a section, with the required value on every pair of local representatives. |
| Support for [P 941–942](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L941-L942), projection formula | [`descendSheafOperation_projection`](Normalizer/SheafOperationDescent.lean#L148) | theorem | The glued operation recovers its prescribed value on the images of two representatives. |
| Support for [P 941–942](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L941-L942), restriction law | [`descendSheafOperation_restrict`](Normalizer/SheafOperationDescent.lean#L157) | theorem | The glued operation commutes with restrictions for arbitrary target sections. |
| Support for [P 941–942](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L941-L942), uniqueness | [`descendSheafOperation_unique`](Normalizer/SheafOperationDescent.lean#L177) | theorem | Recovery on all local representatives uniquely determines the glued section. |

## SheafQuotientBracket

| Source / mathematical role | Lean declaration | Kind | Exact coverage |
|---|---|---|---|
| Support for [P 941–942](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L941-L942) and 952–956, quotient representatives | [`sheaf_cokernel_section_exact`](Normalizer/SheafQuotientBracket.lean#L26) | theorem | For any monomorphism of actual module sheaves, a section killed by its cokernel projection has a preimage in the original subsheaf on that same open. Derived using preservation of kernels by evaluation. |
| Support for [P 952–956](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L952-L956), existence of local lifts | [`sheaf_cokernel_locallySurjective`](Normalizer/SheafQuotientBracket.lean#L71) | theorem | Any actual sheaf-cokernel projection is locally surjective. Compared with sheafification of the presheaf cokernel. Does not assert lifts on every prescribed affine open. |
| [P 941–942](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L941-L942), line inclusion | [`normalizerLineInclusion_mono`](Normalizer/SheafQuotientBracket.lean#L102) | theorem | The constructed inclusion of the abelian subsheaf into its normalizer is monic. |
| [P 941–942](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L941-L942), kernel of quotient projection | [`normalizerQuotient_zero_iff`](Normalizer/SheafQuotientBracket.lean#L111) | theorem | A normalizer section maps to zero exactly when its ambient section belongs to the line subsheaf on that open. |
| [P 952–956](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L952-L956), differences of lifts | [`normalizerQuotient_eq_iff`](Normalizer/SheafQuotientBracket.lean#L129) | theorem | Two normalizer sections have equal quotient images exactly when their difference belongs to the line subsheaf. |
| General support; exact hypotheses in the linked declaration | [`normalizerSectionBracket`](Normalizer/SheafQuotientBracket.lean#L144) | def | SheafQuotientBracket |
| [P 941–942](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L941-L942), bracket restrictions | [`normalizerSectionBracket_restrict`](Normalizer/SheafQuotientBracket.lean#L151) | theorem | The actual normalizer-section bracket commutes with restrictions. |
| [P 941–942](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L941-L942), well-defined quotient bracket | [`normalizerQuotient_bracket_independent`](Normalizer/SheafQuotientBracket.lean#L164) | theorem | The projected bracket is independent of both representatives in the actual quotient sheaf, using skew symmetry and the normalizer property. |
| General support; exact hypotheses in the linked declaration | [`normalizerQuotientBracket`](Normalizer/SheafQuotientBracket.lean#L215) | def | SheafQuotientBracket |
| [P 941–942](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L941-L942), quotient bracket | [`normalizerQuotientBracket_projection`](Normalizer/SheafQuotientBracket.lean#L225) | theorem | The constructed bracket on actual quotient sections satisfies `[π(x),π(y)] = π([x,y])`. |
| [P 941–942](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L941-L942), sheaf compatibility | [`normalizerQuotientBracket_restrict`](Normalizer/SheafQuotientBracket.lean#L235) | theorem | The constructed quotient bracket commutes with restriction for all quotient sections, without assuming they lift on the full open. |

## SheafQuotientLie

| Source / mathematical role | Lean declaration | Kind | Exact coverage |
|---|---|---|---|
| [P 941–942](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L941-L942), Lie bracket | [`normalizerQuotientBracket_skew`](Normalizer/SheafQuotientLie.lean#L50) | theorem | Skew symmetry of the actual quotient operation follows by local lifting. |
| [P 941–942](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L941-L942), Lie bracket | [`normalizerQuotientBracket_add_left`](Normalizer/SheafQuotientLie.lean#L64) | theorem | Additivity in the first argument on arbitrary quotient sections. |
| [P 941–942](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L941-L942), Lie bracket | [`normalizerQuotientBracket_add_right`](Normalizer/SheafQuotientLie.lean#L83) | theorem | Additivity in the second argument, derived from the proved skew law. |
| [P 941–942](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L941-L942), O-bilinearity | [`normalizerQuotientBracket_smul_left`](Normalizer/SheafQuotientLie.lean#L92) | theorem | Scalar linearity in the first argument over each section ring; restrictions of scalars are respected in the local proof. |
| [P 941–942](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L941-L942), O-bilinearity | [`normalizerQuotientBracket_smul_right`](Normalizer/SheafQuotientLie.lean#L109) | theorem | Scalar linearity in the second argument, derived from the proved skew law. |
| [P 941–942](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L941-L942), Lie bracket | [`normalizerQuotientBracket_alternating`](Normalizer/SheafQuotientLie.lean#L120) | theorem | Ambient alternation gives alternation on arbitrary quotient sections, with no characteristic restriction. |
| [P 941–942](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L941-L942), Lie bracket | [`normalizerQuotientBracket_jacobi`](Normalizer/SheafQuotientLie.lean#L131) | theorem | Jacobi on the quotient follows on a common cover of three local representatives. |
| General support; exact hypotheses in the linked declaration | [`normalizerQuotientLieRing`](Normalizer/SheafQuotientLie.lean#L151) | def | SheafQuotientLie |
| General support; exact hypotheses in the linked declaration | [`normalizerQuotientLieAlgebra`](Normalizer/SheafQuotientLie.lean#L169) | def | SheafQuotientLie |
| General support; exact hypotheses in the linked declaration | [`normalizerQuotientLieRestriction`](Normalizer/SheafQuotientLie.lean#L182) | def | SheafQuotientLie |
| [P 941–942](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L941-L942), sheaf restrictions | [`normalizerQuotientLieRestriction_apply`](Normalizer/SheafQuotientLie.lean#L194) | theorem | The bundled Lie homomorphism acts exactly as the actual sheaf restriction. |
| [P 941–942](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L941-L942), sheaf restrictions | [`normalizerQuotientLieRestriction_id`](Normalizer/SheafQuotientLie.lean#L200) | theorem | Bundled restrictions preserve identity maps. |
| [P 941–942](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L941-L942), sheaf restrictions | [`normalizerQuotientLieRestriction_comp`](Normalizer/SheafQuotientLie.lean#L211) | theorem | Bundled restrictions compose as the actual sheaf restrictions do. |
| [P 944–947](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L944-L947), grading character | [`sectionFrameCharacter_bracket`](Normalizer/SheafQuotientLie.lean#L234) | theorem | In a genuine frame the character kills brackets, since Jacobi gives the commutator of two scalar multiplications. |
| [P 944–947](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L944-L947), grading character | [`quotientCharacterOfTrivializations_projected_bracket`](Normalizer/SheafQuotientLie.lean#L254) | theorem | The actual sheaf character kills projected normalizer brackets on every open, using the cover of genuine trivializations. |
| [P 944–947](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L944-L947), grading character | [`quotientCharacterOfTrivializations_bracket`](Normalizer/SheafQuotientLie.lean#L282) | theorem | The actual quotient character kills brackets of arbitrary quotient sections, without assuming global representatives. |
| General support; exact hypotheses in the linked declaration | [`quotientCharacterLieHom`](Normalizer/SheafQuotientLie.lean#L302) | def | SheafQuotientLie |
| [P 944–947](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L944-L947), Lie-character bundling | [`quotientCharacterLieHom_apply`](Normalizer/SheafQuotientLie.lean#L323) | theorem | The bundled Lie-algebra homomorphism agrees with the original sheaf character on every section. |

## SheafStalkCokernel

| Source / mathematical role | Lean declaration | Kind | Exact coverage |
|---|---|---|---|
| General support; exact hypotheses in the linked declaration | [`schemeCokernelStalk_surjective`](Normalizer/SheafStalkCokernel.lean#L20) | theorem | Actual sheaf-cokernel projection is surjective on actual stalks, using local surjectivity. |
| General support; exact hypotheses in the linked declaration | [`schemeCokernelStalk_ker`](Normalizer/SheafStalkCokernel.lean#L28) | theorem | For an actual sheaf monomorphism, the kernel of the cokernel stalk map equals the range of the original stalk map, by shrinking a germ equality. |
| General support; exact hypotheses in the linked declaration | [`schemeCokernelStalkEquiv`](Normalizer/SheafStalkCokernel.lean#L63) | def | Constructed equivalence between the quotient of actual stalks and the stalk of the actual sheaf cokernel. |
| General support; exact hypotheses in the linked declaration | [`schemeCokernelStalkEquiv_mk`](Normalizer/SheafStalkCokernel.lean#L72) | theorem | The cokernel-stalk equivalence sends a quotient class to its actual projected stalk element. |

## SheafStalkFunctional

| Source / mathematical role | Lean declaration | Kind | Exact coverage |
|---|---|---|---|
| General support; exact hypotheses in the linked declaration | [`schemeStalkFunctional`](Normalizer/SheafStalkFunctional.lean#L44) | def | Local-ring-linear functional on the actual module stalk, constructed from the stalk colimit of a supplied sheaf functional. |
| General support; exact hypotheses in the linked declaration | [`schemeStalkFunctional_germ`](Normalizer/SheafStalkFunctional.lean#L60) | theorem | The constructed stalk functional has the actual sheaf functional germ formula. |

## SheafStalkMap

| Source / mathematical role | Lean declaration | Kind | Exact coverage |
|---|---|---|---|
| General support; exact hypotheses in the linked declaration | [`schemeModuleStalkMap`](Normalizer/SheafStalkMap.lean#L16) | def | SheafStalkMap |
| Actual stalk-map support for [P 936](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L936) | [`schemeModuleStalkMap_germ`](Normalizer/SheafStalkMap.lean#L37) | theorem | The constructed local-ring-linear stalk map takes an actual germ to the germ of its image under the sheaf morphism. |
| General support; exact hypotheses in the linked declaration | [`schemeModuleStalkIso`](Normalizer/SheafStalkMap.lean#L45) | def | SheafStalkMap |

## SheafifyLocalIso

| Source / mathematical role | Lean declaration | Kind | Exact coverage |
|---|---|---|---|
| Support for [P 938](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L938), local-to-global sheaf argument | [`modulePresheaf_locallyInjective_of_cover`](Normalizer/SheafifyLocalIso.lean#L23) | theorem | Injectivity on every subopen of a genuine cover gives local injectivity; the source need not be separated. |
| Support for [P 938](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L938), local-to-global sheaf argument | [`modulePresheaf_locallySurjective_of_cover`](Normalizer/SheafifyLocalIso.lean#L38) | theorem | Surjectivity on every subopen of a genuine cover gives local surjectivity. |
| Support for [P 938](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L938), local-to-global sheaf argument | [`sheafificationLift_isIso_of_locallyBijective`](Normalizer/SheafifyLocalIso.lean#L50) | theorem | A locally bijective presheaf map to a sheaf induces an isomorphism from its actual sheafification. |
| Support for [P 938](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L938), local-to-global sheaf argument | [`sheafificationLift_isIso_of_cover`](Normalizer/SheafifyLocalIso.lean#L72) | theorem | Bijectivity on a genuine cover and its subopens proves that the actual sheafification lift is invertible globally. |

## SlTwo

| Source / mathematical role | Lean declaration | Kind | Exact coverage |
|---|---|---|---|
| General support; exact hypotheses in the linked declaration | [`slTwoEquiv`](Normalizer/SlTwo.lean#L8) | def | SlTwo |
| [P 985–987](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L985-L987) | [`slTwo_bracket`](Normalizer/SlTwo.lean#L29) | theorem | The coordinate equivalence to mathlib SpecialLinear.sl (Fin 2) F preserves the bracket. |
| General support; exact hypotheses in the linked declaration | [`semQuotientSlTwoEquiv`](Normalizer/SlTwo.lean#L37) | def | SlTwo |
| [P 985–987](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L985-L987) | [`sem_quotient_slTwo_bracket`](Normalizer/SlTwo.lean#L41) | theorem | The actual quotient’s linear equivalence to mathlib sl2 preserves the bracket. |

## SmoothRegularity

| Source / mathematical role | Lean declaration | Kind | Exact coverage |
|---|---|---|---|
| Étale affine-chart support for P 936 | [`regularLocal_localization_of_etale`](Normalizer/SmoothRegularity.lean#L16) | theorem | Every prime localization of an étale algebra over a regular ring is regular, using the actual local algebra map at the contracted prime. |
| Smooth affine-chart support for P 936 | [`regularLocal_localization_of_smooth`](Normalizer/SmoothRegularity.lean#L40) | theorem | Every prime localization of a smooth algebra over any field is regular. An actual smooth affine neighborhood factors through an étale algebra over a finite polynomial ring. |

## SmoothSchemeStalks

| Source / mathematical role | Lean declaration | Kind | Exact coverage |
|---|---|---|---|
| Actual regular stalks supporting P 936 | [`smoothScheme_stalk_isRegularLocalRing`](Normalizer/SmoothSchemeStalks.lean#L18) | theorem | All actual structure-sheaf stalks of a scheme smooth over a field are regular, by actual affine section localization. No integrality or dimension assumption is used here. |
| Smooth-curve saturated quotient criterion for P 936 | [`smoothCurve_saturatedFiniteBundle_cokernel_isLocallyFree`](Normalizer/SmoothSchemeStalks.lean#L43) | theorem | On an integral scheme smooth over a field of dimension at most one, a mono between actual finite-free-covered bundles with scalar-saturated actual stalk ranges has locally free actual cokernel. Regularity is derived from smoothness. |

## SquareZero

| Source / mathematical role | Lean declaration | Kind | Exact coverage |
|---|---|---|---|
| General support; exact hypotheses in the linked declaration | [`square_zero_three_basis`](Normalizer/SquareZero.lean#L15) | theorem | Constructs the basis (fv, v, w), with w in the kernel outside the span of fv, for a nonzero square-zero operator. |
| General support; exact hypotheses in the linked declaration | [`square_zero_conjugate_nil`](Normalizer/SquareZero.lean#L71) | theorem | Constructs an invertible matrix carrying an arbitrary nonzero square-zero matrix to the checked nilM model. |
| General support; exact hypotheses in the linked declaration | [`square_zero_trace`](Normalizer/SquareZero.lean#L96) | theorem | Every square-zero three-by-three matrix has trace zero, including the zero matrix. |
| General support; exact hypotheses in the linked declaration | [`traceless_shift_square_zero`](Normalizer/SquareZero.lean#L106) | theorem | Trace zero and a square-zero scalar shift force the scalar to vanish in characteristic zero. |
| General support; exact hypotheses in the linked declaration | [`square_zero_matrix_boundary_lift`](Normalizer/SquareZero.lean#L114) | theorem | The checked nilpotent obstruction for every nonzero square-zero matrix, with conjugacy derived. |

## StalkBracket

| Source / mathematical role | Lean declaration | Kind | Exact coverage |
|---|---|---|---|
| Support for P 941–943, 977–979 | [`schemeModuleStalkBilinear`](Normalizer/StalkBracket.lean#L131) | def | Constructs the local-ring-bilinear operation on the actual module stalk from restriction-compatible bilinear section operations. |
| Support for P 941–943, 977–979 | [`schemeModuleStalkBilinear_germ`](Normalizer/StalkBracket.lean#L146) | theorem | The stalk operation commutes with actual germs. |
| Support for P 941–943, 977–979 | [`schemeModuleStalkBilinear_unique`](Normalizer/StalkBracket.lean#L154) | theorem | Uniqueness of the stalk operation with the germ formula. |
| Support for P 941–943, 977–979 | [`schemeModuleStalkBilinear_self_eq_zero`](Normalizer/StalkBracket.lean#L166) | theorem | Sectionwise alternation descends to actual stalks. |
| Support for P 941–943, 977–979 | [`schemeModuleStalkBilinear_leibniz`](Normalizer/StalkBracket.lean#L175) | theorem | Sectionwise Jacobi in Leibniz form descends to actual stalks. |
| Support for P 941–943, 977–979 | [`schemeUnitStalkEquiv`](Normalizer/StalkBracket.lean#L203) | def | Identifies the actual unit-sheaf module stalk with the actual structure-ring stalk. |
| Support for P 941–943, 977–979 | [`schemeUnitStalkEquiv_germ`](Normalizer/StalkBracket.lean#L223) | theorem | The identification agrees with actual germs. |
| Support for P 941–943, 977–979 | [`schemeModuleStalkCharacter`](Normalizer/StalkBracket.lean#L232) | def | Constructs the actual local-ring-linear stalk character from a sheaf morphism. |
| Support for P 941–943, 977–979 | [`schemeModuleStalkCharacter_germ`](Normalizer/StalkBracket.lean#L237) | theorem | The stalk character commutes with actual germs. |

## StalkLocalFreeness

| Source / mathematical role | Lean declaration | Kind | Exact coverage |
|---|---|---|---|
| Local-ring support for [P 936](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L936) | [`principalIdealRing_of_regularLocal_dim_le_one`](Normalizer/StalkLocalFreeness.lean#L21) | theorem | A regular local domain with Krull dimension at most one is a principal ideal ring; includes fields. Smoothness is not assumed to imply regularity here. |
| Affine finite-stalk support for [P 936](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L936) | [`affinePresentation_stalk_finite`](Normalizer/StalkLocalFreeness.lean#L32) | theorem | A finite global presentation of an actual affine sheaf gives finite actual stalks over the actual local rings. |
| Finite-stalk support for [P 936](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L936) | [`sheaf_stalk_finite_of_finitePresentation`](Normalizer/StalkLocalFreeness.lean#L45) | theorem | An actual finitely presented scheme module sheaf has finite actual stalks, using finite affine presentations and the actual semilinear restriction equivalence. |
| Local-freeness support for [P 936](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L936) and [P 941](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L941) | [`sheaf_isLocallyFree_of_torsionFree_stalks`](Normalizer/StalkLocalFreeness.lean#L64) | theorem | On an integral scheme with actual principal ideal local rings, actual finite presentation and torsion-free stalks imply IsLocallyFree. |
| Kernel saturation support for [P 941](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L941) | [`kernelCokernel_isLocallyFree`](Normalizer/StalkLocalFreeness.lean#L79) | theorem | The actual quotient by a sheaf kernel is locally free under explicit quotient finite presentation, principal ideal local rings on an integral scheme, and torsion-free target stalks. Does not automatically prove the kernel itself locally free. |
| Regular dimension-one criterion underlying [P 936](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L936) | [`sheaf_isLocallyFree_of_regular_stalks`](Normalizer/StalkLocalFreeness.lean#L91) | theorem | On an integral scheme with regular actual local rings of dimension at most one, actual finite presentation and torsion-free stalks imply IsLocallyFree. The curve must still supply these hypotheses. |

## TopExteriorCoordinate

| Source / mathematical role | Lean declaration | Kind | Exact coverage |
|---|---|---|---|
| General support; exact hypotheses in the linked declaration | [`topExteriorCoordinate`](Normalizer/TopExteriorCoordinate.lean#L13) | def | Actual top-exterior coordinate map constructed from the determinant alternating form. |
| General support; exact hypotheses in the linked declaration | [`topExteriorCoordinate_ιMulti`](Normalizer/TopExteriorCoordinate.lean#L18) | theorem | The coordinate of an actual pure top wedge is its column-coordinate determinant. |
| General support; exact hypotheses in the linked declaration | [`topExteriorCoordinate_basis`](Normalizer/TopExteriorCoordinate.lean#L24) | theorem | The reference-basis wedge has coordinate one. |
| General support; exact hypotheses in the linked declaration | [`topExteriorCoordinate_expansion`](Normalizer/TopExteriorCoordinate.lean#L30) | theorem | Every top exterior vector equals its coordinate times the reference-basis wedge. |
| General support; exact hypotheses in the linked declaration | [`topExteriorCoordinateEquiv`](Normalizer/TopExteriorCoordinate.lean#L44) | def | Constructed actual top-exterior module equivalence with the coefficient ring; the inverse is multiplication by the basis wedge. |
| General support; exact hypotheses in the linked declaration | [`topExteriorCoordinateEquiv_apply`](Normalizer/TopExteriorCoordinate.lean#L54) | theorem | Forward formula for the constructed top-exterior coordinate equivalence. |
| General support; exact hypotheses in the linked declaration | [`topExteriorCoordinateEquiv_symm_apply`](Normalizer/TopExteriorCoordinate.lean#L58) | theorem | Inverse formula for the constructed top-exterior coordinate equivalence. |

## TopWedgeCoordinates

| Source / mathematical role | Lean declaration | Kind | Exact coverage |
|---|---|---|---|
| General support; exact hypotheses in the linked declaration | [`topWedge_eq_det_smul`](Normalizer/TopWedgeCoordinates.lean#L15) | theorem | Actual top wedge equals the coordinate determinant times the reference-basis wedge, over every commutative ring. |

## TracelessNormalizer

| Source / mathematical role | Lean declaration | Kind | Exact coverage |
|---|---|---|---|
| General support; exact hypotheses in the linked declaration | [`traceless_matrix_boundary_lift`](Normalizer/TracelessNormalizer.lean#L16) | theorem | Exhaustive endpoint for every nonzero traceless matrix over an algebraically closed characteristic-zero field, under precisely MatrixBoundaryLift; the subsequent scalar-extension theorem handles arbitrary characteristic-zero fields. |

## TrivialBundle

| Source / mathematical role | Lean declaration | Kind | Exact coverage |
|---|---|---|---|
| General support; exact hypotheses in the linked declaration | [`schemeTrivialBundle`](Normalizer/TrivialBundle.lean#L21) | abbrev | Actual finite trivial sheaf as a biproduct of unit sheaves. |
| General support; exact hypotheses in the linked declaration | [`schemeTrivialBundleIsoFree`](Normalizer/TrivialBundle.lean#L26) | def | Canonical isomorphism of the biproduct model with mathlib's finite free sheaf. |
| General support; exact hypotheses in the linked declaration | [`schemeTrivialProjection`](Normalizer/TrivialBundle.lean#L31) | def | Actual sheaf morphism giving each coordinate. |
| General support; exact hypotheses in the linked declaration | [`schemeTrivialSection`](Normalizer/TrivialBundle.lean#L36) | def | Actual standard section on every open, obtained from a biproduct inclusion applied to one. |
| General support; exact hypotheses in the linked declaration | [`schemeTrivialCoordinates`](Normalizer/TrivialBundle.lean#L41) | def | Constructed coordinate linear equivalence on every open, using preservation of finite biproducts by evaluation. |
| General support; exact hypotheses in the linked declaration | [`schemeTrivialCoordinates_apply`](Normalizer/TrivialBundle.lean#L50) | theorem | Actual coordinate is the corresponding evaluated sheaf projection. |
| General support; exact hypotheses in the linked declaration | [`schemeTrivialCoordinates_section`](Normalizer/TrivialBundle.lean#L67) | theorem | Kronecker coordinate formula for the constructed standard sections. |
| General support; exact hypotheses in the linked declaration | [`schemeTrivialSection_restrict`](Normalizer/TrivialBundle.lean#L83) | theorem | Standard sections commute with all open restrictions. |
| General support; exact hypotheses in the linked declaration | [`schemeTrivialSection_expansion`](Normalizer/TrivialBundle.lean#L95) | theorem | Actual sections expand in the constructed finite frame with their regular-function coordinates. |

## TrivialBundleStalk

| Source / mathematical role | Lean declaration | Kind | Exact coverage |
|---|---|---|---|
| General support; exact hypotheses in the linked declaration | [`schemeTrivialStalkCoordinates`](Normalizer/TrivialBundleStalk.lean#L18) | def | Coordinates on the actual stalk, induced by the actual sheaf projections. |
| General support; exact hypotheses in the linked declaration | [`schemeTrivialStalkFrame`](Normalizer/TrivialBundleStalk.lean#L24) | def | Constructed local-ring-linear frame map, using germs of the standard global sections. |
| General support; exact hypotheses in the linked declaration | [`schemeTrivialStalkCoordinates_germ`](Normalizer/TrivialBundleStalk.lean#L33) | theorem | Stalk coordinates of a local section germ are germs of its regular-function coordinates. |
| General support; exact hypotheses in the linked declaration | [`schemeTrivialStalkCoordinates_frame`](Normalizer/TrivialBundleStalk.lean#L43) | theorem | The constructed coordinate map is a left inverse to the actual stalk frame. |
| General support; exact hypotheses in the linked declaration | [`schemeTrivialStalkFrame_injective`](Normalizer/TrivialBundleStalk.lean#L54) | theorem | Independence of the actual stalk frame follows from its proved coordinate left inverse. |
| General support; exact hypotheses in the linked declaration | [`schemeTrivialStalkFrame_coordinates`](Normalizer/TrivialBundleStalk.lean#L59) | theorem | Every actual stalk element has its finite frame expansion, by taking a local representative. |
| General support; exact hypotheses in the linked declaration | [`schemeTrivialStalkEquiv`](Normalizer/TrivialBundleStalk.lean#L74) | def | Constructed actual stalk coordinate equivalence over the local ring at any scheme point. |

## TrivializedCharacter

| Source / mathematical role | Lean declaration | Kind | Exact coverage |
|---|---|---|---|
| General support; exact hypotheses in the linked declaration | [`lineTrivializationAt`](Normalizer/TrivializedCharacter.lean#L24) | def | TrivializedCharacter |
| Support for [P 944–947](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L944-L947), local frame restrictions | [`lineTrivializationAt_restrict`](Normalizer/TrivializedCharacter.lean#L32) | theorem | Evaluated basis isomorphisms commute with restriction by naturality of the actual sheaf trivialization. |
| General support; exact hypotheses in the linked declaration | [`sectionFrameCharacter`](Normalizer/TrivializedCharacter.lean#L51) | def | TrivializedCharacter |
| [P 944–947](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L944-L947), scalar action equation | [`sectionFrameCharacter_action`](Normalizer/TrivializedCharacter.lean#L62) | theorem | The coefficient constructed using the inverse basis map acts on the frame by the stated scalar. |
| [P 944–947](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L944-L947), uniqueness of the coefficient | [`sectionFrameCharacter_unique`](Normalizer/TrivializedCharacter.lean#L72) | theorem | Injectivity of the actual basis isomorphism proves uniqueness. |
| [P 944–947](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L944-L947), action on the entire line | [`sectionFrameCharacter_action_all`](Normalizer/TrivializedCharacter.lean#L90) | theorem | Scalar-linearity and commutativity give the same action coefficient on every line section. |
| Support for [P 944–947](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L944-L947), frame independence | [`sectionFrameCharacter_independent`](Normalizer/TrivializedCharacter.lean#L103) | theorem | Any two basis isomorphisms give the same coefficient; transition coefficients are not inputs. |
| General support; exact hypotheses in the linked declaration | [`trivializationCharacter`](Normalizer/TrivializedCharacter.lean#L115) | def | TrivializedCharacter |
| Support for [P 944–947](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L944-L947), restriction compatibility | [`trivializationCharacter_restrict`](Normalizer/TrivializedCharacter.lean#L124) | theorem | The derived local character commutes with actual restriction maps. |
| Support for [P 944–947](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L944-L947), overlap compatibility | [`trivializationCharacter_agree`](Normalizer/TrivializedCharacter.lean#L152) | theorem | Characters from two genuine trivializations agree on each common subopen. |
| [P 942–947](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L942-L947), vanishing on the line | [`trivializationCharacter_kills_line`](Normalizer/TrivializedCharacter.lean#L167) | theorem | The computed coefficient vanishes on the abelian line subsheaf. |
| General support; exact hypotheses in the linked declaration | [`normalizerCharacterOfTrivializations`](Normalizer/TrivializedCharacter.lean#L183) | def | TrivializedCharacter |
| General support; exact hypotheses in the linked declaration | [`quotientCharacterOfTrivializations`](Normalizer/TrivializedCharacter.lean#L193) | def | TrivializedCharacter |
| [P 944–947](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L944-L947), quotient character on local lifts | [`quotientCharacterOfTrivializations_local`](Normalizer/TrivializedCharacter.lean#L204) | theorem | The actual sheaf quotient character evaluates to the computed local coefficient on each normalizer lift. |
| [P 944–947](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L944-L947), character action equation | [`quotientCharacterOfTrivializations_action`](Normalizer/TrivializedCharacter.lean#L214) | theorem | The constructed quotient character acts by its scalar on every local line section, using the actual cokernel projection. |
| [P 941–942](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L941-L942), abelian line | [`lineSubsheaf_abelian_of_trivializations`](Normalizer/TrivializedCharacter.lean#L242) | theorem | Rank-one trivializations, alternation and scalar-linearity imply abelianness on all opens by sheaf separatedness. |
| General support; exact hypotheses in the linked declaration | [`lineQuotientCharacter`](Normalizer/TrivializedCharacter.lean#L261) | def | TrivializedCharacter |

## TrivializedSubsheafEvaluation

| Source / mathematical role | Lean declaration | Kind | Exact coverage |
|---|---|---|---|
| General support; exact hypotheses in the linked declaration | [`schemeSubsheafGenericEvaluation`](Normalizer/TrivializedSubsheafEvaluation.lean#L17) | def | Actual generic evaluation of subsheaf global sections into the ambient generic fibre through its actual inclusion. |
| General support; exact hypotheses in the linked declaration | [`schemeSubsheafGenericEvaluation_apply`](Normalizer/TrivializedSubsheafEvaluation.lean#L32) | theorem | The constructed subsheaf evaluation is the ambient germ of the underlying section. |
| General support; exact hypotheses in the linked declaration | [`properTrivializedSubsheaf_tensor_injective`](Normalizer/TrivializedSubsheafEvaluation.lean#L46) | theorem | An actual global subsheaf trivialization gives injective tensor evaluation into the ambient fibre; all coordinate and independent-frame maps are constructed. |
| General support; exact hypotheses in the linked declaration | [`properTrivializedSubsheaf_evaluation_finrank`](Normalizer/TrivializedSubsheafEvaluation.lean#L71) | theorem | Every subspace of actual global sections of a globally trivialized subsheaf preserves dimension under canonical generic tensor evaluation; no saturation or local freeness of the ambient sheaf is assumed. |

## WedgeThree

| Source / mathematical role | Lean declaration | Kind | Exact coverage |
|---|---|---|---|
| General support; exact hypotheses in the linked declaration | [`wedgeTwo`](Normalizer/WedgeThree.lean#L23) | def | Actual two-fold exterior product in mathlib's second exterior power. |
| General support; exact hypotheses in the linked declaration | [`wedgeTwo_surjective_of_basis_three`](Normalizer/WedgeThree.lean#L113) | theorem | Every bivector is decomposable given an actual three-element basis, over any field. |
| General support; exact hypotheses in the linked declaration | [`exteriorTwo_injective_of_basis_three`](Normalizer/WedgeThree.lean#L128) | theorem | A linear map out of the second exterior power in dimension three is injective if it kills no nonzero exterior product. |
| General support; exact hypotheses in the linked declaration | [`wedgeTwo_surjective_of_finrank_three`](Normalizer/WedgeThree.lean#L139) | theorem | Basis-free decomposability of every bivector in a finite-dimensional space of dimension three. |
| General support; exact hypotheses in the linked declaration | [`exteriorTwo_injective_of_finrank_three`](Normalizer/WedgeThree.lean#L144) | theorem | Basis-free injectivity criterion from nonvanishing on nonzero exterior products. |
| General support; exact hypotheses in the linked declaration | [`exteriorTwo_target_finrank_ge_three`](Normalizer/WedgeThree.lean#L151) | theorem | If no nonzero exterior product is killed, the target has dimension at least three. |
| General support; exact hypotheses in the linked declaration | [`exists_independent_pair_in_wedge_kernel`](Normalizer/WedgeThree.lean#L161) | theorem | Any linear map from the actual second exterior power of a three-dimensional space to a space of dimension at most two kills the wedge of an independent pair; curve wedge and degree data are not constructed. |

## Specified section zero ideal continuation

The following additions supply constructions for the determinant route underlying
the manuscript's section bound. Their immediate source is the regular-section
construction of Stacks 31.15.10(2), not a new manuscript assertion. The global
zero ideal uses finite genuine line charts with quasi-compact inclusions.
Regularity is derived on integral schemes from nonzero generic germ.
The inverse image-ideal module and its section-preserving comparison are actual
module-sheaf constructions. A general bundled effective-Cartier-divisor/O(D)
API, divisor finiteness and degree comparison are not asserted here.

## SectionLocalEquation

| Source / mathematical role | Lean declaration | Kind | Exact coverage |
|---|---|---|---|
| Support for the specified-section construction in [Stacks 31.15.10(2)](https://stacks.math.columbia.edu/tag/01X0) | [`sectionLocalEquation`](Normalizer/SectionLocalEquation.lean#L18) | def | The actual local equation of the specified global section in a genuine line-bundle chart, evaluated on any smaller open. |
| Support for the specified-section construction in [Stacks 31.15.10(2)](https://stacks.math.columbia.edu/tag/01X0) | [`sectionLocalEquation_restrict`](Normalizer/SectionLocalEquation.lean#L23) | theorem | The local equations are compatible with the actual restriction maps. |
| Support for the specified-section construction in [Stacks 31.15.10(2)](https://stacks.math.columbia.edu/tag/01X0) | [`sectionLocalEquation_chart`](Normalizer/SectionLocalEquation.lean#L37) | theorem | The chart carries its actual scalar equation back to the specified section. |
| Support for the specified-section construction in [Stacks 31.15.10(2)](https://stacks.math.columbia.edu/tag/01X0) | [`sectionLocalEquation_smul_frame`](Normalizer/SectionLocalEquation.lean#L44) | theorem | The actual section is its local equation times the actual chart frame. |
| Support for the specified-section construction in [Stacks 31.15.10(2)](https://stacks.math.columbia.edu/tag/01X0) | [`sectionFrameTransition`](Normalizer/SectionLocalEquation.lean#L52) | def | The actual scalar transition from a second line chart to the first. |
| Support for the specified-section construction in [Stacks 31.15.10(2)](https://stacks.math.columbia.edu/tag/01X0) | [`sectionFrameTransition_isUnit`](Normalizer/SectionLocalEquation.lean#L60) | theorem | Transition coefficients of genuine line charts are units, including on empty opens. Their inverses are derived from the inverse sheaf maps. |
| Support for the specified-section construction in [Stacks 31.15.10(2)](https://stacks.math.columbia.edu/tag/01X0) | [`sectionLocalEquation_change_chart`](Normalizer/SectionLocalEquation.lean#L75) | theorem | The two local equations of the same specified section differ by the actual invertible transition coefficient. |
| Support for the specified-section construction in [Stacks 31.15.10(2)](https://stacks.math.columbia.edu/tag/01X0) | [`sectionLocalEquation_ne_zero`](Normalizer/SectionLocalEquation.lean#L91) | theorem | A nonzero generic germ makes the equation in every nonempty line chart nonzero. Generic independence or global triviality is not inferred. |
| Support for the specified-section construction in [Stacks 31.15.10(2)](https://stacks.math.columbia.edu/tag/01X0) | [`sectionLocalEquation_germ_ne_zero`](Normalizer/SectionLocalEquation.lean#L106) | theorem | The local equation has nonzero germ at every point of its chart. This is nonzeroness in the local ring, not in its residue field. |
| Support for the specified-section construction in [Stacks 31.15.10(2)](https://stacks.math.columbia.edu/tag/01X0) | [`sectionLocalEquation_isRegular`](Normalizer/SectionLocalEquation.lean#L117) | theorem | The actual local equation is a non-zero-divisor on every nonempty chart, as required for its effective Cartier zero divisor. |
| Support for the specified-section construction in [Stacks 31.15.10(2)](https://stacks.math.columbia.edu/tag/01X0) | [`sectionLocalEquation_germ_isRegular`](Normalizer/SectionLocalEquation.lean#L124) | theorem | The same equation is a non-zero-divisor in each actual local ring. |

## SectionDualEvaluation

| Source / mathematical role | Lean declaration | Kind | Exact coverage |
|---|---|---|---|
| Support for the specified-section construction in [Stacks 31.15.10(2)](https://stacks.math.columbia.edu/tag/01X0) | [`schemeDualSheaf`](Normalizer/SectionDualEvaluation.lean#L23) | def | The actual sheaf of local module morphisms into the structure sheaf. |
| Support for the specified-section construction in [Stacks 31.15.10(2)](https://stacks.math.columbia.edu/tag/01X0) | [`schemeSectionDualEvaluationAt`](Normalizer/SectionDualEvaluation.lean#L28) | def | Evaluation of a local dual section at the restriction of the prescribed global section, linear over the actual section ring. |
| Support for the specified-section construction in [Stacks 31.15.10(2)](https://stacks.math.columbia.edu/tag/01X0) | [`schemeSectionDualEvaluation`](Normalizer/SectionDualEvaluation.lean#L40) | def | Evaluation at a specified global section is an actual morphism from the constructed dual sheaf to the structure sheaf. |
| Support for the specified-section construction in [Stacks 31.15.10(2)](https://stacks.math.columbia.edu/tag/01X0) | [`schemeSectionDualEvaluation_app`](Normalizer/SectionDualEvaluation.lean#L66) | theorem | The sheaf evaluation has its prescribed sectionwise value. |
| Support for the specified-section construction in [Stacks 31.15.10(2)](https://stacks.math.columbia.edu/tag/01X0) | [`schemeDualFrameCoordinate`](Normalizer/SectionDualEvaluation.lean#L73) | def | A genuine local line chart gives coordinates of actual dual sections, by their evaluation on the actual line frame. |
| Support for the specified-section construction in [Stacks 31.15.10(2)](https://stacks.math.columbia.edu/tag/01X0) | [`schemeDualFrameCoordinate_restrict`](Normalizer/SectionDualEvaluation.lean#L80) | theorem | The actual dual coordinates commute with restriction. |
| Support for the specified-section construction in [Stacks 31.15.10(2)](https://stacks.math.columbia.edu/tag/01X0) | [`schemeDualLineFrameIso`](Normalizer/SectionDualEvaluation.lean#L115) | def | A genuine local line chart constructs a genuine chart of the actual dual sheaf. |
| Support for the specified-section construction in [Stacks 31.15.10(2)](https://stacks.math.columbia.edu/tag/01X0) | [`schemeDualLineFrameIso_coordinate`](Normalizer/SectionDualEvaluation.lean#L124) | theorem | Coordinates of the constructed dual frame are exactly the supplied scalar. |
| Support for the specified-section construction in [Stacks 31.15.10(2)](https://stacks.math.columbia.edu/tag/01X0) | [`schemeSectionDualEvaluation_frame`](Normalizer/SectionDualEvaluation.lean#L133) | theorem | In a genuine line chart, evaluation is multiplication by the prescribed section's coordinate, with the dual coordinate derived from evaluation on the frame. |
| Support for the specified-section construction in [Stacks 31.15.10(2)](https://stacks.math.columbia.edu/tag/01X0) | [`schemeSectionDualEvaluation_frame_one`](Normalizer/SectionDualEvaluation.lean#L150) | theorem | The image of the constructed dual frame is the actual local equation of the specified global section in the original chart. |

## SectionZeroIdeal

| Source / mathematical role | Lean declaration | Kind | Exact coverage |
|---|---|---|---|
| Support for the specified-section construction in [Stacks 31.15.10(2)](https://stacks.math.columbia.edu/tag/01X0) | [`schemeSectionImageIdeal`](Normalizer/SectionZeroIdeal.lean#L21) | def | The actual image on sections of a map into the structure sheaf. |
| Support for the specified-section construction in [Stacks 31.15.10(2)](https://stacks.math.columbia.edu/tag/01X0) | [`mem_schemeSectionImageIdeal`](Normalizer/SectionZeroIdeal.lean#L25) | theorem | Membership means being the image of an actual section. |
| Support for the specified-section construction in [Stacks 31.15.10(2)](https://stacks.math.columbia.edu/tag/01X0) | [`schemeSectionImageIdeal_zero`](Normalizer/SectionZeroIdeal.lean#L29) | theorem | The zero map has the zero image ideal. |
| Support for the specified-section construction in [Stacks 31.15.10(2)](https://stacks.math.columbia.edu/tag/01X0) | [`schemeSectionImageIdeal_id`](Normalizer/SectionZeroIdeal.lean#L36) | theorem | The identity map has the unit image ideal. |
| Support for the specified-section construction in [Stacks 31.15.10(2)](https://stacks.math.columbia.edu/tag/01X0) | [`schemeSectionImageEquation`](Normalizer/SectionZeroIdeal.lean#L42) | def | The local equation obtained from an actual line frame and a sheaf map. |
| Support for the specified-section construction in [Stacks 31.15.10(2)](https://stacks.math.columbia.edu/tag/01X0) | [`schemeSectionImageIdeal_eq_span`](Normalizer/SectionZeroIdeal.lean#L48) | theorem | A genuine line frame proves that the actual image ideal is principal. |
| Support for the specified-section construction in [Stacks 31.15.10(2)](https://stacks.math.columbia.edu/tag/01X0) | [`schemeSectionImageEquation_restrict`](Normalizer/SectionZeroIdeal.lean#L66) | theorem | The frame image restricts as an actual structure-sheaf section. |
| Support for the specified-section construction in [Stacks 31.15.10(2)](https://stacks.math.columbia.edu/tag/01X0) | [`schemeSectionImageIdeal_map_of_chart`](Normalizer/SectionZeroIdeal.lean#L79) | theorem | Inside a genuine line chart, extension of the image ideal along restriction is exactly the image ideal on the smaller open. |
| Support for the specified-section construction in [Stacks 31.15.10(2)](https://stacks.math.columbia.edu/tag/01X0) | [`schemeSectionImageIdealOn`](Normalizer/SectionZeroIdeal.lean#L90) | def | The actual image ideals form ideal-sheaf data on any genuine line chart. The localization law is proved from that chart, not supplied as an assumption. |
| Support for the specified-section construction in [Stacks 31.15.10(2)](https://stacks.math.columbia.edu/tag/01X0) | [`schemeSectionImageIdealOn_ideal`](Normalizer/SectionZeroIdeal.lean#L101) | theorem | On every affine open in the chart this is exactly the image of the given sheaf map on the corresponding open of the original scheme. |
| Support for the specified-section construction in [Stacks 31.15.10(2)](https://stacks.math.columbia.edu/tag/01X0) | [`schemeSectionImageIdealOn_ideal_eq_span`](Normalizer/SectionZeroIdeal.lean#L108) | theorem | Each affine chart of the zero subscheme is cut out by the actual frame image. |
| Support for the specified-section construction in [Stacks 31.15.10(2)](https://stacks.math.columbia.edu/tag/01X0) | [`schemeSectionImageIdealOn_eq`](Normalizer/SectionZeroIdeal.lean#L116) | theorem | Changing the frame does not change the actual image ideal sheaf. |
| Support for the specified-section construction in [Stacks 31.15.10(2)](https://stacks.math.columbia.edu/tag/01X0) | [`schemeSectionImageIdealOn_comap`](Normalizer/SectionZeroIdeal.lean#L129) | theorem | The local image ideal sheaves agree under restriction to a smaller chart. |
| Support for the specified-section construction in [Stacks 31.15.10(2)](https://stacks.math.columbia.edu/tag/01X0) | [`schemeSectionZeroSubschemeOn`](Normalizer/SectionZeroIdeal.lean#L144) | def | The actual zero subscheme on a genuine line chart. |
| Support for the specified-section construction in [Stacks 31.15.10(2)](https://stacks.math.columbia.edu/tag/01X0) | [`schemeSectionZeroSubschemeOnι`](Normalizer/SectionZeroIdeal.lean#L149) | def | The zero subscheme is equipped with its closed immersion into the chart. |
| Support for the specified-section construction in [Stacks 31.15.10(2)](https://stacks.math.columbia.edu/tag/01X0) | [`schemeSectionZeroSubschemeOn_isClosedImmersion`](Normalizer/SectionZeroIdeal.lean#L155) | theorem | The constructed morphism is a closed immersion, including nilpotent structure. |
| Support for the specified-section construction in [Stacks 31.15.10(2)](https://stacks.math.columbia.edu/tag/01X0) | [`schemeSectionZeroSubschemeOnPullbackIso`](Normalizer/SectionZeroIdeal.lean#L163) | def | The zero subscheme on a smaller chart is the actual base change of the zero subscheme on the larger chart. |

## IdealSheafGluing

| Source / mathematical role | Lean declaration | Kind | Exact coverage |
|---|---|---|---|
| Exact finite quasi-compact open gluing supporting the zero-subscheme construction | [`idealSheaf_comap_iInf`](Normalizer/IdealSheafGluing.lean#L16) | theorem | Pulling back along an open immersion preserves finite intersections of ideal-sheaf data. |
| Exact finite quasi-compact open gluing supporting the zero-subscheme construction | [`idealSheaf_ker_comap_of_isPullback`](Normalizer/IdealSheafGluing.lean#L26) | theorem | The kernel ideal of a quasi-compact morphism restricts exactly under an actual open pullback square. |
| Exact finite quasi-compact open gluing supporting the zero-subscheme construction | [`idealSheaf_comap_map_open`](Normalizer/IdealSheafGluing.lean#L37) | theorem | An ideal pushed along a quasi-compact open immersion restricts back to the original ideal, rather than merely containing it. |
| Exact finite quasi-compact open gluing supporting the zero-subscheme construction | [`idealSheaf_comap_map_open_baseChange`](Normalizer/IdealSheafGluing.lean#L46) | theorem | Pushforward of an ideal along a quasi-compact map commutes with restriction to an open subscheme, using the actual pullback. |
| Exact finite quasi-compact open gluing supporting the zero-subscheme construction | [`finiteIdealSheafGlue`](Normalizer/IdealSheafGluing.lean#L62) | def | The global ideal obtained as the finite intersection of the actual pushforwards of local ideals. Exact restriction is proved separately. |
| Exact finite quasi-compact open gluing supporting the zero-subscheme construction | [`idealSheaf_overlap_of_inf`](Normalizer/IdealSheafGluing.lean#L68) | theorem | Equality on the actual intersection of two opens gives compatibility on their categorical pullback. |
| Exact finite quasi-compact open gluing supporting the zero-subscheme construction | [`finiteIdealSheafGlue_comap`](Normalizer/IdealSheafGluing.lean#L81) | theorem | Compatible local ideals on a finite family of quasi-compact open immersions have a global ideal whose restrictions are exactly the inputs. Compatibility is equality on the actual pairwise pullbacks. |
| Exact finite quasi-compact open gluing supporting the zero-subscheme construction | [`exists_idealSheaf_of_finite_openCover`](Normalizer/IdealSheafGluing.lean#L100) | theorem | A finite open cover with quasi-compact inclusions glues compatible actual ideal-sheaf data to an actual global ideal with exact restrictions. |

## SectionZeroScheme

| Source / mathematical role | Lean declaration | Kind | Exact coverage |
|---|---|---|---|
| Support for the specified-section construction in [Stacks 31.15.10(2)](https://stacks.math.columbia.edu/tag/01X0) | [`schemeLineChartRestrict`](Normalizer/SectionZeroScheme.lean#L16) | def | Restrict an actual local line chart to a smaller open. |
| Support for the specified-section construction in [Stacks 31.15.10(2)](https://stacks.math.columbia.edu/tag/01X0) | [`schemeSectionImageIdealOn_overlap`](Normalizer/SectionZeroScheme.lean#L27) | theorem | The actual local image ideals of the same sheaf map agree on an overlap. |
| Support for the specified-section construction in [Stacks 31.15.10(2)](https://stacks.math.columbia.edu/tag/01X0) | [`schemeSectionZeroIdeal`](Normalizer/SectionZeroScheme.lean#L42) | def | The global ideal from a genuine line-chart cover. The actual cover is explicit; finiteness and quasi-compactness prove its exact chart restrictions. |
| Support for the specified-section construction in [Stacks 31.15.10(2)](https://stacks.math.columbia.edu/tag/01X0) | [`schemeSectionZeroIdeal_comap`](Normalizer/SectionZeroScheme.lean#L48) | theorem | The constructed global ideal restricts to the actual section image ideal on every chart; its overlap compatibility follows from the given map. |
| Support for the specified-section construction in [Stacks 31.15.10(2)](https://stacks.math.columbia.edu/tag/01X0) | [`schemeSectionZeroScheme`](Normalizer/SectionZeroScheme.lean#L58) | def | The actual zero subscheme determined by the prescribed sheaf map and its genuine line-chart cover. |
| Support for the specified-section construction in [Stacks 31.15.10(2)](https://stacks.math.columbia.edu/tag/01X0) | [`schemeSectionZeroSchemeι`](Normalizer/SectionZeroScheme.lean#L62) | def | The inclusion of the actual global zero subscheme. |
| Support for the specified-section construction in [Stacks 31.15.10(2)](https://stacks.math.columbia.edu/tag/01X0) | [`schemeSectionZeroScheme_isClosedImmersion`](Normalizer/SectionZeroScheme.lean#L68) | theorem | The global zero subscheme is a closed subscheme, with its full ideal structure rather than only a reduced zero set. |
| Support for the specified-section construction in [Stacks 31.15.10(2)](https://stacks.math.columbia.edu/tag/01X0) | [`schemeSectionZeroSchemeChartIso`](Normalizer/SectionZeroScheme.lean#L76) | def | Base change of the global zero subscheme to a chart is the local zero subscheme constructed directly from the original map. |

## ZeroIdealUniqueness

| Source / mathematical role | Lean declaration | Kind | Exact coverage |
|---|---|---|---|
| Open-cover locality and cover independence of the actual zero ideal | [`idealSheaf_eq_of_openCover`](Normalizer/ZeroIdealUniqueness.lean#L15) | theorem | Ideal-sheaf data agreeing on an actual open cover agree globally. No finiteness or quasi-compactness assumption is needed for uniqueness. |
| Open-cover locality and cover independence of the actual zero ideal | [`schemeSectionZeroIdeal_cover_independent`](Normalizer/ZeroIdealUniqueness.lean#L45) | theorem | Two genuine finite line-chart covers give exactly the same global zero ideal for the same original sheaf map. |
| Open-cover locality and cover independence of the actual zero ideal | [`schemeSectionZeroScheme_cover_independent`](Normalizer/ZeroIdealUniqueness.lean#L71) | theorem | The actual closed zero subscheme is independent of the finite genuine line-chart cover used to construct it. |
| Open-cover locality and cover independence of the actual zero ideal | [`schemeSectionZeroSchemeCoverIso`](Normalizer/ZeroIdealUniqueness.lean#L80) | def | The canonical identification of the two constructed zero schemes. |
| Open-cover locality and cover independence of the actual zero ideal | [`schemeSectionZeroSchemeCoverIso_hom_ι`](Normalizer/ZeroIdealUniqueness.lean#L95) | theorem | Cover independence preserves the actual closed immersion into the original scheme, not merely the abstract isomorphism type of its source. |

## SectionEvaluationMono

| Source / mathematical role | Lean declaration | Kind | Exact coverage |
|---|---|---|---|
| Support for the specified-section construction in [Stacks 31.15.10(2)](https://stacks.math.columbia.edu/tag/01X0) | [`schemeSectionDualEvaluationAt_injective_on_chart`](Normalizer/SectionEvaluationMono.lean#L18) | theorem | On a nonempty genuine line chart, dual evaluation is injective because the section coordinate is nonzero in the integral section ring. |
| Support for the specified-section construction in [Stacks 31.15.10(2)](https://stacks.math.columbia.edu/tag/01X0) | [`schemeSectionDualEvaluationAt_injective`](Normalizer/SectionEvaluationMono.lean#L40) | theorem | Genuine line charts covering the points make dual evaluation injective on sections of every open, including the empty open. |
| Support for the specified-section construction in [Stacks 31.15.10(2)](https://stacks.math.columbia.edu/tag/01X0) | [`schemeSectionDualEvaluation_mono`](Normalizer/SectionEvaluationMono.lean#L69) | theorem | Evaluation at a generically nonzero global section of an actual locally trivial line sheaf is monic as a morphism of actual module sheaves. |

## SectionImageSheaf

| Source / mathematical role | Lean declaration | Kind | Exact coverage |
|---|---|---|---|
| Support for the specified-section construction in [Stacks 31.15.10(2)](https://stacks.math.columbia.edu/tag/01X0) | [`schemeSectionImageSheaf`](Normalizer/SectionImageSheaf.lean#L16) | def | The actual categorical image module sheaf. |
| Support for the specified-section construction in [Stacks 31.15.10(2)](https://stacks.math.columbia.edu/tag/01X0) | [`schemeSectionImageSheafι`](Normalizer/SectionImageSheaf.lean#L19) | def | The actual image inclusion into the structure sheaf. |
| Support for the specified-section construction in [Stacks 31.15.10(2)](https://stacks.math.columbia.edu/tag/01X0) | [`schemeSectionImageSheafIso`](Normalizer/SectionImageSheaf.lean#L23) | def | A regular map identifies its line sheaf with its categorical image. |
| Support for the specified-section construction in [Stacks 31.15.10(2)](https://stacks.math.columbia.edu/tag/01X0) | [`schemeSectionImageSheafIso_hom`](Normalizer/SectionImageSheaf.lean#L27) | theorem | The comparison is the canonical factorization map through the image. |
| Support for the specified-section construction in [Stacks 31.15.10(2)](https://stacks.math.columbia.edu/tag/01X0) | [`schemeSectionImageSheafIso_hom_ι`](Normalizer/SectionImageSheaf.lean#L34) | theorem | Composing the canonical comparison with the image inclusion recovers exactly the original map. |
| Support for the specified-section construction in [Stacks 31.15.10(2)](https://stacks.math.columbia.edu/tag/01X0) | [`schemeSectionImageSheafIso_inv_comp`](Normalizer/SectionImageSheaf.lean#L39) | theorem | The inclusion composed with the inverse comparison gives the same map. |
| Support for the specified-section construction in [Stacks 31.15.10(2)](https://stacks.math.columbia.edu/tag/01X0) | [`schemeSectionImageSheaf_imageIdeal`](Normalizer/SectionImageSheaf.lean#L45) | theorem | The image sheaf inclusion has exactly the original sectionwise image ideal. Surjectivity here follows from the actual isomorphism on sections. |
| Support for the specified-section construction in [Stacks 31.15.10(2)](https://stacks.math.columbia.edu/tag/01X0) | [`schemeSectionImageSheafFrame`](Normalizer/SectionImageSheaf.lean#L64) | def | Every genuine local line frame transports to the actual image sheaf. |
| Support for the specified-section construction in [Stacks 31.15.10(2)](https://stacks.math.columbia.edu/tag/01X0) | [`schemeSectionImageSheafFrame_equation`](Normalizer/SectionImageSheaf.lean#L72) | theorem | The transported image frame has exactly the same local equation. |
| Support for the specified-section construction in [Stacks 31.15.10(2)](https://stacks.math.columbia.edu/tag/01X0) | [`schemeSectionImageSheaf_idealOn`](Normalizer/SectionImageSheaf.lean#L83) | theorem | The actual ideal-sheaf data are unchanged when formed from the image inclusion and its transported line frame. |

## DualTransport

| Source / mathematical role | Lean declaration | Kind | Exact coverage |
|---|---|---|---|
| Support for the specified-section construction in [Stacks 31.15.10(2)](https://stacks.math.columbia.edu/tag/01X0) | [`schemeDualMapAt`](Normalizer/DualTransport.lean#L31) | def | Contravariant transport on actual dual sections is precomposition. |
| Support for the specified-section construction in [Stacks 31.15.10(2)](https://stacks.math.columbia.edu/tag/01X0) | [`schemeDualMap`](Normalizer/DualTransport.lean#L49) | def | Canonical pullback of functionals along an actual module-sheaf morphism. |
| Support for the specified-section construction in [Stacks 31.15.10(2)](https://stacks.math.columbia.edu/tag/01X0) | [`schemeDualMap_eval`](Normalizer/DualTransport.lean#L73) | theorem | Exact evaluation formula for contravariant dual transport. |
| Support for the specified-section construction in [Stacks 31.15.10(2)](https://stacks.math.columbia.edu/tag/01X0) | [`schemeDualMap_id`](Normalizer/DualTransport.lean#L81) | theorem | Pulling a functional back along the identity leaves it unchanged. |
| Support for the specified-section construction in [Stacks 31.15.10(2)](https://stacks.math.columbia.edu/tag/01X0) | [`schemeDualMap_comp`](Normalizer/DualTransport.lean#L93) | theorem | Dual transport reverses composition. |
| Support for the specified-section construction in [Stacks 31.15.10(2)](https://stacks.math.columbia.edu/tag/01X0) | [`schemeDualIso`](Normalizer/DualTransport.lean#L111) | def | An actual sheaf isomorphism induces the actual contravariant dual isomorphism. |
| Support for the specified-section construction in [Stacks 31.15.10(2)](https://stacks.math.columbia.edu/tag/01X0) | [`schemeDualSectionOfHom`](Normalizer/DualTransport.lean#L118) | def | A genuine sheaf morphism to the structure sheaf determines an actual global dual section. |
| Support for the specified-section construction in [Stacks 31.15.10(2)](https://stacks.math.columbia.edu/tag/01X0) | [`schemeDualSectionOfHom_eval`](Normalizer/DualTransport.lean#L126) | theorem | The global dual section associated to a morphism evaluates by its actual components. |
| Support for the specified-section construction in [Stacks 31.15.10(2)](https://stacks.math.columbia.edu/tag/01X0) | [`schemeDualMap_sectionOfHom`](Normalizer/DualTransport.lean#L132) | theorem | Contravariant transport of a morphism's dual section is actual precomposition. |

## LineBidual

| Source / mathematical role | Lean declaration | Kind | Exact coverage |
|---|---|---|---|
| Support for the specified-section construction in [Stacks 31.15.10(2)](https://stacks.math.columbia.edu/tag/01X0) | [`schemeBidualAt`](Normalizer/LineBidual.lean#L47) | def | The canonical bidual map on actual sections. |
| Support for the specified-section construction in [Stacks 31.15.10(2)](https://stacks.math.columbia.edu/tag/01X0) | [`schemeBidualMap`](Normalizer/LineBidual.lean#L85) | def | The canonical bidual sheaf morphism is evaluation of local functionals. |
| Support for the specified-section construction in [Stacks 31.15.10(2)](https://stacks.math.columbia.edu/tag/01X0) | [`schemeBidualMap_eval`](Normalizer/LineBidual.lean#L109) | theorem | Exact evaluation formula for the canonical bidual image, on every smaller open. |
| Support for the specified-section construction in [Stacks 31.15.10(2)](https://stacks.math.columbia.edu/tag/01X0) | [`schemeBidualMap_coordinate`](Normalizer/LineBidual.lean#L117) | theorem | In an actual line chart the bidual coordinate is precisely the original coordinate. |
| Support for the specified-section construction in [Stacks 31.15.10(2)](https://stacks.math.columbia.edu/tag/01X0) | [`schemeBidualMap_bijective_of_chart`](Normalizer/LineBidual.lean#L139) | theorem | The canonical bidual map is bijective on every subopen of a genuine line chart. |
| Support for the specified-section construction in [Stacks 31.15.10(2)](https://stacks.math.columbia.edu/tag/01X0) | [`schemeBidualMap_isIso`](Normalizer/LineBidual.lean#L172) | theorem | Genuine line charts covering the scheme prove canonical biduality globally. |
| Support for the specified-section construction in [Stacks 31.15.10(2)](https://stacks.math.columbia.edu/tag/01X0) | [`schemeLineBidualIso`](Normalizer/LineBidual.lean#L180) | def | The canonical bidual equivalence of an actually locally trivial line sheaf. |
| Support for the specified-section construction in [Stacks 31.15.10(2)](https://stacks.math.columbia.edu/tag/01X0) | [`schemeLineBidualIso_hom`](Normalizer/LineBidual.lean#L188) | theorem | The bidual equivalence uses the canonical map, independent of the covering choice. |
| Support for the specified-section construction in [Stacks 31.15.10(2)](https://stacks.math.columbia.edu/tag/01X0) | [`schemeBidualMap_globalSection`](Normalizer/LineBidual.lean#L194) | theorem | The bidual image of a global section is the actual dual section of its evaluation morphism. |

## SectionZeroDivisor

| Source / mathematical role | Lean declaration | Kind | Exact coverage |
|---|---|---|---|
| Support for the specified-section construction in [Stacks 31.15.10(2)](https://stacks.math.columbia.edu/tag/01X0) | [`schemeSectionDualEvaluation_equation`](Normalizer/SectionZeroDivisor.lean#L20) | theorem | The image equation of actual dual evaluation is exactly the original specified section's local equation, in the constructed dual chart. |
| Support for the specified-section construction in [Stacks 31.15.10(2)](https://stacks.math.columbia.edu/tag/01X0) | [`schemeSectionDualEvaluation_imageIdeal`](Normalizer/SectionZeroDivisor.lean#L27) | theorem | The actual image ideal, rather than an unrelated principal ideal, is generated by the specified section's local equation. |
| Support for the specified-section construction in [Stacks 31.15.10(2)](https://stacks.math.columbia.edu/tag/01X0) | [`schemeSectionDualEvaluation_germ_imageIdeal`](Normalizer/SectionZeroDivisor.lean#L34) | theorem | The same equality after mapping to the actual local ring at a point. |
| Support for the specified-section construction in [Stacks 31.15.10(2)](https://stacks.math.columbia.edu/tag/01X0) | [`schemeSectionDualEvaluation_imageIdeal_eq_top_iff`](Normalizer/SectionZeroDivisor.lean#L44) | theorem | The local image ideal is the unit ideal exactly where the equation is invertible. This is stronger than its nonzeroness in a domain. |
| Support for the specified-section construction in [Stacks 31.15.10(2)](https://stacks.math.columbia.edu/tag/01X0) | [`schemeSectionDualEvaluation_germ_imageIdeal_eq_top_iff`](Normalizer/SectionZeroDivisor.lean#L52) | theorem | The actual local-ring image ideal detects zeros by noninvertibility of the specified equation in that local ring. |
| Support for the specified-section construction in [Stacks 31.15.10(2)](https://stacks.math.columbia.edu/tag/01X0) | [`schemeSectionDualEvaluation_germ_imageIdeal_regular`](Normalizer/SectionZeroDivisor.lean#L63) | theorem | The actual local-ring image ideal has a non-zero-divisor generator when the prescribed section has nonzero generic germ on an integral scheme. |

## SectionIdealBundle

| Source / mathematical role | Lean declaration | Kind | Exact coverage |
|---|---|---|---|
| Support for the specified-section construction in [Stacks 31.15.10(2)](https://stacks.math.columbia.edu/tag/01X0) | [`schemeSectionInverseIdealBundle`](Normalizer/SectionIdealBundle.lean#L21) | def | The inverse ideal module is the actual dual of the categorical image of evaluation at the specified section. |
| Support for the specified-section construction in [Stacks 31.15.10(2)](https://stacks.math.columbia.edu/tag/01X0) | [`schemeSectionInverseIdealSection`](Normalizer/SectionIdealBundle.lean#L26) | def | The canonical section of the inverse ideal module is its actual ideal inclusion, viewed as a local functional on that ideal. |
| Support for the specified-section construction in [Stacks 31.15.10(2)](https://stacks.math.columbia.edu/tag/01X0) | [`schemeSectionInverseIdealFrame`](Normalizer/SectionIdealBundle.lean#L31) | def | Genuine line charts and monic evaluation construct actual line charts of the inverse ideal module. |
| Support for the specified-section construction in [Stacks 31.15.10(2)](https://stacks.math.columbia.edu/tag/01X0) | [`schemeSectionInverseIdealIso`](Normalizer/SectionIdealBundle.lean#L55) | def | The inverse of the actual section image ideal is canonically the original line module. Monicity is proved from generic nonzeroness. |
| Support for the specified-section construction in [Stacks 31.15.10(2)](https://stacks.math.columbia.edu/tag/01X0) | [`schemeSectionInverseIdealIso_section`](Normalizer/SectionIdealBundle.lean#L62) | theorem | The actual canonical inclusion section of the inverse image ideal maps to the specified original section, not just to some nonzero section. |
| Support for the specified-section construction in [Stacks 31.15.10(2)](https://stacks.math.columbia.edu/tag/01X0) | [`schemeSectionImageSheaf_zeroIdeal_comap`](Normalizer/SectionIdealBundle.lean#L82) | theorem | The actual image ideal module has the actual global zero ideal as its chart ideal data. This exposes the sheaf/subscheme linkage explicitly. |
| Support for the specified-section construction in [Stacks 31.15.10(2)](https://stacks.math.columbia.edu/tag/01X0) | [`schemeSectionInverseIdealBundle_isLocallyFree`](Normalizer/SectionIdealBundle.lean#L104) | theorem | The constructed inverse ideal module is locally free in mathlib's actual sheaf sense, as witnessed by the constructed rank-one charts. |
| Support for the specified-section construction in [Stacks 31.15.10(2)](https://stacks.math.columbia.edu/tag/01X0) | [`schemeSectionInverseIdealBundle_isFinitePresentation`](Normalizer/SectionIdealBundle.lean#L116) | theorem | The same constructed rank-one charts prove finite presentation of the actual inverse ideal module. |

## DeterminantZeroDivisor

| Source / mathematical role | Lean declaration | Kind | Exact coverage |
|---|---|---|---|
| Specified determinant application of the regular-section construction; not the degree implication | [`schemeDeterminantDualEvaluation_mono`](Normalizer/DeterminantZeroDivisor.lean#L23) | theorem | Actual rank-n charts and independence of the specified generic germs make evaluation against their actual determinant section monic. |
| Specified determinant application of the regular-section construction; not the degree implication | [`schemeDeterminantLocalEquation_germ_isRegular`](Normalizer/DeterminantZeroDivisor.lean#L38) | theorem | The equation of the specified determinant in the chart induced by an actual rank-n frame is regular in every actual local ring on that chart. |
| Specified determinant application of the regular-section construction; not the degree implication | [`schemeDeterminantInverseIdealIso`](Normalizer/DeterminantZeroDivisor.lean#L51) | def | The inverse ideal module of the actual specified determinant is the actual exterior line, using only genuine rank-n charts and generic independence. |
| Specified determinant application of the regular-section construction; not the degree implication | [`schemeDeterminantInverseIdealIso_section`](Normalizer/DeterminantZeroDivisor.lean#L63) | theorem | This isomorphism carries the canonical inclusion section to the specified determinant section built from the original section family. |
| Specified determinant application of the regular-section construction; not the degree implication | [`schemeDeterminantZeroIdeal`](Normalizer/DeterminantZeroDivisor.lean#L82) | def | The actual global zero ideal of the specified exterior section, built from the genuine rank-n cover and its induced dual determinant charts. |
| Specified determinant application of the regular-section construction; not the degree implication | [`schemeDeterminantZeroIdeal_comap`](Normalizer/DeterminantZeroDivisor.lean#L90) | theorem | The global determinant zero ideal restricts exactly to the actual local image ideal; compatibility is derived from the same evaluation map. |
| Specified determinant application of the regular-section construction; not the degree implication | [`schemeDeterminantZeroIdeal_chart_ideal`](Normalizer/DeterminantZeroDivisor.lean#L100) | theorem | Each affine open of a chart has the actual specified determinant equation as generator of the restriction of the global zero ideal. |
| Specified determinant application of the regular-section construction; not the degree implication | [`schemeDeterminantZeroIdeal_chart_germ_regular`](Normalizer/DeterminantZeroDivisor.lean#L111) | theorem | Generic independence gives a regular generator for the actual local ring image of the global determinant zero ideal on every affine chart. |

## CurveClosedSubscheme

| Source / mathematical role | Lean declaration | Kind | Exact coverage |
|---|---|---|---|
| Topological support for finite zero schemes in [Stacks 33.44.9](https://stacks.math.columbia.edu/tag/0AYY) | [`topologicalKrullDim_nonpos_of_closedEmbedding`](Normalizer/CurveClosedSubscheme.lean#L15) | theorem | A nonsurjective closed embedding into an irreducible space of dimension at most one has zero-dimensional source, including the empty case. |
| Topological support for finite zero schemes in [Stacks 33.44.9](https://stacks.math.columbia.edu/tag/0AYY) | [`closedSubscheme_dimension_nonpos`](Normalizer/CurveClosedSubscheme.lean#L43) | theorem | An actual closed subscheme omitting the generic point of an integral scheme of dimension at most one has topological dimension at most zero. |

## FiniteZeroDimensional

| Source / mathematical role | Lean declaration | Kind | Exact coverage |
|---|---|---|---|
| Finite-type dimension-zero support for [Stacks 33.44.9](https://stacks.math.columbia.edu/tag/0AYY) | [`scheme_isArtinian_of_dim_le_zero`](Normalizer/FiniteZeroDimensional.lean#L18) | theorem | A quasi-compact locally Noetherian scheme of dimension at most zero is an actual Artinian scheme. The empty scheme is included. |
| Finite-type dimension-zero support for [Stacks 33.44.9](https://stacks.math.columbia.edu/tag/0AYY) | [`scheme_finite_points_of_dim_le_zero`](Normalizer/FiniteZeroDimensional.lean#L24) | theorem | The underlying point set of such a scheme is finite; the conclusion does not discard its possibly nonreduced scheme structure. |
| Finite-type dimension-zero support for [Stacks 33.44.9](https://stacks.math.columbia.edu/tag/0AYY) | [`scheme_isFinite_of_dim_le_zero`](Normalizer/FiniteZeroDimensional.lean#L33) | theorem | A quasi-compact finite-type morphism to a field with zero-dimensional source is finite as an actual scheme morphism. Properness is unnecessary. |
| Finite-type dimension-zero support for [Stacks 33.44.9](https://stacks.math.columbia.edu/tag/0AYY) | [`scheme_isFinite_of_compact_dim_le_zero`](Normalizer/FiniteZeroDimensional.lean#L44) | theorem | Compactness of the source suffices in place of an explicit quasi-compactness hypothesis on its finite-type structure morphism. |
| Finite-type dimension-zero support for [Stacks 33.44.9](https://stacks.math.columbia.edu/tag/0AYY) | [`scheme_isFinite_of_proper_dim_le_zero`](Normalizer/FiniteZeroDimensional.lean#L50) | theorem | A proper scheme over a field whose dimension is at most zero is finite over that field, including its full nilpotent structure. |

## SectionZeroSupport

| Source / mathematical role | Lean declaration | Kind | Exact coverage |
|---|---|---|---|
| Actual generic-point exclusion supporting [Stacks 33.44.9](https://stacks.math.columbia.edu/tag/0AYY) | [`schemeSectionImageIdealOn_genericPoint_not_mem`](Normalizer/SectionZeroSupport.lean#L19) | theorem | The actual local zero ideal of the specified section excludes the generic point of every nonempty genuine line chart. |
| Actual generic-point exclusion supporting [Stacks 33.44.9](https://stacks.math.columbia.edu/tag/0AYY) | [`schemeSectionZeroIdeal_genericPoint_not_mem`](Normalizer/SectionZeroSupport.lean#L56) | theorem | A section with nonzero generic germ has an actual zero ideal whose support excludes the generic point; no support condition is assumed. |
| Actual generic-point exclusion supporting [Stacks 33.44.9](https://stacks.math.columbia.edu/tag/0AYY) | [`schemeSectionZeroScheme_genericPoint_not_mem_range`](Normalizer/SectionZeroSupport.lean#L75) | theorem | The generic point is not in the range of the actual zero-scheme immersion. |
| Actual generic-point exclusion supporting [Stacks 33.44.9](https://stacks.math.columbia.edu/tag/0AYY) | [`schemeSectionZeroIdeal_support_ne_top`](Normalizer/SectionZeroSupport.lean#L86) | theorem | The support of the actual zero ideal is a proper closed subset. |
| Actual generic-point exclusion supporting [Stacks 33.44.9](https://stacks.math.columbia.edu/tag/0AYY) | [`schemeSectionZeroIdeal_support_interior_eq_empty`](Normalizer/SectionZeroSupport.lean#L96) | theorem | The actual zero support has empty interior. |
| Actual generic-point exclusion supporting [Stacks 33.44.9](https://stacks.math.columbia.edu/tag/0AYY) | [`schemeSectionZeroIdeal_support_isNowhereDense`](Normalizer/SectionZeroSupport.lean#L110) | theorem | The closed support of the actual zero ideal is nowhere dense. |

## FiniteLineCharts

| Source / mathematical role | Lean declaration | Kind | Exact coverage |
|---|---|---|---|
| Proper-curve chart extraction supporting the constructed section zero ideal | [`exists_finite_lineCharts`](Normalizer/FiniteLineCharts.lean#L16) | theorem | Compactness extracts finitely many genuine charts from pointwise local line triviality, without assuming a finite cover. |
| Proper-curve chart extraction supporting the constructed section zero ideal | [`exists_finite_quasiCompact_lineCharts`](Normalizer/FiniteLineCharts.lean#L33) | theorem | On a noetherian scheme the finite genuine line charts have quasi-compact inclusions, as required by the actual ideal-sheaf gluing construction. |

## FiniteSchemeSections

| Source / mathematical role | Lean declaration | Kind | Exact coverage |
|---|---|---|---|
| Actual finite-scheme function dimension supporting [Stacks 33.44.9](https://stacks.math.columbia.edu/tag/0AYY); no line-degree comparison | [`schemeGlobalFunctionsAlgebra`](Normalizer/FiniteSchemeSections.lean#L19) | def | The actual base-field algebra structure on global functions. |
| Actual finite-scheme function dimension supporting [Stacks 33.44.9](https://stacks.math.columbia.edu/tag/0AYY); no line-degree comparison | [`schemeGlobalFunctionsAlgebra_map`](Normalizer/FiniteSchemeSections.lean#L23) | theorem | The scalar structure is induced by the specified structure morphism. |
| Actual finite-scheme function dimension supporting [Stacks 33.44.9](https://stacks.math.columbia.edu/tag/0AYY); no line-degree comparison | [`finiteScheme_constantMap_finite`](Normalizer/FiniteSchemeSections.lean#L28) | theorem | A finite scheme morphism induces a finite map on actual global functions. |
| Actual finite-scheme function dimension supporting [Stacks 33.44.9](https://stacks.math.columbia.edu/tag/0AYY); no line-degree comparison | [`finiteScheme_globalFunctions_finite`](Normalizer/FiniteSchemeSections.lean#L34) | theorem | Global functions are a finite module for the actual structure-map action. |
| Actual finite-scheme function dimension supporting [Stacks 33.44.9](https://stacks.math.columbia.edu/tag/0AYY); no line-degree comparison | [`finiteScheme_globalFunctions_finiteDimensional`](Normalizer/FiniteSchemeSections.lean#L39) | theorem | Over a field, the actual global function module is finite-dimensional. |
| Actual finite-scheme function dimension supporting [Stacks 33.44.9](https://stacks.math.columbia.edu/tag/0AYY); no line-degree comparison | [`schemeGlobalFunctions_nontrivial`](Normalizer/FiniteSchemeSections.lean#L45) | theorem | Nonempty schemes have nontrivial global function rings, as witnessed by the germ map into a nontrivial local ring at an actual point. |
| Actual finite-scheme function dimension supporting [Stacks 33.44.9](https://stacks.math.columbia.edu/tag/0AYY); no line-degree comparison | [`finiteScheme_globalFunctions_finrank_pos`](Normalizer/FiniteSchemeSections.lean#L50) | theorem | The global function space of a nonempty finite scheme has positive dimension. |
| Actual finite-scheme function dimension supporting [Stacks 33.44.9](https://stacks.math.columbia.edu/tag/0AYY); no line-degree comparison | [`schemeGlobalFunctions_subsingleton_of_isEmpty`](Normalizer/FiniteSchemeSections.lean#L59) | theorem | An empty scheme has only one global regular function. |
| Actual finite-scheme function dimension supporting [Stacks 33.44.9](https://stacks.math.columbia.edu/tag/0AYY); no line-degree comparison | [`finiteScheme_globalFunctions_finrank_eq_zero_iff`](Normalizer/FiniteSchemeSections.lean#L69) | theorem | For an actual finite scheme over the field, vanishing of the dimension of its global function space is equivalent to emptiness of the scheme. |

## SectionZeroLocus

| Source / mathematical role | Lean declaration | Kind | Exact coverage |
|---|---|---|---|
| Actual section zero-locus support for [Stacks 33.44.12(2)](https://stacks.math.columbia.edu/tag/0B40) | [`schemeSectionImageIdealOn_mem_support_iff`](Normalizer/SectionZeroLocus.lean#L17) | theorem | On an affine open inside a genuine line chart, the actual local image ideal contains a point in its support exactly when the equation germ is a nonunit. |
| Actual section zero-locus support for [Stacks 33.44.12(2)](https://stacks.math.columbia.edu/tag/0B40) | [`schemeSectionZeroIdeal_mem_support_iff_affine`](Normalizer/SectionZeroLocus.lean#L38) | theorem | The global zero ideal has the exact nonunit-germ support test on each actual affine chart; global support is derived from exact ideal restriction. |
| Actual section zero-locus support for [Stacks 33.44.12(2)](https://stacks.math.columbia.edu/tag/0B40) | [`schemeSectionZeroIdeal_mem_support_iff`](Normalizer/SectionZeroLocus.lean#L52) | theorem | On every open inside a genuine chart, support membership of the actual global zero ideal is equivalent to noninvertibility of the original equation germ. |
| Actual section zero-locus support for [Stacks 33.44.12(2)](https://stacks.math.columbia.edu/tag/0B40) | [`schemeSectionZeroScheme_nonempty_of_nonunit_affine`](Normalizer/SectionZeroLocus.lean#L77) | theorem | A nonunit equation germ yields an actual point of the constructed global zero scheme, preserving its complete scheme structure. |
| Actual section zero-locus support for [Stacks 33.44.12(2)](https://stacks.math.columbia.edu/tag/0B40) | [`schemeSectionZeroScheme_nonempty_of_nonunit`](Normalizer/SectionZeroLocus.lean#L92) | theorem | A zero of the prescribed section, expressed by a nonunit equation germ on any genuine chart, supplies a point of its actual global zero scheme. |

## LineGenericInjection

| Source / mathematical role | Lean declaration | Kind | Exact coverage |
|---|---|---|---|
| Integral line-sheaf generic injectivity supporting regular-section construction in [Stacks 31.15.10(2)](https://stacks.math.columbia.edu/tag/01X0) | [`lineSheaf_eq_zero_of_genericGerm_eq_zero`](Normalizer/LineGenericInjection.lean#L18) | theorem | Vanishing of the generic germ forces the actual global section of a locally trivial line sheaf to vanish. |
| Integral line-sheaf generic injectivity supporting regular-section construction in [Stacks 31.15.10(2)](https://stacks.math.columbia.edu/tag/01X0) | [`lineSheaf_genericGerm_injective`](Normalizer/LineGenericInjection.lean#L45) | theorem | The actual global-section generic-germ map is injective, derived from line charts rather than an assumed torsion condition. |
| Integral line-sheaf generic injectivity supporting regular-section construction in [Stacks 31.15.10(2)](https://stacks.math.columbia.edu/tag/01X0) | [`lineSheaf_genericGerm_ne_zero_iff`](Normalizer/LineGenericInjection.lean#L55) | theorem | For an actual locally trivial line sheaf, nonzero global section and nonzero generic germ are equivalent. |

## SectionZeroFinite

| Source / mathematical role | Lean declaration | Kind | Exact coverage |
|---|---|---|---|
| Actual finite zero scheme and function-dimension ingredients of [Stacks 33.44.12(2)](https://stacks.math.columbia.edu/tag/0B40); not the degree implication | [`closedSubscheme_isFinite_of_genericPoint_not_mem`](Normalizer/SectionZeroFinite.lean#L23) | theorem | A closed subscheme omitting the generic point of a finite-type integral curve is finite over the base field. |
| Actual finite zero scheme and function-dimension ingredients of [Stacks 33.44.12(2)](https://stacks.math.columbia.edu/tag/0B40); not the degree implication | [`schemeSectionZeroScheme_dimension_nonpos`](Normalizer/SectionZeroFinite.lean#L39) | theorem | The actual zero scheme of the specified section has dimension at most zero. Its generic-point exclusion is derived from the specified section. |
| Actual finite zero scheme and function-dimension ingredients of [Stacks 33.44.12(2)](https://stacks.math.columbia.edu/tag/0B40); not the degree implication | [`schemeSectionZeroScheme_isFinite`](Normalizer/SectionZeroFinite.lean#L50) | theorem | The actual section zero scheme, with all of its nilpotent structure, is finite over the base field on a finite-type integral curve. |
| Actual finite zero scheme and function-dimension ingredients of [Stacks 33.44.12(2)](https://stacks.math.columbia.edu/tag/0B40); not the degree implication | [`properCurve_sectionZeroScheme_isFinite`](Normalizer/SectionZeroFinite.lean#L63) | theorem | In particular, the actual specified section zero scheme on a proper integral curve is finite over the base field. |
| Actual finite zero scheme and function-dimension ingredients of [Stacks 33.44.12(2)](https://stacks.math.columbia.edu/tag/0B40); not the degree implication | [`schemeSectionZeroScheme_globalFunctions_finiteDimensional`](Normalizer/SectionZeroFinite.lean#L72) | theorem | The actual global functions on the constructed zero scheme are finite-dimensional under the action of the actual structure morphism. |
| Actual finite zero scheme and function-dimension ingredients of [Stacks 33.44.12(2)](https://stacks.math.columbia.edu/tag/0B40); not the degree implication | [`schemeSectionZeroScheme_globalFunctions_finrank_eq_zero_iff`](Normalizer/SectionZeroFinite.lean#L86) | theorem | The actual zero-scheme function dimension vanishes exactly when the constructed zero scheme is empty. This is not a line-bundle degree formula. |
| Actual finite zero scheme and function-dimension ingredients of [Stacks 33.44.12(2)](https://stacks.math.columbia.edu/tag/0B40); not the degree implication | [`schemeSectionZeroScheme_globalFunctions_pos_of_zero`](Normalizer/SectionZeroFinite.lean#L102) | theorem | A zero of the specified nonzero section gives a positive-dimensional actual zero-scheme function space. No line-bundle degree is introduced. |
| Actual finite zero scheme and function-dimension ingredients of [Stacks 33.44.12(2)](https://stacks.math.columbia.edu/tag/0B40); not the degree implication | [`properCurve_exists_finite_sectionZeroScheme`](Normalizer/SectionZeroFinite.lean#L119) | theorem | On a proper integral curve, genuine pointwise line charts suffice: the finite quasi-compact cover and finite actual zero scheme are constructed. |
| Actual finite zero scheme and function-dimension ingredients of [Stacks 33.44.12(2)](https://stacks.math.columbia.edu/tag/0B40); not the degree implication | [`schemeSectionZeroScheme_isFinite_of_ne_zero`](Normalizer/SectionZeroFinite.lean#L139) | theorem | Global nonzeroness suffices for the actual zero scheme to be finite: the required generic nonzeroness is derived from the given covering charts. |
| Actual finite zero scheme and function-dimension ingredients of [Stacks 33.44.12(2)](https://stacks.math.columbia.edu/tag/0B40); not the degree implication | [`schemeSectionZeroScheme_globalFunctions_pos_of_ne_zero`](Normalizer/SectionZeroFinite.lean#L155) | theorem | A zero of a globally nonzero section gives a positive-dimensional actual zero-scheme function space, with generic nonzeroness derived. |
| Actual finite zero scheme and function-dimension ingredients of [Stacks 33.44.12(2)](https://stacks.math.columbia.edu/tag/0B40); not the degree implication | [`properCurve_exists_finite_sectionZeroScheme_of_ne_zero`](Normalizer/SectionZeroFinite.lean#L171) | theorem | A nonzero global section and genuine pointwise line charts on a proper integral curve construct a finite cover and an actual finite zero scheme. |
| Actual finite zero scheme and function-dimension ingredients of [Stacks 33.44.12(2)](https://stacks.math.columbia.edu/tag/0B40); not the degree implication | [`schemeDeterminantZeroScheme_isFinite`](Normalizer/SectionZeroFinite.lean#L191) | theorem | The actual determinant zero scheme is finite over the field; its generic nonzeroness and line charts are derived from the specified family and genuine rank-n charts. |
| Actual finite zero scheme and function-dimension ingredients of [Stacks 33.44.12(2)](https://stacks.math.columbia.edu/tag/0B40); not the degree implication | [`schemeDeterminantZeroScheme_globalFunctions_pos_of_zero`](Normalizer/SectionZeroFinite.lean#L204) | theorem | A zero of the actual specified determinant gives positive dimension of the global functions on its actual finite zero scheme. The comparison with the established line-bundle degree remains a separate theorem. |

## ClosedSubschemeModules

| Source / mathematical role | Lean declaration | Kind | Exact coverage |
|---|---|---|---|
| Actual structure-module quotient supporting the zero-scheme sequence in [Stacks 33.44.9](https://stacks.math.columbia.edu/tag/0AYY) | [`closedSubschemeStructureSheaf`](Normalizer/ClosedSubschemeModules.lean#L17) | def | The structure sheaf of the actual closed subscheme, pushed forward as a module sheaf on the ambient scheme. |
| Actual structure-module quotient supporting the zero-scheme sequence in [Stacks 33.44.9](https://stacks.math.columbia.edu/tag/0AYY) | [`closedSubschemeStructureMap`](Normalizer/ClosedSubschemeModules.lean#L23) | def | The actual quotient map from the ambient structure module to the pushforward of the closed subscheme's structure module. |
| Actual structure-module quotient supporting the zero-scheme sequence in [Stacks 33.44.9](https://stacks.math.columbia.edu/tag/0AYY) | [`closedSubschemeStructureMap_app`](Normalizer/ClosedSubschemeModules.lean#L29) | theorem | On sections, the module quotient map is the actual closed-immersion map on regular functions. |
| Actual structure-module quotient supporting the zero-scheme sequence in [Stacks 33.44.9](https://stacks.math.columbia.edu/tag/0AYY) | [`closedSubschemeStructureMap_affine_surjective`](Normalizer/ClosedSubschemeModules.lean#L33) | theorem | On an actual affine open, the structure-module quotient is surjective. |
| Actual structure-module quotient supporting the zero-scheme sequence in [Stacks 33.44.9](https://stacks.math.columbia.edu/tag/0AYY) | [`closedSubschemeStructureMap_affine_eq_zero_iff`](Normalizer/ClosedSubschemeModules.lean#L39) | theorem | On an actual affine open, vanishing under the structure-module quotient is exactly membership in the defining ideal. |
| Actual structure-module quotient supporting the zero-scheme sequence in [Stacks 33.44.9](https://stacks.math.columbia.edu/tag/0AYY) | [`closedSubschemeStructureMap_stalk_surjective`](Normalizer/ClosedSubschemeModules.lean#L47) | theorem | The actual closed-subscheme quotient is surjective on every ambient module stalk, including at points outside the closed subscheme. |

## SectionZeroIdealAffine

| Source / mathematical role | Lean declaration | Kind | Exact coverage |
|---|---|---|---|
| Actual affine ideal/image comparison supporting the specified-section zero scheme; not a degree formula | [`schemeSectionZeroIdeal_ideal_image`](Normalizer/SectionZeroIdealAffine.lean#L18) | theorem | On an affine open of a genuine chart, the glued ideal is exactly the actual sectionwise image of the original module-sheaf morphism. |
| Actual affine ideal/image comparison supporting the specified-section zero scheme; not a degree formula | [`schemeSectionZeroIdeal_ideal_of_le`](Normalizer/SectionZeroIdealAffine.lean#L29) | theorem | On every actual affine subopen of a chosen genuine chart, the global zero ideal is the image of the actual section map. |
| Actual affine ideal/image comparison supporting the specified-section zero scheme; not a degree formula | [`schemeSectionZeroSchemeι_app_ker`](Normalizer/SectionZeroIdealAffine.lean#L46) | theorem | The kernel of the actual zero-subscheme ring map is exactly the sectionwise image ideal on affine subopens of genuine charts. |
| Actual affine ideal/image comparison supporting the specified-section zero scheme; not a degree formula | [`schemeSectionZeroSchemeι_app_eq_zero_iff`](Normalizer/SectionZeroIdealAffine.lean#L56) | theorem | A scalar restricts to zero on the actual zero subscheme exactly when it is the image of an actual section of the source line sheaf. |

## SheafCokernelComparison

| Source / mathematical role | Lean declaration | Kind | Exact coverage |
|---|---|---|---|
| General actual-stalk criterion used to assemble the scalar sheaf cokernel; geometric hypotheses are proved in SectionZeroCokernel | [`sheaf_cokernel_desc_stalk_comp`](Normalizer/SheafCokernelComparison.lean#L19) | theorem | The canonical comparison has the prescribed effect on actual stalk elements represented through the actual cokernel projection. |
| General actual-stalk criterion used to assemble the scalar sheaf cokernel; geometric hypotheses are proved in SectionZeroCokernel | [`sheaf_cokernel_desc_stalk_bijective`](Normalizer/SheafCokernelComparison.lean#L29) | theorem | Actual stalk exactness and surjectivity make the canonical cokernel comparison bijective on that stalk. Monicity of the first map is unnecessary. |
| General actual-stalk criterion used to assemble the scalar sheaf cokernel; geometric hypotheses are proved in SectionZeroCokernel | [`sheaf_cokernel_desc_isIso`](Normalizer/SheafCokernelComparison.lean#L53) | theorem | Exactness and surjectivity on every actual stalk identify the actual sheaf cokernel with the proposed target by its canonical comparison map. |
| General actual-stalk criterion used to assemble the scalar sheaf cokernel; geometric hypotheses are proved in SectionZeroCokernel | [`sheafCokernelComparisonIso`](Normalizer/SheafCokernelComparison.lean#L62) | def | The canonical actual sheaf-cokernel isomorphism produced from the verified stalk conditions. |
| General actual-stalk criterion used to assemble the scalar sheaf cokernel; geometric hypotheses are proved in SectionZeroCokernel | [`sheafCokernelComparisonIso_π_hom`](Normalizer/SheafCokernelComparison.lean#L71) | theorem | The comparison isomorphism preserves the actual quotient map. |

## SectionZeroCokernel

| Source / mathematical role | Lean declaration | Kind | Exact coverage |
|---|---|---|---|
| Actual scalar zero-scheme cokernel supporting [Stacks 33.44.9](https://stacks.math.columbia.edu/tag/0AYY); not the line-degree implication | [`schemeSectionZeroQuotient_stalk_comp`](Normalizer/SectionZeroCokernel.lean#L21) | theorem | The original line map followed by restriction to its actual zero scheme vanishes on every actual stalk. |
| Actual scalar zero-scheme cokernel supporting [Stacks 33.44.9](https://stacks.math.columbia.edu/tag/0AYY); not the line-degree implication | [`schemeSectionZeroQuotient_comp`](Normalizer/SectionZeroCokernel.lean#L42) | theorem | The original line map vanishes under the actual closed-subscheme structure quotient as a morphism of sheaves. |
| Actual scalar zero-scheme cokernel supporting [Stacks 33.44.9](https://stacks.math.columbia.edu/tag/0AYY); not the line-degree implication | [`schemeSectionZeroQuotient_stalk_exact`](Normalizer/SectionZeroCokernel.lean#L62) | theorem | Every actual stalk element killed by the closed-subscheme quotient comes from the original line sheaf. Affine refinement proves the lift. |
| Actual scalar zero-scheme cokernel supporting [Stacks 33.44.9](https://stacks.math.columbia.edu/tag/0AYY); not the line-degree implication | [`schemeSectionZeroQuotient_stalk_ker_eq_range`](Normalizer/SectionZeroCokernel.lean#L103) | theorem | The kernel of the actual zero-scheme quotient on every stalk is the image of the original line map, with no exactness hypothesis supplied. |
| Actual scalar zero-scheme cokernel supporting [Stacks 33.44.9](https://stacks.math.columbia.edu/tag/0AYY); not the line-degree implication | [`schemeSectionZeroCokernelIso`](Normalizer/SectionZeroCokernel.lean#L115) | def | The actual cokernel of a line map is the pushed-forward structure module of its actual zero scheme. No integrality or monicity is required. |
| Actual scalar zero-scheme cokernel supporting [Stacks 33.44.9](https://stacks.math.columbia.edu/tag/0AYY); not the line-degree implication | [`schemeSectionZeroCokernelIso_π_hom`](Normalizer/SectionZeroCokernel.lean#L122) | theorem | The actual cokernel isomorphism preserves the canonical quotient map. |

## SectionHomMono

| Source / mathematical role | Lean declaration | Kind | Exact coverage |
|---|---|---|---|
| Actual nonzero-section monicity supporting [Stacks 33.44.12(2)](https://stacks.math.columbia.edu/tag/0B40) | [`schemeSectionHom_apply`](Normalizer/SectionHomMono.lean#L18) | theorem | The sheaf map represented by the specified section is actual scalar multiplication by its restriction on each open. |
| Actual nonzero-section monicity supporting [Stacks 33.44.12(2)](https://stacks.math.columbia.edu/tag/0B40) | [`schemeSectionHom_coordinate`](Normalizer/SectionHomMono.lean#L27) | theorem | In a genuine line chart, the actual section map is multiplication by the actual local equation of the given section. |
| Actual nonzero-section monicity supporting [Stacks 33.44.12(2)](https://stacks.math.columbia.edu/tag/0B40) | [`schemeSectionHom_injective_on_chart`](Normalizer/SectionHomMono.lean#L40) | theorem | A nonzero generic germ makes the actual section map injective on every nonempty genuine line chart. |
| Actual nonzero-section monicity supporting [Stacks 33.44.12(2)](https://stacks.math.columbia.edu/tag/0B40) | [`schemeSectionHom_injective`](Normalizer/SectionHomMono.lean#L54) | theorem | Genuine pointwise line charts make the section map injective on all opens, including the empty open, by the actual sheaf separation property. |
| Actual nonzero-section monicity supporting [Stacks 33.44.12(2)](https://stacks.math.columbia.edu/tag/0B40) | [`schemeSectionHom_mono_of_generic_ne_zero`](Normalizer/SectionHomMono.lean#L82) | theorem | A generically nonzero actual line section induces a monomorphism of actual module sheaves. |
| Actual nonzero-section monicity supporting [Stacks 33.44.12(2)](https://stacks.math.columbia.edu/tag/0B40) | [`schemeSectionHom_mono`](Normalizer/SectionHomMono.lean#L93) | theorem | A nonzero global section of a locally trivial line sheaf on an integral scheme induces the actual monomorphism `O_X → L`. |

## SectionZeroExact

| Source / mathematical role | Lean declaration | Kind | Exact coverage |
|---|---|---|---|
| Actual scalar short exact sequence supporting [Stacks 33.44.9](https://stacks.math.columbia.edu/tag/0AYY); the line sequence and degree comparison remain separate | [`schemeSectionZeroComplex`](Normalizer/SectionZeroExact.lean#L25) | def | The actual line map and actual closed-subscheme structure quotient, with their zero composite already proved on actual stalks. |
| Actual scalar short exact sequence supporting [Stacks 33.44.9](https://stacks.math.columbia.edu/tag/0AYY); the line sequence and degree comparison remain separate | [`schemeSectionZeroQuotient_epi`](Normalizer/SectionZeroExact.lean#L31) | theorem | The actual closed-subscheme quotient is an epimorphism, because the constructed cokernel isomorphism identifies it with the cokernel projection. |
| Actual scalar short exact sequence supporting [Stacks 33.44.9](https://stacks.math.columbia.edu/tag/0AYY); the line sequence and degree comparison remain separate | [`schemeSectionZeroComplex_exact`](Normalizer/SectionZeroExact.lean#L38) | theorem | The actual zero-scheme scalar complex is exact for every line map, including maps that are not monic. |
| Actual scalar short exact sequence supporting [Stacks 33.44.9](https://stacks.math.columbia.edu/tag/0AYY); the line sequence and degree comparison remain separate | [`schemeSectionZeroComplex_shortExact`](Normalizer/SectionZeroExact.lean#L48) | theorem | For a monic line map, its actual zero-scheme scalar sequence is short exact. |
| Actual scalar short exact sequence supporting [Stacks 33.44.9](https://stacks.math.columbia.edu/tag/0AYY); the line sequence and degree comparison remain separate | [`schemeSectionDualZeroComplex`](Normalizer/SectionZeroExact.lean#L58) | def | The actual scalar zero-scheme sequence associated to the specified section uses its genuine dual sheaf and its actual evaluation map. |
| Actual scalar short exact sequence supporting [Stacks 33.44.9](https://stacks.math.columbia.edu/tag/0AYY); the line sequence and degree comparison remain separate | [`schemeSectionDualZeroComplex_shortExact`](Normalizer/SectionZeroExact.lean#L64) | theorem | A nonzero section in genuine line charts on an integral scheme gives the actual short exact sequence `0 → L∨ → O_X → i_*O_D → 0`. |
| Actual scalar short exact sequence supporting [Stacks 33.44.9](https://stacks.math.columbia.edu/tag/0AYY); the line sequence and degree comparison remain separate | [`schemeDeterminantDualZeroComplex_shortExact`](Normalizer/SectionZeroExact.lean#L79) | theorem | The specified determinant section gives the same actual short exact sequence when its chosen section germs are independent over the function field. |

## LineRestrictionComparison

| Source / mathematical role | Lean declaration | Kind | Exact coverage |
|---|---|---|---|
| Actual local line pullback/pushforward comparisons supporting the line sequence; complete specified-map compatibility is proved in LineRestrictionCompatibility | [`schemePullbackRestrictIso`](Normalizer/LineRestrictionComparison.lean#L16) | def | Restricting an actual pullback to the inverse-image open is the pullback of the actual restriction along the restricted scheme morphism. |
| Actual local line pullback/pushforward comparisons supporting the line sequence; complete specified-map compatibility is proved in LineRestrictionCompatibility | [`schemeLineChartOnRestriction`](Normalizer/LineRestrictionComparison.lean#L27) | def | Convert a genuine over-site line chart to the actual open-subscheme restriction. |
| Actual local line pullback/pushforward comparisons supporting the line sequence; complete specified-map compatibility is proved in LineRestrictionCompatibility | [`schemePullbackLineChart`](Normalizer/LineRestrictionComparison.lean#L37) | def | A genuine local line chart pulls back to a genuine chart on the actual inverse-image open, for an arbitrary scheme morphism. |
| Actual local line pullback/pushforward comparisons supporting the line sequence; complete specified-map compatibility is proved in LineRestrictionCompatibility | [`schemePushforwardOverMap`](Normalizer/LineRestrictionComparison.lean#L57) | def | A morphism over the actual inverse-image open induces a morphism between the pushforwards over the original open, by actual scalar restriction. |
| Actual local line pullback/pushforward comparisons supporting the line sequence; complete specified-map compatibility is proved in LineRestrictionCompatibility | [`schemePushforwardOverIso`](Normalizer/LineRestrictionComparison.lean#L81) | def | Genuine inverse-image charts induce actual isomorphisms between the pushforwards over the original open. |
| Actual local line pullback/pushforward comparisons supporting the line sequence; complete specified-map compatibility is proved in LineRestrictionCompatibility | [`schemeLineRestrictionComparison`](Normalizer/LineRestrictionComparison.lean#L108) | def | A genuine line chart identifies the actual pushforward of its pullback with the actual pushed-forward structure sheaf on that same chart. |
| Actual local line pullback/pushforward comparisons supporting the line sequence; complete specified-map compatibility is proved in LineRestrictionCompatibility | [`schemePullbackUnit_unit_compatibility`](Normalizer/LineRestrictionComparison.lean#L116) | theorem | The canonical identification of the pullback of the unit sheaf preserves the actual structure-sheaf restriction map under adjunction. |
| Actual local line pullback/pushforward comparisons supporting the line sequence; complete specified-map compatibility is proved in LineRestrictionCompatibility | [`schemeOpenRestriction_unit_compatibility`](Normalizer/LineRestrictionComparison.lean#L127) | theorem | The comparison between actual open restriction and categorical pullback preserves their adjunction units. |

## LineRestrictionUnit

| Source / mathematical role | Lean declaration | Kind | Exact coverage |
|---|---|---|---|
| General adjunction-unit coherence supporting the line sequence; these individual identities do not prove the full local comparison diagram | [`schemePullbackComp_unit_compatibility`](Normalizer/LineRestrictionUnit.lean#L12) | theorem | The canonical pullback-composition comparison has the unit compatibility specified by its actual conjugate pushforward-composition map. |
| General adjunction-unit coherence supporting the line sequence; these individual identities do not prove the full local comparison diagram | [`schemeOpenRestriction_inv_unit_compatibility`](Normalizer/LineRestrictionUnit.lean#L29) | theorem | The inverse open-restriction comparison also preserves the actual unit. |
| General adjunction-unit coherence supporting the line sequence; these individual identities do not prove the full local comparison diagram | [`schemePullbackCongr_unit_compatibility`](Normalizer/LineRestrictionUnit.lean#L40) | theorem | Transport along equal scheme morphisms preserves the actual pullback adjunction unit and its corresponding pushforward transport. |

## PullbackRestrictionUnit

| Source / mathematical role | Lean declaration | Kind | Exact coverage |
|---|---|---|---|
| Actual adjunction and restriction coherence supporting the line sequence in [Stacks 33.44.9](https://stacks.math.columbia.edu/tag/0AYY) | [`schemePullbackComp_hom_unit_compatibility`](Normalizer/PullbackRestrictionUnit.lean#L26) | theorem | The forward pullback-composition comparison transports the composed actual adjunction unit to the unit for the composite scheme morphism. |
| Actual adjunction and restriction coherence supporting the line sequence in [Stacks 33.44.9](https://stacks.math.columbia.edu/tag/0AYY) | [`schemePushforwardRestrictionSquareIso`](Normalizer/PullbackRestrictionUnit.lean#L43) | def | The canonical pushforward isomorphism around the actual open-restriction square. |
| Actual adjunction and restriction coherence supporting the line sequence in [Stacks 33.44.9](https://stacks.math.columbia.edu/tag/0AYY) | [`schemePushforwardRestrictionSquareIso_hom_app`](Normalizer/PullbackRestrictionUnit.lean#L52) | theorem | The canonical pushforward square comparison transports actual sections along the proved equality of the two inverse-image opens. |
| Actual adjunction and restriction coherence supporting the line sequence in [Stacks 33.44.9](https://stacks.math.columbia.edu/tag/0AYY) | [`schemePullbackRestrictIso_unit_compatibility`](Normalizer/PullbackRestrictionUnit.lean#L64) | theorem | The actual pullback/restriction comparison transports the actual composite adjunction units around the commuting scheme square. |
| Actual adjunction and restriction coherence supporting the line sequence in [Stacks 33.44.9](https://stacks.math.columbia.edu/tag/0AYY) | [`schemePullbackRestrictIso_unit_app`](Normalizer/PullbackRestrictionUnit.lean#L135) | theorem | On every actual open of the restricted scheme, the comparison takes the transported pullback-unit section to the actual local pullback-unit section. |

## LineRestrictionCompatibility

| Source / mathematical role | Lean declaration | Kind | Exact coverage |
|---|---|---|---|
| Compatibility with the specified line-section maps supporting [Stacks 33.44.9](https://stacks.math.columbia.edu/tag/0AYY) | [`schemePullbackLineChart_overEquiv`](Normalizer/LineRestrictionCompatibility.lean#L14) | theorem | The constructed inverse-image line chart agrees with its actual restricted-scheme chart under the equivalence of sites. |
| Compatibility with the specified line-section maps supporting [Stacks 33.44.9](https://stacks.math.columbia.edu/tag/0AYY) | [`schemeLineChartOnRestriction_hom_app`](Normalizer/LineRestrictionCompatibility.lean#L30) | theorem | The actual restricted line chart has the original chart coordinates. |
| Compatibility with the specified line-section maps supporting [Stacks 33.44.9](https://stacks.math.columbia.edu/tag/0AYY) | [`schemeLineIso_unit_compatibility`](Normalizer/LineRestrictionCompatibility.lean#L40) | theorem | A genuine global line trivialization intertwines the actual adjunction unit with the actual structure-sheaf map. |
| Compatibility with the specified line-section maps supporting [Stacks 33.44.9](https://stacks.math.columbia.edu/tag/0AYY) | [`schemeLineRestrictionComparison_unit_compatibility`](Normalizer/LineRestrictionCompatibility.lean#L61) | theorem | The genuine local line comparison carries the actual adjunction unit to the actual structure-sheaf map, with the original line chart. |

## DiscreteSheafCohomology

| Source / mathematical role | Lean declaration | Kind | Exact coverage |
|---|---|---|---|
| Intrinsic higher-cohomology vanishing on discrete spaces, supporting the zero-dimensional scheme argument of [Stacks Tag 0AYT](https://stacks.math.columbia.edu/tag/0AYT) | [`discreteSheaf_epi_globalSections_surjective`](Normalizer/DiscreteSheafCohomology.lean#L28) | theorem | An epimorphism of actual abelian sheaves on a discrete space is surjective on actual global sections. The lifts are glued from singleton open sets. |
| Intrinsic higher-cohomology vanishing on discrete spaces, supporting the zero-dimensional scheme argument of [Stacks Tag 0AYT](https://stacks.math.columbia.edu/tag/0AYT) | [`discreteSheaf_constantInteger_projective`](Normalizer/DiscreteSheafCohomology.lean#L75) | theorem | The actual constant integer sheaf is projective on a discrete space. |
| Intrinsic higher-cohomology vanishing on discrete spaces, supporting the zero-dimensional scheme argument of [Stacks Tag 0AYT](https://stacks.math.columbia.edu/tag/0AYT) | [`discreteSheaf_positiveCohomology_subsingleton`](Normalizer/DiscreteSheafCohomology.lean#L95) | theorem | Positive-degree cohomology of any actual abelian sheaf on a discrete space vanishes. This uses no reducedness or finiteness assumption on a scheme. |

## FiniteSchemeCohomology

| Source / mathematical role | Lean declaration | Kind | Exact coverage |
|---|---|---|---|
| Intrinsic higher-cohomology vanishing on the actual finite zero scheme, supporting [Stacks Tag 0AYT](https://stacks.math.columbia.edu/tag/0AYT); ambient pushforward comparison remains separate | [`finiteScheme_discreteTopology`](Normalizer/FiniteSchemeCohomology.lean#L17) | theorem | Actual finiteness over a field implies discreteness of the scheme's underlying space, without removing its nilpotents. |
| Intrinsic higher-cohomology vanishing on the actual finite zero scheme, supporting [Stacks Tag 0AYT](https://stacks.math.columbia.edu/tag/0AYT); ambient pushforward comparison remains separate | [`finiteScheme_positiveCohomology_subsingleton`](Normalizer/FiniteSchemeCohomology.lean#L24) | theorem | Every actual abelian sheaf on a finite scheme over a field has vanishing intrinsic positive-degree cohomology. |
| Intrinsic higher-cohomology vanishing on the actual finite zero scheme, supporting [Stacks Tag 0AYT](https://stacks.math.columbia.edu/tag/0AYT); ambient pushforward comparison remains separate | [`schemeSectionZeroScheme_positiveCohomology_subsingleton`](Normalizer/FiniteSchemeCohomology.lean#L41) | theorem | Intrinsic positive-degree cohomology vanishes for every abelian sheaf on the actual zero scheme of the specified section on a finite-type integral curve. |
| Intrinsic higher-cohomology vanishing on the actual finite zero scheme, supporting [Stacks Tag 0AYT](https://stacks.math.columbia.edu/tag/0AYT); ambient pushforward comparison remains separate | [`properCurve_sectionZeroScheme_positiveCohomology_subsingleton`](Normalizer/FiniteSchemeCohomology.lean#L56) | theorem | In particular, intrinsic positive-degree cohomology vanishes on the actual specified zero scheme on a proper integral curve. |

## SectionLineExact

| Source / mathematical role | Lean declaration | Kind | Exact coverage |
|---|---|---|---|
| Actual specified-section short exact sequence in the degree proof of [Stacks 33.44.9](https://stacks.math.columbia.edu/tag/0AYY); no Euler or degree comparison is claimed | [`schemeLocalStalkMap_square`](Normalizer/SectionLineExact.lean#L19) | theorem | An actual commutative square of local sheaf maps gives the corresponding commutative square on the actual stalk, by the germ formulas. |
| Actual specified-section short exact sequence in the degree proof of [Stacks 33.44.9](https://stacks.math.columbia.edu/tag/0AYY); no Euler or degree comparison is claimed | [`schemeSectionHom_dualEvaluation_chart`](Normalizer/SectionLineExact.lean#L37) | theorem | In the same genuine chart, multiplication by the prescribed section and dual evaluation have the same scalar expression. |
| Actual specified-section short exact sequence in the degree proof of [Stacks 33.44.9](https://stacks.math.columbia.edu/tag/0AYY); no Euler or degree comparison is claimed | [`schemeSectionHom_dualEvaluation_stalk`](Normalizer/SectionLineExact.lean#L59) | theorem | The actual line-chart square relating section multiplication and dual evaluation commutes on the ambient stalk. |
| Actual specified-section short exact sequence in the degree proof of [Stacks 33.44.9](https://stacks.math.columbia.edu/tag/0AYY); no Euler or degree comparison is claimed | [`schemeSectionLineRestrictionSheaf`](Normalizer/SectionLineExact.lean#L74) | def | The actual restriction of the line bundle to its section's zero scheme, pushed forward to the ambient scheme. |
| Actual specified-section short exact sequence in the degree proof of [Stacks 33.44.9](https://stacks.math.columbia.edu/tag/0AYY); no Euler or degree comparison is claimed | [`schemeSectionLineRestrictionMap`](Normalizer/SectionLineExact.lean#L82) | def | The actual restriction map is the unit of the pullback-pushforward adjunction for the actual zero-scheme closed immersion. |
| Actual specified-section short exact sequence in the degree proof of [Stacks 33.44.9](https://stacks.math.columbia.edu/tag/0AYY); no Euler or degree comparison is claimed | [`schemeSectionLineRestriction_chart`](Normalizer/SectionLineExact.lean#L133) | theorem | The actual restriction map has the scalar quotient expression in any genuine line chart, by the proved adjunction compatibility. |
| Actual specified-section short exact sequence in the degree proof of [Stacks 33.44.9](https://stacks.math.columbia.edu/tag/0AYY); no Euler or degree comparison is claimed | [`schemeSectionLineRestriction_stalk_surjective`](Normalizer/SectionLineExact.lean#L166) | theorem | Restriction of the line sheaf to the actual zero scheme is surjective on each actual stalk. |
| Actual specified-section short exact sequence in the degree proof of [Stacks 33.44.9](https://stacks.math.columbia.edu/tag/0AYY); no Euler or degree comparison is claimed | [`schemeSectionLineRestriction_stalk_comp`](Normalizer/SectionLineExact.lean#L172) | theorem | Section multiplication followed by actual zero-scheme restriction vanishes on every actual stalk. |
| Actual specified-section short exact sequence in the degree proof of [Stacks 33.44.9](https://stacks.math.columbia.edu/tag/0AYY); no Euler or degree comparison is claimed | [`schemeSectionLineRestriction_stalk_ker_eq_range`](Normalizer/SectionLineExact.lean#L179) | theorem | The actual kernel of line restriction on a stalk is exactly the image of multiplication by the specified section. |
| Actual specified-section short exact sequence in the degree proof of [Stacks 33.44.9](https://stacks.math.columbia.edu/tag/0AYY); no Euler or degree comparison is claimed | [`schemeSectionLineRestriction_comp`](Normalizer/SectionLineExact.lean#L190) | theorem | The specified section vanishes after actual restriction to its zero scheme as a morphism of sheaves. |
| Actual specified-section short exact sequence in the degree proof of [Stacks 33.44.9](https://stacks.math.columbia.edu/tag/0AYY); no Euler or degree comparison is claimed | [`schemeSectionLineCokernelIso`](Normalizer/SectionLineExact.lean#L213) | def | The actual cokernel of section multiplication is the actual pushforward of the line bundle restricted to its zero scheme. |
| Actual specified-section short exact sequence in the degree proof of [Stacks 33.44.9](https://stacks.math.columbia.edu/tag/0AYY); no Euler or degree comparison is claimed | [`schemeSectionLineCokernelIso_π_hom`](Normalizer/SectionLineExact.lean#L221) | theorem | The cokernel comparison preserves the canonical quotient map and the actual adjunction restriction map. |
| Actual specified-section short exact sequence in the degree proof of [Stacks 33.44.9](https://stacks.math.columbia.edu/tag/0AYY); no Euler or degree comparison is claimed | [`schemeSectionLineRestriction_epi`](Normalizer/SectionLineExact.lean#L229) | theorem | The actual zero-scheme restriction map is an epimorphism of sheaves. |
| Actual specified-section short exact sequence in the degree proof of [Stacks 33.44.9](https://stacks.math.columbia.edu/tag/0AYY); no Euler or degree comparison is claimed | [`schemeSectionLineComplex`](Normalizer/SectionLineExact.lean#L234) | def | The actual section-multiplication and zero-scheme restriction complex. |
| Actual specified-section short exact sequence in the degree proof of [Stacks 33.44.9](https://stacks.math.columbia.edu/tag/0AYY); no Euler or degree comparison is claimed | [`schemeSectionLineComplex_exact`](Normalizer/SectionLineExact.lean#L240) | theorem | The actual line restriction sequence is exact even without a nonzero-section or integrality hypothesis. |
| Actual specified-section short exact sequence in the degree proof of [Stacks 33.44.9](https://stacks.math.columbia.edu/tag/0AYY); no Euler or degree comparison is claimed | [`schemeSectionLineComplex_shortExact`](Normalizer/SectionLineExact.lean#L251) | theorem | A nonzero line section on an integral scheme gives the actual short exact sequence `0 → O_X → L → i_*i^*L → 0` for its constructed zero scheme. |
| Actual specified-section short exact sequence in the degree proof of [Stacks 33.44.9](https://stacks.math.columbia.edu/tag/0AYY); no Euler or degree comparison is claimed | [`schemeDeterminantLineComplex_shortExact`](Normalizer/SectionLineExact.lean#L268) | theorem | The specified determinant section produces the actual line restriction short exact sequence when its chosen generic germs are independent. |
| Actual specified-section short exact sequence in the degree proof of [Stacks 33.44.9](https://stacks.math.columbia.edu/tag/0AYY); no Euler or degree comparison is claimed | [`properScheme_exists_sectionLine_shortExact`](Normalizer/SectionLineExact.lean#L282) | theorem | On an integral proper scheme over a field, pointwise genuine line charts suffice: the finite quasi-compact cover and the actual line restriction short exact sequence are constructed. No dimension hypothesis is needed. |

## AbelianSheafPullbackExact

| Source / mathematical role | Lean declaration | Kind | Exact coverage |
|---|---|---|---|
| Exact inverse image supporting the closed-embedding comparison in [Stacks 20.20.1](https://stacks.math.columbia.edu/tag/02UV) | [`abelianSheafPullback_preservesFiniteLimits`](Normalizer/AbelianSheafPullbackExact.lean#L19) | theorem | Inverse image of abelian sheaves preserves finite limits: inverse image on opens is representably flat, and the actual site pullback is left exact. |
| Exact inverse image supporting the closed-embedding comparison in [Stacks 20.20.1](https://stacks.math.columbia.edu/tag/02UV) | [`abelianSheafPullback_preservesFiniteColimits`](Normalizer/AbelianSheafPullbackExact.lean#L27) | theorem | Inverse image preserves finite colimits by its actual pushforward adjunction. |
| Exact inverse image supporting the closed-embedding comparison in [Stacks 20.20.1](https://stacks.math.columbia.edu/tag/02UV) | [`abelianSheafPullback_additive`](Normalizer/AbelianSheafPullbackExact.lean#L32) | theorem | The actual inverse-image functor on abelian sheaves is additive. |
| Exact inverse image supporting the closed-embedding comparison in [Stacks 20.20.1](https://stacks.math.columbia.edu/tag/02UV) | [`abelianSheafPullback_shortExact`](Normalizer/AbelianSheafPullbackExact.lean#L40) | theorem | A short exact sequence of abelian sheaves remains short exact under the actual inverse-image functor of any continuous map. |

## ClosedPushforwardExact

| Source / mathematical role | Lean declaration | Kind | Exact coverage |
|---|---|---|---|
| Exactness part of [Stacks 17.6.1](https://stacks.math.columbia.edu/tag/01AX); no full-faithfulness or essential-image assertion | [`abelianSheafPushforward_additive`](Normalizer/ClosedPushforwardExact.lean#L26) | theorem | Actual abelian-sheaf direct image is additive for every continuous map. |
| Exactness part of [Stacks 17.6.1](https://stacks.math.columbia.edu/tag/01AX); no full-faithfulness or essential-image assertion | [`closedPushforward_map_epi`](Normalizer/ClosedPushforwardExact.lean#L34) | theorem | Direct image along an actual closed embedding preserves epimorphisms of abelian sheaves. The proof uses local lifts, not surjectivity on fixed opens. |
| Exactness part of [Stacks 17.6.1](https://stacks.math.columbia.edu/tag/01AX); no full-faithfulness or essential-image assertion | [`closedPushforward_preservesEpimorphisms`](Normalizer/ClosedPushforwardExact.lean#L75) | theorem | Epimorphism preservation for the actual closed direct-image functor. |
| Exactness part of [Stacks 17.6.1](https://stacks.math.columbia.edu/tag/01AX); no full-faithfulness or essential-image assertion | [`closedPushforward_preservesHomology`](Normalizer/ClosedPushforwardExact.lean#L80) | theorem | Closed direct image preserves homology, hence exactness of actual short complexes. |
| Exactness part of [Stacks 17.6.1](https://stacks.math.columbia.edu/tag/01AX); no full-faithfulness or essential-image assertion | [`closedPushforward_preservesFiniteColimits`](Normalizer/ClosedPushforwardExact.lean#L86) | theorem | Closed direct image of actual abelian sheaves preserves finite colimits. |

## ConstantSheafPullback

| Source / mathematical role | Lean declaration | Kind | Exact coverage |
|---|---|---|---|
| Canonical constant-sheaf and global-section comparison supporting [Stacks 20.20.1](https://stacks.math.columbia.edu/tag/02UV) | [`abelianSheafPushforwardSectionsIso`](Normalizer/ConstantSheafPullback.lean#L17) | def | Global sections of an actual direct image are the original global sections. |
| Canonical constant-sheaf and global-section comparison supporting [Stacks 20.20.1](https://stacks.math.columbia.edu/tag/02UV) | [`abelianSheafPullbackConstantIso`](Normalizer/ConstantSheafPullback.lean#L24) | def | The actual pullback of constant abelian sheaves, naturally in their values. |
| Canonical constant-sheaf and global-section comparison supporting [Stacks 20.20.1](https://stacks.math.columbia.edu/tag/02UV) | [`abelianSheafPullbackConstant_homEquiv`](Normalizer/ConstantSheafPullback.lean#L34) | theorem | The constant-sheaf comparison agrees with the actual global-section adjunction. |

## ClosedPushforwardCohomology

| Source / mathematical role | Lean declaration | Kind | Exact coverage |
|---|---|---|---|
| Actual abelian-sheaf cohomology comparison of [Stacks 20.20.1](https://stacks.math.columbia.edu/tag/02UV) | [`closedPushforwardCohomologyEquiv`](Normalizer/ClosedPushforwardCohomology.lean#L22) | def | Cohomology of an actual closed direct image agrees with intrinsic cohomology, in every degree. This is an additive equivalence. |
| Actual abelian-sheaf cohomology comparison of [Stacks 20.20.1](https://stacks.math.columbia.edu/tag/02UV) | [`closedPushforwardCohomologyEquiv_naturality`](Normalizer/ClosedPushforwardCohomology.lean#L35) | theorem | The comparison preserves cohomology maps of actual sheaf morphisms. |
| Actual abelian-sheaf cohomology comparison of [Stacks 20.20.1](https://stacks.math.columbia.edu/tag/02UV) | [`closedPushforwardCohomologyEquiv_equiv₀`](Normalizer/ClosedPushforwardCohomology.lean#L55) | theorem | The constructed comparison in degree zero is the actual identification of global sections of direct image, under mathlib's `H.equiv₀`. |

## ModuleAbelianPushforward

| Source / mathematical role | Lean declaration | Kind | Exact coverage |
|---|---|---|---|
| Actual module-to-abelian comparison for the line sequence in [Stacks 33.44.9](https://stacks.math.columbia.edu/tag/0AYY) | [`schemeModulesToAbelianSheaves`](Normalizer/ModuleAbelianPushforward.lean#L14) | def | The existing module-sheaf forgetful functor, specialized to a scheme. |
| Actual module-to-abelian comparison for the line sequence in [Stacks 33.44.9](https://stacks.math.columbia.edu/tag/0AYY) | [`schemeModulesToAbelianSheaves_obj_presheaf`](Normalizer/ModuleAbelianPushforward.lean#L19) | theorem | Its underlying presheaf is the actual scheme-module additive presheaf. |
| Actual module-to-abelian comparison for the line sequence in [Stacks 33.44.9](https://stacks.math.columbia.edu/tag/0AYY) | [`schemeModulesToAbelianSheaves_map`](Normalizer/ModuleAbelianPushforward.lean#L23) | theorem | On morphisms it is the actual scheme-module additive presheaf map. |
| Actual module-to-abelian comparison for the line sequence in [Stacks 33.44.9](https://stacks.math.columbia.edu/tag/0AYY) | [`schemeModuleAbelianPushforwardIso`](Normalizer/ModuleAbelianPushforward.lean#L30) | def | Actual scheme-module pushforward commutes with forgetting to abelian sheaves. Scalar restriction does not alter the underlying additive sheaf. |
| Actual module-to-abelian comparison for the line sequence in [Stacks 33.44.9](https://stacks.math.columbia.edu/tag/0AYY) | [`schemeModuleAbelianPushforwardIso_app`](Normalizer/ModuleAbelianPushforward.lean#L36) | theorem | The canonical comparison is identity on actual sections on every open. |
| Actual module-to-abelian comparison for the line sequence in [Stacks 33.44.9](https://stacks.math.columbia.edu/tag/0AYY) | [`schemeModuleAbelianPushforwardIso_naturality`](Normalizer/ModuleAbelianPushforward.lean#L41) | theorem | The comparison commutes with every actual module-sheaf morphism. |
| Actual module-to-abelian comparison for the line sequence in [Stacks 33.44.9](https://stacks.math.columbia.edu/tag/0AYY) | [`schemeModuleAbelianPushforward_map_app`](Normalizer/ModuleAbelianPushforward.lean#L51) | theorem | Pushforward of a module morphism acts on underlying abelian sections by that same morphism on the actual inverse-image open. |
| Actual module-to-abelian comparison for the line sequence in [Stacks 33.44.9](https://stacks.math.columbia.edu/tag/0AYY) | [`schemeSectionLineRestrictionAbelianIso`](Normalizer/ModuleAbelianPushforward.lean#L63) | def | The actual line-restriction cokernel, viewed as an abelian sheaf, is the ordinary abelian-sheaf pushforward of the actual pulled-back line bundle. |
| Actual module-to-abelian comparison for the line sequence in [Stacks 33.44.9](https://stacks.math.columbia.edu/tag/0AYY) | [`schemeSectionLineCokernelAbelianIso`](Normalizer/ModuleAbelianPushforward.lean#L80) | def | The underlying abelian sheaf of the actual section cokernel is the ordinary pushforward of the actual restricted line bundle. |
| Actual module-to-abelian comparison for the line sequence in [Stacks 33.44.9](https://stacks.math.columbia.edu/tag/0AYY) | [`schemeSectionLineCokernelAbelianIso_π_hom`](Normalizer/ModuleAbelianPushforward.lean#L96) | theorem | The abelian-sheaf cokernel identification preserves the actual cokernel projection and the actual adjunction restriction map. |

## SectionCokernelCohomology

| Source / mathematical role | Lean declaration | Kind | Exact coverage |
|---|---|---|---|
| Constructed-cokernel vanishing ingredient of [Stacks 33.33.3](https://stacks.math.columbia.edu/tag/0AYT); no Euler or rank formula is claimed | [`schemeClosedPushforwardCohomologyEquiv`](Normalizer/SectionCokernelCohomology.lean#L20) | def | Cohomology of actual module-sheaf direct image along a closed immersion, computed on the underlying abelian sheaves, agrees with source cohomology. |
| Constructed-cokernel vanishing ingredient of [Stacks 33.33.3](https://stacks.math.columbia.edu/tag/0AYT); no Euler or rank formula is claimed | [`finiteClosedPushforward_positiveCohomology_subsingleton`](Normalizer/SectionCokernelCohomology.lean#L31) | theorem | Direct image of an actual module sheaf on a finite closed subscheme has vanishing ambient positive-degree cohomology. |
| Constructed-cokernel vanishing ingredient of [Stacks 33.33.3](https://stacks.math.columbia.edu/tag/0AYT); no Euler or rank formula is claimed | [`schemeSectionLineCokernelCohomologyEquiv`](Normalizer/SectionCokernelCohomology.lean#L47) | def | The actual section cokernel has the cohomology of the actual restricted line bundle on the constructed zero scheme, in every degree. |
| Constructed-cokernel vanishing ingredient of [Stacks 33.33.3](https://stacks.math.columbia.edu/tag/0AYT); no Euler or rank formula is claimed | [`schemeSectionLineRestriction_positiveCohomology_subsingleton`](Normalizer/SectionCokernelCohomology.lean#L71) | theorem | Positive ambient cohomology of the actual line-restriction quotient vanishes on a finite-type integral curve. Finiteness of its zero scheme is derived. |
| Constructed-cokernel vanishing ingredient of [Stacks 33.33.3](https://stacks.math.columbia.edu/tag/0AYT); no Euler or rank formula is claimed | [`schemeSectionLineCokernel_positiveCohomology_subsingleton`](Normalizer/SectionCokernelCohomology.lean#L88) | theorem | Positive ambient cohomology of the actual cokernel of the specified section vanishes on a finite-type integral curve. |
| Constructed-cokernel vanishing ingredient of [Stacks 33.33.3](https://stacks.math.columbia.edu/tag/0AYT); no Euler or rank formula is claimed | [`properCurve_sectionLineCokernel_positiveCohomology_subsingleton`](Normalizer/SectionCokernelCohomology.lean#L103) | theorem | On a proper integral curve, a nonzero global line section has an acyclic actual cokernel. Both the finite chart cover and generic nonzeroness are derived from genuine pointwise line trivializations. |
| Constructed-cokernel vanishing ingredient of [Stacks 33.33.3](https://stacks.math.columbia.edu/tag/0AYT); no Euler or rank formula is claimed | [`properCurve_determinantCokernel_positiveCohomology_subsingleton`](Normalizer/SectionCokernelCohomology.lean#L121) | theorem | The specified determinant cokernel is acyclic on a proper integral curve. Pointwise rank-n charts construct the exterior line charts, and independence of the actual generic germs supplies nonzeroness of the specified section. |

## SectionCohomologyExact

| Source / mathematical role | Lean declaration | Kind | Exact coverage |
|---|---|---|---|
| Actual cohomology exact sequence underlying the degree argument in [Stacks 33.44.9](https://stacks.math.columbia.edu/tag/0AYY); numerical Euler comparison remains separate | [`schemeModulesToAbelianSheaves_additive`](Normalizer/SectionCohomologyExact.lean#L18) | theorem | The actual forgetful functor is additive. |
| Actual cohomology exact sequence underlying the degree argument in [Stacks 33.44.9](https://stacks.math.columbia.edu/tag/0AYY); numerical Euler comparison remains separate | [`schemeModulesToAbelianSheaves_preservesFiniteLimits`](Normalizer/SectionCohomologyExact.lean#L24) | theorem | The actual forgetful functor preserves finite limits. |
| Actual cohomology exact sequence underlying the degree argument in [Stacks 33.44.9](https://stacks.math.columbia.edu/tag/0AYY); numerical Euler comparison remains separate | [`schemeModulesToAbelianSheaves_map_epi`](Normalizer/SectionCohomologyExact.lean#L35) | theorem | Forgetting module structure preserves epimorphisms: cokernel projections are locally surjective and every epimorphism is its coimage projection followed by an isomorphism. |
| Actual cohomology exact sequence underlying the degree argument in [Stacks 33.44.9](https://stacks.math.columbia.edu/tag/0AYY); numerical Euler comparison remains separate | [`schemeModulesToAbelianSheaves_preservesEpimorphisms`](Normalizer/SectionCohomologyExact.lean#L46) | theorem | The actual module-to-abelian-sheaf forgetful functor preserves epis. |
| Actual cohomology exact sequence underlying the degree argument in [Stacks 33.44.9](https://stacks.math.columbia.edu/tag/0AYY); numerical Euler comparison remains separate | [`schemeModulesToAbelianSheaves_preservesHomology`](Normalizer/SectionCohomologyExact.lean#L51) | theorem | Forgetting module structure preserves homology, hence exactness. |
| Actual cohomology exact sequence underlying the degree argument in [Stacks 33.44.9](https://stacks.math.columbia.edu/tag/0AYY); numerical Euler comparison remains separate | [`schemeModulesToAbelianSheaves_shortExact`](Normalizer/SectionCohomologyExact.lean#L58) | theorem | Every actual short exact sequence of scheme-module sheaves gives a short exact sequence of its actual underlying abelian sheaves. |
| Actual cohomology exact sequence underlying the degree argument in [Stacks 33.44.9](https://stacks.math.columbia.edu/tag/0AYY); numerical Euler comparison remains separate | [`schemeSectionLineAbelianComplex_shortExact`](Normalizer/SectionCohomologyExact.lean#L74) | theorem | The actual sequence O → L → i_*i^*L, with its actual section and restriction maps, remains short exact as abelian sheaves. |
| Actual cohomology exact sequence underlying the degree argument in [Stacks 33.44.9](https://stacks.math.columbia.edu/tag/0AYY); numerical Euler comparison remains separate | [`schemeSectionLineCohomologyδ`](Normalizer/SectionCohomologyExact.lean#L82) | def | The canonical connecting map of the actual section short exact sequence, defined by its extension class. |
| Actual cohomology exact sequence underlying the degree argument in [Stacks 33.44.9](https://stacks.math.columbia.edu/tag/0AYY); numerical Euler comparison remains separate | [`schemeSectionLineCohomologySequence`](Normalizer/SectionCohomologyExact.lean#L93) | def | The six-object segment H⁰(O) → H⁰(L) → H⁰(i_*i^*L) → H¹(O) → H¹(L) → H¹(i_*i^*L), with the actual section and restriction maps. |
| Actual cohomology exact sequence underlying the degree argument in [Stacks 33.44.9](https://stacks.math.columbia.edu/tag/0AYY); numerical Euler comparison remains separate | [`schemeSectionLineCohomologySequence_exact`](Normalizer/SectionCohomologyExact.lean#L110) | theorem | The actual six-object sheaf-cohomology segment is exact at its four interior terms. This assertion does not assume cohomology finiteness. |
| Actual cohomology exact sequence underlying the degree argument in [Stacks 33.44.9](https://stacks.math.columbia.edu/tag/0AYY); numerical Euler comparison remains separate | [`schemeSectionLine_H0_injective`](Normalizer/SectionCohomologyExact.lean#L120) | theorem | The actual first map on H⁰ is injective, as required at the left endpoint of the section cohomology sequence. |
| Actual cohomology exact sequence underlying the degree argument in [Stacks 33.44.9](https://stacks.math.columbia.edu/tag/0AYY); numerical Euler comparison remains separate | [`schemeSectionLine_H1_surjective`](Normalizer/SectionCohomologyExact.lean#L130) | theorem | On a finite-type integral curve the actual H¹ section map is surjective, because the actual line-restriction quotient has vanishing H¹. |


## DiscreteLineTrivialization

| Source / mathematical role | Lean declaration | Kind | Exact coverage |
|---|---|---|---|
| Rank-one finite-scheme ingredient of [Stacks 33.33.3](https://stacks.math.columbia.edu/tag/0AYT); support for P 1440 | [`discreteLineSheafIso`](Normalizer/DiscreteLineTrivialization.lean#L101) | def | Genuine pointwise line charts on a discrete scheme construct an actual global trivialization. Empty and disconnected schemes and nilpotents are allowed. |


## FiniteLineSections

| Source / mathematical role | Lean declaration | Kind | Exact coverage |
|---|---|---|---|
| Rank-one finite-scheme ingredient of [Stacks 33.33.3](https://stacks.math.columbia.edu/tag/0AYT); support for P 1440 | [`finiteLineSheafIso`](Normalizer/FiniteLineSections.lean#L23) | def | A line bundle on a finite scheme is globally trivial. Discreteness is obtained from the actual finite structure morphism and charts are glued. |
| Rank-one finite-scheme ingredient of [Stacks 33.33.3](https://stacks.math.columbia.edu/tag/0AYT); support for P 1440 | [`finiteLineSectionsEquiv`](Normalizer/FiniteLineSections.lean#L29) | def | The constructed line trivialization gives an equivalence between actual sections and global functions, linear for the specified base-field actions. |
| Rank-one finite-scheme ingredient of [Stacks 33.33.3](https://stacks.math.columbia.edu/tag/0AYT); support for P 1440 | [`finiteLineSections_finite`](Normalizer/FiniteLineSections.lean#L40) | theorem | Actual sections of a genuine line bundle on a finite scheme form a finite module over the base field. |
| Rank-one finite-scheme ingredient of [Stacks 33.33.3](https://stacks.math.columbia.edu/tag/0AYT); support for P 1440 | [`finiteLineSections_finrank_eq`](Normalizer/FiniteLineSections.lean#L51) | theorem | The line's actual section dimension equals the dimension of actual global functions; no dimension comparison is supplied as a hypothesis. |
| Rank-one finite-scheme ingredient of [Stacks 33.33.3](https://stacks.math.columbia.edu/tag/0AYT); support for P 1440 | [`finiteLineSections_finrank_pos`](Normalizer/FiniteLineSections.lean#L61) | theorem | A line bundle on a nonempty finite scheme has positive section dimension. |
| Rank-one finite-scheme ingredient of [Stacks 33.33.3](https://stacks.math.columbia.edu/tag/0AYT); support for P 1440 | [`finiteLineSections_finrank_eq_zero_iff`](Normalizer/FiniteLineSections.lean#L72) | theorem | Zero section dimension of a line bundle on a finite scheme detects exactly when the actual scheme is empty. |
| Rank-one finite-scheme ingredient of [Stacks 33.33.3](https://stacks.math.columbia.edu/tag/0AYT); support for P 1440 | [`schemePullback_lineCharts`](Normalizer/FiniteLineSections.lean#L83) | theorem | Pointwise line charts pull back along an arbitrary actual scheme morphism. |
| Rank-one finite-scheme ingredient of [Stacks 33.33.3](https://stacks.math.columbia.edu/tag/0AYT); support for P 1440 | [`finitePullbackLineSections_finrank_eq`](Normalizer/FiniteLineSections.lean#L95) | theorem | Restricting a genuine line bundle to an actual finite scheme preserves the section-dimension formula, using the constructed pullback line charts. |


## ModulePushforwardSections

| Source / mathematical role | Lean declaration | Kind | Exact coverage |
|---|---|---|---|
| Actual scalar comparison supporting the line sequence and P 1440 | [`schemeConstantMap_comp`](Normalizer/ModulePushforwardSections.lean#L18) | theorem | Base constants pull back along the actual scheme morphism, agreeing with the constants induced by the composite structure morphism. |
| Actual scalar comparison supporting the line sequence and P 1440 | [`schemeModulePushforwardGlobalSectionsEquiv`](Normalizer/ModulePushforwardSections.lean#L23) | def | Actual global sections of direct image agree linearly over the base field with global sections on the source. No finiteness or integrality is needed. |
| Actual scalar comparison supporting the line sequence and P 1440 | [`schemeModulePushforwardGlobalSectionsEquiv_apply`](Normalizer/ModulePushforwardSections.lean#L35) | theorem | The global comparison is the actual identity on sections over the inverse image of the top open, which is definitionally the source's top open. |
| Actual scalar comparison supporting the line sequence and P 1440 | [`schemeModulePushforwardGlobalSectionsEquiv_restrict`](Normalizer/ModulePushforwardSections.lean#L41) | theorem | The global comparison preserves restrictions to every actual inverse-image open; it does not replace the sheaf by an abstract isomorphic vector space. |
| Actual scalar comparison supporting the line sequence and P 1440 | [`schemeModulePushforwardGlobalSectionsEquiv_naturality`](Normalizer/ModulePushforwardSections.lean#L49) | theorem | The comparison commutes with actual module-sheaf maps. |


## ModuleSheafCohomologyScalars

| Source / mathematical role | Lean declaration | Kind | Exact coverage |
|---|---|---|---|
| Actual cohomology scalar support for P 924–971 and the determinant degree argument | [`schemeConstantAt_restrict`](Normalizer/ModuleSheafCohomologyScalars.lean#L19) | theorem | Constants on opens commute with actual restriction maps. |
| Actual cohomology scalar support for P 924–971 and the determinant degree argument | [`schemeModuleScalarEnd`](Normalizer/ModuleSheafCohomologyScalars.lean#L27) | def | Multiplication by a base scalar is an actual endomorphism of the underlying abelian sheaf, with scalars restricted from the structure morphism. |
| Actual cohomology scalar support for P 924–971 and the determinant degree argument | [`schemeModuleCohomologyModule`](Normalizer/ModuleSheafCohomologyScalars.lean#L71) | def | The cohomology scalar action is induced by actual scalar endomorphisms, not a chosen vector-space structure on the underlying additive group. |
| Actual cohomology scalar support for P 924–971 and the determinant degree argument | [`schemeModuleScalarEnd_naturality`](Normalizer/ModuleSheafCohomologyScalars.lean#L96) | theorem | Actual module-sheaf morphisms commute with actual scalar endomorphisms. |
| Actual cohomology scalar support for P 924–971 and the determinant degree argument | [`schemeModuleCohomologyMap`](Normalizer/ModuleSheafCohomologyScalars.lean#L105) | def | Actual cohomology maps induced by module-sheaf morphisms are base-field linear. |
| Actual cohomology scalar support for P 924–971 and the determinant degree argument | [`schemeModuleCohomology_smul`](Normalizer/ModuleSheafCohomologyScalars.lean#L123) | theorem | The cohomology scalar is the map induced by multiplication on the sheaf. |
| Actual cohomology scalar support for P 924–971 and the determinant degree argument | [`schemeModuleCohomologyEquiv₀`](Normalizer/ModuleSheafCohomologyScalars.lean#L130) | def | The degree-zero cohomology comparison is linear for the actual base-field actions on cohomology and global sections. |


## SectionCohomologyLinear

| Source / mathematical role | Lean declaration | Kind | Exact coverage |
|---|---|---|---|
| Extension-class scalar naturality supporting actual boundary maps and the line sequence | [`schemeModuleShortExact_extClass_scalar`](Normalizer/SectionCohomologyLinear.lean#L16) | theorem | The extension class of an actual short exact module-sheaf sequence commutes with the actual scalar endomorphisms on its underlying abelian sheaves. |
| Extension-class scalar naturality supporting actual boundary maps and the line sequence | [`schemeSectionLineCohomologyδLinear`](Normalizer/SectionCohomologyLinear.lean#L41) | def | The actual connecting homomorphism of the specified-section sequence is linear over the base field, by naturality of its actual extension class. |


## SectionCokernelSections

| Source / mathematical role | Lean declaration | Kind | Exact coverage |
|---|---|---|---|
| Finite-quotient dimension ingredient of [Stacks 33.44.9](https://stacks.math.columbia.edu/tag/0AYY); support for P 1440, not line degree positivity | [`schemeSectionLineCokernelSectionsEquiv`](Normalizer/SectionCokernelSections.lean#L39) | def | The actual cokernel's global sections agree over the base field with sections of the actual line restricted to its constructed zero scheme. |
| Finite-quotient dimension ingredient of [Stacks 33.44.9](https://stacks.math.columbia.edu/tag/0AYY); support for P 1440, not line degree positivity | [`schemeSectionLineCokernelFunctionsEquiv`](Normalizer/SectionCokernelSections.lean#L56) | def | Actual cokernel sections are linearly equivalent to functions on the actual zero scheme. Finiteness and the restricted line's trivialization are constructed from the curve and genuine line charts. |
| Finite-quotient dimension ingredient of [Stacks 33.44.9](https://stacks.math.columbia.edu/tag/0AYY); support for P 1440, not line degree positivity | [`schemeSectionLineCokernelSections_finite`](Normalizer/SectionCokernelSections.lean#L70) | theorem | The actual cokernel has a finite-dimensional space of global sections. |
| Finite-quotient dimension ingredient of [Stacks 33.44.9](https://stacks.math.columbia.edu/tag/0AYY); support for P 1440, not line degree positivity | [`schemeSectionLineCokernelSections_finrank_eq`](Normalizer/SectionCokernelSections.lean#L82) | theorem | The actual cokernel section dimension equals the actual zero-scheme function dimension under their structure-morphism scalar actions. |
| Finite-quotient dimension ingredient of [Stacks 33.44.9](https://stacks.math.columbia.edu/tag/0AYY); support for P 1440, not line degree positivity | [`schemeSectionLineCokernelSections_finrank_eq_zero_iff`](Normalizer/SectionCokernelSections.lean#L93) | theorem | The actual section cokernel has zero global-section dimension exactly when its constructed zero scheme is empty. |
| Finite-quotient dimension ingredient of [Stacks 33.44.9](https://stacks.math.columbia.edu/tag/0AYY); support for P 1440, not line degree positivity | [`schemeSectionLineCokernelSections_pos_of_zero`](Normalizer/SectionCokernelSections.lean#L105) | theorem | A zero of the specified nonzero section forces positive dimension of the actual cokernel's sections. The zero is tested by its nonunit local germ. |
| Finite-quotient dimension ingredient of [Stacks 33.44.9](https://stacks.math.columbia.edu/tag/0AYY); support for P 1440, not line degree positivity | [`properCurve_sectionLineCokernelSections_finite`](Normalizer/SectionCokernelSections.lean#L120) | theorem | Proper curve hypotheses and genuine pointwise charts construct finite actual cokernel sections, without supplying a finite cover or generic germ. |
| Finite-quotient dimension ingredient of [Stacks 33.44.9](https://stacks.math.columbia.edu/tag/0AYY); support for P 1440, not line degree positivity | [`schemeSectionLineCokernelH0FunctionsEquiv`](Normalizer/SectionCokernelSections.lean#L134) | def | Degree-zero cohomology of the actual cokernel is linearly equivalent to functions on the actual zero scheme under the geometrically induced scalars. |
| Finite-quotient dimension ingredient of [Stacks 33.44.9](https://stacks.math.columbia.edu/tag/0AYY); support for P 1440, not line degree positivity | [`schemeSectionLineCokernelH0_finrank_eq`](Normalizer/SectionCokernelSections.lean#L148) | theorem | Actual H⁰ of the section cokernel has the actual zero-scheme function dimension. This is the zero-dimensional quotient term for Euler additivity. |
| Finite-quotient dimension ingredient of [Stacks 33.44.9](https://stacks.math.columbia.edu/tag/0AYY); support for P 1440, not line degree positivity | [`schemeSectionLineCokernelH0_pos_of_zero`](Normalizer/SectionCokernelSections.lean#L160) | theorem | A zero of the prescribed nonzero section gives positive dimension of actual H⁰ of its actual cokernel, with all scalar structures constructed. |
| Finite-quotient dimension ingredient of [Stacks 33.44.9](https://stacks.math.columbia.edu/tag/0AYY); support for P 1440, not line degree positivity | [`properCurve_sectionLineCokernel_cohomology_finite`](Normalizer/SectionCokernelSections.lean#L176) | theorem | Every actual cohomology group of the section cokernel on a proper integral curve is finite over the base field. Degree zero uses constructed finite-zero-scheme sections; positive degrees use proved ambient vanishing. |
| Finite-quotient dimension ingredient of [Stacks 33.44.9](https://stacks.math.columbia.edu/tag/0AYY); support for P 1440, not line degree positivity | [`properCurve_determinantCokernel_cohomology_finite`](Normalizer/SectionCokernelSections.lean#L198) | theorem | The specified determinant cokernel has finite-dimensional actual cohomology. Genuine rank-n charts construct the line, and independence of the actual generic germs proves the required section is nonzero. |


## ProperLineSectionsFinite

| Source / mathematical role | Lean declaration | Kind | Exact coverage |
|---|---|---|---|
| Proper-curve line H⁰ finiteness support for the degree argument; algebraically closed base, not full proper coherent cohomology | [`sectionCokernel_globalSections_ker_eq_range`](Normalizer/ProperLineSectionsFinite.lean#L25) | theorem | The actual global-section sequence is exact at the line's section space. This does not assert surjectivity onto global sections of the sheaf cokernel. |
| Proper-curve line H⁰ finiteness support for the degree argument; algebraically closed base, not full proper coherent cohomology | [`properCurve_lineSections_finite`](Normalizer/ProperLineSectionsFinite.lean#L48) | theorem | On a proper integral curve over an algebraically closed field, a genuine line bundle with a nonzero global section has finite-dimensional actual global sections. Neither H¹ finiteness nor sectionwise surjectivity is an input. |
| Proper-curve line H⁰ finiteness support for the degree argument; algebraically closed base, not full proper coherent cohomology | [`properCurve_lineSections_finite_of_lineCharts`](Normalizer/ProperLineSectionsFinite.lean#L72) | theorem | Every genuine line bundle on a proper integral curve over an algebraically closed field has finite-dimensional actual global sections. A nonzero section is not an input: when none exists the section space is zero. |
| Proper-curve line H⁰ finiteness support for the degree argument; algebraically closed base, not full proper coherent cohomology | [`properCurve_lineH0_finite_of_lineCharts`](Normalizer/ProperLineSectionsFinite.lean#L91) | theorem | Actual H⁰ of a genuine line bundle on a proper integral curve is finite for the cohomology scalar action induced by the actual structure morphism. |

## SectionCohomologyDimension

| Source / mathematical role | Lean declaration | Kind | Exact coverage |
|---|---|---|---|
| Cohomological support for P 1434–1443; no degree identification | [`schemeSectionLineH1_ker_eq_rangeδ`](Normalizer/SectionCohomologyDimension.lean#L30) | theorem | The actual H¹ section-map kernel equals the range of the actual connecting map, as submodules for the structure-morphism field action. |
| Cohomological support for P 1434–1443; no degree identification | [`schemeSectionLineδ_ker_eq_range`](Normalizer/SectionCohomologyDimension.lean#L53) | theorem | The actual connecting-map kernel equals the range of the actual H⁰ restriction map, over the base field. |
| Cohomological support for P 1434–1443; no degree identification | [`schemeSectionLineH0_ker_eq_range`](Normalizer/SectionCohomologyDimension.lean#L77) | theorem | The actual H⁰ restriction-map kernel equals the range of the actual H⁰ section map. |
| Cohomological support for P 1434–1443; no degree identification | [`properScheme_structureH0_finrank`](Normalizer/SectionCohomologyDimension.lean#L100) | theorem | For integral X universally closed over an algebraically closed field, actual H⁰(O_X) has dimension one for the actual cohomology field action. |
| Cohomological support for P 1434–1443; no degree identification | [`schemeSectionLineRestrictionH0FunctionsEquiv`](Normalizer/SectionCohomologyDimension.lean#L127) | def | On a finite-type integral curve with nonzero line section and finite quasi-compact line charts, actual H⁰(i_*i^*L) is linearly equivalent to functions on its constructed finite zero scheme. |
| Cohomological support for P 1434–1443; no degree identification | [`schemeSectionLineRestrictionH0_finite`](Normalizer/SectionCohomologyDimension.lean#L142) | theorem | Actual H⁰ of the line-restriction term is finite-dimensional, derived from the constructed finite zero scheme. |
| Cohomological support for P 1434–1443; no degree identification | [`schemeSectionLineH1_kernel_finite`](Normalizer/SectionCohomologyDimension.lean#L155) | theorem | The actual H¹ section map has finite-dimensional kernel on the finite-type integral curve; neither whole H¹ space is assumed finite. |
| Cohomological support for P 1434–1443; no degree identification | [`schemeSectionLineH1_finite_iff`](Normalizer/SectionCohomologyDimension.lean#L171) | theorem | The actual H¹(O_X) and H¹(L) finiteness assertions are equivalent for the specified nonzero section. Neither absolute assertion is proved. |
| Cohomological support for P 1434–1443; no degree identification | [`properCurve_sectionH0_add_H1_kernel_finrank`](Normalizer/SectionCohomologyDimension.lean#L201) | theorem | For a proper integral curve over an algebraically closed field, h⁰(L) plus the actual H¹ section-map kernel dimension equals one plus the function dimension of the actual finite zero scheme. It is not a degree formula. |

## SheafCohomologyTerminal

| Source / mathematical role | Lean declaration | Kind | Exact coverage |
|---|---|---|---|
| General cohomology support for P 1434–1443; not affine acyclicity or proper finiteness | [`terminalFreeAbelianPresheafIso`](Normalizer/SheafCohomologyTerminal.lean#L15) | def | The free abelian presheaf represented by a terminal object is canonically isomorphic to the constant lifted-integer presheaf, sending every generator to one. |
| General cohomology support for P 1434–1443; not affine acyclicity or proper finiteness | [`terminalFreeAbelianSheafIso`](Normalizer/SheafCohomologyTerminal.lean#L37) | def | Sheafification constructs the corresponding canonical free-representable/constant-integer sheaf isomorphism. |
| General cohomology support for P 1434–1443; not affine acyclicity or proper finiteness | [`sheafCohomologyTerminalEquiv`](Normalizer/SheafCohomologyTerminal.lean#L46) | def | On a general site with the standard sheafification and Ext infrastructure, actual H'(F,T,n) at terminal T is additively equivalent to actual H(F,n). |
| General cohomology support for P 1434–1443; not affine acyclicity or proper finiteness | [`sheafCohomologyTerminalEquiv_naturality`](Normalizer/SheafCohomologyTerminal.lean#L52) | theorem | The terminal cohomology comparison commutes with maps induced by actual sheaf morphisms. |
| General cohomology support for P 1434–1443; not affine acyclicity or proper finiteness | [`terminalFreeAbelianPresheafIso_inv_one`](Normalizer/SheafCohomologyTerminal.lean#L63) | theorem | The inverse canonical presheaf comparison sends the integer one to the actual identity generator at the terminal object. |
| General cohomology support for P 1434–1443; not affine acyclicity or proper finiteness | [`sheafCohomologyTerminalEquiv_equiv₀`](Normalizer/SheafCohomologyTerminal.lean#L72) | theorem | In degree zero the actual H-to-sections comparison agrees with evaluation on the sheafification of the represented identity generator. |

## OverAbelianExtension

General cohomological support for the determinant step at P 1434–1443.
This is a constructed library interface, not a proof of the manuscript's
full degree or section-bound argument. The site is small; sheafification and
Ext instances are the standard categorical infrastructure, not geometric inputs.

| Source / mathematical role | Lean declaration | Kind | Exact coverage |
|---|---|---|---|
| Support for P 1434–1443; exact hypotheses in declaration | [`overAbelianExtensionObj`](Normalizer/OverAbelianExtension.lean#L40) | def | Extension of an abelian presheaf from the slice, by the direct sum over all arrows into the sliced object. |
| Support for P 1434–1443; exact hypotheses in declaration | [`overAbelianExtensionMap`](Normalizer/OverAbelianExtension.lean#L72) | def | A morphism of slice presheaves acts on each direct-sum coefficient. |
| Support for P 1434–1443; exact hypotheses in declaration | [`overAbelianExtension`](Normalizer/OverAbelianExtension.lean#L94) | def | The direct-sum extension functor on actual abelian presheaves. |
| Support for P 1434–1443; exact hypotheses in declaration | [`overAbelianExtensionAdjunction`](Normalizer/OverAbelianExtension.lean#L152) | def | The direct-sum construction is left adjoint to actual slice restriction of abelian presheaves. |
| Support for P 1434–1443; exact hypotheses in declaration | [`overAbelianExtension_preservesMonomorphisms`](Normalizer/OverAbelianExtension.lean#L207) | theorem | Extension preserves injections because it acts coefficientwise. |
| Support for P 1434–1443; exact hypotheses in declaration | [`overAbelianExtension_additive`](Normalizer/OverAbelianExtension.lean#L223) | theorem | Extension respects addition of presheaf morphisms. |
| Support for P 1434–1443; exact hypotheses in declaration | [`overAbelianSheafExtension`](Normalizer/OverAbelianExtension.lean#L234) | def | The actual left extension of abelian sheaves on the slice site. |
| Support for P 1434–1443; exact hypotheses in declaration | [`overAbelianSheafExtensionAdjunction`](Normalizer/OverAbelianExtension.lean#L241) | def | Sheafification promotes the constructed presheaf adjunction to an adjunction with mathlib's actual slice restriction functor. |
| Support for P 1434–1443; exact hypotheses in declaration | [`overAbelianSheafExtension_additive`](Normalizer/OverAbelianExtension.lean#L250) | theorem | The sheaf extension is additive. |
| Support for P 1434–1443; exact hypotheses in declaration | [`overAbelianSheafExtension_preservesHomology`](Normalizer/OverAbelianExtension.lean#L261) | theorem | The actual sheaf extension is exact; no exactness hypothesis is imposed. |
| Support for P 1434–1443; exact hypotheses in declaration | [`overAbelianRestriction_preservesEpimorphisms`](Normalizer/OverAbelianExtension.lean#L274) | theorem | Slice restriction preserves epimorphisms: cocontinuity supplies its right adjoint by right Kan extension on the small slice site. |
| Support for P 1434–1443; exact hypotheses in declaration | [`overAbelianRestriction_additive`](Normalizer/OverAbelianExtension.lean#L282) | theorem | Slice restriction is additive. |
| Support for P 1434–1443; exact hypotheses in declaration | [`overAbelianRestriction_preservesHomology`](Normalizer/OverAbelianExtension.lean#L289) | theorem | Actual restriction of abelian sheaves to the slice site is exact. |

## OverSheafCohomology

General cohomological support for the determinant step at P 1434–1443.
This is a constructed library interface, not a proof of the manuscript's
full degree or section-bound argument. The site is small; sheafification and
Ext instances are the standard categorical infrastructure, not geometric inputs.

| Source / mathematical role | Lean declaration | Kind | Exact coverage |
|---|---|---|---|
| Support for P 1434–1443; exact hypotheses in declaration | [`freeAbelianSheafEvaluation`](Normalizer/OverSheafCohomology.lean#L20) | def | The actual sheafified free representable corepresents evaluation of abelian sheaves at the specified object. |
| Support for P 1434–1443; exact hypotheses in declaration | [`freeAbelianSheafEvaluation_apply`](Normalizer/OverSheafCohomology.lean#L33) | theorem | Evaluation of a morphism out of the represented abelian sheaf is its value on the sheafified identity generator. |
| Support for P 1434–1443; exact hypotheses in declaration | [`extendedIntegerSheafEvaluation`](Normalizer/OverSheafCohomology.lean#L45) | def | Extending the constant integer sheaf from the slice corepresents the same evaluation functor, using the actual restriction adjunction. |
| Support for P 1434–1443; exact hypotheses in declaration | [`overAbelianExtensionIntegerIso`](Normalizer/OverSheafCohomology.lean#L61) | def | The extension of the actual constant integer sheaf is canonically the actual free abelian sheaf represented by the sliced object. |
| Support for P 1434–1443; exact hypotheses in declaration | [`overAbelianExtensionIntegerIso_evaluation`](Normalizer/OverSheafCohomology.lean#L69) | theorem | The canonical comparison of representing objects preserves evaluation on the distinguished generator. |
| Support for P 1434–1443; exact hypotheses in declaration | [`overSheafCohomologyEquiv`](Normalizer/OverSheafCohomology.lean#L98) | def | Evaluation of the actual cohomology presheaf at an object agrees, in every degree, with intrinsic cohomology of the actual restricted sheaf. |
| Support for P 1434–1443; exact hypotheses in declaration | [`overSheafCohomologyEquiv_naturality`](Normalizer/OverSheafCohomology.lean#L105) | theorem | The slice cohomology comparison commutes with maps of actual sheaves. |
| Support for P 1434–1443; exact hypotheses in declaration | [`overSheafCohomologyEquiv_equiv₀`](Normalizer/OverSheafCohomology.lean#L119) | theorem | In degree zero the slice comparison gives the actual section obtained by evaluating on the sheafified identity generator at the sliced object. |

## AffinePrincipalLocalization

Localization lemmas used in the affine H¹ proof, supporting the determinant
step at P 1434–1443. These concern the actual principal-open restrictions.

| Source / mathematical role | Lean declaration | Kind | Exact coverage |
|---|---|---|---|
| Degree-one affine support for P 1434–1443 | [`localizedModuleAway_cancel_left`](Normalizer/AffinePrincipalLocalization.lean#L15) | theorem | Compatible localization maps M to N at a and M to P at a*b force N to P to be localization at b; both denominator lifting and annihilator conditions are proved. |
| Degree-one affine support for P 1434–1443 | [`localizingSheaf_principalRestriction`](Normalizer/AffinePrincipalLocalization.lean#L65) | theorem | For a localizing R-module sheaf on Spec R, the actual D(a)-to-D(a)-intersect-D(b) restriction localizes at b. |
| Degree-one affine support for P 1434–1443 | [`tilde_principalRestriction`](Normalizer/AffinePrincipalLocalization.lean#L87) | theorem | The actual associated sheaf satisfies the principal-restriction localization theorem without a supplied localization premise. |

## AffineCechOne

The degree-one standard-cover instance of
[Stacks 30.2.1](https://stacks.math.columbia.edu/tag/01X9), proved here by
denominator clearing on actual sections. Higher degrees are not claimed.

| Source / mathematical role | Lean declaration | Kind | Exact coverage |
|---|---|---|---|
| Degree-one affine support for P 1434–1443 | [`affineModuleRestrict`](Normalizer/AffineCechOne.lean#L16) | abbrev | The actual restriction in an R-module sheaf, retained as an R-linear map. |
| Degree-one affine support for P 1434–1443 | [`affineModuleRestrict_comp`](Normalizer/AffineCechOne.lean#L22) | theorem | Composing actual R-linear restrictions agrees with restriction along the composite inclusion. |
| Degree-one affine support for P 1434–1443 | [`localizingSheaf_cechOne_eq_coboundary`](Normalizer/AffineCechOne.lean#L35) | theorem | Every degree-one cocycle of actual sections on a finite principal affine cover of a localizing module sheaf is a coboundary. Two denominator clearings and a partition of unity construct the correction. |
| Degree-one affine support for P 1434–1443 | [`tilde_cechOne_eq_coboundary`](Normalizer/AffineCechOne.lean#L127) | theorem | The finite-principal-cover cocycle result for the actual associated sheaf of any module over any commutative ring. |

## AffineSheafLifting

The gluing step supporting P 1434–1443. Local lifts in arbitrary abelian
sheaves are corrected using the proved finite-cover cocycle theorem.

| Source / mathematical role | Lean declaration | Kind | Exact coverage |
|---|---|---|---|
| Degree-one affine support for P 1434–1443 | [`affineModuleAbelianSheaf`](Normalizer/AffineSheafLifting.lean#L17) | def | The standard scalar-forgetting functor applied to an actual R-module sheaf on Spec R. |
| Degree-one affine support for P 1434–1443 | [`affineSheaf_epi_finitePrincipal_lifts`](Normalizer/AffineSheafLifting.lean#L24) | theorem | Local surjectivity of an abelian-sheaf epimorphism and compactness of Spec R construct a finite principal cover with actual lifts of the specified global section. |
| Degree-one affine support for P 1434–1443 | [`abelianSheaf_shortExact_sections_exact`](Normalizer/AffineSheafLifting.lean#L61) | theorem | An actual short exact sequence of abelian sheaves is exact on sections at its middle term on every open, using preservation of kernels by evaluation. |
| Degree-one affine support for P 1434–1443 | [`localizingSheaf_extension_globalSections_surjective`](Normalizer/AffineSheafLifting.lean#L105) | theorem | Every quotient global section lifts in an arbitrary abelian-sheaf extension with a localizing module sheaf as kernel. The difference cocycle and corrected gluing are constructed. |

## AffineH1Vanishing

The degree-one Spec R instance of
[Stacks 30.2.2](https://stacks.math.columbia.edu/tag/01XB), using an actual
injective presentation. This supports P 1434–1443; the all-degree theorem,
proper-curve finiteness and the determinant conclusion remain separate.

| Source / mathematical role | Lean declaration | Kind | Exact coverage |
|---|---|---|---|
| Degree-one affine support for P 1434–1443 | [`localizingSheaf_H1_subsingleton`](Normalizer/AffineH1Vanishing.lean#L18) | theorem | The actual Ext-defined first cohomology of a localizing module sheaf vanishes, using the proved lifting theorem on its canonical injective presentation. |
| Degree-one affine support for P 1434–1443 | [`tilde_H1_subsingleton`](Normalizer/AffineH1Vanishing.lean#L43) | theorem | Actual H¹(Spec R, tilde M) is zero for every commutative ring and every module. No noetherian, finite-generation, characteristic or acyclicity hypothesis. |
| Degree-one affine support for P 1434–1443 | [`tilde_H1_eq_zero`](Normalizer/AffineH1Vanishing.lean#L51) | theorem | Every element of the actual first cohomology of the associated sheaf is zero. |
| Degree-one affine support for P 1434–1443 | [`quasicoherent_Spec_H1_subsingleton`](Normalizer/AffineH1Vanishing.lean#L59) | theorem | Actual H¹ of every quasicoherent module sheaf on Spec R is zero. The localization input is derived from mathlib quasicoherence, not supplied separately. |

## OpenSheafCohomology

Support for the determinant degree argument in P 1434–1443. These are
cohomological constructions, not the manuscript degree conclusion.

| Source / mathematical role | Lean declaration | Kind | Exact coverage |
|---|---|---|---|
| Actual-open cohomology support for P 1434–1443 | [`openOverInverseSectionsIso`](Normalizer/OpenSheafCohomology.lean#L23) | def | Global sections commute with the inverse of the actual open-site equivalence. |
| Actual-open cohomology support for P 1434–1443 | [`openOverConstantIso`](Normalizer/OpenSheafCohomology.lean#L34) | def | The actual open-site equivalence transports constant sheaves, by the evaluation adjunctions. |
| Actual-open cohomology support for P 1434–1443 | [`openOverCohomologyEquiv`](Normalizer/OpenSheafCohomology.lean#L50) | def | All-degree cohomology comparison from the small slice site to the actual open subspace. |
| Actual-open cohomology support for P 1434–1443 | [`openOverCohomologyEquiv_naturality`](Normalizer/OpenSheafCohomology.lean#L63) | theorem | The open-site comparison commutes with every actual abelian-sheaf morphism. |
| Actual-open cohomology support for P 1434–1443 | [`openSheafCohomologyEquiv`](Normalizer/OpenSheafCohomology.lean#L87) | def | All-degree comparison of ambient-open cohomology-presheaf evaluation with actual topological open restriction. |
| Actual-open cohomology support for P 1434–1443 | [`openSheafCohomologyEquiv_naturality`](Normalizer/OpenSheafCohomology.lean#L94) | theorem | The ambient-open comparison is natural in the original abelian sheaf. |

## SchemeOpenCohomology

The actual scheme restriction, affine-coordinate transport and scalar
compatibility complete the degree-one affine-open input.

| Source / mathematical role | Lean declaration | Kind | Exact coverage |
|---|---|---|---|
| Actual-open cohomology support for P 1434–1443 | [`schemeOpenAbelianRestrictionIso`](Normalizer/SchemeOpenCohomology.lean#L16) | def | Forgetting the module structure commutes with actual scheme open restriction. |
| Actual-open cohomology support for P 1434–1443 | [`schemeOpenCohomologyEquiv`](Normalizer/SchemeOpenCohomology.lean#L23) | def | Actual module restriction to the open subscheme gives the ambient-open cohomology comparison in every degree. |
| Actual-open cohomology support for P 1434–1443 | [`schemeOpenCohomologyEquiv_apply`](Normalizer/SchemeOpenCohomology.lean#L31) | theorem | The module comparison agrees with the actual abelian open comparison on cohomology classes. |
| Actual-open cohomology support for P 1434–1443 | [`schemeIsoRestriction_unit_isIso`](Normalizer/SchemeOpenCohomology.lean#L39) | theorem | The canonical restriction/direct-image adjunction unit is an isomorphism along a scheme isomorphism. |
| Actual-open cohomology support for P 1434–1443 | [`quasicoherent_affine_H1_subsingleton`](Normalizer/SchemeOpenCohomology.lean#L56) | theorem | Actual H1 vanishes for every quasicoherent module sheaf on any affine scheme, via its canonical Spec coordinate isomorphism. |
| Actual-open cohomology support for P 1434–1443 | [`quasicoherent_affineOpen_H1_subsingleton`](Normalizer/SchemeOpenCohomology.lean#L72) | theorem | Actual ambient H-prime in degree one vanishes on every affine open for a quasicoherent module sheaf on the ambient scheme. |
| Actual-open cohomology support for P 1434–1443 | [`schemeConstantAt_open`](Normalizer/SchemeOpenCohomology.lean#L81) | theorem | The composite structure morphism on an actual open subscheme gives precisely the restricted ambient base constants. |
| Actual-open cohomology support for P 1434–1443 | [`schemeModuleScalarEnd_open`](Normalizer/SchemeOpenCohomology.lean#L90) | theorem | Scalar endomorphisms commute with the actual open restriction functor. |
| Actual-open cohomology support for P 1434–1443 | [`schemeModuleOpenCohomologyModule`](Normalizer/SchemeOpenCohomology.lean#L105) | def | The ambient-open cohomology module action is constructed directly from actual scalar endomorphisms, independently of the comparison. |
| Actual-open cohomology support for P 1434–1443 | [`schemeModuleOpenCohomology_smul`](Normalizer/SchemeOpenCohomology.lean#L131) | theorem | The ambient-open scalar action is exactly the map induced on the actual cohomology presheaf. |
| Actual-open cohomology support for P 1434–1443 | [`schemeOpenCohomologyLinearEquiv`](Normalizer/SchemeOpenCohomology.lean#L141) | def | The actual geometric open comparison is linear for the independently constructed structure-morphism scalar actions. |

## TwoAffineCohomology

For a supplied two-affine cover, the actual Mayer-Vietoris sequence
constructs the global H1 quotient. Its finite dimension remains unproved.

| Source / mathematical role | Lean declaration | Kind | Exact coverage |
|---|---|---|---|
| Actual-open cohomology support for P 1434–1443 | [`twoOpenCoverSquare`](Normalizer/TwoAffineCohomology.lean#L18) | def | The actual two-open cover determines its Mayer-Vietoris square with ambient top as the final corner. |
| Actual-open cohomology support for P 1434–1443 | [`twoOpenCohomologyδ`](Normalizer/TwoAffineCohomology.lean#L27) | def | The original Mayer-Vietoris boundary is transported to actual global H1 by the natural terminal comparison. |
| Actual-open cohomology support for P 1434–1443 | [`quasicoherent_twoAffine_δ_surjective`](Normalizer/TwoAffineCohomology.lean#L35) | theorem | For a supplied actual two-affine cover and quasicoherent module sheaf, the original boundary onto global H1 is surjective; both local vanishings are derived. |
| Actual-open cohomology support for P 1434–1443 | [`twoOpenCohomologyδ_eq_zero_iff`](Normalizer/TwoAffineCohomology.lean#L61) | theorem | The kernel of the actual boundary consists exactly of differences of degree-zero restrictions; no affine or finiteness condition is needed for exactness. |
| Actual-open cohomology support for P 1434–1443 | [`twoOpenCohomologyδLinear`](Normalizer/TwoAffineCohomology.lean#L85) | def | The original two-open boundary is linear for the actual structure-morphism scalar actions. |
| Actual-open cohomology support for P 1434–1443 | [`twoAffineH1QuotientEquiv`](Normalizer/TwoAffineCohomology.lean#L109) | def | A supplied actual two-affine cover gives a linear quotient presentation of global H1. The kernel is identified with restriction differences above. The cover is not constructed and quotient finiteness is not asserted. |

## CurveFiniteMap

Support for the determinant degree step in P 1434–1443.
The last theorem is the integral, nonconstant specialization of
[Stacks Lemma 53.2.4](https://stacks.math.columbia.edu/tag/0CCL).
This module does not assert proper-curve H1 finiteness or the degree conclusion.

| Source / mathematical role | Lean declaration | Kind | Exact coverage |
|---|---|---|---|
| Finite-map route support for P 1434–1443 | [`curve_closedPoint_of_ne_generic`](Normalizer/CurveFiniteMap.lean#L29) | theorem | Every nongeneric point of a sober irreducible T0 space of dimension at most one is closed. |
| Finite-map route support for P 1434–1443 | [`noetherian_dimZero_finite`](Normalizer/CurveFiniteMap.lean#L46) | theorem | A Noetherian T0 space of dimension at most zero has finitely many points, via its finitely many irreducible components. |
| Finite-map route support for P 1434–1443 | [`curve_properClosedSubset_finite`](Normalizer/CurveFiniteMap.lean#L64) | theorem | A closed subset different from the whole Noetherian irreducible T0 curve is finite. |
| Finite-map route support for P 1434–1443 | [`curve_closedMap_fibres_finite`](Normalizer/CurveFiniteMap.lean#L78) | theorem | A nonconstant continuous closed map from a Noetherian sober irreducible curve has finite fibres, including fibres over nonclosed points. |
| Finite-map route support for P 1434–1443 | [`curve_nonconstant_proper_isFinite`](Normalizer/CurveFiniteMap.lean#L103) | theorem | A nonconstant proper morphism from an integral Noetherian scheme of dimension at most one is finite; the fibre condition is derived. |
| Integral case of Stacks 53.2.4; support for P 1434–1443 | [`properCurve_nonconstant_map_isFinite`](Normalizer/CurveFiniteMap.lean#L114) | theorem | For a given nonconstant morphism from a proper integral curve over a field to a separated scheme over that field, derive Noetherianity and properness and prove the morphism finite. This does not construct the morphism. |

## LaurentCechFinite

Support for the determinant degree step in P 1434–1443.
This is the algebraic finite-window argument for a proposed two-chart route.
This module does not assert proper-curve H1 finiteness or the degree conclusion.

| Source / mathematical role | Lean declaration | Kind | Exact coverage |
|---|---|---|---|
| Finite-map route support for P 1434–1443 | [`laurentSpan`](Normalizer/LaurentCechFinite.lean#L18) | def | The coefficient-ring span of the specified integer Laurent translates of a family. |
| Finite-map route support for P 1434–1443 | [`laurentSpan_generator`](Normalizer/LaurentCechFinite.lean#L22) | theorem | Each indicated translate belongs to the defined coefficient-ring span. |
| Finite-map route support for P 1434–1443 | [`laurentSpan_univ`](Normalizer/LaurentCechFinite.lean#L35) | theorem | The span of all integer translates equals restriction of scalars of the original Laurent-ring span. |
| Finite-map route support for P 1434–1443 | [`laurent_span_eventually_nonpositive`](Normalizer/LaurentCechFinite.lean#L68) | theorem | Every element in a Laurent-ring span has all sufficiently negative translates in the nonpositive-power span of the given family. |
| Finite-map route support for P 1434–1443 | [`laurent_twoChart_window`](Normalizer/LaurentCechFinite.lean#L98) | theorem | Finite Laurent generators, nonnegative-power containment and a uniform negative-tail bound construct an explicit finite interval of translates spanning the quotient. |
| Finite-map route support for P 1434–1443 | [`laurent_twoChart_quotient_finite`](Normalizer/LaurentCechFinite.lean#L132) | theorem | Two families generating the same Laurent module, with the first family finite, give a quotient finite over the coefficient ring by their nonnegative and nonpositive power spans. No quotient finiteness is assumed. |

## CurveRationalExtension

The normal-curve extension step of [Stacks Lemma 53.2.2](https://stacks.math.columbia.edu/tag/0BXZ). The source is integral and locally Noetherian of dimension at most one, with integrally closed actual stalks. Local valuation lifts, neighbourhood representatives and the unique global map are constructed. This does not extend arbitrary rational functions on singular curves.

These are supporting results for the determinant degree step at P 1434–1443, not a proof of that manuscript step.

| Source / mathematical role | Lean declaration | Kind | Exact coverage |
|---|---|---|---|
| Stacks 53.2.2 extension support; P 1434–1443 | [`normalCurve_stalk_valuationRing`](Normalizer/CurveRationalExtension.lean#L19) | theorem | A Noetherian integral scheme of dimension at most one has valuation local rings at every point where its actual stalk is integrally closed. This includes the generic field stalk. |
| Stacks 53.2.2 extension support; P 1434–1443 | [`partialMap_genericRestriction_eq_stalkRestriction`](Normalizer/CurveRationalExtension.lean#L35) | theorem | Restricting a partial map to the generic point agrees with first restricting to an actual stalk and then to its fraction field. |
| Stacks 53.2.2 extension support; P 1434–1443 | [`genericMap_lift_to_valuationStalk`](Normalizer/CurveRationalExtension.lean#L47) | theorem | Properness extends an actual generic map to any valuation stalk. The source, fraction field, structural square and its lift are constructed. |
| Stacks 53.2.2 extension support; P 1434–1443 | [`genericMap_mem_domain_of_valuationStalk`](Normalizer/CurveRationalExtension.lean#L80) | theorem | The rational map supplied by an actual generic map is defined at every valuation stalk of the source. The local representative is spread out from the valuative lift, and agreement at the generic point is proved. |
| Stacks 53.2.2 extension support; P 1434–1443 | [`rationalMap_exists_hom_of_domain_eq_top`](Normalizer/CurveRationalExtension.lean#L99) | theorem | A rational map defined everywhere on a reduced source, with separated target, is represented by an actual global morphism. |
| Stacks 53.2.2 extension support; P 1434–1443 | [`schemeHom_eq_of_genericRestriction`](Normalizer/CurveRationalExtension.lean#L116) | theorem | Two morphisms from an integral scheme to a separated scheme agreeing on the actual generic field are equal. |
| Stacks 53.2.2 extension support; P 1434–1443 | [`valuationStalks_genericMap_existsUnique`](Normalizer/CurveRationalExtension.lean#L132) | theorem | On an integral scheme with valuation stalks, any generic map to a proper target extends uniquely to an actual morphism over the base. Local lifts and spreading out prove that its rational-map domain is all X. |
| Stacks 53.2.2 extension support; P 1434–1443 | [`normalCurve_genericMap_existsUnique`](Normalizer/CurveRationalExtension.lean#L162) | theorem | Normal integral curves have unique extensions of generic maps into proper targets. The valuation property is derived from Noetherianity, dimension at most one and integral closedness of the actual stalks. |

## ProjectiveLine

The actual projective line is Proj of the standard grading on k[X0,X1]. Its degree-zero ring, structure map, properness, two affine charts and cover are constructed. The map [1:t] from an actual global section preserves the base morphism and has the stated chart pullbacks. The polynomial and Laurent identifications are supplied by the later ProjectiveCoordinates module.

These are supporting results for the determinant degree step at P 1434–1443, not a proof of that manuscript step.

| Source / mathematical role | Lean declaration | Kind | Exact coverage |
|---|---|---|---|
| Actual chart/cohomology support for P 1434–1443 | [`projectiveLine`](Normalizer/ProjectiveLine.lean#L17) | def | The projective line is the actual Proj scheme of the standard graded polynomial ring in two variables. |
| Actual chart/cohomology support for P 1434–1443 | [`projectiveLineZeroConstants`](Normalizer/ProjectiveLine.lean#L21) | def | Constants identify the coefficient ring with the degree-zero ring of the standard homogeneous polynomial grading. |
| Actual chart/cohomology support for P 1434–1443 | [`projectiveLineZeroConstants_bijective`](Normalizer/ProjectiveLine.lean#L30) | theorem | The actual constants map to degree zero is bijective. |
| Actual chart/cohomology support for P 1434–1443 | [`projectiveLineZeroEquiv`](Normalizer/ProjectiveLine.lean#L41) | def | The canonical isomorphism from constants to the actual degree-zero ring. |
| Actual chart/cohomology support for P 1434–1443 | [`projectiveLineToSpec`](Normalizer/ProjectiveLine.lean#L45) | def | The structure morphism of the actual Proj model over its coefficient ring. |
| Actual chart/cohomology support for P 1434–1443 | [`projectiveLineChart`](Normalizer/ProjectiveLine.lean#L50) | def | The standard homogeneous-coordinate open D₊(X_i). |
| Actual chart/cohomology support for P 1434–1443 | [`projectiveLineChart_isAffine`](Normalizer/ProjectiveLine.lean#L54) | theorem | Each standard coordinate open of the actual projective line is affine. |
| Actual chart/cohomology support for P 1434–1443 | [`projectiveLine_adjoin_variables`](Normalizer/ProjectiveLine.lean#L59) | theorem | The two variables generate the graded polynomial algebra over its actual degree-zero ring. |
| Actual chart/cohomology support for P 1434–1443 | [`projectiveLine_finiteType`](Normalizer/ProjectiveLine.lean#L72) | theorem | Finite type over degree zero, with the two homogeneous variables as generators. |
| Actual chart/cohomology support for P 1434–1443 | [`projectiveLineToSpec_isProper`](Normalizer/ProjectiveLine.lean#L80) | theorem | The structure map of the actual projective line is proper. |
| Actual chart/cohomology support for P 1434–1443 | [`projectiveLineChart_cover`](Normalizer/ProjectiveLine.lean#L88) | theorem | The two standard affine opens cover the actual projective line. |
| Actual chart/cohomology support for P 1434–1443 | [`projectiveLineChartIsoSpec`](Normalizer/ProjectiveLine.lean#L93) | def | The actual standard chart has the homogeneous-localization coordinate ring. |
| Actual chart/cohomology support for P 1434–1443 | [`projectiveLineSectionEval`](Normalizer/ProjectiveLine.lean#L103) | def | Homogeneous coordinates `[1:t]`, evaluated in the actual global sections of a scheme over the coefficient ring. |
| Actual chart/cohomology support for P 1434–1443 | [`projectiveLineSectionEval_irrelevant`](Normalizer/ProjectiveLine.lean#L109) | theorem | The coordinate `X₀` maps to one, so the evaluated irrelevant ideal is the unit ideal. |
| Actual chart/cohomology support for P 1434–1443 | [`projectiveLineOfSection`](Normalizer/ProjectiveLine.lean#L120) | def | The actual morphism to Proj defined by the coordinates `[1:t]`. |
| Actual chart/cohomology support for P 1434–1443 | [`projectiveLineOfSection_comp`](Normalizer/ProjectiveLine.lean#L126) | theorem | The section-defined projective-line morphism is over the original base. |
| Actual chart/cohomology support for P 1434–1443 | [`projectiveLineOfSection_preimage_zero`](Normalizer/ProjectiveLine.lean#L143) | theorem | The zero-coordinate chart contains the whole image of `[1:t]`. |
| Actual chart/cohomology support for P 1434–1443 | [`projectiveLineOfSection_preimage_one`](Normalizer/ProjectiveLine.lean#L151) | theorem | The other standard chart pulls back to the invertibility locus of the specified section. |

## TwoAffineSections

For an actual two-affine cover, this identifies actual first cohomology with the quotient of actual overlap sections. Field actions and restriction compatibility are proved. The boundary kernel is exactly the differences of actual restrictions. No finite dimension is concluded.

These are supporting results for the determinant degree step at P 1434–1443, not a proof of that manuscript step.

| Source / mathematical role | Lean declaration | Kind | Exact coverage |
|---|---|---|---|
| Actual chart/cohomology support for P 1434–1443 | [`schemeOpenSectionsModule`](Normalizer/TwoAffineSections.lean#L16) | def | The actual module of sections on an open, with scalars from the base field. |
| Actual chart/cohomology support for P 1434–1443 | [`schemeModuleOpenCohomologyEquiv₀`](Normalizer/TwoAffineSections.lean#L21) | def | Degree-zero cohomology of an actual open is its actual section module, with the base-field action on both sides proved compatible. |
| Actual chart/cohomology support for P 1434–1443 | [`schemeModuleOpenCohomologyEquiv₀_apply`](Normalizer/TwoAffineSections.lean#L52) | theorem | The comparison evaluates the cohomology class on the actual identity generator. |
| Actual chart/cohomology support for P 1434–1443 | [`schemeModuleOpenCohomologyEquiv₀_restrict`](Normalizer/TwoAffineSections.lean#L63) | theorem | The degree-zero comparison commutes with the actual open restriction map. |
| Actual chart/cohomology support for P 1434–1443 | [`twoOpenSectionδ`](Normalizer/TwoAffineSections.lean#L99) | def | The actual section boundary on the overlap, with the original Mayer-Vietoris connecting map and its structure-field action. |
| Actual chart/cohomology support for P 1434–1443 | [`twoOpenSectionδ_surjective`](Normalizer/TwoAffineSections.lean#L111) | theorem | The actual section boundary is onto on a two-affine cover of a quasicoherent sheaf; the local vanishing is derived. |
| Actual chart/cohomology support for P 1434–1443 | [`twoOpenSectionδ_eq_zero_iff`](Normalizer/TwoAffineSections.lean#L118) | theorem | A section on the overlap has zero boundary exactly when it is a difference of actual sections restricted from the two opens. |
| Actual chart/cohomology support for P 1434–1443 | [`twoAffineSectionH1QuotientEquiv`](Normalizer/TwoAffineSections.lean#L166) | def | First cohomology is the quotient of actual overlap sections by the kernel proved above to be precisely actual restriction differences. |

## CurveProjectiveLine

A specified element of the generic stalk constructs a unique actual map from a normal curve to the actual projective line. Its base and generic restrictions are proved. Finiteness still requires proved nonconstancy. For any finite map to this projective line, actual pullback charts and finite coordinate modules are constructed; for an affine map and quasicoherent sheaf, their section quotient computes actual H1. The final chart constructions require no source integrality or normality.

These are supporting results for the determinant degree step at P 1434–1443, not a proof of that manuscript step.

| Source / mathematical role | Lean declaration | Kind | Exact coverage |
|---|---|---|---|
| Actual chart/cohomology support for P 1434–1443 | [`curveGenericProjectiveLineMap`](Normalizer/CurveProjectiveLine.lean#L20) | def | The actual generic-stalk map with homogeneous coordinates `[1:t]`. |
| Actual chart/cohomology support for P 1434–1443 | [`curveGenericProjectiveLineMap_comp`](Normalizer/CurveProjectiveLine.lean#L26) | theorem | The specified generic map is over the original base field. |
| Actual chart/cohomology support for P 1434–1443 | [`normalCurve_projectiveLine_existsUnique`](Normalizer/CurveProjectiveLine.lean#L33) | theorem | A specified rational function on a normal curve gives a unique actual projective-line morphism with those generic coordinates. |
| Actual chart/cohomology support for P 1434–1443 | [`normalCurveProjectiveLineMap`](Normalizer/CurveProjectiveLine.lean#L44) | def | The projective-line morphism constructed by extension of `[1:t]`. |
| Actual chart/cohomology support for P 1434–1443 | [`normalCurveProjectiveLineMap_comp`](Normalizer/CurveProjectiveLine.lean#L51) | theorem | The constructed morphism respects the original structure map. |
| Actual chart/cohomology support for P 1434–1443 | [`normalCurveProjectiveLineMap_generic`](Normalizer/CurveProjectiveLine.lean#L59) | theorem | The generic restriction is the originally specified `[1:t]` map. |
| Actual chart/cohomology support for P 1434–1443 | [`normalCurveProjectiveLineMap_isFinite_of_nonconstant`](Normalizer/CurveProjectiveLine.lean#L69) | theorem | Nonconstancy of the constructed morphism, when established, makes it finite. The normality input is used only in constructing this particular morphism. |
| Actual chart/cohomology support for P 1434–1443 | [`projectiveLinePullbackChart`](Normalizer/CurveProjectiveLine.lean#L83) | def | The actual inverse image of a standard projective-line chart. |
| Actual chart/cohomology support for P 1434–1443 | [`projectiveLinePullbackChart_cover`](Normalizer/CurveProjectiveLine.lean#L87) | theorem | The two pulled-back coordinate opens cover the source scheme. |
| Actual chart/cohomology support for P 1434–1443 | [`projectiveLinePullbackChart_isAffine`](Normalizer/CurveProjectiveLine.lean#L102) | theorem | Under an affine morphism, in particular a finite one, the actual inverse-image coordinate opens are affine. No normality is needed here. |
| Actual chart/cohomology support for P 1434–1443 | [`projectiveLinePullbackChartAlgebra`](Normalizer/CurveProjectiveLine.lean#L109) | def | The actual coordinate-ring action on the inverse-image chart sections, induced by the original morphism's sheaf map. |
| Actual chart/cohomology support for P 1434–1443 | [`projectiveLinePullbackChart_finite`](Normalizer/CurveProjectiveLine.lean#L116) | theorem | A finite map supplies finite actual chart modules over the corresponding projective-line chart rings. Polynomial-coordinate identification is separate. |
| Actual chart/cohomology support for P 1434–1443 | [`projectiveLineChartSectionH1QuotientEquiv`](Normalizer/CurveProjectiveLine.lean#L126) | def | The actual inverse-image chart section quotient computes actual H¹ for an affine morphism to the projective line. In particular this applies to a finite morphism. No cohomology dimension is supplied or concluded. |

## ProjectiveCoordinates

The dimension-one chart calculation underlying [Stacks Lemma 27.13.3](https://stacks.math.columbia.edu/tag/01NG), constructed here for Proj of k[X0,X1] over any commutative coefficient ring. Both actual chart section rings are polynomial rings; the actual overlap section ring is a Laurent polynomial ring. The actual restrictions are polynomial inclusion and inclusion followed by Laurent inversion. Constants in the homogeneous-localization maps are fixed. These are ring isomorphisms; the later FiniteMapLaurent and FiniteMapH1 modules construct the scalar/localization comparisons for actual pulled-back chart modules.

These support the cohomology route behind P 1434–1443; the manuscript degree step remains unformalized.

| Source / mathematical role | Lean declaration | Kind | Exact coverage |
|---|---|---|---|
| Projective-coordinate support for P 1434–1443 | [`projectiveChartCoordinate`](Normalizer/ProjectiveCoordinates.lean#L17) | def | The actual ratio X_rev(i)/X_i in the standard homogeneous-localization chart. |
| Projective-coordinate support for P 1434–1443 | [`projectiveChartFromPolynomial`](Normalizer/ProjectiveCoordinates.lean#L23) | def | Polynomial evaluation at the actual chart ratio, with actual constant coefficients. |
| Projective-coordinate support for P 1434–1443 | [`projectiveChartPolynomialEval`](Normalizer/ProjectiveCoordinates.lean#L29) | def | Dehomogenization of the homogeneous polynomial ring on the chosen chart. |
| Projective-coordinate support for P 1434–1443 | [`projectiveChartToPolynomial`](Normalizer/ProjectiveCoordinates.lean#L33) | def | The actual chart maps to polynomials by setting its denominator coordinate to one. |
| Projective-coordinate support for P 1434–1443 | [`projectiveChartToPolynomial_mk`](Normalizer/ProjectiveCoordinates.lean#L40) | theorem | A homogeneous fraction p/X_i^n dehomogenizes to p with X_i set to one. |
| Projective-coordinate support for P 1434–1443 | [`projectiveChartToPolynomial_coordinate`](Normalizer/ProjectiveCoordinates.lean#L51) | theorem | The actual coordinate ratio is sent to the polynomial variable. |
| Projective-coordinate support for P 1434–1443 | [`projectiveChartToPolynomial_from_C`](Normalizer/ProjectiveCoordinates.lean#L57) | theorem | The composite chart evaluation fixes every coefficient polynomial. |
| Projective-coordinate support for P 1434–1443 | [`projectiveChartToPolynomial_leftInverse`](Normalizer/ProjectiveCoordinates.lean#L68) | theorem | Dehomogenization is a left inverse of evaluation at the actual chart ratio. |
| Projective-coordinate support for P 1434–1443 | [`projectiveChart_monomial_fraction`](Normalizer/ProjectiveCoordinates.lean#L79) | theorem | Every homogeneous monomial fraction on the chart is a power of its actual ratio. |
| Projective-coordinate support for P 1434–1443 | [`projectiveChartFromPolynomial_surjective`](Normalizer/ProjectiveCoordinates.lean#L96) | theorem | The actual chart ratio generates every homogeneous-localization element as a polynomial. |
| Projective-coordinate support for P 1434–1443 | [`projectiveChartToPolynomial_bijective`](Normalizer/ProjectiveCoordinates.lean#L131) | theorem | Dehomogenization is bijective on the actual chart ring. |
| Projective-coordinate support for P 1434–1443 | [`projectiveChartPolynomialEquiv`](Normalizer/ProjectiveCoordinates.lean#L143) | def | The explicit polynomial coordinate isomorphism on either actual standard chart. |
| Projective-coordinate support for P 1434–1443 | [`projectiveOverlapRing`](Normalizer/ProjectiveCoordinates.lean#L148) | abbrev | The actual homogeneous localization on the intersection of the standard charts. |
| Projective-coordinate support for P 1434–1443 | [`projectiveOverlap_product`](Normalizer/ProjectiveCoordinates.lean#L153) | theorem | The product defining the overlap can be ordered from either chart. |
| Projective-coordinate support for P 1434–1443 | [`projectiveChartToOverlap`](Normalizer/ProjectiveCoordinates.lean#L159) | def | The actual homogeneous-localization restriction from either chart to the overlap. |
| Projective-coordinate support for P 1434–1443 | [`projectiveOverlap_isLocalization`](Normalizer/ProjectiveCoordinates.lean#L165) | theorem | The overlap is the localization of either actual chart at its coordinate ratio. |
| Projective-coordinate support for P 1434–1443 | [`projectiveChartPolynomialEquiv_powers`](Normalizer/ProjectiveCoordinates.lean#L173) | theorem | The chart coordinate isomorphism sends the inverted powers to powers of the polynomial variable. |
| Projective-coordinate support for P 1434–1443 | [`projectiveOverlapLaurentEquiv`](Normalizer/ProjectiveCoordinates.lean#L182) | def | The overlap is the actual Laurent polynomial ring, oriented by X_1/X_0. |
| Projective-coordinate support for P 1434–1443 | [`projectiveOverlapLaurentEquiv_restrict_zero`](Normalizer/ProjectiveCoordinates.lean#L189) | theorem | Restriction from the first chart is the usual inclusion of polynomials into Laurent polynomials. |
| Projective-coordinate support for P 1434–1443 | [`projectiveOverlap_coordinate_mul`](Normalizer/ProjectiveCoordinates.lean#L198) | theorem | The two actual chart ratios multiply to one after restriction to their overlap. |
| Projective-coordinate support for P 1434–1443 | [`projectiveOverlapLaurentEquiv_coordinate_one`](Normalizer/ProjectiveCoordinates.lean#L211) | theorem | The second chart coordinate restricts to the inverse Laurent variable. |
| Projective-coordinate support for P 1434–1443 | [`projectiveChartToOverlap_from_C`](Normalizer/ProjectiveCoordinates.lean#L228) | theorem | Both chart restrictions agree on their actual constant coefficients. |
| Projective-coordinate support for P 1434–1443 | [`projectiveOverlapLaurentEquiv_from_one`](Normalizer/ProjectiveCoordinates.lean#L235) | theorem | Restricting a polynomial from the second chart replaces its variable by the inverse Laurent variable. |
| Projective-coordinate support for P 1434–1443 | [`projectiveOverlapLaurentEquiv_restrict_one`](Normalizer/ProjectiveCoordinates.lean#L256) | theorem | Restriction from the second actual chart is polynomial inclusion followed by Laurent inversion. |
| Projective-coordinate support for P 1434–1443 | [`projectiveLineOverlap`](Normalizer/ProjectiveCoordinates.lean#L267) | def | The actual open underlying the Laurent overlap. |
| Projective-coordinate support for P 1434–1443 | [`projectiveLineOverlap_eq_inf`](Normalizer/ProjectiveCoordinates.lean#L272) | theorem | The Laurent overlap open is the intersection of the two standard chart opens. |
| Projective-coordinate support for P 1434–1443 | [`projectiveLineOverlap_le`](Normalizer/ProjectiveCoordinates.lean#L277) | theorem | The actual overlap inclusion into either standard chart. |
| Projective-coordinate support for P 1434–1443 | [`projectiveLineChartSectionsEquiv`](Normalizer/ProjectiveCoordinates.lean#L282) | def | The actual chart sections are the homogeneous-localization ring. |
| Projective-coordinate support for P 1434–1443 | [`projectiveLineOverlapSectionsEquiv`](Normalizer/ProjectiveCoordinates.lean#L289) | def | The actual overlap sections are the homogeneous localization at X_0 X_1. |
| Projective-coordinate support for P 1434–1443 | [`projectiveLineSections_restrict`](Normalizer/ProjectiveCoordinates.lean#L296) | theorem | Actual sheaf restriction agrees with the homogeneous-localization restriction map. |
| Projective-coordinate support for P 1434–1443 | [`projectiveLineChartSectionsPolynomialEquiv`](Normalizer/ProjectiveCoordinates.lean#L317) | def | Polynomial coordinates on the actual section ring of either chart. |
| Projective-coordinate support for P 1434–1443 | [`projectiveLineOverlapSectionsLaurentEquiv`](Normalizer/ProjectiveCoordinates.lean#L322) | def | Laurent coordinates on the actual section ring of the chart intersection. |
| Projective-coordinate support for P 1434–1443 | [`projectiveLineSections_restrict_zero`](Normalizer/ProjectiveCoordinates.lean#L327) | theorem | In actual section coordinates, the first restriction is the usual polynomial inclusion. |
| Projective-coordinate support for P 1434–1443 | [`projectiveLineSections_restrict_one`](Normalizer/ProjectiveCoordinates.lean#L337) | theorem | In actual section coordinates, the second restriction inverts the Laurent variable. |

## ProjectiveLineCohomology

The n=1, d=0, q=1, field-base special case of [Stacks Lemma 30.8.1](https://stacks.math.columbia.edu/tag/01XS): actual H1(P1_k,O) vanishes. Every actual overlap section is a difference of actual chart sections, so the actual Mayer-Vietoris boundary is both zero and surjective. This is an unconditional cohomology calculation on the actual Proj scheme over a field, not a proper-curve finiteness interface. The coordinate and section-difference calculations work over arbitrary commutative rings. The general structure-sheaf local-freeness lemma is support for quasicoherence.

These support the cohomology route behind P 1434–1443; the manuscript degree step remains unformalized.

| Source / mathematical role | Lean declaration | Kind | Exact coverage |
|---|---|---|---|
| Actual projective-line cohomology support for P 1434–1443 | [`laurentPolynomial_twoChart_difference`](Normalizer/ProjectiveLineCohomology.lean#L16) | theorem | Every Laurent polynomial is a difference of polynomials in the two opposite coordinates. |
| Actual projective-line cohomology support for P 1434–1443 | [`projectiveLineOverlap_sections_difference`](Normalizer/ProjectiveLineCohomology.lean#L31) | theorem | Every actual overlap section is a difference of sections from the two actual charts. |
| Actual projective-line cohomology support for P 1434–1443 | [`schemeUnit_isLocallyFree`](Normalizer/ProjectiveLineCohomology.lean#L47) | theorem | The actual structure sheaf is locally free of rank one, via the one-generator free sheaf. |
| Actual projective-line cohomology support for P 1434–1443 | [`projectiveLineChart_sup`](Normalizer/ProjectiveLineCohomology.lean#L53) | theorem | The standard two-chart cover expressed as a binary union. |
| Actual projective-line cohomology support for P 1434–1443 | [`projectiveLine_unit_H1_subsingleton`](Normalizer/ProjectiveLineCohomology.lean#L64) | theorem | The first cohomology of the actual structure sheaf of the actual Proj projective line vanishes. |
| Actual projective-line cohomology support for P 1434–1443 | [`projectiveLine_unit_H1_finite`](Normalizer/ProjectiveLineCohomology.lean#L94) | theorem | Actual structure-sheaf H¹ on the projective line is finite over the structure field. |

## FiniteChartGeometry

Actual principal-open and localization construction. The invertibility locus of the specified Proj chart ratio is its actual overlap; pullback identifies the source overlap with the principal open of the actual pulled-back ratio. An affine morphism therefore gives the actual ring localization. No source normality or cohomology hypothesis is used.

Supporting construction for the cohomology route behind P 1434–1443; the manuscript degree step remains unformalized.

| Source / mathematical role | Lean declaration | Kind | Exact coverage |
|---|---|---|---|
| Actual finite-map cohomology support for P 1434–1443 | [`projectiveLineChartRatio`](Normalizer/FiniteChartGeometry.lean#L18) | def | The coordinate ratio as an actual section of a projective-line chart. |
| Actual finite-map cohomology support for P 1434–1443 | [`projectiveLineChartRatio_basicOpen`](Normalizer/FiniteChartGeometry.lean#L22) | theorem | The invertibility locus of the actual chart ratio is exactly the chart overlap. |
| Actual finite-map cohomology support for P 1434–1443 | [`finiteMapOverlap`](Normalizer/FiniteChartGeometry.lean#L55) | def | The actual inverse image of the projective overlap. |
| Actual finite-map cohomology support for P 1434–1443 | [`finiteMapOverlap_le`](Normalizer/FiniteChartGeometry.lean#L59) | theorem | The inverse-image overlap lies in either actual inverse-image chart. |
| Actual finite-map cohomology support for P 1434–1443 | [`finiteMapOverlap_eq_basicOpen`](Normalizer/FiniteChartGeometry.lean#L64) | theorem | The pulled-back overlap is the principal open of the pulled-back coordinate ratio. |
| Actual finite-map cohomology support for P 1434–1443 | [`finiteMapChartRestriction`](Normalizer/FiniteChartGeometry.lean#L69) | def | The actual ring restriction from an inverse-image chart to the overlap. |
| Actual finite-map cohomology support for P 1434–1443 | [`finiteMapChartRestriction_isLocalization`](Normalizer/FiniteChartGeometry.lean#L74) | theorem | For an affine morphism, actual overlap restriction is localization at the actual chart ratio. |

## ProjectiveChartScalars

Actual scalar compatibility. The Proj chart structure morphism and homogeneous-localization constants agree; actual polynomial coordinates send the base constants to coefficient polynomials. Constants on inverse-image opens agree with pullback along the original morphism.

Supporting construction for the cohomology route behind P 1434–1443; the manuscript degree step remains unformalized.

| Source / mathematical role | Lean declaration | Kind | Exact coverage |
|---|---|---|---|
| Actual finite-map cohomology support for P 1434–1443 | [`projectiveLineChart_structure`](Normalizer/ProjectiveChartScalars.lean#L16) | theorem | The structure morphism on a standard chart is induced by the actual constant-coefficient map. |
| Actual finite-map cohomology support for P 1434–1443 | [`projectiveLineChart_constant`](Normalizer/ProjectiveChartScalars.lean#L27) | theorem | Actual base-field constants on a chart are the constants of its homogeneous-localization ring. |
| Actual finite-map cohomology support for P 1434–1443 | [`projectiveLineChart_polynomial_constant`](Normalizer/ProjectiveChartScalars.lean#L50) | theorem | In actual polynomial chart coordinates, constants from the structure morphism are coefficient polynomials. |
| Actual finite-map cohomology support for P 1434–1443 | [`schemeConstantAt_comp`](Normalizer/ProjectiveChartScalars.lean#L61) | theorem | Base constants on actual inverse-image opens agree with pullback of the original constants. |

## LaurentChartModules

Module support for the two-affine cohomology calculation. Actual denominator identities promote images of chart generators to generators over the Laurent ring. A specified polynomial scalar map identifies the restriction range with the coefficient span of oriented powers. A surjective coefficient-linear boundary killed by the two tails has finite target, via the proved Laurent quotient theorem. These are explicit module identities, not existence of geometric data.

Supporting construction for the cohomology route behind P 1434–1443; the manuscript degree step remains unformalized.

| Source / mathematical role | Lean declaration | Kind | Exact coverage |
|---|---|---|---|
| Actual finite-map cohomology support for P 1434–1443 | [`laurentChart_image_mem_span`](Normalizer/LaurentChartModules.lean#L21) | theorem | Images of chart generators span every restricted chart section over the Laurent ring. |
| Actual finite-map cohomology support for P 1434–1443 | [`laurentChart_span_eq_top`](Normalizer/LaurentChartModules.lean#L35) | theorem | Clearing a Laurent-power denominator proves the images of chart generators span the whole overlap. |
| Actual finite-map cohomology support for P 1434–1443 | [`laurentChart_range_eq_span`](Normalizer/LaurentChartModules.lean#L50) | theorem | A chart restriction image is exactly the coefficient span of its generator translates, when the chart scalars have the stated polynomial coordinate. |
| Actual finite-map cohomology support for P 1434–1443 | [`laurentChart_boundary_finite`](Normalizer/LaurentChartModules.lean#L105) | theorem | A surjective coefficient-linear boundary killed by the two Laurent tails has finite target. |

## FiniteMapLaurent

Constructed geometric instantiation of those module identities. The actual Laurent action uses the original f.app; Laurent constants equal constants from the composed structure morphism. Actual restriction is semilinear, and actual localization clears denominators by powers of the oriented Laurent coordinate.

Supporting construction for the cohomology route behind P 1434–1443; the manuscript degree step remains unformalized.

| Source / mathematical role | Lean declaration | Kind | Exact coverage |
|---|---|---|---|
| Actual finite-map cohomology support for P 1434–1443 | [`projectiveChartExponent`](Normalizer/FiniteMapLaurent.lean#L17) | def | The two projective coordinates have Laurent exponents 1 and -1. |
| Actual finite-map cohomology support for P 1434–1443 | [`projectiveChartLaurentHom`](Normalizer/FiniteMapLaurent.lean#L20) | def | Actual chart restriction expressed in the overlap's Laurent coordinates. |
| Actual finite-map cohomology support for P 1434–1443 | [`projectiveChartLaurentHom_eval`](Normalizer/FiniteMapLaurent.lean#L26) | theorem | The actual Laurent-coordinate restriction is evaluation in the appropriate oriented variable. |
| Actual finite-map cohomology support for P 1434–1443 | [`projectiveChartLaurentHom_ratio`](Normalizer/FiniteMapLaurent.lean#L47) | theorem | The actual ratio restricts to its oriented Laurent monomial. |
| Actual finite-map cohomology support for P 1434–1443 | [`projectiveLineOverlap_laurent_constant`](Normalizer/FiniteMapLaurent.lean#L60) | theorem | Constants of the actual overlap agree with coefficients in its Laurent coordinates. |
| Actual finite-map cohomology support for P 1434–1443 | [`finiteMapLaurentHom`](Normalizer/FiniteMapLaurent.lean#L71) | def | The Laurent ring acts on actual overlap sections by the original morphism's sheaf map. |
| Actual finite-map cohomology support for P 1434–1443 | [`finiteMapLaurentAlgebra`](Normalizer/FiniteMapLaurent.lean#L77) | def | The actual Laurent-ring algebra structure on overlap sections. |
| Actual finite-map cohomology support for P 1434–1443 | [`finiteMapOverlapFieldAlgebra`](Normalizer/FiniteMapLaurent.lean#L82) | def | The actual coefficient-field algebra structure on overlap sections. |
| Actual finite-map cohomology support for P 1434–1443 | [`finiteMapLaurentHom_C`](Normalizer/FiniteMapLaurent.lean#L86) | theorem | Laurent constants pull back to precisely the constants of the original structure morphism. |
| Actual finite-map cohomology support for P 1434–1443 | [`finiteMapOverlap_scalarTower`](Normalizer/FiniteMapLaurent.lean#L98) | theorem | The overlap's two actual scalar actions form a scalar tower. |
| Actual finite-map cohomology support for P 1434–1443 | [`finiteMapChartAlgebra`](Normalizer/FiniteMapLaurent.lean#L110) | def | The actual chart-ring action on inverse-image chart sections. |
| Actual finite-map cohomology support for P 1434–1443 | [`finiteMapChartSemilinear`](Normalizer/FiniteMapLaurent.lean#L115) | def | Actual restriction is semilinear for the actual chart-to-Laurent scalar map. |
| Actual finite-map cohomology support for P 1434–1443 | [`finiteMapOverlap_clearDenominator`](Normalizer/FiniteMapLaurent.lean#L137) | theorem | Actual localization clears denominators by a power of the corresponding Laurent monomial. |

## FiniteMapH1

Actual H1(X,O_X) finiteness for any finite f:X -> P1_k, over every field k. This is a special case of [Stacks Lemma 30.19.2](https://stacks.math.columbia.edu/tag/02O6), proved here through actual two-affine sections and the Laurent quotient, without importing the general coherent higher-direct-image theorem. The source need not be integral, normal, smooth or reduced. A proper-integral-curve corollary derives finiteness of a supplied nonconstant P1 map by the existing [Stacks 53.2.4](https://stacks.math.columbia.edu/tag/0CCL) specialization, and then proves actual H1 finite. Map existence remains separate.

Supporting construction for the cohomology route behind P 1434–1443; the manuscript degree step remains unformalized.

| Source / mathematical role | Lean declaration | Kind | Exact coverage |
|---|---|---|---|
| Actual finite-map cohomology support for P 1434–1443 | [`schemeUnitBoundaryOnOverlap`](Normalizer/FiniteMapH1.lean#L17) | def | The actual section boundary on any open equal to the intersection of a two-open cover. |
| Actual finite-map cohomology support for P 1434–1443 | [`schemeUnitBoundaryOnOverlap_surjective`](Normalizer/FiniteMapH1.lean#L27) | theorem | The actual boundary on the specified overlap is onto for an affine cover. |
| Actual finite-map cohomology support for P 1434–1443 | [`schemeUnitBoundaryOnOverlap_eq_zero_iff`](Normalizer/FiniteMapH1.lean#L36) | theorem | The original boundary kernel consists exactly of actual restriction differences. |
| Actual finite-map cohomology support for P 1434–1443 | [`finiteMapOverlap_eq_inf`](Normalizer/FiniteMapH1.lean#L49) | theorem | The actual pulled-back overlap is the intersection used by the cohomology boundary. |
| Actual finite-map cohomology support for P 1434–1443 | [`finiteMapChart_module_finite`](Normalizer/FiniteMapH1.lean#L55) | theorem | Finite morphisms give finite actual chart modules, with the original sheaf-map action. |
| Actual finite-map cohomology support for P 1434–1443 | [`finiteMapChart_generators_span`](Normalizer/FiniteMapH1.lean#L62) | theorem | Images of actual chart generators generate the actual overlap over the Laurent ring. |
| Actual finite-map cohomology support for P 1434–1443 | [`finiteMapChart_restriction_image`](Normalizer/FiniteMapH1.lean#L76) | theorem | Each actual chart restriction image equals the coefficient span of the corresponding oriented Laurent powers of its restricted generators. |
| Actual finite-map cohomology support for P 1434–1443 | [`projectiveChartExponent_range_zero`](Normalizer/FiniteMapH1.lean#L95) | theorem | The first chart's oriented exponents are precisely the nonnegative integers. |
| Actual finite-map cohomology support for P 1434–1443 | [`projectiveChartExponent_range_one`](Normalizer/FiniteMapH1.lean#L104) | theorem | The second chart's oriented exponents are precisely the nonpositive integers. |
| Actual finite-map cohomology support for P 1434–1443 | [`finiteMap_projectiveLine_unit_H1_finite`](Normalizer/FiniteMapH1.lean#L115) | theorem | For any actual finite morphism to P1, actual structure-sheaf H1 is finite over the original field. |
| Actual finite-map cohomology support for P 1434–1443 | [`properCurve_unit_H1_finite_of_projectiveMap`](Normalizer/FiniteMapH1.lean#L164) | theorem | A nonconstant projective-line map on a proper integral curve suffices: its finiteness and actual H1 finiteness are both derived. |

## CurveMapExistence

Finite-map existence on proper normal integral curves, with smoothness-to-normality derived for the smooth branch. Dimension zero is proved without integrality or reducedness. Local nonconstancy is constructed from an actual affine basic open; extension uses the valuative method in [Stacks 53.2.1–2](https://stacks.math.columbia.edu/tag/0BXX) and finiteness uses the earlier [Stacks 53.2.4](https://stacks.math.columbia.edu/tag/0CCL) specialization. Actual H1 finiteness uses the proved actual Laurent-chart comparison. This is not a formalization of unrestricted curve projectivity [Stacks 33.43.4](https://stacks.math.columbia.edu/tag/0A26).

Supporting cohomology construction for P 1434–1443. The Euler/degree implication itself remains unformalized.

| Source / mathematical role | Lean declaration | Kind | Exact coverage |
|---|---|---|---|
| Finite-map existence supporting P 1434–1443 | [`proper_dimZero_isFinite`](Normalizer/CurveMapExistence.lean#L18) | theorem | A proper zero-dimensional scheme over a field is finite, with no integrality or reducedness requirement. |
| Finite-map existence supporting P 1434–1443 | [`finiteScheme_map_isFinite`](Normalizer/CurveMapExistence.lean#L30) | theorem | Every morphism over a field from a finite scheme to a separated scheme is finite; the finiteness of its point fibres is derived. |
| Finite-map existence supporting P 1434–1443 | [`proper_dimZero_exists_finite_projectiveLine`](Normalizer/CurveMapExistence.lean#L49) | theorem | The zero-dimensional branch has an actual finite map to the projective line, obtained from the constant homogeneous coordinates `[1:0]`. |
| Finite-map existence supporting P 1434–1443 | [`proper_dimZero_positiveCohomology_subsingleton`](Normalizer/CurveMapExistence.lean#L59) | theorem | All positive-degree abelian-sheaf cohomology vanishes on a proper zero-dimensional scheme over a field. |
| Finite-map existence supporting P 1434–1443 | [`partialMap_eq_restriction_of_generic`](Normalizer/CurveMapExistence.lean#L68) | theorem | Generic agreement with a global map forces agreement on the entire specified partial-map domain, for an integral source and separated target. |
| Finite-map existence supporting P 1434–1443 | [`partialMap_extends_of_valuationOutside`](Normalizer/CurveMapExistence.lean#L80) | theorem | A partial map extends into a proper target when every stalk outside its actual domain is a valuation ring. Stalks inside that domain need not be normal: the already-defined map is retained there. |
| Finite-map existence supporting P 1434–1443 | [`normalCurve_partialMap_extends`](Normalizer/CurveMapExistence.lean#L119) | theorem | A specified partial map on a normal integral curve extends to a global map into a proper target over the original base. Its restriction is proved, not supplied as a further geometric hypothesis. |
| Finite-map existence supporting P 1434–1443 | [`affineIntegral_exists_nonconstant_projectiveLineMap`](Normalizer/CurveMapExistence.lean#L131) | theorem | On an affine integral scheme with at least two points, an actual global section defines a nonconstant projective-line map. The section is chosen with a proper nonempty invertibility locus. |
| Finite-map existence supporting P 1434–1443 | [`integral_exists_nontrivial_affineOpen`](Normalizer/CurveMapExistence.lean#L159) | theorem | An integral scheme with at least two points contains an actual affine open with at least two points. |
| Finite-map existence supporting P 1434–1443 | [`normalCurve_exists_nonconstant_projectiveLineMap`](Normalizer/CurveMapExistence.lean#L175) | theorem | A normal integral curve with at least two points has an actual nonconstant projective-line map over its original field. No rational function or nonconstancy certificate is supplied as an input. |
| Finite-map existence supporting P 1434–1443 | [`proper_finiteSpace_isFinite`](Normalizer/CurveMapExistence.lean#L197) | theorem | A proper morphism with a finite source space is finite. |
| Finite-map existence supporting P 1434–1443 | [`properNormalCurve_exists_finite_projectiveLine`](Normalizer/CurveMapExistence.lean#L206) | theorem | A proper normal integral curve of dimension at most one admits an actual finite projective-line map over its original field. Normality is explicit; this theorem includes the zero-dimensional case. |
| Finite-map existence supporting P 1434–1443 | [`properNormalCurve_unit_H1_finite`](Normalizer/CurveMapExistence.lean#L226) | theorem | Actual structure-sheaf H1 is finite-dimensional on a proper normal integral curve. The finite map and its scalar compatibility are constructed. |
| Finite-map existence supporting P 1434–1443 | [`smoothCurve_stalk_isIntegrallyClosed`](Normalizer/CurveMapExistence.lean#L239) | theorem | Smooth integral curves have integrally closed actual stalks. Smoothness supplies regularity; dimension at most one supplies the principal ideal property. |
| Finite-map existence supporting P 1434–1443 | [`properSmoothCurve_exists_finite_projectiveLine`](Normalizer/CurveMapExistence.lean#L253) | theorem | A proper smooth integral curve admits an actual finite projective-line map, with no supplied rational function, local normality or nonconstancy. |
| Finite-map existence supporting P 1434–1443 | [`properSmoothCurve_unit_H1_finite`](Normalizer/CurveMapExistence.lean#L261) | theorem | Actual structure-sheaf H1 finiteness for a proper smooth integral curve. Normality and the finite projective-line map are derived from these hypotheses. |

## CurveMapSingular

Constructed finite maps for proper integral curves normal outside a supplied nontrivial affine open, and for curves normal away from one specified point where that open is constructed. The exceptional point may be singular. The general affine neighborhood of the entire nonnormal locus remains unformalized. No arbitrary singular-curve H1 theorem is claimed.

Supporting cohomology construction for P 1434–1443. The Euler/degree implication itself remains unformalized.

| Source / mathematical role | Lean declaration | Kind | Exact coverage |
|---|---|---|---|
| Finite-map existence supporting P 1434–1443 | [`integral_exists_nontrivial_affineOpen_at`](Normalizer/CurveMapSingular.lean#L17) | theorem | Every point of a nontrivial integral scheme lies in an actual affine open with at least two points. For the generic point, choose a neighborhood of another point, which necessarily also contains the generic point. |
| Finite-map existence supporting P 1434–1443 | [`properCurve_exists_finite_projectiveLine_of_normalOutsideAffine`](Normalizer/CurveMapSingular.lean#L38) | theorem | A proper integral curve admits a finite projective-line map if an actual nontrivial affine open contains all its nonnormal points. The map, its extension across the complementary points, and nonconstancy are derived. |
| Finite-map existence supporting P 1434–1443 | [`properCurve_exists_finite_projectiveLine_of_normalAwayPoint`](Normalizer/CurveMapSingular.lean#L64) | theorem | A proper integral curve normal away from one specified point has an actual finite projective-line map. No normality at that point or affine neighborhood containing it is assumed. |
| Finite-map existence supporting P 1434–1443 | [`properCurve_unit_H1_finite_of_normalAwayPoint`](Normalizer/CurveMapSingular.lean#L88) | theorem | Actual structure-sheaf H1 finiteness when the proper integral curve is normal away from one point. The exceptional point may be singular. |
