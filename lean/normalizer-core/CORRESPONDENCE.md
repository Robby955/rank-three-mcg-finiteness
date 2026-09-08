# Public manuscript-to-Lean correspondence

All declaration names have the prefix `Normalizer.`. This table covers all
233 named theorems. The final index covers the other 107 named constructions;
all 340 declarations are included in `AxiomAudit.lean`.

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
normalizer quotients. The required global-section realization, function-field
passage and exhaustive orbit classification remain outside those results.
The [overview](OVERVIEW.md) records the current geometric gaps; no finite
arithmetic script serves as a proof in this package.

Source SHA-256 values:

```text
2cc61289a02074c4bd42cdbe337ca5dca922bc83299ccf56ca485d6b65f2d6c3  manuscript/rank3_genus5_reader.tex
b64fe79e47d5862c0bf2b77ca3f3cb06bd6e1289ad6721e9b8d23b5305aa622b  LOAD_BEARING_AUDIT.md
```

## AffineFreeNeighborhood

| Public source / mathematical role | Lean theorem | Exact coverage |
|---|---|---|
| Actual chart support for [P 936](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L936) | [`affineLocalizationMap_opensRange`](Normalizer/AffineFreeNeighborhood.lean#L96) | The image of Spec of localization away from r is the actual principal open D(r). |
| Actual affine trivialization support for [P 936](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L936) | [`affineLocalization_finiteFree_trivialization`](Normalizer/AffineFreeNeighborhood.lean#L112) | A finite module with free localization gives a finite free-sheaf isomorphism on the actual localization chart; the localization is explicitly nontrivial. |
| Associated-sheaf neighborhood step supporting [P 936](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L936) | [`affineStalk_exists_finiteFree_neighborhood`](Normalizer/AffineFreeNeighborhood.lean#L122) | A free actual stalk of tilde(M), with M finitely presented, produces a principal affine chart containing the point and an actual finite free-sheaf trivialization. |

## AffineLocallyFree

| Public source / mathematical role | Lean theorem | Exact coverage |
|---|---|---|
| Affine local-trivialization support for [P 936](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L936) | [`affineFreeSheaf_isLocallyFree`](Normalizer/AffineLocallyFree.lean#L26) | A free module's actual associated sheaf is locally free, via its basis and tilde of the free module. |
| Affine finite-type support for [P 936](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L936) | [`affineFreeSheaf_isFiniteType`](Normalizer/AffineLocallyFree.lean#L32) | A finite free module's actual associated sheaf has finite local generators. |
| Affine PID case of [P 936](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L936) | [`affineSaturatedQuotient_trivialization`](Normalizer/AffineLocallyFree.lean#L46) | Constructs an actual global free-sheaf isomorphism with a finite index type for the scalar-saturated quotient over Spec of a PID. |
| Affine PID case of [P 936](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L936) | [`affineSaturatedQuotient_finiteLocallyFree`](Normalizer/AffineLocallyFree.lean#L56) | The actual affine sheaf cokernel is both locally free and finite type. No PID-chart assumption for smooth curves is used. |

## AffinePresentedNeighborhood

| Public source / mathematical role | Lean theorem | Exact coverage |
|---|---|---|
| Presented-affine neighborhood step supporting [P 936](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L936) | [`affinePresentation_exists_finiteFree_neighborhood`](Normalizer/AffinePresentedNeighborhood.lean#L18) | An actual affine sheaf with a finite global presentation and a free actual stalk has a principal affine finite free-sheaf neighborhood. |

## AffineQuotient

| Public source / mathematical role | Lean theorem | Exact coverage |
|---|---|---|
| Affine quotient support for [P 936](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L936) | [`affineCokernelIso_projection`](Normalizer/AffineQuotient.lean#L26) | The actual sheaf cokernel comparison preserves the projection induced by the module cokernel. |
| Affine saturation support for [P 936](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L936) | [`quotient_isTorsionFree_of_saturated`](Normalizer/AffineQuotient.lean#L33) | Over a domain, explicit scalar saturation of S proves torsion freeness of the actual module quotient M/S. |
| Affine PID case of [P 936](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L936) | [`quotient_free_of_saturated`](Normalizer/AffineQuotient.lean#L48) | A finite module quotient with explicit scalar saturation is free over a PID, using mathlib's standard finite torsion-free theorem. |
| Actual affine quotient support for [P 936](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L936) | [`affineSubmoduleQuotientIso_projection`](Normalizer/AffineQuotient.lean#L66) | The actual sheaf cokernel of tilde(S -> M) is identified with tilde(M/S) by the canonical quotient projection. |

## AffineStalks

| Public source / mathematical role | Lean theorem | Exact coverage |
|---|---|---|
| Local-ring action support for [P 936](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L936) | [`affineStalk_isScalarTower`](Normalizer/AffineStalks.lean#L26) | The ordinary base-ring action on the actual associated-sheaf stalk agrees with its actual local-ring action. |
| Affine free-stalk support for [P 936](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L936) | [`affineStalk_free_iff`](Normalizer/AffineStalks.lean#L34) | The ordinary module free locus is exactly the locus of free actual sheaf stalks over their actual local rings. |
| Finite-stalk support for [P 936](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L936) | [`affineStalk_finite`](Normalizer/AffineStalks.lean#L47) | The actual stalk of an associated finite module is finite over the actual local ring. |
| Affine neighborhood support for [P 936](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L936) | [`affineStalk_freeLocus_isOpen`](Normalizer/AffineStalks.lean#L57) | For a finitely presented module, the free-actual-stalk locus of its associated sheaf is open. |
| Module localization step supporting [P 936](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L936) | [`affineStalk_exists_free_localization`](Normalizer/AffineStalks.lean#L67) | A free actual stalk gives a free localization away from an element outside the prime, with the same rank. The separate sheaf comparison constructs the actual trivialization. |

## Boundary

| Public source / mathematical role | Lean theorem | Exact coverage |
|---|---|---|
| [P 952–961](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L952-L961), arbitrary overlap sections | [`abelian_overlap_difference`](Normalizer/Boundary.lean#L14) | Uses [a,b]=0 and the two normalizer actions, without requiring constant scalar multiples of a line generator. |
| [P 952–961](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L952-L961); [A 46–54](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/LOAD_BEARING_AUDIT.md#L46-L54) | [`cech_commutator_difference`](Normalizer/Boundary.lean#L22) | Local overlap expansion with the convention Xj − Xi; derived from Lie algebra identities. |
| [P 957–966](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L957-L966); [A 48–54](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/LOAD_BEARING_AUDIT.md#L48-L54) | [`boundary_cocycle`](Normalizer/Boundary.lean#L35) | Apply a linear class map on a cocycle submodule. The representative equalities and constant scalars are explicit hypotheses; actual sheaf cohomology is not constructed. |
| [P 968–972](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L968-L972); [A 57–60](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/LOAD_BEARING_AUDIT.md#L57-L60) | [`quotient_boundary_law`](Normalizer/Boundary.lean#L58) | Injectivity of an ambient linear boundary map yields the bracket identity. |

## ExtensionDimension

| Public source / mathematical role | Lean theorem | Exact coverage |
|---|---|---|
| E2 rank A≤1 and kernel estimate | [`extension_dimension_loss`](Normalizer/ExtensionDimension.lean#L16) | General linear bound dim V≤dim ker A+dim ker s when e is injective and s e A=0. |
| Reconstruction encompassing E1 and E2 | [`extension_kernel_lower_bound`](Normalizer/ExtensionDimension.lean#L32) | General d≥1 estimate dim ker A≥g−h under the displayed dimension hypotheses. |
| E2 dim ker A≥4 | [`degree_two_kernel_four`](Normalizer/ExtensionDimension.lean#L42) | Exact genus-five degree-two numerical specialization. |

## ExtensionNaturality

| Public source / mathematical role | Lean theorem | Exact coverage |
|---|---|---|
| E2 zero-left extension diagram | [`connecting_zero_of_zero_left`](Normalizer/ExtensionNaturality.lean#L18) | Actual mathlib homology connecting map, for arbitrary short exact complexes. |
| E1 morphism identity; E2 s_*eA=0 | [`extension_block_annihilated`](Normalizer/ExtensionNaturality.lean#L29) | Derives the annihilation identity from two genuine morphisms of short exact complexes and their right-component factorization. |
| E1 A=0 | [`extension_block_zero`](Normalizer/ExtensionNaturality.lean#L43) | Cancels two monomorphisms; their geometric identification is not asserted. |
| E1 and E2, extension naturality plus dimension count | [`homology_extension_kernel_lower_bound`](Normalizer/ExtensionNaturality.lean#L64) | Combines actual connecting maps, injectivity from vanishing middle homology, and the dimension estimate. No sheaf cohomology construction is claimed. |

## Flagship

| Public source / mathematical role | Lean theorem | Exact coverage |
|---|---|---|
| [P 985–990](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L985-L990); [A 66–68](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/LOAD_BEARING_AUDIT.md#L66-L68) | [`sem_quotient_no_three`](Normalizer/Flagship.lean#L19) | Every subspace of the actual semisimple matrix quotient satisfying the law has finrank < 3. |
| [P 992–1035](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L992-L1035); [A 68–82](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/LOAD_BEARING_AUDIT.md#L68-L82) | [`nil_quotient_no_three`](Normalizer/Flagship.lean#L29) | Every subspace of the actual minimal matrix quotient satisfying the law has finrank < 3. |
| Algebraic corollary of [P 968–990](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L968-L990) | [`sem_injective_boundary_obstruction`](Normalizer/Flagship.lean#L40) | Boundary map on the whole algebraic quotient is explicitly assumed injective. This convenience corollary is not the geometric global-section instantiation. |
| Algebraic corollary of [P 968–1035](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L968-L1035) | [`nil_injective_boundary_obstruction`](Normalizer/Flagship.lean#L51) | Same algebraic corollary for the minimal quotient, with its grading character. No map on the geometric generic fibre is asserted to exist. |
| [P 1029–1035](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L1029-L1035); [A 80–82](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/LOAD_BEARING_AUDIT.md#L80-L82) | [`nil_eigenvalue_conflict`](Normalizer/Flagship.lean#L63) | The two displayed eigenvalues cannot both equal one. |
| E1/E2 followed by P normalizer obstruction | [`sem_extension_obstruction`](Normalizer/Flagship.lean#L78) | Excludes an explicit injective realization of the large kernel in the semisimple quotient satisfying its law. |
| E1/E2 followed by P normalizer obstruction | [`nil_extension_obstruction`](Normalizer/Flagship.lean#L91) | Same for the minimal-nilpotent quotient. |

## FrameCharacter

| Public source / mathematical role | Lean theorem | Exact coverage |
|---|---|---|
| [P 937–942](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L937-L942), [M,M]=0 | [`frameLine_abelian`](Normalizer/FrameCharacter.lean#L22) | The actual cyclic Lie subalgebra is abelian. |
| [P 937–947](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L937-L947), normalizer action | [`mem_frameNormalizer`](Normalizer/FrameCharacter.lean#L31) | Actual normalizer membership iff the generator has scalar action. |
| [P 944–947](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L944-L947), [x,m]=λ(x)m | [`frameCharacter_action`](Normalizer/FrameCharacter.lean#L73) | The constructed character satisfies its action equation. |
| [P 944–947](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L944-L947), uniqueness | [`frameCharacter_eq`](Normalizer/FrameCharacter.lean#L79) | Frame injectivity makes the coefficient unique. |
| [P 944–947](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L944-L947), grading character | [`frameCharacter_bracket`](Normalizer/FrameCharacter.lean#L88) | Jacobi proves bracket vanishing. |
| [P 942–947](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L942-L947), descent | [`frameCharacter_kills_line`](Normalizer/FrameCharacter.lean#L106) | The character kills the actual line ideal. |
| [P 942–947](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L942-L947), lift independence | [`frameCharacter_change_lift`](Normalizer/FrameCharacter.lean#L117) | Changing a lift by a line section preserves its character. |
| [P 942–947](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L942-L947), quotient | [`quotientFrameCharacter_mk`](Normalizer/FrameCharacter.lean#L132) | The actual quotient character agrees on representatives. |
| [P 944–947](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L944-L947), quotient character | [`quotientFrameCharacter_bracket`](Normalizer/FrameCharacter.lean#L138) | It kills the actual quotient Lie bracket. |
| [P 944–947](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L944-L947), frame independence | [`frameLine_unit`](Normalizer/FrameCharacter.lean#L148) | Unit rescaling preserves the line subalgebra and normalizer. |
| [P 944–947](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L944-L947), frame independence | [`frame_action_unit_iff`](Normalizer/FrameCharacter.lean#L155) | The action coefficient survives unit rescaling. |
| [P 944–947](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L944-L947), frame property | [`frame_unit_injective`](Normalizer/FrameCharacter.lean#L166) | Rescaling preserves frame injectivity. |
| [P 944–947](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L944-L947), frame independence | [`frameCharacter_unit`](Normalizer/FrameCharacter.lean#L176) | The constructed characters agree in unit-related frames. |
| [P 944–947](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L944-L947), overlap compatibility | [`frameCharacter_unit_mod_line`](Normalizer/FrameCharacter.lean#L190) | Simultaneous frame and quotient-lift changes preserve the character. |
| [P 944–947](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L944-L947), restriction | [`frameCharacter_restrict`](Normalizer/FrameCharacter.lean#L226) | Compatibility with a bracket-preserving semilinear restriction. |
| [P 942–947](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L942-L947), quotient restriction | [`quotientFrameCharacter_restrict`](Normalizer/FrameCharacter.lean#L253) | Compatibility on the actual normalizer quotients. |

## HomologyBoundary

| Public source / mathematical role | Lean theorem | Exact coverage |
|---|---|---|
| Exactness underlying [P 959–966](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L959-L966) | [`connecting_eq_zero_of_closed_lift`](Normalizer/HomologyBoundary.lean#L18) | Actual mathlib connecting map vanishes on a class with a closed middle cochain lift. |
| [P 959–966](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L959-L966) | [`connecting_boundary_law`](Normalizer/HomologyBoundary.lean#L41) | Proves the actual connecting-map law from a differential identity on lifts; no boundary-value identities are assumed. |
| [P 952–966](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L952-L966) | [`connecting_boundary_law_of_overlaps`](Normalizer/HomologyBoundary.lean#L68) | Derives that differential identity using arbitrary abelian-ideal overlap sections and an injective overlap map. Construction of the curve's complexes is outside scope. |

## IntegralSheafTorsion

| Public source / mathematical role | Lean theorem | Exact coverage |
|---|---|---|
| Actual scheme-stalk support for [P 936](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L936) and [P 941](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L941) | [`schemeModule_germ_smul`](Normalizer/IntegralSheafTorsion.lean#L32) | The actual structure-sheaf and module-sheaf germs satisfy the scalar multiplication identity. |
| Actual integral-scheme torsion support for [P 936](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L936) and [P 941](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L941) | [`integralSheaf_sections_isTorsionFree`](Normalizer/IntegralSheafTorsion.lean#L43) | Torsion-free actual stalks imply torsion-free sections on every open; empty opens use sheaf separatedness. |
| Actual integral-scheme torsion support for [P 936](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L936) and [P 941](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L941) | [`integralSheaf_stalk_isTorsionFree`](Normalizer/IntegralSheafTorsion.lean#L62) | Torsion-free section modules on all opens imply torsion-free actual stalks by representing germs and shrinking their relations. |
| Actual integral-scheme torsion support for [P 936](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L936) and [P 941](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L941) | [`integralSheaf_torsionFree_iff`](Normalizer/IntegralSheafTorsion.lean#L96) | Proves the equivalence of the actual stalkwise and all-open sectionwise torsion-free criteria on an integral scheme. |
| Actual integral-scheme kernel saturation in [P 941](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L941) | [`integralSheaf_kernelCokernel_stalk_isTorsionFree`](Normalizer/IntegralSheafTorsion.lean#L105) | The actual quotient by a sheaf kernel has torsion-free stalks when the target has torsion-free stalks. The target hypothesis remains explicit. |

## KernelQuotient

| Public source / mathematical role | Lean theorem | Exact coverage |
|---|---|---|
| General categorical support for [P 937–942](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L937-L942) | [`kernelQuotientProjection_fac`](Normalizer/KernelQuotient.lean#L25) | The map between the two actual kernels composes to the original kernel inclusion followed by the cokernel projection. |
| General categorical support for [P 937–942](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L937-L942) | [`kernelQuotientProjection_epi`](Normalizer/KernelQuotient.lean#L32) | That map is an epimorphism, proved through epimorphic refinements; no sectionwise surjectivity is assumed. |
| General categorical support for [P 937–942](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L937-L942) | [`kernelQuotientIso_projection`](Normalizer/KernelQuotient.lean#L74) | The cokernel/kernel isomorphism is induced by the canonical kernel projection. |
| General categorical support for [P 937–942](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L937-L942) | [`kernelQuotientIso_fac`](Normalizer/KernelQuotient.lean#L82) | The comparison commutes with the original and quotient inclusions. |
| General categorical support for [P 937–942](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L937-L942) | [`kernelQuotientIso_hom_ι`](Normalizer/KernelQuotient.lean#L89) | The map into the ambient quotient is its actual cokernel descent. |
| General categorical support for [P 937–942](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L937-L942) | [`kernelQuotientIsoOfKernel_fac`](Normalizer/KernelQuotient.lean#L123) | The same compatibility holds for any supplied actual kernel satisfying its universal property. |
| General categorical support for [P 937–942](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L937-L942) | [`kernelQuotientIsoOfKernel_hom_ι`](Normalizer/KernelQuotient.lean#L132) | The supplied-kernel comparison is the descent of its original inclusion. |

## KernelSaturation

| Public source / mathematical role | Lean theorem | Exact coverage |
|---|---|---|
| Categorical quotient support for [P 941](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L941) | [`kernelCokernelToTarget_projection`](Normalizer/KernelSaturation.lean#L36) | The actual quotient by a sheaf kernel maps to the target with composite equal to the original morphism. |
| Categorical quotient support for [P 941](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L941) | [`kernelCokernelToTarget_mono`](Normalizer/KernelSaturation.lean#L41) | The actual quotient by the kernel embeds in the target sheaf, by the abelian-category coimage theorem. |
| Sectionwise support for [P 941](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L941) | [`kernelCokernelToTarget_app_injective`](Normalizer/KernelSaturation.lean#L48) | Evaluation of the actual monomorphism is injective; no sectionwise quotient formula or surjectivity is asserted. |
| Sectionwise support for [P 941](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L941) | [`kernelCokernel_sections_isTorsionFree`](Normalizer/KernelSaturation.lean#L57) | At a specified open with torsion-free target sections, the actual quotient's sections are torsion free. |
| Sectionwise support for [P 941](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L941) | [`sheaf_kernel_regular_smul_iff`](Normalizer/KernelSaturation.lean#L65) | A regular scalar can be cancelled when testing vanishing under the actual sheaf morphism. |
| Sectionwise support for [P 941](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L941) | [`subsheafKernel_regular_smul_mem_iff`](Normalizer/KernelSaturation.lean#L74) | For a supplied subsheaf identified with the actual kernel, regular scalar multiplication does not change membership. |

## KernelTargetIso

| Public source / mathematical role | Lean theorem | Exact coverage |
|---|---|---|
| Categorical support for [P 938–939](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L938-L939) | [`kernelTargetIso_hom_ι`](Normalizer/KernelTargetIso.lean#L23) | Changing a morphism target by an actual isomorphism preserves its kernel inclusion into the source. |
| Categorical support for [P 938–939](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L938-L939) | [`kernelTargetIso_inv_ι`](Normalizer/KernelTargetIso.lean#L28) | The inverse kernel transport also preserves the canonical inclusion. |

## LineSheafTensor

| Public source / mathematical role | Lean theorem | Exact coverage |
|---|---|---|
| [P 938](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L938), canonical tensor-Hom comparison | [`lineSheafTensorEvalAt_tmul`](Normalizer/LineSheafTensor.lean#L111) | The canonical sectionwise tensor evaluation acts by phi(m) • res(g) on every smaller open. |
| [P 938](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L938), canonical tensor-Hom comparison | [`lineSheafTensorEvalPresheaf_pure`](Normalizer/LineSheafTensor.lean#L207) | The bundled presheaf evaluation has the same canonical pure-tensor formula. |
| [P 938](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L938), canonical tensor-Hom comparison | [`lineSheafTensorEvalAt_bijective`](Normalizer/LineSheafTensor.lean#L254) | Canonical presheaf evaluation is bijective on every subopen of an actual rank-one trivialization. |
| [P 938](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L938), canonical tensor-Hom comparison | [`lineSheafTensorEval_pure`](Normalizer/LineSheafTensor.lean#L270) | Evaluation from the actual tensor sheaf retains the prescribed formula on pure tensors and all smaller opens. |
| [P 938](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L938), canonical tensor-Hom comparison | [`lineSheafTensorEval_isIso`](Normalizer/LineSheafTensor.lean#L285) | A genuine covering family of rank-one sheaf trivializations makes canonical tensor evaluation an isomorphism globally. |
| [P 938](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L938), canonical tensor-Hom comparison | [`lineSheafTensorIso_hom`](Normalizer/LineSheafTensor.lean#L305) | The forward isomorphism is the canonical evaluation map, which was defined independently of the cover. |

## LineTensor

| Public source / mathematical role | Lean theorem | Exact coverage |
|---|---|---|
| Support for [P 936–940](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L936-L940), module algebra | [`tensorHomEval_tmul`](Normalizer/LineTensor.lean#L23) | Canonical module evaluation sends g tensor phi to the map m -> phi(m) • g. |
| Support for [P 936–940](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L936-L940), module algebra | [`line_coordinate`](Normalizer/LineTensor.lean#L29) | A chosen rank-one frame reconstructs every vector from its coordinate. |
| Support for [P 936–940](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L936-L940), module algebra | [`line_dual_coordinate`](Normalizer/LineTensor.lean#L35) | Every functional is its value on the frame times the coordinate functional. |
| Support for [P 936–940](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L936-L940), module algebra | [`lineTensorHomInv_apply`](Normalizer/LineTensor.lean#L50) | The explicit inverse sends f to f(frame) tensor coordinate. |
| Support for [P 936–940](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L936-L940), module algebra | [`tensorHomEval_lineTensorHomInv`](Normalizer/LineTensor.lean#L53) | Evaluation after the constructed inverse is the identity. |
| Support for [P 936–940](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L936-L940), module algebra | [`lineTensorHomInv_tensorHomEval`](Normalizer/LineTensor.lean#L59) | The constructed inverse after evaluation is the identity on all tensors. |
| Support for [P 936–940](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L936-L940), module algebra | [`lineTensorHomEquiv_toLinearMap`](Normalizer/LineTensor.lean#L79) | The local equivalence has exactly the canonical evaluation as its forward map. |
| Support for [P 936–940](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L936-L940), module algebra | [`lineTensorHomEquiv_symm_apply`](Normalizer/LineTensor.lean#L83) | The equivalence inverse has the prescribed frame formula. |
| Support for [P 936–940](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L936-L940), module algebra | [`lineTensorHomEquiv_eq`](Normalizer/LineTensor.lean#L87) | The canonical equivalence is independent of the chosen frame. |
| Support for [P 936–940](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L936-L940), module algebra | [`tensorHomEval_injective`](Normalizer/LineTensor.lean#L92) | Evaluation is injective for an actually trivialized rank-one source. |
| Support for [P 936–940](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L936-L940), module algebra | [`tensorHomEval_surjective`](Normalizer/LineTensor.lean#L96) | Evaluation is surjective for an actually trivialized rank-one source. |
| Support for [P 936–940](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L936-L940), module algebra | [`tensorHomEval_natural_target`](Normalizer/LineTensor.lean#L103) | Evaluation commutes with any linear map on the target module. |
| Support for [P 936–940](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L936-L940), module algebra | [`tensorHomEval_natural_source`](Normalizer/LineTensor.lean#L115) | Evaluation commutes with precomposition on the source module. |

## LocalCharacterGluing

| Public source / mathematical role | Lean theorem | Exact coverage |
|---|---|---|
| Support for [P 944–947](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L944-L947), local-to-global action | [`glueLocalModuleMorphisms_local`](Normalizer/LocalCharacterGluing.lean#L132) | The constructed sheaf-of-modules morphism recovers each prescribed local linear map on every subopen of a cover member. |
| Support for [P 944–947](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L944-L947), independence of gluing choices | [`glueLocalModuleMorphisms_unique`](Normalizer/LocalCharacterGluing.lean#L143) | Any morphism with the prescribed local components equals the constructed morphism. |
| Support for [P 944–947](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L944-L947), existence of a global morphism | [`existsUnique_localModuleMorphism`](Normalizer/LocalCharacterGluing.lean#L162) | Restriction and overlap compatibility give exactly one morphism of the actual sheaves of modules. |

## LocallyFreeAssembly

| Public source / mathematical role | Lean theorem | Exact coverage |
|---|---|---|
| Local-generator support for [P 936](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L936) | [`freeCoverLocalGeneratorsData_isLocallyFree`](Normalizer/LocallyFreeAssembly.lean#L47) | Proves every local generator map is an isomorphism, the defining local-freeness datum. |
| General local-freeness criterion underlying [P 936](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L936) | [`sheaf_isLocallyFree_of_free_stalks`](Normalizer/LocallyFreeAssembly.lean#L60) | For any scheme, actual sheaf finite presentation and free actual stalks imply mathlib IsLocallyFree. The cover and generators are constructed. |

## LocallyFreeTransport

| Public source / mathematical role | Lean theorem | Exact coverage |
|---|---|---|
| Actual local-trivialization support for [P 936](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L936) | [`isLocallyFree_of_iso`](Normalizer/LocallyFreeTransport.lean#L35) | An actual sheaf isomorphism transports local generators and their isomorphism property on the unchanged covering family. |
| Actual finite-type support for [P 936](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L936) | [`isFiniteType_of_iso`](Normalizer/LocallyFreeTransport.lean#L47) | The same transport retains the finite local generator index types. |
| Actual finite-type support for [P 936](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L936) | [`freeSheaf_isFiniteType`](Normalizer/LocallyFreeTransport.lean#L57) | A free sheaf indexed by a finite type has actual finite local generators. |

## Matrices

| Public source / mathematical role | Lean theorem | Exact coverage |
|---|---|---|
| [P 985–987](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L985-L987) | [`semLift_trace`](Normalizer/Matrices.lean#L41) | Semisimple coordinate lifts are trace zero. |
| [P 992–997](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L992-L997) | [`nilLift_trace`](Normalizer/Matrices.lean#L44) | Minimal coordinate lifts are trace zero. |
| [P 985–987](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L985-L987); [A 66–68](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/LOAD_BEARING_AUDIT.md#L66-L68) | [`sem_action`](Normalizer/Matrices.lean#L49) | Every parametrized semisimple normalizer element centralizes the distinguished matrix. |
| [P 999–1002](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L999-L1002); [A 76](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/LOAD_BEARING_AUDIT.md#L76) | [`nil_action`](Normalizer/Matrices.lean#L52) | Action on E12 is exactly multiplication by the D-coordinate. |
| [P 985–987](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L985-L987) | [`sem_bracket_lift`](Normalizer/Matrices.lean#L55) | All semisimple matrix commutators equal the lifted sl2 coordinate bracket; arbitrary line lifts allowed. |
| [P 1003–1006](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L1003-L1006) | [`nil_bracket_lift`](Normalizer/Matrices.lean#L61) | All minimal matrix commutators equal the lifted coordinate bracket plus an explicitly calculated multiple of E12. |
| [P 980–990](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L980-L990); [A 63–68](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/LOAD_BEARING_AUDIT.md#L63-L68) | [`sem_normalizer`](Normalizer/Matrices.lean#L68) | If and only if: trace zero and [X,m]=t m are equivalent to the explicit four-parameter normal form with t=0. |
| [P 992–1002](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L992-L1002); [A 68–76](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/LOAD_BEARING_AUDIT.md#L68-L76) | [`nil_normalizer`](Normalizer/Matrices.lean#L98) | If and only if: trace zero and [X,E12]=t E12 are equivalent to the explicit five-parameter normal form with t equal to the D-coordinate. |

## ModuleHomLine

| Public source / mathematical role | Lean theorem | Exact coverage |
|---|---|---|
| Support for [P 938](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L938), actual local sheaf frames | [`moduleLineFrameAt_restrict`](Normalizer/ModuleHomLine.lean#L25) | The frame from a restricted-sheaf isomorphism commutes with restriction. |
| Support for [P 938](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L938), actual local sheaf frames | [`moduleLineFrameAt_symm_restrict`](Normalizer/ModuleHomLine.lean#L35) | Coordinates in that frame commute with restriction. |
| Support for [P 938](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L938), actual local sheaf frames | [`moduleHom_eval_frame`](Normalizer/ModuleHomLine.lean#L72) | Naturality on every smaller open recovers an internal-Hom section from the image of its frame. |
| Support for [P 938](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L938), actual local sheaf frames | [`moduleHomFrameEquiv_apply`](Normalizer/ModuleHomLine.lean#L118) | The local internal-Hom equivalence is actual evaluation at the frame. |

## ModuleSheafHom

| Public source / mathematical role | Lean theorem | Exact coverage |
|---|---|---|
| Hom-sheaf infrastructure for [P 937–942](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L937-L942) | [`moduleHomEval_mk`](Normalizer/ModuleSheafHom.lean#L210) | A constructed Hom section recovers every supplied compatible local linear map. |
| Hom-sheaf infrastructure for [P 937–942](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L937-L942) | [`moduleHom_ext`](Normalizer/ModuleSheafHom.lean#L222) | Equality is tested on all smaller opens and all source sections. |
| Hom-sheaf infrastructure for [P 937–942](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L937-L942) | [`moduleHom_restrict`](Normalizer/ModuleSheafHom.lean#L232) | Restricting a Hom section retains its original component on each smaller open. |
| Hom-sheaf infrastructure for [P 937–942](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L937-L942) | [`moduleHomEval_natural`](Normalizer/ModuleSheafHom.lean#L248) | Every Hom section acts naturally with respect to module restrictions. |
| Hom-sheaf infrastructure for [P 937–942](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L937-L942) | [`moduleHomEval_zero`](Normalizer/ModuleSheafHom.lean#L258) | Zero acts by zero. |
| Hom-sheaf infrastructure for [P 937–942](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L937-L942) | [`moduleHomEval_add`](Normalizer/ModuleSheafHom.lean#L262) | Addition acts componentwise. |
| Hom-sheaf infrastructure for [P 937–942](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L937-L942) | [`moduleHomEval_smul`](Normalizer/ModuleSheafHom.lean#L268) | Scalars are restricted before acting on a smaller open. |

## ModuleSheafTensor

| Public source / mathematical role | Lean theorem | Exact coverage |
|---|---|---|
| Support for [P 938](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L938), actual tensor sheaf | [`moduleTensorHomEquiv_apply`](Normalizer/ModuleSheafTensor.lean#L60) | The actual sheafification adjunction restricts a sheaf morphism along its canonical projection. |
| Support for [P 938](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L938), actual tensor sheaf | [`moduleTensorProjection_lift`](Normalizer/ModuleSheafTensor.lean#L66) | The lifted sheaf morphism has the originally prescribed presheaf values. |
| Support for [P 938](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L938), actual tensor sheaf | [`moduleTensor_hom_ext`](Normalizer/ModuleSheafTensor.lean#L73) | The projection formula uniquely determines a morphism from the actual tensor sheaf. |
| Support for [P 938](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L938), actual tensor sheaf | [`moduleTensorPresheafPure_restrict`](Normalizer/ModuleSheafTensor.lean#L94) | Restriction of a presheaf pure tensor is the tensor of the restricted sections. |
| Support for [P 938](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L938), actual tensor sheaf | [`moduleTensorPresheaf_map_tmul`](Normalizer/ModuleSheafTensor.lean#L101) | The actual tensor-presheaf restriction has the ordinary pure-tensor formula. |
| Support for [P 938](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L938), actual tensor sheaf | [`moduleTensorPure_restrict`](Normalizer/ModuleSheafTensor.lean#L110) | The same pure-tensor restriction formula survives actual sheafification. |
| Support for [P 938](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L938), actual tensor sheaf | [`moduleTensorLift_pure`](Normalizer/ModuleSheafTensor.lean#L118) | A lifted sheaf map evaluates pure tensors by its prescribed presheaf map. |

## NormalizerKernel

| Public source / mathematical role | Lean theorem | Exact coverage |
|---|---|---|
| [P 937–942](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L937-L942), ambient quotient exactness | [`ambientQuotient_zero_iff`](Normalizer/NormalizerKernel.lean#L26) | A section of E maps to zero in the actual sheaf quotient exactly when it lies in I on that same open. |
| [P 937–941](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L937-L941), actual bracket-induced map | [`normalizerBracketMap_apply`](Normalizer/NormalizerKernel.lean#L176) | Evaluating b(x) on a local I-section gives the actual projected bracket [res x,m] mod I. |
| [P 937–942](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L937-L942), normalizer kernel | [`normalizerBracketMap_zero_iff`](Normalizer/NormalizerKernel.lean#L186) | Vanishing of the constructed Hom-valued map is equivalent to the existing all-restrictions normalizer condition. |
| [P 937–942](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L937-L942), normalizer inclusion | [`normalizerBracketMap_condition`](Normalizer/NormalizerKernel.lean#L206) | The existing normalizer inclusion is killed by the actual bracket map. |
| [P 937–941](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L937-L941), descent through E/I | [`normalizerBracketMap_kills_line`](Normalizer/NormalizerKernel.lean#L227) | Abelianness makes b kill the actual subsheaf inclusion. |
| [P 937–941](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L937-L941), induced quotient map | [`ambientQuotientBracketMap_projection`](Normalizer/NormalizerKernel.lean#L241) | The constructed beta satisfies q composed with beta equals b. |
| [P 937–941](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L937-L941), bracket formula after descent | [`ambientQuotientBracketMap_apply`](Normalizer/NormalizerKernel.lean#L249) | On projected sections, beta evaluates to the same actual projected bracket on every smaller open. |
| [P 937–942](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L937-L942), kernel identification | [`normalizerQuotientKernelIso_fac`](Normalizer/NormalizerKernel.lean#L283) | The proved N/I ≅ ker beta identifies the original inclusion/projection diagram. No kernel-identification hypothesis remains. |
| [P 937–942](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L937-L942), canonical map into G | [`normalizerQuotientToAmbient_projection`](Normalizer/NormalizerKernel.lean#L312) | The direct cokernel descent from N/I to G recovers N -> E -> G. |
| [P 937–942](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L937-L942), intended inclusion under the isomorphism | [`normalizerQuotientKernelIso_hom_ι`](Normalizer/NormalizerKernel.lean#L320) | The kernel inclusion is exactly the canonical descended map, not an unrelated embedding. |
| [P 937–942](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L937-L942), K as a subobject of G | [`normalizerQuotientToAmbient_mono`](Normalizer/NormalizerKernel.lean#L329) | The canonical N/I -> G is monic as an actual module-sheaf morphism. Saturation on a curve remains separate. |

## NormalizerSheaf

| Public source / mathematical role | Lean theorem | Exact coverage |
|---|---|---|
| [P 937–942](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L937-L942), normalizer subsheaf | [`mem_normalizerSubsheaf`](Normalizer/NormalizerSheaf.lean#L61) | Membership means preserving the subsheaf after every restriction; the subsheaf and its local membership proof are constructed. |
| [P 944–947](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L944-L947), action on the line | [`normalizerSubsheaf_action`](Normalizer/NormalizerSheaf.lean#L67) | A normalizer section acts on sections of the subsheaf on the same open. |
| [P 941–942](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L941-L942), inclusion of the line | [`abelian_subsheaf_le_normalizer`](Normalizer/NormalizerSheaf.lean#L73) | An actual abelian subsheaf lies in the constructed normalizer. |
| [P 941–942](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L941-L942), closure under bracket | [`normalizerSubsheaf_bracket`](Normalizer/NormalizerSheaf.lean#L82) | Restriction compatibility and Jacobi imply bracket closure of the constructed normalizer. |
| Support for [P 944–947](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L944-L947), framed description | [`normalizerSubsheaf_frame_criterion`](Normalizer/NormalizerSheaf.lean#L96) | A frame generating the line on all subopens reduces normalizer membership to the action on that frame. |
| [P 944–947](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L944-L947), character descent | [`descendNormalizerCharacter_fac`](Normalizer/NormalizerSheaf.lean#L139) | A character killing the inclusion factors through the actual sheaf cokernel, recovering the original map. |
| [P 944–947](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L944-L947), uniqueness of descent | [`descendNormalizerCharacter_unique`](Normalizer/NormalizerSheaf.lean#L148) | The factorization through the sheaf quotient is unique. |
| Support for [P 944–947](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L944-L947), vanishing on the line | [`gluedNormalizerCharacter_kills_line`](Normalizer/NormalizerSheaf.lean#L192) | Local vanishing of the supplied compatible characters gives zero composition with the actual line inclusion. |
| [P 944–947](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L944-L947), local action equation after quotienting | [`gluedNormalizerQuotientCharacter_local`](Normalizer/NormalizerSheaf.lean#L220) | The constructed quotient character recovers the prescribed coefficient on every local normalizer lift under the actual sheaf-cokernel projection. |

## NormalizerTensorKernel

| Public source / mathematical role | Lean theorem | Exact coverage |
|---|---|---|
| [P 938–939](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L938-L939), tensor-valued normalizer kernel | [`normalizerTensorBracketMap_evaluation`](Normalizer/NormalizerTensorKernel.lean#L36) | Contracting the tensor-valued bracket by canonical evaluation recovers the original Hom-valued bracket. |
| [P 938–939](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L938-L939), tensor-valued normalizer kernel | [`normalizerTensorBracketMap_projection`](Normalizer/NormalizerTensorKernel.lean#L45) | The tensor bracket after the ambient cokernel projection is the original bracket transported by the proved target isomorphism. |
| [P 938–939](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L938-L939), tensor-valued normalizer kernel | [`normalizerTensorBracketMap_apply`](Normalizer/NormalizerTensorKernel.lean#L55) | Contracting on a local line section gives the projected actual commutator, including the original sign. |
| [P 938–939](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L938-L939), tensor-valued normalizer kernel | [`normalizerTensorQuotientKernelIso_hom_ι`](Normalizer/NormalizerTensorKernel.lean#L91) | The tensor-kernel isomorphism identifies its kernel inclusion with the actual descended N/I -> G map. |
| [P 938–939](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L938-L939), tensor-valued normalizer kernel | [`normalizerTensorQuotientKernelIso_projection`](Normalizer/NormalizerTensorKernel.lean#L108) | The tensor-kernel identification commutes with the original normalizer inclusion and ambient quotient projection. |

## Obstruction

| Public source / mathematical role | Lean theorem | Exact coverage |
|---|---|---|
| [P 985–990](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L985-L990); [A 66–68](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/LOAD_BEARING_AUDIT.md#L66-L68) | [`sem_no_three`](Normalizer/Obstruction.lean#L31) | Coordinate proof: finrank at least 3 forces the whole sl2 model, contradicted by [E12,E21] ≠ 0. |
| [P 1008–1035](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L1008-L1035); [A 78–82](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/LOAD_BEARING_AUDIT.md#L78-L82) | [`nil_dimension_le_two`](Normalizer/Obstruction.lean#L57) | Alternative proof of the same obstruction by injective coordinate projections. It proves finrank ≤ 2 without assuming the manuscript’s abelian-plane classification. |
| [P 1008–1035](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L1008-L1035) | [`nil_no_three`](Normalizer/Obstruction.lean#L103) | Immediate dimension-<3 form of nil_dimension_le_two. |

## Quotients

| Public source / mathematical role | Lean theorem | Exact coverage |
|---|---|---|
| [P 937–947](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L937-L947); [A 39–43](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/LOAD_BEARING_AUDIT.md#L39-L43) | [`mem_lineNormalizer`](Normalizer/Quotients.lean#L25) | Actual matrix normalizer membership: trace zero and a scalar action on the specified line. |
| [P 985–987](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L985-L987); presentation infrastructure | [`sem_coordinates_lift`](Normalizer/Quotients.lean#L41) | Semisimple coordinates recover the quotient vector independently of its line lift. |
| [P 992–997](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L992-L997); presentation infrastructure | [`nil_coordinates_lift`](Normalizer/Quotients.lean#L45) | Minimal coordinates recover the quotient vector independently of its line lift. |
| [P 985–987](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L985-L987); presentation infrastructure | [`sem_projection_surjective`](Normalizer/Quotients.lean#L55) | All three semisimple quotient coordinates are realized by actual normalizer matrices. |
| [P 992–997](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L992-L997); presentation infrastructure | [`nil_projection_surjective`](Normalizer/Quotients.lean#L63) | All four minimal quotient coordinates are realized by actual normalizer matrices. |
| [P 937–942](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L937-L942), 985–987 | [`sem_projection_kernel`](Normalizer/Quotients.lean#L72) | Projection kernel is exactly the distinguished scalar line; quotient is not an unrelated coordinate definition. |
| [P 937–942](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L937-L942), 992–997 | [`nil_projection_kernel`](Normalizer/Quotients.lean#L87) | Projection kernel is exactly F E12. |
| [P 980–987](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L980-L987); [A 63–68](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/LOAD_BEARING_AUDIT.md#L63-L68) | [`sem_quotient_finrank`](Normalizer/Quotients.lean#L112) | The actual semisimple normalizer modulo its line has dimension 3. |
| [P 980–997](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L980-L997); [A 63–73](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/LOAD_BEARING_AUDIT.md#L63-L73) | [`nil_quotient_finrank`](Normalizer/Quotients.lean#L114) | The actual minimal normalizer modulo its line has dimension 4. |
| [P 937–942](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L937-L942), 985–987 | [`sem_projection_bracket`](Normalizer/Quotients.lean#L118) | Matrix commutators project to semBracket for all normalizer representatives. |
| [P 937–942](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L937-L942), 1003–1006 | [`nil_projection_bracket`](Normalizer/Quotients.lean#L129) | Matrix commutators project to nilBracket for all normalizer representatives. |
| [P 944–947](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L944-L947), 985–987 | [`sem_projection_character`](Normalizer/Quotients.lean#L140) | Any scalar action on the distinguished line is zero. |
| [P 944–947](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L944-L947), 999–1002 | [`nil_projection_character`](Normalizer/Quotients.lean#L146) | Any scalar action on E12 equals the quotient D-coordinate. |
| [P 985–987](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L985-L987); semisimple model | [`sem_frameCharacter`](Normalizer/Quotients.lean#L158) | The constructed character equals zero for the specified matrix. |
| [P 999–1002](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L999-L1002); minimal model | [`nil_frameCharacter`](Normalizer/Quotients.lean#L171) | It equals the specified D-coordinate. |

## RestrictionStalks

| Public source / mathematical role | Lean theorem | Exact coverage |
|---|---|---|
| Restriction local-ring support for [P 936](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L936) | [`restrictionLocalRingEquiv_germ`](Normalizer/RestrictionStalks.lean#L23) | The actual local-ring isomorphism under an open immersion has the prescribed formula on germs using the actual section-ring isomorphism. |
| Restriction module-stalk support for [P 936](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L936) | [`restrictionStalkAddIso_germ`](Normalizer/RestrictionStalks.lean#L43) | The actual additive stalk identification under open restriction has the prescribed section-germ formula. |
| Free-stalk restriction supporting [P 936](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L936) | [`restrictionStalk_free`](Normalizer/RestrictionStalks.lean#L72) | A free actual stalk stays free under open restriction, transported semilinearly through the actual local-ring isomorphism. |

## SheafBoundary

| Public source / mathematical role | Lean theorem | Exact coverage |
|---|---|---|
| E1/E2, use of H⁰(E)=0 | [`sheaf_global_map_zero_of_vanishing`](Normalizer/SheafBoundary.lean#L21) | Vanishing of the actual global-section vector space makes the induced global morphism zero. |
| Alternative descent proof of [P 952–970](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L952-L970) | [`sheaf_boundary_law_of_overlaps`](Normalizer/SheafBoundary.lean#L30) | Actual sheaf gluing and separatedness give the global relation from local lifts and the overlap law, provided the global image of E in G is zero. This is a consequence of H⁰(E)=0; the general injective-boundary case still requires the geometric exactness input. |

## SheafFinitePresentation

| Public source / mathematical role | Lean theorem | Exact coverage |
|---|---|---|
| Actual finite-presentation support for [P 936](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L936) | [`sheafPresentation_isFinitePresentation`](Normalizer/SheafFinitePresentation.lean#L25) | An actual finite global sheaf presentation supplies mathlib's actual local finite-presentation property. |
| Affine finite-presentation support for [P 936](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L936) | [`presentationTilde_isFinite`](Normalizer/SheafFinitePresentation.lean#L42) | Finite module generators and relations remain finite in the actual global presentation of the associated sheaf. |
| Affine finite-presentation support for [P 936](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L936) | [`tilde_isFinitePresentation`](Normalizer/SheafFinitePresentation.lean#L58) | A finitely presented module gives an actual finitely presented associated sheaf. |
| Affine-section finite-presentation support for [P 936](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L936) | [`affinePresentation_sections_finitePresentation`](Normalizer/SheafFinitePresentation.lean#L69) | An actual finite global affine sheaf presentation yields finitely presented global sections by reconstructing a finite module cokernel and its sheaf isomorphism. No arbitrary right exactness of global sections is assumed. |
| Affine-cover refinement supporting [P 936](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L936) | [`exists_affineOpenCover_finitePresentation`](Normalizer/SheafFinitePresentation.lean#L101) | Mathlib's local finite-presentation property yields an actual affine open cover with actual finite global presentations on its restrictions. |

## SheafFreeNeighborhood

| Public source / mathematical role | Lean theorem | Exact coverage |
|---|---|---|
| General pointwise local-freeness interface underlying [P 936](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L936) and [P 941](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L941) | [`sheafStalk_exists_finiteFree_neighborhood`](Normalizer/SheafFreeNeighborhood.lean#L23) | For any actual scheme module with mathlib finite presentation and a free actual stalk at x, constructs an affine open immersion whose image contains x and an isomorphism of the actual restricted sheaf to a finite free sheaf. |

## SheafOperationDescent

| Public source / mathematical role | Lean theorem | Exact coverage |
|---|---|---|
| Support for [P 941–942](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L941-L942) and 952–956, checking local identities | [`sheaf_eq_of_local_lifts`](Normalizer/SheafOperationDescent.lean#L69) | Equality in any target module sheaf can be checked on a constructed cover of simultaneous lifts of three sections. Uses intersections of covering image sieves. |
| Support for [P 941–942](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L941-L942), actual gluing | [`descendSheafOperation_local`](Normalizer/SheafOperationDescent.lean#L134) | A natural binary operation constant on fibres of a locally surjective map glues to a section, with the required value on every pair of local representatives. |
| Support for [P 941–942](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L941-L942), projection formula | [`descendSheafOperation_projection`](Normalizer/SheafOperationDescent.lean#L148) | The glued operation recovers its prescribed value on the images of two representatives. |
| Support for [P 941–942](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L941-L942), restriction law | [`descendSheafOperation_restrict`](Normalizer/SheafOperationDescent.lean#L157) | The glued operation commutes with restrictions for arbitrary target sections. |
| Support for [P 941–942](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L941-L942), uniqueness | [`descendSheafOperation_unique`](Normalizer/SheafOperationDescent.lean#L177) | Recovery on all local representatives uniquely determines the glued section. |

## SheafQuotientBracket

| Public source / mathematical role | Lean theorem | Exact coverage |
|---|---|---|
| Support for [P 941–942](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L941-L942) and 952–956, quotient representatives | [`sheaf_cokernel_section_exact`](Normalizer/SheafQuotientBracket.lean#L26) | For any monomorphism of actual module sheaves, a section killed by its cokernel projection has a preimage in the original subsheaf on that same open. Derived using preservation of kernels by evaluation. |
| Support for [P 952–956](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L952-L956), existence of local lifts | [`sheaf_cokernel_locallySurjective`](Normalizer/SheafQuotientBracket.lean#L71) | Any actual sheaf-cokernel projection is locally surjective. Compared with sheafification of the presheaf cokernel. Does not assert lifts on every prescribed affine open. |
| [P 941–942](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L941-L942), line inclusion | [`normalizerLineInclusion_mono`](Normalizer/SheafQuotientBracket.lean#L102) | The constructed inclusion of the abelian subsheaf into its normalizer is monic. |
| [P 941–942](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L941-L942), kernel of quotient projection | [`normalizerQuotient_zero_iff`](Normalizer/SheafQuotientBracket.lean#L111) | A normalizer section maps to zero exactly when its ambient section belongs to the line subsheaf on that open. |
| [P 952–956](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L952-L956), differences of lifts | [`normalizerQuotient_eq_iff`](Normalizer/SheafQuotientBracket.lean#L129) | Two normalizer sections have equal quotient images exactly when their difference belongs to the line subsheaf. |
| [P 941–942](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L941-L942), bracket restrictions | [`normalizerSectionBracket_restrict`](Normalizer/SheafQuotientBracket.lean#L151) | The actual normalizer-section bracket commutes with restrictions. |
| [P 941–942](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L941-L942), well-defined quotient bracket | [`normalizerQuotient_bracket_independent`](Normalizer/SheafQuotientBracket.lean#L164) | The projected bracket is independent of both representatives in the actual quotient sheaf, using skew symmetry and the normalizer property. |
| [P 941–942](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L941-L942), quotient bracket | [`normalizerQuotientBracket_projection`](Normalizer/SheafQuotientBracket.lean#L225) | The constructed bracket on actual quotient sections satisfies `[π(x),π(y)] = π([x,y])`. |
| [P 941–942](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L941-L942), sheaf compatibility | [`normalizerQuotientBracket_restrict`](Normalizer/SheafQuotientBracket.lean#L235) | The constructed quotient bracket commutes with restriction for all quotient sections, without assuming they lift on the full open. |

## SheafQuotientLie

| Public source / mathematical role | Lean theorem | Exact coverage |
|---|---|---|
| [P 941–942](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L941-L942), Lie bracket | [`normalizerQuotientBracket_skew`](Normalizer/SheafQuotientLie.lean#L50) | Skew symmetry of the actual quotient operation follows by local lifting. |
| [P 941–942](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L941-L942), Lie bracket | [`normalizerQuotientBracket_add_left`](Normalizer/SheafQuotientLie.lean#L64) | Additivity in the first argument on arbitrary quotient sections. |
| [P 941–942](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L941-L942), Lie bracket | [`normalizerQuotientBracket_add_right`](Normalizer/SheafQuotientLie.lean#L83) | Additivity in the second argument, derived from the proved skew law. |
| [P 941–942](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L941-L942), O-bilinearity | [`normalizerQuotientBracket_smul_left`](Normalizer/SheafQuotientLie.lean#L92) | Scalar linearity in the first argument over each section ring; restrictions of scalars are respected in the local proof. |
| [P 941–942](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L941-L942), O-bilinearity | [`normalizerQuotientBracket_smul_right`](Normalizer/SheafQuotientLie.lean#L109) | Scalar linearity in the second argument, derived from the proved skew law. |
| [P 941–942](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L941-L942), Lie bracket | [`normalizerQuotientBracket_alternating`](Normalizer/SheafQuotientLie.lean#L120) | Ambient alternation gives alternation on arbitrary quotient sections, with no characteristic restriction. |
| [P 941–942](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L941-L942), Lie bracket | [`normalizerQuotientBracket_jacobi`](Normalizer/SheafQuotientLie.lean#L131) | Jacobi on the quotient follows on a common cover of three local representatives. |
| [P 941–942](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L941-L942), sheaf restrictions | [`normalizerQuotientLieRestriction_apply`](Normalizer/SheafQuotientLie.lean#L194) | The bundled Lie homomorphism acts exactly as the actual sheaf restriction. |
| [P 941–942](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L941-L942), sheaf restrictions | [`normalizerQuotientLieRestriction_id`](Normalizer/SheafQuotientLie.lean#L200) | Bundled restrictions preserve identity maps. |
| [P 941–942](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L941-L942), sheaf restrictions | [`normalizerQuotientLieRestriction_comp`](Normalizer/SheafQuotientLie.lean#L211) | Bundled restrictions compose as the actual sheaf restrictions do. |
| [P 944–947](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L944-L947), grading character | [`sectionFrameCharacter_bracket`](Normalizer/SheafQuotientLie.lean#L234) | In a genuine frame the character kills brackets, since Jacobi gives the commutator of two scalar multiplications. |
| [P 944–947](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L944-L947), grading character | [`quotientCharacterOfTrivializations_projected_bracket`](Normalizer/SheafQuotientLie.lean#L254) | The actual sheaf character kills projected normalizer brackets on every open, using the cover of genuine trivializations. |
| [P 944–947](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L944-L947), grading character | [`quotientCharacterOfTrivializations_bracket`](Normalizer/SheafQuotientLie.lean#L282) | The actual quotient character kills brackets of arbitrary quotient sections, without assuming global representatives. |
| [P 944–947](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L944-L947), Lie-character bundling | [`quotientCharacterLieHom_apply`](Normalizer/SheafQuotientLie.lean#L323) | The bundled Lie-algebra homomorphism agrees with the original sheaf character on every section. |

## SheafStalkMap

| Public source / mathematical role | Lean theorem | Exact coverage |
|---|---|---|
| Actual stalk-map support for [P 936](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L936) | [`schemeModuleStalkMap_germ`](Normalizer/SheafStalkMap.lean#L37) | The constructed local-ring-linear stalk map takes an actual germ to the germ of its image under the sheaf morphism. |

## SheafifyLocalIso

| Public source / mathematical role | Lean theorem | Exact coverage |
|---|---|---|
| Support for [P 938](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L938), local-to-global sheaf argument | [`modulePresheaf_locallyInjective_of_cover`](Normalizer/SheafifyLocalIso.lean#L23) | Injectivity on every subopen of a genuine cover gives local injectivity; the source need not be separated. |
| Support for [P 938](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L938), local-to-global sheaf argument | [`modulePresheaf_locallySurjective_of_cover`](Normalizer/SheafifyLocalIso.lean#L38) | Surjectivity on every subopen of a genuine cover gives local surjectivity. |
| Support for [P 938](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L938), local-to-global sheaf argument | [`sheafificationLift_isIso_of_locallyBijective`](Normalizer/SheafifyLocalIso.lean#L50) | A locally bijective presheaf map to a sheaf induces an isomorphism from its actual sheafification. |
| Support for [P 938](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L938), local-to-global sheaf argument | [`sheafificationLift_isIso_of_cover`](Normalizer/SheafifyLocalIso.lean#L72) | Bijectivity on a genuine cover and its subopens proves that the actual sheafification lift is invertible globally. |

## SlTwo

| Public source / mathematical role | Lean theorem | Exact coverage |
|---|---|---|
| [P 985–987](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L985-L987) | [`slTwo_bracket`](Normalizer/SlTwo.lean#L29) | The coordinate equivalence to mathlib SpecialLinear.sl (Fin 2) F preserves the bracket. |
| [P 985–987](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L985-L987) | [`sem_quotient_slTwo_bracket`](Normalizer/SlTwo.lean#L41) | The actual quotient’s linear equivalence to mathlib sl2 preserves the bracket. |

## StalkLocalFreeness

| Public source / mathematical role | Lean theorem | Exact coverage |
|---|---|---|
| Local-ring support for [P 936](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L936) | [`principalIdealRing_of_regularLocal_dim_le_one`](Normalizer/StalkLocalFreeness.lean#L21) | A regular local domain with Krull dimension at most one is a principal ideal ring; includes fields. Smoothness is not assumed to imply regularity here. |
| Affine finite-stalk support for [P 936](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L936) | [`affinePresentation_stalk_finite`](Normalizer/StalkLocalFreeness.lean#L32) | A finite global presentation of an actual affine sheaf gives finite actual stalks over the actual local rings. |
| Finite-stalk support for [P 936](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L936) | [`sheaf_stalk_finite_of_finitePresentation`](Normalizer/StalkLocalFreeness.lean#L45) | An actual finitely presented scheme module sheaf has finite actual stalks, using finite affine presentations and the actual semilinear restriction equivalence. |
| Local-freeness support for [P 936](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L936) and [P 941](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L941) | [`sheaf_isLocallyFree_of_torsionFree_stalks`](Normalizer/StalkLocalFreeness.lean#L64) | On an integral scheme with actual principal ideal local rings, actual finite presentation and torsion-free stalks imply IsLocallyFree. |
| Kernel saturation support for [P 941](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L941) | [`kernelCokernel_isLocallyFree`](Normalizer/StalkLocalFreeness.lean#L79) | The actual quotient by a sheaf kernel is locally free under explicit quotient finite presentation, principal ideal local rings on an integral scheme, and torsion-free target stalks. Does not automatically prove the kernel itself locally free. |
| Regular dimension-one criterion underlying [P 936](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L936) | [`sheaf_isLocallyFree_of_regular_stalks`](Normalizer/StalkLocalFreeness.lean#L91) | On an integral scheme with regular actual local rings of dimension at most one, actual finite presentation and torsion-free stalks imply IsLocallyFree. The curve must still supply these hypotheses. |

## TrivializedCharacter

| Public source / mathematical role | Lean theorem | Exact coverage |
|---|---|---|
| Support for [P 944–947](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L944-L947), local frame restrictions | [`lineTrivializationAt_restrict`](Normalizer/TrivializedCharacter.lean#L32) | Evaluated basis isomorphisms commute with restriction by naturality of the actual sheaf trivialization. |
| [P 944–947](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L944-L947), scalar action equation | [`sectionFrameCharacter_action`](Normalizer/TrivializedCharacter.lean#L62) | The coefficient constructed using the inverse basis map acts on the frame by the stated scalar. |
| [P 944–947](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L944-L947), uniqueness of the coefficient | [`sectionFrameCharacter_unique`](Normalizer/TrivializedCharacter.lean#L72) | Injectivity of the actual basis isomorphism proves uniqueness. |
| [P 944–947](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L944-L947), action on the entire line | [`sectionFrameCharacter_action_all`](Normalizer/TrivializedCharacter.lean#L90) | Scalar-linearity and commutativity give the same action coefficient on every line section. |
| Support for [P 944–947](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L944-L947), frame independence | [`sectionFrameCharacter_independent`](Normalizer/TrivializedCharacter.lean#L103) | Any two basis isomorphisms give the same coefficient; transition coefficients are not inputs. |
| Support for [P 944–947](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L944-L947), restriction compatibility | [`trivializationCharacter_restrict`](Normalizer/TrivializedCharacter.lean#L124) | The derived local character commutes with actual restriction maps. |
| Support for [P 944–947](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L944-L947), overlap compatibility | [`trivializationCharacter_agree`](Normalizer/TrivializedCharacter.lean#L152) | Characters from two genuine trivializations agree on each common subopen. |
| [P 942–947](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L942-L947), vanishing on the line | [`trivializationCharacter_kills_line`](Normalizer/TrivializedCharacter.lean#L167) | The computed coefficient vanishes on the abelian line subsheaf. |
| [P 944–947](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L944-L947), quotient character on local lifts | [`quotientCharacterOfTrivializations_local`](Normalizer/TrivializedCharacter.lean#L204) | The actual sheaf quotient character evaluates to the computed local coefficient on each normalizer lift. |
| [P 944–947](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L944-L947), character action equation | [`quotientCharacterOfTrivializations_action`](Normalizer/TrivializedCharacter.lean#L214) | The constructed quotient character acts by its scalar on every local line section, using the actual cokernel projection. |
| [P 941–942](https://github.com/Robby955/rank-three-mcg-finiteness/blob/12f81e2852e0a8e71f16777d9eb9c7bc8916e6df/manuscript/rank3_genus5_reader.tex#L941-L942), abelian line | [`lineSubsheaf_abelian_of_trivializations`](Normalizer/TrivializedCharacter.lean#L242) | Rank-one trivializations, alternation and scalar-linearity imply abelianness on all opens by sheaf separatedness. |

## Audited constructions

These definitions and abbreviations provide the objects and maps used by
the theorems above. Their types and implementations are linked directly.

| Declaration | Kind | Module |
|---|---|---|
| [`affineLocalizationMap`](Normalizer/AffineFreeNeighborhood.lean#L17) | `def` | AffineFreeNeighborhood |
| [`affineLocalizationSheaf`](Normalizer/AffineFreeNeighborhood.lean#L25) | `def` | AffineFreeNeighborhood |
| [`affineLocalizationSections`](Normalizer/AffineFreeNeighborhood.lean#L36) | `def` | AffineFreeNeighborhood |
| [`affineLocalizationToSections`](Normalizer/AffineFreeNeighborhood.lean#L62) | `def` | AffineFreeNeighborhood |
| [`affineLocalizationSectionsIso`](Normalizer/AffineFreeNeighborhood.lean#L74) | `def` | AffineFreeNeighborhood |
| [`affineTildeRestrictionIso`](Normalizer/AffineFreeNeighborhood.lean#L87) | `def` | AffineFreeNeighborhood |
| [`affineLocalizationFreeSheafIso`](Normalizer/AffineFreeNeighborhood.lean#L101) | `def` | AffineFreeNeighborhood |
| [`affineFreeSheafIso`](Normalizer/AffineLocallyFree.lean#L19) | `def` | AffineLocallyFree |
| [`affineCokernelIso`](Normalizer/AffineQuotient.lean#L20) | `def` | AffineQuotient |
| [`affineSubmoduleQuotientIso`](Normalizer/AffineQuotient.lean#L57) | `def` | AffineQuotient |
| [`affineStalkAlgebra`](Normalizer/AffineStalks.lean#L18) | `def` | AffineStalks |
| [`semQuotientBracket`](Normalizer/Flagship.lean#L10) | `def` | Flagship |
| [`nilQuotientBracket`](Normalizer/Flagship.lean#L14) | `def` | Flagship |
| [`nilCharacter`](Normalizer/Flagship.lean#L17) | `def` | Flagship |
| [`frameLine`](Normalizer/FrameCharacter.lean#L13) | `def` | FrameCharacter |
| [`frameCharacter`](Normalizer/FrameCharacter.lean#L56) | `def` | FrameCharacter |
| [`frameIdeal`](Normalizer/FrameCharacter.lean#L100) | `def` | FrameCharacter |
| [`quotientFrameCharacter`](Normalizer/FrameCharacter.lean#L126) | `def` | FrameCharacter |
| [`frameNormalizerMap`](Normalizer/FrameCharacter.lean#L213) | `def` | FrameCharacter |
| [`frameQuotientMap`](Normalizer/FrameCharacter.lean#L238) | `def` | FrameCharacter |
| [`schemeModuleStalkModule`](Normalizer/IntegralSheafTorsion.lean#L24) | `def` | IntegralSheafTorsion |
| [`kernelQuotientProjection`](Normalizer/KernelQuotient.lean#L21) | `def` | KernelQuotient |
| [`kernelQuotientIso`](Normalizer/KernelQuotient.lean#L68) | `def` | KernelQuotient |
| [`kernelQuotientIsoOfKernel`](Normalizer/KernelQuotient.lean#L116) | `def` | KernelQuotient |
| [`kernelCokernelToTarget`](Normalizer/KernelSaturation.lean#L31) | `def` | KernelSaturation |
| [`kernelTargetIso`](Normalizer/KernelTargetIso.lean#L19) | `def` | KernelTargetIso |
| [`lineSheafTensorEvalAt`](Normalizer/LineSheafTensor.lean#L103) | `def` | LineSheafTensor |
| [`moduleHomSectionEval`](Normalizer/LineSheafTensor.lean#L122) | `def` | LineSheafTensor |
| [`moduleHomSectionEquiv`](Normalizer/LineSheafTensor.lean#L140) | `def` | LineSheafTensor |
| [`lineSheafTensorEvalPresheaf`](Normalizer/LineSheafTensor.lean#L170) | `def` | LineSheafTensor |
| [`lineSheafTensorEval`](Normalizer/LineSheafTensor.lean#L262) | `def` | LineSheafTensor |
| [`lineSheafTensorIso`](Normalizer/LineSheafTensor.lean#L296) | `def` | LineSheafTensor |
| [`tensorHomEval`](Normalizer/LineTensor.lean#L19) | `def` | LineTensor |
| [`lineTensorHomInv`](Normalizer/LineTensor.lean#L43) | `def` | LineTensor |
| [`lineTensorHomEquiv`](Normalizer/LineTensor.lean#L71) | `def` | LineTensor |
| [`glueLocalModuleMorphisms`](Normalizer/LocalCharacterGluing.lean#L119) | `def` | LocalCharacterGluing |
| [`openImmersionOverFreeIso`](Normalizer/LocallyFreeAssembly.lean#L16) | `def` | LocallyFreeAssembly |
| [`freeCoverLocalGeneratorsData`](Normalizer/LocallyFreeAssembly.lean#L37) | `def` | LocallyFreeAssembly |
| [`localGeneratorsDataOfIso`](Normalizer/LocallyFreeTransport.lean#L24) | `def` | LocallyFreeTransport |
| [`Mat`](Normalizer/Matrices.lean#L11) | `abbrev` | Matrices |
| [`comm`](Normalizer/Matrices.lean#L13) | `def` | Matrices |
| [`semM`](Normalizer/Matrices.lean#L14) | `def` | Matrices |
| [`nilM`](Normalizer/Matrices.lean#L15) | `def` | Matrices |
| [`semLift`](Normalizer/Matrices.lean#L18) | `def` | Matrices |
| [`nilLift`](Normalizer/Matrices.lean#L22) | `def` | Matrices |
| [`semBracket`](Normalizer/Matrices.lean#L26) | `def` | Matrices |
| [`nilBracket`](Normalizer/Matrices.lean#L30) | `def` | Matrices |
| [`moduleLineFrameAt`](Normalizer/ModuleHomLine.lean#L18) | `def` | ModuleHomLine |
| [`moduleHomFrameEquiv`](Normalizer/ModuleHomLine.lean#L94) | `def` | ModuleHomLine |
| [`moduleHomSheaf`](Normalizer/ModuleSheafHom.lean#L171) | `def` | ModuleSheafHom |
| [`moduleHomEval`](Normalizer/ModuleSheafHom.lean#L182) | `def` | ModuleSheafHom |
| [`moduleHomMk`](Normalizer/ModuleSheafHom.lean#L190) | `def` | ModuleSheafHom |
| [`moduleHomOverEquiv`](Normalizer/ModuleSheafHom.lean#L276) | `def` | ModuleSheafHom |
| [`moduleSectionCommRing`](Normalizer/ModuleSheafTensor.lean#L20) | `def` | ModuleSheafTensor |
| [`moduleTensorPresheaf`](Normalizer/ModuleSheafTensor.lean#L32) | `def` | ModuleSheafTensor |
| [`moduleTensorSheaf`](Normalizer/ModuleSheafTensor.lean#L37) | `def` | ModuleSheafTensor |
| [`moduleTensorProjection`](Normalizer/ModuleSheafTensor.lean#L42) | `def` | ModuleSheafTensor |
| [`moduleTensorHomEquiv`](Normalizer/ModuleSheafTensor.lean#L48) | `def` | ModuleSheafTensor |
| [`moduleTensorLift`](Normalizer/ModuleSheafTensor.lean#L54) | `def` | ModuleSheafTensor |
| [`moduleTensorPresheafPure`](Normalizer/ModuleSheafTensor.lean#L80) | `def` | ModuleSheafTensor |
| [`moduleTensorPure`](Normalizer/ModuleSheafTensor.lean#L87) | `def` | ModuleSheafTensor |
| [`ambientQuotientSheaf`](Normalizer/NormalizerKernel.lean#L19) | `def` | NormalizerKernel |
| [`ambientQuotientProjection`](Normalizer/NormalizerKernel.lean#L22) | `def` | NormalizerKernel |
| [`normalizerBracketMap`](Normalizer/NormalizerKernel.lean#L141) | `def` | NormalizerKernel |
| [`normalizerBracketIsKernel`](Normalizer/NormalizerKernel.lean#L215) | `def` | NormalizerKernel |
| [`ambientQuotientBracketMap`](Normalizer/NormalizerKernel.lean#L235) | `def` | NormalizerKernel |
| [`normalizerQuotientKernelIso`](Normalizer/NormalizerKernel.lean#L269) | `def` | NormalizerKernel |
| [`normalizerQuotientToAmbient`](Normalizer/NormalizerKernel.lean#L305) | `def` | NormalizerKernel |
| [`normalizerSubsheaf`](Normalizer/NormalizerSheaf.lean#L45) | `def` | NormalizerSheaf |
| [`normalizerLineInclusion`](Normalizer/NormalizerSheaf.lean#L119) | `def` | NormalizerSheaf |
| [`normalizerQuotientSheaf`](Normalizer/NormalizerSheaf.lean#L126) | `def` | NormalizerSheaf |
| [`descendNormalizerCharacter`](Normalizer/NormalizerSheaf.lean#L131) | `def` | NormalizerSheaf |
| [`gluedNormalizerCharacter`](Normalizer/NormalizerSheaf.lean#L187) | `def` | NormalizerSheaf |
| [`gluedNormalizerQuotientCharacter`](Normalizer/NormalizerSheaf.lean#L208) | `def` | NormalizerSheaf |
| [`normalizerTensorBracketMap`](Normalizer/NormalizerTensorKernel.lean#L27) | `def` | NormalizerTensorKernel |
| [`normalizerTensorQuotientKernelIso`](Normalizer/NormalizerTensorKernel.lean#L79) | `def` | NormalizerTensorKernel |
| [`BoundaryLaw`](Normalizer/Obstruction.lean#L9) | `def` | Obstruction |
| [`rightAdjoint`](Normalizer/Quotients.lean#L8) | `def` | Quotients |
| [`lineNormalizer`](Normalizer/Quotients.lean#L20) | `def` | Quotients |
| [`semCoordinates`](Normalizer/Quotients.lean#L31) | `def` | Quotients |
| [`nilCoordinates`](Normalizer/Quotients.lean#L36) | `def` | Quotients |
| [`semProjection`](Normalizer/Quotients.lean#L49) | `def` | Quotients |
| [`nilProjection`](Normalizer/Quotients.lean#L52) | `def` | Quotients |
| [`SemQuotient`](Normalizer/Quotients.lean#L102) | `abbrev` | Quotients |
| [`NilQuotient`](Normalizer/Quotients.lean#L104) | `abbrev` | Quotients |
| [`semQuotientEquiv`](Normalizer/Quotients.lean#L107) | `def` | Quotients |
| [`nilQuotientEquiv`](Normalizer/Quotients.lean#L109) | `def` | Quotients |
| [`restrictionLocalRingEquiv`](Normalizer/RestrictionStalks.lean#L18) | `def` | RestrictionStalks |
| [`restrictionStalkAddIso`](Normalizer/RestrictionStalks.lean#L38) | `def` | RestrictionStalks |
| [`restrictionStalkEquiv`](Normalizer/RestrictionStalks.lean#L53) | `def` | RestrictionStalks |
| [`descendSheafOperation`](Normalizer/SheafOperationDescent.lean#L125) | `def` | SheafOperationDescent |
| [`normalizerSectionBracket`](Normalizer/SheafQuotientBracket.lean#L144) | `def` | SheafQuotientBracket |
| [`normalizerQuotientBracket`](Normalizer/SheafQuotientBracket.lean#L215) | `def` | SheafQuotientBracket |
| [`normalizerQuotientLieRing`](Normalizer/SheafQuotientLie.lean#L151) | `def` | SheafQuotientLie |
| [`normalizerQuotientLieAlgebra`](Normalizer/SheafQuotientLie.lean#L169) | `def` | SheafQuotientLie |
| [`normalizerQuotientLieRestriction`](Normalizer/SheafQuotientLie.lean#L182) | `def` | SheafQuotientLie |
| [`quotientCharacterLieHom`](Normalizer/SheafQuotientLie.lean#L302) | `def` | SheafQuotientLie |
| [`schemeModuleStalkMap`](Normalizer/SheafStalkMap.lean#L16) | `def` | SheafStalkMap |
| [`schemeModuleStalkIso`](Normalizer/SheafStalkMap.lean#L45) | `def` | SheafStalkMap |
| [`slTwoEquiv`](Normalizer/SlTwo.lean#L8) | `def` | SlTwo |
| [`semQuotientSlTwoEquiv`](Normalizer/SlTwo.lean#L37) | `def` | SlTwo |
| [`lineTrivializationAt`](Normalizer/TrivializedCharacter.lean#L24) | `def` | TrivializedCharacter |
| [`sectionFrameCharacter`](Normalizer/TrivializedCharacter.lean#L51) | `def` | TrivializedCharacter |
| [`trivializationCharacter`](Normalizer/TrivializedCharacter.lean#L115) | `def` | TrivializedCharacter |
| [`normalizerCharacterOfTrivializations`](Normalizer/TrivializedCharacter.lean#L183) | `def` | TrivializedCharacter |
| [`quotientCharacterOfTrivializations`](Normalizer/TrivializedCharacter.lean#L193) | `def` | TrivializedCharacter |
| [`lineQuotientCharacter`](Normalizer/TrivializedCharacter.lean#L261) | `def` | TrivializedCharacter |
