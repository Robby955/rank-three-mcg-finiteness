import Normalizer.ClosedPushforwardCohomology
import Normalizer.ModuleAbelianPushforward
import Normalizer.FiniteSchemeCohomology
import Normalizer.LineGenericInjection

/-! Actual ambient cohomology of the specified-section cokernel.
The closed immersion and its finite source are constructed by the section. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Normalizer
open CategoryTheory AlgebraicGeometry

universe u v
variable {X Y : Scheme.{u}}

/-- Cohomology of actual module-sheaf direct image along a closed immersion,
computed on the underlying abelian sheaves, agrees with source cohomology. -/
def schemeClosedPushforwardCohomologyEquiv (i : Y ⟶ X) [IsClosedImmersion i]
    (F : Y.Modules) (n : ℕ) :
    CategoryTheory.Sheaf.H ((schemeModulesToAbelianSheaves X).obj
      ((Scheme.Modules.pushforward i).obj F)) n ≃+
    CategoryTheory.Sheaf.H ((schemeModulesToAbelianSheaves Y).obj F) n :=
  (((CategoryTheory.Sheaf.functorH _ n).mapIso
    ((schemeModuleAbelianPushforwardIso i).app F)).addCommGroupIsoToAddEquiv).trans
    (closedPushforwardCohomologyEquiv i.base i.isClosedEmbedding _ n)

/-- Direct image of an actual module sheaf on a finite closed subscheme
has vanishing ambient positive-degree cohomology. -/
theorem finiteClosedPushforward_positiveCohomology_subsingleton
    {k : Type u} [Field k] (i : Y ⟶ X) [IsClosedImmersion i]
    (p : Y ⟶ Spec (.of k)) [IsFinite p] (F : Y.Modules) (n : ℕ) :
    Subsingleton (CategoryTheory.Sheaf.H ((schemeModulesToAbelianSheaves X).obj
      ((Scheme.Modules.pushforward i).obj F)) (n + 1)) := by
  have := finiteScheme_positiveCohomology_subsingleton p
    ((schemeModulesToAbelianSheaves Y).obj F) n
  exact (schemeClosedPushforwardCohomologyEquiv i F (n + 1)).injective.subsingleton

variable (L : X.Modules) (s : Γ(L, ⊤))
  {ι : Type v} [Finite ι] (U : ι → X.Opens) [∀ a, QuasiCompact (U a).ι]
  (e : ∀ a, (SheafOfModules.unit X.ringCatSheaf).over (U a) ≅ L.over (U a))
  (hU : iSup U = ⊤)

/-- The actual section cokernel has the cohomology of the actual restricted
line bundle on the constructed zero scheme, in every degree. -/
def schemeSectionLineCokernelCohomologyEquiv (n : ℕ) :
    CategoryTheory.Sheaf.H ((schemeModulesToAbelianSheaves X).obj
      (Limits.cokernel (schemeSectionHom L s))) n ≃+
    CategoryTheory.Sheaf.H ((schemeModulesToAbelianSheaves
      (schemeSectionZeroScheme (schemeSectionDualEvaluation L s) U
        (fun a => schemeDualLineFrameIso L (e a)) hU)).obj
        ((Scheme.Modules.pullback
          (schemeSectionZeroSchemeι (schemeSectionDualEvaluation L s) U
            (fun a => schemeDualLineFrameIso L (e a)) hU)).obj L)) n := by
  have := schemeSectionZeroScheme_isClosedImmersion (schemeSectionDualEvaluation L s)
    U (fun a => schemeDualLineFrameIso L (e a)) hU
  exact (((CategoryTheory.Sheaf.functorH _ n).mapIso
    (schemeSectionLineCokernelAbelianIso L s U e hU)).addCommGroupIsoToAddEquiv).trans
    (closedPushforwardCohomologyEquiv _
      (schemeSectionZeroSchemeι (schemeSectionDualEvaluation L s) U
        (fun a => schemeDualLineFrameIso L (e a)) hU).isClosedEmbedding _ n)

variable [IsIntegral X]
  (hs : L.presheaf.germ ⊤ (genericPoint X) (by trivial) s ≠ 0)
  {k : Type u} [Field k]

include hs in
/-- Positive ambient cohomology of the actual line-restriction quotient
vanishes on a finite-type integral curve. Finiteness of its zero scheme is derived. -/
theorem schemeSectionLineRestriction_positiveCohomology_subsingleton
    (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p] [QuasiCompact p]
    (hdim : topologicalKrullDim X ≤ 1) (n : ℕ) :
    Subsingleton (CategoryTheory.Sheaf.H ((schemeModulesToAbelianSheaves X).obj
      (schemeSectionLineRestrictionSheaf L s U e hU)) (n + 1)) := by
  have := schemeSectionZeroScheme_isClosedImmersion (schemeSectionDualEvaluation L s)
    U (fun a => schemeDualLineFrameIso L (e a)) hU
  have := schemeSectionZeroScheme_isFinite L s hs U hU e p hdim
  exact finiteClosedPushforward_positiveCohomology_subsingleton
    (schemeSectionZeroSchemeι (schemeSectionDualEvaluation L s) U
      (fun a => schemeDualLineFrameIso L (e a)) hU)
    (schemeSectionZeroSchemeι (schemeSectionDualEvaluation L s) U
      (fun a => schemeDualLineFrameIso L (e a)) hU ≫ p) _ n

include hs U e hU in
/-- Positive ambient cohomology of the actual cokernel of the specified
section vanishes on a finite-type integral curve. -/
theorem schemeSectionLineCokernel_positiveCohomology_subsingleton
    (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p] [QuasiCompact p]
    (hdim : topologicalKrullDim X ≤ 1) (n : ℕ) :
    Subsingleton (CategoryTheory.Sheaf.H ((schemeModulesToAbelianSheaves X).obj
      (Limits.cokernel (schemeSectionHom L s))) (n + 1)) := by
  have := schemeSectionZeroScheme_positiveCohomology_subsingleton L s hs U hU e p hdim
    ((schemeModulesToAbelianSheaves _).obj
      ((Scheme.Modules.pullback
        (schemeSectionZeroSchemeι (schemeSectionDualEvaluation L s) U
          (fun a => schemeDualLineFrameIso L (e a)) hU)).obj L)) n
  exact (schemeSectionLineCokernelCohomologyEquiv L s U e hU (n + 1)).injective.subsingleton

/-- On a proper integral curve, a nonzero global line section has an
acyclic actual cokernel. Both the finite chart cover and generic nonzeroness
are derived from genuine pointwise line trivializations. -/
theorem properCurve_sectionLineCokernel_positiveCohomology_subsingleton
    (p : X ⟶ Spec (.of k)) [IsProper p] (hdim : topologicalKrullDim X ≤ 1)
    (hs0 : s ≠ 0)
    (hlocal : ∀ x : X, ∃ W : X.Opens, x ∈ W ∧
      Nonempty ((SheafOfModules.unit X.ringCatSheaf).over W ≅ L.over W)) (n : ℕ) :
    Subsingleton (CategoryTheory.Sheaf.H ((schemeModulesToAbelianSheaves X).obj
      (Limits.cokernel (schemeSectionHom L s))) (n + 1)) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  have : IsNoetherian X := {}
  obtain ⟨t, V, hV, hQC, ⟨eV⟩⟩ := exists_finite_quasiCompact_lineCharts L hlocal
  let := hQC
  exact schemeSectionLineCokernel_positiveCohomology_subsingleton L s V eV hV
    ((lineSheaf_genericGerm_ne_zero_iff L hlocal s).mpr hs0) p hdim n

/-- The specified determinant cokernel is acyclic on a proper integral curve.
Pointwise rank-n charts construct the exterior line charts, and independence
of the actual generic germs supplies nonzeroness of the specified section. -/
theorem properCurve_determinantCokernel_positiveCohomology_subsingleton
    (p : X ⟶ Spec (.of k)) [IsProper p] (hdim : topologicalKrullDim X ≤ 1)
    (H : X.Modules) (n : ℕ) (t : Fin n → Γ(H, ⊤))
    {I : Type u} [Fintype I] (j : I ≃ Fin n)
    (hcharts : ∀ x : X, ∃ W : X.Opens, x ∈ W ∧
      Nonempty ((schemeTrivialBundle X I).over W ≅ H.over W))
    (ht : LinearIndependent X.functionField
      (fun a => H.presheaf.germ ⊤ (genericPoint X) (by trivial) (t a))) (a : ℕ) :
    Subsingleton (CategoryTheory.Sheaf.H ((schemeModulesToAbelianSheaves X).obj
      (Limits.cokernel (schemeSectionHom (schemeExteriorSheaf H n)
        (schemeExteriorGlobalSection H n t)))) (a + 1)) := by
  apply properCurve_sectionLineCokernel_positiveCohomology_subsingleton _ _ p hdim
    (schemeExteriorGlobalSection_ne_zero H n t ht)
  intro x
  obtain ⟨W, hx, ⟨eW⟩⟩ := hcharts x
  exact ⟨W, hx, ⟨bundleTopExteriorSheafIsoOver j eW⟩⟩

end Normalizer
