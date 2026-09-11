import Normalizer.SectionCokernelCohomology
import Normalizer.ModuleAbelianPushforward
import Normalizer.SheafQuotientBracket
import Normalizer.DiscreteSheafCohomology
import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences

/-! The actual section sequence remains short exact after forgetting module
structure, and yields the usual exact sequence of actual sheaf cohomology. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Normalizer
open CategoryTheory Limits AlgebraicGeometry
universe u v

/-- The actual forgetful functor is additive. -/
theorem schemeModulesToAbelianSheaves_additive (X : Scheme.{u}) :
    (schemeModulesToAbelianSheaves X).Additive := by
  change (SheafOfModules.toSheaf X.ringCatSheaf).Additive
  infer_instance

/-- The actual forgetful functor preserves finite limits. -/
theorem schemeModulesToAbelianSheaves_preservesFiniteLimits (X : Scheme.{u}) :
    PreservesFiniteLimits (schemeModulesToAbelianSheaves X) := by
  change PreservesFiniteLimits (SheafOfModules.toSheaf X.ringCatSheaf)
  infer_instance

attribute [local instance] schemeModulesToAbelianSheaves_additive
  schemeModulesToAbelianSheaves_preservesFiniteLimits

/-- Forgetting module structure preserves epimorphisms: cokernel projections
are locally surjective and every epimorphism is its coimage projection
followed by an isomorphism. -/
theorem schemeModulesToAbelianSheaves_map_epi {X : Scheme.{u}}
    {A B : X.Modules} (f : A ⟶ B) [Epi f] :
    Epi ((schemeModulesToAbelianSheaves X).map f) := by
  let T := schemeModulesToAbelianSheaves X
  have hπ : Epi (T.map (Abelian.coimage.π f)) :=
    (Sheaf.isLocallySurjective_iff_epi' _ _).mp
      (sheaf_cokernel_locallySurjective (kernel.ι f))
  rw [← Abelian.coimage.fac f, Functor.map_comp]
  exact epi_comp (T.map (Abelian.coimage.π f)) (T.map (Abelian.factorThruCoimage f))

/-- The actual module-to-abelian-sheaf forgetful functor preserves epis. -/
theorem schemeModulesToAbelianSheaves_preservesEpimorphisms (X : Scheme.{u}) :
    (schemeModulesToAbelianSheaves X).PreservesEpimorphisms where
  preserves f _ := schemeModulesToAbelianSheaves_map_epi f

/-- Forgetting module structure preserves homology, hence exactness. -/
theorem schemeModulesToAbelianSheaves_preservesHomology (X : Scheme.{u}) :
    (schemeModulesToAbelianSheaves X).PreservesHomology := by
  have := schemeModulesToAbelianSheaves_preservesEpimorphisms X
  exact Functor.preservesHomology_of_preservesEpis_and_kernels _

/-- Every actual short exact sequence of scheme-module sheaves gives a
short exact sequence of its actual underlying abelian sheaves. -/
theorem schemeModulesToAbelianSheaves_shortExact {X : Scheme.{u}}
    (S : ShortComplex X.Modules) (hS : S.ShortExact) :
    (S.map (schemeModulesToAbelianSheaves X)).ShortExact := by
  have := schemeModulesToAbelianSheaves_preservesHomology X
  have := schemeModulesToAbelianSheaves_preservesEpimorphisms X
  have := hS.mono_f
  have := hS.epi_g
  exact hS.map _

variable {X : Scheme.{u}} (L : X.Modules) (s : Γ(L, ⊤))
  {ι : Type v} [Finite ι] (U : ι → X.Opens) [∀ a, QuasiCompact (U a).ι]
  (e : ∀ a, (SheafOfModules.unit X.ringCatSheaf).over (U a) ≅ L.over (U a))
  (hU : iSup U = ⊤)

/-- The actual sequence O → L → i_*i^*L, with its actual section and
restriction maps, remains short exact as abelian sheaves. -/
theorem schemeSectionLineAbelianComplex_shortExact [IsIntegral X] (hs : s ≠ 0) :
    ((schemeSectionLineComplex L s U e hU).map
      (schemeModulesToAbelianSheaves X)).ShortExact :=
  schemeModulesToAbelianSheaves_shortExact _
    (schemeSectionLineComplex_shortExact L s U e hU hs)

/-- The canonical connecting map of the actual section short exact
sequence, defined by its extension class. -/
def schemeSectionLineCohomologyδ [IsIntegral X] (hs : s ≠ 0) :
    Sheaf.H ((schemeModulesToAbelianSheaves X).obj
      (schemeSectionLineRestrictionSheaf L s U e hU)) 0 →+
      Sheaf.H ((schemeModulesToAbelianSheaves X).obj
        (SheafOfModules.unit X.ringCatSheaf)) 1 :=
  (schemeSectionLineAbelianComplex_shortExact L s U e hU hs).extClass.postcomp
    ((constantSheaf (Opens.grothendieckTopology X)
      AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift ℤ))) (by rfl)

/-- The six-object segment H⁰(O) → H⁰(L) → H⁰(i_*i^*L) → H¹(O)
→ H¹(L) → H¹(i_*i^*L), with the actual section and restriction maps. -/
def schemeSectionLineCohomologySequence [IsIntegral X] (hs : s ≠ 0) :
    ComposableArrows AddCommGrpCat.{u} 5 :=
  ComposableArrows.mk₅
    (AddCommGrpCat.ofHom (Sheaf.H.map
      ((schemeModulesToAbelianSheaves X).map (schemeSectionHom L s)) 0))
    (AddCommGrpCat.ofHom (Sheaf.H.map
      ((schemeModulesToAbelianSheaves X).map
        (schemeSectionLineRestrictionMap L s U e hU)) 0))
    (AddCommGrpCat.ofHom (schemeSectionLineCohomologyδ L s U e hU hs))
    (AddCommGrpCat.ofHom (Sheaf.H.map
      ((schemeModulesToAbelianSheaves X).map (schemeSectionHom L s)) 1))
    (AddCommGrpCat.ofHom (Sheaf.H.map
      ((schemeModulesToAbelianSheaves X).map
        (schemeSectionLineRestrictionMap L s U e hU)) 1))

/-- The actual six-object sheaf-cohomology segment is exact at its four
interior terms. This assertion does not assume cohomology finiteness. -/
theorem schemeSectionLineCohomologySequence_exact [IsIntegral X] (hs : s ≠ 0) :
    (schemeSectionLineCohomologySequence L s U e hU hs).Exact :=
  Abelian.Ext.covariantSequence_exact
    ((constantSheaf (Opens.grothendieckTopology X)
      AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift ℤ)))
    (schemeSectionLineAbelianComplex_shortExact L s U e hU hs) 0 1 rfl

include U e hU in
/-- The actual first map on H⁰ is injective, as required at the left
endpoint of the section cohomology sequence. -/
theorem schemeSectionLine_H0_injective [IsIntegral X] (hs : s ≠ 0) :
    Function.Injective (Sheaf.H.map
      ((schemeModulesToAbelianSheaves X).map (schemeSectionHom L s)) 0) := by
  have : Mono ((schemeModulesToAbelianSheaves X).map (schemeSectionHom L s)) :=
    (schemeSectionLineAbelianComplex_shortExact L s U e hU hs).mono_f
  exact Abelian.Ext.postcomp_mk₀_injective_of_mono _ _

include U e hU in
/-- On a finite-type integral curve the actual H¹ section map is
surjective, because the actual line-restriction quotient has vanishing H¹. -/
theorem schemeSectionLine_H1_surjective [IsIntegral X] (hs : s ≠ 0)
    {k : Type u} [Field k] (p : X ⟶ Spec (.of k))
    [LocallyOfFiniteType p] [QuasiCompact p] (hdim : topologicalKrullDim X ≤ 1) :
    Function.Surjective (Sheaf.H.map
      ((schemeModulesToAbelianSheaves X).map (schemeSectionHom L s)) 1) := by
  have hcharts : ∀ x : X, ∃ W : X.Opens, x ∈ W ∧
      Nonempty ((SheafOfModules.unit X.ringCatSheaf).over W ≅ L.over W) := by
    intro x
    have hx : x ∈ iSup U := by rw [hU]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    exact ⟨U i, hi, ⟨e i⟩⟩
  have hg := (lineSheaf_genericGerm_ne_zero_iff L hcharts s).mpr hs
  have := schemeSectionLineRestriction_positiveCohomology_subsingleton
    L s U e hU hg p hdim 0
  have hz : ∀ z : Sheaf.H ((schemeModulesToAbelianSheaves X).obj
      (schemeSectionLineRestrictionSheaf L s U e hU)) 1, z = 0 :=
    fun z => Subsingleton.elim z 0
  intro y
  exact Abelian.Ext.covariant_sequence_exact₂ _
    (schemeSectionLineAbelianComplex_shortExact L s U e hU hs) y
    (hz _)

end Normalizer
