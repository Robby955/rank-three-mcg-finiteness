import Normalizer.SectionCokernelSections
import Normalizer.SheafQuotientBracket
import Normalizer.ModuleSheafCohomologyScalars
import Mathlib.RingTheory.Finiteness.Finsupp

/-! Finiteness of actual line-bundle global sections on proper integral curves
with a specified nonzero section, using exactness at the middle term only. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Normalizer
open CategoryTheory AlgebraicGeometry Limits Opposite

universe u
variable {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]
  (L : X.Modules) (s : Γ(L, ⊤)) (hs : s ≠ 0)
  (p : X ⟶ Spec (.of k))
  (hlocal : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
    Nonempty ((SheafOfModules.unit X.ringCatSheaf).over U ≅ L.over U))

include hs hlocal

/-- The actual global-section sequence is exact at the line's section space.
This does not assert surjectivity onto global sections of the sheaf cokernel. -/
theorem sectionCokernel_globalSections_ker_eq_range :
    let := schemeGlobalSectionsModuleOfMorphism p (SheafOfModules.unit X.ringCatSheaf)
    let := schemeGlobalSectionsModuleOfMorphism p L
    let := schemeGlobalSectionsModuleOfMorphism p (cokernel (schemeSectionHom L s))
    LinearMap.ker (schemeGlobalSectionsMap p (cokernel.π (schemeSectionHom L s))) =
      LinearMap.range (schemeGlobalSectionsMap p (schemeSectionHom L s)) := by
  let := schemeGlobalSectionsModuleOfMorphism p (SheafOfModules.unit X.ringCatSheaf)
  let := schemeGlobalSectionsModuleOfMorphism p L
  let := schemeGlobalSectionsModuleOfMorphism p (cokernel (schemeSectionHom L s))
  have := schemeSectionHom_mono L s hs hlocal
  ext t
  constructor
  · intro ht
    exact sheaf_cokernel_section_exact (schemeSectionHom L s) (op ⊤) t ht
  · rintro ⟨a, rfl⟩
    have hz := congrArg
      (fun q : SheafOfModules.unit X.ringCatSheaf ⟶ cokernel (schemeSectionHom L s) =>
        q.val.app (op ⊤) a) (cokernel.condition (schemeSectionHom L s))
    exact hz

/-- On a proper integral curve over an algebraically closed field, a genuine
line bundle with a nonzero global section has finite-dimensional actual global
sections. Neither H¹ finiteness nor sectionwise surjectivity is an input. -/
theorem properCurve_lineSections_finite [IsAlgClosed k] [IsProper p]
    (hdim : topologicalKrullDim X ≤ 1) :
    let := schemeGlobalSectionsModuleOfMorphism p L
    Module.Finite k Γ(L, ⊤) := by
  let := schemeGlobalSectionsModuleOfMorphism p (SheafOfModules.unit X.ringCatSheaf)
  let := schemeGlobalSectionsModuleOfMorphism p L
  let := schemeGlobalSectionsModuleOfMorphism p (cokernel (schemeSectionHom L s))
  have hO : Module.Finite k Γ(SheafOfModules.unit X.ringCatSheaf, ⊤) :=
    RingHom.Finite.of_surjective (schemeConstantMap p)
      (schemeConstantMap_bijective p).surjective
  have hQ := properCurve_sectionLineCokernelSections_finite L s hs p hdim hlocal
  let f := schemeGlobalSectionsMap p (schemeSectionHom L s)
  let g := schemeGlobalSectionsMap p (cokernel.π (schemeSectionHom L s))
  have heq : g.ker = f.range := sectionCokernel_globalSections_ker_eq_range L s hs p hlocal
  refine ⟨(⊤ : Submodule k Γ(L, ⊤)).fg_of_fg_map_of_fg_inf_ker g ?_ ?_⟩
  · exact IsNoetherian.noetherian (Submodule.map g ⊤)
  · rw [top_inf_eq, heq]
    exact Submodule.fg_range f


omit hs in
/-- Every genuine line bundle on a proper integral curve over an algebraically
closed field has finite-dimensional actual global sections. A nonzero section
is not an input: when none exists the section space is zero. -/
theorem properCurve_lineSections_finite_of_lineCharts [IsAlgClosed k] [IsProper p]
    (hdim : topologicalKrullDim X ≤ 1) :
    let := schemeGlobalSectionsModuleOfMorphism p L
    Module.Finite k Γ(L, ⊤) := by
  classical
  let := schemeGlobalSectionsModuleOfMorphism p L
  by_cases hex : ∃ t : Γ(L, ⊤), t ≠ 0
  · obtain ⟨t, ht⟩ := hex
    exact properCurve_lineSections_finite L t ht p hlocal hdim
  · have hzero (t : Γ(L, ⊤)) : t = 0 := by
      by_contra ht
      exact hex ⟨t, ht⟩
    have : Subsingleton Γ(L, ⊤) := ⟨fun a b => (hzero a).trans (hzero b).symm⟩
    infer_instance


omit hs in
/-- Actual H⁰ of a genuine line bundle on a proper integral curve is finite
for the cohomology scalar action induced by the actual structure morphism. -/
theorem properCurve_lineH0_finite_of_lineCharts [IsAlgClosed k] [IsProper p]
    (hdim : topologicalKrullDim X ≤ 1) :
    let := schemeModuleCohomologyModule p L 0
    Module.Finite k (CategoryTheory.Sheaf.H ((schemeModulesToAbelianSheaves X).obj L) 0) := by
  let := schemeModuleCohomologyModule p L 0
  let := schemeGlobalSectionsModuleOfMorphism p L
  have := properCurve_lineSections_finite_of_lineCharts L p hlocal hdim
  exact Module.Finite.equiv (schemeModuleCohomologyEquiv₀ p L).symm

end Normalizer
