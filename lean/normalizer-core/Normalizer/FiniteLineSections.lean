import Normalizer.DiscreteLineTrivialization
import Normalizer.FiniteSchemeCohomology
import Normalizer.ProperTrivialEvaluation
import Normalizer.LineRestrictionComparison

/-! Sections of a genuine line bundle on an actual finite scheme over a field
have the same dimension as its global functions. The global trivialization is
constructed from pointwise bundle charts, including on nonreduced schemes. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Normalizer
open CategoryTheory AlgebraicGeometry

universe u
variable {k : Type u} [Field k] {Y : Scheme.{u}}
  (p : Y ⟶ Spec (.of k)) [IsFinite p] (L : Y.Modules)
  (hlocal : ∀ y : Y, ∃ U : Y.Opens, y ∈ U ∧
    Nonempty ((SheafOfModules.unit Y.ringCatSheaf).over U ≅ L.over U))

/-- A line bundle on a finite scheme is globally trivial. Discreteness is
obtained from the actual finite structure morphism and charts are glued. -/
def finiteLineSheafIso : SheafOfModules.unit Y.ringCatSheaf ≅ L := by
  have := finiteScheme_discreteTopology p
  exact discreteLineSheafIso L hlocal

/-- The constructed line trivialization gives an equivalence between actual
sections and global functions, linear for the specified base-field actions. -/
def finiteLineSectionsEquiv :
    letI := schemeGlobalSectionsModuleOfMorphism p L
    letI := schemeGlobalFunctionsAlgebra p
    Γ(L, ⊤) ≃ₗ[k] Γ(Y, ⊤) := by
  letI := schemeGlobalSectionsModuleOfMorphism p L
  letI := schemeGlobalFunctionsAlgebra p
  exact schemeGlobalSectionsIso p (finiteLineSheafIso p L hlocal).symm

include hlocal in
/-- Actual sections of a genuine line bundle on a finite scheme form a finite
module over the base field. -/
theorem finiteLineSections_finite :
    let := schemeGlobalSectionsModuleOfMorphism p L
    Module.Finite k Γ(L, ⊤) := by
  let := schemeGlobalSectionsModuleOfMorphism p L
  let := schemeGlobalFunctionsAlgebra p
  have := finiteScheme_globalFunctions_finite p
  exact Module.Finite.equiv (finiteLineSectionsEquiv p L hlocal).symm

include hlocal in
/-- The line's actual section dimension equals the dimension of actual global
functions; no dimension comparison is supplied as a hypothesis. -/
theorem finiteLineSections_finrank_eq :
    let := schemeGlobalSectionsModuleOfMorphism p L
    let := schemeGlobalFunctionsAlgebra p
    Module.finrank k Γ(L, ⊤) = Module.finrank k Γ(Y, ⊤) := by
  let := schemeGlobalSectionsModuleOfMorphism p L
  let := schemeGlobalFunctionsAlgebra p
  exact (finiteLineSectionsEquiv p L hlocal).finrank_eq

include hlocal in
/-- A line bundle on a nonempty finite scheme has positive section dimension. -/
theorem finiteLineSections_finrank_pos [Nonempty Y] :
    let := schemeGlobalSectionsModuleOfMorphism p L
    0 < Module.finrank k Γ(L, ⊤) := by
  let := schemeGlobalSectionsModuleOfMorphism p L
  change 0 < Module.finrank k Γ(L, ⊤)
  rw [finiteLineSections_finrank_eq p L hlocal]
  exact finiteScheme_globalFunctions_finrank_pos p

include hlocal in
/-- Zero section dimension of a line bundle on a finite scheme detects exactly
when the actual scheme is empty. -/
theorem finiteLineSections_finrank_eq_zero_iff :
    let := schemeGlobalSectionsModuleOfMorphism p L
    Module.finrank k Γ(L, ⊤) = 0 ↔ IsEmpty Y := by
  let := schemeGlobalSectionsModuleOfMorphism p L
  change Module.finrank k Γ(L, ⊤) = 0 ↔ IsEmpty Y
  rw [finiteLineSections_finrank_eq p L hlocal]
  exact finiteScheme_globalFunctions_finrank_eq_zero_iff p

variable {X : Scheme.{u}}

/-- Pointwise line charts pull back along an arbitrary actual scheme morphism. -/
theorem schemePullback_lineCharts (i : Y ⟶ X) (M : X.Modules)
    (hM : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      Nonempty ((SheafOfModules.unit X.ringCatSheaf).over U ≅ M.over U)) :
    ∀ y : Y, ∃ V : Y.Opens, y ∈ V ∧
      Nonempty ((SheafOfModules.unit Y.ringCatSheaf).over V ≅
        ((Scheme.Modules.pullback i).obj M).over V) := by
  intro y
  obtain ⟨U, hy, ⟨e⟩⟩ := hM (i y)
  exact ⟨i ⁻¹ᵁ U, hy, ⟨schemePullbackLineChart i M U e⟩⟩

/-- Restricting a genuine line bundle to an actual finite scheme preserves the
section-dimension formula, using the constructed pullback line charts. -/
theorem finitePullbackLineSections_finrank_eq (i : Y ⟶ X) (M : X.Modules)
    (hM : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      Nonempty ((SheafOfModules.unit X.ringCatSheaf).over U ≅ M.over U)) :
    let := schemeGlobalSectionsModuleOfMorphism p ((Scheme.Modules.pullback i).obj M)
    let := schemeGlobalFunctionsAlgebra p
    Module.finrank k Γ((Scheme.Modules.pullback i).obj M, ⊤) =
      Module.finrank k Γ(Y, ⊤) :=
  finiteLineSections_finrank_eq p _ (schemePullback_lineCharts i M hM)

end Normalizer
