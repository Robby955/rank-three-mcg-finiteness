import Normalizer.FiniteLineSections
import Normalizer.ModulePushforwardSections
import Normalizer.SectionLineExact
import Normalizer.SectionZeroFinite
import Normalizer.ModuleSheafCohomologyScalars
import Normalizer.SectionCokernelCohomology

/-! Actual global sections of the specified line-section cokernel are compared
with functions on its constructed zero scheme over the actual base field. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Normalizer
open CategoryTheory AlgebraicGeometry Limits
universe u v
variable {k : Type u} [Field k] {X : Scheme.{u}}
  (L : X.Modules) (s : Γ(L, ⊤))
  {ι : Type v} [Finite ι] (U : ι → X.Opens) [∀ a, QuasiCompact (U a).ι]
  (e : ∀ a, (SheafOfModules.unit X.ringCatSheaf).over (U a) ≅ L.over (U a))
  (hU : iSup U = ⊤)

include U e hU in
omit [Finite ι] [∀ a, QuasiCompact (U a).ι] in
private theorem lineCharts_from_cover : ∀ x : X, ∃ W : X.Opens, x ∈ W ∧
    Nonempty ((SheafOfModules.unit X.ringCatSheaf).over W ≅ L.over W) := by
  intro x
  have hx : x ∈ iSup U := by rw [hU]; trivial
  obtain ⟨a, ha⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  exact ⟨U a, ha, ⟨e a⟩⟩

local notation "D" => schemeSectionZeroScheme (schemeSectionDualEvaluation L s)
  U (fun a => schemeDualLineFrameIso L (e a)) hU
local notation "iD" => schemeSectionZeroSchemeι (schemeSectionDualEvaluation L s)
  U (fun a => schemeDualLineFrameIso L (e a)) hU
local notation "Q" => cokernel (schemeSectionHom L s)

/-- The actual cokernel's global sections agree over the base field with
sections of the actual line restricted to its constructed zero scheme. -/
def schemeSectionLineCokernelSectionsEquiv (p : X ⟶ Spec (.of k)) :
    letI := schemeGlobalSectionsModuleOfMorphism p Q
    letI := schemeGlobalSectionsModuleOfMorphism (iD ≫ p) ((Scheme.Modules.pullback iD).obj L)
    Γ(Q, ⊤) ≃ₗ[k] Γ((Scheme.Modules.pullback iD).obj L, ⊤) := by
  letI := schemeGlobalSectionsModuleOfMorphism p Q
  letI := schemeGlobalSectionsModuleOfMorphism (iD ≫ p) ((Scheme.Modules.pullback iD).obj L)
  letI := schemeGlobalSectionsModuleOfMorphism p (schemeSectionLineRestrictionSheaf L s U e hU)
  exact (schemeGlobalSectionsIso p (schemeSectionLineCokernelIso L s U e hU)).trans
    (schemeModulePushforwardGlobalSectionsEquiv iD p _)

variable [IsIntegral X] (hs : s ≠ 0)
  (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p] [QuasiCompact p]
  (hdim : topologicalKrullDim X ≤ 1)

/-- Actual cokernel sections are linearly equivalent to functions on the
actual zero scheme. Finiteness and the restricted line's trivialization
are constructed from the curve and genuine line charts. -/
def schemeSectionLineCokernelFunctionsEquiv :
    letI := schemeGlobalSectionsModuleOfMorphism p Q
    letI := schemeGlobalFunctionsAlgebra (iD ≫ p)
    Γ(Q, ⊤) ≃ₗ[k] Γ(D, ⊤) := by
  letI := schemeGlobalSectionsModuleOfMorphism p Q
  letI := schemeGlobalFunctionsAlgebra (iD ≫ p)
  letI := schemeGlobalSectionsModuleOfMorphism (iD ≫ p) ((Scheme.Modules.pullback iD).obj L)
  have := schemeSectionZeroScheme_isFinite_of_ne_zero L s U hU e hs p hdim
  exact (schemeSectionLineCokernelSectionsEquiv L s U e hU p).trans
    (finiteLineSectionsEquiv (iD ≫ p) _
      (schemePullback_lineCharts iD L (lineCharts_from_cover L U e hU)))

include U e hU hs hdim in
/-- The actual cokernel has a finite-dimensional space of global sections. -/
theorem schemeSectionLineCokernelSections_finite :
    letI := schemeGlobalSectionsModuleOfMorphism p Q
    Module.Finite k Γ(Q, ⊤) := by
  let := schemeGlobalSectionsModuleOfMorphism p Q
  let := schemeGlobalFunctionsAlgebra (iD ≫ p)
  have := schemeSectionZeroScheme_isFinite_of_ne_zero L s U hU e hs p hdim
  have := finiteScheme_globalFunctions_finite (iD ≫ p)
  exact Module.Finite.equiv (schemeSectionLineCokernelFunctionsEquiv L s U e hU hs p hdim).symm

include hs hdim in
/-- The actual cokernel section dimension equals the actual zero-scheme
function dimension under their structure-morphism scalar actions. -/
theorem schemeSectionLineCokernelSections_finrank_eq :
    letI := schemeGlobalSectionsModuleOfMorphism p Q
    letI := schemeGlobalFunctionsAlgebra (iD ≫ p)
    Module.finrank k Γ(Q, ⊤) = Module.finrank k Γ(D, ⊤) := by
  let := schemeGlobalSectionsModuleOfMorphism p Q
  let := schemeGlobalFunctionsAlgebra (iD ≫ p)
  exact (schemeSectionLineCokernelFunctionsEquiv L s U e hU hs p hdim).finrank_eq

include hs hdim in
/-- The actual section cokernel has zero global-section dimension exactly
when its constructed zero scheme is empty. -/
theorem schemeSectionLineCokernelSections_finrank_eq_zero_iff :
    letI := schemeGlobalSectionsModuleOfMorphism p Q
    Module.finrank k Γ(Q, ⊤) = 0 ↔ IsEmpty D := by
  let := schemeGlobalSectionsModuleOfMorphism p Q
  change Module.finrank k Γ(Q, ⊤) = 0 ↔ IsEmpty D
  rw [schemeSectionLineCokernelSections_finrank_eq L s U e hU hs p hdim]
  have := schemeSectionZeroScheme_isFinite_of_ne_zero L s U hU e hs p hdim
  exact finiteScheme_globalFunctions_finrank_eq_zero_iff (iD ≫ p)

include hU hs hdim in
/-- A zero of the specified nonzero section forces positive dimension of the
actual cokernel's sections. The zero is tested by its nonunit local germ. -/
theorem schemeSectionLineCokernelSections_pos_of_zero (a : ι)
    (V : X.Opens) (h : V ≤ U a) (x : X) (hx : x ∈ V)
    (hz : ¬ IsUnit (X.presheaf.germ V x hx (sectionLocalEquation L s (e a) V h))) :
    letI := schemeGlobalSectionsModuleOfMorphism p Q
    0 < Module.finrank k Γ(Q, ⊤) := by
  let := schemeGlobalSectionsModuleOfMorphism p Q
  change 0 < Module.finrank k Γ(Q, ⊤)
  rw [schemeSectionLineCokernelSections_finrank_eq L s U e hU hs p hdim]
  exact schemeSectionZeroScheme_globalFunctions_pos_of_ne_zero L s U hU e hs p hdim
    a V h x hx hz

include hs hdim in
omit [LocallyOfFiniteType p] [QuasiCompact p] in
/-- Proper curve hypotheses and genuine pointwise charts construct finite
actual cokernel sections, without supplying a finite cover or generic germ. -/
theorem properCurve_sectionLineCokernelSections_finite [IsProper p]
    (hlocal : ∀ x : X, ∃ W : X.Opens, x ∈ W ∧
      Nonempty ((SheafOfModules.unit X.ringCatSheaf).over W ≅ L.over W)) :
    letI := schemeGlobalSectionsModuleOfMorphism p Q
    Module.Finite k Γ(Q, ⊤) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  have : IsNoetherian X := {}
  obtain ⟨t, V, hV, hQC, ⟨eV⟩⟩ := exists_finite_quasiCompact_lineCharts L hlocal
  let := hQC
  exact schemeSectionLineCokernelSections_finite L s V eV hV hs p hdim

/-- Degree-zero cohomology of the actual cokernel is linearly equivalent to
functions on the actual zero scheme under the geometrically induced scalars. -/
def schemeSectionLineCokernelH0FunctionsEquiv :
    letI := schemeModuleCohomologyModule p Q 0
    letI := schemeGlobalFunctionsAlgebra (iD ≫ p)
    CategoryTheory.Sheaf.H ((schemeModulesToAbelianSheaves X).obj Q) 0 ≃ₗ[k]
      Γ(D, ⊤) := by
  letI := schemeModuleCohomologyModule p Q 0
  letI := schemeGlobalSectionsModuleOfMorphism p Q
  letI := schemeGlobalFunctionsAlgebra (iD ≫ p)
  exact (schemeModuleCohomologyEquiv₀ p Q).trans
    (schemeSectionLineCokernelFunctionsEquiv L s U e hU hs p hdim)

include hs hdim in
/-- Actual H⁰ of the section cokernel has the actual zero-scheme function
dimension. This is the zero-dimensional quotient term for Euler additivity. -/
theorem schemeSectionLineCokernelH0_finrank_eq :
    letI := schemeModuleCohomologyModule p Q 0
    letI := schemeGlobalFunctionsAlgebra (iD ≫ p)
    Module.finrank k (CategoryTheory.Sheaf.H ((schemeModulesToAbelianSheaves X).obj Q) 0) =
      Module.finrank k Γ(D, ⊤) := by
  let := schemeModuleCohomologyModule p Q 0
  let := schemeGlobalFunctionsAlgebra (iD ≫ p)
  exact (schemeSectionLineCokernelH0FunctionsEquiv L s U e hU hs p hdim).finrank_eq

include hU hs hdim in
/-- A zero of the prescribed nonzero section gives positive dimension of
actual H⁰ of its actual cokernel, with all scalar structures constructed. -/
theorem schemeSectionLineCokernelH0_pos_of_zero (a : ι)
    (V : X.Opens) (h : V ≤ U a) (x : X) (hx : x ∈ V)
    (hz : ¬ IsUnit (X.presheaf.germ V x hx (sectionLocalEquation L s (e a) V h))) :
    letI := schemeModuleCohomologyModule p Q 0
    0 < Module.finrank k (CategoryTheory.Sheaf.H ((schemeModulesToAbelianSheaves X).obj Q) 0) := by
  let := schemeModuleCohomologyModule p Q 0
  change 0 < Module.finrank k (CategoryTheory.Sheaf.H ((schemeModulesToAbelianSheaves X).obj Q) 0)
  rw [schemeSectionLineCokernelH0_finrank_eq L s U e hU hs p hdim]
  exact schemeSectionZeroScheme_globalFunctions_pos_of_ne_zero L s U hU e hs p hdim
    a V h x hx hz

include hs hdim in
omit [LocallyOfFiniteType p] [QuasiCompact p] in
/-- Every actual cohomology group of the section cokernel on a proper
integral curve is finite over the base field. Degree zero uses constructed
finite-zero-scheme sections; positive degrees use proved ambient vanishing. -/
theorem properCurve_sectionLineCokernel_cohomology_finite [IsProper p]
    (hlocal : ∀ x : X, ∃ W : X.Opens, x ∈ W ∧
      Nonempty ((SheafOfModules.unit X.ringCatSheaf).over W ≅ L.over W)) (a : ℕ) :
    letI := schemeModuleCohomologyModule p Q a
    Module.Finite k (CategoryTheory.Sheaf.H ((schemeModulesToAbelianSheaves X).obj Q) a) := by
  cases a with
  | zero =>
    let := schemeModuleCohomologyModule p Q 0
    let := schemeGlobalSectionsModuleOfMorphism p Q
    have := properCurve_sectionLineCokernelSections_finite L s hs p hdim hlocal
    exact Module.Finite.equiv (schemeModuleCohomologyEquiv₀ p Q).symm
  | succ a =>
    let := schemeModuleCohomologyModule p Q (a + 1)
    have := properCurve_sectionLineCokernel_positiveCohomology_subsingleton
      L s p hdim hs hlocal a
    infer_instance

include hdim in
omit [LocallyOfFiniteType p] [QuasiCompact p] in
/-- The specified determinant cokernel has finite-dimensional actual
cohomology. Genuine rank-n charts construct the line, and independence of
the actual generic germs proves the required section is nonzero. -/
theorem properCurve_determinantCokernel_cohomology_finite [IsProper p]
    (H : X.Modules) (n : ℕ) (t : Fin n → Γ(H, ⊤))
    {I : Type u} [Fintype I] (j : I ≃ Fin n)
    (hcharts : ∀ x : X, ∃ W : X.Opens, x ∈ W ∧
      Nonempty ((schemeTrivialBundle X I).over W ≅ H.over W))
    (ht : LinearIndependent X.functionField
      (fun b => H.presheaf.germ ⊤ (genericPoint X) (by trivial) (t b))) (a : ℕ) :
    letI := schemeModuleCohomologyModule p
      (cokernel (schemeSectionHom (schemeExteriorSheaf H n)
        (schemeExteriorGlobalSection H n t))) a
    Module.Finite k (CategoryTheory.Sheaf.H ((schemeModulesToAbelianSheaves X).obj
      (cokernel (schemeSectionHom (schemeExteriorSheaf H n)
        (schemeExteriorGlobalSection H n t)))) a) := by
  apply properCurve_sectionLineCokernel_cohomology_finite _ _
    (schemeExteriorGlobalSection_ne_zero H n t ht) p hdim
  intro x
  obtain ⟨W, hx, ⟨eW⟩⟩ := hcharts x
  exact ⟨W, hx, ⟨bundleTopExteriorSheafIsoOver j eW⟩⟩

end Normalizer
