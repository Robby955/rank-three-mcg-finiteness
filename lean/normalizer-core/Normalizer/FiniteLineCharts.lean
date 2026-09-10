import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.Topology.Sets.OpenCover

/-! Finite genuine line charts derived from pointwise trivializations,
with quasi-compact inclusions on a noetherian scheme. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Normalizer
open CategoryTheory AlgebraicGeometry TopologicalSpace
universe u
variable {X : Scheme.{u}} (L : X.Modules)

/-- Compactness extracts finitely many genuine charts from pointwise local
line triviality, without assuming a finite cover. -/
theorem exists_finite_lineCharts [CompactSpace X]
    (hlocal : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      Nonempty ((SheafOfModules.unit X.ringCatSheaf).over U ≅ L.over U)) :
    ∃ (t : Finset X) (U : t → X.Opens), iSup U = ⊤ ∧
      Nonempty (∀ i, (SheafOfModules.unit X.ringCatSheaf).over (U i) ≅ L.over (U i)) := by
  classical
  choose U hx he using hlocal
  have hU : IsOpenCover U := by
    apply IsOpenCover.mk
    apply top_unique
    intro x _
    exact Opens.mem_iSup.mpr ⟨x, hx x⟩
  obtain ⟨t, ht⟩ := hU.exists_finite_of_compactSpace
  exact ⟨t, (fun i ↦ U i.val), ht.iSup_eq_top, ⟨fun i ↦ (he i.val).some⟩⟩

/-- On a noetherian scheme the finite genuine line charts have quasi-compact
inclusions, as required by the actual ideal-sheaf gluing construction. -/
theorem exists_finite_quasiCompact_lineCharts [IsNoetherian X]
    (hlocal : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      Nonempty ((SheafOfModules.unit X.ringCatSheaf).over U ≅ L.over U)) :
    ∃ (t : Finset X) (U : t → X.Opens), iSup U = ⊤ ∧
      (∀ i, QuasiCompact (U i).ι) ∧
      Nonempty (∀ i, (SheafOfModules.unit X.ringCatSheaf).over (U i) ≅ L.over (U i)) := by
  obtain ⟨t, U, hU, he⟩ := exists_finite_lineCharts L hlocal
  exact ⟨t, U, hU, fun _ ↦ inferInstance, he⟩

end Normalizer
