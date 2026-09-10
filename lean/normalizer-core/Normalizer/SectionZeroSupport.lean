import Normalizer.SectionZeroScheme
import Normalizer.SectionDualEvaluation
import Normalizer.SectionLocalEquation
import Mathlib.Topology.GDelta.Basic

/-! Generic nonzeroness of a specified section excludes the generic point
from its actual closed zero subscheme. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Normalizer
open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
universe u v
variable {X : Scheme.{u}} [IsIntegral X] (L : X.Modules) (s : Γ(L, ⊤))
  (hs : L.presheaf.germ ⊤ (genericPoint X) (by trivial) s ≠ 0)

include hs in
/-- The actual local zero ideal of the specified section excludes the generic
point of every nonempty genuine line chart. -/
theorem schemeSectionImageIdealOn_genericPoint_not_mem {U : X.Opens} [Nonempty U]
    (e : (SheafOfModules.unit X.ringCatSheaf).over U ≅ L.over U) :
    genericPoint U.toScheme ∉
      (schemeSectionImageIdealOn (schemeSectionDualEvaluation L s)
        (schemeDualLineFrameIso L e)).support := by
  obtain ⟨V, hV, hxV, _⟩ := exists_isAffineOpen_mem_and_subset
    (X := U.toScheme) (x := genericPoint U.toScheme)
    (U := ⊤) (by trivial)
  intro hx
  have hz := (Scheme.IdealSheafData.mem_support_iff_of_mem (U := ⟨V, hV⟩) hxV).mp hx
  rw [U.toScheme.mem_zeroLocus_iff] at hz
  let a : Γ(U.toScheme, V) := sectionLocalEquation L s e (U.ι ''ᵁ V) (U.ι_image_le V)
  have ha : a ∈ (schemeSectionImageIdealOn (schemeSectionDualEvaluation L s)
      (schemeDualLineFrameIso L e)).ideal ⟨V, hV⟩ := by
    rw [schemeSectionImageIdealOn_ideal_eq_span]
    have he : schemeSectionImageEquation (schemeSectionDualEvaluation L s)
        (schemeDualLineFrameIso L e) (U.ι ''ᵁ V) (U.ι_image_le V) = a :=
      schemeSectionDualEvaluation_frame_one L s e _ _
    rw [he]
    exact Ideal.subset_span (Set.mem_singleton a)
  apply hz a ha
  rw [U.toScheme.mem_basicOpen a (genericPoint U.toScheme) hxV]
  apply isUnit_iff_ne_zero.mpr
  intro hzero
  have hazero : a = 0 := (germ_injective_of_isIntegral U.toScheme
    (genericPoint U.toScheme) hxV) (by simpa using hzero)
  let : Nonempty (U.ι ''ᵁ V) :=
    ⟨⟨(genericPoint U.toScheme).val, ⟨genericPoint U.toScheme, hxV, rfl⟩⟩⟩
  exact sectionLocalEquation_ne_zero L s e hs (U.ι ''ᵁ V) (U.ι_image_le V) hazero

variable {ι : Type v} [Finite ι] (U : ι → X.Opens)
  [∀ i, QuasiCompact (U i).ι] (hU : iSup U = ⊤)
  (e : ∀ i, (SheafOfModules.unit X.ringCatSheaf).over (U i) ≅ L.over (U i))

include hs in
/-- A section with nonzero generic germ has an actual zero ideal whose
support excludes the generic point; no support condition is assumed. -/
theorem schemeSectionZeroIdeal_genericPoint_not_mem :
    genericPoint X ∉
      (schemeSectionZeroIdeal (schemeSectionDualEvaluation L s) U
        (fun i ↦ schemeDualLineFrameIso L (e i)) hU).support := by
  have hxcover : genericPoint X ∈ iSup U := by rw [hU]; trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hxcover
  let : Nonempty (U i) := ⟨⟨genericPoint X, hi⟩⟩
  intro hx
  apply schemeSectionImageIdealOn_genericPoint_not_mem L s hs (e i)
  rw [← schemeSectionZeroIdeal_comap (schemeSectionDualEvaluation L s) U
    (fun i ↦ schemeDualLineFrameIso L (e i)) hU i,
    Scheme.IdealSheafData.support_comap]
  change (U i).ι (genericPoint (U i).toScheme) ∈
    (schemeSectionZeroIdeal (schemeSectionDualEvaluation L s) U
      (fun i ↦ schemeDualLineFrameIso L (e i)) hU).support
  rwa [genericPoint_eq_of_isOpenImmersion (U i).ι]

include hs in
/-- The generic point is not in the range of the actual zero-scheme immersion. -/
theorem schemeSectionZeroScheme_genericPoint_not_mem_range :
    genericPoint X ∉ Set.range (schemeSectionZeroSchemeι (schemeSectionDualEvaluation L s)
      U (fun i ↦ schemeDualLineFrameIso L (e i)) hU) := by
  change genericPoint X ∉ Set.range
    (schemeSectionZeroIdeal (schemeSectionDualEvaluation L s) U
      (fun i ↦ schemeDualLineFrameIso L (e i)) hU).subschemeι
  rw [Scheme.IdealSheafData.range_subschemeι]
  exact schemeSectionZeroIdeal_genericPoint_not_mem L s hs U hU e

include hs in
/-- The support of the actual zero ideal is a proper closed subset. -/
theorem schemeSectionZeroIdeal_support_ne_top :
    (schemeSectionZeroIdeal (schemeSectionDualEvaluation L s) U
      (fun i ↦ schemeDualLineFrameIso L (e i)) hU).support ≠ ⊤ := by
  intro he
  apply schemeSectionZeroIdeal_genericPoint_not_mem L s hs U hU e
  rw [he]
  trivial

include hs in
/-- The actual zero support has empty interior. -/
theorem schemeSectionZeroIdeal_support_interior_eq_empty :
    interior ((schemeSectionZeroIdeal (schemeSectionDualEvaluation L s) U
      (fun i ↦ schemeDualLineFrameIso L (e i)) hU).support : Set X) = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hg : genericPoint X ∈ interior
      ((schemeSectionZeroIdeal (schemeSectionDualEvaluation L s) U
        (fun i ↦ schemeDualLineFrameIso L (e i)) hU).support : Set X) :=
    ((genericPoint_spec X).mem_open_set_iff isOpen_interior).mpr (by
      exact ⟨x, trivial, hx⟩)
  exact schemeSectionZeroIdeal_genericPoint_not_mem L s hs U hU e (interior_subset hg)

include hs in
/-- The closed support of the actual zero ideal is nowhere dense. -/
theorem schemeSectionZeroIdeal_support_isNowhereDense :
    IsNowhereDense ((schemeSectionZeroIdeal (schemeSectionDualEvaluation L s) U
      (fun i ↦ schemeDualLineFrameIso L (e i)) hU).support : Set X) := by
  apply (schemeSectionZeroIdeal (schemeSectionDualEvaluation L s) U
    (fun i ↦ schemeDualLineFrameIso L (e i)) hU).support.isClosed.isNowhereDense_iff.mpr
  exact schemeSectionZeroIdeal_support_interior_eq_empty L s hs U hU e

end Normalizer
