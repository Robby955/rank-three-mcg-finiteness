import Normalizer.SectionZeroScheme
import Normalizer.SectionZeroDivisor

/-! Exact support membership for the actual zero ideal of a specified section.
Vanishing means a nonunit germ, rather than a zero element of the local ring. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Normalizer
open CategoryTheory AlgebraicGeometry Opposite

universe u v
variable {X : Scheme.{u}} (L : X.Modules) (s : Γ(L, ⊤))

/-- On an affine open inside a genuine line chart, the actual local image
ideal contains a point in its support exactly when the equation germ is a nonunit. -/
theorem schemeSectionImageIdealOn_mem_support_iff {U : X.Opens}
    (e : (SheafOfModules.unit X.ringCatSheaf).over U ≅ L.over U)
    (V : U.toScheme.affineOpens) (x : U.toScheme) (hx : x ∈ V.1) :
    x ∈ (schemeSectionImageIdealOn (schemeSectionDualEvaluation L s)
      (schemeDualLineFrameIso L e)).support ↔
      ¬ IsUnit (X.presheaf.germ (U.ι ''ᵁ V.1) x.val (by exact ⟨x, hx, rfl⟩)
        (sectionLocalEquation L s e (U.ι ''ᵁ V.1) (U.ι_image_le V.1))) := by
  rw [Scheme.IdealSheafData.mem_support_iff_of_mem hx,
    schemeSectionImageIdealOn_ideal_eq_span, schemeSectionDualEvaluation_equation,
    Scheme.zeroLocus_span, Scheme.zeroLocus_singleton]
  change (x ∉ U.toScheme.basicOpen _) ↔ _
  rw [Scheme.Opens.mem_basicOpen_toScheme,
    X.mem_basicOpen _ x.val (by exact ⟨x, hx, rfl⟩)]
  rfl

variable {ι : Type v} [Finite ι] (U : ι → X.Opens)
  [∀ i, QuasiCompact (U i).ι] (hU : iSup U = ⊤)
  (e : ∀ i, (SheafOfModules.unit X.ringCatSheaf).over (U i) ≅ L.over (U i))

/-- The global zero ideal has the exact nonunit-germ support test on each
actual affine chart; global support is derived from exact ideal restriction. -/
theorem schemeSectionZeroIdeal_mem_support_iff_affine (i : ι)
    (V : (U i).toScheme.affineOpens) (x : (U i).toScheme) (hx : x ∈ V.1) :
    x.val ∈ (schemeSectionZeroIdeal (schemeSectionDualEvaluation L s) U
      (fun i ↦ schemeDualLineFrameIso L (e i)) hU).support ↔
      ¬ IsUnit (X.presheaf.germ ((U i).ι ''ᵁ V.1) x.val (by exact ⟨x, hx, rfl⟩)
        (sectionLocalEquation L s (e i) ((U i).ι ''ᵁ V.1) ((U i).ι_image_le V.1))) := by
  have he := schemeSectionZeroIdeal_comap (schemeSectionDualEvaluation L s) U
    (fun i ↦ schemeDualLineFrameIso L (e i)) hU i
  have hh := congrArg (fun I ↦ x ∈ I.support) he
  rw [Scheme.IdealSheafData.support_comap] at hh
  exact (iff_of_eq hh).trans (schemeSectionImageIdealOn_mem_support_iff L s (e i) V x hx)

/-- On every open inside a genuine chart, support membership of the actual
global zero ideal is equivalent to noninvertibility of the original equation germ. -/
theorem schemeSectionZeroIdeal_mem_support_iff (i : ι)
    (V : X.Opens) (h : V ≤ U i) (x : X) (hx : x ∈ V) :
    x ∈ (schemeSectionZeroIdeal (schemeSectionDualEvaluation L s) U
      (fun i ↦ schemeDualLineFrameIso L (e i)) hU).support ↔
      ¬ IsUnit (X.presheaf.germ V x hx (sectionLocalEquation L s (e i) V h)) := by
  let y : (U i).toScheme := ⟨x, h hx⟩
  obtain ⟨W, hW, hyW, hWV⟩ := exists_isAffineOpen_mem_and_subset
    (X := (U i).toScheme) (x := y) (U := (U i).ι ⁻¹ᵁ V) hx
  have hiWV : (U i).ι ''ᵁ W ≤ V := by
    rintro z ⟨w, hw, rfl⟩
    exact hWV hw
  have hxW : x ∈ (U i).ι ''ᵁ W := ⟨y, hyW, rfl⟩
  have heq : X.presheaf.germ ((U i).ι ''ᵁ W) x hxW
      (sectionLocalEquation L s (e i) ((U i).ι ''ᵁ W) ((U i).ι_image_le W)) =
      X.presheaf.germ V x hx (sectionLocalEquation L s (e i) V h) := by
    rw [← sectionLocalEquation_restrict L s (e i) hiWV h]
    exact X.presheaf.germ_res_apply (homOfLE hiWV) x hxW _
  have hh := schemeSectionZeroIdeal_mem_support_iff_affine L s U hU e i ⟨W, hW⟩ y hyW
  change (x ∈ _) ↔ ¬ IsUnit (X.presheaf.germ ((U i).ι ''ᵁ W) x hxW
    (sectionLocalEquation L s (e i) ((U i).ι ''ᵁ W) ((U i).ι_image_le W))) at hh
  rw [heq] at hh
  exact hh

/-- A nonunit equation germ yields an actual point of the constructed
global zero scheme, preserving its complete scheme structure. -/
theorem schemeSectionZeroScheme_nonempty_of_nonunit_affine (i : ι)
    (V : (U i).toScheme.affineOpens) (x : (U i).toScheme) (hx : x ∈ V.1)
    (hz : ¬ IsUnit (X.presheaf.germ ((U i).ι ''ᵁ V.1) x.val (by exact ⟨x, hx, rfl⟩)
      (sectionLocalEquation L s (e i) ((U i).ι ''ᵁ V.1) ((U i).ι_image_le V.1)))) :
    Nonempty (schemeSectionZeroScheme (schemeSectionDualEvaluation L s) U
      (fun i ↦ schemeDualLineFrameIso L (e i)) hU) := by
  have hm := (schemeSectionZeroIdeal_mem_support_iff_affine L s U hU e i V x hx).mpr hz
  change x.val ∈ ((schemeSectionZeroIdeal (schemeSectionDualEvaluation L s) U
    (fun i ↦ schemeDualLineFrameIso L (e i)) hU).support : Set X) at hm
  rw [← Scheme.IdealSheafData.range_subschemeι] at hm
  obtain ⟨z, _⟩ := hm
  exact ⟨z⟩

/-- A zero of the prescribed section, expressed by a nonunit equation germ
on any genuine chart, supplies a point of its actual global zero scheme. -/
theorem schemeSectionZeroScheme_nonempty_of_nonunit (i : ι)
    (V : X.Opens) (h : V ≤ U i) (x : X) (hx : x ∈ V)
    (hz : ¬ IsUnit (X.presheaf.germ V x hx (sectionLocalEquation L s (e i) V h))) :
    Nonempty (schemeSectionZeroScheme (schemeSectionDualEvaluation L s) U
      (fun i ↦ schemeDualLineFrameIso L (e i)) hU) := by
  have hm := (schemeSectionZeroIdeal_mem_support_iff L s U hU e i V h x hx).mpr hz
  change x ∈ ((schemeSectionZeroIdeal (schemeSectionDualEvaluation L s) U
    (fun i ↦ schemeDualLineFrameIso L (e i)) hU).support : Set X) at hm
  rw [← Scheme.IdealSheafData.range_subschemeι] at hm
  obtain ⟨z, _⟩ := hm
  exact ⟨z⟩

end Normalizer
