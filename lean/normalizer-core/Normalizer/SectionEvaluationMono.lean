import Normalizer.SectionDualEvaluation
import Normalizer.GlobalSectionFrame
import Mathlib.AlgebraicGeometry.FunctionField

/-! Evaluation at a generically nonzero line section is an actual monomorphism. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Normalizer
open CategoryTheory AlgebraicGeometry Opposite

universe u v
variable {X : Scheme.{u}} [IsIntegral X] (L : X.Modules) (s : Γ(L, ⊤))

/-- On a nonempty genuine line chart, dual evaluation is injective because
the section coordinate is nonzero in the integral section ring. -/
theorem schemeSectionDualEvaluationAt_injective_on_chart
    (hs : L.presheaf.germ ⊤ (genericPoint X) (by trivial) s ≠ 0)
    {U : X.Opens} (e : (SheafOfModules.unit X.ringCatSheaf).over U ≅ L.over U)
    (V : X.Opens) (h : V ≤ U) [Nonempty V] :
    Function.Injective (schemeSectionDualEvaluationAt L s V) := by
  have hne : (moduleLineFrameAt L e V h).symm
      (L.presheaf.map (homOfLE le_top).op s) ≠ 0 := by
    intro hz
    have he := congrArg (moduleLineFrameAt L e V h) hz
    simp only [LinearEquiv.apply_symm_apply, map_zero] at he
    have hx : genericPoint X ∈ V :=
      ((genericPoint_spec X).mem_open_set_iff V.isOpen).mpr (by simpa using ‹Nonempty V›)
    have hg := congrArg (L.presheaf.germ V (genericPoint X) hx) he
    apply hs
    simpa only [map_zero, TopCat.Presheaf.germ_res_apply] using hg
  intro a b hab
  rw [schemeSectionDualEvaluation_frame L s e V h,
    schemeSectionDualEvaluation_frame L s e V h] at hab
  exact (schemeDualFrameCoordinate L e V h).injective (mul_left_cancel₀ hne hab)

/-- Genuine line charts covering the points make dual evaluation injective
on sections of every open, including the empty open. -/
theorem schemeSectionDualEvaluationAt_injective
    (hs : L.presheaf.germ ⊤ (genericPoint X) (by trivial) s ≠ 0)
    (hcharts : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      Nonempty ((SheafOfModules.unit X.ringCatSheaf).over U ≅ L.over U))
    (V : X.Opens) : Function.Injective (schemeSectionDualEvaluationAt L s V) := by
  intro a b hab
  apply TopCat.Presheaf.section_ext
    (SheafOfModules.toSheaf X.ringCatSheaf |>.obj (schemeDualSheaf L)) V a b
  intro x hx
  obtain ⟨U, hxU, ⟨e⟩⟩ := hcharts x
  let W := V ⊓ U
  have hxW : x ∈ W := ⟨hx, hxU⟩
  have : Nonempty W := ⟨⟨x, hxW⟩⟩
  have hr : (schemeDualSheaf L).presheaf.map (homOfLE (inf_le_left : W ≤ V)).op a =
      (schemeDualSheaf L).presheaf.map (homOfLE (inf_le_left : W ≤ V)).op b := by
    apply schemeSectionDualEvaluationAt_injective_on_chart L s hs e W inf_le_right
    have he := congrArg (X.presheaf.map (homOfLE (inf_le_left : W ≤ V)).op) hab
    exact ((schemeSectionDualEvaluation L s).mapPresheaf.naturality_apply
      (homOfLE (inf_le_left : W ≤ V)).op a).trans
      (he.trans ((schemeSectionDualEvaluation L s).mapPresheaf.naturality_apply
        (homOfLE (inf_le_left : W ≤ V)).op b).symm)
  have hg := congrArg ((schemeDualSheaf L).presheaf.germ W x hxW) hr
  exact ((schemeDualSheaf L).presheaf.germ_res_apply
    (homOfLE (inf_le_left : W ≤ V)) x hxW a).symm.trans
    (hg.trans ((schemeDualSheaf L).presheaf.germ_res_apply
      (homOfLE (inf_le_left : W ≤ V)) x hxW b))

/-- Evaluation at a generically nonzero global section of an actual locally
trivial line sheaf is monic as a morphism of actual module sheaves. -/
theorem schemeSectionDualEvaluation_mono
    (hs : L.presheaf.germ ⊤ (genericPoint X) (by trivial) s ≠ 0)
    (hcharts : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      Nonempty ((SheafOfModules.unit X.ringCatSheaf).over U ≅ L.over U)) :
    Mono (schemeSectionDualEvaluation L s) := by
  apply (SheafOfModules.forget X.ringCatSheaf).mono_of_mono_map
  exact PresheafOfModules.mono_of_injective
    (fun {V} ↦ schemeSectionDualEvaluationAt_injective L s hs hcharts V.unop)

end Normalizer
